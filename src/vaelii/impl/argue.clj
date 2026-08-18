;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.argue
  "Four-valued epistemic status for ground assertions.

   Queries both a sentence and its explicit negation (not S) and returns
   a verdict map with :verdict, :for, :against, and justification evidence.

   Two query modes:
   - No opts: uses `ask?` (ground facts + prover registry, no rule expansion)
   - With opts containing :max-depth: uses `query` (rules fire, bounded)

   Callers who want rule expansion MUST pass {:max-depth N} explicitly.
   A silent default depth would turn derivable facts into false :unknown."
  (:require [vaelii.core :as v]))

(defn- results
  "Get query results for `goal` in `context`. Returns a seq of binding
   maps (possibly empty maps for ground goals), or nil if not provable."
  [kb goal context opts]
  (seq (if (:max-depth opts)
         (v/query kb goal context opts)
         (v/ask kb goal context))))

(defn- justification-for
  "If `sentence` is stored and believed in `context`, return its full
   `why` map (handle, sentence, believed?, defeat-class, support).
   Returns nil if not stored or not believed."
  [kb sentence context]
  (when-let [h (v/handle-of kb sentence context)]
    (when (v/in? kb h)
      (v/why kb h))))

(defn- defeat-class-of
  "If `sentence` is stored in `context`, return its JTMS defeat-class
   (:monotonic or :default), or nil if not stored/not believed."
  [kb sentence context]
  (:defeat-class (justification-for kb sentence context)))

(defn- resolve-contradiction
  "Argumentation stub: when both asent and (not asent) are provable,
   attempt to resolve by comparing justification strength.
   A :monotonic justification wins over a :default one.

   Returns :true if the positive side wins, :false if the negative
   side wins, or nil if the conflict cannot be resolved (leaving
   :contradiction as the verdict)."
  ;; Resolves monotonic-vs-default only.  Specificity, recency, authority,
  ;; and user-defined preference orderings are not yet implemented.
  [kb asent context]
  (let [pos-class (defeat-class-of kb asent context)
        neg-class (defeat-class-of kb (list 'not asent) context)]
    (cond
      (and (= pos-class :monotonic) (= neg-class :default)) :true
      (and (= pos-class :default) (= neg-class :monotonic)) :false
      :else nil)))

(defn argue
  "Four-valued epistemic query over a ground assertion.

   (argue kb asent context)
   (argue kb asent context opts)

   Queries both `asent` and `(not asent)` and returns:

     {:verdict      :true/:false/:unknown/:contradiction
      :for          <query results for asent, when provable>
      :against      <query results for (not asent), when provable>
      :for-why      <justification for asent, when stored+believed>
      :against-why  <justification for (not asent), when stored+believed>}

   Without opts: uses `ask?`/`ask` (no rule expansion).
   With {:max-depth N}: uses `query?`/`query` (rules fire, bounded).
   Callers who want rule expansion MUST pass :max-depth explicitly.

   In the :contradiction case, a simple argumentation stub attempts
   resolution: a :monotonic justification beats a :default one."
  ([kb asent context]
   (argue kb asent context nil))
  ([kb asent context opts]
   (let [neg       (list 'not asent)
         for-r     (results kb asent context opts)
         against-r (results kb neg context opts)
         pos?      (boolean (seq for-r))
         neg?      (boolean (seq against-r))
         for-j     (justification-for kb asent context)
         against-j (justification-for kb neg context)
         base      (cond-> {}
                     pos?      (assoc :for for-r)
                     neg?      (assoc :against against-r)
                     for-j     (assoc :for-why for-j)
                     against-j (assoc :against-why against-j))]
     (cond
       (and pos? (not neg?))
       (assoc base :verdict :true)

       (and neg? (not pos?))
       (assoc base :verdict :false)

       (and (not pos?) (not neg?))
       (assoc base :verdict :unknown)

       ;; both provable — try argumentation
       :else
       (if-let [resolved (resolve-contradiction kb asent context)]
         (assoc base :verdict resolved)
         (assoc base :verdict :contradiction))))))
