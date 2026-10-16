;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.recheck
  "Narrowing the `exceptWhen` re-check to the firings a trigger can reach: a memory-only
  filter over a queued rule's firings and recorded refusals, run before any level-6
  query, in which every \"cannot tell\" answers keep.  A settle pass reads it through
  `exception-blocked-set` and `released-refusals`.  See docs/exceptions.md, \"Narrowing
  the re-check to the firings a trigger can reach\"."
  (:require [vaelii.impl.chain :as chain]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- peel-negation
  "`s` with every `not` wrapper stripped.  Polarity is dropped: the shape test asks only
  which content a trigger is about."
  [s]
  (if (and (sequential? s) (= 'not (first s)) (= 2 (count s)))
    (recur (second s))
    s))

(defn- literal-shape
  "`[predicate {argument -> count}]` of `lit` with polarity dropped, or nil when `lit` is
  not flat and ground.  The arguments are a multiset, so a symmetric predicate's mirrored
  fact has the same shape."
  [lit]
  (let [body (peel-negation lit)]
    (when (and (sequential? body) (symbol? (nm/functor body)))
      (let [as (nm/args body)]
        (when (and (seq as)
                   (not-any? sequential? as)               ; a nested subterm: cannot tell
                   (not-any? #(and (symbol? %) (sx/variable? %)) as))
          [(nm/functor body) (frequencies as)])))))

(defn- cross-argument-predicate?
  "Can a level-6 prover derive `pred` from content with different arguments?  Then
  argument agreement proves nothing about it, and the caller keeps every candidate.
  True for the closure relations, `disjoint`, the evaluables, a predicate declared
  transitive, reflexive or with an inverse, and one `inherit/declared-about?` names as
  having a preserved argument position.  The property reads are global."
  [kb pred]
  (let [tx (reasoning/taxonomy kb)]
    (or (contains? provers/transitive-predicates pred)
        (contains? provers/evaluable-predicates pred)
        (= 'evaluate pred)
        (= 'disjoint pred)
        (tax/has-prop? tx :transitive pred)
        (tax/has-prop? tx :reflexive pred)
        (seq (tax/inverses-under tx pred))
        (inherit/declared-about? kb pred))))

(defn- merge-normalizer
  "A `literal -> literal` fn mapping every symbol to its equality-class representative,
  read unscoped, or nil when the partition is empty.  The caller applies it to both sides
  of the shape test."
  [kb]
  (when (tax/merged-term-pred (reasoning/taxonomy kb))
    (fn [lit] (res/representative-term kb nil lit))))

(defn- trigger-shapes
  "The shapes of a rule's queued triggers, or `:all` when the rule was queued
  unconditionally or any trigger has no readable shape.  `norm` is `merge-normalizer`,
  applied here and to the conjunct side alike."
  [triggers norm]
  (if (#{:all :all-rejoin} triggers)
    :all
    (let [ss (map #(literal-shape (cond-> % norm norm)) triggers)]
      (if (some nil? ss) :all (set ss)))))

(defn- reachable-predicates
  "The trigger predicates that can answer the exception conjunct `lit`, whose predicate is
  `pred`: the global `specs` of `pred` for a positive conjunct, and `specs` plus `genls`
  for a negated one."
  [kb pred lit]
  (let [tax (reasoning/taxonomy kb)]
    (if (sx/negation? lit)
      (into (tax/specs-global tax pred) (tax/genls-global tax pred))
      (tax/specs-global tax pred))))

(defn- separation-reaches?
  "Can a trigger on the predicate `tp` answer the negated unary conjunct `lit` on `pred`
  through a separation's denial: a membership `(tp x)` of a type a declaration separates
  from `pred` (`tax/pair-separated?`, unscoped, a superset over every reader) answers
  `(not (pred x))` (`res/separation-denials`)."
  [kb pred lit tp]
  (boolean (and (sx/negation? lit) (symbol? tp) (symbol? pred)
                (= 1 (count (nm/args (peel-negation lit))))
                (tax/pair-separated? (reasoning/taxonomy kb) tp pred))))

(defn- firing-reachable?
  "Could a trigger of a shape in `shapes` have flipped this firing's block condition?
  `except` is the rule's block literals; `bindings` are substituted into each, and one
  literal whose arguments agree with a trigger's and whose `reachable-predicates` hold the
  trigger's predicate, or whose denial a membership on it answers through a separation
  (`separation-reaches?`), is enough.  An unreadable literal, or one on a `cross?` predicate,
  keeps the firing.

  `cross?` is `cross-argument-predicate?` memoized by the caller for the pass, because
  one of its arms reads the index and the filter reads nothing but memory per firing.
  `norm` is `merge-normalizer`'s answer, applied to each substituted literal as it is to
  the trigger shapes."
  [kb except bindings shapes cross? norm]
  (boolean
   (some (fn [lit]
           (let [lit' (cond-> (res/substitute lit bindings) norm norm)]
             (if-let [[lp la] (literal-shape lit')]
               (or (cross? lp)
                   (let [reach (reachable-predicates kb lp lit')]
                     (some (fn [[tp ta]] (and (= la ta)
                                              (or (contains? reach tp)
                                                  (separation-reaches? kb lp lit' tp))))
                           shapes)))
               true)))                                    ; unreadable conjunct: keep
         except)))

(defn- firing-test
  "A `bindings -> boolean` fn answering `firing-reachable?` for the block literals
  `except` against the trigger `shapes`, for one rule.  With no equality class
  (`norm` nil) and every literal flat, on a named predicate `cross?` refuses and with a
  variable argument, a literal agrees with a trigger only when a variable of it is bound
  to a trigger argument.  So the fn first looks each variable up in `bindings`, and
  rejects a firing that binds every one to an atom and none to a trigger argument: a
  firing the trigger does not name costs a lookup per variable, not a substitution per
  literal."
  [kb except shapes cross? norm]
  (let [args  (into #{} (mapcat (comp keys second)) shapes)
        var?  #(and (symbol? %) (sx/variable? %))
        flat? (fn [lit]
                (let [b (peel-negation lit)]
                  (and (sequential? b) (symbol? (nm/functor b)) (not (var? (nm/functor b)))
                       (not (cross? (nm/functor b)))
                       (not-any? sequential? (nm/args b)) (some var? (nm/args b)))))
        vars  (when (and (nil? norm) (seq except) (every? flat? except))
                (into [] (comp (mapcat #(nm/args (peel-negation %))) (filter var?) (distinct))
                      except))]
    (if vars
      ;; a variable left unbound (a query's own) or bound to a compound gives a literal
      ;; the shape test cannot read, so it goes to the full test
      (fn [bindings] (and (some #(let [x (res/substitute % bindings)]
                                   (or (sequential? x) (var? x) (contains? args x)))
                                vars)
                          (firing-reachable? kb except bindings shapes cross? norm)))
      (fn [bindings] (firing-reachable? kb except bindings shapes cross? norm)))))

(defn withdrawal-marker?
  "Is queued trigger `t` one of `special`'s withdrawal markers rather than a sentence?"
  [t]
  (or (keyword? t) (map? t)))

(defn- blocked-firings
  "The members of `firings` the blocked set holds, walking whichever is smaller."
  [blocked firings]
  (if (< (count blocked) (count firings))
    (filter #(contains? firings %) blocked)
    (filter #(contains? blocked %) firings)))

(defn- entailment-candidates
  "The firings of rule `rsx` whose `chain/entailment-withdrawn?` answer an `::entailment`
  marker can have moved: the blocked ones, which a satisfiable network releases, and the
  rest only while some network the rule joins on is unsatisfiable
  (`chain/entailment-withdrawable?`) — or all of them when a block literal is on a
  predicate a calculus answers, whose answer moves with the whole network."
  [kb rsx firings block-lits blocked]
  (if (or (chain/entailment-withdrawable? kb rsx)
          (some #(let [b (peel-negation %)]
                   (and (sequential? b) (chain/answered-by-calculus? kb (nm/functor b))))
                block-lits))
    firings
    (blocked-firings @blocked firings)))

(defn- preserving-candidates
  "The firings of rule `rsx` a `{::preserving s}` marker can have moved: those binding an
  antecedent on a declared predicate to a goal one of the markers' sentences moves
  (`inherit/moved-goal-test`), each also read under the equality representative
  (`merge-normalizer`).  All of them when a sentence has no test or no antecedent is on
  a declared predicate."
  [kb rsx firings sens test-for norm]
  (let [tests (for [s sens, s' (cond-> [s] norm (conj (norm s)))] (test-for s'))
        antes (filterv #(and (sequential? %) (symbol? (nm/functor %))
                             (not= 'not (nm/functor %))
                             (inherit/declared-about? kb (nm/functor %)))
                       (:antecedent rsx))]
    (if (or (some nil? tests) (empty? antes))
      firings
      (filter (fn [jid]
                (if-let [j (p/get-justification (:records kb) jid)]
                  (some (fn [a]
                          (let [g (res/substitute a (:bindings j))]
                            (some (fn [t] (or (t g) (and norm (t (norm g))))) tests)))
                        antes)
                  false))
              firings))))

(defn- except-candidates
  "The firings of the rule at `rh` resting on a handle of one of `closures`, the
  consequence closures of the targets an `except` moved (`{::except-closure c}`
  markers): read off each handle's dependents, so they cost the closure and not the
  rule's extent."
  [tms rh closures]
  (into #{}
        (comp cat
              (mapcat #(jtms/dependents tms %))
              (filter #(= rh (:informant (jtms/justification tms %)))))
        closures))

(defn- names-moved?
  "Do the bindings `b` of a firing or a refusal bind a variable to one of `moved`?"
  [moved b]
  (boolean (some moved (vals b))))

(defn- separation-candidates
  "The members of `firings` whose bindings name a type of the `{::separation types}`
  markers' sets `seps`: a separation moved only for pairs below what moved, and a
  firing binds the pair its `disjoint` antecedent read."
  [kb firings seps]
  (let [moved (into #{} cat seps)]
    (filter (fn [jid]
              (when-let [j (p/get-justification (:records kb) jid)]
                (names-moved? moved (:bindings j))))
            firings)))

(defn exception-candidates
  "The justifications of the queued rules whose block condition the queued triggers could
  have flipped.  One record fetch per rule, and none for a rule queued `:all`, which
  keeps every firing.  The block literals are the exception conjuncts read through
  their query frames (`rules/watched-literals`), the NAF inner queries and the aggregate
  bodies (docs/naf.md).  A withdrawal marker adds the firings its own test keeps
  (`entailment-candidates`, `preserving-candidates`, `except-candidates`,
  `separation-candidates`), and `::computed` keeps every firing."
  [kb queued]
  (let [tms      (reasoning/tms kb)
        cross?   (memoize #(cross-argument-predicate? kb %))
        norm     (merge-normalizer kb)
        blocked  (delay (jtms/blocked tms))
        test-for (memoize #(inherit/moved-goal-test kb %))]
    (into #{}
          (mapcat (fn [[rh triggers]]
                    (let [firings (jtms/dependents tms rh)]
                      (if (#{:all :all-rejoin} triggers)
                        firings
                        (let [sens   (remove withdrawal-marker? triggers)
                              marks  (filter withdrawal-marker? triggers)
                              shapes (when (seq sens) (trigger-shapes sens norm))
                              rsx    (when (or (seq marks) (not= :all shapes))
                                       (p/get-sentex (:records kb) rh))
                              block-lits (when rsx
                                           (concat (mapcat rules/watched-literals
                                                           (apply concat (provers/rule-exceptions kb rh)))
                                                   (rules/naf-queries rsx)
                                                   (rules/aggregate-queries rsx)))
                              pres   (keep ::special/preserving marks)
                              seps   (keep ::special/separation marks)]
                          (cond
                            (and (seq sens) (or (= :all shapes) (empty? block-lits)))
                            firings                        ; nothing to narrow by
                            (and (seq marks) (nil? rsx)) firings
                            :else
                            (concat
                             (when (seq sens)
                               ;; the bindings are on the record: the network keeps only
                               ;; what belief is computed from (`jtms/graph-just`)
                               (let [reach? (firing-test kb block-lits shapes cross? norm)]
                                 (filter (fn [jid]
                                           (if-let [j (p/get-justification (:records kb) jid)]
                                             (reach? (:bindings j))
                                             false))
                                         firings)))
                             (when (some #{::special/entailment} marks)
                               (entailment-candidates kb rsx firings block-lits blocked))
                             ;; a computed answer moves with every source the prover
                             ;; reads, which no argument of the firing names
                             (when (some #{::special/computed} marks) firings)
                             (when (seq seps) (separation-candidates kb firings seps))
                             (when (seq pres)
                               (preserving-candidates kb rsx firings pres test-for
                                                      norm))
                             (except-candidates tms rh (keep ::special/except-closure marks)))))))))
          queued)))

(defn exception-blocked-set
  "The blocked set after re-deciding the exceptions of `exception-candidates`' firings:
  a block outside the candidates is carried forward, and every candidate is re-decided
  from scratch.  The whole set, since `jtms/set-blocked` replaces rather than adds.
  `cands` is `exception-candidates`' answer for `queued`, when the caller holds it."
  ([kb queued] (exception-blocked-set kb queued (exception-candidates kb queued)))
  ([kb _queued cands]
   (let [tms   (reasoning/tms kb)
         held  (into #{} (remove cands) (jtms/blocked tms))]
     (into held
           (filter (fn [jid]
                     (when-let [j (p/get-justification (:records kb) jid)]
                       (chain/justification-excepted? kb j))))
           cands))))

(defn released-refusals
  "The recorded refusals the queued triggers may have released: `{:free [[rule-handle
  entry] …] :overflow [rule-handle …]}`.  Narrowed as `exception-candidates` narrows
  justifications.  A dead entry is dropped as it is read, and an overflowed rule is named
  for the caller to re-join (docs/exceptions.md, \"A refused firing is remembered as
  bindings\")."
  [kb queued]
  (let [refused @(reasoning/refused kb)]
    (if (empty? refused)
      {:free [] :overflow []}
      (let [cross? (memoize #(cross-argument-predicate? kb %))
            norm   (merge-normalizer kb)]
        (reduce
         (fn [acc [rh triggers]]
           (let [recs (get refused rh)]
             (cond
               (nil? recs)        acc
               (= :overflow recs) (update acc :overflow conj rh)
               :else
               (let [seps   (when (set? triggers) (keep ::special/separation triggers))
                     ;; separation markers alone keep the refusals naming a moved type
                     moved? (when (and (seq seps) (every? ::special/separation triggers))
                              (partial names-moved? (into #{} cat seps)))
                     shapes (if (and (set? triggers) (some withdrawal-marker? triggers))
                              :all             ; a marker keeps every refusal, as `:all` does
                              (trigger-shapes triggers norm))
                     rsx    (when-not (= :all shapes) (p/get-sentex (:records kb) rh))
                     ;; the two block conditions the record covers, frames peeled
                     ;; as in `exception-candidates`
                     lits   (when rsx
                              (concat (mapcat rules/watched-literals
                                              (apply concat (provers/rule-exceptions kb rh)))
                                      (rules/naf-queries rsx)))]
                 (reduce (fn [acc e]
                           (case (chain/refusal-state kb rh e)
                             :free (update acc :free conj [rh e])
                             :dead (do (chain/drop-refusal! kb rh e) acc)
                             acc))
                         acc
                         (cond
                           moved?      (filter #(moved? (:bindings %)) recs)
                           (seq lits)  (let [reach? (firing-test kb lits shapes cross? norm)]
                                         (filter #(reach? (:bindings %)) recs))
                           :else       recs))))))
         {:free [] :overflow []}
         queued)))))
