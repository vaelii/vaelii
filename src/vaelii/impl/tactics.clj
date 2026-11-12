;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.tactics
  "The node engine's search policy: one additive estimate whose terms carry signs a
  tactician picks, so `vaelii.impl.inference` searches breadth-first, depth-first or
  best-first with one driver.  Every complete tactician returns the same answer set.  See
  docs/inference.md."
  (:require [vaelii.impl.plan :as plan]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]))

(def literal-ceiling
  "The most any one literal may contribute to the base term.

  The index model answers a large finite number for a literal it cannot bound at all,
  and a conjunction of those must not sum into a cost that swamps the sign terms — the
  ordering would stop being a policy and become a saturation.  Clamping per literal
  keeps the base term comparable with the weights below."
  1000000)

;; ---- the base term -------------------------------------------------------

(defn solved-form
  "The node's conjunction as it will actually be solved, paired with the rewriting
  allowance each literal still carries.

  Nothing is applied here: a node's literals already carry every unifier taken to reach
  it, because a rewrite substitutes into them.  The conjunction *is* the question as it
  now stands, which is what the estimate has to cost."
  [{:keys [literals]}]
  (mapv (fn [{:keys [sentence depth]}] [sentence (long depth)]) literals))

;; `backchain-estimate` is genuinely recursive — a rule's antecedent is costed by the
;; rules concluding *it* — so it stands ahead of the base term that consults it.

(defn- goal-cost
  "What the index model expects `goal` to match, clamped."
  [kb goal context]
  (min literal-ceiling (long (plan/est-matches kb goal #{} {:context context}))))

(defn backchain-estimate
  "What proving `goal` *through the rules that conclude it* is expected to cost, or
  **nil** when no rule concludes it and the direct estimate is the whole story.

  A literal whose only route is an expensive backchain is costed by the index at its own
  fan-out, which for a predicate with no stored facts at all is zero — the most
  expensive literal in the conjunction ranked as the cheapest.  This asks the rules
  instead: unify the goal with each candidate consequent and cost that rule's
  antecedents, recursively.

  `:aggregate` is the choice between two readings of several candidate rules.
  `:first` takes the **min** — any one rule suffices, so the cheapest route is what the
  goal costs.  `:all` takes the **sum** — a complete search runs every candidate, so
  they all get paid for.

  Strictly more expensive to compute than a direct estimate, and recursive, which is why
  it is opt-in (`:estimate-backchain?`), bounded by `:depth`, and consulted only for a
  literal that still has rewriting allowance.  `seen` caps it at a repeated goal
  (`res/goal-key`, so two goals differing only in variable names are one), which is
  what makes it terminate on a cyclic rule set."
  ([kb goal context] (backchain-estimate kb goal context {}))
  ([kb goal context {:keys [aggregate depth seen] :or {aggregate :first depth 2 seen #{}}}]
   (let [k (res/goal-key goal)]
     (when (and (pos? (long depth))
                (sequential? goal)
                (not (sx/deferred-literal? goal))
                (not (contains? seen k)))
       (let [seen' (conj seen k)
             cost  (fn [{:keys [antecedents consequent]}]
                     (when-let [b (res/subsuming-unify kb goal consequent res/no-bindings context)]
                       (reduce (fn [acc a]
                                 (let [g (res/substitute a b)]
                                   (+ acc (or (backchain-estimate
                                               kb g context
                                               {:aggregate aggregate
                                                :depth     (dec (long depth))
                                                :seen      seen'})
                                              (goal-cost kb g context)))))
                               0 antecedents)))
             costs (keep cost (provers/candidate-rules kb goal context))]
         (when (seq costs)
           (min literal-ceiling
                (long (case aggregate
                        :all (reduce + 0 costs)
                        (reduce min costs))))))))))

(defn base-estimate
  "The estimate's **base term**: what this node's conjunction costs to solve.

  `plan/explain` in one call, summed — so each literal is estimated under the variables
  the literals ahead of it bind, exactly as the join will run, and the number equals what
  `core/query-plan` prints for the same conjunction.

  With `:estimate-backchain?` set, a literal that still has rewriting allowance is costed
  through its concluding rules instead, and falls back to the index model when no rule
  concludes it."
  [kb node context strat]
  (let [pairs (solved-form node)
        bc    (:estimate-backchain? strat)
        room  (when bc
                (reduce (fn [m [s d]] (update m s (fnil max 0) d)) {} pairs))]
    (reduce (fn [acc {:keys [goal est-matches]}]
              (+ acc (min literal-ceiling
                          (long (or (when (and bc (pos? (long (get room goal 0))))
                                      (backchain-estimate kb goal context
                                                          {:aggregate bc
                                                           :depth (:backchain-depth strat 2)}))
                                    est-matches)))))
            0
            (plan/explain kb (mapv first pairs) context))))

;; ---- the tacticians ------------------------------------------------------

(def tacticians
  "A tactician is a pair of signs and a child bias, nothing more.

    :cost                  the cheapest conjunction first, and nothing else
    :budget-first          the node with the most rewriting allowance left
    :ground-first          the node closest to having spent it, hence nearest to ground —
                           the default, on the measurement (see `defaults`)
    :breadth-first         level order over the search tree
    :depth-first           the deepest node first — a dive
    :removal-first         a productive node's children sink: finish what is paying
    :transformation-first  a productive node's children rise: chase what is paying

  The last two act through the child bias rather than the node estimate (`child-bias`),
  because what they choose between is not two numbers on one node but which of two nodes
  a *parent's* answers should recommend.  All seven are complete: each reorders the
  frontier and none of them drops a node."
  {:cost                 {:depth-sign  0 :tree-sign  0 :motivation  0}
   :budget-first         {:depth-sign -1 :tree-sign  0 :motivation  0}
   :ground-first         {:depth-sign  1 :tree-sign  0 :motivation  0}
   :breadth-first        {:depth-sign  0 :tree-sign  1 :motivation  0}
   :depth-first          {:depth-sign  0 :tree-sign -1 :motivation  0}
   :removal-first        {:depth-sign  0 :tree-sign  0 :motivation  1}
   :transformation-first {:depth-sign  0 :tree-sign  0 :motivation -1}})

(def defaults
  "The strategy a session runs under when a caller names none.

  **`:ground-first`, on the measurement** (`lein bench-tactics`).  It is the only
  tactician that is best-or-tied on every column measured: 0.47× the default's time to a
  **first** answer, 0.93× to fifty of them, the fastest node ordering on a needle at
  every depth tried, and 1.00× on an exhaustive run, where nothing can differ.  Preferring
  the node closest to spending its rewriting allowance means preferring the node closest
  to being ground, and a ground conjunction is one facts can answer.

  `:cost` — both signs zero, the base term and the size penalty alone — is the identity
  policy, and stays available for a caller who wants the ordering to follow the cost model
  and nothing else.

  The weights are large next to a typical base term on purpose: a sign that only broke
  ties would not be a strategy.  `:breadth-bias` scales the depth term alone, for tuning
  the one weight that decides how far the search commits before it reconsiders.

  It carries `:ground-first`'s three signs, so this is itself a **normalized** strategy —
  the shape every reader of one expects (`child-bias` reads `:motivation`, `node-estimate`
  reads the other two).  `strategy` merging the tactician's signs over it is a no-op for
  this tactician and the override for any other."
  (merge (:ground-first tacticians)
         {:tactician           :ground-first
          :size-penalty        4
          :depth-weight        1000
          :tree-weight         1000
          :breadth-bias        1.0
          :motivation-weight   1000000000
          :first-result?       false
          :estimate-backchain? false
          :backchain-depth     2}))

(defn strategy
  "Normalize `s` — a tactician keyword, a full or partial strategy map, or nil — into the
  map the engine reads.  An explicit sign in the map overrides the tactician's, so a
  caller may name a tactician and then bend one term of it."
  [s]
  (let [m (cond (nil? s) {} (keyword? s) {:tactician s} :else s)
        t (get m :tactician (:tactician defaults))]
    (if-let [signs (get tacticians t)]
      (merge defaults signs m {:tactician t})
      (throw (ex-info (str "no such tactician: " (pr-str t) " — want one of "
                           (pr-str (vec (sort (keys tacticians)))))
                      {:type :unknown-tactician :tactician t
                       :known (vec (sort (keys tacticians)))})))))

(defn with-tactician
  "`strat` re-pointed at tactician `t`: `t`'s signs replace whatever signs `strat`
  carries, and every other weight the caller set is kept.

  `strategy` cannot do this, and must not: an explicit sign in the map it is handed
  **overrides** the tactician's, which is what lets a caller name a tactician and then
  bend one term of it.  A strategy that has already been normalized carries all three
  signs, so re-normalizing it under a different `:tactician` keeps the old ordering
  under the new name — which is a portfolio racing several copies of one search while
  reporting three tacticians.  So the swap says which side wins, here, where the answer
  is the new tactician's.

  The result is a fixed point of `strategy`: its signs are `t`'s, so normalizing it
  again merges `t`'s signs over the identical values."
  [strat t]
  (if-let [signs (get tacticians t)]
    (merge strat signs {:tactician t})
    (throw (ex-info (str "no such tactician: " (pr-str t) " — want one of "
                         (pr-str (vec (sort (keys tacticians)))))
                    {:type :unknown-tactician :tactician t
                     :known (vec (sort (keys tacticians)))}))))

(defn complete?
  "Does this strategy return the whole answer set?

  Every tactician only reorders, so the answer is yes unless `:first-result?` is on —
  the one mode that stops the search rather than steering it."
  [strat]
  (not (:first-result? strat)))

;; ---- the estimate --------------------------------------------------------

(defn estimate
  "What `node` is expected to cost, under `strat`.  Lower pops first.

  Runs once per node, at enqueue.  That is the whole reason `:estimate-backchain?` is
  off by default: the base term is index reads, and a sub-search per enqueued node would
  make choosing what to expand cost more than expanding it."
  [kb strat node]
  (let [{:keys [size-penalty depth-weight tree-weight breadth-bias depth-sign tree-sign]} strat
        lits (:literals node)
        sumd (reduce (fn [acc l] (+ acc (long (:depth l)))) 0 lits)]
    (long (+ (base-estimate kb node (:context node) strat)
             (* (long size-penalty) (count lits))
             (* (long depth-sign)
                (Math/round (* (double depth-weight) (double breadth-bias) (double sumd))))
             (* (long tree-sign) (long tree-weight) (long (:tree-depth node)))))))

(defn estimate-breakdown
  "The terms `estimate` sums, itemized — so a reader can see *where* a node's cost came
  from rather than only its total.  The four terms and the total are `estimate`'s own,
  recomputed the same way; the per-literal costs are `plan/explain`'s, in the order the
  join will run them, so they are the numbers `core/query-plan` prints for the same
  conjunction.

  The per-literal `:cost` is the clamped index estimate (`:est-matches`, ≤ `literal-ceiling`).
  With `:estimate-backchain?` set, `:base` costs an allowance-carrying literal through its
  concluding rules instead, so the summed per-literal costs and `:base` may then differ —
  `:base` is the authoritative total either way."
  [kb strat node]
  (let [{:keys [size-penalty depth-weight tree-weight breadth-bias depth-sign tree-sign]} strat
        ctx   (:context node)
        pairs (solved-form node)
        sumd  (reduce (fn [acc [_ d]] (+ acc (long d))) 0 pairs)
        base  (long (base-estimate kb node ctx strat))
        size  (* (long size-penalty) (count pairs))
        dep   (* (long depth-sign)
                 (Math/round (* (double depth-weight) (double breadth-bias) (double sumd))))
        tree  (* (long tree-sign) (long tree-weight) (long (:tree-depth node)))]
    {:literals      (mapv (fn [{:keys [goal est-matches block isolated? deferred? recursive?]}]
                            {:sentence   goal
                             :cost       (min literal-ceiling (long est-matches))
                             :block      block
                             :isolated?  (boolean isolated?)
                             :deferred?  (boolean deferred?)
                             :recursive? (boolean recursive?)})
                          (plan/explain kb (mapv first pairs) ctx))
     :sum-allowance sumd
     :base          base
     :size-penalty  size
     :depth-term    dep
     :tree-term     tree
     :total         (+ base size dep tree)}))

(defn child-bias
  "The additive bias this node's children carry into the frontier — zero unless the
  tactician has an opinion about a node that already produced answers.

  A **large** additive number rather than a reordering: `+bias` sinks a child behind
  everything in the frontier without dropping it, `−bias` hoists it above everything.
  The bias applies to the children of a *productive* node only, which is the one
  removal-versus-transformation distinction this engine has to offer — a node solves its
  conjunction inline and rewrites it into children in the same step, so there are no two
  classes of child to choose between, only two readings of a parent that is paying:
  finish it, or chase it.

  Complete either way — a biased child is expanded, just later or sooner — so both
  tacticians that use this are in the completeness sweep."
  [strat productive?]
  (if productive?
    (* (long (:motivation strat)) (long (:motivation-weight strat)))
    0))

;; ---- choosing one without a caller ---------------------------------------

(defn- functor [goal] (when (and (sequential? goal) (seq goal)) (first goal)))

(defn auto-strategy
  "A tactician (or `:portfolio`) picked from the *shape* of the query, for a caller who
  has no opinion.  One index read and no search: the point is to cost less than the
  first node expansion it is choosing for.

  - no rewriting allowance at all — the root is the whole search, and ordering a
    frontier of one decides nothing;
  - a conjunction, or a single literal several rules conclude — more than one plausible
    route, which is what a portfolio is a bet on;
  - a single literal with one route — nothing to hedge, so dive.

  Opt-in (`:auto?`).  A caller who names a strategy has already answered this."
  [kb goals context depth]
  (let [goals (vec goals)
        f     (functor (first goals))]
    (cond
      (zero? (long depth))  :cost
      (not= 1 (count goals)) :portfolio
      (and f (not (sx/variable? f))
           (> (count (res/concluding-rule-handles kb f context)) 1)) :portfolio
      :else :depth-first)))
