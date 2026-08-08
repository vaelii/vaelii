;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.plan
  "Conjunctive query planning: the order a conjunction's literals are solved in.

  A conjunction is commutative — `[(parentOf Tom ?y) (dog ?y)]` and its reverse have
  exactly the same solutions — but it is not equicost.  Solved left to right, the
  first literal's matches are enumerated in full and each one re-drives the second;
  so the first literal's *fan-out* multiplies everything after it.  Leading with the
  selective literal is the whole game, and on a measured three-literal join it ran
  7x faster than leading with the general one.

  Three mechanisms, the first two of which the KB already had lying around unused:

  **Selectivity** — the count-aware trie answers \"how many facts are under this
  path prefix\" in O(1) (`count-at`), and the secondary argument roots answer \"how
  many facts have this term at position n\" (`count-with-arg`) for the ground
  arguments the trie cannot reach.  `est-matches` reads both.

  **Sideways information passing** — a literal's cost is not fixed, it depends on
  what is already bound when it runs.  `(parentOf ?x ?y)` is the whole extent of
  `parentOf`; the same literal after `?x` is bound is one person's children.  So no
  literal is costed once and for all: an estimate is always taken under the variables
  bound at the point the literal would run.

  **The cartesian factors last, on structure rather than on cost** — a literal
  sharing no variable with anything else in the conjunction narrows nothing and is
  narrowed by nothing, so wherever it runs it multiplies the row count of everything
  after it.  Its own extent is then the wrong thing to rank it by, and rank it the
  wrong way: a *selective* isolated literal is the worst kind, because taking the
  cheapest available literal puts exactly that one first, where its factor is applied
  to the whole rest of the plan.  `deferring-isolated-order` holds them to the back.

  Sharing no variable is what makes such a literal *unconstrained*; it is not on its
  own what makes it a multiplier.  A literal matching at most once multiplies by at
  most one, so it can only prune and belongs first — and the ground literal, which
  both chaining paths produce by substituting a rule's bindings before planning, has
  no variables to share and so satisfies the structural test vacuously.  Both
  conditions are therefore checked, and `cartesian-factors` is where.

  That placement is deliberately made on **structure and not on an estimate**.
  Whether a literal shares a variable is read off the conjunction; how big a join
  comes out is a guess the index can only bound from above, and those bounds do not
  compose — a plan chosen by minimizing estimated cost end to end multiplies the
  bound's error once per literal, and lands wide of one that never trusted it that
  far.  So the estimate decides the order *within* each group, where it is compared
  once and locally, and structure decides which group a literal is in.  The one thing
  an upper bound *can* settle is that a literal will not fan out at all — a bound of 1
  is a proof of it — which is the only load the estimate carries in that decision.

  ## What is never reordered

  Ordering here is an execution decision and must not change the answer set.  Two
  classes of literal are held back, exactly as `sentex/canonicalize-rule` holds them
  back when it canonicalizes a rule for storage:

  - **Deferred (evaluable) literals** — `evaluate`, `lessThan`, `greaterThan`.
    These consume bindings rather than produce them; `(evaluate ?z (+ ?x ?y))` run
    before `?x` is bound does not throw, it quietly yields *no* solutions.  They are
    never hoisted above a literal that binds them.  They are, however, pulled
    *forward* to the first point where all their variables are bound — a test that
    can run early prunes the search early, which the storage canonicalization (which
    parks them uniformly last) does not attempt.
  - **The recursive literal of a rule** — an antecedent whose functor is the rule's
    own consequent functor.  It stays last among the generators, because a backward
    chainer executes the conjunction left to right and one that re-enters the rule
    before generating anything has nothing to recurse *on*.

    Note what this is **not** protecting against.  A rule's antecedents are put into
    canonical order at *storage* (`sentex/canonicalize-rule`), which is where an
    author's spelling stops being observable — assert the same rule with the
    recursive literal written first and the stored antecedents are identical.  So
    left-recursion is not a state a rule can reach here, and this pin is the cost
    model being kept from re-introducing one, not a rescue.

  ## Determinism

  Ties break on the literal's original position, so a plan is a function of the
  conjunction and the KB's counts, never of iteration order.  Same knowledge, same
  plan — the order-independence the rest of the engine holds to (see
  `vaelii.impl.jtms`) applied to execution rather than belief."
  (:require [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]))

;; ---- the cost model -----------------------------------------------------

(def ^:dynamic *enabled*
  "Bind to false to run every conjunction in the order it was written.

  Planning is a pure cost decision — it must never change the answer *set*, only how
  fast it is reached — and that is a claim worth being able to test rather than
  assert.  Binding this false gives the unplanned execution to compare against, which
  is what `plan_test` does over every permutation of a conjunction."
  true)

(def ^:private unbounded
  "The estimate for a literal the index cannot bound at all.  A large finite number
  rather than `Long/MAX_VALUE`, because the subtype fan-out *sums* estimates and a
  saturating sentinel would overflow into a negative cost."
  1000000000)

(defn- vars-of [form]
  (into #{} (filter sx/variable?) (tree-seq sequential? seq form)))

(defn- closed?
  "Is this term settled by the time the literal runs — either literally ground, or a
  variable already in `bound`?  Distinct from `known?`: a bound variable *will* have
  a value, but the planner does not know which one, so it can constrain a count
  without being usable as a trie prefix token."
  [term bound]
  (every? #(contains? bound %) (filter sx/variable? (tree-seq sequential? seq term))))

(defn- known?
  "Is this term's *value* known right now, so it can be used as a trie prefix token?"
  [term]
  (not-any? sx/variable? (tree-seq sequential? seq term)))

(defn- negative? [goal]
  (and (sequential? goal) (seq goal) (= 'not (first goal))))

(defn- functor-of [goal]
  (cond (not (sequential? goal)) goal
        (negative? goal)         (functor-of (second goal))
        :else                    (first goal)))

(defn- variable-functor?
  "A literal whose *functor* is open — `(?type Muffet)`.  It names no predicate, so
  neither of the two functor-keyed models below means anything for it: there is no
  subtype closure to fan over and no functor root to count.  The argument roots are
  what is left — and for the plain `(?type Muffet)` shape they are exactly what the
  matcher reads for it (`res/candidate-handles`), so the estimate is the candidate
  set.  A dotted rest has not even those."
  [goal]
  (and (sequential? goal) (seq goal) (sx/variable? (first goal))))

(defn- dotted?
  "A dotted rest pattern — `(?pred . ?args)`, `(rel A . ?rest)` — whose tail variable
  splices a whole argument list.  It has no fixed arity, so past the marker nothing
  sits at a position the trie key or an argument root pins, and the marker itself is
  not a term: both index models answer 0 for it, a *lower* bound that would rank the
  literal cheapest and hoist it to the front of the conjunction."
  [goal]
  (and (sequential? goal) (boolean (some #(= sx/dot-marker %) goal))))

(defn- unary-literal? [goal]
  (and (sequential? goal) (= 2 (count goal)) (symbol? (first goal))
       (not (sx/variable? (first goal)))))

(defn- memoizing
  "A one-plan read cache over the index.  `order` estimates every remaining literal
  on every pick, so the same `count-at` prefix is asked for O(n) times per plan;
  each of those is an index lookup.  Counts cannot change mid-plan, so caching
  them for the life of one call is free correctness-wise.

  **Fixed arities, and the cache is nested one level per argument.**  The reads it
  wraps take two arguments or three, all of them known here; a variadic wrapper would
  allocate a rest-seq per call *and* key the cache on it, and this is called O(n²)
  times per plan for a hit that should cost a hash lookup and nothing else.  Nesting
  keys on the arguments as they are, so a hit allocates nothing at all — a tuple key
  would have moved the allocation rather than removed it."
  [f]
  (let [cache (volatile! {})]
    (fn
      ([a b]
       (if-let [e (find (get @cache a) b)]
         (val e)
         (let [v (f a b)] (vswap! cache update a assoc b v) v)))
      ([a b c]
       (if-let [e (find (get (get @cache a) b) c)]
         (val e)
         (let [v (f a b c)] (vswap! cache update-in [a b] assoc c v) v))))))

(defn- prefix-estimate
  "Walk the literal left to right against the trie, extending a known path prefix.

  The walk is over the literal's **structural token stream** (`sx/key-stream`), the
  same linearization the index key uses, so a nested compound argument contributes
  its interior tokens — an arity marker, then its functor and elements — rather than
  terminating the walk as one opaque unit.  A marker carries no variable, so it
  extends the prefix like any known value; `(mass Obj1 (QuantityFn ?n Kilogram))` is
  costed by the deep prefix `[mass Obj1 <M> QuantityFn]` (selective) instead of
  stopping at `[mass Obj1]`.

  Three cases per token, and the walk stops at the first token that is not a literal
  value, because the trie narrows left to right and cannot skip a level:

  - **known value** — extend the prefix and take `count-at` of it.  Exact, not an
    estimate, for everything matching that prefix.
  - **bound but unknown** — the token will have exactly one value at run time, we
    just do not know which.  Charge the *average* branch under the prefix:
    `count-at(prefix) / |children(prefix)|`.  This is what makes sideways
    information passing pay: the trie's own fan-out is the distinct-value count that
    a textbook N/V selectivity formula wants, and it is already stored.
  - **free** — nothing constrains this position or any after it; the prefix count
    stands."
  [ix goal bound count-at* children*]
  (loop [toks (sx/key-stream goal), prefix []]
    (if (empty? toks)
      (count-at* ix prefix)
      (let [t (first toks)]
        (cond
          (known? t)       (recur (rest toks) (conj prefix t))
          (closed? t bound) (let [total    (count-at* ix prefix)
                                  branches (max 1 (count (children* ix prefix)))]
                              (max 1 (quot total branches)))
          :else            (count-at* ix prefix))))))

(defn- arg-root-estimate
  "The tightest count from the secondary argument roots.  These reach what the trie
  cannot: a ground argument sitting *after* a variable is on no prefix, so the trie
  can only count up to that variable, while the argument roots (`[:argument-root pred
  pos term]`, summed over the slot roster's predicates) index it directly.
  Each is an upper bound on the literal's matches (it ignores the other positions),
  so the smallest is the tightest.

  Only the arguments *before* a dotted rest have fixed positions — the marker is not a
  term and the tail splices a whole list — so the walk stops there rather than asking
  the roots about `.` and getting the 0 that would floor the whole estimate."
  [ix goal count-with-arg*]
  (let [args   (take-while #(not= sx/dot-marker %) (rest goal))
        counts (keep-indexed (fn [i a] (when (known? a) (count-with-arg* ix (inc i) a)))
                             args)]
    (when (seq counts) (apply min counts))))

(defn est-matches
  "Estimated number of stored facts a literal matches, given the variables already
  `bound`.  This is the literal's fan-out — the number by which it multiplies the
  cost of everything sequenced after it — which is what join ordering turns on.

  Every input is an *upper* bound on the true match count, so the minimum of them is
  the tightest bound available without touching a record."
  ([kb goal bound] (est-matches kb goal bound {}))
  ([kb goal bound {:keys [count-at children count-with-arg count-with-functor context]
                   :or   {count-at           p/count-at
                          children           p/children
                          count-with-arg     p/count-with-arg
                          count-with-functor p/count-with-functor}}]
   (let [ix (:index kb)]
     (cond
       (not (sequential? goal)) 1

       ;; A literal with nothing left open is a test: it matches at most once.
       (closed? goal bound) 1

       ;; A negative literal keys under [:false <body>], so no prefix built from its
       ;; own tokens reaches it and `count-at` would answer 0 — a *lower* bound, which
       ;; would rank the most expensive literal cheapest.  The functor root is the one
       ;; count that spans both polarities (a negative fact roots under its positive
       ;; body's functor), so it is the whole model here — unless the functor is open,
       ;; when it roots nothing and answers 0, the very trap this branch exists to
       ;; avoid.  The argument roots span both polarities too, so a ground argument
       ;; still bounds it; with nothing ground, nothing does.
       (negative? goal)
       (let [body (second goal)]
         (if (variable-functor? body)
           (or (arg-root-estimate ix body count-with-arg) unbounded)
           (count-with-functor ix (functor-of goal))))

       ;; A dotted rest pattern pins no argument position at all, so the functor root
       ;; is the only real bound on it — and an open functor has not even that.
       (dotted? goal)
       (if (variable-functor? goal)
         unbounded
         (count-with-functor ix (functor-of goal)))

       ;; A unary type literal fans out over its subtype closure at match time —
       ;; `(animal ?x)` is answered by every stored `(dog Muffet)`.  Costing it by
       ;; `animal`'s own extent would rank the most expensive kind of literal in the
       ;; KB as the cheapest, since a type high in the hierarchy usually has no direct
       ;; instances at all.  A non-type predicate has a singleton closure, so this
       ;; degenerates to the ordinary path for it.
       (unary-literal? goal)
       (let [[t a] goal]
         ;; the same scoped fan the matcher will walk (`res/sub-predicates`): an
         ;; invisible subtype contributes no matches, so it must contribute no cost
         (min unbounded
              (reduce (fn [acc t']
                        (+ acc (prefix-estimate ix (list t' a) bound count-at children)))
                      0
                      (tax/specs (:taxonomy kb) t context))))

       :else
       (min (prefix-estimate ix goal bound count-at children)
            (or (arg-root-estimate ix goal count-with-arg) unbounded))))))

;; ---- ordering -----------------------------------------------------------

(defn- deferred? [l] (sx/deferred-literal? l))

(defn- recursive-in?
  "An antecedent whose functor is the rule's own consequent functor — the literal
  whose position decides whether the rule is right- or left-recursive."
  [l consequent-pred]
  (and consequent-pred (sequential? l) (= (first l) consequent-pred)))

;; ---- placing the literals no estimate can rank --------------------------

(defn- greedy-order
  "Order generators by repeatedly taking the cheapest under the bindings in hand."
  [gens bound0 cost]
  (loop [remaining gens, bound bound0, acc []]
    (if (empty? remaining)
      acc
      ;; sort-by is stable, and the original index is the second key, so a cost tie
      ;; resolves to the literal the caller wrote first
      (let [[_ l :as pick] (first (sort-by (fn [[i g]] [(cost g bound) i]) remaining))]
        (recur (filterv #(not= (first %) (first pick)) remaining)
               (into bound (vars-of l))
               (conj acc pick))))))

(defn- cartesian-factors
  "The generators held to the back, by index.  Two conditions, and the second is not a
  refinement of the first — it is a different claim, and the pair of them is what
  \"multiplies the rest of the plan\" actually means.

  **Shares no variable** with anything else the conjunction will run.  Nothing it binds
  narrows another literal and nothing another binds narrows it, so wherever it is placed
  it multiplies the row count of everything sequenced after it.  Its extent is therefore
  not what decides where it belongs — a selective one is the worst kind, because taking
  the cheapest literal available puts precisely that one first, where the multiplication
  is applied to the whole rest of the plan.  Sharing is judged against every other
  literal the caller wrote — the other generators, the deferred literals, the recursive
  one — and against the variables already bound, so a literal feeding an evaluable is
  not one of these, and this stays a claim about the conjunction rather than about the
  generators alone.

  **And can multiply at all.**  A literal matching at most once multiplies by at most
  one: it cannot fan the plan out, only prune it, so it belongs wherever it is cheapest
  and that is first.  The case to keep in view is the *ground* literal — `(dog Bob)`
  once a rule's bindings are substituted in, which is the shape both chaining paths
  hand the planner.  It has no variables at all, so the sharing test above passes it
  vacuously; hold it to the back and a conjunction runs its whole join before reaching
  the one-lookup test that would have refuted it.

  `est-matches` bounds a literal from *above*, so an estimate of 1 is a proof that it
  matches at most once.  That is the one direction the bound is sound in and the only
  one this uses it for — it decides nothing about which of two multipliers is larger,
  which is the comparison upper bounds cannot make (see `deferring-isolated-order`)."
  [gens others bound0 cost]
  (let [elsewhere (into (set bound0) (mapcat vars-of) others)
        var-count (reduce (fn [m [_ l]]
                            (reduce (fn [m v] (update m v (fnil inc 0))) m (vars-of l)))
                          {} gens)]
    (set (keep (fn [[i l]]
                 (when (and (every? (fn [v] (and (not (elsewhere v))
                                                 (= 1 (var-count v))))
                                    (vars-of l))
                            ;; only now, and only for the few literals that got this
                            ;; far, is the index asked anything
                            (> (cost l bound0) 1))
                   i))
               gens))))

(defn- deferring-isolated-order
  "Order generators cheapest-first, but with every cartesian factor held to the back.

  This is the one ordering decision the cost model cannot be trusted to make and does
  not have to be.  Whether a literal shares a variable is **structural** — read off
  the conjunction, not off an estimate — while how large a join comes out is a
  guess the index can only bound from above.  A plan built by minimizing estimated
  cost end to end compounds that bound k times over and can land wide of a plan that
  never trusted it that far; the placement below compounds nothing, because it rests
  on no estimate at all.

  Among the connected literals the cheapest-first pick stands, and it is estimated
  under the bindings in hand as ever.  Among the isolated tail the order is cheapest
  first too, and there it is not a heuristic: a run of pure multiplications sums to
  least when the smallest factor is applied first."
  [gens bound0 cost others]
  (let [iso     (cartesian-factors gens others bound0 cost)
        connect (filterv (fn [[i _]] (not (iso i))) gens)
        loose   (filterv (fn [[i _]] (iso i)) gens)]
    (if (empty? connect)
      ;; nothing constrains anything: the whole conjunction is one product, and
      ;; ascending order is optimal for it rather than merely cheap to compute
      (greedy-order gens bound0 cost)
      (let [head  (greedy-order connect bound0 cost)
            bound (into bound0 (mapcat (comp vars-of second)) head)]
        (into head (greedy-order loose bound cost))))))

;; Literals are carried as [index literal] pairs throughout, never as bare literals.
;; A conjunction may legitimately repeat one — `[(lessThan ?a ?b) (lessThan ?a ?b)]`
;; is odd but well-formed — and removing a chosen literal by value would drop every
;; copy of it, silently shortening the conjunction.  The index is also the tie-break
;; key, so it has to survive anyway.
(defn- partition-literals
  "Split a conjunction into the three classes that are ordered differently, as
  `[index literal]` pairs: the **generators** free to be reordered on cost, the
  **recursive** literal pinned last, and the **deferred** ones threaded back in where
  each becomes ready.  `order` sequences them and `explain` reports which class a
  literal landed in, so the split is made once rather than agreed on twice."
  [goals consequent-pred]
  (let [pairs (vec (map-indexed vector goals))
        rec?  (fn [l] (and (not (deferred? l)) (recursive-in? l consequent-pred)))]
    {:gens (filterv (fn [[_ l]] (not (or (deferred? l) (rec? l)))) pairs)
     :recs (filterv (fn [[_ l]] (rec? l)) pairs)
     :defs (filterv (fn [[_ l]] (deferred? l)) pairs)}))

(defn- ready
  "The deferred literals whose variables are all bound — pull them forward to here,
  in their original relative order (one computation may feed the next)."
  [defs bound]
  (filterv (fn [[_ l]] (every? bound (vars-of l))) defs))

(defn- lits [pairs] (mapv second pairs))

(defn order
  "Order `goals` — a conjunction — for execution, and return the reordered vector.

  `opts`:
    :bound            variables already bound when the conjunction starts (default
                      none).  Callers that have already substituted their bindings
                      into the goals can leave this empty; the substituted values
                      make the literals ground on their own.
    :consequent-pred  the functor of the rule these goals are the antecedents of, if
                      they are.  Identifies the recursive literal, which is pinned
                      last (see the namespace docstring).
    :est-override     (fn [goal bound]) -> estimate or nil.  Consulted before the
                      index model, so a caller whose executor is not the index — the
                      prover registry, say — can cost a goal the way it will
                      actually be answered.

  A conjunction of fewer than two reorderable literals is returned untouched,
  without reading the index at all: the overwhelmingly common `prove` call is a
  single goal and must not pay for a planner it cannot use."
  ([kb goals context] (order kb goals context {}))
  ([kb goals context {:keys [bound consequent-pred est-override]
                      :or   {bound #{}}}]
   (let [goals (vec goals)]
     (if (or (not *enabled*) (< (count goals) 2))
       goals
       (let [{:keys [gens recs defs]} (partition-literals goals consequent-pred)
             drop-i (fn [pending taken]
                      (let [taken (set (map first taken))]
                        (filterv (fn [[i _]] (not (taken i))) pending)))]
         (if (< (count gens) 2)
           ;; Nothing to choose between, but the deferred literals can still be
           ;; pulled forward past the recursive one.
           (let [bound' (into bound (mapcat (comp vars-of second) gens))
                 early  (ready defs bound')]
             (lits (concat gens early recs (drop-i defs early))))
           (let [count-at*  (memoizing p/count-at)
                 children*  (memoizing p/children)
                 with-arg*  (memoizing p/count-with-arg)
                 functor*   (memoizing p/count-with-functor)
                 opts       {:count-at count-at* :children children*
                             :count-with-arg with-arg* :count-with-functor functor*
                             :context context}
                 cost       (fn [g bnd]
                              (or (when est-override (est-override g bnd))
                                  (est-matches kb g bnd opts)))
                 ;; the generators, cheapest first with the cartesian factors held to
                 ;; the back; the deferred literals are threaded back through that
                 ;; order below, each at the point it becomes ready
                 ordered    (deferring-isolated-order
                             gens bound cost
                             (concat (lits recs) (lits defs)))]
             (loop [remaining ordered
                    bound     bound
                    pending   defs
                    acc       []]
               (if (empty? remaining)
                 (let [early (ready pending bound)]
                   (lits (concat acc early recs (drop-i pending early))))
                 (let [[_ l :as pick] (first remaining)
                       bound'         (into bound (vars-of l))
                       early          (ready pending bound')]
                   (recur (rest remaining)
                          bound'
                          (drop-i pending early)
                          (into (conj acc pick) early))))))))))))

(defn explain
  "The plan as data: each literal in execution order with the estimate it was chosen
  on and the variables bound when it runs.  What `core/query-plan` reports for a
  conjunction, and the way to see *why* an order was chosen rather than just what it
  was.

  Three flags, because a literal's position is decided by one of three different
  things and a plan is only diagnosable if it says which.  `:deferred?` and
  `:recursive?` mark the operational pins.  **`:isolated?` marks a cartesian factor
  that was held to the back** for being one — read it as the answer to \"why is this
  last\", not as a structural property of the literal.  Without it a selective one
  reads as a small number sitting last, which looks like the planner erred; it is the
  one position the estimate beside it does not account for.  A literal sharing no
  variable but matching at most once is *not* flagged, because it is not held back:
  `cartesian-factors` says why, and a flag that disagreed with the order it explains
  would be worse than no flag.

  The flag is computed under the same guards `order` plans under, so a conjunction
  short enough to be returned untouched reports nothing as held back — there being
  nowhere to hold it."
  ([kb goals context] (explain kb goals context {}))
  ([kb goals context opts]
   (let [ordered  (order kb goals context opts)
         bound0   (or (:bound opts) #{})
         override (:est-override opts)
         cost     (fn [g bnd] (or (when override (override g bnd))
                                  (est-matches kb g bnd {:context context})))
         {:keys [gens recs defs]} (partition-literals goals (:consequent-pred opts))
         iso     (if (and *enabled* (>= (count goals) 2) (>= (count gens) 2))
                   (cartesian-factors gens (lits (concat recs defs)) bound0 cost)
                   #{})
         iso?    (set (keep (fn [[i l]] (when (iso i) l)) gens))]
     (first
      (reduce (fn [[acc bound] g]
                [(conj acc {:goal         g
                            :est-matches  (est-matches kb g bound {:context context})
                            :bound-before bound
                            :deferred?    (boolean (deferred? g))
                            :recursive?   (boolean (recursive-in? g (:consequent-pred opts)))
                            :isolated?    (contains? iso? g)})
                 (into bound (vars-of g))])
              [[] bound0]
              ordered)))))
