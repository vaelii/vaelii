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

  ## Two estimators, two contracts

  Both read the count-aware trie and neither fetches a record, but they answer
  different questions and are not interchangeable:

  - **`est-matches`** is a sound *upper bound* on how many facts one literal matches.
    Its one-sided guarantee is required — an estimate of 1 is a **proof** that a
    literal matches at most once, and therefore cannot fan the plan out — and that
    proof is what the placement rules below rest on.  It says nothing usable about
    how two literals combine: maxima of products do not factor.
  - **`est-rows`** is an *expected* cardinality, with the distinct-value count of each
    variable beside it, and is explicitly allowed to be wrong in both directions.
    That is the property that makes it compose — expectations of products do factor
    under independence — so it is the quantity a join is costed in.

  A **summary** is what `est-rows` returns and what the planner threads through its
  fold: `{:rows 400 :vars #{?x ?y} :distinct {?x 20}}`.  A variable in `:vars` and
  absent from `:distinct` is one the index cannot count, which the join formula reads
  as 1 — so `max(d_A(v), d_B(v))` defers to whichever side of the join *can* count it.

  ## Three mechanisms

  **Selectivity** — the count-aware trie answers \"how many facts are under this
  path prefix\" in O(1) (`count-at`), \"how many distinct values sit at the next
  level\" in O(1) too (`count-children`, which is its own read rather than
  `(count (children …))` — that one materializes the child set, so asking it once per
  literal makes planning a fixed conjunction scale with the KB), and the secondary
  argument roots answer \"how many facts
  have this term at position n\" (`count-with-arg`) for the ground arguments the trie
  cannot reach.  Both estimators read those and nothing else: there is **no statistics
  table**, and there is not to be one, because a second source of truth about
  cardinality would need maintaining on every write.

  Every one of those counts **spans all contexts**, since the trie key ends with the
  context and no prefix the walk builds reaches past the arguments.  A read is scoped to
  one context and the `genlCx` ancestor set above it, so the counts are an over-estimate by
  a sentence's context multiplicity — which leaves `est-matches` sound (an ancestor set is a
  subset of what is stored, so the bound can only be too large) and puts the error on
  `est-rows`'s `:rows` alone, `:distinct` sitting a level above the contexts.  A ground
  literal is clamped to one row and never sees it.  `docs/inference.md` states the size
  of it; `context` reaches the estimators only for the subtype fan below.

  **Sideways information passing** — a literal's cost is not fixed, it depends on
  what is already bound when it runs.  `(parentOf ?x ?y)` is the whole extent of
  `parentOf`; the same literal after `?x` is bound is one person's children.  In the
  summary algebra that is not a special case: the variables already bound are a
  one-row relation, and joining a literal onto it divides its extent by the literal's
  own distinct count at that position — the textbook N/V selectivity, reached by the
  general rule instead of by a rule of its own.

  It lives there and **only** there.  The per-literal model does not narrow on a
  binding, because `est-matches` is a bound and a binding buys an *average*: a bound
  variable takes one value, and the value it takes may be the one the whole prefix sits
  under.  Charging the average per literal would put an expectation where the placement
  rules read a proof (`prefix-estimate`).

  **Blocks, on structure rather than on cost** — two literals sharing a variable
  constrain each other; two that share none do not, and no ordering *within* one
  group changes what the other costs.  So the generators are split into connected
  components (`components`), the split is exact and free because it is read off the
  conjunction, and the estimate is then asked only the two questions it can answer:
  which literal to take next *inside* a block, and which block to run first.

  ## Ordering the blocks

  A block that produces `n` rows at internal intermediate cost `s`, placed after a
  prefix of `P` rows, costs `P·s`; run before another block it also multiplies that
  one by `n`.  Two blocks therefore compare by adjacent transposition —

      cost[i,j] = P·(sᵢ + nᵢ·sⱼ)   against   cost[j,i] = P·(sⱼ + nⱼ·sᵢ)
      i first  ⟺  sᵢ/(nᵢ−1) ≥ sⱼ/(nⱼ−1)

  — so a **descending sort on `s/(n−1)`** is optimal, in O(k log k) and with no
  search.  It degenerates correctly, which is the check that it is the right law: a
  single-literal block has `s = n`, so its ratio `n/(n−1)` decreases in `n` and the
  law reduces to taking the smallest extent first; a block of one row ranks `+∞` and
  leads; a block of none would make the ratio change sign, so `n ≤ 1` is ranked first
  structurally rather than by the formula.

  A block's literals run consecutively, which is an assumption rather than a theorem —
  interleaving two blocks is a legal plan the law does not consider — and it is measured
  rather than asserted: on a conjunction of two disconnected pairs the contiguous plan is
  the cheapest of all twenty-four permutations, interleaved ones included.

  Two placements sit outside the law, and both are claims the estimate cannot make:

  - **A block that cannot multiply runs first.**  `est-matches` bounds each literal
    from above, so a block whose literals each bound to 1 is *proved* to match at most
    once: it can only prune, never fan out, and belongs wherever it is cheapest, which
    is first.  The case that makes this required is the **ground** literal —
    `(dog Bob)` once a rule's bindings are substituted in, the shape both chaining
    paths hand the planner.  It has no variables, so it is a block of its own with
    nothing to share; held back, a false one costs the entire join to reach a test
    that refutes it in one lookup.
  - **The anchored block runs before the rest.**  Every component touching the
    already-bound variables, a deferred (evaluable) literal or the recursive literal
    is fused into one component, and that one leads.  It is the only block the pins
    reach: its literals feed the evaluables, which prune, and are narrowed by bindings
    the caller already has — neither of which the summary algebra models, since an
    evaluable's selectivity is a function of values rather than of counts.  Running it
    first is what makes those prunes land before another block multiplies them.

  ## Why a sort and not a search

  Costing whole orders — the sum of a plan's intermediate row counts, minimized by a
  subset search — is refuted over `est-matches`, and measurably: on randomized joins
  it ran a mean 2.31× the best permutation's actual rows against cheapest-first's
  1.19×, losing 3 trials of 9 and winning none.  The reason is not that a search is
  the wrong shape but that it minimizes the wrong quantity: `est-matches` is a
  *bound*, one-sided by contract, and a plan's cost is a sum of expected intermediate
  sizes.  Maxima of products do not factor, so summing bounds across a join adds numbers
  that answer a different question than the one being minimized.  `est-rows` exists to
  fix that, and once the numbers compose the ordering does not need a search at all: the
  transposition law sorts.

  ## Why the subtype fan is made cheap rather than remembered

  One branch of `est-matches` is not an O(1) index read: a **unary type literal** sums an
  estimate over the type's whole subtype closure, and `order` asks for it once per pick.
  `memoizing` collects the repeated *index reads* inside one plan, so a subtype counted on
  the first pick is not counted again — but it wraps the reads and not `est-matches`, and
  `greedy-block` re-costs every remaining literal on every pick.  So what is left is one
  fan per pick, per plan, per firing attempt: the traversal and its per-subtype
  allocation stay, and only the store traffic under them collapses.  That is the number
  the section below is written against.

  It is made cheap **by construction** rather than cached: for the structure that costs, the
  argument a bare open variable, the general walk is provably `count-at [t']` per subtype
  and `fan-of-roots` reads exactly that (see the section above it).  That halves the fan
  — 13.2% of a forward chaining run at 364 subtypes down to 6.8% (`lein bench-hotreads`)
  — while the number it returns cannot move, which is the only kind of change this
  estimate admits.

  **Remembering the answer does not work**, and both halves of why are measured rather
  than argued.  A cache stamped with `observe/change-clock` is retired between one plan
  and the next by the chaining run's own placements, and turning one on measures
  **0.98–0.99×** there.  On a query, where nothing moves the clock and every plan after
  the first would be served, the fan is under 3% of the run — 120 estimates against a
  search that dominates them, where chaining makes 901 — and it measures **0.91–1.04×**.
  So the entry is either invalid or not worth having, by path.

  A **finer** stamp is what would reach it, and it is unsound rather than merely fiddly:
  the estimate bounds a literal from *above*, an estimate of 1 is a proof `rank-blocks`
  and `cartesian-factors` rest on, and a fact placed under one subtype makes an entry
  computed before it too small.  Reaching this cost again means making the fan cheaper
  again — a count maintained per closure, say — not holding its answer for longer.

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

  Every number in the decision is derived from the conjunction and the KB's counts,
  and ties break on the literal's original position — so a plan is a function of
  content, never of iteration order.  Same knowledge, same plan: the order
  independence the rest of the engine holds to (see `vaelii.impl.jtms`) applied to
  execution rather than belief."
  (:require [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the cost model -----------------------------------------------------

(def ^:dynamic *enabled*
  "Bind to false to run a conjunction's generators in the order they were written.

  Ranking them is a pure cost decision — it must never change the answer *set*, only
  how fast it is reached — and that is a claim worth being able to test rather than
  assert.  Binding this false gives the unranked execution to compare against, which is
  what `plan_test` does over every permutation of a conjunction and what
  `VAELII_PLAN=0` does over the whole suite (docs/inference.md).

  **What it does not turn off is the readiness discipline**, and that is the line
  between the two decisions `plan-pairs` makes.  A deferred literal placed ahead of
  what binds its arguments cannot be evaluated at all — `[(big_enough ?n) (hasScore ?x
  ?n)]` answers nothing, silently — and the recursive literal placed anywhere but last
  is a rule that may not terminate.  Neither is a cost, so neither is behind this
  switch: it removes the ranking and leaves the order legal."
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
        (negative? goal)         (recur (second goal))
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
  times per plan for a hit that should cost a hash lookup and little else.  Nesting keys
  on the arguments as they are, so a hit allocates one `MapEntry` (`find`, to tell a
  cached nil from a miss) rather than a key tuple *and* an entry — the point of not going
  variadic being that the key is free, not that the lookup is."
  [f]
  (let [cache (volatile! {})]
    (fn
      ([a b]
       (if-let [e (find (get @cache a) b)]
         (val e)
         (let [v (f a b)] (vswap! cache update a assoc b v) v)))
      ([a b c]
       (if-let [e (find (get-in @cache [a b]) c)]
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

  Two cases per token, and the walk stops at the first token that is not a literal
  value, because the trie narrows left to right and cannot skip a level:

  - **known value** — extend the prefix and take `count-at` of it.  Exact, not an
    estimate, for everything matching that prefix.
  - **anything else** — a variable, whether or not the plan has bound it: nothing
    constrains this position or any after it, so the prefix count stands.

  **A bound-but-unknown token is not charged an average**, and that is the whole of
  what keeps `est-matches` one-sided.  `count-at(prefix) / count-children(prefix)` is
  the branch a bound variable takes *on average*, and a bound variable does not take
  the average — it takes one value, and the value it takes may be the one the whole
  prefix sits under.  Three facts over two first arguments read an average of 1 while
  the busy argument matches twice, so a `:prune?` proof off that number would be a
  proof of something false (`plan_test`, `a-bound-token-is-not-charged-an-average`).
  The narrowing a binding really buys is priced where it composes instead:
  `join-summary` divides the literal's extent by its own distinct count at that
  position, which is the same N/V selectivity by the general rule rather than by a
  rule of its own."
  [ix goal count-at*]
  (loop [toks (sx/key-stream goal), prefix []]
    (if (empty? toks)
      (count-at* ix prefix)
      (let [t (first toks)]
        (if (known? t)
          (recur (rest toks) (conj prefix t))
          (count-at* ix prefix))))))

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

;; ---- the subtype fan, walked once per subtype and no more ----------------
;;
;; Every branch of `est-matches` is a handful of O(1) index reads except the unary type
;; one, which runs `prefix-estimate` **per subtype** — and that is the branch the broad
;; antecedent this namespace's docstring names goes down.  `specs` is memoized on the
;; taxonomy generation so the closure's *fetch* is O(1); what is not O(1) is the fan over
;; it, and `order` asks for it once per pick, per plan, per firing attempt.
;;
;; For the structure that actually costs — `(animal ?x)`, the argument a bare free variable —
;; the general walk is provably a long way round to one number.  `sx/key-stream` of
;; `(t' ?x)` is two tokens: the functor, which is known and extends the prefix, and the
;; variable, which is not a value and stops the walk.  So `prefix-estimate` returns
;; `count-at [t']` and nothing else — after building a literal, linearizing it, and
;; testing each token, per subtype.  `fan-of-roots` reads the same counts directly.
;;
;; It is a **constant-factor** change and has to be: the number must not move at all, and
;; the equality above is why it cannot.  Any other argument shape — a compound, which puts
;; its own tokens on the prefix, or a partly-bound one, which turns on what `bound` holds
;; — takes the general walk, because for those the prefix genuinely is deeper than `[t']`.

(defn- open-atom?
  "Is `term` a bare variable this literal leaves open — an atom (so it contributes exactly
  one trie token) and a variable (so the token is not a value, and the walk stops there)?
  The conditions under which `prefix-estimate` over `(t term)` is exactly `count-at [t]`.

  A variable the plan has already **bound** satisfies the equality too — the walk stops on
  a bound token exactly as on a free one — and is excluded here all the same: widening the
  fast path is a cost decision, and this predicate is written to name the form the
  direct read was measured on rather than every shape it would also answer."
  [term bound]
  (and (sx/variable? term)
       (not (sequential? term))
       (not (contains? bound term))))

(defn- fan-of-roots
  "The subtype closure's summed extent: `count-at [t']` per subtype, added.  What the
  general walk computes for an open atom argument, without building a literal per subtype
  to discover it."
  [ix specs count-at]
  (reduce (fn [acc t'] (+ acc (long (count-at ix [t'])))) 0 specs))

(defn est-matches
  "Estimated number of stored facts a literal matches, given the variables already
  `bound`.  This is the literal's fan-out — the number by which it multiplies the
  cost of everything sequenced after it.

  Every input is an *upper* bound on the true match count, so the minimum of them is
  the tightest bound available without touching a record.  That one-sidedness is the
  contract: this number may be far too large and may never be too small, so a reading
  of 1 **proves** the literal cannot fan out, which is the only claim the placement
  rules take from it.  For how much a literal fans out — a quantity that has to
  compose across a join — see `est-rows`, which is the other estimator and is not a
  bound."
  ([kb goal bound] (est-matches kb goal bound {}))
  ;; `:count-children` is part of the shared estimator-option map and is read by
  ;; `summary` rather than here: the child count is the *distinct-value* reading a join
  ;; divides by, and this estimator no longer charges one (see `prefix-estimate`).
  ([kb goal bound {:keys [count-at count-with-arg count-with-functor context]
                   :or   {count-at           reads/stored-count-at
                          count-with-arg     reads/stored-count-with-arg
                          count-with-functor reads/stored-count-with-functor}}]
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
       (let [[t a] goal
             ;; the same scoped fan the matcher will walk (`res/sub-predicates`): an
             ;; invisible subtype contributes no matches, so it must contribute no cost
             specs (tax/specs (reasoning/taxonomy kb) t context)]
         (min unbounded
              (if (open-atom? a bound)
                (fan-of-roots ix specs count-at)
                (reduce (fn [acc t']
                          (+ acc (prefix-estimate ix (list t' a) count-at)))
                        0
                        specs))))

       :else
       (min (prefix-estimate ix goal count-at)
            (or (arg-root-estimate ix goal count-with-arg) unbounded))))))

;; ---- the join model: summaries, and how two of them compose -------------
;;
;; Rows and distinct counts are carried as **doubles** throughout the algebra, and the
;; reason is the divisions rather than overflow — a product of two unbounded literals
;; is 1e18, which a long holds.  A divisor is a ratio and not a count, and truncating
;; one collapses exactly the small cases the ordering law turns on: `s/(n−1)` reads 2
;; for a two-row block and 1.5 for a three-row one, and in integers both read 1.
;; `est-rows` rounds at the boundary, so nothing outside this section sees a float.

(def ^:private empty-prefix
  "The empty plan prefix: one row of nothing.  Joining a literal onto it shares no
  variable and divides by nothing, so it yields the literal — which is what makes the
  first pick of a block a special case of the general rule rather than one of its
  own."
  {:rows 1.0 :vars #{} :distinct {}})

(defn- bound-prefix
  "The variables a conjunction starts with, as a summary: one row, each of them
  taking exactly one known value.  Joining a literal onto *this* divides its extent by
  its own distinct count at that variable's position — the N/V selectivity a per-literal
  model would charge as an average, arrived at by the general rule, which is why sideways
  information passing needs no rule of its own anywhere.  **Here and nowhere else**: this
  is an expectation, and `est-matches` stays a bound rather than charging the same
  narrowing a second time in a quantity that may not carry it (`prefix-estimate`)."
  [bound]
  {:rows 1.0 :vars (set bound) :distinct (zipmap bound (repeat 1.0))})

(defn- cap-distinct
  "No column has more distinct values than its relation has rows."
  [dist rows]
  (reduce-kv (fn [m v d] (assoc m v (min (double d) rows))) {} dist))

(defn- proxy-distinct
  "A relation's own reading of its most duplicated column, or nil if it has none.

  Used only where a join variable is counted on *neither* side, and used as the
  smaller of the two relations' — see `join-summary`."
  [s]
  (let [ds (vals (:distinct s))]
    (when (seq ds) (double (reduce min ds)))))

(defn- join-summary
  "The summary of `a ⋈ b`, joined on every variable the two have in common.

      rows(A ⋈ B) = rows(A) · rows(B) ÷ Π d(v)    over shared v
             d(v) = max(d_A(v), d_B(v))           over whichever are read

  **A count the trie read beats one inferred**, and that two-tier rule is what makes
  the model work on a chain.  `d(v)` is the larger of the counts the two sides
  actually read — larger, because a join cannot group more finely than the coarser
  side allows — and in `(p ?a ?b) ⋈ (q ?b ?c)` only `q` can read `?b`, since on `p`
  it sits behind a free position the trie walk stops at.  Taking the maximum over
  *read* counts alone is what lets the side that knows decide.

  Where **neither** side read the variable the model would otherwise divide by
  nothing and call a join a cartesian product, which is the error that compounds
  fastest with depth: a chain joined on a trailing position at both ends hits it at
  every step.  So it falls back on a proxy — the smaller of the two relations' own
  most-duplicated readings (`proxy-distinct`), and 1 where neither has one.  The
  smaller, because a proxy is a guess and an over-large divisor understates a join,
  which is the direction that puts an exploding literal early.

  The distinct counts are propagated, and that step is what makes a *second* join
  possible rather than a product:

      d(v) = min(d_A(v), d_B(v))       for a shared v, over whichever are read
      d(u) = min(d_A(u), rows(A ⋈ B))  otherwise — a column cannot have more distinct
                                       values than its relation has rows

  A variable neither side read stays unread rather than being invented at `rows`: a
  fabricated count would rank as a reading in the next join and throw away the one
  the other side actually has."
  [a b]
  (let [va (:vars a), vb (:vars b)
        da (:distinct a), db (:distinct b)
        pa (proxy-distinct a), pb (proxy-distinct b)
        guess   (max 1.0 (cond (and pa pb) (min pa pb) pa pa pb pb :else 1.0))
        shared  (filter vb va)
        divisor (reduce (fn [acc v]
                          (let [ka (get da v), kb (get db v)]
                            (* acc (max 1.0 (double (cond (and ka kb) (max ka kb)
                                                          ka ka
                                                          kb kb
                                                          :else guess))))))
                        1.0 shared)
        rows    (max 0.0 (/ (* (:rows a) (:rows b)) divisor))
        vars    (into (set va) vb)
        dist    (reduce (fn [m v]
                          (let [ka (get da v), kb (get db v)
                                k  (cond (and ka kb) (min ka kb) ka ka :else kb)]
                            (if k (assoc m v (min (double k) rows)) m)))
                        {} vars)]
    {:rows rows :vars vars :distinct dist}))

(defn- clamped-join
  "`prefix ⋈ literal`, with the sound per-literal bound applied on top.

  The two estimators say different things here and both are worth keeping.  The join
  formula assumes the literal's arguments are independent of the prefix's, which for
  a literal every one of whose variables the prefix already binds is simply false —
  it is a *test*, matching at most once per row, and `est-matches` proves that where
  the formula would still be dividing extents.  So the expected model composes and
  the bound clamps it, and the clamp can only ever shrink a reading."
  [prefix summary bound]
  (let [j   (join-summary prefix summary)
        cap (* (:rows prefix) (double bound))]
    (if (< cap (:rows j))
      (assoc j :rows cap :distinct (cap-distinct (:distinct j) cap))
      j)))

(defn- prefix-summary
  "Walk the literal against the trie exactly as `prefix-estimate` does, but return the
  relation's shape rather than one number: the row count under the deepest known
  prefix, and the distinct-value count of the variable sitting at the first position
  the walk cannot extend past.

  That variable is the only one the trie can count.  Past it the walk has stopped —
  the trie narrows left to right and cannot skip a level — so every later variable is
  left uncounted rather than guessed at, which `join-summary` reads as \"ask the other
  side\"."
  [ix goal count-at* kids*]
  (loop [toks (sx/key-stream goal), prefix []]
    (if (empty? toks)
      {:rows (double (count-at* ix prefix)) :distinct {}}
      (let [t (first toks)]
        (if (known? t)
          (recur (rest toks) (conj prefix t))
          ;; the trie narrows left to right, so the first token that is not a value is
          ;; where the walk ends — and it is a variable, since a marker carries none
          (let [rows (double (count-at* ix prefix))
                d    (double (kids* ix prefix))]
            {:rows rows
             :distinct (if (and (sx/variable? t) (pos? d)) {t (min d rows)} {})}))))))

(defn- self-join-factor
  "How much a variable repeated *inside* one literal narrows it.

  `(marriedTo ?x ?x)` is not the extent of `marriedTo`: the second occurrence is an
  equality between two positions, which is a join the literal makes with itself and
  the same formula prices.  Each occurrence past the first divides by the variable's
  distinct count — the trie's reading where it has one, and the literal's own
  most-duplicated reading as the proxy where it does not, exactly as `join-summary`
  falls back.  Without this a reflexive literal is costed at its whole relation, which
  is the single largest over-estimate the walk can make, since the true count is
  usually a handful of rows."
  [goal dist]
  (let [freq  (frequencies (filter sx/variable? (sx/key-stream goal)))
        proxy (or (some->> (vals dist) seq (reduce min) double) 1.0)]
    (reduce-kv (fn [acc v n]
                 (if (> n 1)
                   (* acc (Math/pow (max 1.0 (double (get dist v proxy))) (dec n)))
                   acc))
               1.0 freq)))

(defn- summary
  "`est-rows` in the algebra's own units — doubles, and `:vars` present."
  [kb goal {:keys [count-at count-children count-with-arg count-with-functor context]
            :or   {count-at           reads/stored-count-at
                   count-children     reads/stored-count-children
                   count-with-arg     reads/stored-count-with-arg
                   count-with-functor reads/stored-count-with-functor}}]
  (let [ix   (:index kb)
        ;; A deferred literal is computed from bindings, not looked up: it produces no
        ;; rows of its own, joins on nothing, and multiplies nothing.  How much it
        ;; *prunes* is a function of values rather than of counts, so the model
        ;; declines to guess and reads it as transparent — one row over no columns,
        ;; which any prefix joins with unchanged.  That is also why the block feeding
        ;; one is placed by the anchor rule and not by the transposition law: the law
        ;; would be ranking it on a selectivity the model has just declined to state.
        vs   (if (sx/deferred-literal? goal) #{} (vars-of goal))
        base (cond
               (not (sequential? goal)) {:rows 1.0 :distinct {}}

               (sx/deferred-literal? goal) {:rows 1.0 :distinct {}}

               ;; The three shapes the trie cannot walk at all — a negative literal
               ;; (keyed under [:false …]), a dotted rest (no fixed positions), an open
               ;; functor (no functor root).  `est-matches`'s fallbacks give the row
               ;; count; no column is counted, so a join with one of these divides by
               ;; whatever the other side knows and by nothing otherwise.
               (or (negative? goal) (dotted? goal) (variable-functor? goal))
               {:rows (double (est-matches kb goal #{}
                                           {:count-at count-at :count-children count-children
                                            :count-with-arg count-with-arg
                                            :count-with-functor count-with-functor
                                            :context context}))
                :distinct {}}

               ;; A unary type literal is the union of its subtype closure's extents,
               ;; so the rows sum; the distinct counts sum too and are then capped,
               ;; since two subtypes may share an instance but cannot have more between
               ;; them than the union has rows.
               (unary-literal? goal)
               (let [[t a] goal
                     parts (mapv #(prefix-summary ix (list % a) count-at count-children)
                                 (tax/specs (reasoning/taxonomy kb) t context))
                     rows  (min (double unbounded) (reduce + 0.0 (map :rows parts)))]
                 {:rows rows
                  :distinct (cap-distinct (apply merge-with + {} (map :distinct parts)) rows)})

               :else
               (let [p    (prefix-summary ix goal count-at count-children)
                     a    (arg-root-estimate ix goal count-with-arg)
                     rows (if a (min (:rows p) (double a)) (:rows p))
                     f    (self-join-factor goal (:distinct p))
                     rows (if (and (> f 1.0) (>= rows 1.0)) (max 1.0 (/ rows f)) rows)]
                 {:rows rows :distinct (cap-distinct (:distinct p) rows)}))
        ;; A literal with no variables yields one solution or none, whatever the trie
        ;; counts under it — the same sentence may be stored in several contexts, and
        ;; a read is scoped to one.
        rows (if (seq vs) (:rows base) (min 1.0 (:rows base)))]
    {:rows rows :vars vs :distinct (cap-distinct (:distinct base) rows)}))

(defn est-rows
  "The expected shape of the relation a literal denotes: how many rows it produces,
  and how many distinct values each of its variables takes over them.

      (est-rows kb '(parentOf ?x ?y))
      ;; => {:rows 400 :vars #{?x ?y} :distinct {?x 20}}

  This is the **other** estimator, and it is not `est-matches`.  That one is a sound
  upper bound and this one is a point estimate, wrong in both directions by design —
  which is the property that lets it compose, since expectations of products factor
  under independence where maxima of products do not.  Use `est-matches` to prove a
  literal cannot fan out; use this to say how much it does.

  `:distinct` holds only what the index can **count**.  The trie narrows left to
  right, so the one variable it counts exactly is the one at the first position the
  known prefix cannot extend past — `(parentOf Tom ?y)` counts `?y`, `(parentOf ?x ?y)`
  counts `?x` and leaves `?y` out.  A variable in `:vars` and absent from `:distinct`
  is uncounted, not zero, and the join formula reads it as the neutral 1 so that
  whichever side of a join *can* count a variable is the side that decides.

  There is deliberately no `bound` argument, and the asymmetry with `est-matches` is
  the point: a literal's own shape does not depend on what the plan has bound, and the
  narrowing that binding buys is what the join formula computes.  A planner seeds its
  prefix with the bound variables as a one-row relation and reads the narrowing off the
  join, by the general rule.  `est-matches` under the same bindings does **not** narrow,
  and must not: it is the one-sided quantity, and an average of the same narrowing there
  can read 1 for a literal that matches twice."
  ([kb goal] (est-rows kb goal {}))
  ([kb goal opts]
   (let [s     (summary kb goal opts)
         round (fn [^double d] (long (Math/round d)))]
     {:rows     (round (:rows s))
      :vars     (:vars s)
      :distinct (reduce-kv (fn [m v d] (assoc m v (round (double d)))) {} (:distinct s))})))

;; ---- ordering -----------------------------------------------------------

(defn- deferred? [l] (sx/deferred-literal? l))

(defn- recursive-in?
  "An antecedent whose functor is the rule's own consequent functor — the literal
  whose position decides whether the rule is right- or left-recursive."
  [l consequent-pred]
  (and consequent-pred (sequential? l) (= (first l) consequent-pred)))

;; ---- blocks: the components a conjunction falls into --------------------

(defn- reachable
  "Every literal index connected to `start` through a chain of shared variables."
  [start by-idx by-var]
  (loop [stack [start], seen #{}]
    (if-let [i (peek stack)]
      (if (seen i)
        (recur (pop stack) seen)
        (recur (into (pop stack) (mapcat by-var) (by-idx i)) (conj seen i)))
      seen)))

(defn- components
  "The generators split into connected components — two literals are in one component
  when they share a variable, transitively — with every component touching
  `anchor-vars` fused into a single **anchored** one.

  The split is structural: read off the conjunction, exact, and costing nothing,
  which is why it is made here rather than left to an estimate.  It gives the
  claim the cost model most needs and least deserves to be trusted with — that no
  ordering *inside* one component changes what another component costs — so the
  estimate is only ever asked to compare within a block, or to rank two whole blocks
  by the transposition law.

  A literal with no variables at all is a component of its own: it shares nothing with
  anything, including with the anchor, and being alone is what lets the \"cannot
  multiply\" rule take it to the front.

  Returns `[{:pairs [[i literal] …] :anchored? bool} …]` in written order, each
  block's pairs in written order too."
  [gens anchor-vars]
  (let [by-idx (into {} (map (fn [[i l]] [i (vars-of l)])) gens)
        by-var (reduce (fn [m [i vs]]
                         (reduce #(update %1 %2 (fnil conj #{}) i) m vs))
                       {} by-idx)
        touches? (fn [i] (boolean (some anchor-vars (by-idx i))))
        anchor   (reduce (fn [s [i _]]
                           (if (and (touches? i) (not (s i)))
                             (into s (reachable i by-idx by-var))
                             s))
                         #{} gens)
        block-of (fn [seen [i _]]
                   (cond (seen i)   nil
                         (anchor i) anchor
                         :else      (reachable i by-idx by-var)))]
    (loop [pending gens, seen #{}, out []]
      (if-let [[pr & more] (seq pending)]
        (if-let [idx (block-of seen pr)]
          (recur more (into seen idx)
                 (conj out {:pairs (filterv (comp idx first) gens)
                            :anchored? (= idx anchor)}))
          (recur more seen out))
        out))))

(defn- greedy-block
  "Order one block's literals by repeatedly taking the one whose join onto the prefix
  is smallest, and report what the block costs.

  Two numbers come back beside the order, and they are what the transposition law
  ranks blocks on: **`:n`**, the rows the block produces, and **`:s`**, the
  intermediate rows it passes through getting there — the sum of every prefix, which
  is what running it actually costs.  **`:prune?`** is the separate, *sound* claim
  that the block cannot multiply at all: every literal in it bounded to at most one
  match by `est-matches`, which the estimate cannot say and the bound can."
  [pairs prefix0 bound0 cost summary-of]
  (loop [remaining pairs, prefix prefix0, bound bound0, acc [], s 0.0, prune? true]
    (if (empty? remaining)
      {:pairs acc :n (:rows prefix) :s s :prune? prune?}
      (let [scored (map (fn [[i l :as pr]]
                          (let [b      (cost l bound)
                                joined (clamped-join prefix (summary-of pr) b)]
                            [(:rows joined) i pr joined b]))
                        remaining)
            ;; ties resolve to the literal the caller wrote first
            [rows _ pick joined b] (first (sort-by (fn [[r i]] [r i]) scored))]
        (recur (filterv #(not= (first %) (first pick)) remaining)
               joined
               (into bound (vars-of (second pick)))
               (conj acc pick)
               (+ s rows)
               (and prune? (<= b 1)))))))

(defn- rank-blocks
  "The blocks in execution order, and the rule is three-tiered because three different
  kinds of claim decide a block's place.

  1. **A block that cannot multiply, first.**  `:prune?` is a proof off `est-matches`,
     not an estimate: every literal in the block matches at most once, so the block can
     only shrink what follows it and costs one lookup to do so.  A false ground literal
     belongs here and this is the tier that puts it there.
  2. **The anchored block next.**  It holds every literal the pins and the caller's
     bindings reach, and both are selectivity the summary algebra does not model — an
     evaluable prunes on values, and a bound variable narrows a literal the block's own
     `n` already accounts for but a rival block's does not.
  3. **Everything else by the transposition law**, `s/(n−1)` descending, with `n ≤ 1`
     ranked `+∞` so it leads (and `n = 0`, where the formula would change sign, with
     it).

  Ties inside every tier break on the block's earliest literal, so the whole ranking
  is a function of the conjunction and the counts."
  [planned]
  (let [ratio (fn [{:keys [n s]}]
                (if (<= n 1.0) Double/POSITIVE_INFINITY (/ s (- n 1.0))))]
    (concat (->> planned (filter #(and (not (:anchored? %)) (:prune? %)))
                 (sort-by (juxt :n :at)))
            (filter :anchored? planned)
            (->> planned (remove :anchored?) (remove :prune?)
                 (sort-by (fn [b] [(- (ratio b)) (:at b)]))))))

(defn- block-order
  "Order the generators: split them into blocks, order each block internally, rank the
  blocks, and concatenate.

  Returns `{:pairs [[i literal] …] :info {i {:block n :anchored? bool :isolated? bool}}}`
  — the order to run, and why each literal is where it is, so `explain` reports the
  decision that was made rather than one recomputed beside it."
  [gens bound0 cost summary-of anchor-vars]
  (let [blocks  (components gens anchor-vars)
        planned (mapv (fn [{:keys [pairs anchored?]}]
                        (assoc (greedy-block pairs
                                             (if anchored? (bound-prefix bound0) empty-prefix)
                                             (if anchored? bound0 #{})
                                             cost summary-of)
                               :anchored? anchored?
                               :at (reduce min (map first pairs))))
                      blocks)
        ranked  (rank-blocks planned)]
    {:pairs (into [] (mapcat :pairs) ranked)
     :info  (into {} (map-indexed
                      (fn [b {:keys [pairs anchored? prune?]}]
                        (into {} (map (fn [[i _]]
                                        [i {:block b
                                            :anchored? anchored?
                                            ;; the answer to "why is this last": a
                                            ;; literal sharing no variable with
                                            ;; anything else, ranked behind a block
                                            ;; that does.  A block that leads was not
                                            ;; held back, so it is not flagged.
                                            :isolated? (and (not anchored?)
                                                            (not prune?)
                                                            (= 1 (count pairs))
                                                            (pos? b))}]))
                              pairs)))
                  ranked)}))

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
  "The deferred literals whose **input** variables are all bound — pull them forward to
  here, in their original relative order (one computation may feed the next).

  Gated on the inputs a literal reads (`sentex/deferred-input-vars`), not on every
  variable it mentions: `(evaluate ?z (+ ?x ?y))` is ready once `?x` and `?y` are bound,
  and its own written `?z` is never generator-bound, so gating on it would strand the
  literal in the tail — after the pinned recursive literal — where the docstring above
  says it must be pulled forward, and a bind-mode `evaluate` parked there can cost the
  recursive subgoal its per-level distinctness."
  [defs bound]
  (filterv (fn [[_ l]] (every? bound (sx/deferred-input-vars l))) defs))

(defn- lits [pairs] (mapv second pairs))

(defn- memo-opts
  "The estimator options for one plan: the four index reads behind a `memoizing`
  cache each, plus the context.  One cache for the life of a plan — and for the
  `explain` that reports it, which re-costs every literal and would otherwise re-read
  each subtype's count the ranking already paid for."
  [context]
  {:count-at           (memoizing reads/stored-count-at)
   :count-children     (memoizing reads/stored-count-children)
   :count-with-arg     (memoizing reads/stored-count-with-arg)
   :count-with-functor (memoizing reads/stored-count-with-functor)
   :context            context})

(defn- plan-pairs
  "The whole ordering decision, once: the conjunction's literals in execution order as
  `[index literal]` pairs, beside the per-generator record of which block placed each
  one.  `order` takes the literals off it and `explain` reports the rest, so the two
  cannot drift — a flag computed beside the plan rather than with it can claim a
  literal was placed by a rule that did not run.  `:opts` is the memoized estimator
  set the ranking read through, when it ran one, so `explain` costs its report off the
  same cache rather than the index again."
  [kb goals context {:keys [bound consequent-pred est-override] :or {bound #{}}}]
  (let [goals (vec goals)]
    (if (< (count goals) 2)
      {:pairs (vec (map-indexed vector goals)) :info {}}
      (let [{:keys [gens recs defs]} (partition-literals goals consequent-pred)
            drop-i (fn [pending taken]
                     (let [taken (set (map first taken))]
                       (filterv (fn [[i _]] (not (taken i))) pending)))]
        ;; `*enabled*` false lands here too, and that is the whole of what it turns
        ;; off: the RANKING below.  The partition and the readiness discipline run
        ;; either way, because they are not cost — a deferred literal ahead of what
        ;; binds it cannot be evaluated at all, so leaving one there answers nothing
        ;; and a switch that did leave one there would be changing the answer set.
        (if (or (not *enabled*) (< (count gens) 2))
          ;; Nothing to choose between — or nothing allowed to — so the generators
          ;; keep the order they were written in, and the deferred literals are still
          ;; pulled forward past the recursive one.
          (let [bound' (into bound (mapcat (comp vars-of second) gens))
                early  (ready defs bound')]
            {:pairs (vec (concat gens early recs (drop-i defs early))) :info {}})
          (let [opts       (memo-opts context)
                cost       (fn [g bnd]
                             (or (when est-override (est-override g bnd))
                                 (est-matches kb g bnd opts)))
                ;; A literal's own shape does not depend on the bindings in hand, so
                ;; unlike `cost` it is computed once per literal rather than once per
                ;; pick — which is what keeps a richer estimate off the O(k²) path.
                ;; An override reports a row count and nothing about columns, so its
                ;; summary counts none of them and every join with it defers to the
                ;; other side, which is the fan-out the override exists to report.
                summaries  (volatile! {})
                summary-of (fn [[i l]]
                             (or (get @summaries i)
                                 (let [s (if-let [e (when est-override (est-override l bound))]
                                           {:rows (double e) :vars (vars-of l) :distinct {}}
                                           (summary kb l opts))]
                                   (vswap! summaries assoc i s)
                                   s)))
                {:keys [pairs info]} (block-order gens bound cost summary-of
                                                  (into (set bound)
                                                        (mapcat (comp vars-of second))
                                                        (concat recs defs)))]
            (loop [remaining pairs
                   bound     bound
                   pending   defs
                   acc       []]
              (if (empty? remaining)
                (let [early (ready pending bound)]
                  {:pairs (vec (concat acc early recs (drop-i pending early))) :info info
                   :opts  opts})
                (let [[_ l :as pick] (first remaining)
                      bound'         (into bound (vars-of l))
                      early          (ready pending bound')]
                  (recur (rest remaining)
                         bound'
                         (drop-i pending early)
                         (into (conj acc pick) early)))))))))))

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
  ([kb goals context opts]
   (lits (:pairs (plan-pairs kb goals context opts)))))

(defn explain
  "The plan as data: each literal in execution order with what it was costed at, the
  variables bound when it runs, and the reason it is where it is.  What
  `core/query-plan` reports for a conjunction, and the way to see *why* an order was
  chosen rather than just what it was.

  Three numbers, because the decision turns on three:

  - **`:est-matches`** — the sound upper bound on this literal's own fan-out, under
    the bindings in hand.  What proves a literal cannot multiply.
  - **`:est-rows`** — the expected size of the relation the literal denotes, on its
    own and irrespective of the plan.  What a join is costed in.
  - **`:est-prefix`** — the model's expected row count for the whole plan up to and
    including this literal.  This is the number the ordering actually turned on, and
    the one to read a surprising plan against: a literal placed early on a small
    `:est-matches` whose `:est-prefix` then jumps is the cost model being wrong about
    a join rather than about a literal.

  And three flags, because a literal's position is decided by one of three different
  things and a plan is only diagnosable if it says which.  `:deferred?` and
  `:recursive?` mark the operational pins.  **`:isolated?` marks a cartesian factor
  that was held to the back** for being one — read it as the answer to \"why is this
  last\", not as a structural property of the literal.  Without it a selective one
  is indistinguishable from a small number sitting last, which looks like the planner erred; it is the
  one position the estimate beside it does not account for.  A literal sharing no
  variable but matching at most once is *not* flagged, because it is not held back,
  and neither is one whose block the ranking put first.

  **`:block`** is the rest of that answer, and the part `:isolated?` cannot give: the
  index of the block the literal was placed in, blocks running in the order shown. Two
  literals sharing a variable with each other and with nothing else are a cartesian
  block just as much as one literal is, and neither is `:isolated?`; the block number
  is what says they moved together.  It is nil wherever no block ranking ran — planning
  off, or fewer than two *reorderable* literals, which a two-literal conjunction reaches
  whenever one of them is an evaluable.  The deferred literal is still pulled forward
  there; what is absent is blocks for it to be pulled forward through.

  The flags are read off the plan that ran rather than recomputed beside it, so a
  conjunction returned untouched reports nothing as held back — there being nowhere to
  hold it — and none of them can name a rule that did not fire.  The three numbers are
  recomputed, since the plan keeps only the block-local prefixes it ranked on and these
  are threaded across the whole execution order; they are computed by the same two calls
  `plan-pairs` costs with, `:est-override` included, so a reported number and the number
  that chose the order are one cost model rather than two — and through the same
  memoized reads (`memo-opts`), so a unary type literal's subtype fan is counted once for
  the ranking and the report together, not once per call per literal."
  ([kb goals context] (explain kb goals context {}))
  ([kb goals context opts]
   (let [{:keys [pairs info] memo :opts} (plan-pairs kb goals context opts)
         bound0   (or (:bound opts) #{})
         est-opts (or memo (memo-opts context))
         ;; A deferred literal is not a generator, so `plan-pairs` never costs one and
         ;; never asks the override about one — and neither does this, or a literal the
         ;; model reads as transparent would report a fan-out it never has.
         override (when-let [f (:est-override opts)]
                    (fn [g bnd] (when-not (deferred? g) (f g bnd))))
         ;; otherwise mirroring `plan-pairs`: the bound is taken under the bindings in
         ;; hand and the summary under the caller's, and an override reports rows and
         ;; nothing about columns — so every join with it defers to the other side
         bound-of (fn [g bnd] (long (or (when override (override g bnd))
                                        (est-matches kb g bnd est-opts))))
         sum-of   (fn [g] (if-let [e (when override (override g bound0))]
                            {:rows (double e) :vars (vars-of g) :distinct {}}
                            (summary kb g est-opts)))]
     (first
      (reduce (fn [[acc bound prefix] [i g]]
                (let [s      (sum-of g)
                      bnd    (bound-of g bound)
                      ;; a deferred literal is a test on the rows in hand, never a
                      ;; source of them, so it clamps the prefix to itself — reading
                      ;; the trie for `lessThan` would zero it
                      joined (clamped-join prefix s (if (deferred? g) 1 bnd))
                      flag   (get info i)]
                  [(conj acc {:goal         g
                              :est-matches  bnd
                              :est-rows     (long (Math/round ^double (:rows s)))
                              :est-prefix   (long (Math/round ^double (:rows joined)))
                              :bound-before bound
                              :block        (:block flag)
                              :deferred?    (boolean (deferred? g))
                              :recursive?   (boolean (recursive-in? g (:consequent-pred opts)))
                              :isolated?    (boolean (:isolated? flag))})
                   (into bound (vars-of g))
                   joined]))
              [[] bound0 (bound-prefix bound0)]
              pairs)))))
