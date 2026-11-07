;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.plan
  "Conjunctive query planning: the order a conjunction's literals are solved in.

  Two estimators read the count-aware trie and fetch no record: `est-matches`, a sound
  upper bound on one literal's matches, and `est-rows`, an expected relation summary
  that composes across a join.  `order` splits the generators into blocks, orders each
  block on `est-rows`, ranks the blocks, and threads the deferred, recursive and
  waiting literals back in; `explain` reports the same decision.
  See docs/inference.md, \"Conjunctive query planning\"."
  (:require [vaelii.impl.budget :as budget]
            [vaelii.impl.graph :as graph]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the cost model -----------------------------------------------------

(def ^:dynamic *enabled*
  "Bind to false to run a conjunction's generators in written order, skipping the cost
  ranking.  The readiness discipline stays in force: deferred, waiting and computed
  literals still follow their binders, and the recursive literal still runs after the
  other generators.
  `VAELII_PLAN=0` installs false for the whole suite (docs/inference.md)."
  true)

(def unbounded
  "The estimate for a literal the index cannot bound.  A finite number rather than
  `Long/MAX_VALUE`, because the subtype fan sums estimates and a saturating sentinel
  would overflow.  An `:est-override` returning it marks a literal computed from its
  bindings (`provers/deferred-est`)."
  1000000000)

(defn- settled-when-run?
  "True when every variable in `term` is in `bound`.  Distinct from `sx/ground-term?`:
  a bound variable has a value at run time, but not one the planner can use as a trie
  prefix token."
  [term bound]
  (every? #(contains? bound %) (sx/form-vars term)))

(defn- negative? [goal]
  (and (sequential? goal) (seq goal) (= 'not (first goal))))

(defn- functor-of [goal]
  (cond (not (sequential? goal)) goal
        (negative? goal)         (recur (second goal))
        :else                    (first goal)))

(defn- variable-functor?
  "A literal whose functor is a variable, `(?type Muffet)`.  It names no predicate, so
  `est-matches` costs it by the argument roots alone."
  [goal]
  (and (sequential? goal) (seq goal) (sx/variable? (first goal))))

(defn- unary-literal? [goal]
  (and (sequential? goal) (= 2 (count goal)) (symbol? (first goal))
       (not (sx/variable? (first goal)))))

(defn- memoizing
  "Wrap the index read `f`, of arity 2 or 3, in a cache that lives for one plan.  A
  cached nil is served as an answer.  The arities are fixed and the cache nests one map
  level per argument, so a hit allocates one `MapEntry` and no key tuple."
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
  "The count under the deepest known prefix of `goal`'s token stream (`sx/key-stream`):
  the walk extends the prefix through each ground token and stops at the first
  variable, bound or free.  A bound variable is not charged the average branch, so the
  result stays an upper bound (`a-bound-token-is-not-charged-an-average`)."
  [ix goal count-at*]
  (loop [toks (sx/key-stream goal), prefix []]
    (if (empty? toks)
      (count-at* ix prefix)
      (let [t (first toks)]
        (if (sx/ground-term? t)
          (recur (rest toks) (conj prefix t))
          (count-at* ix prefix))))))

(defn- arg-root-estimate
  "The smallest argument-root count (`count-with-arg`) over `goal`'s ground arguments,
  or nil when none is ground.  Each count bounds the literal's matches from above.
  Arguments past a dotted rest marker have no position and are skipped."
  [ix goal count-with-arg*]
  (let [args   (rest (sx/positional goal))
        counts (keep-indexed (fn [i a] (when (sx/ground-term? a) (count-with-arg* ix (inc i) a)))
                             args)]
    (when (seq counts) (apply min counts))))

;; ---- the subtype fan ----------------------------------------------------
;; docs/inference.md, "What the subtype fan costs": for an open atom argument the walk
;; is `count-at [t']` per subtype, which `fan-of-roots` reads directly.

(defn- open-atom?
  "True when `term` is a variable the plan has not bound: the argument shape for which
  `prefix-estimate` over `(t term)` is `count-at [t]`.  A bound variable gives the same
  equality and is excluded, so the direct read covers the shape it was measured on."
  [term bound]
  (and (sx/variable? term)
       (not (sequential? term))
       (not (contains? bound term))))

(defn- fan-of-roots
  "The sum of `count-at [t']` over `specs`: the general walk's number for an open atom
  argument, read without building a literal per subtype."
  [ix specs count-at]
  (reduce (fn [acc t'] (+ acc (long (count-at ix [t'])))) 0 specs))

(defn est-matches
  "A sound upper bound on how many stored facts `goal` matches with the variables in
  `bound` bound.  The result may be too large and is never too small, so 1 proves the
  literal matches at most once.  `opts` overrides the index reads (`:count-at`,
  `:count-with-arg`, `:count-with-functor`) and gives the `:context` that scopes a
  unary type literal's subtype fan."
  ([kb goal bound] (est-matches kb goal bound {}))
  ;; `:count-children` belongs to the shared option map and is read by `summary`.
  ([kb goal bound {:keys [count-at count-with-arg count-with-functor context]
                   :or   {count-at           reads/stored-count-at
                          count-with-arg     reads/stored-count-with-arg-global
                          count-with-functor reads/stored-count-with-functor}}]
   (let [ix (:index kb)]
     (cond
       (not (sequential? goal)) 1

       ;; a literal with nothing left open is a test
       (settled-when-run? goal bound) 1

       ;; A negative literal keys under [:false <body>], so `count-at` answers 0.  The
       ;; predicate extent counts both polarities; for an open functor the argument
       ;; roots, which also span both polarities, are the only bound.
       (negative? goal)
       (let [body (second goal)]
         (if (variable-functor? body)
           (or (arg-root-estimate ix body count-with-arg) unbounded)
           (count-with-functor ix (functor-of goal))))

       ;; a dotted rest binds no position past its marker: the predicate extent, or nothing
       (sx/dotted? goal)
       (if (variable-functor? goal)
         unbounded
         (count-with-functor ix (functor-of goal)))

       ;; A unary type literal matches over its subtype closure, scoped to `context`
       ;; as the matcher's `res/sub-predicates` is.
       (unary-literal? goal)
       (let [[t a] goal
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
;; Rows and distinct counts are doubles throughout.  Truncating a divisor collapses the
;; small cases the ordering law turns on: `s/(n−1)` reads 2 for a two-row block and 1.5
;; for a three-row one, and 1 for both in integers.  `est-rows` rounds at the boundary.

(def ^:private empty-prefix
  "The empty plan prefix: one row over no variables.  Joining a literal onto it yields
  the literal's own summary."
  {:rows 1.0 :vars #{} :distinct {}})

(defn- bound-prefix
  "The summary of the variables `bound` at the start: one row, each variable taking one
  value.  Joining a literal onto it divides the literal's extent by its distinct count
  at that variable, the one place the planner prices a binding."
  [bound]
  {:rows 1.0 :vars (set bound) :distinct (zipmap bound (repeat 1.0))})

(defn- cap-distinct
  "No column has more distinct values than its relation has rows."
  [dist rows]
  (reduce-kv (fn [m v d] (assoc m v (min (double d) rows))) {} dist))

(defn- proxy-distinct
  "The smallest distinct count `s` read, or nil when it read none: the proxy divisor
  `join-summary` uses for a variable neither side counted."
  [s]
  (let [ds (vals (:distinct s))]
    (when (seq ds) (double (reduce min ds)))))

(defn- join-summary
  "The summary of `a ⋈ b`, joined on their shared variables, by the formulas under
  Composing them in docs/inference.md.  Each shared variable divides the product of the
  rows by the larger distinct count either side read, by the smaller `proxy-distinct`
  where neither side read the variable, and by 1 where neither side read any column.
  Each variable carries the smaller read count forward, capped at the join's rows.  A
  variable neither side read stays out of `:distinct`."
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
  "`prefix ⋈ summary`, its rows capped at `prefix rows × bound`, where `bound` is the
  literal's `est-matches`.  The cap applies where the join formula's independence
  assumption fails, as for a literal whose every variable the prefix binds."
  [prefix summary bound]
  (let [j   (join-summary prefix summary)
        cap (* (:rows prefix) (double bound))]
    (if (< cap (:rows j))
      (assoc j :rows cap :distinct (cap-distinct (:distinct j) cap))
      j)))

(defn- prefix-summary
  "`prefix-estimate`'s walk, returning `{:rows :distinct}`: the rows under the deepest
  known prefix, and the distinct count of the variable at the first position the walk
  stops at.  Every later variable is uncounted."
  [ix goal count-at* kids*]
  (loop [toks (sx/key-stream goal), prefix []]
    (if (empty? toks)
      {:rows (double (count-at* ix prefix)) :distinct {}}
      (let [t (first toks)]
        (if (sx/ground-term? t)
          (recur (rest toks) (conj prefix t))
          ;; the first non-value token, which is a variable: a marker carries none
          (let [rows (double (count-at* ix prefix))
                d    (double (kids* ix prefix))]
            {:rows rows
             :distinct (if (and (sx/variable? t) (pos? d)) {t (min d rows)} {})}))))))

(defn- self-join-factor
  "The divisor the variables repeated inside `goal` contribute: each occurrence past the
  first divides by the variable's distinct count in `dist`, or by the smallest count in
  `dist` where the variable has none.  `(marriedTo ?x ?x)` is the extent of `marriedTo`
  divided by `?x`'s distinct count."
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
                   count-with-arg     reads/stored-count-with-arg-global
                   count-with-functor reads/stored-count-with-functor}}]
  (let [ix   (:index kb)
        ;; A deferred literal is computed from bindings: one row over no columns, which
        ;; any prefix joins with unchanged.
        vs   (if (sx/deferred-literal? goal) #{} (sx/form-variables goal))
        base (cond
               (not (sequential? goal)) {:rows 1.0 :distinct {}}

               (sx/deferred-literal? goal) {:rows 1.0 :distinct {}}

               ;; A negative literal, a dotted rest and an open functor have no trie
               ;; walk: the rows are `est-matches`'s, and no column is counted.
               (or (negative? goal) (sx/dotted? goal) (variable-functor? goal))
               {:rows (double (est-matches kb goal #{}
                                           {:count-at count-at :count-children count-children
                                            :count-with-arg count-with-arg
                                            :count-with-functor count-with-functor
                                            :context context}))
                :distinct {}}

               ;; A unary type literal is the union of its subtype extents: rows and
               ;; distinct counts sum, the counts capped at the rows.  A broad type takes
               ;; one walk per subtype, so each walk checks `budget/*deadline*`.
               (unary-literal? goal)
               (let [[t a] goal
                     dl    budget/*deadline*
                     parts (mapv #(do (budget/check-deadline! dl)
                                      (prefix-summary ix (list % a) count-at count-children))
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
        ;; a literal with no variables yields one row or none, however many contexts
        ;; store it
        rows (if (seq vs) (:rows base) (min 1.0 (:rows base)))]
    {:rows rows :vars vs :distinct (cap-distinct (:distinct base) rows)}))

(defn est-rows
  "The expected relation `goal` denotes, `{:rows n :vars #{…} :distinct {var n}}` in
  longs.  An estimate, wrong in either direction, where `est-matches` is a bound.  `:distinct`
  holds the one variable the trie can count, at the first position the known prefix
  cannot extend past; a variable in `:vars` and absent from `:distinct` is uncounted.
  There is no `bound` argument: the planner prices bindings in the join.  `opts` is
  `est-matches`'s, plus `:count-children`."
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
  (graph/reach-all [start] #(mapcat by-var (by-idx %))))

(defn- components
  "Split the generators `gens` into blocks: two literals share a block when they share a
  variable, transitively, and every block touching `anchor-vars` is fused into one
  anchored block.  A literal with no variables is a block of its own.  Returns
  `[{:pairs [[i literal] …] :anchored? bool} …]`, blocks and pairs in written order."
  [gens anchor-vars]
  (let [by-idx (into {} (map (fn [[i l]] [i (sx/form-variables l)])) gens)
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
  "Order one block's `pairs` by repeatedly taking a literal `cost` does not cost
  `unbounded` under the variables bound so far, while one remains, then the one whose join
  onto the prefix has the fewest rows, ties to a literal `cost` does not call a test, then
  to the earlier index.  A literal costed `unbounded` lacks the bindings it computes from,
  and asked ahead of its binders it answers nothing, however few rows the join formula
  estimates for it.  A test binds nothing and keeps at most the rows in hand.  On a tie the
  model cannot say whether the other literal keeps fewer, and a test run ahead of one that
  does is asked on the rows it would have dropped.  `cost` returns `[est-matches test?]`.
  Returns `{:pairs :n :s :prune?}`: the order, the rows the block produces, the sum of its
  prefix rows, and whether every literal's `est-matches` is at most 1."
  [pairs prefix0 bound0 cost summary-of]
  (loop [remaining pairs, prefix prefix0, bound bound0, acc [], s 0.0, prune? true]
    (if (empty? remaining)
      {:pairs acc :n (:rows prefix) :s s :prune? prune?}
      (let [scored (map (fn [[i l :as pr]]
                          (let [[b test?] (cost l bound)
                                joined    (clamped-join prefix (summary-of pr) b)]
                            [(if (>= b unbounded) 1 0) (:rows joined) (if test? 1 0) i pr joined b]))
                        remaining)
            [_ rows _ _ pick joined b] (first (sort-by (fn [[u r t i]] [u r t i]) scored))]
        (recur (filterv #(not= (first %) (first pick)) remaining)
               joined
               (into bound (sx/form-variables (second pick)))
               (conj acc pick)
               (+ s rows)
               (and prune? (<= b 1)))))))

(defn- rank-blocks
  "The `planned` blocks in execution order, in three tiers:

  1. the unanchored blocks with `:prune?`, by `:n`;
  2. the anchored block;
  3. the rest by `s/(n−1)` descending, `n ≤ 1` ranking `+∞`.

  Ties break on the block's earliest literal index (`:at`)."
  [planned]
  (let [ratio (fn [{:keys [n s]}]
                (if (<= n 1.0) Double/POSITIVE_INFINITY (/ s (- n 1.0))))]
    (concat (->> planned (filter #(and (not (:anchored? %)) (:prune? %)))
                 (sort-by (juxt :n :at)))
            (filter :anchored? planned)
            (->> planned (remove :anchored?) (remove :prune?)
                 (sort-by (fn [b] [(- (ratio b)) (:at b)]))))))

(defn- block-order
  "Order the generators `gens`: split them into blocks, order each block, rank the
  blocks and concatenate.  Returns `{:pairs [[i literal] …] :info {i {:block n
  :anchored? bool :isolated? bool}}}`, the record `explain` reports."
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
                                            ;; a lone literal that could multiply,
                                            ;; ranked behind another block
                                            :isolated? (and (not anchored?)
                                                            (not prune?)
                                                            (= 1 (count pairs))
                                                            (pos? b))}]))
                              pairs)))
                  ranked)}))

(defn- closed-extent-tests
  "The literals of `goals` that `rules/closed-extent-antecedents` selects: a closed
  negative literal over a predicate a closed extent is declared on.  Under the grant
  `ClosedExtentProver` answers one only once it is ground, so the plan places it as a
  deferred literal."
  [kb goals]
  (set (rules/closed-extent-antecedents (reasoning/taxonomy kb) goals)))

;; Literals travel as [index literal] pairs.  A conjunction may repeat a literal, and
;; removing a chosen literal by value would drop every copy; the index is also the
;; tie-break key.
(defn- partition-literals
  "Split `goals` into `[index literal]` pairs by class: `:gens`, reordered on cost;
  `:recs`, the recursive literal, placed last; `:defs`, the deferred literals and the
  literals in `tests`, each threaded in where its inputs are bound."
  [goals consequent-pred tests]
  (let [pairs (vec (map-indexed vector goals))
        def?  (fn [l] (or (deferred? l) (contains? tests l)))
        rec?  (fn [l] (and (not (def? l)) (recursive-in? l consequent-pred)))]
    {:gens (filterv (fn [[_ l]] (not (or (def? l) (rec? l)))) pairs)
     :recs (filterv (fn [[_ l]] (rec? l)) pairs)
     :defs (filterv (fn [[_ l]] (def? l)) pairs)}))

(defn- runs-bound
  "The variables bound once literal `l` has run: a deferred literal's inputs and outputs
  (`sentex/deferred-input-vars`, `sentex/deferred-output-vars`), every variable of any
  other literal."
  [l]
  (if (deferred? l)
    (into (sx/deferred-input-vars l) (sx/deferred-output-vars l))
    (sx/form-variables l)))

(defn- ready
  "`[ready bound']`: the literals of `defs` that `runs?` lets run under `bound` and the
  variables the ready literals before them bind (`runs-bound`), in run order, and `bound`
  with those variables added.  `(evaluate ?z (+ ?x ?y))` is ready once `?x` and `?y` are
  bound: waiting on its output `?z` as well would hold it behind the recursive literal."
  [defs bound runs?]
  (loop [pending defs, bound bound, acc []]
    (if-let [pick (first (filter (fn [[_ l]] (runs? l bound)) pending))]
      (recur (filterv #(not= pick %) pending) (into bound (runs-bound (second pick))) (conj acc pick))
      [acc bound])))

(defn- split-waits
  "Split the literals that wait for a bound end (`:end-vars`) out of the generators
  `gens`, as `[gens waits]`: a literal waits when none of its end variables is in
  `bound` and another generator or a recursive literal of `recs` can bind one of them.
  `[gens []]` for a caller that names none."
  [gens recs bound end-vars]
  (if-not end-vars
    [gens []]
    (let [waits? (fn [[i l]]
                   (when-let [ends (not-empty (end-vars l))]
                     (and (not-any? bound ends)
                          (some (fn [[j g]] (and (not= i j) (some (sx/form-variables g) ends)))
                                (concat gens recs)))))]
      [(filterv (complement waits?) gens) (filterv waits? gens)])))

(defn- thread-waits
  "`[threaded pending]`: the literals `pairs` in execution order, with each waiting
  literal of `waits` placed right after the first literal that binds one of its ends,
  and the waiting literals no literal of `pairs` bound, in their written order."
  [pairs waits bound end-vars]
  (loop [remaining pairs, bound bound, pending waits, acc []]
    (if-let [pick (first (filter (fn [[_ l]] (some bound (end-vars l))) pending))]
      (recur remaining (into bound (sx/form-variables (second pick)))
             (filterv #(not= pick %) pending) (conj acc pick))
      (if-let [[_ l :as pick] (first remaining)]
        (recur (rest remaining) (into bound (sx/form-variables l)) pending (conj acc pick))
        [acc pending]))))

(defn- recs-then-waits
  "The recursive literals `recs`, each followed by the waiting literals of `waits` it
  binds an end of, then the waiting literals nothing bound, in their written order."
  [recs waits bound end-vars]
  (let [[threaded pending] (thread-waits recs waits bound end-vars)]
    (into threaded pending)))

(defn- thread-computed
  "The generators `pairs`, in execution order, with each literal `computed?` names moved
  to right after the generators that let `runs?` run it.  Those the generators never let
  run follow them all, in their written order."
  [pairs computed? runs? bound]
  (loop [remaining pairs, bound bound, pending [], acc []]
    (let [ready? (fn [[_ l]] (runs? l bound))]
      (if-let [pick (first (filter ready? pending))]
        (recur remaining (into bound (sx/form-variables (second pick)))
               (filterv #(not= pick %) pending) (conj acc pick))
        (if-let [[_ l :as pick] (first remaining)]
          (if (and (computed? l) (not (ready? pick)))
            (recur (rest remaining) bound (conj pending pick) acc)
            (recur (rest remaining) (into bound (sx/form-variables l)) pending (conj acc pick)))
          (into acc pending))))))

(defn- hold-computed
  "Split the generators `gens` as `[gens held]`.  With a recursive literal in `recs`, a
  literal `computed?` names is held when `runs?` does not let it run under the fixpoint
  of `bound`, the non-computed generators' variables and the variables of each computed
  literal the fixpoint lets run.  Ranked among the generators, a held literal would run
  with an input open and answer nothing.  `plan-pairs` threads a held literal in with
  the deferred literals, so it runs once the recursive literal has bound its inputs."
  [gens recs bound computed? runs?]
  (if (empty? recs)
    [gens []]
    (let [computed (filterv (comp computed? second) gens)
          base     (into bound
                         (comp (remove (comp computed? second))
                               (mapcat (comp sx/form-variables second)))
                         gens)
          [ran _]  (ready computed base runs?)
          ran      (set ran)
          held?    (fn [[_ l :as pr]] (and (computed? l) (not (ran pr))))]
      [(filterv (complement held?) gens) (filterv held? gens)])))

(defn- lits [pairs] (mapv second pairs))

(defn- override-cost
  "`[estimate test?]` from the `:est-override` for `goal` with the variables in `bound`
  bound, or nil when it gives none.  An override reads the literal as written, so a
  literal whose every variable the plan has bound is a test, costed at most 1 as
  `est-matches` costs one: it runs ahead of the literals the model expects to multiply
  the rows in hand, where the override's estimate for its open variables would hold it
  behind every generator."
  [est-override goal bound]
  (when-let [e (when est-override (est-override goal bound))]
    (if (settled-when-run? goal bound) [(min e 1) true] [e false])))

(defn- memo-opts
  "The estimator options for one plan: each of the four index reads behind its own
  `memoizing` cache, and `context`.  `explain` reuses the plan's set, so its report
  reads no count the ranking already read."
  [context]
  {:count-at           (memoizing reads/stored-count-at)
   :count-children     (memoizing reads/stored-count-children)
   :count-with-arg     (memoizing reads/stored-count-with-arg-global)
   :count-with-functor (memoizing reads/stored-count-with-functor)
   :context            context})

(defn- plan-pairs
  "The ordering decision: `goals` in execution order as `[index literal]` pairs, the
  per-generator `:info` `block-order` recorded, and `:opts`, the memoized estimator set
  the ranking read through (absent when no ranking ran).  `order` and `explain` both
  read this one result."
  [kb goals context {:keys [bound consequent-pred est-override end-vars] :or {bound #{}}}]
  (let [goals (vec goals)]
    (if (< (count goals) 2)
      {:pairs (vec (map-indexed vector goals)) :info {}}
      (let [bound (set bound)
            {:keys [gens recs defs]} (partition-literals goals consequent-pred
                                                         (closed-extent-tests kb goals))
            computed? (fn [l] (when-let [e (when est-override (est-override l bound))]
                                (<= unbounded e)))
            ;; A computed literal runs once every variable is bound, or once the override
            ;; costs it under the bindings below `unbounded`: its inputs are bound and the
            ;; computation binds the rest.
            runs?  (fn [l bnd]
                     (if (and (not (deferred? l)) (computed? l))
                       (or (every? bnd (sx/form-variables l))
                           (let [e (est-override l bnd)] (or (nil? e) (< e unbounded))))
                       (every? bnd (sx/deferred-input-vars l bnd))))
            [gens held] (hold-computed gens recs bound computed? runs?)
            defs   (if (seq held) (vec (sort-by first (into defs held))) defs)
            [gens waits] (split-waits gens recs bound end-vars)
            drop-i (fn [pending taken]
                     (let [taken (set (map first taken))]
                       (filterv (fn [[i _]] (not (taken i))) pending)))
            ;; the literals of `pending` after the recursive and waiting literals, those
            ;; ready under their bindings first, in run order
            after  (fn [pending bnd]
                     (let [[r _] (ready pending
                                        (into bnd (mapcat (comp sx/form-variables second))
                                              (concat recs waits))
                                        runs?)]
                       (into r (drop-i pending r))))]
        ;; `*enabled*` false skips the ranking only; the readiness discipline runs
        ;; either way.
        (if (or (not *enabled*) (< (count gens) 2))
          ;; written order, with waiting and computed literals behind their binders and
          ;; the ready deferred literals ahead of the recursive one
          (let [[gens late] (thread-waits gens waits bound end-vars)
                gens   (thread-computed gens computed? runs? bound)
                [early bound'] (ready defs (into bound (mapcat (comp sx/form-variables second))
                                                 gens)
                                      runs?)]
            {:pairs (vec (concat gens early (recs-then-waits recs late bound' end-vars)
                                 (after (drop-i defs early) bound')))
             :info  {}})
          (let [opts       (memo-opts context)
                cost       (fn [g bnd]
                             (or (override-cost est-override g bnd)
                                 [(est-matches kb g bnd opts) false]))
                ;; A summary does not depend on the bindings in hand, so it is computed
                ;; once per literal.  An override's summary counts no column, so a join
                ;; with it divides by what the other side read.
                summaries  (volatile! {})
                summary-of (fn [[i l]]
                             (or (get @summaries i)
                                 (let [s (if-let [e (when est-override (est-override l bound))]
                                           {:rows (double e) :vars (sx/form-variables l) :distinct {}}
                                           (summary kb l opts))]
                                   (vswap! summaries assoc i s)
                                   s)))
                {:keys [pairs info]} (block-order gens bound cost summary-of
                                                  (into bound
                                                        (mapcat (comp sx/form-variables second))
                                                        (concat recs defs waits)))
                [threaded late] (thread-waits pairs waits bound end-vars)]
            (loop [remaining threaded
                   bound     bound
                   pending   defs
                   acc       []]
              (if (empty? remaining)
                (let [[early bound'] (ready pending bound runs?)]
                  {:pairs (vec (concat acc early (recs-then-waits recs late bound' end-vars)
                                       (after (drop-i pending early) bound')))
                   :info  info
                   :opts  opts})
                (let [[_ l :as pick]  (first remaining)
                      [early bound']  (ready pending (into bound (sx/form-variables l)) runs?)]
                  (recur (rest remaining)
                         bound'
                         (drop-i pending early)
                         (into (conj acc pick) early)))))))))))

(defn order
  "Order `goals`, a conjunction, for execution, and return the reordered vector.

  `opts`:
    :bound            variables bound when the conjunction starts (default none).  A
                      caller that substituted its bindings into the goals leaves this
                      empty.
    :consequent-pred  the functor of the rule whose antecedents these are; the literal
                      with that functor is placed after the other generators, and of
                      the generators only an `:end-vars` literal it binds an end of
                      and a computed literal it binds a variable of follow it.
    :est-override     (fn [goal bound]) -> estimate or nil, consulted before the index
                      model.  An estimate of `unbounded` marks a literal computed from
                      its bindings.  A literal whose every variable the plan has bound
                      costs at most 1, whatever the override gives (`override-cost`).
    :end-vars         (fn [literal]) -> the end variables of a literal that answers in
                      full only once one end is bound, or nil.  Such a literal waits for
                      the first generator that binds an end, or for the recursive
                      literal when only that binds one.

  A conjunction with fewer than two reorderable literals skips the ranking and reads no
  index."
  ([kb goals context] (order kb goals context {}))
  ([kb goals context opts]
   (lits (:pairs (plan-pairs kb goals context opts)))))

(defn explain
  "The plan as data: one map per literal, in execution order, with

  - `:goal`, and `:bound-before`, the variables bound when it runs;
  - `:est-matches`, the sound upper bound on its fan-out under those bindings;
  - `:est-rows`, the expected size of its own relation;
  - `:est-prefix`, the expected rows of the plan through it;
  - `:block`, the index of the block it ran in, nil where no ranking ran;
  - `:deferred?`, `:recursive?`, and `:isolated?`, a cartesian factor ranked behind
    another block.

  The flags and `:block` are read off the plan that ran.  The numbers are recomputed
  through the same estimator calls, the `:est-override` and the plan's memoized reads.
  `opts` is `order`'s."
  ([kb goals context] (explain kb goals context {}))
  ([kb goals context opts]
   (let [{:keys [pairs info] memo :opts} (plan-pairs kb goals context opts)
         bound0   (or (:bound opts) #{})
         est-opts (or memo (memo-opts context))
         ;; `plan-pairs` never asks the override about a deferred literal; neither does this
         override (when-let [f (:est-override opts)]
                    (fn [g bnd] (when-not (deferred? g) (f g bnd))))
         ;; as in `plan-pairs`: the bound under the bindings in hand, the summary under
         ;; the caller's
         bound-of (fn [g bnd] (long (or (first (override-cost override g bnd))
                                        (est-matches kb g bnd est-opts))))
         sum-of   (fn [g] (if-let [e (when override (override g bound0))]
                            {:rows (double e) :vars (sx/form-variables g) :distinct {}}
                            (summary kb g est-opts)))]
     (first
      (reduce (fn [[acc bound prefix] [i g]]
                (let [s      (sum-of g)
                      bnd    (bound-of g bound)
                      ;; a deferred literal filters the rows in hand: clamp to 1
                      ;; rather than read the trie, which answers 0 for `lessThan`
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
                   (into bound (sx/form-variables g))
                   joined]))
              [[] bound0 (bound-prefix bound0)]
              pairs)))))
