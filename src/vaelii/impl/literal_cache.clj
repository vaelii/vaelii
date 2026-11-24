;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.literal-cache
  "Canonical variable names for a **solution** cache keyed by a literal, and the
  translation back into the caller's names.

  A backward proof asks the same question many times.  Two sibling branches that both
  need `(parentOf Tom ?y)` each solve it in full, and a diamond-shaped rule set pays for
  the shared literal once per path through the diamond — `res/prove-from`'s per-path
  `:seen` guard stops a goal from re-*expanding* itself on one path, and says nothing
  about the same goal being re-*solved* on another.  Keying an
  answer by the literal is what collects that sharing, and the key has to be blind to
  what the caller happened to name its variables: `(P ?x)` and `(P ?y)` are one question.

  **Why `res/goal-key` is not that key.**  It collapses *every* variable to `?`, so
  `(P ?x ?x)` and `(P ?x ?y)` share a key.  That is sound for a loop guard, which only
  has to be conservative — over-matching prunes a branch that was going to be pruned —
  and unsound for a solution cache, where the second goal's answers include the pairs
  the first excludes.  Serving one for the other invents solutions.  So the renaming
  here is **repetition-preserving**: distinct variables get distinct names and a
  repeated variable keeps its repetition.

  **Why `sentex/alpha-rename` is not it either.**  That one builds an *index* key, where
  a variable means \"anything in this position\" and each anonymous `_` is therefore
  fresh and unshared.  `unify` does not read `_` that way — `variable?` admits it and
  `unify-var` chases its binding, so `(P _ _)` fails against `(P A B)` exactly as
  `(P ?x ?x)` does.  A cache keyed on retrieval semantics would hand `(P _ _)` the
  answers of `(P ?0 ?1)`, so `_` is renamed here as the ordinary variable it is.

  **What is cached, and why there.**  The unit is one literal's *visible matches*
  (`res/matches-visible`), not one literal's *solutions* (`provers/solve-goal`).  That
  is where the repetition measurably is — a rule-heavy query re-asks a handful of
  metadata literals (`(arg P n ?t)`, read per believed sentex per argument position
  by `provers/inferred-types`) hundreds of times, while its rule subgoals arrive
  already substituted and so are mostly distinct.  It is also the only layer at which
  the answer is a function of the KB alone.  `solve-goal` is **tier**-dependent, because
  `ask-capped` drops provers above a cost tier, and **scope**-dependent, because provers
  underneath it read the taxonomy closures and the resident networks through
  `observe/cached` — so inside a held-values scope they answer from the values that scope holds fixed.
  An answer cached at that layer would therefore have to carry the tier and the scope
  that produced it.  `matches-visible` carries neither and reads nothing through
  `observe/cached`, so a held-values scope cannot hand it a reading the clock has left.

  There is **one layer, not two**.  A per-query memo would be redundant: a query
  performs no mutation, so the change clock cannot move while one runs, and every
  repeat a per-query memo would catch is a repeat this cache already serves under an
  unmoved change clock."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private canonical-vars
  "`?0 ?1 …` pre-built and interned.  A literal's variable count is small and the same
  handful of names is rebuilt for every key, so they are shared objects rather than a
  fresh symbol per canonicalization (`sentex/intern-sym`, for the reason the symbol pool
  exists at all)."
  (mapv #(sx/intern-sym (symbol (str "?" %))) (range 32)))

(defn- canonical-var
  "The Nth canonical variable — from the table, or built for a literal with more
  variables than the table holds."
  [n]
  (if (< n (count canonical-vars))
    (nth canonical-vars n)
    (sx/intern-sym (symbol (str "?" n)))))

(defn- has-variable?
  "Does `form` hold a variable outside every `(Quote …)`?  A scan that allocates nothing,
  so the ground case is answered without building the tree-seq a `some` over one would."
  [form]
  (cond
    (sx/variable? form)  true
    (sx/quote-form? form) false
    (sequential? form)   (boolean (some has-variable? form))
    :else                false))

(defn canonicalize
  "`[canonical rename]` for `form`: its variables renamed to `?0 ?1 …` in
  first-occurrence order, and the map from each canonical name back to the caller's.

  First occurrence, not sorted — the order is a function of the literal's own shape, so
  two spellings of one question converge without either of them being consulted about
  the other.  Shape is preserved (a vector stays a vector), as `sentex/alpha-rename`
  preserves it and for the same reason: a conjunction is a vector and a literal a list.

  `rename` is empty for a ground literal, which is the common post-substitution case —
  and one this returns **unchanged**, without rebuilding it.  That fast path is not a
  micro-optimization: canonicalizing sits in front of every cached lookup, so it is
  charged to the calls that *hit* as much as to the ones that miss, and rebuilding a
  ground literal to discover it had nothing to rename is the whole cost of the lookup it
  was meant to save.  A `(Quote …)` form is left as written, since `res/unify` matches
  it only by equality.  A `java.util.HashMap` for the scratch numbering, for the same
  reason — the map is thrown away at the end of the call and never escapes."
  [form]
  (if-not (has-variable? form)
    [form {}]
    (let [seen (java.util.HashMap.)                  ; caller's variable -> canonical
          back (volatile! {})]                       ; canonical -> caller's variable
      (letfn [(rn [x]
                (cond
                  (sx/variable? x)
                  (or (.get seen x)
                      (let [v (canonical-var (.size seen))]
                        (.put seen x v)
                        (vswap! back assoc v x)
                        v))
                  (sx/quote-form? x) x
                  (vector? x)     (mapv rn x)
                  (sequential? x) (apply list (map rn x))
                  :else           x))]
        (let [c (rn form)]
          [c @back])))))

(defn- rename-term
  "`t` with every canonical variable `rename` knows about replaced by the caller's name.
  One pass, not a fixpoint: each node is rewritten at most once, so a caller whose own
  goal happens to mention `?0` cannot have its answers rewritten twice.  A `(Quote …)`
  form is stored content and is not renamed."
  [rename t]
  (cond
    (contains? rename t) (get rename t)
    (sx/quote-form? t)   t
    (vector? t)          (mapv #(rename-term rename %) t)
    (sequential? t)      (apply list (map #(rename-term rename %) t))
    :else                t))

(defn rename-bindings
  "A canonical-space solution binding map translated back into the caller's variable
  names, or nil when the translated bindings do not unify.  Identity when `rename` is
  empty (a ground literal).  Each binding is renamed in its key and its value and added
  through `unify` (`res/unify`, passed in because this namespace cannot require it), so a
  stored formula that carries the caller's own variable names answers as it does
  uncached.  See docs/inference.md, \"The literal cache\"."
  [unify rename bindings]
  (if (empty? rename)
    bindings
    (reduce-kv (fn [acc k v]
                 (or (unify (get rename k k) (rename-term rename v) acc) (reduced nil)))
               {} bindings)))

(defn rename-matches
  "A seq of `matches-visible` results translated out of canonical space by
  `rename-bindings`, dropping a result whose bindings do not unify.  A result is
  `[handle bindings …]` — some carry a third slot — so only slot 1 is touched and the
  rest is passed through.  Lazy: a consumer taking one match renames one."
  [unify rename ms]
  (if (empty? rename)
    ms
    (keep (fn [m] (some->> (rename-bindings unify rename (nth m 1)) (assoc m 1))) ms)))

;; ---- the cache -----------------------------------------------------------

(def ^:dynamic *enabled*
  "Whether a cached lookup is consulted at all.  Bound false, `matches-visible` is
  byte-for-byte the uncached path — no key built, no atom read, nothing allocated —
  which is what makes the off state genuinely free rather than merely cheap.

  A toggle that changes cost and not results, in the spirit of `plan/*enabled*`."
  true)

(def ^:private cache-limit
  "The most entries a KB's cache holds before it is cleared wholesale.  The same bound
  and the same wholesale clearing `observe/resident-limit` takes, and for the same
  reason: evicting exactly the right entry costs more bookkeeping than the entry saved,
  and a cache that has grown past this is one whose queries have moved on."
  4096)

(defn- storing
  "`xs`, with the fully realized answer handed to `store!` **at the moment the source
  runs dry** — and never if the consumer stops first.

  This is what keeps the cache compatible with the laziness contract
  (`docs/anytime.md`): a bounded run (`budget/collect` hitting `:max-results`, a
  deadline, a `take`) realizes exactly what it asked for, and stores nothing, so the
  next unbounded ask for the same literal cannot be served a truncated prefix as though
  it were the whole extent.  Realize-and-store is a decision made by the *source*
  ending, not by the consumer leaving."
  [store! xs]
  (let [acc (volatile! [])]
    ((fn step [s]
       (lazy-seq
        (if-let [c (seq s)]
          (do (vswap! acc conj (first c))
              (cons (first c) (step (rest c))))
          (do (store! @acc) nil))))
     xs)))

(defn- marked-seq
  "`xs`, each step of its realization run through `step`."
  [step xs]
  (lazy-seq (when-let [c (step #(seq xs))]
              (cons (first c) (marked-seq step (rest c))))))

(defn lookup
  "The cached value of `k` in the per-KB `cache` atom, or `compute`'s answer on the way
  into it.  A nil `cache` computes every time.

  **The clock is read before `compute` runs, and the entry is stored only if the clock
  has not moved by the time it is complete.**  Both halves matter.  Reading the clock
  afterwards would claim the value describes a state it was never computed from; storing
  across a moved clock would keep a value the mutation invalidated.  Together they mean a
  stored entry describes exactly the state its clock value names — and that a scope which
  *writes while it reads* (forward chaining, `chain/process-datum`) fills the cache with
  nothing, since its own conclusions move the clock under it.  A backward query moves the
  clock never, so it stores everything it completes.

  The correctness argument is `observe/note-change`'s, unrestated: any mutation moves
  the clock, so a hit is served only across a stretch in which the engine performed no
  mutation at all — which is the stretch a query spends reading.

  Inside a second-route search each step of the realization runs under
  `caches/*open-mark*`, and an answer one of whose steps read a route question still open
  is provisional and is not stored (`marked-seq`)."
  [c cache k compute]
  (if (nil? cache)
    (compute)
    (let [now (observe/change-clock c)
          hit (get @cache k)
          t   (caches/tally-of cache :R1)]
      (if (and hit (== now (long (:clock hit))))
        (do (caches/hit t) (:value hit))
        (let [start   (System/nanoTime)
              mark    caches/*open-mark*
              settled (volatile! true)
              step    (fn [f] (let [[v ok?] (mark f)] (when-not ok? (vreset! settled false)) v))]
          (caches/miss t)
          (storing (fn [v]
                     (caches/spent t start)
                     (when (and hit (caches/tallying?))
                       (caches/compared t (= (:value hit) v)))
                     (when (and @settled (== (observe/change-clock c) now))
                       (swap! cache caches/assoc-bounded
                              (caches/limit-of :literal-matches cache-limit)
                              k {:clock now :value v})))
                   (if mark (marked-seq step (step compute)) (compute))))))))

(defn stats
  "`{:size :limit :hits :misses :clock}` — entries held for `kb`, the bound they are
  cleared wholesale at, `kb`'s hit and miss counts (its tally, `caches/row-tally`), and
  the change clock a fresh lookup would key by."
  [kb]
  (let [{:keys [hits misses]} (caches/tally-map (caches/tally-of (reasoning/matches kb) :R1))]
    {:size   (count @(reasoning/matches kb))
     :limit  (caches/limit-of :literal-matches cache-limit)
     :hits   hits
     :misses misses
     :clock  (observe/change-clock (:clock kb))}))

(defn clear-cache
  "Drop everything `kb` has cached; answers how many entries went.  Not `!`: it destroys
  no knowledge — every entry is derived, and the next read recomputes it.  The hit and
  miss counts stay; `caches/clear-caches` zeroes them when asked to."
  [kb]
  (let [n (count @(reasoning/matches kb))]
    (reset! (reasoning/matches kb) {})
    n))

(caches/register-cache
 {:cache    :literal-matches
  :label    "Literal matches"
  :scope    :kb
  :unit     "literals"
  :limit    (caches/limit-thunk :literal-matches cache-limit)
  :counters :kb
  :note     (str "One literal's visible matches, keyed blind to what the caller named "
                 "its variables. Every entry carries the change clock it was computed "
                 "under, so one mutation anywhere retires the whole cache's usefulness "
                 "at once; past the limit it is cleared wholesale rather than evicted "
                 "entry by entry.")
  :read     (fn [kb] {:entries (count @(reasoning/matches kb))})
  :clear    clear-cache
  :trim     (fn [kb target] (caches/trim-map! (reasoning/matches kb) target))})

(caches/register-derived
 {:id :R1 :label "Literal matches" :cache :literal-matches :kind :cache :keyed-by :literal
  :holds-content? false
  :reads [:index :M1 :T1]
  :retired-by (assoc (caches/on-every :G*) :caches-cleared :W)
  :computed :read :imaged? false :at [[:matches]]
  :live (fn [kb] (let [now (observe/change-clock (:clock kb))]
                   (count (filter #(== now (long (:clock %))) (vals @(reasoning/matches kb))))))
  :note "a stale entry is ignored, not removed, and replaced at its next read"})
