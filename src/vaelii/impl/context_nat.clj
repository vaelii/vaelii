;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.context-nat
  "The structural genlCx producer for reified-NAT contexts — docs/context-nat.md.

  A `(contextArgSubrelation F pos R)` declaration says two `F`-contexts identical except
  at argument `pos` are ordered by the sub-relation `R` on that argument.  This namespace
  reads the declarations and the context NATs of `F` from the store and **materializes**
  the `genlCx` edges they entail: for two siblings whose `pos` arguments stand in `R`, the
  more specific one (its argument `R`-below the other's) is deduced to `genlCx` the more
  general, as a **justified** sentex in CxUniverse.  So the edge belief-follows for free —
  retract a context (its `termOfUnit` map), the declaration, or the `R`-evidence, and the
  ordinary JTMS relabel withdraws it.  It is never a premise anyone asserted.

  `R` is resolved by a **bounded** oracle, because the producer runs on the assert
  maintenance path and a genlCx edge feeds the taxonomy closure a relabel loop reads — so
  a prover search is out (docs/naf.md): either a registered pure structural comparator
  (the datetime one, keyed on `subintervalOf` over `DatetimeFn` terms) answers it, or a
  believed stored `(R a b)` fact does.  A comparator answer is a pure function of the two
  expressions, already carried by the `termOfUnit` antecedents, so it needs no extra
  supporter; a stored fact contributes its own handle so defeating it withdraws the edge.

  Materialization reuses the derived-sentex pattern `special/deduce-lift` uses:
  `find-or-create-sentex`, then `special/derived-sentex-added` to reach the genlCx closure
  and post the re-check triggers, then a JTMS justification under the
  `contextArgSubrelation` informant — and then, on the transition into belief,
  `special/reconcile-context-edge`, the same entry point the assert and rule-conclusion paths
  call.  A `genlCx` edge widens which merges a context can see, and an edge nobody
  asserted widens it exactly as much as one somebody did (vaelii#56); the merge it
  yields is handed back up to `core`, which owns the follow-through."
  (:require [vaelii.impl.datetime :as datetime]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private universal-context 'CxUniverse)

;; ---- the bounded R oracle -------------------------------------------------

(def ^:private comparators
  "Registered pure structural comparators, `{sub-relation → (fn [a b] boolean)}`.  A
  comparator answers `R` between two structural argument terms by reading their shape — no
  store read, no proof — so the producer may call it inside the relabel loop.  Each is a
  total predicate that returns `false` for terms it does not apply to, so it composes with
  the stored-fact fallback: `datetime/subinterval?` answers a pair of `DatetimeFn` terms
  and declines anything else."
  {'subintervalOf datetime/subinterval?})

(defn- comparator-holds?
  "True iff a registered comparator for `r` answers that `a` is `R`-below `b`."
  [r a b]
  (boolean (when-let [f (get comparators r)] (f a b))))

(defn- r-evidence
  "The belief the relationship `a` `R`-below `b` rests on: `::pure` when a comparator
  answers it (a pure function of the two expressions, already carried by the `termOfUnit`
  antecedents), the handle of a believed `(R a b)` fact when one does, or `nil` when the
  relationship does not hold and no edge should be made.

  When several believed `(R a b)` facts stand — the same ground relation in different
  contexts — the supporter is chosen **content-keyed**, not by whichever the retrieval
  yielded first: sorting by context before taking one keeps the edge's justification off
  the insertion/index order of the facts (a handle tie-break would break order
  independence), the determinism `dedup-constant` uses.  The facts share the ground
  sentence `(R a b)`, so their context is what distinguishes them."
  [kb r a b]
  (cond
    (comparator-holds? r a b) ::pure
    :else (some->> (kb/sentexes-matching kb (list r a b) '?ctx)
                   (sort-by :context)
                   first
                   :id)))

;; ---- reading the declarations and the context NATs ------------------------

(defn any-context-subrelations?
  "Cheap gate: does the KB declare any `contextArgSubrelation`?  The producer is a no-op
  otherwise — one O(1) functor count per assert, the shape `nat/any-corresponding-predicates?`
  has."
  [kb]
  (pos? (reads/stored-count-with-functor (:index kb) 'contextArgSubrelation)))

(defn- subrelation-declarations
  "Believed `(contextArgSubrelation F pos R)` declarations as `[F pos R handle]`, kept
  where `(pred? F)` — all of them, or only those for one function."
  [kb pred?]
  (for [sx  (kb/sentexes-matching kb '(contextArgSubrelation ?f ?pos ?r) '?ctx)
        :let [[_ f pos r] (:sentence sx)]
        :when (pred? f)]
    [f pos r (:id sx)]))

(defn- context-nats-of
  "Every believed context NAT whose expression head is `f`, as `[k expr termOfUnit-handle]`.

  Reached through the **inverted term index** on `f` — which descends into a ground
  compound, so an expression's head is one of the sentex's posted terms — rather than by
  reading the whole `termOfUnit` population and keeping the few under `f`.  That
  distinction is the difference between a bounded read and a scan of every reified NAT in
  the KB, and this runs on the assert maintenance path (`reconcile-genlCx`), once per
  fact stored into a `cx/` context.  `nat/minted-applications` reads the same map the
  same way, for the same reason."
  [kb f]
  (->> (kb/find-sentexes kb f)
       (keep (fn [sx]
               (let [[_ k e] (:sentence sx)]
                 (when (and (= universal-context (:context sx))
                            (= 'termOfUnit (nm/functor (:sentence sx)))
                            (jtms/in? (reasoning/tms kb) (:id sx))
                            (nat/reified-context-symbol? k)
                            (sequential? e) (= f (first e)))
                   [k e (:id sx)]))))
       distinct))

(defn- sibling-key
  "The identity of a context NAT's sibling group under argument `pos`: its expression with
  the ordered argument masked, so two contexts share a key iff they agree on every *other*
  argument (the dimension) and differ only where `R` orders them.  `pos` is 1-based over
  the function's arguments, hence the expression index `pos` (index 0 is the functor).

  **nil when `pos` does not index this expression** — a `pos` past the function's arity,
  or one that is not a position at all.  Nothing at the assert entry point ties a declaration's
  `pos` to the arity of the function it names, so `(contextArgSubrelation CxTimeFn 9 R)`
  is storable; masking blind would throw out of the maintenance path and take the
  unrelated assert with it, and appending at `pos = arity` would invent a sibling group
  whose ordered argument is `nil`.  `reconcile-function` drops a nil key, which is the
  same tolerance `order-group` already shows with its `(nth … pos nil)`."
  [expr pos]
  (when (and (integer? pos) (pos? (long pos)) (< (long pos) (count expr)))
    (assoc (vec expr) pos '_)))

;; ---- materialization ------------------------------------------------------

(defn- combine
  "Merge the `{:new :superseded :violations}` results of several materializations into
  one, or nil when every one of them was nil.  nil rather than an empty accumulator for
  the reason `special/reconcile-context-edge` returns nil: the producer runs on the
  assert maintenance path of every KB that declares a context function, and the common
  case is a sweep that re-derives edges it already has and merges nothing."
  [ms]
  (let [ms (remove nil? ms)]
    (when (seq ms)
      (apply merge-with into {:new [] :superseded [] :violations []} ms))))

(defn- materialize-edge
  "Deduce `(genlCx sub super)` in CxUniverse, justified by `antes`, unless a violation
  refuses it (a genlCx edge over two `cx/` contexts is admissible except a self-edge, which
  the caller already excludes).  Idempotent: a second call with the same antecedents adds
  no justification, and a different route adds another supporter of the one edge.

  Bare: it adds one derived sentex and one justification, and the JTMS withdraws the edge
  when an antecedent stops being believed — nothing here destroys stored knowledge, so
  nothing in this chain carries a `!`.

  **Returns what the edge merged**, `{:new :superseded :violations}` or nil — not the
  handle, which no caller ever read.  A `genlCx` edge widens which merges a context can
  see, and until vaelii#56 a *computed* edge was the one entry point that never said so: the
  three equality reconcilers were spelled out by hand in the assert path and in the
  rule-conclusion path, and a calendar month→year edge ran neither, so two fillers of one
  functional slot that this edge made jointly visible for the first time stayed unmerged
  and uncontradicted.  `special/reconcile-context-edge` is now the single entry point all three
  call, and the caller carries the result out to `core`, which owns the follow-through
  (`refresh-supersessions`, the chaining seeds, the violation ledger) for the assert path
  already.

  **Reconciled exactly on the transition into belief**, which is both halves of the
  budget question.  *After* the justification, because the three sweeps read the
  belief-filtered `genlCx` closure and a line earlier the edge is a node nothing supports
  — they would enumerate the pre-edge ancestor set and find nothing.  And only when the edge was
  not believed before this call, because the producer is idempotent and re-runs over
  every context of a declared function on every assert into one of them: without the
  transition gate a calendar of `k` sibling months would re-sweep its O(k²) edges on each
  arrival, where each edge in fact owes exactly one sweep in its life.  A second route to
  an edge already believed widens no ancestor set, so it owes none at all."
  [kb sub super antes]
  (let [edge (list 'genlCx sub super)
        tms  (reasoning/tms kb)]
    (when-not (special/inadmissible kb edge universal-context)
      (let [[h2 s2 new?] (kb/find-or-create-sentex kb edge universal-context)
            _            (when new? (special/derived-sentex-added kb s2 h2))
            believed?    (and (not new?) (jtms/in? tms h2))]
        (let [depth (inc (reduce max 0 (map #(jtms/depth tms %) antes)))
              antes (vec antes)]
          (jtms/ensure-node tms h2 depth)
          (when-not (jtms/has-justification? tms 'contextArgSubrelation antes h2)
            (let [jid  (p/next-id (:records kb))
                  just (jtms/->just jid 'contextArgSubrelation antes h2 {} :monotonic)]
              (p/put-justification (:records kb) just)
              (jtms/add-justification tms just))))
        (when (and (not believed?) (jtms/in? tms h2))
          (special/reconcile-context-edge kb edge))))))

(defn- order-group
  "Materialize every genlCx edge within one sibling group under declaration `[pos R declH]`:
  for each ordered pair of siblings whose `pos` arguments stand in `R`, the sub `genlCx` the
  super.  `nats` is `[k expr termOfUnit-handle]` for the group's members.

  Returns the group's merged `{:new :superseded :violations}`, or nil — see
  `materialize-edge`, whose result this is carrying out."
  [kb pos r declH nats]
  (combine
   (for [[ksub esub th-sub] nats
         [ksup esup th-sup] nats
         :when (not= ksub ksup)
         :let  [asub (nth esub pos nil)
                asup (nth esup pos nil)
                ev   (r-evidence kb r asub asup)]
         :when ev]
     (materialize-edge kb ksub ksup
                       (cond-> [th-sub th-sup declH]
                         (not= ::pure ev) (conj ev))))))

(defn- reconcile-function
  "Materialize the structural genlCx edges for every declaration of function `f`, over all
  of `f`'s context NATs grouped into siblings.  Returns their merged
  `{:new :superseded :violations}`, or nil."
  [kb f]
  (combine
   (for [[_ pos r declH] (subrelation-declarations kb #(= f %))
         :let [groups (group-by #(sibling-key (second %) pos) (context-nats-of kb f))]
         [k nats] groups
         ;; a nil key is an expression the declared `pos` does not index — no sibling
         ;; group, so nothing to order (`sibling-key`)
         :when (some? k)]
     (order-group kb pos r declH nats))))

(defn- functions-ordered-by
  "The context functions some believed declaration orders by sub-relation `r`.  What the
  **stored-fact oracle**'s retroactive arm reconciles: an `(R a b)` fact arriving after
  both contexts is new evidence for an edge the producer previously declined, and `R` is
  all the fact says about which function that edge belongs to."
  [kb r]
  (when (symbol? r)
    (distinct (for [[f _ r' _] (subrelation-declarations kb (constantly true))
                    :when (= r r')]
                f))))

(defn reconcile-genlCx
  "The structural-genlCx maintenance a just-asserted `sentence` in `context` calls for,
  scoped to what could have changed:

  - a `(contextArgSubrelation F …)` declaration reconciles all of `F`'s contexts;
  - a fact stored into a `cx/` context reconciles that context's function — its arrival, or
    the mint of a new context beside it, is what creates a sibling pair to order;
  - an `(R a b)` fact on a **declared sub-relation** reconciles the functions declared to
    order by `R`.  That is the third way an edge can become entailed with both contexts
    already stored: a comparator dimension needs nothing but the contexts, but a dimension
    resolved by stored facts has the evidence arrive on its own schedule, and without this
    arm the edge would wait for the next assert that happened to touch one of the two
    contexts.

  A no-op — one functor count — on a KB that declares no `contextArgSubrelation`.  Every
  arrival order reaches the same fixpoint: a declaration arriving after the contexts sweeps
  them (`reconcile-function`), a context arriving after a declaration is swept when it is
  stored into, and the evidence arriving after both sweeps the functions it is evidence
  for.  Idempotent, so re-running orders the same edges without duplicating.

  **Returns what the edges it computed merged** — `{:new :superseded :violations}`, or
  nil when they merged nothing, which is every KB that states no equality and every
  re-run over edges it already had.  A computed edge widens which merges a context can
  see exactly as a stated one does, and the caller owes it the same follow-through
  (`core/assert`)."
  [kb sentence context]
  (when (any-context-subrelations? kb)
    (cond
      (and (sequential? sentence) (seq sentence)
           (= 'contextArgSubrelation (first sentence)))
      (reconcile-function kb (second sentence))

      (nat/reified-context-symbol? context)
      (when-let [e (nat/nat-expression kb context)]
        (when (sequential? e) (reconcile-function kb (first e))))

      :else
      (combine
       (for [f (functions-ordered-by kb (nm/functor sentence))]
         (reconcile-function kb f))))))

(defn reconcile-revivals
  "Rebuild the structural genlCx edges for **every** declared `contextArgSubrelation`
  function — the build direction a belief *revival* needs, which `reconcile-genlCx` (only
  ever called from the assert choke-point) cannot serve.

  Belief of a `contextArgSubrelation` declaration — or of a stored `(R a b)` evidence fact
  — can flip OUT→IN with no assert: retracting a monotonic defeater above it revives it.
  The JTMS revives a *justification that already exists*, but an edge the producer never
  built (because the declaration was OUT when the contexts were stored) has no
  justification to revive, so the edge would stay absent.  A teardown therefore re-runs the
  producer once its belief has settled, and the withdraw direction the JTMS already handles
  meets a build direction here.

  Idempotent (`materialize-edge` adds no duplicate justification) and **local**: scoped to
  the declared context functions, each reconciled only over its own contexts — bounded by
  the context-NAT population, never the whole graph.  Behind the **free** in-memory
  `context_denoting_function` gate first — a KB with no `cx/` context to order pays neither
  the `any-context-subrelations?` functor-count index read nor anything else, so the retract
  hot path is untouched on every KB that declares no context function
  (`assert_cost_test`).

  Returns the merged `{:new :superseded :violations}` of whatever it rebuilt, or nil —
  a revived edge widens an ancestor set like any other, so the teardown owes it the same
  follow-through the assert path gives a computed edge."
  [kb]
  (when (and (nat/any-context-denoting-functions? kb) (any-context-subrelations? kb))
    (combine
     (for [f (distinct (map first (subrelation-declarations kb (constantly true))))]
       (reconcile-function kb f)))))
