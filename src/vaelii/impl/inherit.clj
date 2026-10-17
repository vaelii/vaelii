;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.inherit
  "**Argument-position preservation** — when a claim about one term licenses the same
  claim about another.

  `(typeLargerThan dog cat)` says something about two *kinds*.  Whether it also says
  something about a golden retriever and a maine coon is not decidable from the
  sentence: it depends on whether the relation distributes over the kinds' members.
  Some relations do (`disjoint` — subtypes of disjoint types are disjoint) and some
  emphatically do not (a chihuahua is a dog, a maine coon is a cat, and the maine coon
  is bigger).  So it is **declared**, per predicate, per argument position:

      (transitiveInArg        P n R)   ; a stored (P … w …) licenses (P … a …) when (R w a)
      (transitiveInArgInverse P n R)   ; …licenses it when (R a w)

  `R` is any **transitive** relation — `genl` and `genlCx` through their cached
  closures, or a predicate declared `(transitive R)` walked over stored facts.  A
  declaration over anything else is refused at assert
  (`wff/arg-preserving-problems`): the reach is walked to a fixpoint, so a relation
  that was never said to compose would have transitivity *manufactured* for it, and
  `(arg transitiveInArg 3 transitive)` cannot say so — arg is
  open-world, and an untyped relation cannot violate it.  Naming the relation is what
  keeps this from being a `genl` special case: an argument can equally be preserved
  along `tangiblePartOf`, `connectedTo`, or anything else transitive.  `transitiveInArg` carries
  the claim along `R`'s arrow and `transitiveInArgInverse` against it, the directions of
  Cyc's `transitiveViaArg` / `transitiveViaArgInverse`; the two names exist so neither
  direction requires declaring an inverse predicate that has no other purpose.

  Several declarations may name one argument position; their reaches **union**, since
  each independently licenses the claim.

  ## Preservation stays on one side of the type/instance line

  `genl` relates **types**, so `(typeLargerThan dog cat)` preserved along `genl` reaches
  `golden_retriever` and `maine_coon` and stops there.  It says nothing about Rex and
  Whiskers, and that is not a gap here to fill: `relation_kind` is a `disjoint_metatype`
  over `type_relation_predicate` and `instance_relation_predicate`, so one predicate
  symbol relates kinds *or* instances and never both.  A `typeLargerThan` that inherited
  across the line would be a predicate of both kinds at once, which the KB's own
  meta-ontology refuses.

  Preservation moves an argument along a relation, leaving the predicate and the level
  it lives at alone.  Crossing the line is a *different* claim — it links two
  predicates and has a quantifier reading to pin down (every member? some member?) —
  and the vocabulary for it is `(typeToInstancePred TypePred InstancePred)`, which
  records the pairing for a reader and is inferred from by nothing.

  ## Specificity, and why it is not the deleted axis

  The interesting case is a claim that inherits *and* a more specific claim that
  disagrees.  `(typicallyLargerThan dog cat)` reaches `[chihuahua maine_coon]`;
  `(typicallyLargerThan maine_coon chihuahua)` is stated directly.  The stated one
  wins, and the general one simply **does not fire for that pair** — undercutting, not
  defeat.  Nothing is derived, so there is nothing to arbitrate.

  That matters, because `docs/nmtms.md` deleted genl-based specificity as an
  arbitration axis on the grounds that it was inference *about* the knowledge rather
  than *from* it: it scored a type by the size of its up-closure, a numeric proxy that
  tied silently whenever the exception was not keyed on a narrower type.  Nothing here
  reconstructs an ordering.  Two claims are compared along the **very relation the
  inheritance travels down** — `[maine_coon chihuahua]` is below `[cat dog]` because
  `(genl maine_coon cat)` and `(genl chihuahua dog)` are edges the KB holds.  Claims
  that are genuinely incomparable are not ranked at all; they come back `:ambiguous`,
  which is the same answer the engine gives every other unresolvable clash.

  ## Strict versus typical, for free

  A `:monotonic` claim is **never** undercut.  Strength already propagates from a
  justification's antecedents, so `(typeLargerThan dog cat)` asserted `{:strength
  :monotonic}` inherits as known-true and a contrary specific claim is a
  contradiction, while `(typicallyLargerThan dog cat)` at the default `:default`
  inherits defeasibly and yields to the specific claim.  One declaration, both
  behaviours, and the difference is stated where it belongs: on the claim, not on the
  vocabulary.

  A stored `(not (P a b))`, and a stored `(P b a)` under an `asymmetric` mark on `P` or
  above it, are paired with the inherited claim by `discovery/preserving-nogoods`, whose
  members are the general claim and everything the reading rests on, so `decide/verdict`
  weighs the set and the weakest member decides (`clashing-claim` and `converse-claim`
  below, `docs/inherit.md` for the readings).

  Ground goals only.  An open argument is left to the fact and rule provers, in the
  shape `different` and the NAF operators already use — enumerating it would mean
  walking the inverse reach of every stored witness, which is a different and much
  larger question than the one a closed goal asks."
  (:require [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as st]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def declarations
  "The two declaration functors, mapped to the `along?` flag of the walk that serves
  them: true licenses `a` from `w` when `(R w a)` (along `R`'s arrow, `transitiveInArg`),
  false when `(R a w)` (against it, `transitiveInArgInverse`)."
  '{transitiveInArgInverse false, transitiveInArg true})

;; ---- one question, one set of closure reads ------------------------------

(def ^:dynamic *memo*
  "A per-question cache for the two reads every layer here repeats — an atom of
  `{[:positions pred context] -> …, [:reach rel along? x context] -> set}`, or nil
  for no memoization.

  Answering one ground goal asks for a predicate's declared positions from
  `applicable?`, `verdict`, `surviving` and `claims`, and for a term's reach once per
  preserved position and then again per *pair* of claims inside `undercut?`.  Neither
  answer can change while the question is being answered — a query never mutates
  belief — so the memo is created fresh per top-level question and needs no
  invalidation protocol at all.  `with-memo` reuses an outer one when a caller has
  already opened it, which is the discipline `observe/*reach-memo*` follows for the
  transitive closure."
  nil)

(defmacro with-memo
  "Answer `body` under a memo, reusing the enclosing one when there is one.

  **`body` must be eager**, the precondition `observe/with-search-scope` carries for the
  same reason: a lazy seq handed back from here realizes after the binding frame has
  popped, so every `positions` and `reach` its elements ask for is walked again from
  scratch. Nothing reports that — the answers are identical — so each seq-returning
  layer below realizes before it returns."
  [& body]
  `(binding [*memo* (or *memo* (atom {}))] ~@body))

(defn- memoized [k f]
  (if-let [m *memo*]
    (if (contains? @m k)
      (get @m k)
      (let [v (f)] (swap! m assoc k v) v))
    (f)))

(def virtual-relations
  "The relations `witness-terms` walks from a cached closure of the engine's own
  rather than from stored `(R a b)` facts — the type hierarchy and the context
  hierarchy.  Both are transitive by construction, so a `(transitive R)` declaration
  on them is inert (it never routes them to the generic prover); every other relation
  must carry one, which is what `wff/arg-preserving-problems` reads this set to decide.
  The same set the taxonomy names `closure-relations`."
  tax/closure-relations)

;; ---- the declared positions ---------------------------------------------
;; Read as ordinary stored sentexes through `matches-visible`, exactly as `arg` and
;; `genlArg` are — so they are context-scoped and belief-following with no cache of
;; their own, and a retracted declaration stops applying the moment it stops being
;; believed.

(defn usable-relation?
  "May a declaration's `R` be walked?  Either the engine owns its closure, or the KB
  says it composes.  Read at *use* and not only at assert, so retracting
  `(transitive R)` stops the inheritance it licensed the way retracting anything else
  here does — the declaration is stored, but a relation nobody currently says is
  transitive is one whose reach we have no right to close.  Read from `context`, like
  the declaration itself: a transitivity claim some invisible context makes is not
  a licence this one holds."
  [tax rel context]
  (boolean (or (contains? virtual-relations rel)
               (tax/has-prop? tax :transitive rel context))))

(def ^:private declaration-functors
  "`declarations`' keys, held rather than re-`keys`-ed: `declared-anywhere?` runs on
  every `applicable?` of a preservation-aware prover."
  (vec (keys declarations)))

(defn declared-about?
  "Could any stored declaration name `pred`?  The declaration functors' roots
  intersected with the argument root at position 1, where a declaration's predicate
  sits — one set intersection per functor, against a root that is empty for nearly
  every KB and tiny for the rest.

  This is a **gate, not an answer**: it is neither belief-filtered nor context-scoped,
  so a true says only that the real read is worth making.  A false is exact, because a
  declaration naming `pred` would be in that intersection whatever anyone believes
  about it.  That is also what makes it the right question for a *conservative* caller
  that wants no answer at all, only \"could preservation be in play here\":
  `recheck/cross-argument-predicate?` reads it to decide whether an exception conjunct's
  arguments may be compared with a trigger's, where an under-selection is a missed
  withdrawal.

  The gate is for the query path rather than the assert path.  `positions` is
  read by `TransitiveInArgProver.applicable?` and by `provers/shadowing-channels`, so it
  runs for **every goal's functor in the KB**, and each real read is two
  `matches-visible` calls.  Ungated, one declaration anywhere made a `genl` goal cost
  2.8x what it costs in a KB with none — a tax every query pays for a feature almost
  none of them use.

  Two stages, because the two questions have different prices and different answers.
  The **cardinality** read is O(1) and false for nearly every KB there is, so it comes
  first and nothing else runs; the **intersection** is a real (if small) index read
  and only a KB that declares something ever pays it."
  [kb pred]
  (let [idx (:index kb)]
    (boolean
     (some (fn [f]
             (and (pos? (reads/stored-count-with-functor idx f))
                  (seq (reads/as-stored-with-args idx f {1 pred}))))
           declaration-functors))))

(defn positions
  "`[{:n :rel :along? :handle :in} …]` — the preserved argument positions declared for
  `pred`, visible from `context`, whose relation is one this may actually walk.  Empty
  (the overwhelmingly common case) means the predicate inherits nothing and every
  consumer here is a no-op.

  Several declarations may name one position; they are not collapsed here, because
  their reaches **union** (`reach`) rather than compete.

  Each carries the `:handle` of the declaration it was read off, which is what
  `supports-for` names when a firing rests on the move it licenses: the declaration is
  as much a reason for an inherited claim as the claim itself, and retracting it has to
  withdraw whatever was concluded.

  **`:in` is the context the declaration was asserted in**, and it is here because
  `move-supports` orders the declarations that may license a move by content:
  `[rel, along?, n]` fixes the declaration's whole sentence, so two visible statements
  of it differ only in where they were said, and without `:in` the order would fall to
  `matches-visible`' answer set — handle order, which is arrival order.  It costs one
  record fetch per declaration, paid inside the memo rather than per firing, over a list
  that is empty for nearly every predicate.

  Realized rather than lazy, and memoized on `[pred context]`: four layers of one
  question ask for this, and each computation is two `matches-visible` calls.

  Behind a root-intersection gate on any declaration naming `pred` at all, so a
  predicate nobody declared about — which is every predicate but a handful, in every
  KB — pays one intersection against an empty root rather than two index lookups.  The
  same shape of gate `special.clj` puts in front of the exception re-check triggers,
  for the same reason."
  [kb pred context]
  (when (and (symbol? pred) (declared-about? kb pred))
    (memoized [:positions pred context]
              #(vec (for [[f along?] declarations
                          [h b] (res/matches-visible kb (list f pred '?n '?rel) context)
                          :let  [n (get b '?n) rel (get b '?rel)]
                          :when (and (integer? n) (pos? n) (symbol? rel)
                                     (usable-relation? (reasoning/taxonomy kb) rel context))]
                      {:n n :rel rel :along? along? :handle h
                       :in (:context (p/get-sentex (:records kb) h))})))))

(defn declarations-exist?
  "Does this KB declare any preservation at all?  One set-cardinality read per
  declaration functor, false for nearly every KB there is.  The forward join's gate:
  `chain/preserving-antecedent?` asks it before `positions`, once per chaining run
  through `chain/*declarations-cell*`, so a KB that declares nothing pays O(1) and stops.
  `moved-predicates`, `licensing-functors` and `preserved-pairs` ask it first as well
  (`declaration-index`).

  Neither belief-filtered nor context-scoped, for `declared`'s reason — a false is
  exact whatever anyone believes, since a declaration would be in the root."
  [kb]
  (let [idx (:index kb)]
    (boolean (some #(pos? (reads/stored-count-with-functor idx %)) declaration-functors))))

(defn declared
  "Every declaration's `[P R]` pair — the predicate that inherits, and the relation it
  inherits along — read off the predicate extents rather than through `matches-visible`.

  Deliberately **not** context-scoped and not belief-filtered, because the callers are
  `vaelii.impl.special`'s exception re-check triggers, and a trigger must be
  conservative in the direction the answer is: a declaration this edge cannot see
  still qualifies a rule in some context that can, and a missed trigger leaves a
  conclusion blocked (or unblocked) on evidence that has since moved.  Over-queueing
  costs a level-6 query at the next settle; under-queueing is a wrong belief.

  Costs one set-cardinality read per functor on a KB that declares none, which is
  nearly all of them, and a record fetch per stored declaration otherwise.  A negated
  declaration is in the same predicate extent and drops out on its shape, as does one of
  another arity."
  [kb]
  (let [recs (:records kb) idx (:index kb)]
    (into #{}
          (comp (filter #(pos? (reads/stored-count-with-functor idx %)))
                (mapcat #(reads/as-stored-with-functor idx %))
                (keep #(p/get-sentex recs %))
                (keep (fn [sxr]
                        (let [s (:sentence sxr) [_ pred _ rel] s]
                          (when (and (= 4 (count s)) (symbol? pred) (symbol? rel))
                            [pred rel])))))
          declaration-functors)))

;; ---- the reach of one argument ------------------------------------------

(defn- fact-reach
  "Reflexive-transitive reach of `x` over a declared-transitive `rel`, read from the
  believed facts.  The virtual relations never come here — their closures are the
  engine's own, which is the whole reason they are `virtual-relations`."
  [kb rel along? x context]
  (let [step (fn [n]
               (into #{} (keep #(get (second %) '?rv))
                     (res/matches-visible
                      kb (if along? (list rel '?rv n) (list rel n '?rv)) context)))]
    (loop [seen #{x}, frontier [x]]
      (if-let [n (peek frontier)]
        (let [fresh (remove seen (step n))]
          (recur (into seen fresh) (into (pop frontier) fresh)))
        seen))))

(def ^:private bounded-reach-limit
  "The most terms a `genl` reach is walked for and held as a set.  Past it a membership
  is a walk per term (`witness?`) and the closure is never built."
  1024)

(def ^:private walks-before-reach
  "How many memberships past the bound one term's reach answers by walking before the
  question reads the reach whole (`witness?`).  A walk toward a shallow term climbs
  about as much of the ancestry as the whole reach does, so each walk past the first
  few costs what reading the reach once would: a term asked twice pays at most twice,
  and one asked often stops walking early."
  2)

(def ^:private whole-reach-limit
  "The most terms one whole reach is walked for (`whole-reach`).  Past it the walk stops,
  holds nothing, and the term's memberships stay a walk each: a broad type's down-closure
  is most of the KB's types."
  65536)

(def ^:private whole-reach-budget
  "The most terms the whole reaches one memo holds may come to together (`whole-reach`):
  past it the least recently read are dropped, and a term read again is walked again.
  The memo lives for one question or one discovery pass, and is dropped with it."
  1048576)

(defn- unscoped? [context] (or (nil? context) (sx/variable? context)))

(defn- scoped
  "`(f)` with the scoped walks' neighbours held for the question or pass
  (`tax/with-neighbours`): a discovery pass tests the reach of every argument term of
  every stored claim from a context, each test a walk whose every edge asks whether a
  supporter is believed there, and belief does not move while the pass asks."
  [f]
  (tax/with-neighbours (memoized [:neighbours] #(atom {})) f))

(defn- bounded-reach
  "The `genl` reach of `x` from `context` when it holds at most `bounded-reach-limit`
  terms, else nil: a walk of the edges `context` sees (of every active edge when it is
  unscoped) that stops at the limit and stores nothing in the closure cache
  (`tax/genls-within`), held in the memo for the question or pass.  A discovery pass reads the reach of every argument term of
  every stored claim, and building each through the closure cache overran it on a large
  KB: a closure built from its parents' held ones rebuilds whatever parents were
  evicted."
  [kb along? x context]
  (let [cx (when-not (unscoped? context) context)]
    (memoized [:bounded-reach along? x cx]
              #(let [tx (reasoning/taxonomy kb)]
                 (scoped (fn []
                           (if along?
                             (tax/specs-within tx x cx bounded-reach-limit)
                             (tax/genls-within tx x cx bounded-reach-limit))))))))

(defn witness-terms
  "The terms a claim's argument may be **stated of** for it to reach `x` at this
  position: `{w : (rel x w)}` for `transitiveInArgInverse`, `{w : (rel w x)}` for
  `transitiveInArg`.  Reflexive, so `x` itself is always among them and a directly-stated claim is
  found by the same walk as an inherited one.

  One declaration's reach.  Callers want a *position's*, which is the union over the
  declarations made at it — `reach`.

  The `genl` walk is **scoped to `context`**, exactly as `fact-reach` is: a claim
  travels along the edges the asking context can see and no others, or a context
  would inherit `(typeLargerThan dog cat)` down to a subtype some invisible theory
  declared.  `genlCx` stays global — the context closure is (docs/taxonomy.md,
  the stated exception), and a preservation along it is a claim about the topology,
  which is universal.

  Memoized on `[rel along? x context]` for the life of one question.  The virtual
  relations read a cached closure and would survive without it; a **fact-relation** is
  the one that must not be re-walked, since each walk costs a `matches-visible` per
  node and `undercut?` asks for the same term's reach once per pair of claims."
  [kb {:keys [rel along?]} x context]
  (memoized [:reach rel along? x context]
            (fn []
              (let [tx (reasoning/taxonomy kb)]
                (case rel
                  ;; a reach within the bound is walked and not built through the
                  ;; closure cache (`bounded-reach`): the same set
                  genl        (or (bounded-reach kb along? x context)
                                  (scoped #(if along?
                                             (tax/specs tx x context)
                                             (tax/genls tx x context))))
                  genlCx (if along? (tax/context-down tx x) (tax/context-up tx x)) ; global on purpose
                  (fact-reach kb rel along? x context))))))

(defn- reach
  "The terms one argument may be stated of, over **every** declaration at its
  position: a union, because each independently licenses the claim.  A position
  preserved along both `genl` and a declared-transitive `tangiblePartOf` reaches what either
  reaches, and `below?` compares along the same union."
  [kb poss x context]
  (if (= 1 (count poss))
    (witness-terms kb (first poss) x context)   ; the common case: no set to rebuild
    (into #{} (mapcat #(witness-terms kb % x context)) poss)))

(defn- whole-reach
  "The `genl` reach of `x` from `context`, whole, walked through the edges it sees and
  stored nowhere but the question's memo: never through the closure cache, whose builds
  from held parents a discovery pass over a large KB overran.  nil, and remembered so,
  when it holds more than `whole-reach-limit` terms; the walk stops there and holds
  nothing.  The memo holds the reaches in a weighted LRU bounded by `whole-reach-budget`,
  so a discovery pass, which moves from goal term to goal term, keeps the recent ones
  where a budget spent once would leave every later term a walk per membership."
  [kb along? x cx]
  (let [lru (memoized [:whole-reach]
                      #(caches/weighted-lru (constantly whole-reach-budget)
                                            (fn [r] (if (set? r) (max 1 (count r)) 1))))
        k   [along? x cx]
        hit (caches/lru-get lru k)]
    (cond
      (identical? ::past hit) nil
      (some? hit)             hit
      :else
      (let [tx (reasoning/taxonomy kb)
            r  (scoped (fn []
                         (if along?
                           (tax/specs-within tx x cx whole-reach-limit)
                           (tax/genls-within tx x cx whole-reach-limit))))]
        (caches/lru-put! lru k (if (some? r) r ::past))
        r))))

(defn- witness?
  "Is `t` among `witness-terms` of `x` at one declaration?  A `genl` reach is read
  bounded (`bounded-reach`), and past the bound the membership is a reachability walk of
  the edges `context` sees (`tax/genl?`, `tax/genl?-global` unscoped), memoized like the
  reach, so the closure is never built.  A term asked more than `walks-before-reach`
  such memberships has its reach walked whole once instead (`whole-reach`), when it holds
  few enough terms: a discovery pass tests every stored claim's argument against one goal
  term's reach, and a walk per argument climbs the same ancestry each time.  Every other
  reach is `witness-terms`."
  [kb {:keys [rel along?] :as pos} x t context]
  (if (= 'genl rel)
    (if-some [r (bounded-reach kb along? x context)]
      (contains? r t)
      (let [cx (when-not (unscoped? context) context)
            [sub super] (if along? [t x] [x t])
            n  (memoized [:walks along? x cx] #(volatile! 0))]
        (if-some [r (when (>= @n walks-before-reach) (whole-reach kb along? x cx))]
          (contains? r t)
          (memoized [:witness? sub super cx]
                    #(let [tx (reasoning/taxonomy kb)]
                       (vswap! n inc)
                       (if cx
                         (scoped (fn [] (tax/genl? tx sub super cx)))
                         (tax/genl?-global tx sub super)))))))
    (contains? (witness-terms kb pos x context) t)))

(defn- held-reach
  "`reach` of `x` over the declarations `poss` as a set, when each `genl` reach in it holds
  at most `whole-reach-limit` terms (`bounded-reach`, else `whole-reach`), or nil when one
  holds more.  Read through the memo, so a pass walks each term's reach once."
  [kb poss x context]
  (let [cx  (when-not (unscoped? context) context)
        one (fn [{:keys [rel along?] :as pos}]
              (if (= 'genl rel)
                (or (bounded-reach kb along? x context) (whole-reach kb along? x cx))
                (witness-terms kb pos x context)))]
    (if (= 1 (count poss))
      (one (first poss))
      (reduce (fn [acc pos] (if-some [r (one pos)] (into acc r) (reduced nil))) #{} poss))))

(defn- reaches?
  "Is `t` in `reach` of `x` over the declarations `poss`: one of them licenses it."
  [kb poss x t context]
  (boolean (some #(witness? kb % x t context) poss)))

(defn- reach-size
  "How many terms `reach` of `x` holds, when it holds at most `limit`, else ##Inf.  Only
  ever weighed against an extent to pick a retrieval path, which never changes the
  answer.  A `genl` reach is counted bounded (`bounded-reach`, then a walk of the edges
  `context` sees that stops at `limit`, `tax/genls-within`), so the closure is not built
  to be counted."
  [kb poss x context limit]
  (let [tx  (reasoning/taxonomy kb)
        cx  (when-not (unscoped? context) context)
        lim (long (min limit Long/MAX_VALUE))]
    (reduce (fn [n {:keys [rel along?] :as pos}]
              (let [m (if (= 'genl rel)
                        (if-some [r (bounded-reach kb along? x context)]
                          (count r)
                          (if-let [c (if along?
                                       (tax/specs-within tx x cx lim)
                                       (tax/genls-within tx x cx lim))]
                            (count c)
                            ##Inf))
                        (count (witness-terms kb pos x context)))
                    n (+ n m)]
                (if (> n limit) (reduced ##Inf) n)))
            0 poss)))

;; ---- the claims bearing on a goal ---------------------------------------

(defn- by-position
  "The declarations grouped by the argument position they preserve, dropping any
  position the goal does not have — a declaration naming argument 3 of a binary
  predicate is ill-advised but stored, and reading past the tuple's end is not the
  way to report it."
  [positions arity]
  (into {} (filter (fn [[n _]] (<= n arity))) (group-by :n positions)))

(defn- slots
  "What a claim's argument may be, per argument position of the goal: at a preserved
  position `{:reach terms :in? member? :size size :held held}`, `terms` a delay of the
  reach and `held` a thunk of `held-reach`, and `{:pinned term}` where the goal's own
  argument stands.

  The **product** of the reaches is the set of tuples a claim could be stated at, and
  it is what the two retrieval paths below are two ways of intersecting with what is
  actually stored.  Only enumerating the product reads a reach whole: reading the
  extent tests membership (`:in?`, `reaches?`), and weighing the two reads a size that
  stops at a limit (`:size`, `reach-size`), so a question answered off the extent
  builds no closure."
  [kb positions args context]
  (let [by-n (by-position positions (count args))]
    (mapv (fn [i]
            (if-let [poss (by-n (inc i))]
              (let [x (nth args i)]
                {:reach (delay (reach kb poss x context))
                 :in?   #(reaches? kb poss x % context)
                 :size  #(reach-size kb poss x context %)
                 :held  #(held-reach kb poss x context)})
              {:pinned (nth args i)}))
          (range (count args)))))

(defn- product-tuples
  "Every argument tuple a claim could be stated at — the product of the reaches,
  pinned elsewhere."
  [slots]
  (reduce (fn [tuples s]
            (let [terms (if-let [r (:reach s)] @r #{(:pinned s)})]
              (for [t tuples, w terms] (conj t w))))
          [[]]
          slots))

(def ^:private product-ceiling
  "Past this an extent stops being counted and is simply *large*.  The extent is counted
  first, and the product's size only up to it (`product-size`), so no reach is read whole
  to weigh the two; no extent reaches this."
  1e12)

(defn- product-size
  "How many tuples the product holds — the count the extent is weighed against — or
  ##Inf once it passes `limit`, since the caller asks only which is smaller."
  ^double [slots ^double limit]
  (reduce (fn [^double n s]
            (if (> n limit)
              (reduced ##Inf)
              (* n (double (if-let [size (:size s)] (size (/ limit n)) 1)))))
          1.0 slots))

(defn- extent-size
  "How many stored sentexes one open probe would walk: the predicate extents of every
  predicate the matcher fans the probe over, capped by whichever pinned argument position
  is most selective.  The fan is `pred`'s sub-predicates for a positive probe and its
  super-predicates for a negated one (`res/sub-predicates`, `res/super-predicates`), so a
  sub-predicate holding the facts is counted where the walk reads them.  The sum stops once
  it passes `limit`, the product's size, since the caller asks only which is smaller.

  Read through `order`, because that is where the pinned term will actually **sit** in
  the probe.  The converse an asymmetric predicate is denied by swaps the tuple
  indices, so a term pinned at tuple index 0 is looked up at sentence position 2.  Both
  roots span either polarity."
  [kb pred slots order negated? context limit]
  (let [idx  (:index kb)
        fan  (if negated?
               (res/super-predicates kb pred context)
               (res/sub-predicates kb pred context))
        rows (reduce (fn [n f]
                       (let [n (+ n (reads/stored-count-with-functor idx f))]
                         (if (> n limit) (reduced n) n)))
                     0 (or (not-empty fan) [pred]))]
    (double
     (reduce (fn [n j]
               (let [s (nth slots (nth order j))]
                 (if-some [t (:pinned s)] (min n (reads/stored-count-with-arg-global idx (inc j) t)) n)))
             rows
             (range (count order))))))

;; ---- the two ways to find them ------------------------------------------
;; A claim bearing on the goal is a stored sentence whose argument tuple lies in the
;; product.  There are two ways to intersect a product with a store, and which is
;; cheaper is a property of the KB rather than of the feature: **enumerate the
;; product** and probe each tuple (cost: the product), or **read the extent** of the
;; predicate with a variable at every preserved position and keep the tuples that land
;; in the product (cost: what was written about that predicate).  Both go through
;; `matches-visible`, so subsumption, the symmetric mirror, context visibility and
;; belief are the same set either way — the choice is retrieval, never semantics.

(defn- probe-var [j] (symbol (str "?w" j)))

(defn- probe-sentence
  "The sentence to look up.  `order` maps each argument position of the *sentence* to
  the tuple index it fills: the identity for a claim read forwards, `[1 0]` for the
  converse an asymmetric predicate is denied by.  `terms` supplies a term for a tuple
  index, or nil to leave a variable there."
  [pred slots order terms]
  (cons pred (map-indexed (fn [j ti]
                            (let [s (nth slots ti)]
                              (if (:reach s) (or (terms ti) (probe-var j)) (:pinned s))))
                          order)))

(defn- in-product?
  "Is `tuple` one of the tuples a claim bearing on the goal could be stated at?  Asked
  of every position, pinned ones included: the symmetric mirror can hand back a match
  whose arguments sit in the other order, and a pinned position is only pinned in the
  pattern."
  [slots tuple]
  (and (= (count tuple) (count slots))
       (every? (fn [i]
                 (let [s (nth slots i) t (nth tuple i)]
                   (if-let [in? (:in? s)] (in? t) (= t (:pinned s)))))
               (range (count slots)))))

(defn- bound-tuple
  "The tuple a match is a statement about, read back through `order` — the bindings at
  the preserved positions, the goal's own terms at the pinned ones.  nil when a
  preserved position came back unbound, which no match of this pattern can do."
  [bindings slots order]
  (reduce (fn [t j]
            (let [ti (nth order j) s (nth slots ti)]
              (if (:reach s)
                (if-some [v (get bindings (probe-var j))] (assoc t ti v) (reduced nil))
                (assoc t ti (:pinned s)))))
          (vec (repeat (count slots) nil))
          (range (count order))))

(def ^:dynamic *deadline*
  "The `System/nanoTime` instant a claim walk stops at, bound only by
  `provers/TransitiveInArgProver` from `budget/*deadline*`.  nil for every other reader of
  `claims` (the asymmetry check at `assert`, settle, forward chaining), which walk to the
  end whatever deadline an enclosing `ask` holds."
  nil)

(defn- believed-matches
  "`[tuple handle sentex]` for every believed sentex matching `sentence` that states
  something about a tuple in the product.  `known` is the tuple when the caller
  already has it — a ground probe binds nothing to read one back from.  `strong?` keeps
  the known-true sentexes alone.  `dl` is checked per probe and per row read
  (`budget/check-deadline!`)."
  [kb sentence slots order context known strong? dl]
  (budget/check-deadline! dl)
  (let [tms (reasoning/tms kb)]
    (for [[h b] (res/matches-visible kb sentence context)
          :let  [_     (budget/check-deadline! dl)
                 tuple (or known (bound-tuple b slots order))]
          :when (and tuple
                     (or (not strong?) (st/known-true? (jtms/defeat-class tms h)))
                     (in-product? slots tuple))
          :let  [sxr (p/get-sentex (:records kb) h)]
          :when (and sxr (jtms/in? tms h))]
      [tuple h sxr])))

(defn- extent-key [sentence order context strong?]
  [:extent-index sentence order context strong?])

(defn- extent-index
  "The matches of the open probe `sentence` from `context`, as `[tuple handle]`, grouped
  by the term at each preserved tuple index: `{ti {term [[tuple h] …]}}`, the known-true
  ones alone under `strong?`.  Held in the memo, so the questions of one discovery pass
  read a predicate's extent once between them.  The grouping reads no goal: the probe
  pins the pinned positions, and `slots` says only which tuple indices are preserved."
  [kb sentence slots order context strong?]
  (memoized (extent-key sentence order context strong?)
            #(let [tms  (reasoning/tms kb)
                   rows (into [] (keep (fn [[h b]]
                                         (when (or (not strong?)
                                                   (st/known-true? (jtms/defeat-class tms h)))
                                           (when-let [t (bound-tuple b slots order)] [t h]))))
                              (res/matches-visible kb sentence context))]
               (into {}
                     (comp (filter (fn [ti] (:reach (nth slots ti))))
                           (map (fn [ti] [ti (group-by (fn [[t]] (nth t ti)) rows)])))
                     (range (count slots))))))

(defn- indexed-rows
  "The rows of `extent-index` whose term at one preserved tuple index lies in that slot's
  `held-reach`, read from whichever of the reach and the index's terms is smaller, at the
  tuple index where that is smallest; nil when no preserved slot's reach is held.  A
  tuple index with no rows reads no reach."
  [slots index]
  (let [cost (fn [[ti groups]]
               (if (empty? groups)
                 [0 groups #{}]
                 (when-some [r ((:held (nth slots ti)))]
                   [(min (count r) (count groups)) groups r])))
        best (reduce (fn [b x] (if (or (nil? b) (< (first x) (first b))) x b))
                     nil (keep cost index))]
    (when-let [[_ groups r] best]
      (if (< (count r) (count groups))
        (into [] (mapcat #(get groups %)) r)
        (into [] (comp (filter #(contains? r (key %))) (mapcat val)) groups)))))

(defn- indexed-matches
  "`believed-matches` over the open probe `sentence`, read through `extent-index` and
  `indexed-rows`, then `in-product?` over the rest of each tuple.  nil when no preserved
  slot's reach is held, for the caller to read the extent row by row."
  [kb sentence slots order context strong?]
  (when-let [rows (indexed-rows slots (extent-index kb sentence slots order context strong?))]
    (let [tms (reasoning/tms kb)]
      (for [[tuple h] rows
            :when (in-product? slots tuple)
            :let  [sxr (p/get-sentex (:records kb) h)]
            :when (and sxr (jtms/in? tms h))]
        [tuple h sxr]))))

(def ^:dynamic *retrieval*
  "Which of the two paths finds the claims: `:auto` weighs the extent against the
  product per goal, `:extent` and `:product` force one.  The forcing values exist so a
  test can hold the two against each other on the same KB — they answer the identical
  claim set by construction (both filter `matches-visible` by the same
  `in-product?`), and `inherit_oracle_test` is the claim that they do."
  :auto)

(defn- found-claims
  "Every believed statement bearing on the goal at `order` and `negated?`, the known-true
  ones alone under `strong?`, by whichever of the two retrieval paths is cheaper for this
  KB.  Either path throws `budget/check-deadline!`'s signal once `*deadline*` passes."
  [kb pred slots order negated? context strong?]
  (let [wrap (fn [s] (if negated? (list 'not s) s))
        dl   *deadline*
        open (delay (wrap (probe-sentence pred slots order (constantly nil))))]
    ;; the index reads the extent whole before its first row, so a reader under a
    ;; deadline reads it row by row.  A known-true read takes an index the memo already
    ;; holds before the two paths are weighed: it holds the known-true statements alone,
    ;; and weighing the product walks the reaches an empty index does not read
    (or (when (and strong? (not dl) (not= :product *retrieval*)
                   (some-> *memo* deref (contains? (extent-key @open order context true))))
          (indexed-matches kb @open slots order context true))
        (if (case *retrieval*
              :extent  true
              :product false
              (let [extent (extent-size kb pred slots order negated? context product-ceiling)]
                (<= extent (product-size slots extent))))
          (or (when-not dl (indexed-matches kb @open slots order context strong?))
              (believed-matches kb @open slots order context nil strong? dl))
          (mapcat (fn [tuple]
                    (believed-matches kb (wrap (probe-sentence pred slots order tuple))
                                      slots order context tuple strong? dl))
                  (product-tuples slots))))))

(defn- strongest-per-tuple
  "One claim per tuple — the **strongest** believed statement of it, with its
  defeat-class.

  Strongest, and not merely the first found, because one tuple can be stated in
  several visible contexts at different strengths.  `:class` decides both whether a
  claim can be undercut and whether `checks/asymmetry-problem` refuses, so taking the
  first would key an *admission* decision on handle iteration order — and handles are
  allocated in assertion order, which is the one thing belief may never depend on.
  The maximum over the class lattice is a function of the content alone, and the ties
  it leaves are broken on the context **name**, then the sentence's printed form, for
  the same reason: one tuple can carry two sentences in one context at one class (the
  matcher is type-aware, so a goal fans over sub-predicates), and a tie left to the
  retrieval order would survive differently under the retrieval sweeps.

  The other statements of the tuple ride along as `:also`, in the same order, and only
  `supports-for` reads them: two statements of one tuple in contexts neither of which
  sees the other each license the claim in a reader the other does not reach, so each is
  a reading a firing can rest on.  Every decision about the claim — undercut, verdict,
  asymmetry — reads the winner alone."
  [kb polarity found]
  (->> found
       (map (fn [[tuple h sxr]]
              {:polarity polarity :handle h :sentence (:sentence sxr)
               :context (:context sxr) :tuple tuple
               :class (or (jtms/defeat-class (reasoning/tms kb) h) :default)}))
       (group-by :tuple)
       (map (fn [[_ cs]]
              ;; the strongest claim on a tuple: key built once per claim (min in one
              ;; pass), not per comparison of a full sort thrown away but for its first.
              ;; The sentence prints through `nm/print-key`, since `cs` is a bucket of a
              ;; `res/matches-visible` answer *set* and the winner's `:class` is what
              ;; `verdict` and `checks/asymmetry-problem` read — an ambient
              ;; `*print-length*` collapsing the key would decide an admission on the
              ;; order the retrieval happened to answer in
              (let [k (juxt #(- (st/rank-of (:class %)))
                            #(nm/name-key (:context %))
                            #(nm/print-key (:sentence %)))
                    w (nm/min-by-content-key k compare cs)]
                (if (next cs)
                  (let [others (into [] (comp (remove #(= (:handle w) (:handle %)))
                                              (distinct))
                                     cs)]
                    (cond-> w
                      (seq others) (assoc :also (nm/sort-by-content-key k compare others))))
                  w))))))

(defn- separation-test
  "`tax/separation-test` for the type `a` at `context`, honouring the
  `siblingDisjointException`s it reads; at an unscoped `context`, the unscoped test that
  exempts no pair, the union of what every reader separates, for a caller that asks on
  behalf of every reader (a trigger, the discovery pass)."
  [tax a context]
  (if (unscoped? context)
    (tax/separation-test tax a nil (constantly false))
    (tax/separation-test tax a context)))

(defn- separated-denials
  "`[tuple handle sentex]` for each believed membership `(S x)` `context` sees whose type
  `S` the taxonomy separates from `pred` there: a denial of `(pred x)`, since no term is a
  member of two separated types.  The candidate types are the predicates holding a stored
  fact at `x` (`reads/as-stored-predicates-at-arg`), each read through
  `believed-matches`.  Nothing is read when no separation reaches `pred`."
  [kb pred x slots context dl]
  (when-let [sep? (separation-test (reasoning/taxonomy kb) pred context)]
    (into []
          (mapcat #(believed-matches kb (list % x) slots [0] context [x] false dl))
          (into (sorted-set)
                (filter #(and (symbol? %) (not= pred %) (sep? %)))
                (reads/as-stored-predicates-at-arg (:index kb) 1 x)))))

(defn claims
  "Every believed claim bearing on the ground goal `(P a1 … an)`, each tagged with the
  argument tuple it is stated at and whether it argues `:for` or `:against`.

  Against comes from three places: an explicit `(not (P …))` at a tuple in range;
  when `P` is declared `asymmetric`, the converse `(P … y … x …)`, since a relation
  that cannot hold both ways is denied by its own mirror; and, for a **unary** goal
  `(P x)` with a preserved position, a membership `(S x)` of a type a separation holds
  apart from `P` at `context` (`separated-denials`), at the goal's own tuple.  The
  converse is only read for a **binary** goal, which is the only arity for which
  `asymmetric` means anything.

  **Every probe is made, and one tuple can yield several claims.**  A tuple where both
  `P` and `(not P)` are believed is a contradiction the KB already reports through
  `(contradictions kb)`; taking whichever probe answered first would have this read it
  as a clean `:for` and hand `verdict` a decision that the engine, looking at the same
  two sentexes, refuses to make.  Collecting both sends it to `verdict` as the
  `:ambiguous` it is.  The price is two probes per tuple rather than short-circuiting on
  the positive (three for an asymmetric predicate) — the `:against` sources are
  kept separately rather than folded, since they can be believed at different
  strengths and `undercut?` reads that per claim.

  The converse probe is skipped at a **self tuple** `[a a]`, where it would read the
  very sentex the positive probe just read and file it as opposition.  That is one
  fact disputing itself, not two claims disagreeing, and it is the one shape where
  collecting both polarities would manufacture the dilemma rather than report it.
  (`(P a a)` under an `asymmetric P` *is* wrong — asymmetry implies irreflexivity —
  but it is wrong in a way `contradictions` does not report either, so answering
  `:ambiguous` here would be this function inventing a verdict on its own.)

  `strong?` reads the known-true statements alone, which are all a caller keeping only
  known-true claims needs: `undercut?` drops none of them, and a tuple's strongest
  statement is known-true whenever one of its statements is.  It reads no separated
  membership: each `strong?` caller pairs a stored claim with a claim at another tuple."
  ([kb goal context] (claims kb goal context false))
  ([kb goal context strong?]
   (with-memo
     (let [pred  (nm/functor goal)
           args  (vec (nm/args goal))
           poss  (positions kb pred context)
           asym? (tax/has-prop? (reasoning/taxonomy kb) :asymmetric pred context)
           ;; With no preserved position the product is the goal's own arguments alone,
           ;; so this still answers "what is believed about exactly this tuple" — which
           ;; is what the asymmetry check needs of a predicate that inherits nothing.
           sl    (slots kb poss args context)
           fwd   (vec (range (count args)))
           probe (fn [order negated? polarity]
                   (strongest-per-tuple
                    kb polarity (found-claims kb pred sl order negated? context strong?)))]
       ;; realized here, inside the memo (`with-memo`): the probes read the store and
       ;; `strongest-per-tuple` groups lazily, so a seq handed back unrealized does all
       ;; of that with the memo gone
       (vec
        (concat
         (probe fwd false :for)
         (probe fwd true  :against)
         ;; The converse is read with the tuple indices swapped, so a stored `(P x y)`
         ;; is filed against the tuple `[y x]` it denies.
         (when (and asym? (= 2 (count args)))
           (remove #(= (first (:tuple %)) (second (:tuple %)))
                   (probe [1 0] false :against)))
         (when (and (= 1 (count args)) (seq poss) (not strong?))
           (strongest-per-tuple
            kb :against
            (separated-denials kb pred (first args) sl context *deadline*)))))))))

;; ---- specificity ---------------------------------------------------------

(defn- below?
  "Is tuple `t1` at or below `t2` — for every preserved position, is `t2`'s term one
  of the terms `t1`'s can be stated of?  The order is read off the same relations the
  inheritance travels, never off a score."
  [kb positions t1 t2 context]
  (every? (fn [[n poss]]
            (reaches? kb poss (nth t1 (dec n)) (nth t2 (dec n)) context))
          (by-position positions (count t1))))

(defn- undercut?
  "Is `c` displaced by a strictly more specific claim?  Only a `:default` claim can
  be: a `:monotonic` one is known-true, so a contrary specific claim is a
  contradiction to report rather than a refinement to defer to."
  [kb positions c others context]
  (and (= :default (:class c))
       (boolean (some (fn [o] (and (not= (:tuple o) (:tuple c))
                                   (below? kb positions (:tuple o) (:tuple c) context)))
                      others))))

(def ^:dynamic *default-contraries-set-aside*
  "True while `chain` reads a preserved antecedent: a `:default` claim that denies the
  goal is left out before the survivors are read, so a firing it alone undercuts is made,
  and stored with a defeat of its conclusion resting on that claim (`contraries`,
  design ruling 25).  The prover reads every claim."
  false)

(defn surviving
  "The believed claims bearing on `goal` that a strictly more specific one has not
  displaced, each carrying its `:polarity` and `:class`.  The raw material both
  consumers read: the prover turns it into a verdict, and `checks/asymmetry-problem`
  asks the narrower question of whether any survivor is **known-true**.  Under
  `*default-contraries-set-aside*` a `:default` claim against the goal is not read."
  [kb goal context]
  (with-memo
    (let [poss (positions kb (nm/functor goal) context)
          cs   (cond->> (claims kb goal context)
                 *default-contraries-set-aside*
                 (into [] (remove #(and (not= :for (:polarity %)) (= :default (:class %))))))]
      ;; realized inside the memo, and this is the layer where it matters most:
      ;; `undercut?` compares every claim against every other and each comparison walks
      ;; a `reach` per preserved position, so a seq escaping the binding pays that
      ;; product uncached.  Both callers outside this namespace drain it
      ;; (`checks/asymmetry-problems`, `provers`), so nothing is realized that a lazy
      ;; answer would have skipped.
      (into [] (remove #(undercut? kb poss % cs context)) cs))))

(defn verdict
  "What the preserved claims say about the ground goal:

    `:for`       — some claim reaches it and nothing surviving disagrees
    `:against`   — the surviving claims deny it
    `:ambiguous` — surviving claims disagree at incomparable specificity, which is a
                   dilemma and is deliberately not decided here
    `nil`        — nothing bears on it, or the predicate declares no preserved position

  Claims displaced by a strictly more specific one drop out first; that is where a
  general default yields to a specific statement without either being defeated."
  [kb goal context]
  ;; Gated on a declared position: without one there is no inheritance to perform, and
  ;; answering from the goal's own tuple would just be `FactProver` wearing a hat.
  (with-memo
    (when (seq (positions kb (nm/functor goal) context))
      (let [polarity (into #{} (map :polarity) (surviving kb goal context))]
        (cond
          (= polarity #{:for})     :for
          (= polarity #{:against}) :against
          (seq polarity)           :ambiguous)))))

(defn contraries
  "The surviving claims (`surviving`, every claim read) that do not argue for `goal` in
  `context`: what keeps a `:for` verdict from it.  A firing over `goal` whose contraries
  are all `:default` is stored with a defeat resting on each (design ruling 25)."
  [kb goal context]
  (binding [*default-contraries-set-aside* false]
    (with-memo
      (into [] (remove #(= :for (:polarity %))) (surviving kb goal context)))))

(defn ground-goal?
  "A closed positive literal this can speak about.

  A negated goal is left alone: `(not (P a b))` asks whether the claim is *refuted*,
  and an inheritance that only ever licenses claims has nothing to say about that —
  `:against` here means \"not licensed\", the open-world reading, not \"licensed to be
  false\"."
  [goal]
  (and (sequential? goal) (seq goal)
       (symbol? (nm/functor goal))
       (not= 'not (nm/functor goal))
       (seq (nm/args goal))
       (every? sx/ground-term? (nm/args goal))))

;; ---- what an inherited claim rests on ------------------------------------
;;
;; An inherited claim is not stored, so it has no handle for a justification to name.
;; What it does have is the sentexes it was **read from**: the claim actually stated,
;; the declaration licensing the move, and the relation edges the reach travelled —
;; every one of them an ordinary sentex with a handle and a context.  Naming them is
;; what gives an inherited antecedent the contract a matched one has: retraction
;; reaches whatever was concluded from it, `why` explains it, and placement can see
;; where its reasons live.  `docs/inherit.md` and `docs/qcn.md` (the same shape, for a
;; relation a constraint network entails).
;;
;; It is *a* witness per reader rather than every witness, the simplification the
;; qualitative support makes for the same reason: a claim reachable two ways through
;; contexts one reader sees carries one justification, and the second route is re-derived
;; after a retraction rather than recorded in advance.  Two routes stated in contexts
;; neither of which sees the other are both named, one reading each (`supports-for`),
;; since each places the conclusion in a reader the other does not reach.

(defn- supporter-rank
  "The strength rank of handle `h` under `sclass` (`handle → defeat class`, `:default`
  where it answers nil), or nil when `sclass` is nil and strength takes no part."
  [sclass h]
  (when sclass (st/rank-of (or (sclass h) :default))))

(defn- reading-rank
  "The rank of the weakest of handles `hs` under `sclass` — a reading's floor class — or
  nil when `sclass` is nil.  `:monotonic`'s rank for no handles."
  [sclass hs]
  (when sclass (reduce min (st/rank-of :monotonic) (map #(supporter-rank sclass %) hs))))

(defn- hidable-of
  "The members of `hs` that `hid` (`handle → boolean`, nil for none) marks as hidable by
  an except, as a set, or nil when none: the third member of a `tax/uncovered` label."
  [hid hs]
  (when hid (not-empty (into #{} (filter hid) hs))))

(defn- general-supporters
  "The believed sentexes supporting `sentence` visible from `context` that no other one
  covers (`tax/uncovered`, weighing strength under `sclass` as `claim-supports` does), as
  `[handle ctx]` pairs: the one stated most generally where
  their contexts are comparable, and one per context where two are stated in contexts
  neither of which sees the other, since each licenses a firing in a reader the other
  does not reach.  Ordered on the supporting sentex's **context name and printed
  sentence** — never on its handle, which is allocated in assertion order — and of two
  that cover each other the earlier is kept, so which supporter a firing names is a
  function of the content.  The sentence is the second key because the matches are a
  fan, not one sentence: a sub-predicate's sentex answers a query on its `genl`, so two
  matches can share a context while spelling different claims.  `hid` is
  `claim-supports`'."
  [kb sentence context sclass hid]
  (let [tx (reasoning/taxonomy kb)]
    (->> (res/matches-visible kb sentence context)
         (keep (fn [[h _]]
                 (when-let [sxr (p/get-sentex (:records kb) h)]
                   (when (jtms/in? (reasoning/tms kb) h)
                     [[(str (:context sxr)) (nm/print-key (:sentence sxr))]
                      [h (:context sxr)]]))))
         (sort-by first)
         (mapv second)
         (tax/uncovered tx (fn [[h c]] [(supporter-rank sclass h) (if (nil? c) #{} #{c})
                                        (hidable-of hid [h])])))))

(defn- with-supporters
  "Each of `alts` (`{:hs :ctxs}`) once per supporter in `sups` (`[handle ctx]` pairs),
  that supporter appended; `alts` unchanged when `sups` is empty."
  [alts sups]
  (if (empty? sups)
    alts
    (vec (for [{:keys [hs ctxs]} alts, [h c] sups]
           {:hs (conj hs h) :ctxs (conj ctxs c)}))))

(defn- licensed-terms
  "The terms a claim stated at `w` reaches at this position — `witness-terms` read the
  other way round, which is the same walk with the declaration's direction flipped.
  `witness-terms` asks what a *goal* may be stated of; the forward join asks what a
  *claim* licenses, and `(rel a w)` is one relation read from either end."
  [kb {:keys [rel along?]} w context]
  (witness-terms kb {:rel rel :along? (not along?)} w context))

(defn- fact-paths
  "The paths from `a` to `w` over the declared-transitive `rel` that `context` sees and
  no other path covers (`tax/uncovered-routes`), each the `[handle ctx]` of the stored
  fact stating each step; `[[]]` when `a` is `w`, `[]` when no path exists.

  What `taxonomy/general-reach-supports` is for the two virtual relations, over the very
  adjacency `fact-reach` walks — so a path is found for exactly the pairs the reach
  answers and the two cannot disagree about what a context reaches.  A path stated in
  general contexts covers one stated in a context below them, so a conclusion resting on
  it is placed as high as any route allows and a short route through a specific context
  does not drag it down; paths stated in contexts neither of which sees the other are
  each returned, since each places the conclusion in a reader the other does not reach.
  Each step names the facts stating it that no other fact stating it covers, ordered on
  the **context name and then on what the fact says**, so the witnesses are a function
  of the content rather than of the order the facts arrived in, and each step carries
  that key into the walk's own order (`tax/uncovered-routes`).  The sentence is in the
  key because the matcher is type-aware and a goal fans over sub-predicates: two
  believed sentexes routinely state one step from one context, and the handle chosen
  here becomes an antecedent of the recorded justification — the same completeness
  `general-supporters` keys on just above.  Under `sclass` a step carries its fact's
  rank, so a route is labelled with its weakest fact as `tax/reach-supports` labels one,
  and `hid` is `claim-supports`'."
  [kb rel along? a w context sclass hid]
  (let [tx    (reasoning/taxonomy kb)
        label (fn [[h c]] [(supporter-rank sclass h) (if (nil? c) #{} #{c}) (hidable-of hid [h])])
        step  (fn [n]
                (->> (res/matches-visible
                      kb (if along? (list rel '?rv n) (list rel n '?rv)) context)
                     (keep (fn [[h b]]
                             (let [v (get b '?rv)]
                               (when (and v (not= v n))
                                 (when-let [sxr (p/get-sentex (:records kb) h)]
                                   [v [h (:context sxr)]
                                    (str (:context sxr))
                                    (nm/print-key (:sentence sxr))])))))
                     (nm/sort-by-content-key
                      (juxt #(nm/print-key (nth % 0)) #(nth % 2) #(nth % 3))
                      compare)
                     (partition-by first)
                     (mapcat (fn [steps]
                               (let [keys (into {} (map (fn [[_ sw c t]] [sw [c t]])) steps)]
                                 (for [sw (tax/uncovered tx label (mapv second steps))]
                                   [(first (first steps)) sw (supporter-rank sclass (first sw))
                                    (boolean (and hid (hid (first sw)))) (keys sw)]))))))]
    (tax/uncovered-routes tx a w step)))

(defn- move-supports
  "The alternative supports licensing the step from the claim's term `w` to the goal's `a`
  at one preserved position, each `{:hs [handle …] :ctxs [ctx …]}`: the declaration that
  permits the move, the relation edges the reach travelled, and — for a fact-relation —
  the `(transitive R)` the reach is closed under (one alternative per uncovered
  statement of it, `general-supporters`), which `usable-relation?` reads at *use*
  and so may be withdrawn with nothing else moving; `:ctxs` are the contexts those
  sentexes were asserted in.  Empty when no declaration at this position reaches from
  one to the other through edges `context` can see.

  **One alternative with no handles when the position did not move**, and that is the
  whole of the reflexive case: a claim stated at the goal's own term rests on no edge
  and needs no licence, so it contributes nothing and the justification stays the one
  the ordinary matcher already records.

  Every declaration that reaches contributes its routes, and the alternatives another
  one covers are dropped (`tax/uncovered`): two statements of one declaration differ
  only in where they were said, and the one said more generally covers the other, while
  two said in contexts neither of which sees the other each license the move in a reader
  the other does not reach.  The declarations are taken in content order — `[rel,
  along?]` alone fixes a declaration's sentence, so the asserting context separates
  two visible statements of one declaration — and a tie keeps the earlier, so retracting
  one of two equivalent declarations does not withdraw a conclusion by coin-toss.

  Under `sclass` (`handle → defeat class`) the routes and the alternatives are weighed on
  their weakest member too (`tax/reach-supports`), so a stronger route stays beside a
  weaker one its contexts cover; nil leaves strength out.  `hid` is `claim-supports`'."
  [kb poss a w context sclass hid]
  (if (= a w)
    [{:hs [] :ctxs []}]
    (let [tx   (reasoning/taxonomy kb)
          alts (into []
                     (mapcat
                      (fn [{:keys [rel along? handle in]}]
                        (let [[sub super] (if along? [w a] [a w])]
                          (if (contains? virtual-relations rel)
                            (for [route (let [k (keyword rel) v (when (= 'genl rel) context)]
                                          (if (or sclass hid)
                                            (tax/reach-supports tx k sub super v sclass hid)
                                            (tax/general-reach-supports tx k sub super v)))]
                              {:hs   (into [handle] (map first) route)
                               :ctxs (into [in] (map second) route)})
                            (when-let [routes (seq (fact-paths kb rel along? a w context sclass hid))]
                              (with-supporters
                                (mapv (fn [route]
                                        {:hs   (into [handle] (map first) route)
                                         :ctxs (into [in] (map second) route)})
                                      routes)
                                (general-supporters kb (list 'transitive rel) context sclass hid))))))
                      (nm/sort-by-content-key
                       (juxt #(str (:rel %)) #(str (:along? %)) #(str (:in %))) compare poss)))]
      (tax/uncovered tx (fn [{:keys [hs ctxs]}]
                          [(reading-rank sclass hs) (tax/context-floor tx ctxs) (hidable-of hid hs)])
                     alts))))

(defn- claim-supports
  "The alternative readings of claim `c` at the goal's arguments `args`, each
  `{:hs [handle …] :ctxs [ctx …]}`: what the reading rests on beyond the claim itself —
  the declaration permitting each move, the relation edges the reach travelled, and, for
  a mirrored reading, the `(symmetric …)` that licensed the mirror — and the contexts
  those were asserted in.  nil when no declaration reaches from the claim's tuple to
  `args` through edges `context` can see; one alternative with no handles when the claim
  is stated at the goal's own tuple and nothing had to move.

  A position whose move has several uncovered alternatives multiplies the readings, and
  the products another covers are dropped (`tax/uncovered`), so each reading left places
  the conclusion in a reader no other reading reaches.

  The claim's **own** handle is deliberately absent: one caller names it separately
  (`supports-for`'s `:claim`) and the other makes it a member of a nogood in its own
  right (`clashing-claim`), and folding it in here would have each of them strip it
  back out.

  `by-n` is `by-position`'s grouping of the declared positions, hoisted by the caller
  because both of them already hold it.  `sclass` is `move-supports`'.

  `hid` (`handle → boolean`, or nil) marks the handles an except can hide.  A reading
  resting on one covers only the readings resting on it too, so a reading another
  covers stays a candidate in a reader where an except hides the covering one."
  [kb by-n args c context sclass hid]
  (when-let [alts (reduce (fn [acc i]
                            (if-let [ps (by-n (inc i))]
                              (let [ms (move-supports kb ps (nth args i) (nth (:tuple c) i) context
                                                      sclass hid)]
                                (if (seq ms)
                                  (vec (for [x acc, m ms]
                                         {:hs   (into (:hs x) (:hs m))
                                          :ctxs (into (:ctxs x) (:ctxs m))}))
                                  (reduced nil)))
                              acc))
                          [{:hs [] :ctxs []}]
                          (range (count args)))]
    ;; A claim whose stored orientation is not the tuple it was read at came through the
    ;; symmetric mirror, and that reading rests on a `(symmetric …)` declaration exactly
    ;; as a fact-relation reach rests on `(transitive R)`: name it, so retracting the
    ;; symmetry withdraws what only the mirror licensed.  The matcher mirrors each fanned
    ;; literal on *its own* declaration, so the one named is the stored sentence's
    ;; functor's — the goal predicate's only when they coincide.
    (let [sups (when (and (= 2 (count args))
                          (not= (vec (nm/args (:sentence c))) (:tuple c)))
                 (general-supporters kb (list 'symmetric (nm/functor (:sentence c))) context
                                     sclass hid))
          alts (mapv #(update % :hs (fn [hs] (into [] (distinct) hs)))
                     (with-supporters alts sups))
          tx   (reasoning/taxonomy kb)]
      (tax/uncovered tx (fn [{:keys [hs ctxs]}]
                          [(reading-rank sclass hs) (tax/context-floor tx ctxs) (hidable-of hid hs)])
                     alts))))

(defn- defeat-classes
  "`kb`'s `handle → defeat class` read, the `sclass` the opposing readings are weighed
  under."
  [kb]
  (let [tms (reasoning/tms kb)] #(jtms/defeat-class tms %)))

(defn- strongest-reading
  "The reading of claim `c` whose weakest member is strongest, as `[rank handles]`, or nil
  when none reaches: the one reading a caller that opposes the claim to a stored one
  takes, since the claim holds as strongly as its strongest reading.  Of two at one rank
  the earlier in `claim-supports`' content order is kept."
  [kb by-n args c context]
  (let [sclass (defeat-classes kb)]
    (reduce (fn [best {:keys [hs]}]
              (let [r (reading-rank sclass hs)]
                (if (or (nil? best) (> r (first best))) [r hs] best)))
            nil
            (claim-supports kb by-n args c context sclass nil))))

(defn claim-reading
  "The handles of claim `c`'s `strongest-reading`, `c` a `surviving` claim bearing on the
  ground `goal`, read at `goal`'s arguments from `context`: the reading `clashing-claim`
  pairs a stored claim with.  nil when no declaration reaches."
  [kb goal c context]
  (with-memo
    (let [args (vec (nm/args goal))
          poss (positions kb (nm/functor goal) context)]
      (when (seq poss)
        (second (strongest-reading kb (by-position poss (count args)) args c context))))))

(defn supports-for
  "What licenses the ground goal `(P a1 … an)` by preservation — a vector of `{:claim
  handle :handles [handle …]}`, each the claim it was read off and every sentex the
  reading rests on — empty when nothing does.

  `verdict` answers *whether*; this answers *from what*, which is what a justification
  needs.  The semantics are `verdict`'s exactly: the surviving claims must agree, so a
  goal the KB also denies, or one two claims disagree about at incomparable
  specificity, licenses nothing here either.

  **A goal the KB states directly licenses nothing**, and that is deliberate.
  `witness-terms` is reflexive, so a stored `(P a b)` is among the claims bearing on
  `(P a b)` — it is the diagonal, it rests on no edge, and the ordinary matcher already
  finds it with a justification of its own.  Answering it here too would hand the same
  conclusion a second justification resting on nothing the first did not already name.

  **One reading per reader the others do not reach.**  Each surviving claim, and each
  other statement of its tuple (`:also`), contributes its readings (`claim-supports`),
  and a reading is dropped when another is at least as
  strong — the claim's defeat class — and is seen from every reader that sees it
  (`tax/uncovered`).  A claim and a route stated in one context, beside a route stated in
  a sibling context, therefore license two readings, and a firing over each places the
  conclusion where that reading is seen.  The survivors are taken on defeat class first
  and then on content — the tuple, the context and the sentence, all spellings rather
  than handles (one tuple can carry two sentences at one class and context, the matcher
  being type-aware, and the chosen handle lands in a recorded justification) — and of two
  readings that cover each other the earlier is kept."
  [kb goal context]
  (with-memo
    (let [pred (nm/functor goal)
          args (vec (nm/args goal))
          poss (positions kb pred context)]
      (or (when (seq poss)
            (let [sv (surviving kb goal context)]
              (when (and (seq sv)
                         (= #{:for} (into #{} (map :polarity) sv))
                         (not-any? #(= (:tuple %) args) sv))
                (let [by-n (by-position poss (count args))
                      tx   (reasoning/taxonomy kb)
                      alts (into []
                                 (mapcat (fn [c]
                                           (for [c                 (cons c (:also c))
                                                 {:keys [hs ctxs]} (claim-supports kb by-n args c context nil nil)]
                                             {:claim   (:handle c)
                                              :handles (into [] (distinct) (cons (:handle c) hs))
                                              ::rank   (st/rank-of (:class c))
                                              ::ctxs   (cons (:context c) ctxs)})))
                                 ;; the key mixes a `str` tuple and a printed sentence —
                                 ;; built once per survivor, not per comparison; the
                                 ;; `[rank …]` tuple orders under `compare`.  Through
                                 ;; `nm/print-key`, because the survivor chosen here has
                                 ;; its `:handle` written into a recorded justification
                                 ;; and `sv` is drawn from a `res/matches-visible` answer
                                 ;; *set*
                                 (nm/sort-by-content-key (juxt #(- (st/rank-of (:class %)))
                                                               #(nm/print-key (:tuple %))
                                                               #(nm/name-key (:context %))
                                                               #(nm/print-key (:sentence %)))
                                                         compare
                                                         sv))]
                  (mapv #(dissoc % ::rank ::ctxs)
                        (tax/uncovered tx (fn [a] [(::rank a) (tax/context-floor tx (::ctxs a))])
                                       alts))))))
          []))))

(defn- strongest-claim
  "Of the surviving claims `sv` bearing on the tuple `args`, the one whose
  `strongest-reading`, capped at the claim's class, is strongest, as `[claim handles]`, or
  nil when no reading reaches or the strongest is not known-true: a reading is as strong
  as its weakest reason, so one resting on a `:default` declaration or edge is undercut
  as a `:default` claim is.  Of two at one rank the first on content: the tuple, then
  the asserting context, then what the claim says, all spellings rather than handles,
  since the chosen handle lands in a reported nogood."
  [kb by-n args sv context]
  (when-let [[r c hs]
             (reduce (fn [best c]
                       (if-let [[r hs] (strongest-reading kb by-n args c context)]
                         (let [r (min r (st/rank-of (:class c)))]
                           (if (or (nil? best) (> r (first best))) [r c hs] best))
                         best))
                     nil
                     (nm/sort-by-content-key (juxt #(nm/print-key (:tuple %))
                                                   #(nm/name-key (:context %))
                                                   #(nm/print-key (:sentence %)))
                                             compare
                                             sv))]
    (when (st/known-true? (st/class-of-rank r)) [c hs])))

(defn clashing-claim
  "The **known-true** claim that reaches `sentence`'s own tuple by preservation and
  denies it — `{:sentence :context :claim handle :handles [handle …] :class}` — or nil.

  `sentence` is a stored fact of a preserved predicate, in either polarity; the claim
  looked for is the opposite one.  A stored `(not (P a b))` is denied by a `(P w b)`
  above it, and a stored `(P a b)` by a `(not (P w b))` above it, since `claims` reads
  both polarities out of the reach.

  **Known-true, because that is the whole of what `undercut?` leaves standing.**  A
  `:default` general claim yields to a nearer contrary one: it is undercut, never fires
  for that tuple, and there is nothing for anybody to report (docs/inherit.md).  A
  `:monotonic` one is not undercut, so it survives beside the stored claim and the pair
  is a nogood with no second stored member.  This names it.

  **The claim's own tuple is excluded**: a claim stated at the very tuple `sentence` is
  about is an ordinary `P` beside an ordinary `(not P)`, both stored, which the negation
  family pairs (`decide/note-candidate!`).  A claim stating `sentence` itself is excluded
  too: an asymmetric converse carried round a `genl` cycle to its own tuple is one
  sentence on both sides (docs/inherit.md).

  `:handles` is the reading's support and not the claim: the declaration that permits
  each move, the relation edges the reach travelled, the `(transitive R)` a fact-relation
  reach is closed under, and the `(symmetric …)` behind a mirrored reading.  One claim is
  named where several reach (`strongest-claim`).  Asked from the vantage of `context`: a
  claim in a context that cannot see the general one is not denied by it."
  [kb sentence context]
  (with-memo
    (let [neg? (and (sequential? sentence) (= 'not (nm/functor sentence))
                    (= 2 (count sentence)))
          body (if neg? (second sentence) sentence)]
      (when (ground-goal? body)
        (let [pred (nm/functor body)
              args (vec (nm/args body))
              poss (positions kb pred context)]
          (when (seq poss)
            (let [want (if neg? :for :against)
                  ;; known-true claims alone, which `undercut?` never drops
                  sv   (->> (claims kb body context true)
                            (filter #(and (= want (:polarity %))
                                          (st/known-true? (:class %))
                                          (not= (:tuple %) args)
                                          (not= (:sentence %) sentence))))]
              (when-let [[c hs] (strongest-claim kb (by-position poss (count args)) args sv
                                                 context)]
                {:sentence (if neg? body (list 'not body))
                 :context  context
                 :claim    (:handle c)
                 :handles  hs
                 :class    (:class c)}))))))))

(defn- converse-goal
  "`(P b a)` for a ground positive binary `sentence` `(P a b)` with `a` distinct from `b`
  whose functor `P`, or a super-predicate of it, carries an `asymmetric` mark
  (`tax/props-over`, read from `context`, or anywhere for `'?ctx`), else nil."
  [kb sentence context]
  (when (and (ground-goal? sentence) (= 3 (count sentence)))
    (let [[pred a b] sentence
          tax        (reasoning/taxonomy kb)]
      (when (and (not= a b)
                 (seq (tax/props tax :asymmetric))
                 (seq (tax/props-over tax :asymmetric pred (when-not (= '?ctx context) context))))
        (list pred b a)))))

(defn converse-claim
  "The **known-true** claim that reaches the converse `(P b a)` of the stored `sentence`
  `(P a b)` by preservation, while an `asymmetric` mark on `P` or on a super-predicate of
  it holds at `context` — `{:sentence (P b a) :context :claim handle :handles [handle …]
  :class}` — or nil.  The mark says the two tuples cannot both hold, so the inherited
  converse and the stored tuple are a nogood as `clashing-claim`'s pair is.  A claim
  stated at `(P b a)` itself is a stored converse, which the `asymmetric` family pairs
  (`decide/note-candidate!`), and is excluded.  The reading and the choice among several
  claims are `clashing-claim`'s (`strongest-claim`)."
  [kb sentence context]
  (with-memo
    (when-let [goal (converse-goal kb sentence context)]
      (let [pred (nm/functor goal)
            args (vec (nm/args goal))
            poss (positions kb pred context)]
        (when (seq poss)
          (let [sv (filter #(and (= :for (:polarity %))
                                 (st/known-true? (:class %))
                                 (not= (:tuple %) args))
                           (claims kb goal context true))]
            (when-let [[c hs] (strongest-claim kb (by-position poss 2) args sv context)]
              {:sentence goal
               :context  context
               :claim    (:handle c)
               :handles  hs
               :class    (:class c)})))))))

(defn claims-stored?
  "Does the store hold a sentex whose functor is `pred` or a predicate below it
  (`tax/specs-global`), in either polarity, in any context, believed or not?  False means
  `claims` of `pred` is empty for every goal and every reader, since every claim is a
  stored statement on a predicate the matcher fans `pred` over.  The closure is unscoped
  because it answers for every reader: a scoped fan is a subset of it.  One index count
  per predicate in the closure, memoized on `pred`."
  [kb pred]
  (memoized [::claims-stored pred]
            #(let [idx (:index kb)]
               (boolean (some (fn [f] (pos? (reads/stored-count-with-functor idx f)))
                              (tax/specs-global (reasoning/taxonomy kb) pred))))))

(defn separated-preserved
  "The predicates a stored declaration names (`declared`) that the taxonomy separates from
  the type `s` at `context` (`tax/separation-test`) and that some stored claim states
  (`claims-stored?`), sorted: a membership `(s x)` denies `(P x)` for each.  At `'?ctx`
  the read is unscoped and exempts no pair, the union of what every reader separates.  A
  type no separation reaches reads no declaration.  Memoized on `[s context]`."
  [kb s context]
  (memoized [::separated s context]
            #(when (symbol? s)
               (when-let [sep? (separation-test (reasoning/taxonomy kb) s context)]
                 (filterv (fn [p] (and (sep? p) (claims-stored? kb p)))
                          (into (sorted-set) (comp (map first) (remove #{s}))
                                (memoized [::declared] (fn [] (declared kb)))))))))

(defn separated-claims
  "The **known-true** claims that reach `(P x)` by preservation, for each `P` the taxonomy
  separates at `context` from the type `S` of the stored membership `sentence` `(S x)`
  (`separated-preserved`), as `clashing-claim` answers: one `{:sentence (P x) :context
  :claim :handles :class}` per `P` some claim reaches.  A claim stated at `(P x)` itself
  is a stored membership the `disjoint` family pairs with `sentence`, and is excluded.
  The separating declarations are not among `:handles`: each asker reads the separation
  again, as `converse-claim`'s reads the `asymmetric` mark."
  [kb sentence context]
  (with-memo
    (when (and (ground-goal? sentence) (= 2 (count sentence)))
      (let [[s x] sentence]
        (into []
              (keep (fn [pred]
                      (let [poss (positions kb pred context)]
                        (when (seq poss)
                          (let [sv (filter #(and (= :for (:polarity %))
                                                 (st/known-true? (:class %))
                                                 (not= (:tuple %) [x]))
                                           (claims kb (list pred x) context true))]
                            (when-let [[c hs] (strongest-claim kb (by-position poss 1) [x] sv
                                                               context)]
                              {:sentence (list pred x)
                               :context  context
                               :claim    (:handle c)
                               :handles  hs
                               :class    (:class c)}))))))
              (separated-preserved kb s context))))))

(defn- separation-supports
  "Each way a reader can see the type `s` separated from `pred`, as `{:handles :contexts}`:
  the contexts of one derivation (`tax/disjointness-witnesses`), and the supporters stated
  in them of the declarations separating the two (`tax/separating-keys`, unscoped and
  exempting nothing).  Memoized per pair: discovery asks one pair once per membership of
  `s` it reads."
  [kb s pred]
  (memoized [::separation-supports s pred]
            (fn []
              (let [tax  (reasoning/taxonomy kb)
                    recs (:records kb)
                    sups (into [] (comp (mapcat #(tax/visible-supporters tax % nil))
                                        (distinct)
                                        (map (fn [h] [h (:context (p/get-sentex recs h))])))
                               (tax/separating-keys tax s pred nil (constantly false)))]
                (into #{}
                      (map (fn [w]
                             {:handles  (into #{} (keep (fn [[h c]] (when (or (nil? c) (contains? w c)) h)))
                                              sups)
                              :contexts w}))
                      (tax/disjointness-witnesses tax s pred))))))

(defn denial-readings
  "Each reading of a claim that denies `sentence` by preservation, read from every
  context at once, as `{:handles :contexts}`: the claim and what the reading rests on
  (`claim-supports`), and the contexts those are stated in.  Empty when nothing reaches
  `sentence`'s tuple to deny it.

  `clashing-claim` answers from one reader, and a reader that sees `sentence` but not
  the claim, or not an edge the reach travels, finds nothing.  This is the question
  asked before any reader is chosen: which handles a reader would have to see for the
  clash to be in view.  `discovery/preserving-entry` asks the clash from the most general
  contexts that see each reading with `sentence` and no except hiding one of them.

  Read at `'?ctx`, which every layer here passes through as unscoped: the matcher reads
  every context, and the `genl` walk and the mark reads take every edge and every
  statement.  Over-approximating in both directions it can: every class of claim, and
  claims `undercut?` would drop, since a claim undercut in the whole KB can survive in a
  reader that does not see the claim undercutting it.  A reader asked because of a
  reading named here re-reads the clash on what it sees, so a reading that turns out to
  convict nothing costs one question.

  The claim's own tuple is excluded, as `clashing-claim` excludes it: a claim stated at
  `sentence`'s tuple is a stored pair, found by the partner reads that pair stored
  sentexes.  The readings of `converse-claim`'s converse are named too, each joined by
  an `asymmetric` statement that makes the converse deny `sentence`, and those of
  `separated-claims`' claims, each joined by a way to see the separation
  (`separation-supports`)."
  [kb sentence]
  (with-memo
    (let [neg?  (and (sequential? sentence) (= 'not (nm/functor sentence))
                     (= 2 (count sentence)))
          body  (if neg? (second sentence) sentence)
          cls   (defeat-classes kb)
          hid   (memoize #(exc/closure-excepted-anywhere? kb %))
          reads (fn [goal want]
                  (let [args (vec (nm/args goal))
                        poss (positions kb (nm/functor goal) '?ctx)]
                    (if (empty? poss)
                      #{}
                      (let [by-n (by-position poss (count args))]
                        (into #{}
                              (comp (filter #(and (= want (:polarity %)) (not= (:tuple %) args)))
                                    (mapcat #(cons % (:also %)))
                                    (remove #(= (:sentence %) sentence))
                                    (mapcat (fn [c]
                                              (for [{:keys [hs ctxs]} (claim-supports kb by-n args c '?ctx
                                                                                      cls hid)]
                                                {:handles  (into #{(:handle c)} hs)
                                                 :contexts (into #{(:context c)} ctxs)}))))
                              (claims kb goal '?ctx))))))]
      (if-not (ground-goal? body)
        #{}
        (-> (reads body (if neg? :for :against))
            (into (when-let [goal (when-not neg? (converse-goal kb body '?ctx))]
                    (let [tax  (reasoning/taxonomy kb)
                          mark (into #{}
                                     (mapcat #(tax/prop-supporter-contexts tax :asymmetric %))
                                     (tax/props-over tax :asymmetric (nm/functor body)))]
                      (for [r (reads goal :for), [h c] mark]
                        (-> (update r :handles conj h)
                            (update :contexts #(cond-> % c (conj c))))))))
            (into (when (and (not neg?) (= 2 (count body)))
                    (let [[s x] body]
                      (for [pred (separated-preserved kb s '?ctx)
                            :let [sups (separation-supports kb s pred)]
                            r    (reads (list pred x) :for)
                            w    sups]
                        (-> (update r :handles into (:handles w))
                            (update :contexts into (:contexts w))))))))))))

;; ---- enumerating what a claim licenses -----------------------------------
;; A backward goal is closed and asks one question.  A **forward** antecedent is a
;; pattern, so the question runs the other way: which tuples does a stored claim
;; license, and which of them does this literal admit?  That is the walk `docs/inherit.md`
;; declines to make for an open *goal* — it is the larger question — and the forward
;; join is exactly the caller for whom it is the right one, because a conclusion has to
;; be drawn per tuple whether or not anybody asked.

(defn- goal-bindings
  "The bindings making the literal's argument list `args` the tuple `t`, or nil where
  they cannot: a ground argument must be the tuple's term, and a variable written twice
  must take one value."
  [args t]
  (reduce (fn [b i]
            (let [a (nth args i) v (nth t i)]
              (if (and (symbol? a) (sx/variable? a))
                (if-let [prev (get b a)]
                  (if (= prev v) b (reduced nil))
                  (assoc b a v))
                (if (= a v) b (reduced nil)))))
          {}
          (range (count args))))

(defn- stated-claims
  "`[tuple handle]` for every believed claim of `pred` this literal could inherit from
  — the predicate's extent, with the literal's own ground arguments pinned at the
  positions that preserve nothing, since there the claim's term *is* the conclusion's.

  A preserved position is left open even where the literal pins it: the claim licensing
  that term is stated *above* it, and narrowing to the term itself would find only the
  diagonal.

  A **symmetric** predicate's claim is a statement of both orientations, and an open
  probe surfaces only the stored one — the mirror shares its handle, so the matcher's
  mirrored probe of an open pattern adds no second row.  Ground probes bake the
  orientation into the pattern (which is how the backward entry point reads the mirror), so
  the swap has to happen here: a tuple whose stored sentence's own functor is declared
  symmetric — the fan surfaces sub-predicates, and the matcher mirrors each fanned
  literal on *its* declaration — is also read backwards, kept where the pattern's
  pinned positions still agree.

  The `symmetric` mark is read unscoped, a superset that `supports-for` narrows at
  `context`."
  [kb pred args poss context]
  (let [by-n (by-position poss (count args))
        pat  (mapv (fn [i]
                     (let [a (nth args i)]
                       (if (or (by-n (inc i)) (and (symbol? a) (sx/variable? a)))
                         (probe-var i)
                         a)))
                   (range (count args)))
        base (for [[h b] (res/matches-visible kb (cons pred pat) context)
                   :when (jtms/in? (reasoning/tms kb) h)
                   :let  [t (mapv (fn [i]
                                    (let [p (nth pat i)]
                                      (if (= p (probe-var i)) (get b p) p)))
                                  (range (count args)))]
                   :when (every? some? t)]
               [t h])]
    (if-not (= 2 (count args))
      base
      (let [tx   (reasoning/taxonomy kb)
            syms (into #{} (filter #(tax/has-prop? tx :symmetric %))
                       (res/sub-predicates kb pred nil))]
        (if (empty? syms)
          base
          (concat base
                  (for [[t h] base
                        :let  [sxr (p/get-sentex (:records kb) h)
                               f   (some-> sxr :sentence nm/functor)]
                        :when (and f (contains? syms f))
                        :let  [rt [(nth t 1) (nth t 0)]]
                        :when (and (not= rt t)
                                   (every? #(let [pp (nth pat %)]
                                              (or (= pp (probe-var %)) (= pp (nth rt %))))
                                           (range 2)))]
                    [rt h])))))))

(defn- licensed-product
  "Every tuple a claim stated at `w` licenses that the literal's arguments admit — the
  product of the licensed terms at the preserved positions, the claim's own term
  elsewhere, and a ground argument of the literal pinned wherever it has one."
  [kb by-n args w context]
  (reduce (fn [tuples i]
            (let [terms (if-let [ps (by-n (inc i))]
                          (let [r (if (= 1 (count ps))
                                    (licensed-terms kb (first ps) (nth w i) context)
                                    (into #{} (mapcat #(licensed-terms kb % (nth w i) context)) ps))
                                a (nth args i)]
                            (if (and (symbol? a) (sx/variable? a))
                              r
                              (when (contains? r a) #{a})))
                          #{(nth w i)})]
              (for [tp tuples, x terms] (conj tp x))))
          [[]]
          (range (count args))))

(defn solve-with-support
  "Solve the antecedent literal `literal` by **preservation**: a seq of `{:bindings
  :claim :handles}`, one per reading of an inherited claim it matches, each carrying the
  claim it was read off and the handles the reading rests on.  A tuple reached over
  routes stated in contexts neither of which sees the other has one reading per route
  (`supports-for`), and each becomes a firing placed where its route is seen.

  A closed literal asks `supports-for` once.  An open one enumerates: every believed
  claim of the predicate, the tuples it licenses, and then the same `supports-for` per
  tuple — so the tuples are *found* by the reach and *admitted* by the full semantics,
  and an antecedent can no more join on an undercut or disputed claim than `ask` can
  answer one.

  The diagonal is dropped (`supports-for`), so a claim stated at the tuple it is asked
  about stays the ordinary matcher's to find.  Nothing here replaces that matcher; the
  caller unions the two."
  [kb literal context]
  (with-memo
    (when (and (sequential? literal) (seq literal) (symbol? (nm/functor literal))
               (not= 'not (nm/functor literal)) (seq (nm/args literal)))
      (let [pred (nm/functor literal)
            args (vec (nm/args literal))
            poss (positions kb pred context)]
        (when (seq poss)
          (if (every? sx/ground-term? args)
            (not-empty (mapv #(assoc % :bindings {}) (supports-for kb literal context)))
            (let [by-n (by-position poss (count args))]
              ;; realized inside the memo: `licensed-product` walks a `reach` per
              ;; preserved position per claim and `supports-for` opens a memo of its own
              ;; per tuple, so an escaping seq shares nothing between the tuples of one
              ;; literal.  The join drains this per state (`chain/solve-preserving`),
              ;; so the whole product is what it consumes either way.
              (into [] (distinct)
                    (for [[w _] (stated-claims kb pred args poss context)
                          t     (licensed-product kb by-n args w context)
                          :when (not= t w)
                          :let  [b (goal-bindings args t)]
                          :when b
                          s     (supports-for kb (cons pred t) context)]
                      (assoc s :bindings b))))))))))

;; ---- which rules an arriving sentence moves ------------------------------

(def crossing-closure-cap
  "The most closure terms `crossing-claim?` reads the slot roster at.  The closure is
  `specs-global` of a `genl` edge's lower term together with `genls-global` of its upper
  one.  An edge whose closure holds more is not narrowed: every predicate preserved along
  `genl` is moved, read off the declarations' relation index with no index read.  The
  closures are walked through `tax/specs-global-within`, which stops one term past the
  cap, so an edge under a type with 20,000 subtypes pays 513 steps and not 20,000.

  The narrowing costs a slot-roster read per closure term per preserved position, and the
  fallback costs a full re-join of every rule on a predicate preserved along `genl`.  The
  bound keeps the first from growing with the closure: `(genl root_t top_t)` over 20,000
  leaves and one preserved position reads 20,000 slots without it."
  512)

(def permuting-marks
  "The marks under which the matcher reads a stored fact in more than one argument order:
  the functors whose arms install `tax/props :symmetric` and the `:commuting` table, which
  are what `res/matches-hierarchical` permutes a literal by (`sx/commuting-arrangements`).
  A late one moves what a rule's antecedent reaches over facts already stored, so
  `moved-predicates` and `chain/permuting-rejoin-rules` both key on it."
  '[symmetric commutative commutativeInArgs commutativeInArgAndRest])

(def ^:private permuting-mark-set (set permuting-marks))

(defn permuting-mark?
  "Is `f` one of `permuting-marks`?  A set lookup: every placement asks it of its
  conclusion's functor (`special/deduce-lifts`)."
  [f]
  (contains? permuting-mark-set f))

(defn- mark-group
  "The commuting group descriptor a stored mark states, `[:args [p …]]` or `[:rest f]`, or
  nil for anything else — a negated mark included, whose functor is `not`.  The same
  descriptors `special`'s arms install, with `(symmetric P)` read as `[:args [1 2]]`."
  [sentence]
  (let [[f q & more] sentence]
    (when (symbol? q)
      (case f
        symmetric               [:args [1 2]]
        commutative             [:rest 1]
        commutativeInArgAndRest (let [n (first more)]
                                  (when (and (integer? n) (pos? n)) [:rest n]))
        commutativeInArgs       (let [ps (vec (sort (distinct more)))]
                                  (when (and (> (count ps) 1)
                                             (every? #(and (integer? %) (pos? %)) ps))
                                    [:args ps]))
        nil))))

(defn- rearranges?
  "Do the commuting `groups` rearrange the argument list `s` into `t`?  Every position
  outside their components holds the same term in both, and each component holds the
  same terms with the same multiplicity — the arrangements `sx/commuting-arrangements`
  probes, read from the other end."
  [groups s t]
  (let [comps (sx/commuting-components groups (count s))
        moved (into #{} cat comps)
        at    (fn [v c] (frequencies (map #(nth v (dec %)) c)))]
    (and (every? #(or (contains? moved (inc %)) (= (nth s %) (nth t %))) (range (count s)))
         (every? #(= (at s %) (at t %)) comps))))

(def ^:private universal-context
  "Where the engine lifts a permuting mark (`special/universal-context`, which requires this
  namespace and so cannot be read from it)."
  sx/root-context)

(def ^:private permuted-mark-cap
  "The most mark statements on one predicate `permuted-read-supports` searches the
  subsets of.  Past it the reading names every statement it found as one conjunction."
  8)

(defn permuted-read-supports
  "The alternative sets of mark sentexes a read of the stored `sentence` at the argument
  list `tuple` rests on, each a vector of handles, or nil when `tuple` is the stored
  argument list or no believed mark licenses the rearrangement.

  The matcher reads a stored fact in every arrangement its own functor's permuting marks
  license (`res/raw-match`), and a firing reached through one of those arrangements holds
  only while a mark does.  So the reading names them, as `claim-supports` names the
  `(symmetric …)` a mirrored claim came through, and retracting the mark withdraws what
  only it licensed.

  **One alternative per minimal set of statements that licenses the rearrangement.**  A
  binary `(P a b)` read as `(P b a)` under both `(symmetric P)` and `(commutative P)` is
  licensed by either, and a firing naming both would go with the first retracted while the
  other still licenses it.  Two `commutativeInArgs` statements whose components are both
  moved license the read together, and that set is one alternative.  The statements are
  those stored on the fact's own functor, since the matcher permutes each fanned literal
  on its own declaration, and each is named by the believed sentexes stating it that
  `context` sees and no other covers, ordered on context name as `general-supporters`
  orders them.  Where the CxUniverse copy is believed it is the one named: the engine
  lifts every statement into it, so it stands while any statement does, as the store's
  sort does.  A firing is placed by its rule and the facts it matched and not by the
  statements named (`chain/placement-antecedents`), so the copy serves a fact in a
  context that cannot see it as well as one below it.  Naming only a statement the
  fact's context sees would drop the firing when that statement is retracted while one
  the context cannot see still sorts the fact.

  Read off the taxonomy's supporter sets (`tax/prop-supporters`,
  `tax/commuting-supporters`) rather than through `general-supporters`: this runs once
  per mirrored firing, `firing_cost_test` holds it to no index read, and the matcher reads
  a mark by its exact functor, so the sub-predicate fan a match would add names
  nothing.

  The groups are read unscoped, a superset: each alternative names the mark sentexes,
  which the read walk believes or hides per reader."
  [kb sentence tuple context]
  (let [s (vec (rest sentence))
        f (nm/functor sentence)]
    (when (and (symbol? f) (not= s tuple) (= (count s) (count tuple)))
      (let [tx    (reasoning/taxonomy kb)
            tms   (reasoning/tms kb)
            recs  (:records kb)
            up    (when-not (sx/variable? context) (tax/context-up tx context))
            ;; `[sentence group [[handle ctx] …]]` per statement, in content order
            marks (->> (concat (when (= 2 (count s)) (tax/prop-supporters tx :symmetric f))
                               (mapcat #(tax/commuting-supporters tx f %)
                                       (tax/commuting-groups tx f)))
                       distinct
                       (keep (fn [h]
                               (when (jtms/in? tms h)
                                 (let [sxr (p/get-sentex recs h)
                                       sen (:sentence sxr)
                                       g   (when (sequential? sen) (mark-group sen))]
                                   (when (and g (or (nil? up) (contains? up (:context sxr))))
                                     [sen g [h (:context sxr)]])))))
                       (group-by (juxt first second))
                       (map (fn [[[sen g] rows]]
                              [sen g (->> (let [rs (mapv #(nth % 2) rows)
                                                u  (filterv #(= universal-context (second %)) rs)]
                                            (if (seq u) u rs))
                                          (sort-by (comp nm/print-key second))
                                          (tax/uncovered tx (fn [[_ c]] [nil (if (nil? c) #{} #{c})])))]))
                       (sort-by (comp nm/print-key first))
                       vec)
            n     (count marks)
            ok?   (fn [idx] (rearranges? (map #(second (nth marks %)) idx) s tuple))
            sets  (if (> n permuted-mark-cap)
                    (let [all (range n)] (when (ok? all) [all]))
                    ;; by size, so a set holding one already found is not minimal
                    (reduce (fn [found mask]
                              (let [idx (filter #(bit-test mask %) (range n))]
                                (if (or (some (fn [fs] (every? (set idx) fs)) found)
                                        (not (ok? idx)))
                                  found
                                  (conj found (vec idx)))))
                            []
                            (sort-by #(Long/bitCount %) (range 1 (bit-shift-left 1 n)))))
            alts  (for [idx sets
                        alt (reduce (fn [alts i]
                                      (for [a alts, [h _] (nth (nth marks i) 2)] (conj a h)))
                                    [[]]
                                    idx)]
                    alt)]
        (not-empty (into [] (distinct) alts))))))

(defonce ^:private crossing-reads
  ;; `{kb-key -> {:decls postings :derived {k value} :stamp s :marks {q #{group}}}}`, one
  ;; entry per KB, keyed by `crossing-key`
  (atom {}))

(defn- crossing-key
  "The key `kb`'s `crossing-reads` entry is held under: its `:unrecovered` atom, which the
  KB owns and which holds a few flags, so an entry keeps no store reachable.  Nil for a
  KB value without one, whose reads are not cached."
  [kb]
  (:unrecovered kb))

(def ^:private crossing-reads-limit
  "How many KBs' entries `crossing-reads` holds before it is cleared wholesale."
  64)

(caches/register-cache
 {:cache    :preservation-crossing
  :label    "Preservation crossing reads"
  :scope    :process
  :unit     "KBs"
  :limit    (caches/limit-thunk :preservation-crossing crossing-reads-limit)
  :counters nil
  :note     (str "Per KB, the argument positions the declarations preserving along genl "
                 "name and the commuting groups the stored marks state, which a genl edge "
                 "reads to decide which preserved predicates it moves. An entry is re-read "
                 "when a declaration functor's or a mark functor's posting moves. Past the "
                 "limit it is cleared wholesale.")
  :read     (fn [_] {:entries (count @crossing-reads)})
  :clear    (fn [kb] (let [k (crossing-key kb)
                           n (if (contains? @crossing-reads k) 1 0)]
                       (swap! crossing-reads dissoc k)
                       n))
  :trim     (fn [_ target] (caches/trim-map! crossing-reads target))})

(defn- store-crossing-read!
  "Merge `f`'s result into `kb`'s `crossing-reads` entry, clearing the cache wholesale when a
  new KB's entry would take it past its bound.  Stores nothing for a KB with no
  `crossing-key`."
  [kb f]
  (when-let [k (crossing-key kb)]
    (swap! crossing-reads
           (fn [m]
             (if (contains? m k)
               (update m k f)
               (caches/assoc-bounded m (caches/limit-of :preservation-crossing crossing-reads-limit)
                                     k (f nil)))))))

(defn- declaration-postings
  "The declaration functors' postings, in `declaration-functors` order: two
  predicate-extent reads.  A declaration stored or removed changes its functor's posting,
  and a handle is never reused, so equal postings hold the same declarations."
  [kb]
  (mapv #(reads/as-stored-with-functor (:index kb) %) declaration-functors))

(defn- declarations-cached
  "The value `compute` answers for `k`, cached in `kb`'s `crossing-reads` entry and keyed on
  `decls`, the `declaration-postings` read before `compute` runs.  A write between the
  read and `compute` leaves an answer newer than its key, which the next read finds
  unequal and reads again."
  [kb decls k compute]
  (let [e (get @crossing-reads (crossing-key kb))]
    (if (and e (= decls (:decls e)) (contains? (:derived e) k))
      (get-in e [:derived k])
      (let [v (compute)]
        (store-crossing-read! kb (fn [e]
                                   (let [e (if (= decls (:decls e))
                                             e
                                             (-> e (assoc :decls decls) (dissoc :derived)))]
                                     (assoc-in e [:derived k] v))))
        v))))

(defn- positions-along
  "`{:preds {P #{n …}} :positions #{n …}}` — the argument positions every stored
  declaration preserving along `rel` names, per predicate and as one set, read off the
  argument root at position 3 and one record fetch per declaration.  Global and not
  belief-filtered, for `declared`'s reason.  A negated declaration is in the same root and
  drops out on its shape.  Cached on the declaration postings (`declarations-cached`)."
  [kb rel]
  (declarations-cached
   kb (declaration-postings kb) [:along rel]
   #(let [idx  (:index kb)
          recs (:records kb)
          m    (reduce (fn [m h]
                         (let [[_ pred n] (:sentence (p/get-sentex recs h))]
                           (if (and (symbol? pred) (integer? n) (pos? n))
                             (update m pred (fnil conj #{}) n)
                             m)))
                       {}
                       (mapcat (fn [f] (reads/as-stored-with-args idx f [[3 rel]]))
                               declaration-functors))]
      {:preds m :positions (into #{} (mapcat val) m)})))

(defn- commuting-marks
  "`{q #{group …}}` — the commuting groups every stored mark states, in any context and
  whatever its belief (`permuting-marks`, `mark-group`).  Not belief-filtered, for
  `moved-predicates`' reason: a mark read here and not believed costs a re-join that finds
  nothing, and a mark believed and not read here is a crossing claim never asked about.

  Four predicate-extent reads per call, and the record fetches only when one of the four
  posting sets differs from the ones the cached answer was read off.  A mark stored or
  removed changes its functor's posting, and a handle is never reused, so equal postings
  hold the same marks."
  [kb]
  (let [idx   (:index kb)
        stamp (mapv #(reads/as-stored-with-functor idx %) permuting-marks)
        e     (get @crossing-reads (crossing-key kb))]
    (if (and e (contains? e :marks) (= stamp (:stamp e)))
      (:marks e)
      (let [recs  (:records kb)
            marks (reduce (fn [m h]
                            (let [sen (:sentence (p/get-sentex recs h))]
                              (if-let [g (and (sequential? sen) (mark-group sen))]
                                (update m (second sen) (fnil conj #{}) g)
                                m)))
                          {}
                          (sequence cat stamp))]
        (store-crossing-read! kb #(assoc % :stamp stamp :marks marks))
        marks))))

(defn- reach-positions
  "The argument positions a claim on a predicate carrying the commuting groups `groups` can
  hold a term at and still be read at one of the preserved positions `ns`: `ns` itself and
  every position sharing a commuting component with one of them (`sx/commuting-components`,
  which merges overlapping groups as the matcher does).  `:any` when such a component
  reaches past every position named, which only a `:rest` group does — its extent is the
  claim's own arity, so no fixed set of positions covers it."
  [ns groups]
  (if (empty? groups)
    ns
    (let [top   (inc (long (reduce max 1 (concat ns (mapcat (fn [[k v]] (if (= :args k) v [v]))
                                                            groups)))))
          comps (filter #(some (set ns) %) (sx/commuting-components groups top))]
      (if (some #(some #{top} %) comps)
        :any
        (into (set ns) cat comps)))))

(defn- crossings
  "The set of predicates preserved along `genl` that the edge `a → b` moves, or nil where
  no narrowing is read: a closure past `crossing-closure-cap`, or an index store with no
  slot roster.  `crossing-claim?` states what it computes.

  The closures are unscoped: the moved set is a trigger over every reader, and each
  re-join reads its rule from the rule's own context."
  [kb a b]
  (let [tax   (reasoning/taxonomy kb)
        cap   (long crossing-closure-cap)
        below (tax/specs-global-within tax a cap)
        above (when below (tax/genls-global-within tax b (- cap (count below))))]
    (when above
      (let [idx    (:index kb)
            {along :preds poss0 :positions} (positions-along kb 'genl)
            ;; {P {q positions-or-:any}}, for each marked sub-predicate q of a declared P
            marked (reduce-kv (fn [m q gs]
                                (reduce (fn [m pr]
                                          (if-let [ns (get along pr)]
                                            (assoc-in m [pr q] (reach-positions ns gs))
                                            m))
                                        m
                                        (tax/genls-global tax q)))
                              {}
                              (commuting-marks kb))
            any    (into #{} (keep (fn [[pr qs]] (when (some #{:any} (vals qs)) pr))) marked)
            poss   (into poss0 (comp (mapcat vals) (remove keyword?) cat) (vals marked))
            ;; {q #{n …}}: the positions each predicate holds a closure term at
            hits   (reduce (fn [m t]
                             (reduce (fn [m n]
                                       (let [qs (reads/as-stored-predicates-at-arg idx n t)]
                                         (if (nil? qs)
                                           (reduced (reduced nil))
                                           (reduce #(update %1 %2 (fnil conj #{}) n) m qs))))
                                     m
                                     poss))
                           {}
                           (into below above))]
        (when hits
          (reduce-kv
           (fn [acc q ns]
             (reduce (fn [acc pr]
                       (let [ok (or (get-in marked [pr q]) (get along pr))]
                         (if (and ok (or (= :any ok) (some ok ns)))
                           (conj acc pr)
                           acc)))
                     acc
                     (tax/genls-global tax q)))
           any
           hits))))))

(defn- crossing-claim?
  "For the `genl` edge in `body` (`(genl a b)`, or the body under a `not`), the set of
  predicates `P` preserved along `genl` for which a reach that a claim on `P` licenses
  could pass through the edge.  A set, so it is also the predicate `P -> truthy` that
  `moved-predicates` applies.  Nil where no narrowing is read, which leaves every
  declaration on `genl` moved: the edge's terms are not both symbols, the closure holds
  more than `crossing-closure-cap` terms, or the index store keeps no slot roster.

  A walk through `a → b` runs from a term below `a` to a term above `b`, so a claim whose
  preserved argument lies in neither `specs-global` of `a` nor `genls-global` of `b` has no
  reach across the edge, before or after it changed.  Both declaration forms are covered:
  `transitiveInArgInverse` walks up from the conclusion's term to the claim's,
  `transitiveInArg` walks up from the claim's, and either walk crosses the edge from the first set into the
  second.  The segments on either side are the edges still standing, so the closures
  read now contain every end a walk through the edge had or will have; a second edge on
  the same walk moving in the same block is asked about when it arrives.  The claim may be
  on `P` or on a sub-predicate of it, in either polarity, since the slot roster lists
  both.

  **A permuting mark widens the positions.**  The matcher reads a claim of a sub-predicate
  `q` in every argument order `q`'s own `symmetric`, `commutative`, `commutativeInArgs`
  and `commutativeInArgAndRest` marks permit, so a term stored at any position sharing a
  commuting component with a preserved one is read there (`reach-positions`).  A component
  a `:rest` group opens has the claim's arity as its extent, and a `P` with such a
  component at a preserved position is moved by every edge.  The marks are read as stored
  (`commuting-marks`).

  A predicate whose only declaration on `genl` names no positive integer position is in
  no answer here, and `positions` declines to read it too: it preserves nothing, so no
  edge moves what it licenses.

  The closures are global, as `moved-predicates`' own reads are: the re-join places a
  firing in whichever context its routes are seen from, so an edge seen from any context
  can move a claim, and a scoped closure would leave out a route a more specific context
  holds.

  The reads run from the terms: one slot-roster read per closure term per preserved
  position names the predicates holding that term there, and each is walked up to the
  declared predicates above it.  So the cost is the closure's size times the distinct
  preserved positions, and not times the declarations, of which a KB may hold thousands;
  the marks add four predicate-extent reads.  Memoized per edge inside a `with-memo`."
  [kb body]
  (let [[_ a b] body]
    (when (and (symbol? a) (symbol? b))
      (memoized [:crossings a b] #(crossings kb a b)))))

(defn- decl-index
  "`{:by-p {P #{R …}} :by-r {R #{P …}}}` over the `[P R]` pairs `decls`, so a channel reads
  the pairs naming one predicate or one relation with a map lookup rather than a pass over
  every declaration."
  [decls]
  (reduce (fn [m [pr r]]
            (-> m
                (update-in [:by-p pr] (fnil conj #{}) r)
                (update-in [:by-r r] (fnil conj #{}) pr)))
          {:by-p {} :by-r {}}
          decls))

(defn- declaration-index
  "`decl-index` over the `[P R]` pairs `declared` reads, with the pairs under `:pairs`,
  cached on the declaration postings (`declarations-cached`); nil when no declaration is
  stored.  A KB that declares none pays `declarations-exist?`'s two predicate-extent counts,
  and one that does pays the two postings besides."
  [kb]
  (when (declarations-exist? kb)
    (let [di (declarations-cached kb (declaration-postings kb) :decl-index
                                  #(let [ps (declared kb)] (assoc (decl-index ps) :pairs ps)))]
      (when (seq (:pairs di)) di))))

(defn preserved-pairs
  "Every stored declaration's `[P R]` pair (`declared`), off `declaration-index`, or nil
  when none is stored."
  [kb]
  (:pairs (declaration-index kb)))

(defn- among
  "The members of `xs` that `in` holds, walking whichever of the two is smaller.  `in` is a
  set or a map, so membership is `contains?` on either."
  [xs in]
  (if (<= (count xs) (count in))
    (filter #(contains? in %) xs)
    (filter #(contains? xs %) (if (map? in) (keys in) in))))

(defn- moved-in
  "`moved-predicates` over the declarations indexed as `decl-index` indexes them, as
  `[claimed other]`: the predicates moved through the claim channel, and those moved
  through every other channel.  The `genl` closures are global for `moved-predicates`'
  reason: over-selecting costs a join that derives what is already there, and a scoped
  closure would leave out a predicate a context that sees more edges moves.

  `wanted` names the predicates whose narrowing the caller acts on.  A `genl` edge is
  narrowed (`crossing-claim?`) only when a predicate it would otherwise move is wanted;
  otherwise it moves every predicate preserved along `genl`, unnarrowed.  The narrowing
  reads a slot roster per closure term per preserved position, and a caller that does
  nothing with a predicate (no rule on it, or one already in its answer) gains nothing
  from it."
  [kb sen {:keys [by-p by-r]} wanted]
  (let [body (or (sx/underlying-body sen) sen)
        f    (nm/functor body)
        arg1 (nth body 1 nil)]
    (when (symbol? f)
      (cond
        (contains? declarations f) [nil (when (symbol? arg1) #{arg1})]
        (= 'transitive f)          [nil (into #{} (get by-r arg1))]
        ;; the mark binds its spec subtree, whose converses `converse-claim` reads
        (= 'asymmetric f)          [nil (when (symbol? arg1)
                                          (into #{} (among (tax/specs-global
                                                            (reasoning/taxonomy kb) arg1)
                                                           by-p)))]
        ;; the permutation is applied per fanned literal on its own mark, so a mark on
        ;; a sub-predicate moves every preserved super it feeds
        (permuting-mark? f)        [nil (when (symbol? arg1)
                                          (into #{} (among (tax/genls-global
                                                            (reasoning/taxonomy kb) arg1)
                                                           by-p)))]
        :else (let [preds (tax/genls-global (reasoning/taxonomy kb) f)]
                ;; a claim on P or on a sub-predicate of it
                [(into #{} (among preds by-p))
                 ;; a fact on a relation some P is preserved along
                 (into #{}
                       (mapcat (fn [r]
                                 (let [ps (get by-r r)]
                                   (if-some [crosses (when (and (= 'genl f) (= 'genl r)
                                                                (some wanted ps))
                                                       (crossing-claim? kb body))]
                                     (among ps crosses)
                                     ps))))
                       (among preds by-r))])))))

(defn channels-read-arguments?
  "Does `moved-channels`' answer for a sentence with functor `f` read its arguments?  True
  for a declaration, `transitive`, `asymmetric`, a permuting mark and `genl`; every other
  functor's answer is a function of `f` alone."
  [f]
  (or (contains? declarations f) (contains? '#{transitive asymmetric genl} f)
      (permuting-mark? f)))

(defn moved-channels
  "`moved-predicates`' answer for `sen` over the `[P R]` pairs `decls`, split by channel:
  `[claimed other]`, the predicates a claim on one of them or on a sub-predicate moves,
  and the predicates every other channel moves.  A caller opens a `with-memo`, which
  indexes `decls` once."
  [kb sen decls wanted]
  (moved-in kb sen (memoized [:decl-index decls] #(decl-index decls)) wanted))

(defn- separation-moved
  "The predicates of `ps` whose `separated-denials` `sen` arriving or leaving can move,
  read unscoped and exempting no pair, a superset over every reader, since the re-joins
  and re-checks it triggers read each firing from its own context, as `[member any]`:
  `member` those whose goal at `sen`'s own argument alone moves, and `any` those whose
  every goal may move.

  * for a membership `(S x)`, in either polarity, those separated from `S`, in `member`;
  * for a `genl` edge `sen` installs (`tax/installed-edges`) whose upper end is
    `tax/separable?`, those separated from the upper end, whose memberships the edge
    places under it, and those at or below the lower end;
  * for any other sentence that moves a separation, those at or below a type
    `tax/sentence-separation-ends` names.

  Taxonomy reads alone, and none for a sentence of no such shape."
  [kb sen ps]
  (let [body (or (sx/underlying-body sen) sen)
        f    (when (seq? body) (nm/functor body))]
    (when (and (symbol? f) (seq ps))
      (let [tx       (reasoning/taxonomy kb)
            args     (nm/args body)
            unary?   (= 1 (count args))
            sep-from (fn [t] (when-let [sep? (separation-test tx t nil)] (filter sep? ps)))
            edges    (filter (fn [[_ b]] (tax/separable? tx b)) (tax/installed-edges body))
            ends     (tax/sentence-separation-ends tx body)]
        [(if unary? (set (sep-from f)) #{})
         (cond-> (into #{} (mapcat (fn [[_ b]] (sep-from b))) edges)
           (seq ends) (into (filter #(some ends (tax/genls-global tx %))) ps))]))))

(defn separation-moved-predicates
  "The preserved predicates whose goals' `separated-denials` `sen` arriving or leaving can
  move (`separation-moved`), for the exception re-check; empty when the KB declares no
  preservation."
  [kb sen]
  (if-let [di (declaration-index kb)]
    (into #{} cat (separation-moved kb sen (keys (:by-p di))))
    #{}))

(defn moved-goal-test
  "A test `(fn [goal] → boolean)`, false only for a goal on a preserved predicate whose
  verdict, and whether it is stated at its own tuple, `sen` arriving or leaving cannot
  move — or nil where no test is read and every goal may have moved: a declaration,
  `transitive`, `asymmetric`, a permuting mark, a `genl` edge into a predicate some
  declaration names or sits below, an argument that is not a symbol.

  Two channels are read, at `'?ctx` and over the global `genls`, the union of what every
  context reads, since the firings re-decided live in any context.  A **claim**
  moves only a goal whose product holds its tuple (`claims`), so every argument of the
  goal is one of the claim's or a term one of them licenses.  A fact on a **relation**
  moves only a goal whose reach crosses it, and a walk from the goal's term reaches the
  fact's first term whether the fact is there or not, so some argument of the goal is an
  end of the fact or a term one licenses along it (docs/inherit.md).  A membership, a
  separation or a `genl` edge moves the goals `separation-moved` names: a goal on a
  predicate it separates from the membership's type at the membership's own argument,
  and every goal on a predicate whose separations it moves."
  [kb sen]
  (let [body   (or (sx/underlying-body sen) sen)
        f      (when (sequential? body) (nm/functor body))
        args   (when (symbol? f) (nm/args body))]
    (when-let [{:keys [by-p by-r]} (when (and (seq args) (every? symbol? args)
                                              (not (contains? declarations f))
                                              (not (contains? '#{transitive asymmetric} f))
                                              (not (permuting-mark? f)))
                                     (declaration-index kb))]
      (with-memo
        (let [tx      (reasoning/taxonomy kb)
              preds   (tax/genls-global tx f)
              claimed (among preds by-p)
              rels    (set (among preds by-r))
              reached (fn [prs keep-pos?]
                        (into (set args)
                              (for [pr prs, pos (positions kb pr '?ctx) :when (keep-pos? pos)
                                    t args, w (licensed-terms kb pos t '?ctx)]
                                w)))]
          (when-not (and (= 'genl f)
                         (some #(seq (among (tax/genls-global tx %) by-p)) args))
            (let [every-t (when (seq claimed) (reached claimed any?))
                  some-t  (when (seq rels)
                            (reached (into #{} (mapcat by-r) rels) #(contains? rels (:rel %))))
                  [member any] (separation-moved kb sen (keys by-p))]
              (when (or every-t some-t (seq member) (seq any))
                (fn [goal]
                  (let [gs (nm/args goal)
                        g  (nm/functor goal)]
                    (boolean (or (not-every? symbol? gs)
                                 (and every-t (every? every-t gs))
                                 (and some-t (some some-t gs))
                                 (contains? any g)
                                 (and (contains? member g) (= args gs))))))))))))))

(defn claim-reach-extent
  "The stored facts of the preserved predicate `pred`, in either polarity, whose tuple the
  claim `sen` (on `pred` or a sub-predicate of it, in either polarity) can reach by
  preservation from some context, as a superset: the handles holding at argument 1 one of
  `sen`'s arguments or a term a believed declaration of `pred` licenses from one
  (`licensed-terms`, read at `'?ctx`).  Every argument order the matcher reads a claim in
  holds its terms among these, and so does the converse an asymmetric predicate is denied
  by.  nil when an argument is not a symbol or the terms outnumber `pred`'s stored
  extent, for a caller to read the extent instead."
  [kb sen pred]
  (with-memo
    (let [args  (nm/args (or (sx/underlying-body sen) sen))
          idx   (:index kb)
          limit (reads/stored-count-with-functor idx pred)
          poss  (positions kb pred '?ctx)
          terms (when (every? symbol? args)
                  (reduce (fn [acc t]
                            (let [acc (into acc (mapcat #(licensed-terms kb % t '?ctx)) poss)]
                              (if (> (count acc) limit) (reduced nil) acc)))
                          (set args)
                          args))]
      (when terms
        (into #{} (mapcat #(reads/as-stored-with-args idx pred {1 %})) terms)))))

(defn separated-types
  "The types the unscoped taxonomy, exempting no pair, separates from `pred`: each type at
  or below one `tax/separating-partners` names.  The functors of the stored memberships a
  claim of `pred` can deny (`separated-claims`), read as a superset over every reader,
  since the callers re-open candidates each asker reads again."
  [kb pred]
  (memoized [::separated-types pred]
            #(let [tax (reasoning/taxonomy kb)]
               (into #{} (mapcat (fn [y] (conj (tax/specs-global tax y) y)))
                     (tax/separating-partners tax pred nil (constantly false))))))

(defn claim-reach-separated
  "The stored memberships `(S x)` the claim `sen`, on the preserved `pred` or a
  sub-predicate of it, can deny by reaching `(pred x)` from some context
  (`separated-claims`), as a superset: the unary facts at an argument of `sen` or at a
  term a believed declaration of `pred` licenses from one (`licensed-terms`, read at
  `'?ctx`) whose type is one of `separated-types`, or the stored extents of those types
  when the terms outnumber them.  The unary facts are read in every context, a candidate
  set each asker reads again from its own."
  [kb sen pred]
  (with-memo
    (let [types (separated-types kb pred)]
      (if (empty? types)
        #{}
        (let [args  (nm/args (or (sx/underlying-body sen) sen))
              idx   (:index kb)
              recs  (:records kb)
              limit (reduce + (map #(reads/stored-count-with-functor idx %) types))
              poss  (positions kb pred '?ctx)
              terms (when (every? symbol? args)
                      (reduce (fn [acc t]
                                (let [acc (into acc (mapcat #(licensed-terms kb % t '?ctx)) poss)]
                                  (if (> (count acc) limit) (reduced nil) acc)))
                              (set args)
                              args))]
          (if terms
            (into #{}
                  (filter #(let [s (some-> (p/get-sentex recs %) :sentence)]
                             (and (seq? s) (= 2 (count s)) (contains? types (first s)))))
                  (mapcat #(reads/as-stored-unary-with-arg-global idx %) terms))
            (into #{} (mapcat #(reads/as-stored-with-functor idx %)) types)))))))

(defn moved-predicates
  "The preserved predicates whose licensed claims `sen` may have moved.

  Five channels, and none of them is the predicate-keyed trigger a forward rule is
  ordinarily fired from:

  * a **claim** on `P` (or on a sub-predicate of it) licenses a tuple nobody stated,
    and undercuts one somebody did;
  * a fact on the **relation** `R` — a `genl` / `genlCx` edge included — moves
    every reach walked along it, with neither of its terms appearing anywhere near `P`.
    A `genl` edge moves only the `P` with a claim whose reach can cross it
    (`crossing-claim?`), reading the claim at every position a permuting mark lets it
    hold the preserved argument at; an edge whose closure is past
    `crossing-closure-cap` moves every `P` preserved along `genl`.  Every declaration in
    a KB may preserve along `genl`, so without the narrowing each edge re-joins all of
    their rules;
  * the **declaration** itself, which names `P` at argument 1;
  * `(transitive R)`, the licence `usable-relation?` reads at use, which names no `P`
    at all; `(asymmetric P)`, which is what gives a converse the standing to deny
    an inherited claim; and a permuting mark — `(symmetric P)`, `(commutative P)`,
    `(commutativeInArgs P …)`, `(commutativeInArgAndRest P n)` — which makes every
    permutation it licenses of a stored claim a claim, so arriving late it licenses
    tuples nobody re-joined for;
  * a **membership** of a type a separation holds apart from `P`, which `claims` reads
    as a denial, and a separation or `genl` edge that moves which types those are
    (`separation-moved`).

  The reads are **global** and not belief-filtered, exactly as `declared`'s are and for
  the same reason: over-selecting costs a join that derives what is already there,
  under-selecting is a conclusion that depends on when a sentence arrived.  The pairs
  are `declared`'s, indexed by predicate and by relation (`declaration-index`, cached on
  the declaration postings), so each channel reads the pairs it names and the answer
  costs no pass over every declaration; a KB that declares nothing pays two
  predicate-extent counts.

  **The three-argument form takes the `[P R]` pairs**, for a caller holding them already
  and asking this per member of a settle's region.  That caller opens a `with-memo`, so
  the pairs are indexed, and an edge in the region narrowed, once per settle however
  often they are asked about."
  ([kb sen] (moved-predicates kb sen nil any?))
  ([kb sen decls] (moved-predicates kb sen decls any?))
  ([kb sen decls wanted]
   (if-let [di (when (and (sequential? sen) (seq sen))
                 (if decls
                   (memoized [:decl-index decls] #(decl-index decls))
                   (declaration-index kb)))]
     (let [[claimed other] (moved-in kb sen di wanted)]
       (-> (set claimed)
           (into other)
           (into cat (separation-moved kb sen (keys (:by-p di))))))
     #{})))

(defn rejoin-rules
  "The forward rules to re-join in full because `sen` moved what a preserved predicate
  licenses — every rule carrying an antecedent on one — or nil.

  Keyed on the antecedent index rather than on the arriving sentence's predicate,
  because the two are unrelated: `(genl chihuahua dog)` licenses a `typeLargerThan`
  antecedent and no walk from `genl` reaches `typeLargerThan`.  That is the same shape the
  qualitative re-join has, for the same reason, and `special/recheck-preserving-along`
  reads the same declarations to close the exception side of the identical channel."
  [kb sen]
  (let [idx      (:index kb)
        rules-on (memoize #(reads/as-stored-rules-by-antecedent-global idx %))]
    (when-let [ps (seq (moved-predicates kb sen nil #(seq (rules-on %))))]
      (let [rs (into #{} (mapcat rules-on) ps)]
        (when (seq rs) rs)))))

(defn licensing-functors
  "The functors whose facts move what a preserved predicate in `preds` (a set, or a map
  keyed by predicate) licenses, or nil — `moved-predicates`' channels named as functors
  rather than asked of one sentence, for a caller that enumerates stored facts to hand
  to `rejoin-rules`.

  The declaration functors, `transitive` and `asymmetric`, and each relation some `P` in
  `preds` is preserved along, with its sub-predicates, since a fact on one is a fact on
  the relation.  A claim on `P` is not named: its functor is `P` or under it, and the
  caller reads those already.  The permuting marks are not named either, since the
  engine lifts each into `CxUniverse`, where every reader sees it.  Where a separation
  holds a `P` apart from some type, the types `separated-types` names, `disjoint`, the
  `tax/separation-functors` and the disjoint metatypes are named too
  (`separation-moved`).  Two
  predicate-extent counts for a KB that declares nothing (`declaration-index`).

  The sub-predicate closure is **global**, for `moved-predicates`' reason: these name
  candidates for a re-join, over-selecting costs a join that derives what is already
  there, and a scoped closure would leave out a relation a context that sees more edges
  walks."
  [kb preds]
  (when-let [{:keys [by-p]} (declaration-index kb)]
    (let [tx   (reasoning/taxonomy kb)
          rels (into #{} (comp (filter #(contains? preds (key %))) (mapcat val)) by-p)
          seps (into #{} (comp (map key) (filter #(contains? preds %))
                               (mapcat #(separated-types kb %)))
                     by-p)]
      (when (seq rels)
        (cond-> (into (into #{'transitive 'asymmetric} (keys declarations))
                      (mapcat #(tax/specs-global tx %))
                      rels)
          (seq seps) (-> (into seps)
                         (into tax/separation-functors)
                         (conj 'disjoint)
                         (into (tax/disjoint-metatypes tx))))))))

(caches/register-derived
 {:id :R5 :label "Inherit question memo" :kind :pass :keyed-by :value :reads [:index :T1]
  :holds-content? false
  :retired-by {} :computed :pass :imaged? false :var #'*memo*
  :note "positions, reach and whole reach for one question or one discovery pass; whole reach 1,048,576 terms, 65,536 a walk"})

(caches/register-derived
 {:id :R6 :label "Preservation crossing reads" :cache :preservation-crossing :kind :cache
  :holds-content? false
  :keyed-by :global :reads [:index :records]
  :retired-by {:stored :I :removed :I :respelled :I :caches-cleared :W :recover :W}
  :computed :read :imaged? false :var #'crossing-reads
  :value (fn [kb] (get @crossing-reads (crossing-key kb)))
  :note "keyed by the KB's `:unrecovered` atom: re-read when the declaration postings or the mark postings are not equal"})

;; ---- a second route at a reader -----------------------------------------
;; A rule firing whose witness path a reader hides stands there when each goal it matched
;; through a reach is reached by a believed claim over edges the reader does not hide: a
;; backward search from the goal, stopping at the first claim (docs/nmtms.md, "Where the
;; layer stops").

(defn- claim-in?
  "Does a claim stated of the term `t` reach the goal term `x` along the declaration
  `pos` from `context`: for `genl`, membership of the upper of the two in the lower's
  scoped ancestor set (`tax/genls`, held in the closure cache across reads), which reads
  the edges `context` sees and believes, and `witness-terms` for a fact relation."
  [kb {:keys [rel along?] :as pos} x t context]
  (if (= 'genl rel)
    (let [[sub super] (if along? [t x] [x t])]
      (scoped #(contains? (tax/genls (reasoning/taxonomy kb) sub context) super)))
    (contains? (witness-terms kb pos x context) t)))

(defn- stated-reached?
  "Is the ground `goal` stated at `context` of its own functor or of a sub-predicate the
  edges `context` believes and sees reach it from: the predicates the store holds a fact
  of with the goal's first argument (`reads/as-stored-predicates-at-arg`), each walked up
  to the goal's functor, when they number fewer than the functor's sub-predicates counted
  unscoped, and the matcher's sub-predicate fan otherwise.  The count is unscoped because
  it only weighs the two seeds, which answer the same; the walk up reads the scoped
  ancestor set, as `claim-in?` does."
  [kb goal context]
  (let [pred  (nm/functor goal)
        args  (nm/args goal)
        tx    (reasoning/taxonomy kb)
        preds (some-> (reads/as-stored-predicates-at-arg (:index kb) 1 (first args)) set)]
    (if (and preds (nil? (tax/specs-global-within tx pred (count preds))))
      (boolean (some (fn [l] (and (scoped #(contains? (tax/genls tx l context) pred))
                                  (seq (res/matches-visible kb (apply list l args) context))))
                     (sort preds)))
      (boolean (seq (res/matches-visible kb goal context))))))

(defn- goal-reached?
  "Is the ground positive `goal` reached at `context` by a believed claim: a stated match
  of its functor or a sub-predicate (`stated-reached?`), or, at a preserved position, a
  claim whose term reaches the goal's over edges `context` sees and believes
  (`claim-in?`).  Stops at the first claim found.  Seeded off the stored claims with the
  goal's pinned arguments when they number no more than the goal term's reach
  (`extent-size`, `product-size`), and off the reach's terms otherwise.  The reach is
  weighed unscoped, an upper bound on the scoped one, since the weighing never changes the
  answer."
  [kb goal context]
  (binding [*memo* (atom {})]
    (let [pred (nm/functor goal)
          args (vec (nm/args goal))
          poss (positions kb pred context)
          by-n (by-position poss (count args))]
      (if (empty? by-n)
        (stated-reached? kb goal context)
        (let [tx   (reasoning/taxonomy kb)
              ;; a reach weighed by the unscoped walk, which stops at `limit` and reads no
              ;; edge's visibility: an upper bound on the scoped reach, and weighing never
              ;; changes the answer
              size (fn [i limit]
                     (let [x   (nth args i)
                           lim (long (min limit Long/MAX_VALUE))]
                       (reduce (fn [n {:keys [rel along?] :as pos}]
                                 (let [m (if (= 'genl rel)
                                           (if-let [c (if along?
                                                        (tax/specs-global-within tx x lim)
                                                        (tax/genls-global-within tx x lim))]
                                             (count c)
                                             ##Inf)
                                           (count (witness-terms kb pos x context)))
                                       n (+ n m)]
                                   (if (> n limit) (reduced ##Inf) n)))
                               0 (by-n (inc i)))))
              sl   (into [] (map-indexed
                             (fn [i s]
                               (if (:reach s)
                                 (let [x (nth args i)]
                                   (assoc s
                                          :in?  (fn [t] (boolean (some #(claim-in? kb % x t context)
                                                                       (by-n (inc i)))))
                                          :size #(size i %)))
                                 s)))
                         (slots kb poss args context))
              fwd  (vec (range (count args)))
              ext  (extent-size kb pred sl fwd false context product-ceiling)]
          (boolean
           (seq (if (<= ext (product-size sl ext))
                  (believed-matches kb (probe-sentence pred sl fwd (constantly nil))
                                    sl fwd context nil false nil)
                  (mapcat (fn [tuple]
                            (believed-matches kb (probe-sentence pred sl fwd tuple)
                                              sl fwd context tuple false nil))
                          (product-tuples sl))))))))))

(defn- firing-goals
  "`[goals stated]` for the rule firing `j`: the antecedent literals of its rule that no
  antecedent of `j` states, instantiated from its conclusion and the stated antecedents,
  and the antecedent handles that state a literal.  nil when `j`'s informant is not a rule
  or a goal is left open."
  [kb j]
  (let [recs (:records kb)
        rsx  (when (integer? (:informant j)) (p/get-sentex recs (:informant j)))
        conc (some-> (p/get-sentex recs (:consequence j)) :sentence)]
    (when-let [lits (and conc (seq (:antecedent rsx)))]
      (let [antes (into [] (keep (fn [h] (when-let [x (p/get-sentex recs h)] [h (:sentence x)])))
                        (:antecedents j))
            [b open stated]
            (reduce (fn [[b open stated] lit]
                      (if-let [[h b'] (some (fn [[h s]] (when-let [b' (res/unify lit s b)] [h b']))
                                            antes)]
                        [b' open (conj stated h)]
                        [b (conj open lit) stated]))
                    [(res/unify (:consequent rsx) conc) [] #{}]
                    lits)
            ;; a variable only an open literal names takes its term from the claim the
            ;; literal was reached from: a stated antecedent of the literal's functor and
            ;; arity, read position by position past the positions the reach moved
            loose (fn [b lit]
                    (or (some (fn [[_ s]]
                                (when (and (seq? s) (= (nm/functor s) (nm/functor lit))
                                           (= (count s) (count lit)))
                                  (reduce (fn [b [l t]]
                                            (if (and (sx/variable? l) (not (contains? b l))) (assoc b l t) b))
                                          b (map vector (rest lit) (rest s)))))
                              antes)
                        b))
            goals (when b
                    (mapv (fn [lit] (let [g (res/substitute lit b)]
                                      (if (ground-goal? g) g (res/substitute lit (loose b lit)))))
                          open))]
        (when (and (seq goals) (every? ground-goal? goals))
          [goals stated])))))

;; the read walk asks these walks whether a reader reaches a preserved claim's path, or a
;; rule firing's goals, over a second route (`exc/install-route-reach!`)
(exc/install-route-reach!
 (fn [kb rel a b reader]
   (binding [*memo* (atom {})]
     (contains? (witness-terms kb {:rel rel :along? false} a reader) b)))
 firing-goals
 goal-reached?)
