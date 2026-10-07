# Taxonomy: types, genl, and disjointness

- **Covers:** how the `genl` type hierarchy is cached and queried, how `disjoint` /
  `disjoint_metatype` are enforced, how `covering` / `separating` / `partition` state a
  named roster's claims,
  and how `arg` / `genlArg` constrain arguments as a
  rejection check — of a ground sentence, and of a rule's shared variables.
- **Not here:** `genlCx`, the sibling closure over contexts rather than types →
  [contexts.md](contexts.md); `arg` / `genlArg` read as an entailment that mints a
  stored, justified fact → [argtypes.md](argtypes.md).
- **Assumes:** sentex, context, belief, justification → [glossary.md](glossary.md).

`vaelii.impl.taxonomy`. Transitivity is the lifeblood of common sense, so it is **not**
done with rules — the direct adjacency of the type graph is stored and the transitive
closure is answered on demand (read-memoized per edge generation), never materialized.

**Where the rule went, for a reader who looks for it.** The spelling for recording
transitivity without running it is the **inert rule** (`set/inertRule`,
[inference.md](inference.md)): stored, believed, indexed under its predicates and
browsable like any other rule, and chaining in neither direction. [why an inert rule
rather than a forward one](defenses.md#an-inert-rule-records-transitivity-not-a-forward-rule)

`CxCore.txt` states no rule for `genl`'s transitivity, inert or otherwise: `genl`
carries its account in the `comment` on the predicate, where the closure is described,
and `(transitive genl)` classifies it without handing it to the generic prover. The two
inert rules CxCore does state record the `commutative` / `commutativeInArgAndRest` bridge.

## genl: the type hierarchy

`(genl Sub Super)` — every `Sub` tuple is a `Super` tuple. Types are unary predicates,
rooted at `thing`. Predicate specializations of other arities also use `genl`;
membership in that graph alone does not imply `unary_predicate`. The starter assigns
unary membership to the subtypes of `thing`. A `genl` between two predicates spelled
camelCase is on the forced-monotonic roster, held `:monotonic` and undeniable; a `genl`
between types stays defeasible ([nmtms.md](nmtms.md#the-forced-monotonic-roster)). We
cache the reflexive-transitive closure both ways:

- `genls tax t context` — supertypes of `t`, incl. `t` (up-closure).
- `specs tax t context` — subtypes of `t`, incl. `t` (down-closure).
- `genl? tax sub super context`.

Each has a `-global` twin — `genls-global tax t`, `specs-global`, `genl?-global`, and, over
on the `genlCx` side, `context-up-global` and `genlCx?-global` (the twin of `sees?`) — which
walks **every** active edge rather than the edges a context sees. The two are spelled apart rather than distinguished by
arity because on a KB where no edge is context-restricted they return the *same object*:
a caller that meant to scope and did not is right until the KB it is wrong on. Who reads
globally, and why: [below](#the-global-readers-and-who-may-use-one).

### Three uses of genl

1. **Arg constraints.** `(arg pred n type)` sentexes constrain arguments;
   `assert` checks arg *n* with `isa?` (does the arg have a type whose `genls`
   reaches the constraint). Open-world about a **symbol**: an untyped one can't
   violate. A **value** carries its type in its syntax and is checked against it.
   A **function application** is checked against what its function is declared to
   yield.
2. **Specificity.** Matching a unary type predicate fans out over `specs`, so an
   antecedent `(animal ?x)` is satisfied by a stored `(dog Muffet)` — no need to
   materialize `(animal Muffet)`. `isa?` answers membership on demand.
3. **(genlCx is the sibling relation over contexts — see contexts.md.)**

### Relations and arity policy

`relation` is the common parent of `predicate` and `function`: both can be applied to
arguments, while only predicates hold or fail and only functions denote values. Arity
policy and the exact `arity` table are therefore relation-wide.

`fixed_arity` and `variable_arity` classify two disjoint policies, with predicate and
function specializations for each. Unsuffixed `unary`, `binary` and `ternary` classify
exact relations; `unary_predicate` / `unary_function` and their binary and ternary peers
specialize those relation-wide classes. `relationTypeByArity` owns the shared mapping;
`predicateTypeByArity` and `functionTypeByArity` are its `genl` specializations, and one
generator stamps, per mapping fact, the rule classifying a relation from its asserted
`arity`, with no parallel rule families. CxCore ships **three** mapping facts, over
`unary`, `binary` and `ternary`. The predicate and function types reach them through
their `genl` edges, so a `(predicateTypeByArity unary_predicate 1)` beside them would
classify a unary function as a predicate. The two specializations stay declared for a KB
mapping an arity the relation-wide table has no class for. `arityMin` states the lower bound of a variable-arity relation. Prefer
variable arity for a repeatable, homogeneously typed argument role. A relation with a
bounded optional tail declares variable arity too, with its `arityMin`, and its
well-formedness check bounds the tail: `functionCorrespondingPredicate` is
`variable_arity_predicate` with `arityMin 2`, and `wff/correspondence-problems` refuses
it with other than two or three arguments, the third an optional argument position.

`at_least_binary_relation` and `at_least_ternary_relation` are generic derived
classifications over `arityMin`; callers can conjoin them with `predicate` or `function`
instead of maintaining duplicate predicate/function classes. `admitsArgnum` names the
separate question of whether one positive argument position exists. No WFF/query reader
currently consumes it, and no parallel finite position roster is inferred.

Exact `(arity R N)` entails `fixed_arity`; it is not also an `arityMin` floor. The nine
shipped variable predicates state their lower bound with `arityMin` instead of carrying
an exact binary classification.

The mapping's rule runs one way: `(arity R 2)` concludes `(binary R)`, and no rule
concludes an arity. `arity`, the nine exact-arity classes, `variable_arity` with its two
specializations and `arityMin` are on the forced-monotonic roster
([nmtms.md](nmtms.md#the-forced-monotonic-roster)): each is held `:monotonic` whatever
strength it was written at, and a firing concluding one from a non-roster antecedent is
held void. The minted `(arity R 2)` → `(binary R)` rule reads a roster antecedent, so its
firings stand. Every reader of an arity reads the exact-class membership beside the
`(arity P n)` table: the arity nogoods ([Arity](#arity)), the argument-position check
(`checks/declared-arity`), `kb/relation-arity` behind `describe` and the quality pass, and
the prover answering `admitsArgnum`. The conclusion is **relation-wide** and has to be:
`arity` covers functions, so a rule concluding `(binary_predicate R)` from `(arity R 2)`
would make every shipped binary function a predicate and clash with `(disjoint predicate
function)`. `binary` carries no kind, which is what an arity actually says. An arity no
class maps to concludes nothing, which is why `(arity InstantFn 6)` leaves `InstantFn`
classified only by its own `fixed_arity_function`.

The `genl` edges on the arity classes run downward only: a `binary_predicate` is `binary`
and is a `predicate`. None of them says that a relation which is `binary` **and** a
`predicate` is a `binary_predicate`, and CxCore does not state that half either. A
`(defnSufficient binary_predicate (and (arity ?x 2) (predicate ?x)))` ([defns.md](defns.md))
would say it, and the six of them measure 748 justifications and 600 ms of a 3.2 s
starter load for 36 memberships: `(predicate ?x)` matches every class membership of
every predicate by subsumption, once per `genl` route between the two, so one conclusion
collects a justification per route. The nine exact classes cost that once each; the
intersection would cost it again for a membership nothing reads.

The classification is read for its arity, and the relation-wide class answers that
without the intersection: `(arity P 2)` derives `(binary P)` through the generator above,
and `tax/exact-arity-classes` — the roster the arity nogoods and the quality readings
share — holds all nine spellings, so `(binary P)`, `(binary_predicate P)` and
`(binary_function F)` each declare an arity a reader enforces. A KB that wants the kind membership as well writes the
`defnSufficient` itself, in its own context, and pays for it there.

## The closures are derived state

A cached closure is an optimization, and an optimization that disagrees with the
data is a bug. The source of truth for an edge is **the set of believed sentexes
asserting it**, so each relation carries that set explicitly:

```clojure
{:support {[dog animal] {41 CxA, 88 CxB}} ; every sentex asserting the edge, and its context
 :edges   #{[dog animal]}           ; the ACTIVE edges — those with a believed supporter
 :fwd {dog #{animal}}               ; direct up-adjacency (a genl b)
 :rev {animal #{dog}}               ; direct down-adjacency
 :nodes #{dog animal}               ; every node in an active edge
 :depth {dog 1 animal 0}            ; topological potential for O(1) reachability rejects
 :scc {}                            ; node -> component, for the nodes in a cycle
 :scc-members {}                    ; component -> its nodes, the inverse of :scc
 :gen 7                             ; bumped on every edge change; retires the read memo
 :moves {7 #{dog}}}                 ; per generation, the lower ends of the edges it moved
```

`:moves` holds each node once, at the last generation an edge from it was activated,
dropped or given other supporting contexts, so a reader holding an older generation
reads which closures moved since (`tax/moves-since`) without comparing them: the
membership candidates read it ([What a declaration reaches back
over](#what-a-declaration-reaches-back-over)).

The closure itself — `genls` (up) / `specs` (down) — is **not** stored. It is
answered on demand — an up-closure built from its parents' closures, a down-closure by a
reflexive-transitive `reach` over `:rev` — and held per `:gen` in the closure LRU.

Three properties follow, each of which a cache is easy to get wrong:

- **Belief.** A defeated `(genl dog animal)` leaves the closure. Matching is
  belief-sensitive everywhere else in the engine — a defeated sentex stays stored
  but does not match — so a taxonomy that exempts itself lets `isa?` answer through
  an edge nothing believes. `refresh-beliefs` reconciles at the end of every
  `settle` that moved belief, which is the only point a supporter's label flips without a sentex being
  added or removed, and it costs what *moved* rather than what the taxonomy holds — the
  next subsection is how. Inside a `with-deferred-settle` batch there is not yet
  anything to reconcile against: `add-edge` runs on the assert path, where the JTMS has
  not labelled the new sentex, so an edge is active from the moment it is stored and the
  closing settle is what narrows the active set to the believed one. A mid-batch `isa?` /
  `genl?` / `disjoint?` reads that belief-blind set — a superset, so it answers through an
  edge it should not rather than missing one it should — and the batch's own answer is the
  one after it closes (`deferred_settle_test` holds the witness).
- **Reference counting.** The same edge asserted in two contexts is two sentexes.
  Retracting one leaves the edge standing while the other still asserts it.
- **Derived edges count.** A rule concluding `(genl a b)` reaches the taxonomy via
  `integrate-transitive` on the derivation path, not just the assert path. Without
  it the running KB and `recover` (which reads the store) disagree about what the KB
  entails, so a restart silently changes the answer. The same question is owed by every
  other declaration a rule can conclude, and the next subsection is the answer for each.

`recover` calls `clear-relations!` — which empties every cache the taxonomy holds, the
two closures, the equality partition, the rewrite rules and the flat caches — before rebuilding.
A rebuild that merged into the existing cache could only ever *add*, so an edge whose
sentex was gone would survive the recovery meant to re-derive it. `rebuild-taxonomy`
reads **stored** rather than believed sentexes, so `:support` / `:cache-support` record
every asserting sentex; `recover` then runs `refresh-beliefs` over the replay itself,
giving the same answer either side of a restart. Belief-filtering the replay would drop
a disbelieved supporter, and clearing its defeat could never revive the entry.

That reconcile is `recover`'s own rather than its closing settle's, and the case that
needs it is the **unsupported** edge: a record carrying no premise mark and no
justification is OUT from the moment the JTMS rebuild makes its node, so no defeat, no
block and no supersession ever names it — nothing a settle reacts to, and no region a
settle-scoped reconcile could reach it through — while the replay has already made it
answer `genls`. The *defeated* edge is narrowed either way, since its opposition is an
event. `recovery_test/recover-does-not-answer-through-an-unsupported-edge` is the
witness for the first case and
`taxonomy_belief_test/recover-does-not-revive-a-defeated-edge` for the second.

### What a rule may conclude, and what it reaches

A rule consequent may name any of the functors the engine interprets, and the rebuild
replays every one of them off the store. So each owes the same answer `genl` owes:
whether a *derived* one reaches its cache while the KB is running. The assert path walks
the whole special-predicate table (`special/integrate-sentex`); the derivation path
walks the `:derived?` subset (`special/integrate-transitive`) plus what
`chain/place-fact-conclusion` calls by name.

| a rule concluding | the cache behind it | reached by |
|---|---|---|
| `genl` `genlCx` | the two closures | `:derived?` |
| `disjoint` `disjoint_metatype` `sibling_disjoint` `orthogonal` | disjointness, the metatype and sibling marks, and the exemption | `:derived?` |
| `arity` `inverse` | the arity and inverse caches | `:derived?` |
| `transitive` `symmetric` `asymmetric` `reflexive` `functional` `forced_decontextualized_predicate` `abducible_predicate` `closed_extent_predicate` `reifiable_function` `unreifiable_function` | the predicate-metadata marks | `:derived?` |
| `rewriteOf` `sameAs` `equals` | the equality partition, and migration | by name — the arm's return value is the twins and the violations, which `:derived?` would discard ([equality.md](equality.md)) |
| `arg` `genlArg` `interArg` | the roster of predicates some declaration of that kind names (`:declares-arg-isa` / `:declares-arg-genl` / `:declares-inter-arg-isa`), and the declarations themselves read back through the index per query | `:derived?` — the roster is what lets the descension ask *whose* declarations bind a tuple without an index probe per super-predicate |
| `transitiveInArg` `transitiveInArgInverse` `functionCorrespondingPredicate` | none — read back through the index per query | nothing to reach |
| `different` `unknown` `thereExists`, the five aggregates | none — never stored | nothing to reach: `wff` refuses the conclusion on the derivation path exactly as it refuses the assertion |

A row naming a functor on the forced-monotonic roster (`genlCx`, a relation mark,
`disjoint`, `sibling_disjoint`, an arity binding, an equality, a `genl` between predicates) is
reached only by a firing whose rule reads roster literals alone: any other firing
concluding one is stored, held void and reported as `:forced-conclusion`, and the rule
stays stored ([nmtms.md](nmtms.md#the-forced-monotonic-roster)). The conclusion's arm
installs it and the chainer then reconciles its caches to belief
(`special/reconcile-belief-change`), so a conclusion held void takes effect neither live
nor after `recover`.

**One conclusion reaches its cache only once a restart replays it**, and it is
stated here rather than left to be found:

- **`decontextualized_predicate`.** Its arm marks the predicate *and* runs an O(extent)
  retroactive lift whose copies are chaining seeds, which the `:derived?` walk would
  throw away — so a derived declaration would lift half of what an asserted one lifts.
  A rule concluding it therefore leaves the mark unset until a restart replays it.

A disjoint metatype's own members reach theirs by another route. `(animal_species dog)`
is recorded by the structural arm rather than by a table entry — the functor is the
metatype, which is data and not vocabulary — and the derivation path runs the structural
arms too, all but the rule arm (`special/derived-sentex-added`). A rule concluding a
membership therefore separates the member as soon as the conclusion is stored, as a rule
concluding the metatype *mark* over asserted members does.

### The belief reconcile is scoped to the moved region

`settle` hands `refresh-beliefs` the region it relabelled (`jtms/touched`, a **superset**
of every handle whose belief flipped). Belief moves by handle, and a `genl` sentex's
sentence names exactly one edge, so only an edge some moved handle supports can have
changed which of its supporters are believed. `:handle-edge` is that map — the transpose
of `:support`, maintained 1:1 by the same writers — and `refresh-relation` reads its scope
forward off the moved set through it, never backward off the relation.

The direction is the whole of it. Read backward, both halves of the reconcile are
O(vocabulary): asking "did anything here move" walks every supporter, and answering
"which edges are active now" evaluates belief for every edge. Neither is visible to a
test, because both are merely slow — ~180 ms per flip in a 64k-edge relation, and ~8 ms
even to decide the relation was untouched. Read forward, one flip costs ~10µs at any size.
`perf`'s `taxonomy-belief-flip` is the gate on that: defeat and revive one edge in a
taxonomy of n, and the per-op cost must not track n. Across an 8× taxonomy the backward
reading grows 6.9×, the forward one 0.6×.

Two things widen the scope past the moved edges, and both are required:

- **`nil` means unconditional** — reconcile every edge with a supporter, which is what a
  caller holding no region gets. `recover` is that caller, and the one that passes it: a
  settle's reconcile is scoped to a region *and* gated on belief having moved, and a
  rebuild replaying an unsupported declaration moves nothing (the subsection above).
  Every `settle` path names a region instead, and `settle-finish` *widens* its own by
  hand rather than dropping it, because a supersession flip is a belief change with no
  relabel to record it. The widening is the data whose supersession entry changed since
  the last settle (`special/take-supersession-moves!`), so it grows with the change, not
  with the merges standing.
- **`:dirty` carries what a belief-blind writer left behind.** `add-edge` / `del-edge` run
  on the assert and retract paths, where no `believed?` is in hand, so they recompute an
  edge's `:edge-ctxs` from every recorded supporter rather than the believed ones. On the
  single-supporter edge that is nearly every edge — and all of a bulk load — that is
  already exact. On a **shared** edge it is a superset, and losing the last *believed*
  supporter of an edge two sentexes still assert is a deactivation only a `believed?` can
  make. So a writer touching a shared edge names it in `:dirty` and the next reconcile
  takes it whether or not belief moved there. A superset is the safe interim reading: a
  scoped read sees an edge it should not, rather than missing one it should.

  This holds the reconcile to **its own contract** rather than to the caller's generosity.
  `moved` is documented as the handles whose belief flipped; `jtms/touched` passes a
  superset, and today that superset is wide enough that no engine path leaves a stale
  edge without `:dirty` — a retraction's region names the edge's other supporters, over
  forty intervening settles as well as none. The oracle in `taxonomy_test` is what fails
  without it, because it passes the exact flip set. Depending on the width instead would
  make correctness rest on something nothing states and nothing tests, and the failure is
  a silent one.

**The flat caches below work the same way, off the same reasoning.** `:cache-handle-keys`
is the transpose of `:cache-support` and `:cache-dirty` is the twin of `:dirty`, with one
difference that is about the caches rather than about the scoping: the index is a
**multimap**, `{handle #{[kind key]}}`. A `genl` sentence names one edge and the writers
here name one entry per sentence too, but nothing in the structure says so and removal is
per-(handle, key) — a 1:1 index would have the first `support-drop` take a handle out from
under an entry the same sentex still supports, which shows up as a stale cache rather than as
a crash. A set per handle costs the single-key case one small set and holds the index to
`:cache-support`'s own shape.

The reason to scope them is the reason `:cache-support` is one map: it holds every
disjoint pair, predicate property, `inverse` and declared `arity` in the KB at once, so a
reconcile drawn over it is drawn over the vocabulary. Read backward it measured ~95 ms per
flip over 32k declarations and ~5 ms merely to decide nothing had moved; forward, ~5 µs
and ~1 µs, and neither moves with the count. `perf`'s `flat-cache-belief-flip` is the gate:
across an 8× KB the backward reading grows 7.0×, the forward one 1.2×.

Two caches do **not** scope, and gate instead: the equality partition and the rewrite
rules. Both hold the KB's asserted term-identity claims rather than its vocabulary, and
the gate reads whichever of the moved region and the supporter set is smaller — so a
settle that moves neither pays the size of its own region rather than of the cache. A
settle that *does* move one of them rescans it whole. For the rewrite rules that is a
handful of schematic equations. For the equality partition it is every `sameAs` / `equals`
/ `rewriteOf` the KB asserts, and the scan is what recomputes `:out`, the relation-wide
set of disbelieved supporters, from the current support keys — relation-global state
rather than per-edge, which is what makes it a different question from the two above.

### The closure is not materialized — it is answered on demand

A materialized closure is Θ(V²) for a deep hierarchy — a 10k-node `genl` chain holds
~50M pairs — so building it incrementally makes a bulk load quadratic *however*
cleverly each insert extends it: the representation itself is the cost. Loading E
edges of a chain that way was Θ(E²) (measured: a 4k chain took ~13s and grew ~4× per
doubling). So the closure is not stored at all. Only the O(V+E) direct adjacency is,
and `genls` / `specs` walk it on demand.

- **Insertion** records the edge in `:fwd` / `:rev`, adds the endpoints to `:nodes`,
  and repairs the `:depth` potential (`edge x→y ⇒ depth[x] > depth[y]`) by lifting the
  new child above its parent and pushing that lift to the child's descendants as far as
  it forces them — O(1) for a hierarchy loaded parent-before-child, since a fresh node
  has no descendants, and O(descendants) when it is not (which is what a batch defers;
  see below). The lift moves whole **components**, since the potential ranks the
  condensation: a member raised alone would sit above its own mates, each of which then
  forces the next one round the cycle. A component's members are a lookup in
  `:scc-members`, so a lift reads the components it moves and none of the others. No
  closure is touched. A redundant re-assert of an already-active edge is a no-op.
- **Deletion** drops the edge from the adjacency and prunes any node left with no edge
  (so `types` / `contexts` match a from-scratch build). Depths are left as loose upper
  bounds: a deletion only relaxes the ordering, so the `edge ⇒ depth` invariant
  survives untouched, and a loose depth only costs an occasional un-pruned walk step,
  never a wrong answer.
- **Reads** compute the reflexive-transitive closure over `:fwd` / `:rev`, held in the
  closure LRU keyed with the relation's `:gen`. Every edge change bumps `:gen`, which
  retires every held closure of that relation without touching it — a read keys on the
  new gen, misses, and recomputes. A repeat read on a shallow hierarchy is O(1); a deep
  one is never materialized. `genl?` / `sees?` skip the closure entirely: they answer
  reachability with a `:depth`-pruned early-exit walk (`depth[src] ≤ depth[tgt]` rejects
  a pair in O(1)), which is what keeps the per-assert `wff` cycle check flat on a deep
  load.
- A **cycle** is refused for both `genl` and `genlCx` at assert, and the potential is
  what still makes a recovered one work. `wff` (assert path) and `special/wff-violation`
  (derivation path) refuse a `genl` or `genlCx` edge that would close one: a type cycle
  claims two types are coextensive — a claim about *terms*, which is the equality
  partition's job, and which would make a `disjoint` pair disjoint from itself — and a
  context cycle, though it claims only that the two contexts see each other, is refused
  too, so the context hierarchy is a partial order like the type hierarchy. A recovered
  or foreign store replays its stored edges past those checks (`recovery/recover`), so
  the taxonomy still holds a cycle such a store presents.
- Holding it means the potential ranks the **condensation** rather than the graph:
  `edge x→y ⇒ depth[x] > depth[y]`, except inside a strongly connected component, where
  the members are level and `:scc` maps each to the component's representative
  (`term-min`, so it is content-keyed like every other tie-break here). `reachable?`
  then answers a same-component pair in O(1) without walking at all, and prunes everything
  else exactly as before — a real path between components must descend, so equal depth in
  different components still rejects. `:scc` holds an entry only for a node *in* a cycle,
  so an acyclic relation carries an empty map and reads identically.
- Maintaining it, and the two directions are not symmetric. An edge that **closes** a
  cycle merges two components, which is a question about the whole graph rather than
  about the edge, so `activate` condenses the whole relation on the spot — one O(V+E)
  pass, Tarjan for the components, then Kahn for the heights over the condensation —
  and `:scc` holds the merged component the moment the edge is active. It has to:
  the assert that closes the cycle forward-chains before it settles, and a firing the
  closing edge seeds reads `:scc` to place its conclusion on the component's one
  representative. **A relation that is already loose is no exception**, though it is the
  one place the cost shows: with no potential to prune it, the guard walks `b`'s whole
  up-closure instead of a prefix of it, so it is gated on `a` already being a node — an
  edge introducing a fresh sub can be reached by nothing, which is the parent-first
  arrival a loose batch is still mostly made of. The condensation that follows lifts
  `:loose?` with it, so the batch pays for the cycle once rather than once per edge
  after it. The loose mark still short-circuits the *acyclic* repair, which has
  no sound base to build on.
- A deletion can **split** a component, and a stale component is the one thing here that
  would answer *true* for a pair no longer connected, so it is never left standing. But a
  split is a question about the component alone: an edge can only break the strong
  connectivity of a component whose **induced subgraph it belongs to**, so an edge with
  an endpoint outside — every deletion in an acyclic relation, and most of them in a
  cyclic one — changes no component at all and `deactivate` leaves the potential alone.
  When both endpoints do share one, that component's own induced subgraph is re-run
  through Tarjan; the new components of the whole graph refine the old ones, so a split
  produces nothing outside the component that split. The pieces are then ranked against
  each other and against what they point at, and a piece that lands higher than the
  component did pushes that lift up through `:rev`. So the relation does **not** go
  loose, the reads keep their pruning, and the cost is the component's rather than the
  relation's.

### Reads are scoped by the asking context

A read asked from context K uses exactly the edges K can see: an edge counts iff some
**believed** supporter asserts it from K's `genlCx` ancestor set, the same filter
`matches-visible` applies to facts. Every supporter records its asserting context
(`:support` is `{[a b] {handle ctx}}`), the active edges carry theirs in `:edge-ctxs`
(reconciled with belief by `refresh-relation`, whose third arm catches a supporter's
belief moving while the edge's liveness does not), and `genls` / `specs` / `genl?` /
`disjoint?` / `has-prop?` / `inverse-of` each take a context argument. A nil context,
a `?var`, or a reader that sees every asserting context is the unscoped path,
byte-identical to the one-shorter arity; a supporter with no recorded context (a
probe) constrains everywhere.

**Believed** here is belief as that reader reads it, not the network's label. The
supporter predicate the KB installs (`res/supporter-believed?`) applies both withdrawal
kinds: a believed `except` visible from the reader, and a loser of a nogood the reader
decides, together with everything resting only on such a handle. A reader that
disbelieves an edge therefore stops reaching over it, and `genl?` from that context
agrees with `believed?` of the edge's handle (docs/nmtms.md, "A defeat is scoped to its
vantage"). `relation-filter-active?` is the gate: with neither roster holding anything
that supports an edge of the relation, the read takes the context-only walk and asks the
predicate never.

The filter keys on `vis = up(K) ∩ ctxs`, where `ctxs` is the relation's context
census (`:ctx-counts`): every edge's context set is a subset of the census, so two
readers with the same `vis` induce the identical filtered edge set — `vis` is the
memo key, interned per `[genlCx-gen ctxs-gen]` (`:vis-index`), and the scoped
walk is memoized under it in the same closure cache as the global one (the census on the
OpenCyc import [kbs.md](kbs.md) is the route to: ~450 asserting contexts, ~560 distinct
vissets across ~13k readers).

**Every closure, global or scoped, is held in one weighted LRU** (`:closure-lru`), weighed
by the terms it holds and bounded at `closure-memo-limit` through the cache profile, so the
memory guard shrinks it under a filling heap and the least recently used closures go
first — the upper types every walk passes stay. A closure is keyed with its relation's
`:gen`, so an edge change retires it by never asking for it again. It is bounded by
weight because a large import can hold millions of types with supertype chains of hundreds
to thousands, and a memo holding every closure a whole-corpus clash pass walks grows with
the corpus rather than with the closures a walk reuses.

**An up-closure is built from its parents' closures** (`reach-by-parents`): `C ∪ ⋃
closure(p)` for the parents `p` outside the type's component `C`, bottom-up from the
nearest ancestors the LRU holds, each built one held for the next. A walk climbs the whole
ancestry again for every type, and on a large taxonomy that climb — hash lookups into an
adjacency map with a key per type — can be half of a settle. The union starts from the
largest parent's set, so a type with one parent shares its parent's structure and adds
itself. It runs over the condensation: `:scc` never names a false component (a removal
repairs it eagerly), and a cycle it has not yet recorded — a deferred replay's — makes the
build hand back to the walk, as does a parent's closure evicted mid-build. A down-closure
is always walked: built from its children, one read of a broad type would hold the
down-closure of every type under it.

**A membership test does not build a closure.** `genl?` answers through the depth-pruned
walk, which holds nothing; `kb/memberships` and a clash's membership lookup
(`checks/membership-handles`) ask it, and only a caller that walks or intersects the set
reads one. The lookup names a surviving exact membership `(t x)` without testing
anything, since the entailing ones are named only when none survives; otherwise it tests
every type an instance holds and asks the same pair once per instance of a shared type,
so it asks `genl?-per-pass`, which keeps each answer in a pass cache when one is bound. A
reader's re-read of its definitional nogoods (`clashes/reread-at`) binds one for its span,
which holds a detached taxonomy and one reading still.

**Neither does a question asking something small of every type above.**
`genls-global-union` answers the union of what a transducer makes of each term of
`genls-global`, by the same recurrence as the up-closure, since what it makes of a union
is the union of what it makes of the parts; `genls-global-among` is the union with a
filter, the closure cut to a set of marked terms. Each answer holds a few terms or none.
Nothing enters the LRU: the caller's memo keeps the answers for one pass over a still
taxonomy. The arity candidate index (`arity/recompute-arity`) asks the cut to the bound
predicates only for a functor whose own length differs from one above it: where every type
binds its own length, the cut to the bound predicates is the closure again. It asks the
union (`arity/relength`) for the exact lengths above each type below a binding or an edge
that leaves.

**A property every subtype inherits is spread down, not read up.** The arity index keeps
the exact lengths bound at or above each type below a binding (`::lengths`), and a length
arriving is added by `specs-global-while`: a walk down from a type through every active
edge that enters a subtype only while the caller's predicate holds, here "misses one of
the arriving lengths". A subtype holding them all stops the walk, since every type below
it holds them too, so a binding arriving above bound types costs the edges to its
children; `lein perf`'s `bound-type-load` holds it. A recover spreads every binding once.

**Most scoped reads are the global read.** A node's global closure records the contexts
its edges rest on (`closure-needs`: the one supporting context of each edge the closure
walks, or "several" when an edge has more than one); a `vis` holding all of them sees
every edge the global walk takes, so the scoped closure *is* the global set, returned as
that object with no walk and no second copy in the cache.

Depth pruning survives unchanged — the potential holds over
the global edge set and the visible set is a subset — so `reachable-filtered?` keeps
both prunings, with the direct-edge test behind the same filter.

It keeps the **condensation** with them, and this is the half a filtered walk is easy to
get wrong. The potential ranks components, not nodes, so a node on a path to the target
is either strictly above it *or level with it inside the target's own component*; a walk
pruned on a strict descent alone rejects the second, and then the scoped `genl?` denies
a path the scoped `genls` — walking the very same visible edges — returns. What the
filtered walk may **not** borrow is `reachable?`'s other half, answering true off a
shared component: mutual reachability there is a fact about the *global* edge set, and
the whole question a scoped read asks is which of those edges the reader can see. So a
component is a reason to keep walking and never an answer. (A `genl` cycle between types is
refused at assert time and reachable anyway: defeat an edge, assert its reverse — the
check reads the *active* adjacency, which no longer holds the defeated one — then revive
the first. A `genlCx` edge is on the forced-monotonic roster and is never defeated, so
a context cycle comes only from a recovered or foreign store, which replays a stored
cycle past the check, as it does a type cycle.)

The **`genlCx` closure itself is the stated exception and stays global**:
visibility scoped by visibility would be circular, every `genlCx` edge is forced
universal, and the interning above rests on it. So do the identity, storage, trigger,
and stratification reads. The scoped-or-not split per check, and the deciding of clashes
only a descendant can see whole, are docs/contexts.md's story.

### The global readers, and who may use one

Every one of those reads goes through a reader whose **name** says it is global —
`genls-global`, `specs-global`, `genl?-global`, `context-up-global`, `genlCx?-global` —
rather than through a shorter arity of the scoped one. The reason is that the two agree far more often than
they differ: `visible-ctxs` hands back the global closure itself, the identical object,
for any reader that sees every context an edge was asserted from, which is most readers of
most KBs. A caller that dropped the context by accident would therefore pass every test
anybody wrote, and answer wrongly only once somebody restricted an edge.

`lein lint`'s **E17** rosters the callers as `(file, definition)` pairs, so a new global
read is a decision somebody wrote down rather than a shorter line somebody reached for.
The roster records *that* a caller has a reason; the reason lives in that definition's own
docstring. What is on it:

| Caller class | Why it must not be scoped |
|---|---|
| `vaelii.core`'s own 2-arity `genls` / `specs` / `genl?` | the public API offers both readings, and this arity **is** the global one |
| assert-time refusals (`wff/genl-problems`, `wff/genlCx-problems`, `checks`) | a refusal is a claim about the KB: a cycle refused when asked from one context and allowed from another is a coin toss, not a rule |
| the forward join and the trigger keys (`rules/trigger-keys`, `chain`, `inherit/moved-predicates`, `vantage`) | a firing is placed in a context the join decides, so the candidate fan cannot be scoped by one — the narrowing happens at placement |
| the exception re-check triggers (`special`) | a trigger over-approximates in the direction the answer is: a declaration this edge cannot see still qualifies a rule in some context that can, and a missed trigger is a wrong belief where a spare one is a query |
| settle's candidate discovery, and the membership candidates a reader filters (`membership/term-nogoods`) | an over-approximated candidate merely checks and yields nothing; the reader that follows reads its own ancestor set |
| `resolution`'s exception index, `except-hidden-fn` and `withdrawal` | the visibility filter cannot be scoped by the filter it is itself derived from |
| `quality/taxonomy-coverage` | a report on the whole taxonomy has no vantage to read from |
| `quality/clash-partners` | a rule pair is decided from a common descendant of the two rules' contexts, a vantage belonging to neither, so the candidate fan cannot be scoped by either |

A visibility `except` (docs/contexts.md) can hide a *supporter* from a reader, and then
the context-only filter is not enough: the scoped walk asks the KB, per supporter, whether
that handle is believed and unhidden from the concrete reader (`supporter-visible?`,
installed by the KB), and the memo key carries the reader and a **visibility
generation** that moves whenever an except arrives, leaves, or flips belief — and
whenever a settle's region names a supporter of either relation, since a supporter
moving belief can change what a reader sees through an edge that stays active. That
path is gated **per relation** (`relation-filter-active?`): it runs only while some
roster target is a supporter of the relation being read, or of `genlCx`, whose holes move
every reader's ancestor set. A supporter no except targets is visible iff it is believed, which
the active edge set already records, so an except on an ordinary fact leaves every
taxonomy read on the context-only path. `context-down` is the read with no single
reader — each candidate descendant brings its own ancestor set — so under an except that
reaches `genlCx` it filters the raw candidates by each one's own forward walk and
memoizes the answer per context, stamped on the same generations.

### The equality partition reads the same way

`representative` / `same-class?` / `equiv-class` / `deprecated?` take a context too, and
`tax/scoped-class` answers the first three. It is **not** a filter of the global
partition: dropping an edge can
*split* a class, so `A~B~C` with only `A~B` visible is the class `{A B}`, and its
representative is elected among those two alone rather than inherited from the class
`C` was in. The election rule is the global one over the visible edges' preference
claims, so a `rewriteOf` a context cannot see neither retires a term there nor promotes
one — which is also why `deprecated?` reads the per-supporter claims rather than the
aggregated `:edge-prefs`, since one edge may carry a `rewriteOf` and a `sameAs` at once
and only the first deprecates. Recomputed per call rather than memoized — a class is a
handful of terms, and the
caller already pays a record fetch per supporter to decide visibility (the equality
relation records supporters as handles; only the record store knows where each was
asserted, which is `res/visible-supporter-fn`). `tax/merged?` is the O(1) gate, so a
term nothing has merged never reaches any of it; `tax/merged-term-pred` is the same gate
closed over one snapshot, for a caller asking it of many terms in a row rather than once.

Its reference is therefore `equality-partition` — the same from-scratch build the
incremental union is checked against — handed only the visible edges and their
preference claims, and `taxonomy_scoped_test` compares members *and* elected
representative against it per reader after every edit of a random sequence.

### What a batch does to the depth potential

The insert above is O(1) only when the node it lifts has no descendants yet. Lift a
node that does and the push-down costs its whole descendant set, so a bulk load
arriving **child-first** is quadratic in the hierarchy — a 4k chain took ~13s and grew
~4× per doubling, against ~0.4s for the same edges deferred.

`vaelii.core/with-deferred-settle` therefore binds `taxonomy/*defer-depths?*`, and a
deferred insert repairs **only the new edge's own source** (`local-lift`): set
`depth[a] = depth[b] + 1`, then check the edges *into* `a` — an in-degree scan, never a
descendant walk. Raising a source can only break edges above it, so if none is broken
the global invariant still holds and nothing was given up.

When one **is** broken the relation goes `:loose?`: the potential is no longer sound,
`reachable?` drops its pruning, and `restore-depths` rebuilds every depth in one
reverse-topological O(V+E) pass at the next `settle`. That is the fallback, not the
normal path, because going loose is expensive in its own right — an unpruned
`reachable?` walks the source's whole ancestor set where the potential answered in
O(1) (measured at roughly 1,300× on an 8k-deep chain), and `wff` runs one per taxonomy
edge asserted. Deferring by simply marking the relation loose would only move the
quadratic: child-first would get cheap and parent-first — the order hierarchies are
actually written in — would get expensive. The local lift is what keeps *both* orders
flat, since parent-first arrival never breaks an edge above a fresh node.

Three consequences follow:

- **A settle repairs on both sides of its belief reconcile.** The batch above is not the
  only thing that surrenders the potential: `refresh-beliefs` changes the active edge set
  with no sentex added or removed, so an edge revived into a cycle closes a new component
  and the reconcile goes loose. Repairing only before it would leave that state standing
  until the *next* settle,
  which for `:scc` is not merely a lost pruning: `placement-rep` reads the component map
  to give a mutually-visible group one name, so a firing in between lands wherever its
  antecedents happened to point (docs/contexts.md). `restore-depths` is idempotent and
  free when nothing is loose, so the second call costs a map lookup per relation on every
  belief move that touches no cycle — which is nearly all of them.
- **A batch that aborts still repairs.** The closing `settle` never runs, so
  `with-deferred-settle` repairs the potential on the way out before rethrowing.
  Otherwise a cancelled load — the catalog aborts one by throwing from its progress
  callback, and leaves the KB queryable — would leave every later `genl?` / `sees?`
  walking unpruned for the life of the KB. Belief is still left unsettled; that is the
  documented state an aborted batch leaves behind.
- **`activate` reads `:loose?`, not just the dynamic var.** An insert arriving onto an
  unrepaired potential neither prunes its cycle check with it nor pushes a lift through
  it: both would be building on a stale base, and `raise-depth`'s termination argument
  rests on a cycle check made *with* that base. It still **makes** the cycle check —
  unpruned, and gated on the sub already being a node — because `:scc` is what
  `placement-rep` reads and a component found only at the batch's settle is a firing
  placed on whichever member it happened to see.

`recover` replays every stored edge, so it is a bulk load and is deferred like one,
repairing once before anything reads the relation back (~2.8× on a 16k-edge chain).

Depth *numbers* differ between an incremental build and a from-scratch repair — the
first only ever grows a depth, the second computes each node's exact height above the
sinks. Only the invariant is contractual, and `taxonomy_depth_test` checks reads
against it rather than against particular numbers, in both arrival orders and over
shuffled ones.

`closures` (the from-scratch materialized build) is the **reference implementation**,
kept for that and not read on any query path. `taxonomy_test` checks the on-demand
`genls` / `specs` against it,
node by node, after *every single edit* across 25 pseudo-random DAG edit sequences
(fixed seed, so a failure reproduces), biased toward deletion since that is where
depths go loose; a separate exhaustive test gates `genl?`'s depth-pruned verdict
against the reference's membership for every ordered pair under the same edit stream.

The scoped reads get the same treatment against the reference *filtered first*
(`taxonomy_scoped_test`), and twice: over DAGs, and over edit streams whose edges point
either way, which is the form the potential ranks by component. The second oracle holds
three readers of one question to one answer — the closure, the reachability, and the
witness the reachability rests on — since a scoped `genl?` disagreeing with the scoped
`genls` is the failure a DAG-only stream cannot produce.

**Scope.** The belief discipline applies to the two transitive relations, to the
equality partition, and — through the shared `:cache-support` reference count, keyed by
`[kind key]` — to the flat caches too: `disjoint`, the disjoint metatypes and their
members, the `sibling_disjoint` marks and their exemptions, the `covering` /
`separating` / `partition` rosters, the predicate properties
(`transitive`/`symmetric`/`asymmetric`/`reflexive`/`functional`), `inverse`, the
declared `arity`, the `functionalInArg` positions and the commuting groups. Only `genlCx` is forced-decontextualized, so only it is guaranteed one
sentex per claim; `(disjoint dog cat)` asserted in two contexts is two sentexes folding
into one cache entry through that refcount. `refresh-beliefs` reconciles each cache
entry against belief after every
relabel (the same call that reconciles the closures), reusing the same
`cache-install`/`cache-uninstall` the assert path uses, so a defeated `(disjoint dog
cat)` stops constraining, a defeated `(functional P)` stops merging, a defeated
`(inverse P Q)` stops answering the swapped goal, and a defeated `(symmetric P)`
unmarks — each reviving when its defeater is retracted, exactly as a genl edge does.
(Retracting the *last* stored supporter still tears the entry down through the
`del-*`/`unmark-*` path; belief-tracking governs the case where a supporter is
defeated but still stored.)

That reconcile is **scoped** to the moved region exactly as the closures' is, and by the
same two fields: `:cache-handle-keys`, the `{handle #{[kind key]}}` transpose of
`:cache-support`, turns a settle's moved handles into the entries it has to look at, and
`:cache-dirty` carries the entries the belief-blind writers left owing one. "The belief
reconcile is scoped to the moved region" above is the whole of the reasoning; what is
particular to these caches is that a *single* map holds every disjoint pair, property,
`inverse` and declared arity in the KB, so a reconcile drawn over it is drawn over the
vocabulary — ~95 ms per flip over 32k declarations, and ~5 ms to decide none of them
moved, against ~5 µs and ~1 µs read forward.

The index is therefore a **contract** — it must be exactly the live `:cache-support`
map's transpose, or the scope quietly stops being one. `support-add` / `support-drop` are
the one place it moves, with a single exception: unmarking a metatype drops its members'
entries wholesale (`forget-metatype`, below), so it owes both fields the same removal by
hand. A handle left behind after its entry is gone puts a key nothing supports into the
scope of every settle that relabels *that* sentex, and a `:cache-dirty` mark left behind
puts one there on every settle at all — for the life of the KB, since nothing ever removes
them. The reconcile skips a key `:cache-support` no longer holds, so the cost of getting
this wrong is work that never stops rather than a wrong answer.

### What a batch of edges costs the passes that read it

The depth potential is not the only thing a batch of `genl` edges is quadratic in. Two
passes read the hierarchy *per arriving edge*, and each one's memoization is keyed on
the node a walk **began** at — so nested roots share nothing and n edges cost n²/2. The
edges arrive nested because that is what a hierarchy is, and what a load writes.

- **The `special` arms decide before reading the subtree.** `equate-under-edge` and
  `antisym-equate-under-edge` read it only when a mark of their family stands at or above
  the edge's upper end (`tax/props-over`), since the edge brings the subtree under those
  marks and no other; an edge under a broad type whose subtree holds most of the
  vocabulary reads none of it otherwise (`lein perf`'s `genl-edge-under-no-merge-mark`).
  `entail-under-edge` is gated on an argument constraint reached from the upper end. All
  take their extent through one `subtree-sentexes`, filtered by index cardinality first.
  `subsumption-seeds` reads the subtree's believed handles only when a rule reads a term
  at or above the upper end, as an antecedent or through a re-join family
  (`special/rule-reads-above?`, `lein perf`'s `genl-edge-under-no-rule-above`).

All three are **free where nothing is declared**, which is every bulk load: an empty
marked roster seeds an empty walk, and a KB with no argument constraint never reaches
the second arm.

### Strength of a subsumption path

A `genl` edge can itself be defeasible — asserted `{:strength :default}` rather than
`:monotonic` — so reachability has a strength, and a firing that climbs the closure spends
it. When a fact reaches an antecedent of a *different* functor (`(fatherOf Tom Bob)`
satisfying `(parentOf ?x ?y)`), the supporters of the edges the match climbed become
antecedents of the conclusion's justification, and `strength` caps the conclusion at their
weakest class. So *which* path the walk names decides how strongly the conclusion holds.

**The rank of a path is its floor — the `min` defeat class along it — and the walk names
the path whose floor is highest.** This is the same fold `strength` applies to a
justification's antecedents (`min` over the conjuncts), so it composes rather than
inventing a second lattice; and it adds **no third class** — the rank of an edge is just
the defeat class of the strongest believed supporter crossing it (`:monotonic` >
`:default`). A path with one default edge and a path with nine defaults are the same floor:
`:default`. Bottleneck, not a count.

So on a hierarchy with two routes from `ff` to `af` — a one-hop edge asserted `:default`
and a two-hop chain asserted `:monotonic` — a conclusion reached across it holds
`:monotonic`, on the strong route, not `:default` on the short one. `tax/reach-support`
takes an optional `supporter-class` (a live JTMS `defeat-class` read) and, given it, walks
the **widest bottleneck** instead of the shortest path: highest floor, tie-broken by depth
then by the same name order every closure read uses, so the choice is a function of the
hierarchy and never of a handle (`docs/nmtms.md`). With exactly two classes the widest
floor is found by trying each class as a threshold, highest first, and taking the first
shortest path made only of edges that clear it. Each edge on the chosen path names its
**strongest** supporter (most general among those at the top class, so placement is
unchanged wherever two supporters tie on strength). `kb/reach-strength` reports the floor
directly, derived from that same path so the number and the witness never disagree.

The **shortest-path** walk (no `supporter-class`) is still what the `genlCx` visibility
placement takes, and what an unstrengthened caller gets: fewest supports, most general
supporter per edge. Only the `genl` subsumption a firing rests on asks for the widest one,
because only there does a supporter's *class* — not just its existence and visibility —
change an answer the engine gives. Why the widest bottleneck and not the shortest route:
[defenses.md](defenses.md#the-subsumption-path-is-the-widest-bottleneck-not-the-shortest-route).

A third walk answers a third question. `tax/general-reach-supports` returns every route
that no other route **covers**, where a route covers another when each reader that sees
all of the other's supporter contexts also sees all of its own — each of its contexts is
seen from one of the other's. A preservation claim's justification names a path from it
([inherit.md](inherit.md)), and that path decides where the conclusion is placed — so a
short route asserted in a specific context would put the conclusion below a longer route
through general ones, and belief would then depend on which route arrived first. The route
through general contexts covers the short one and is the one returned. Two routes stated in
contexts neither of which sees the other are both returned, since each places the
conclusion in a reader the other does not reach, and a firing is placed once per route.
Each edge names the supporters no other supporter of it covers, which is the most general
one wherever the supporters' contexts are comparable. The walk keeps one partial route per
uncovered label at each node, so where every edge is stated in contexts one reader sees it
settles each node once. Its queue orders by `context-specificity` — the size of a context's
`genlCx` ancestor set, which agrees with `sees?` on every comparable pair — then by length,
then by the same name order, so of two routes with one label the one kept is a function of
the content. `tax/reach-supports` is the same walk with the defeat class beside the
contexts, for the placement of a subsumed firing that has to descend below its other
ingredients ([contexts.md](contexts.md#the-consumers-and-what-each-of-them-may-reach)),
and for the reading a claim opposes a stored one at
([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

## Disjointness

Three mechanisms declare that types share no instance; all are closed under `genl`
(subtypes of disjoint types are disjoint):

- `(disjoint TypeA TypeB)` — an explicit pair.
- `(disjoint_metatype Metatype)` — a metatype whose member types (`(Metatype T)`
  facts) are pairwise disjoint. Membership is **recorded, not materialized**: the
  metatype and its members are cached (`:metatype-members`, reference-counted on the
  `(M T)` sentex) and `disjoint?` consults them, so the clique is a property of the
  code rather than of the store. Asserting the metatype after its members, or a
  member after the metatype, both work; neither writes a `(disjoint …)` sentex. A
  membership is recorded while the mark is **stored**, whatever its label
  (`stored-disjoint-metatype?`): the `(M T)` sentex is a supporter, and belief follows
  it through the flat-cache reconcile, so a member stated while the mark is defeated
  separates the moment the mark revives, in either order of arrival.

  Recording rather than asserting the clique is deliberate — [why recording beats
  asserting the clique](defenses.md#recording-a-disjoint-clique-beats-asserting-it).
  The cost is that membership is in-memory, so
  `recover` re-reads the `(M T)` sentexes after marking the metatypes. The browser's
  disjointness list computes the induced disjoint pairs rather than querying for them,
  for the same reason — there are no `(disjoint …)` sentexes to query.
- `(sibling_disjoint C)` — a collection whose **specializations** (the types below `C`
  under `genl`) are pairwise disjoint, *unless one is a `genl` of the other*. It is the
  metatype clique keyed off the `genl` closure rather than a recorded member set: only
  the mark on `C` is cached (`:sibling-disjoint`, reference-counted on the
  `(sibling_disjoint C)` sentex), and `disjoint?` tests whether a supertype of either
  side is a specialization of `C` by reading that supertype's own `genls`, where the
  metatype arm reads its members. `C`'s spec closure holds the whole clique and is rebuilt
  after every `genl` edge, so an edge into the clique does not read it (`lein perf`'s
  `sibling-disjoint-new-spec`). So nothing quadratic is stored, dropping
  the mark releases every pair at once, and a specialization added later — an `(A C)`
  membership is a mistake, but a `(genl A C)` edge is the shape — is separated the
  moment it is believed.

  The genl-relatedness exception is essential and not a special case: a type and its
  own supertype are both specializations of `C`, so without it the mark would separate
  a subtype from the very type it refines. It is read over the **whole** KB, not the
  reader's context ancestor set — the same global test `(disjoint a b)` applies when it refuses
  a genl-related pair as ill-formed — which is what keeps the sibling arm monotone on
  the visibility of `genl` edges, so a descendant context never separates a pair the
  whole edge set knows overlaps.

  **A mark says nothing about covering.** `sibling_disjoint` says the specializations
  do not *overlap*; it does not say they *exhaust* `C`, so a bare `C` carrying no
  further membership violates the mark in no way. Exhaustion is declared separately and
  by name, over a named roster rather than over every specialization at once —
  [covering](#covering-a-whole-and-the-parts-named-against-it), below.
- `(orthogonal X Y)` — the converse of a separation: `X` and `Y` may overlap (something
  could be an instance of both) and neither is a `genl` of the other. It does not say that
  anything is an instance of both, and claims nothing about things that are instances of
  neither. Symmetric, so `(orthogonal Y X)` is the same sentex, and forced monotonic. It
  derives nothing — no shared instance is minted for it — and is read in three places.

  **It exempts the pair from every form of disjointness.** Each form is one claim: a
  `(disjoint X Y)`, a `partition` or `separating` roster naming both (a partition keeps
  its coverage half), a `disjoint_metatype` and a `sibling_disjoint` parent. Over the pair
  the `orthogonal` names, none of them separates. It is keyed as an unordered pair exactly
  like `disjoint` (`:orthogonal-index`, reference-counted on the `(orthogonal X Y)` sentex)
  and read by `disjointness-test` behind each arm's guards. A Braille reading, both a
  `reading` and a `touch_perception`, is the case it exists for. The `disjoint` or roster
  stays stored and believed; the KB integrity sweep is where a stated `disjoint` beside an
  `orthogonal` of the same pair is reported.

  **Pair-local, read against the separated pair.** The exemption spares `X`, `Y` alone,
  and each stays disjoint from everything else. A separation is found between a
  supertype of each side, and the exemption is tested against that pair: exempting `X`,
  `Y` therefore lifts what their separation reached below them, while an `orthogonal`
  over two subtypes `X'`, `Y'` of a pair that stays separated exempts nothing. Overlap
  propagates upward: an instance of both `X'` and `Y'` would be an instance of both `X`
  and `Y`, so that declaration is the clash below.

  **Read at the reader.** A reader is exempted only by an `orthogonal` some supporter
  states where it reads (`tax/exemption`): a context that sees it reads the pair apart,
  and a context above it or beside it reads the pair separated. With `(sibling_disjoint
  C)`, `(genl A C)`, `(genl B C)`, `(A X)` and `(B X)` in CxU and `(orthogonal A B)` in
  CxE below CxU, CxU reads the two memberships as a nogood and CxE reads none, in every
  arrival order (`reference_test`'s
  `a-sibling-exception-exempts-its-pair-only-where-it-is-seen-in-every-order`). The
  exemption is the one read that makes `disjoint?` non-monotone on visibility: seeing
  more contexts can remove a separation. An unscoped read sees every `orthogonal`.
  The membership candidate index keeps the pairs the unscoped taxonomy separates with no
  exemption read, and marks the ones a stored `orthogonal` spares, so a reader that does
  not see the declaration still finds the nogood and a reader that sees every ground
  context reads a spared one again over its own ancestor set (`membership/separation-tests`,
  `membership/scoped-reads`). Asserting an `orthogonal` releases a standing clash at the
  readers that see it and retracting one re-arms the pair: the exempted pairs are part of
  `tax/separation-stamp`, so their move reads every kept type pair's separation again
  (`membership/sync-memberships`).

  **What contradicts it is a clash.** A `genl` edge between the two, the one type named
  twice, or a separation of two supertypes it does not exempt makes the declaration a
  one-member nogood wherever a reader reads that
  ([nmtms.md](nmtms.md#declarations-over-related-types)).

  **And it is one of the `:orthogonal` witnesses** `subsumption-status` reads
  ([below](#auditing-the-hierarchy-for-missing-disjointness)).

**All three separating mechanisms — `disjoint`, `disjoint_metatype` and `sibling_disjoint` — separate any term, not only individuals.** `checks/checkable-term?`
admits every non-variable symbol, so the predicate meta-ontology is enforced the same
way the domain is: `(relation_kind …)` is a `disjoint_metatype` over
`instance_relation_predicate` and `type_relation_predicate`, and a predicate declared both
is a clash exactly as `Muffet` being both a `dog` and a `cat` is. The same widening makes
`arg` constrain predicate-valued positions — `(arg typeToInstancePred 1
type_relation_predicate)` refuses a link whose first argument is not classified
type-level. A **value** is typed by what it *is* rather than by what somebody
asserted: `checks/value-kind` reads its EDN kind, and the kinds sit in the lattice
(CxCore) precisely so the comparison can be made — a `string` is not a `dog`, and `arg`
says so. There is one per leaf kind a sentence can carry, and the set is complete on
purpose: a kind with no name is one both argument checks must wave through, which is a
hole in a declaration rather than a policy. A **compound** stays outside that lattice: what
`(QuantityFn 5 Meter)` denotes is its function's business, not its syntax's, so no kind
would be the right answer — and its function is what answers instead. `arg` reads
`(result F T)` and `genlArg` reads `(genlResult F T)`, from the asking context's
vantage, so the declaration binds every application of `F` whether or not `F` mints one:
a *reifiable* application arrives as its minted constant carrying the same types
materialized, an *unreifiable* one is read through the declaration itself, and both meet
one verdict ([nat.md](nat.md)). A function that declares no result exempts its
applications, exactly as an unclassified symbol exempts itself.
Open-world is unchanged for a **symbol**: a term carrying no type membership at all
still cannot violate anything.

`disjoint? kb a b` decides disjointness via the genl closure. Disjointness is
enforced as **contradiction detection**: `assert` of a type membership `(T X)`
is rejected when `X` already holds a type disjoint from `T`. Finding `X`'s
existing types is a lookup on the argument root (`types-of`).

### What the question is asked of

Declarations are held two ways, because the walk and the report want different
shapes. `:disjoint` is the set of unordered `#{x y}` pairs — what `disjoint-pairs`,
`separating-pairs` and the witness search read, and the form in which a declaration
is one thing. But answering `disjoint?` means walking `a`'s genl closure against `b`'s
looking for a separated pair, and consulting a set of pairs means *building* a
`#{x y}` per candidate: on a term holding a few types over chain-deep closures that is
hundreds of two-element hash sets allocated to answer one assert. So the same relation is
also kept as adjacency — `:disjoint-index`, `{type -> #{types declared disjoint from
it}}` — and the walk reads that: one map lookup per supertype, short-circuiting on
the `nil` that most types have. Both are maintained at `cache-install` /
`cache-uninstall`, so belief moves them together.

The metatype arm has the same shape and is inverted the same way, from the other
side: a metatype has a handful of members where a closure has a chain's worth of
supertypes, so it intersects the members against both closures rather than testing
membership over their product.

`tax/disjointness-test` is the whole question with `a` and the context fixed — the
closure, the visibility ancestor set, the adjacency and the metatype roster read once
(`separation-frame`), returning a predicate over candidate types. `disjoint?` is that
asked once; `checks/disjoint-problem` asks it of every type the term already holds,
which is what it exists for.

Unscoped, neither side reads a whole closure. The frame and each candidate read their
supertypes cut to the separable types (`separable-genls`): those declared disjoint from
something, the members of a disjoint metatype, the sibling-disjoint parents and the
partition parts. A cut is built from the parents' cuts and held in the closure cache
beside the closures, keyed by the separation stamp. Most types sit under few separable
types or none, so the membership sync that frames every type of a large KB after a
recover costs the edges and a small set per type. Only the sibling arm reads a whole
closure, for the chain under a marked parent.

Scoped, the cut is the same set built through the edges the reader sees
(`separable-genls-at`). Read from an ancestor set, which carries no belief callback, it is
held in the closure cache beside the unscoped cuts, as the membership nogoods a reader
finds from a term ask it; from a concrete context, whose scope reads belief, it is held
only inside a read-only pass, in the pass cache: a reader's re-read of its
definitional nogoods frames the types of every nogood it re-asks, and a scoped closure a
type was most of what it read. A `genl` component every edge of which the reader sees is
read as one unit, as the unscoped build reads each one. A concrete context off a pass, and
a type whose build meets a cycle through a component the reader sees only part of, read
the scoped closure itself, uncut: it holds the same separable types, and cutting it would
cost more than reading it.

### Enumerating instead of testing

A goal with an open argument — `(disjoint a ?t)` — asks the other question: not *is
this candidate separated* but *which types are*. [why the answer is not found by
testing every type](defenses.md#the-answer-is-not-found-by-testing-every-type)

So it is read off the same frame, the other way round. `tax/separating-partners` is
every `y` a visible declaration separates `a` from — the pairs `a`'s supertypes carry
in `:disjoint-index`, plus the other members of any disjoint metatype one of them
belongs to, plus the specializations of a `sibling_disjoint` parent one of them stands
beside. Every type disjoint from `a` is a subtype of one of those partners and
nothing else is, since inheritance through `genl` is how a separation reaches a
candidate at all; so the answer is `specs` of the partner set, and its size is the
answer's own. `tax/separating-pairs` is the same question with neither side given,
which is what bounds a two-variable goal.

The visibility filter belongs *here* rather than at the lookup: `:disjoint-index` is
the adjacency of every declaration in the KB and carries no context, so an
enumeration driven straight off it would report a context's separations to a
context that cannot see them. One prologue serves the test and the enumeration for
that reason — a candidate the predicate convicts and the enumeration cannot reach is
an answer that silently stops existing, and two copies of this is how that happens.

**Which context it is asked from is a separate question from what it may see.** The
answer is scoped and stays scoped, but a pair whose halves sit either side of a
`genlCx` edge is visible from neither of the two contexts they are written in
alone, so each reader asks it over its own ancestor set, and the readers that see both
halves decide it ([nmtms.md](nmtms.md#nogoods-decided-at-the-reader)).

### Auditing the hierarchy for missing disjointness

`subsumption-status kb a b` classifies one type pair against the whole hierarchy at once,
returning `:genl` / `:spec` (one subsumes the other), `:coextensional` (each is `genl`
the other), `:disjoint` (a declaration, closed under `genl`), `:orthogonal` (a stated
`(orthogonal a b)`, or, where neither subsumption nor disjointness holds, a shared
instance the registry answers without rule expansion or a shared subtype that is not
provably empty), `:unknown` (none of these is provable), or `:inconsistent` (two
or more hold at once, such as genl-related and disjoint, or a stated `orthogonal` beside
a `genl` edge or a separation of two supertypes it does not exempt).
`genl?` reads the global closure. `disjoint?` and the `:orthogonal` witnesses are read
from a `context` (default `CxUniverse`), because a read sees only that context and its
`genlCx` ancestors and an `orthogonal` exempts its pair only where it is seen. Two of
the three witnesses are facts-only queries (`{:max-depth 0}`): for the
`(orthogonal a b)` declaration in either spelling, and for a member of `a` that is also
a member of `b`. The third, a type in both `specs` closures, is read from the global
closures as `genl?` is, and its self-separation from `context`. The declaration stands
alone; the shared instance and the shared subtype settle only a pair the taxonomy and
the separations leave open.

**A shared subtype counts only when it is not provably empty.** Every member of a
subtype of both `a` and `b` is a member of both, so a subtype with a member puts one in
the overlap. An empty type is a subtype of every type, so an empty shared subtype shows
nothing, and nothing in the KB refuses an empty type
([below](#and-against-the-variables-of-a-rule)). The engine proves a type below two
separated types empty, and `disjoint?` reports such a type as separated from itself; a
stated `(disjoint c c)` is refused by `wff`. A known `(empty c)` is the other proof of
emptiness the reading accepts. A shared subtype for which `(disjoint? kb c c context)` is false
and no `(empty c)` is known shows that the two types can overlap. A pair whose only
shared subtypes are provably empty stays `:unknown`.

**A shared subtype is a witness only when it is known nonempty.** A known
`(nonempty c)` makes the shared subtype a `:shared-spec` witness. A claim is known when a
facts-only query answers it: stated, concluded by a forward rule, or carried along
`genl` by `(transitiveInArg nonempty 1 genl)` from a nonempty subtype, and
`(transitiveInArgInverse empty 1 genl)` carries `empty` down the same way. A shared subtype with
no known `(nonempty c)` still
reads `:orthogonal`, and the audit marks the pair `:unwitnessed-spec`: the two types can
overlap, and the KB names no instance in the overlap. Both reads are facts-only, from
the same `context` as the shared instance.

`disjointness-audit kb` runs the classification over every unordered pair of distinct
types and returns `{:types :pairs :by-status :pairs-data}`. A relation that a `genl`
edge between relations names, such as `performedBy` under `doneBy`, is a node of the
hierarchy and not a type, so the audit leaves it out. A node is such a relation by an
arity of two or more, read from `(arity P n)` or an exact-arity class, or by a
`variable_arity` declaration. An entry whose `:statuses`
holds `:orthogonal` also carries `:witness` — `:declared`, `:shared-instance`,
`:shared-spec` or `:unwitnessed-spec` — and, for the last three, `:via`, the instance or
the subtype found. Of several shared subtypes it names a nonempty one ahead of the
others, and among those the one with the most subtypes of its own. Of several shared
instances it names the least in content order. A shared instance is reported ahead of a
shared subtype. The `:unknown` pairs are the candidates
for a missing `disjoint` or `orthogonal` declaration: no subsumption relates them, no
declaration separates them, and neither a declaration, a shared instance nor a shared
subtype shows they can overlap — so the modeller decides which they are. The audit reads
only, and writes nothing.

### What a declaration reaches back over

A declaration changes what already-stored content *means*, so a reader reads the content
written before it, or the KB would answer differently depending on whether the separation
or the memberships were written first, which is the invariant [nmtms.md](nmtms.md) opens
with. Nine sentence shapes move what a membership clash means: `disjoint`,
`disjoint_metatype`, `sibling_disjoint`, `partition`, `separating`, `covering`, a new
`(M T)` member of a metatype, `orthogonal` leaving, and `genl`.

**No declaration arriving reads a membership.** The candidate index keeps every term
holding two memberships, or a membership and a denial, and each pair of types some kept
term holds (`membership/note-membership!`), whatever the KB declares. A declaration moves
`tax/separation-stamp`, and the index reads the separations again over those type pairs
(`membership/sync-memberships`): one separation test per pair, so the cost is the vocabulary
of type pairs some term holds and not the extent below the types. A `genl` edge moving is
logged at its lower end (`tax/moves-since`), and only the pairs holding a type at or below
it are read again; `lein perf`'s `sibling-disjoint-new-spec` holds an edge flat in the
pairs beside it. A term
holding a separated pair, or a membership and a denial under a stored cover, keeps its
nogoods, and each reader reads them off the index
([nmtms.md](nmtms.md#nogoods-decided-at-the-reader)). `lein perf`'s
`membership-declaration-arrival` holds a declaration's arrival flat in the memberships
under the types it separates. `(M T)` is an ordinary unary membership whose functor is
whatever the metatype is called, and it moves the metatype roster the stamp holds, as
`(disjoint A B)` moves the pair roster. A `genlCx` edge moves which readers see both halves
of a pair, and no candidate.

The merge sweeps are bounded where the membership families are not.
`special/equate-under-context-edge`'s merge-deriving sweep takes a handle-ordered prefix
of the ancestor set a `genlCx` edge widens, within `tax/*exposure-instance-budget*`, and
nothing re-triggers on an edge that has already landed. So past that cap arrival order
decides whether a merge is derived at all. It is reported on every cut
(`:context-edge-exposure-truncated`) and exact below the cap; the residual is stated in
full in [equality.md](equality.md).

The **standing** question needs no index: a term is a candidate iff it holds two believed
memberships, so walking the memberships finds every candidate exactly, which is what
`core/exposed-clashes` does. It names every jointly-visible pair, decided or not.

## Covering: a whole and the parts named against it

Two independent claims can be made about a named roster of parts, and three spellings
make them:

```clojure
(covering   Whole Part1 Part2 …)   ; the parts exhaust Whole, and may overlap
(separating Whole Part1 Part2 …)   ; no two parts share an instance, and they need not exhaust
(partition  Whole Part1 Part2 …)   ; both
```

| | the parts exhaust the whole | the parts are pairwise disjoint |
|---|---|---|
| `covering` | yes | no claim |
| `separating` | no claim | yes |
| `partition` | yes | yes |

`separating` is the roster-shaped spelling of what `disjoint_metatype` and
`sibling_disjoint` say about a metatype's members and a parent's every specialization:
the same separation over a named few, with no metatype term to invent and no claim about
the specializations nobody named.

All three relations are variable-arity, and each takes a whole followed by two or more
distinct parts. Argument 1 is the whole, and the part roster commutes
(`(commutativeInArgAndRest covering 2)`), so a roster written in another order is the
same sentex rather than a second one. The three are one cache entry apart: the key
carries the whole, the sorted roster and which of the two claims the declaration makes
(`tax/cover-kinds`).

### A cover states the specialization it rests on

Each part is a subtype of the whole, and the declaration **states** that edge rather than
demanding that one already exist. All three spellings install a `genl` edge per part
through `tax/add-genl`, supported by the declaring sentex and carrying its context,
exactly as a stated `(genl Part Whole)` does. Three consequences follow: `(Part1 X)`
answers `(Whole X)` with no second declaration written by hand, every reader of the
closure sees one taxonomy rather than two, and defeating or retracting the cover drops
the edges with it. A cover asserted before its parts carry any other fact therefore
settles to the state a cover asserted after them does.

Every reader that asks which edges a datum put into or took out of the closure reads them
off `tax/installed-edges`, which names one edge for a `genl` sentence and one per part
for a cover. A cover arriving after a rule on the whole and a fact on a part therefore
seeds the rule over that fact (`subsumption-seeds`) and re-joins a rule reading `genl`
(`chain/closure-rejoin-rules`), and a retracted cover re-derives over a surviving route
(`resubsumption-seeds`), each as a stated edge in its place does.

### The coverage inference is gated on explicit negation

For `(covering W A B C)` and a term `X`, a believed `(W X)` together with a believed
`(not (A X))` and `(not (B X))` proves `(C X)`. `CoveringProver` answers that goal the
way `DefnSufficientProver` answers a definitional membership: a ground goal, one bounded
subquery per premise, and no enumeration of a part's extent.

Nothing fires on absence. `(W X)` with no part known stays unknown — the cover invents no
membership, picks no part, and reports no violation. A ruled-out part must be **known
not**: a believed `(not (Part X))`, never a `(Part X)` that merely cannot be proved.
Negation as failure is a separate operator, spelled `unknown`, and it stays a query
operator that nothing stores ([naf.md](naf.md)).

Ruling out *every* part falsifies the cover. `(W X)` with `(not (A X))`, `(not (B X))`
and `(not (C X))` is a contradiction of kind `:cover`, and the entry point treats it as
it treats a disjointness clash: the sentence that completes it is stored, and the
refutation is a nogood decided in every arrival order. A denial of a supertype of a part
denies the part: `(not (Q X))` with `(genl A Q)` rules out `(A X)`. The candidate index
keeps a term holding a membership and a denial, and reads its covers again when the
covering roster (`tax/coverings`, in `tax/separation-stamp`) or a `genl` edge moves, so the
membership, a denial or the declaration arriving last forms the same nogood
(`reference_test/a-cover-refuted-through-a-denial-of-a-part-s-supertype-is-decided-in-every-order`).
The nogood names the membership and the
negations and **not** the declaration, which is `disjoint`'s rule and is there for
`disjoint`'s reason: a nogood that could defeat the cover would read a taxonomy without
it on the next pass, find no violation, and revive it.

### `partition` and `separating` add no separation mechanism of their own

A separating roster is recorded the way a `disjoint_metatype`'s member set is: held
in the taxonomy, consulted by `disjointness-test`, and never written out as `(disjoint
…)` sentexes. An `orthogonal`, the genl-relatedness guard and the nogood reporting
therefore read a partition exactly as they read a metatype. A bare `covering`
records no separation at all, so two of its parts may overlap and `disjoint?` answers
false for the pair.

**Every reader of a separation reads all four spellings**, and each place that enumerates
them is a place the roster has to appear by name: `clashes/separations?`, the emptiness
gate `exposed-clashes` sits behind; `tax/separation-stamp`, which decides whether the
membership candidates' separations still hold; `disjointness-witnesses`, whose emptiness a
caller reads as *not disjoint at any reader*. A gate naming fewer spellings than the test behind it shuts on a
KB `disjoint?` answers true in — and the pair the entry point stores is then never
weighed, with `contradictions` and `exposed-clashes` both reporting nothing about it.

`disjoint_metatype` keeps its own meaning — pairwise disjointness among members, with no
claim that the members exhaust anything.

Only a **covering** roster reaches `CoveringProver` and the refutation check, so a
`separating` declaration proves no membership and is falsified by no set of negations: an
instance of its whole belonging to none of its parts is what it declines to speak about.

### What a cover is refused for

`wff/covering-problems` rejects any of the three that states nothing or cannot hold: fewer
than two parts, a repeated part, an individual in any position, a part equal to the
whole, and a part the closure already places above the whole (the `genl` edge would close
a cycle). Each refusal takes the structured `:not-well-formed` path rather than throwing,
as every other `wff` arm does. A part disjoint from the whole is stored: the refusal would
read the stored `disjoint`, and what is stored would depend on which of the two arrived
first ([nmtms.md](nmtms.md#1-order-independence)).

### The three partitions of `thing`

CxCore divides `thing` three ways, each with a `partition`, so each pair is separated and
covers `thing`:

| partition | the first part | the second part |
|---|---|---|
| `(partition thing spatial aspatial)` | a location in some space, physical or mathematical | no location in any space |
| `(partition thing temporal atemporal)` | a location in time | none |
| `(partition thing tangible intangible)` | mass | no mass |

`genl` edges and two intersections in CxCore relate the parts across the three
divisions. `tangible` is below `spatiotemporal`, the intersection of `spatial` and
`temporal`. `aspatial` and `atemporal` are below `intangible`, and `nowhere_never` is
their intersection. No edge or disjointness relates `intangible` to `spatial`: a region
of space is `spatiotemporal` and `intangible`.

A kind with no location in any space sits below `aspatial`, which separates it from
`spatial` and from every CxSpace argument. `fluent` and `organization` (CxAbstract) are
below `aspatial`. `relation_type` (CxAbstract) is below `nowhere_never`, so
`relation_type` is `aspatial` and `atemporal` both.
The `expression` lattice is in CxCore. `expression` is below `nowhere_never`, and
`context`, `relation`, `formula`, `relation_application`, `denotational_term` and
`unrepresented_term` are below `expression`. The value kinds `string`, `number`,
`keyword`, `boolean` and `character` are below `unrepresented_term`. `language` is below
`nowhere_never` in CxCore too. Every spindle member therefore reads each of these kinds as
disjoint from `spatial`.
`ontology_test` pins each separation from the contexts that read it.

## Predicate metadata

Beyond types, the taxonomy caches predicate properties, declared as sentexes and
maintained by `integrate-sentex`. The relation marks `irreflexive`, `anti_symmetric`,
`asymmetric`, `functional`, `functionalInArg`, `anti_transitive`, `transitiveInArg` and `transitiveInArgInverse`,
the function classes `injection`, `surjection` and `bijection`, and the declarations
`disjoint`, `covering`, `partition` and `sibling_disjoint`, and the arity bindings
([Arity](#arity)), are on the forced-monotonic roster: each is held `:monotonic` whatever
strength it was written at, and a denial of one is held OUT
([nmtms.md](nmtms.md#the-forced-monotonic-roster)).

- `(transitive P)` / `(symmetric P)` / `(reflexive P)` — drive the generic
  relation provers (see [inference.md](inference.md)).

  `symmetric` is the one of the three that also decides **storage**: the entry point sorts a
  ground symmetric literal's arguments, so the two spellings of a pair are one sentex.
  That makes its retroactive half a record migration rather than a derivation — a mark
  arriving after the facts re-spells the rows stored before it and folds a mirrored pair
  into one, or the same knowledge in two arrival orders would leave two records for one
  proposition (vaelii#61). What it does, what it keeps and what it declines:
  [canonicalization.md](canonicalization.md#a-mark-arriving-after-the-facts-migrates-them).

  A declared-transitive `P` is **metadata only** — it is not a cached relation. Nothing
  about `P` enters the adjacency, so there is no closure to maintain, no depth potential
  to repair, and nothing an arrival order could make expensive; asserting `(largerThan A
  B)` is an ordinary fact assert. The cost is entirely at query time, where
  `TransitivePredicateProver` walks the believed facts (memoized per search step,
  `observe/*reach-memo*`, and the answer held per KB — "What is cached", below). A
  **closed** goal stops at its answer, so a near pair is
  cheap; an **open** one enumerates and needs the whole reach, which is inherent. Both
  guard with a `seen` set, because nothing refuses a cycle in a user-declared transitive
  predicate the way `wff` refuses a `genl` cycle — and a cycle there genuinely entails
  reflexivity around the loop rather than being an error.

  `genl` and `genlCx` are cached instead precisely because the engine reads them on
  every match, placement and visibility check, where recomputing a reach per read would
  not survive. That is the whole difference, and it is why only those two carry the
  machinery above. A forward join reads the two cached closures as well as their stored
  edges, with the same bounded arms the walk below has
  ([inference.md](inference.md#a-genl--genlcx-antecedent-reads-the-closure)).

  #### The step relation: which hops are on the graph

  A closure is a walk, so what it answers is decided by what counts as **one hop**, and
  that is a narrower thing than what the engine can answer about a pair. A hop is a
  **believed match** (`res/matches-visible`), which is:

  - a stored believed `(P x y)` **visible from the asking context** — the walk follows
    belief and visibility like every other read, so a hop stored where the asker cannot
    see it is a break in the chain rather than an edge of it;
  - a stored `(P' x y)` for a sub-predicate `P'` of `P`, since the matcher fans the
    functor over its `genl` spec closure;
  - the **symmetric mirror**, for a `P` also declared symmetric — the mirrored probe
    `raw-match` makes, so one direction of each edge is enough to read an equivalence
    class;
  - a stored `(Q y x)` where `(inverse P Q)` is visible, because that *is* the edge
    `x → y` written in the partner's spelling. A user declaring both `inverse` and
    `transitive` of one relation — ordinary temporal modelling — gets a chain that
    crosses hops recorded either way round.

  Each probe is a `matches-visible` call and never a goal handed back to the prover
  registry, and that is required twice over. It keeps the step relation a function
  of the KB alone rather than of the tier and scope a `solve-goal` answer carries (the
  argument is `vaelii.impl.literal-cache`'s), and it is why a mutual `(inverse P Q)` +
  `(inverse Q P)` pair cannot cycle here — a recursion across predicates that the walk's
  own per-node `seen` set would not close.

  **A rule's conclusion is not a hop, and that is deliberate.** Nothing may start an
  unbounded proof search from inside a walk a relabel loop can reach — the same sentence
  [naf.md](naf.md) carries for negation as failure and `provers.clj` carries for
  aggregates. So a `set/backwardRule` concluding `(P b c)` answers that goal when it is
  *asked*, and leaves the chain through `b` broken. A calculus entailment
  ([qcn.md](qcn.md)) and an `transitiveInArg` conclusion ([inherit.md](inherit.md)) are
  outside the step relation for the same reason. Materialize the hop with a forward rule
  and the walk crosses it, because then it is a stored fact.

  #### The other direction: a forward join reads the walk

  A rule *conclusion* is not a hop, and a rule *antecedent* on a declared-transitive
  predicate is answered by the walk. The two are not in tension: the first would put a
  proof search inside the closure, and the second puts the closure inside a join, which is
  bounded by one node's reach.

  `chain/join-antecedent` unions the walk's answers with the matcher's, so a rule whose
  antecedents are `(event ?a)` and `(causes ?a ?c)`, `?a` bound by the first when the
  second is joined, fires across two stored hops and not only across one —
  and `TransitivePredicateProver` is a `prover-types/SupportingProver`, so each answer carries
  the handles of one chain of edges (a breadth-first pass with parent pointers, so a
  shortest one) and the firing rests on exactly those. Retracting a hop of the chain
  withdraws the conclusion by the ordinary relabel; retracting an edge the chain never
  crossed withdraws nothing. An arriving edge re-joins the rules carrying such an
  antecedent in full (`chain/transitive-rejoin-rules`), because the trigger index offers
  only the tuple the edge is *stated* at and the pairs it licenses *through* itself are
  reached by joining. Details, and what the protocol does not carry, are
  [inference.md](inference.md), "What a computed answer rests on".

  The bounded arms are the ones that answer, here as anywhere: an antecedent with both
  ends open contributes nothing from the walk, for the quadratic reason below.

  **A rule that concludes on what it would walk takes the matcher alone**
  (`chain/walks-its-own-conclusion?`), and that is about the support rather than the
  answer. A forward-derived edge *is* a hop — it is stored and believed, and an `ask`
  crosses it like any other — but a rule deriving `(P x z)` from `(P x y)` and `(P y z)`
  stores its conclusions *inside* the fixpoint, so which chain was shortest would depend on
  how far the rule had got, and two chainers agreeing about every belief would record
  different antecedents for one conclusion. Nothing is lost by declining: that rule **is**
  the closure written out, it reaches every pair the walk would, and each conclusion rests
  on the two hops it joined. The test is a property of the rule, so it answers the same
  whatever else the KB holds and in whatever order it arrived.

  **The `(transitive P)` declaration re-joins too**, exactly as a `(symmetric P)` does: it
  is what turns the antecedent into a walk, and the edges it walks have already arrived, so
  nothing about `P` would otherwise bring the rule round again.

  **With both arguments open the walk answers nothing, and the extent answers instead** —
  the stored `P` facts and those of `P`'s `genl` sub-predicates, through the ordinary
  match path, exactly as for a predicate carrying no marker at all. The prover's
  `completeness` is 70 rather than 100, so the registry unions it rather than running it
  alone, and contributing no solutions here is a contribution of none rather than an
  answer of none.

  The asymmetry with the bounded arms is deliberate. Those fix one end, so both the work
  and the answer are bounded by one node's reach. A fully-open ask is bounded by neither:
  a transitive closure is **quadratic** in a chain's length, so returning it for a
  1M-node chain means offering half a trillion pairs rather than coming back. Laziness
  does not rescue that — `reach` is a fixpoint, so the first pair costs a whole node's
  closure. **The closure is computed for membership and for one bound end; it is never
  stored and never enumerated whole.** A caller who wants it asks for it: `(P ?x ?x)` is
  the one-variable case and asks which nodes lie on a cycle, and binding one end per
  source term is the general way.

  So `(P ?x ?y)` and a loop over `(P a ?y)` give different answers, and that is the one
  place a marker's arms disagree. It is the trade the quadratic buys.

  #### What one hop costs, and where

  Two facts elsewhere in these docs multiply, and the product matters: the walk
  reads the **believed facts**, and a stored-fact read on `:disk` is a **paged decode**
  ([storage.md](storage.md)). So a hop that crosses an edge costs one `get-sentex` — the
  per-candidate fetch in `resolution.clj`, since the neighbour term lives in the record
  and nowhere else — and a walk of *n* nodes costs *n* of them. `docs/storage.md` takes
  the same product for `rebuild-taxonomy`; this is the read-side twin of it.

  `lein bench-walk` measures the fetch as a **share** of the hop rather than assuming it
  is the hop, by timing a direct sweep over the same records on the same mount. What it
  finds is a threshold rather than a slope, and the threshold is the hot-record LRU's
  capacity (`docs/density.md`):

  | chain | fetch, `:memory` | fetch, `:disk` | share of the hop, `:disk` | `:disk` walk vs `:memory` |
  |---|---|---|---|---|
  | 20,000 nodes | 0.14 µs/edge | 0.06 µs/edge | 1% | 0.92× |
  | 150,000 nodes | 0.37 µs/edge | 3.03 µs/edge | 21% | 0.61× |

  Under the LRU the fetch is *cheaper* on `:disk` than on `:memory` — a hit is one
  `LinkedHashMap` read against a nested-map lookup — and the two mounts walk at the same
  speed. Past it the fetch is a real page-in at 3.03 µs, which is the warm figure
  `density.md` publishes, and the disk walk falls to 0.61× the memory one. `:disk-memory`
  (durable records, RAM index) lands with `:disk-log` at every size, which is what says the
  **record store** is the whole of the difference and the index half is none of it.

  The rest of a hop — canonicalizing the pattern, the scoped argument-root read, the
  belief test, the unify, and the walk's own bookkeeping — is the same work on every
  mount, and it is the majority of the cost at every size measured. That is the number to
  hold against any scheme for making the fetch cheaper: it bounds one.
- `(asymmetric P)` — a *constraint*, and the mirror of a claim denies it: `(P a b)` and
  `(P b a)` are contradictory, so a claim whose converse is believed forms a nogood with
  it, which the settle decides; a converse read by preservation opposes at the weakest
  class of the claim and its reading ([inherit.md](inherit.md)). A strict order like
  `largerThan` is the usual case. The conviction needs a believed **opposing** sentex, and a self tuple has
  none — its converse is the sentence itself — so `(P a a)` is admitted with no clash,
  which asymmetry alone would not license. `inherit/claims` skips the converse probe
  there for the same reason, and says so.
  It is also what gives the converse standing to deny a preserved claim, so it decides
  whether `TransitiveInArgProver` finds anything *against* one
  ([inherit.md](inherit.md)).

  **`:pred` on the violation names the marked predicate, not the sentence's own
  functor**, and a caller reading the two as one key reads it wrong. The mark is read up
  the hierarchy and the converse is probed at the predicate carrying it, so what the
  violation reports is the predicate whose declaration convicted — the general spelling,
  whenever the sentence is written at a specialization of it:

  ```clojure
  (assert kb '(asymmetric parentOf) 'CxUniverse)
  (assert kb '(genl fatherOf parentOf) 'CxUniverse)
  (assert kb '(parentOf Ann Bob) 'CxUniverse {:strength :monotonic})
  (require '[vaelii.impl.checks :as checks])
  (checks/arbitrable-violations kb '(fatherOf Bob Ann) 'CxUniverse)
  ;; [{:type :asymmetric :sentence (fatherOf Bob Ann) :pred parentOf
  ;;   :opposing (parentOf Ann Bob) :opposing-handle 3
  ;;   :message "asymmetric: parentOf cannot hold both ways, and (parentOf Ann Bob) is known true"}]
  ```

  The functor of `:sentence` is the spelling the caller wrote; `:pred` is the declaration
  it ran into. Several supers may carry the mark and each contributes its own violation,
  so one sentence can yield several entries differing only in `:pred`. `:opposing` and
  `:opposing-handle` name the believed claim on the other side, which is what makes the
  entry a pair `settle` arbitrates rather than a refusal.
- `(inverse P Q)` — `P` and `Q` are inverses. A predicate may declare **several**, and
  the cache holds `{predicate #{partners}}` maintained in both directions, so retracting
  one declaration retires that partner and leaves the rest. `tax/inverses-of` is the set,
  and it is what the step relation walks and what `solve-inverted` unions over;
  `tax/inverse-of` answers *a* partner — the lexicographically smallest, so a caller
  wanting one gets a content-keyed answer rather than an order-keyed one. `P` may be its
  own inverse, which says `(P a b)` iff `(P b a)` — the same claim `symmetric` makes, and
  the cache key folds to the one-element set it names. **A partner declared on a
  sub-predicate answers the super-predicate's goal**, since a sub-predicate's tuples are
  the super's: `tax/inverses-under` is that set, and it consults the spec closure only
  where some inverse exists at all, so a KB declaring none pays one lookup.
- `(arity P n)` — the declared arity, cached for the argument-position check and
  `kb/relation-arity`; the arity nogoods read it from the candidate index
  ([Arity](#arity)).
- `(functional P)` — a *constraint*: two believed tuples `(P a b)` and `(P a c)` with
  `b` distinct from `c` collide (`checks/functional-clashes`). A collision of two symbols
  whose members are both `:monotonic` derives `(equals b c)` and merges
  (`special/derive-functional-equalities`, [equality.md](equality.md#what-a-merge-does)).
  Every other collision, a `:default` member or a filler that is not a symbol, is a
  nogood the settle decides (`checks/functional-problems`): the unique `:default` member
  is OUT, two `:default` members are a dilemma, and two `:monotonic` members are a hard
  clash ([reference.md](reference.md#decisions), decision 6).
- `(functionalInArg P n)` — the same constraint with the *determined* position named
  rather than fixed at 2: every argument of `P` except `n`, taken together, fixes the
  filler at `n`. `(functional P)` is the arity-2 case, and `(functionalInArg P 2)` on a
  binary predicate is behaviourally identical to it — the regression half of
  `functional_in_arg_test` holds that. The generalization gives a **composite
  determinant**, which the arity-2 spelling cannot express:
  `(functionalInArg namesObject 3)` says one namespace and one path name one object,
  where `(functional namesObject)` could only speak about argument 1 determining
  argument 2. `n` is one-based and held to a positive integer; an `n` past the
  predicate's declared arity is admitted and simply matches no tuple, matching `arity`'s
  own open-worldness about a declaration arriving before the arity does. Several
  positions may be declared for one predicate and each is an independent constraint —
  unlike `arity`, which collapses to a single value because two lengths are an ambiguity
  where two functional positions are two facts.

  It resolves exactly as `functional` does, and a merge rests on **every** declaration
  constraining that position, so a predicate carrying both `(functional P)`
  and `(functionalInArg P 2)` keeps its merge when either is retracted
  (`checks/functional-declaration-supporters`). It is read up the hierarchy for
  `functional`'s reason, through a reader of its own — `tax/functional-in-arg-over`,
  since the table is keyed `pred → #{n …}` and a `:props` roster has nowhere to put the
  integer, which is also why `functionalInArg` is not a `::prop-kind`.

  The degenerate end is worth naming: `(functionalInArg P 1)` on a *unary* predicate
  leaves an **empty** determinant, which reads as "at most one filler, full stop" — every
  believed tuple of `P` is then comparable to every other. A tuple finds the others of
  its determinant with one trie read when the determinant's positions lead, or one
  intersection of their argument roots, whatever the position and the arity, and a
  determinant already holding two fillers takes a new tuple with no read at all
  ([nmtms.md](nmtms.md#nogoods-decided-at-the-reader)).
- `(irreflexive P)` — a *constraint*, and the strict counterpart of `reflexive`: a self
  tuple `(P a a)` is a one-member nogood, decided at each reader that reads the mark
  ([nmtms.md](nmtms.md#nogoods-decided-at-the-reader)). A `:default` self tuple is OUT
  there and a `:monotonic` one is a hard clash in `conflicts`, whichever of the mark, the
  tuple, a `genl` edge between predicates or a `genlCx` edge arrives last. Stronger than
  `asymmetric`, which **admits** the self tuple, since asymmetry needs a believed opposing
  sentex to convict and a lone tuple names none. `(genl asymmetric irreflexive)` classifies
  every asymmetric predicate as an irreflexive one for a *query*, but does not set the
  `:irreflexive` property on it, so an asymmetric predicate still admits its self tuple.
- `(anti_symmetric P)` — a *constraint*: a believed converse `(P b a)` beside `(P a b)`,
  with `a` distinct from `b`, is a two-member nogood, decided at each reader that reads
  the pair and the mark ([nmtms.md](nmtms.md#nogoods-decided-at-the-reader)): the unique
  `:default` member is OUT, two `:default` members are a dilemma, and two `:monotonic`
  members are a hard clash. A converse of two symbols whose members are both `:monotonic`
  merges instead: the KB derives `(equals a b)` (`special/derive-antisymmetric-equalities`),
  the antisymmetric twin of what `functional` does with two symbol values and the same
  three arrival directions (fact, declaration, `genl` edge). The merge is justified by
  both facts and the declaration, so retracting any one un-merges. A converse is found
  under the tuple's own functor and under every predicate below a mark on it or above
  it. A self tuple's converse is itself and `(equals a a)` is trivial, so it is admitted.
- `(anti_transitive P)` — a *constraint* whose conviction spans **three** claims: `(P a b)`
  and `(P b c)` believed make `(P a c)` contradictory, the dual of `transitive`. The three
  are one nogood rather than three pairs, weighed by the same rule any contradiction is
  (`decide/verdict` over the whole member set): a chain that is known true refuses
  the direct step at the entry point, a chain with one defeasible step has that step defeated
  instead, and three equal defaults are a three-sided dilemma the engine reports and
  declines to decide ([nmtms.md](nmtms.md)). Read up the predicate hierarchy like the other
  constraint marks, and probed at the marked predicate, so `(anti_transitive parentOf)`
  convicts a `fatherOf` chain. It does **not** imply `irreflexive`: a self tuple `(P a a)`
  is its own whole chain, names no second sentex to weigh, and is admitted exactly as an
  `asymmetric` predicate's is. Its disjointness `(disjoint transitive anti_transitive)`
  holds beside that: no predicate is declared both.
- `(equivalence_relation P)` — no engine code: three shipped CxCore forward rules derive
  `(symmetric P)`, `(transitive P)` and `(reflexive P)`, each a real mark the engine
  enforces in turn. A `(genl equivalence_relation symmetric)` subsumption edge would answer
  the *query* but would not set the `:symmetric` property the enforcement reads, since a
  genl-inherited membership is not a stored `symmetric` sentex the mark ingestion sees — so
  the rules, which materialize that sentex, are the minimal correct expression.
- `(injection P)`, `(surjection P)`, `(bijection P)` — the composite **function marks**,
  no engine code either: eight shipped CxCore rules derive what the engine already
  enforces and audits. Each mark splits into two halves, and the split is what the family
  is for. The **enforced** half is `(functional P)` and `(functionalInArg P 1)`, merged or
  decided as a nogood exactly as a directly written mark is. The **audited**
  half is the binary `(predAllSpecified P D)` for totality and `(predSpecifiedAll P R)`
  for ontoness — each filler type derived from the predicate's own slot contract at
  read time — reported by `specified-violations` when a caller asks
  ([predall.md](predall.md)).

  | mark | single-valued | one-to-one | total on `D` | onto `R` |
  |---|---|---|---|---|
  | `injection`  | yes | yes | yes | no  |
  | `surjection` | yes | no  | yes | yes |
  | `bijection`  | yes | yes | yes | yes |

  **`D` and `R` are not arguments of the mark.** Totality and ontoness are claims about a
  domain and a range rather than about `P` alone, and `(arg P 1 D)` and `(arg P 2 R)`
  already state those two types, so the rules read them from there. A predicate declaring
  no `arg` pair gets the enforced half and no audit, rather than a requirement
  quantified over `thing`. `genlArg` is not read, so a
  `type_relation_predicate` — which the entry point refuses an `arg` on — carries the
  enforced half alone. The audit requirements rest on the `arg`
  declarations as well as on the mark, so retracting `(arg P 1 D)` withdraws them and
  leaves the refusals standing.

  **The two halves divide on what an open world can refuse.** A second filler contradicts
  a stored one, so the engine refuses it at the write. A domain member with no filler
  contradicts nothing — the filler may arrive next — so totality is a sweep to run at a
  checkpoint. `(bijection P)` derives `(injection P)` and `(surjection P)` rather than the
  base marks directly, so the whole family reaches the engine through two entries.
  `(genl bijection injection)` and `(genl bijection surjection)` state the subsumption
  outright; those edges set none of the properties the enforcement reads, for the reason
  `equivalence_relation`'s entry above gives, so the rules are the minimal correct
  expression.

**The constraint marks are read up the predicate hierarchy; the generative marks
are not.** Which family a mark belongs to decides whether it descends, and the reader
differs by mark. `tax/props-over` walks up for `asymmetric`, `functional`, `irreflexive`,
`anti-symmetric` and `anti-transitive`, the `::prop-kind` marks on the `:props` roster.
`functionalInArg` walks up too and is no prop: `tax/functional-in-arg-over` reads a
table keyed `pred → #{n …}`, which is `arity`'s shape rather than a roster's, and
returns the `[pred n]` pairs a probe predicate is reached by. `arity` is no prop at all:
a reader reads the bindings off the candidate index ([Arity](#arity)), falling back to the
super-predicates' where the predicate binds nothing of its own. And `inverse` has a reader of its own,
`tax/inverses-under`, which walks the hierarchy the other way.

| mark | descends? | why |
|---|---|---|
| `arity`, and the exact-class memberships | yes — read where the sub-predicate binds none of its own, and where it binds one the two disagreeing are a hard clash | a ternary `fatherOf` fact is a ternary `parentOf` tuple |
| `asymmetric` | yes | `(fatherOf a b)` beside `(parentOf b a)` is two `parentOf` tuples one way round each |
| `functional` | yes | two `fatherOf` mothers for one child are two `parentOf` values |
| `functionalInArg` | yes — through `tax/functional-in-arg-over` rather than `props-over`, the table carrying an integer | `(functionalInArg parentOf 2)` must convict two `fatherOf` mothers exactly as `(functional parentOf)` does, or the generalization would be weaker than the case it generalizes |
| `irreflexive` | yes | a `fatherOf` self tuple is a `parentOf` self tuple |
| `anti-symmetric` | yes | a `fatherOf` pair both ways is a `parentOf` pair both ways, merged under the super's mark |
| `anti-transitive` | yes | a `fatherOf` chain is a `parentOf` chain, and the steps may be spelled one at each level |
| `transitive`, `symmetric`, `reflexive`, `transitiveInArg` | **no** | a licence generates tuples, and generating them under a predicate nobody declared preserving is manufacturing knowledge |
| `inverse` | the other direction — a partner on a **sub**-predicate answers the super's goal (`tax/inverses-under`) | a hop recorded either way round is a hop |

Each of the three convicted on the exact functor while the machinery it convicts *with*
already fanned down the hierarchy — `matches-visible` finds the converse and the rival
filler under a sub-predicate spelling — so which spelling arrived second decided whether
the pair existed. The mark is now read at every predicate above the sentence's, and the
probe runs **at the marked predicate**: `(parentOf b a)` rather than `(fatherOf b a)`,
since only the general spelling's probe fans down over both. `arity` is the strict one: a
specialization does not get a signature of its own, because a `genl` edge says its tuples
*are* the super's and tuples of different lengths are not the same tuples, so two
disagreeing bindings across an edge are reported as a hard clash ([Arity](#arity)).

`tax/props-over` gates on the `:props` roster for the kind being empty, which it is on
nearly every KB, so a descending read is one map lookup where nothing is declared — the
gate `tax/inverses-under` takes on the empty `:inverse` map, and what keeps a closure
walk off the goal paths that ask `has-prop?` per goal.
- `(decontextualized_predicate P)` — every `(P ...)`, asserted or concluded by a rule,
  is also deduced into CxUniverse, which every context below the joint sees, so the
  fact stops being a claim of one theory. The target is fixed rather than named, because
  the definitional checks are context-scoped and only cover the copy when the stating
  context can see where it lands (see [contexts.md](contexts.md)).
- `(forced_decontextualized_predicate P)` — stronger: every `(P ...)` is *stored* in
  CxUniverse directly (its context forced there on assert, no justification). Declared
  for `genlCx`, so the context topology has one canonical home (see
  [contexts.md](contexts.md)).

Accessors: `has-prop?`, `inverse-of`, `props` (the set carrying a property). With a
context, `has-prop?` and `inverse-of` answer from the declaring sentexes that context
sees, the statement itself and, for a lifted mark, its CxUniverse copy; without one they
answer whether any sentex declares it. Which marks are lifted, and so read from every
context, is [contexts.md](contexts.md#where-a-relation-property-is-read-from)'s table.

## The predicate meta-ontology

Predicates are **reified** and classified in the genl hierarchy under `predicate`
(itself a `thing`):

- by arity — `unary_predicate` (every type, plus one-place properties like `flies`),
  `binary_predicate` (relations like `parentOf`), `ternary_predicate` (`arg`);
- by algebra — `symmetric` / `asymmetric` / `transitive` / `reflexive` / `functional`,
  each a subtype of `binary_predicate`.

**The three arity classes separate each other**, as three `(disjoint …)` pairs in CxCore.
A predicate takes one number of arguments, so a second classification is refused where it
is written (`:disjoint`) rather than stored and convicted a step later as two values in
the `functional` `(arity P N)` table. It is stated pairwise and **not** as
`(sibling_disjoint predicate)`: `predicate`'s specializations are every classification of a
relation there is, and a predicate is rightly several of those at once — `arity` is a
`binary_predicate` and an `instance_relation_predicate` — so the mark would separate pairs
that must coexist. The separation closes under `genl` like any other, so the algebraic
marks above are separated from `unary_predicate` and `ternary_predicate` along with the
`binary_predicate` they specialize.

The algebraic marks are **the classification itself** — no derived `…Predicate` twin.
Each mark is one predicate doing two jobs: `(symmetric siblingOf)` maintains the
`:symmetric` taxonomy property (canonicalization, the generic prover) **and**, through
`(genl symmetric binary_predicate)` in CxCore, *is* a membership in a `binary_predicate`
subtype. The mark is a `decontextualized_predicate`, so `(symmetric P)` is stated once and
seen KB-wide (the definitional reads and the structural ones agree). A bare KB, which
declares no lift, keeps `transitive` and the other definitional marks in their declaring
context, and the engine lifts `symmetric` and the three commutativity marks on every KB,
since they decide a sentex's stored key
([contexts.md](contexts.md#where-a-relation-property-is-read-from)). A bare KB holds the
forced-monotonic roster's engine baseline as a CxCore KB does, so an arity binding or a
`disjoint` declaration stated `:default` is held `:monotonic` on it
([nmtms.md](nmtms.md#the-forced-monotonic-roster)). Arity memberships are likewise direct (the starter loops every
subtype of `thing` into `unary_predicate`). So `isa? siblingOf symmetric`, `isa? siblingOf
binary_predicate`, and `isa? siblingOf predicate` all hold, and `isa? dog unary_predicate` /
`isa? arg ternary_predicate`.

Because the mark is a stored fact, `ask (symmetric ?p)` enumerates the declared predicates
by ordinary retrieval — the same answer `isa?` reads, from the same store, with no separate
prover (see [inference.md](inference.md)). `genl` / `genlCx` are the `closure-relations`
exception: `(transitive genl)` is stored and enumerable but held out of the `:transitive`
property machinery, so the engine keeps answering their transitivity from its own cached
closures rather than the generic prover.

## Well-formedness (`vaelii.impl.wff`)

Before storing, `assert` checks the special predicates are structurally sound:

- `genl` / `genlCx` — both arguments are types / contexts (not individuals), not
  equal, and don't create a cycle (the reverse relation must not already hold).
- `disjoint` / `disjoint_metatype` — arguments are types, and a type is not disjoint
  with itself. Two `genl`-related types may be declared disjoint: the refusal would read
  the stored edge, so the declaration is stored whichever of the two arrived first, the
  explicit arm separates the pair, and `conflicts` lists the declaration as a hard clash
  (decision 8 of [reference.md](reference.md#decisions);
  [nmtms.md](nmtms.md#declarations-over-related-types)).
- `arg` / `genlArg` — a predicate, a positive-integer position, and a type. One
  check serves both (`wff/arg-constraint-problems`): they are structurally identical
  and differ only in what they demand of the argument, which is `checks`' business.

These are structural checks; the *content* check that an argument actually reaches its
`arg` type is `checks/constraint-checks`.

## Two argument constraints

`(arg P n T)` asks argument *n* to be an **instance** of T; `(genlArg P n T)` asks
it to be a **subtype** — `arg` one level up. An `instance_relation_predicate` takes
the first, a `type_relation_predicate` the second, and the same symbol answers them
differently: `penguin` satisfies `(genlArg partType 1 tangible)` and fails
`(arg partOf 1 tangible)`, which is exactly the distinction between a claim
about a kind and a claim about a thing.

**A constraint on a predicate binds its sub-predicates' tuples.** `(genl fatherOf
parentOf)` says every `fatherOf` tuple *is* a `parentOf` tuple, and a tuple set only
narrows going down — so `(arg parentOf 1 person)` refuses `(fatherOf TheRock1 Mary)`
exactly as it refuses the same claim spelled `parentOf`. It has to: the matcher fans a
goal's functor over its subtypes, so a stored sub-predicate fact answers every
super-predicate query, and a refusal readable through only one of the two spellings
fails at the job it exists for. All three constraints descend, both readings of them do
(the refusal and the entailment), and one reader decides whose declarations speak for a
tuple — `res/constraining-predicates`, which is the predicate's own `genl` closure as
seen from the writing context. A `genl` edge the writer cannot see imports no
constraint, for the reason its memberships are read the same way.

The line, because the other direction is the mistake: **a generative property does not
descend.** `transitiveInArg`, `transitive`, `symmetric` and `reflexive` are claims *about
a relation* and stay with the predicate that carries them —
[inherit.md](inherit.md), "A declaration is read for the goal's own predicate". Dogs
being larger than cats does not make every subkind *much* larger. Refusal-side
constraints descend because tuples narrow; licences generate tuples, and generating more
of them under a predicate nobody declared preserving is manufacturing knowledge.

Which constraints apply is context-scoped for both, and so are the `genl` tests
themselves: a closure read asked from K walks only the edges K can see, so an
argument is judged against the hierarchy the writer's own ancestor set holds. Open-world
holds for both, with a global floor and a scoped one: an argument outside the
hierarchy **everywhere** is excused, except an **individual** in a `genlArg` position,
which asks for a subtype (`wff/genl-problems` refuses `genl` of an individual, so it can
never acquire the edges that would excuse it — a global probe on purpose, since a reified NAT is indistinguishable from an individual by
spelling and is minted with real `genl` edges into `CxUniverse`, which not
every writer sees); and an argument whose edges are merely *out of the writer's
sight* is excused too, since a NAF check that convicted on invisible evidence would
convict harder the less a context sees.

### Arity

A tuple is held to the length its predicate is **bound** to, and each reader decides a
tuple that breaks it ([nmtms.md](nmtms.md#nogoods-decided-at-the-reader)). Four spellings
bind, every one of them on the forced-monotonic roster and read as storage: `(arity P N)`,
an exact-class membership (`tax/exact-arity-classes`: the relation-wide `unary` /
`binary` / `ternary` and their six predicate and function specializations), a
`variable_arity` membership (`variable_arity`, `variable_arity_predicate` or
`variable_arity_function`) and `(arityMin P M)`. A membership binds by its own functor
and not through a type `genl` edge: `(transitive P)` binds no length although CxCore puts
`transitive` under `binary_predicate`, because a type edge and a membership off the roster
are defeasible, and a binding goes OUT only by retraction ([reference.md](reference.md)
decision 11). The reference model does not model arity, so it settles nothing about that
reading. Two exact lengths one reader sees bind nothing there; `(functional arity)` and
the pairwise `disjoint` of the three relation-wide classes report them. Open-world: a
predicate nothing binds takes a tuple of any length.

A tuple that breaks the binding is a **one-member nogood** whose ground is the binding. A
`:default` tuple is OUT at every reader that sees the binding, with everything resting
only on it; a `:monotonic` one is a hard clash, believed and reported in `conflicts` with
the binding under `:grounds`. Nothing refuses a wrong-length tuple, so the stored set is
the same whichever of the tuple, the binding and the edges arrived first.

`(variable_arity P)` releases a predicate from one exact length. `lessThan` has `arityMin`
two and reads a chain of any length (`(lessThan 1 2 3)` is `1 < 2 < 3`); the membership is
what says so, rather than the check carrying a roster of predicates it quietly skips. A
`variable_arity` predicate is still floored at its `arityMin`: a shorter tuple breaks it.

**A predicate that binds no length takes its super-predicates'**, and only then: a
`fatherOf` tuple is a `parentOf` tuple, so a ternary `fatherOf` fact is a ternary
`parentOf` tuple that `(binary_predicate parentOf)` says does not exist. The super-predicates
are those above it through `genl` edges stated in the reader's ancestor set. The
restriction to predicates that bind nothing is what keeps this a *check* rather than a
preserved fact: `(arity fatherOf ?n)` answers the one value somebody wrote of `fatherOf`,
and nothing where nobody wrote one. Supers that disagree bind nothing, and a
`variable_arity` super releases the inheritance for the reason it releases the predicate
carrying it.

**A predicate that binds a length is held to match its super-predicates'.** Two
predicates a `genl` edge relates whose own exact lengths differ are a nogood of their
bindings, `:arity-descension`, read wherever both bindings and the edges between them are
visible, and neither end `variable_arity`. Every member is on the roster, so the nogood is
a hard clash: all of it stays believed, and `conflicts` reports it. Neither the edge nor a
declaration is refused, in either arrival order. The tuple rule still reads a predicate's
own binding first, so a `fatherOf` declared ternary under a binary `parentOf` holds its
ternary tuples, and the report names the pair.

A specialization therefore does not carry a signature of its own. This is the one point
where an arity constraint is stricter than the argument constraints beside it, and the
reason is that a length cannot be narrowed: `arg` on a sub-predicate *adds* to what the
super demands of a tuple, while a second length says the two tuple sets are one set and
are shaped differently. Own bindings only, on both sides; supers that disagree with *each
other* are not a pair, since they are not genl-related and the sub takes nothing from
them.

### The declarations are checked against each other

`checks/declaration-problem` runs on an `arg` / `genlArg` sentence itself, not on
the content it constrains, and refuses two ways one can contradict what the KB
already says about its predicate:

- **A position the predicate does not have** — `(arg parentOf 5 animal)` where
  `parentOf` is declared binary. The constraint would never fire, so it reads as
  enforced while enforcing nothing. The arity comes from `(arity P N)` or from a
  `unary_predicate` / `binary_predicate` / `ternary_predicate` membership; the CxCore
  rules derive each from the other, so either spelling is enough, and both are read
  because a `{:chain? false}` assert has only what was written. **`variable_arity`
  releases this arm too**: such a predicate reads a tuple of any length from its declared
  arity upward, so a position past that length is one its tuples really do reach and a
  constraint on it fires on the tuples long enough to have it — refusing the declaration
  while the same KB admits those very facts is the reading no arrival order makes
  coherent. The release is read off the predicate's **own** memberships, since
  `checks/inherited-arity` already declines to bind when a super carries the mark.
- **A constraint disagreeing with the predicate's `relation_kind`** — `genlArg` on an
  `instance_relation_predicate`, or `arg` on a `type_relation_predicate`.

**Both constraints on one position is not one of them**, and it is the case worth naming
because the opposite reads plausible: one asks the argument to be an instance of a type
and the other a subtype of a type, and a *type* is routinely both. `(arg P 2
unary_predicate)` beside `(genlArg P 2 animal)` says the slot holds a kind of animal, and
`dog` satisfies it — an instance of `unary_predicate`, a subtype of `animal`, which is how a
converted ontology ordinarily declares a type-valued position. The two checks are
independent and each is open-world on its own, so declaring both narrows the slot rather
than emptying it.

Each arm needs a declaration to contradict, so a predicate the KB has said nothing
about stays unconstrained. `(functional arity)` closes the matching hole on the
declarations themselves: a second, different arity for one predicate is a clash rather
than a second belief, and since two numbers can never merge it is a nogood rather than
an inferred equality.

`arg` reads **two ways**: as a *constraint* when asserting (`checks/args-problem`
rejects a wrongly-typed argument), and as an *inference* when querying — the
`ArgTypeProver` (see [inference.md](inference.md)) concludes an individual's type
from the arg-constrained position it fills, so a thing's type can follow from
how it is used, not only from a stored membership.

### And against the variables of a rule

`args-problem` reads a **ground** argument. Every argument of a rule is a variable, so
it passes over all of them vacuously — and a rule whose variable-binding chain feeds an
impossible term into a position is stored, fires, and is then convicted one conclusion
at a time by a complaint naming the conclusion and never the rule that wrote it.

A variable is one term standing in several positions at once, so
`checks/check-variable-constraints!` holds the positions to **each other** before the
rule is stored — on both storage entry points and in `check`, since it rides `check-rule!`.
It refuses `:arg-variable`:

```clojure
(v/check kb '(implies (comment ?x ?string) (genl ?x ?string)) 'CxUniverse)
;; [{:type :arg-variable :variable ?string :expected [string unary_predicate]
;;   :message "arg constraint: ?string must be a string (arg 2 of comment)
;;             and a type (arg 2 of genl, a type_relation_predicate), and the two types
;;             are disjoint"}]
```

`(implies (arg ?pred ?n ?kind) (genl ?pred ?kind))` is the structure that must *pass*, and
does: `?kind` is asked for a kind at both ends.

**A type-level position asks for a `unary_predicate`**, which is what makes the two
demands comparable at all — `disjoint` separates *memberships*, and a subtype demand is
not one until it is read as the membership every type carries. A position is type-level
when a `genlArg` names it **or** when its predicate is a `type_relation_predicate`, the
mark saying that of every position at once; that second half is how `genl`'s second
argument is constrained, since it deliberately carries no declaration of its own
(CxCore says why).

Four restrictions keep the arm to what it can actually prove:

- **Instance demand against instance demand only.** Two *subtype* demands are left
  alone: a type below two disjoint types is empty, not impossible, and nothing else in
  the KB refuses an empty type.
- **Positive literals only.** A negated antecedent says the variable does *not* fill
  that position, so `(implies (and (dog ?x) (not (plant ?x))) …)` is saying exactly what
  its author meant; an existential is skipped because its variables are local.
- **Declared disjointness only**, so the arm stays as open-world as the ground one. The
  value kinds carry the declaration that makes the case above bite — each is an
  `unrepresented_term`, and `(disjoint unrepresented_term relation)` in CxCore
  separates it from every predicate, text and a number each being a thing no relation
  is, and `number` carrying `integer` with it.
  `symbol` deliberately carries neither: a name is exactly how a predicate is written, so
  the disjointness would be false. `(disjoint function predicate)` is derived from
  CxCore's `(partition relation function truth_valued_relation)` and `(partition
  truth_valued_relation logical_constant predicate)` rather than stated; it is what
  `function`'s own comment has always said in prose, and it is what refuses
  `(implies (result ?f ?t) (genl ?f ?t))`: `?f` is asked for a function at one end and
  a kind at the other.
- **Two constraint kinds of the four**, and the other two are a *result* rather than a
  scope decision. `arg` and `genlArg` are read; `quotedArg` and `interArg` are not,
  because each pairing has a binding both ends accept — refusing the rule would refuse
  one that works. Both `quotedArg` pairings admit a **compound**, the one thing
  `value-kind` declines to answer for; and `interArg`'s trigger is a
  *demand*, not a fact — `(arg P i T)` does not make argument `i` a `T`, since an
  unclassified term satisfies it vacuously, so no rule's own bindings entail the trigger.
  For the same reason there is no reading of `arg` against `genlArg` sharper than the
  `unary_predicate` mapping above: a term may be an instance of one type and a subtype of
  another at once, and the meta-ontology depends on it. Each of those has a witness in
  `rule_variable_arg_test`, so widening the arm turns one red first.

## What is cached, what is not, and why

- **A transitive predicate's closure is not held as a *relation*, but the answer is
  held.** The distinction from the `genl`/`genlCx` closures above is maintenance:
  those are adjacency the engine keeps current through every edge change, which is what
  earns them a `:gen` and a repair path. Nothing about a declared-transitive `P` is
  maintained. `reach` (in `vaelii.impl.provers`) walks the believed facts, and what it
  finds is **cached per `[direction predicate node context belief-mode]` on the KB** and dropped —
  not repaired — the moment anything moves.

  Two layers, at two scopes, and they are not alternatives:

  | | holds | scope | retired by |
  |---|---|---|---|
  | `observe/*reach-memo*` | one node's neighbours | one search step | going out of scope |
  | `:closure-answers` | one whole reach | the KB | the change clock |

  The KB's `literal-cache` is **not** a third: a walk visits each node once, so it asks
  each neighbour literal once and leaves that cache nothing to serve, while its insertion
  per node would clear the whole cache part-way through. The neighbour probes read with
  `res/matches-visible`'s `cached?` false — [caches.md](caches.md) states the rule a scan
  follows.

  The clock is the whole invalidation story, and it is what makes `:closure-answers` follow
  **belief**: a relabel moves it, so a defeated edge retires the closure that crossed it
  without anything having to know which entry the edge was in. It is also what makes a
  scope that *writes while it reads* — forward chaining, whose own conclusions move the
  clock under it — fill the cache with nothing rather than with something stale, the
  discipline `literal-cache/lookup` spells out.

  The bound counts **members**, not entries, because an entry is a whole reach: ten
  entries can be ten members or a million, so a bound on entries would be a bound on
  nothing. A reach larger than the bound is never stored — it is the case the bound
  exists for — and a total that reaches it drops the map wholesale.

  An **open-argument** ask fills it; a **closed** goal reads it without filling it, since
  computing a closure to store would charge a two-hop question for the whole extent and
  lose `reaches?`'s early exit. Measured (`lein bench-walk`): a second identical ask over
  an unmutated KB costs 0.10–0.14× the first on a 2,000- to 8,000-node chain and fetches
  no records. Nothing under it could answer that repeat anyway: the neighbour probes go
  with `res/matches-visible`'s `cached?` false, so a walk neither consults the KB's solution
  cache nor fills it — a walk asks each node once, and the entries it would spend, one
  per node, would clear that cache under a reader who does re-ask. Note that genl
  changes are **not** a dependency of the walk itself: subtype fan-out applies only to
  unary goals, and `(P x y)` is binary.
- **Metatype membership is cached rather than stored**, so `disjointness-test` scans
  the marked metatypes once per asking type, intersecting each one's members against
  that type's closure. Metatypes are few and the scan is hoisted out of the
  per-candidate loop, so it costs one pass over a short list.
- **A contradiction is rejected, not analysed.** There is no assumption retraction and
  no ATMS: the engine reports the clash and leaves both sides where they are.

### What each constraint does in each arrival order

The declarations differ in how far back they reach, and the differences are principled
rather than incidental — so the table is the reference, and the two cells that read
"nothing" each have a reason below it.

**Read the table as being about *storage*, not belief.** Where a cell says "refuses", the
fact is not stored; where it says "stores" or "reaches back", the fact is stored and then
weighed or reported. A clash that names its other members is stored in every order, so
its rows store the same content whichever half arrived first, and each reader that sees
the clash whole decides it, the settle deciding the clashes whose members' contexts are
one or comparable ([nmtms.md](nmtms.md#nogoods-decided-at-the-reader)).

| declaration | declaration first | facts first | why |
|---|---|---|---|
| `disjoint` | stores the membership; a nogood | same — the next read at each reader decides it, and the declaration reads no membership | two memberships to weigh |
| `disjoint_metatype` | same | same | the members separate each other |
| `genl` / `genlCx` | same | same | closes a separation over content already stored |
| `covering` / `partition`, over a refuted cover | stores the sentence; a nogood | same, over the terms holding a denial of a part or of a supertype of one | the membership and the negations to weigh |
| `functional` | stores the value; a nogood | reaches back as a nogood, over the spec subtree of the predicate it names and not that predicate alone | two values to weigh |
| `asymmetric` | same | same | the converse is the second side |
| `irreflexive`, and `anti_symmetric` over a converse that does not merge | stores the tuple; a nogood each reader decides | same — the next read at each reader decides it, and a `genl` edge below the marked predicate or a `genlCx` edge into the tuple's sight does the same | the tuple's own arguments find the nogood |
| an arity binding: `arity`, an exact-arity class, `variable_arity`, `arityMin` | stores the tuple; a nogood each reader decides | same — and a `genl` edge that binds a sub-predicate's length, or a `genlCx` edge that brings a binding into a tuple's sight, does the same | the tuple's own length finds the nogood |
| `arg` / `genlArg` / `quotedArg` / `interArg`, the covering `args` / `argAndRest` and the homogeneity `interArgs` / `interArgAndRest` | refuses | **nothing** — for the conditional forms, whichever of the declaration, the trigger's type or the target's type arrives last | convicted by an absence; no second sentex at all |
| a predicate-level `genl` edge, under an *argument* constraint above it | refuses what follows | **nothing** — the entailment reaches back, the refusal does not | the family's non-reach, one ingredient further out |
| a predicate-level `genl` edge, under a `functional` / `asymmetric` mark above it | stores what follows and weighs it on the marked predicate's terms — `tax/props-over` reads the mark at every predicate above the sentence's own functor | the edge is admitted, and it reaches back over the sub's stored facts: a nogood, plus the merges a `functional` mark now licenses (`special/equate-under-edge`) | the sub's tuples *are* the super's, so a clash among them is the super's |
| a predicate-level `genl` edge, across two bound **arities** | stores the edge; a hard clash of the two bindings each reader reads | same | every member is on the roster |

**A row's two halves answer one question about one KB, so they answer it in one
vocabulary.** Both are true statements either way, which is what makes a disagreement
between them expensive: a reader who meets one and greps for the other finds nothing, and
a reader who meets both concludes there are two problems. So the halves owe each other the
predicate blamed, whether the constraint was inherited or declared outright, and which
stored sentex convicted — `entry_point_and_report_test` is the roster over these rows, the cells
reading "nothing" included.

**`arg` and its family have no retroactive reach.** A constraint arriving after a fact
whose argument is the wrong type does not reach back over it. It is the one family that
**cannot** become a nogood — the conviction rests on the *absence* of a path to the
constraint type, which is open-world negation as failure, so there is no second sentex to
weigh and nothing for a defeat class to compare — and a retroactive pass over it would
have to decide whether silence about a pre-existing argument's type is a violation or
merely silence. That is a policy question nobody has answered, and answering it by
accident in a sweep would quietly turn an open-world check into a closed-world one.

**`quotedArg` takes the same non-reach, and half the argument reaches it.** The mention
twin convicts the term as it is *written*, and every term has a syntactic kind, so there
is no argument whose type has merely not arrived yet and no "silence or violation" for a
sweep to decide. The other half does carry over. `(quotedArg pAgeOf 2 string)` convicts
`(pAgeOf Bob 5)` because no `genl` path runs from `integer` to `string`, which is the
absence `arg` rests on read over the syntactic lattice instead of over an asserted type.
A retroactive report would therefore name a conviction a later edge can lift.
`entry_point_and_report_test` pins the cell rather than leaving it inherited from the
three spellings beside it.

**The descension makes it a third ingredient rather than a second**, and the non-reach
covers that one too. `(fatherOf TheRock1 Mary)` stored, `(arg parentOf 1 person)`
stored, then `(genl fatherOf parentOf)`: the edge is admitted, the fact the edge brings
under `parentOf`'s constraint stays stored and believed, no arg violation is reported, and the next such claim is
refused. That is the same reading the row above it takes, one ingredient further out —
the conviction still rests on an absence, so there is still no pair to weigh. What *does*
reach back is the entailment, which is a different question and answered in
[argtypes.md](argtypes.md): a minted type is justified content, so it has to exist in
every arrival order or belief would depend on which. Where `TheRock1` holds a type
disjoint from `person`, the entailment's `(person TheRock1)` is placed and forms a nogood
with that membership, as a rule's conclusion does.

**A declaration the arity strands is a census finding, not a ledger one.** `(arg
parentOf 3 person)` is admitted while `parentOf` has no declared length, because the
highest position a declaration names is a lower bound on the arity rather than a claim
about it. When a length arrives — declared of the predicate, or inherited through a
`genl` edge — the declaration is left constraining a position the predicate provably does
not have, and the entry point refuses the identical sentence one line later. A `variable_arity`
predicate is the length that is not the last word, and it releases both halves at once:
its tuples reach any length from the declared one upward, so a position past that length
is one they really do have, and nothing of such a predicate's is stranded or refused
however high the position. It is not refused
retroactively, for the reason everything else in this section is not: that would make the
binding's arrival order decide. Nor is it a nogood: a wrong-length *fact* is a claim a
reader believes or withdraws, while a stranded declaration is inert — it constrains
nothing, refuses nothing, mints nothing — and reads the same an hour later, so it belongs
to `kb-quality`, whose `:declarations` reading names them.

`interArg` inherits that argument verbatim, and shows the other side of the same gap. A
conditional constraint has **three** ingredients, not two — the fact, the declaration, and
the trigger argument's type — and it is the *third* arriving last that nothing reaches:
`(eats Rex Chunk)` and `(interArg eats 1 carnivore 2 meat)` both stored, then
`(carnivore Rex)`, and the violation `Chunk` now commits goes unreported. `arg` has
exactly this, less visibly: an argument that acquires its first type after the fact was
admitted was excused by open-world when it was written and is not re-examined. Both are the
same non-reach, and closing either means answering the policy question above.

