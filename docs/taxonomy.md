# Taxonomy: types, genl, and disjointness

- **Covers:** how the `genl` type hierarchy is cached and queried, how `disjoint` /
  `disjoint_metatype` are enforced, and how `arg` / `genlArg` constrain arguments as a
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

The shipped ontology states the global lifting rule this way today in
`CxCore.txt`, not `genl`'s transitivity: `genl` carries its account in the
`comment` on the predicate instead, where the closure is described rather than written
as a sentence.

## genl: the type hierarchy

`(genl Sub Super)` — every `Sub` is a `Super`. Types are unary predicates, rooted
at `thing`. We cache the reflexive-transitive closure both ways:

- `genls tax t context` — supertypes of `t`, incl. `t` (up-closure).
- `specs tax t context` — subtypes of `t`, incl. `t` (down-closure).
- `genl? tax sub super context`.

Each has a `-global` twin — `genls-global tax t`, `specs-global`, `genl?-global`, and
`context-up-global` over on the `genlCx` side — which walks **every** active edge rather
than the edges a context sees. The two are spelled apart rather than distinguished by
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
policy is therefore relation-wide even though the current exact `arity` table remains
predicate-typed.

`fixed_arity` and `variable_arity` classify the two policies, with predicate and
function specializations for each. `arityMin` states the lower bound of a
variable-arity relation; every exact `(arity R N)` entails `(arityMin R N)`. Prefer
variable arity for a repeatable, homogeneously typed argument role. A relation may
explicitly define a bounded optional tail instead, as `functionCorrespondingPredicate`
does.

`at_least_binary_relation` and `at_least_ternary_relation` are generic derived
classifications over `arityMin`; callers can conjoin them with `predicate` or `function`
instead of maintaining duplicate predicate/function classes. `admitsArgnum` names the
separate question of whether one positive argument position exists. No WFF/query reader
currently consumes it, and no parallel finite position roster is inferred.

No disjointness declaration currently separates the fixed and variable classes, and
exact `arity` does not derive `fixed_arity`. This lets direct generic variable markers
coexist with the new specializations without classifying the same relation both ways.

## The closures are derived state

A cached closure is an optimization, and an optimization that disagrees with the
data is a bug. The source of truth for an edge is **the set of believed sentexes
asserting it**, so each relation carries that set explicitly:

```clojure
{:support {[dog animal] #{41 88}}   ; every sentex asserting the edge
 :edges   #{[dog animal]}           ; the ACTIVE edges — those with a believed supporter
 :fwd {dog #{animal}}               ; direct up-adjacency (a genl b)
 :rev {animal #{dog}}               ; direct down-adjacency
 :nodes #{dog animal}               ; every node in an active edge
 :depth {dog 1 animal 0}            ; topological potential for O(1) reachability rejects
 :scc {}                            ; node -> component, for the nodes in a cycle
 :gen 7}                            ; bumped on every edge change; retires the read memo
```

The closure itself — `genls` (up) / `specs` (down) — is **not** stored. It is
answered on demand by a reflexive-transitive `reach` over `:fwd` / `:rev`, and
read-memoized per `:gen` in a side atom.

Three properties follow, each of which a cache is easy to get wrong:

- **Belief.** A defeated `(genl dog animal)` leaves the closure. Matching is
  belief-sensitive everywhere else in the engine — a defeated sentex stays stored
  but does not match — so a taxonomy that exempts itself lets `isa?` answer through
  an edge nothing believes. `refresh-beliefs` reconciles at the end of every
  `settle`, which is the only point a supporter's label flips without a sentex being
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

`recover` calls `clear-relations!` — which empties all ten caches — before rebuilding.
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
| `disjoint` `disjoint_metatype` `sibling_disjoint` `siblingDisjointException` | disjointness, the metatype and sibling marks, and the exemption | `:derived?` |
| `arity` `inverse` | the arity and inverse caches | `:derived?` |
| `transitive` `symmetric` `asymmetric` `reflexive` `functional` `forced_decontextualized_predicate` `abducible_predicate` `closed_extent_predicate` `reifiable_function` `unreifiable_function` | the predicate-metadata marks | `:derived?` |
| `rewriteOf` `sameAs` `equals` | the equality partition, and migration | by name — the arm's return value is the twins and the violations, which `:derived?` would discard ([equality.md](equality.md)) |
| `arg` `genlArg` `interArg` | the roster of predicates some declaration of that kind names (`:declares-arg-isa` / `:declares-arg-genl` / `:declares-inter-arg-isa`), and the declarations themselves read back through the index per query | `:derived?` — the roster is what lets the descension ask *whose* declarations bind a tuple without an index probe per super-predicate |
| `transitiveInArg` `transitiveInArgInverse` `functionCorrespondingPredicate` | none — read back through the index per query | nothing to reach |
| `different` `unknown` `thereExists`, the five aggregates | none — never stored | nothing to reach: `wff` refuses the conclusion on the derivation path exactly as it refuses the assertion |

**Two conclusions reach their cache only once a restart replays them**, and both are
stated here rather than left to be found:

- **`decontextualized_predicate`.** Its arm marks the predicate *and* runs an O(extent)
  retroactive lift whose copies are chaining seeds, which the `:derived?` walk would
  throw away — so a derived declaration would lift half of what an asserted one lifts.
  A rule concluding it therefore leaves the mark unset until a restart replays it.
- **A disjoint metatype's own members.** `(animal_species dog)` is recorded by the
  structural arm rather than by a table entry — the functor is the metatype, which is
  data and not vocabulary — and the derivation path runs no structural arm. A rule
  concluding a membership therefore separates nothing until a restart replays it, though
  a rule concluding the metatype *mark* over asserted members does.

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
  Every `settle` path names a region instead, and the supersession pass *widens* its own
  by hand rather than dropping it, because a supersession flip is a belief change with no
  relabel to record it. The width of that by-hand widening is the **whole standing
  supersession set**, so on a KB holding N live merges every settle hands the reconcile an
  Ω(N) region — the reconcile stays proportional to what it was handed, but what it is
  handed there grows with the merges standing, not with the change.
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
  without it, because it passes the honest flip set. Depending on the width instead would
  make correctness rest on something nothing states and nothing tests, and the failure is
  a silent one.

**The flat caches below work the same way, off the same reasoning.** `:cache-handle-keys`
is the transpose of `:cache-support` and `:cache-dirty` is the twin of `:dirty`, with one
difference that is about the caches rather than about the scoping: the index is a
**multimap**, `{handle #{[kind key]}}`. A `genl` sentence names one edge and the writers
here name one entry per sentence too, but nothing in the structure says so and removal is
per-(handle, key) — a 1:1 index would have the first `support-drop` take a handle out from
under an entry the same sentex still supports, which is indistinguishable from a stale cache rather than as
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
  see below). The O(1) is conditioned on an empty `:scc`: the lift moves whole
  components, and finding a component's members reads the `:scc` map, so it holds
  always for `genl` (cycles are refused there) and for `genlCx` only while no
  context cycle stands — with cyclic contexts in the map, an insert pays a walk of
  the cyclic population. The lift moves whole **components**, since the potential ranks the
  condensation: a member raised alone would sit above its own mates, each of which then
  forces the next one round the cycle. No closure is touched. A redundant re-assert of
  an already-active edge is a no-op.
- **Deletion** drops the edge from the adjacency and prunes any node left with no edge
  (so `types` / `contexts` match a from-scratch build). Depths are left as loose upper
  bounds: a deletion only relaxes the ordering, so the `edge ⇒ depth` invariant
  survives untouched, and a loose depth only costs an occasional un-pruned walk step,
  never a wrong answer.
- **Reads** compute the reflexive-transitive `reach` over `:fwd` / `:rev`, memoized in
  a side atom stamped with the relation's `:gen`. Every edge change bumps `:gen`, which
  invalidates the whole memo for that relation without touching it — a read simply sees
  a gen mismatch and recomputes. A repeat read on a shallow hierarchy is O(1); a deep
  one is never materialized. `genl?` / `sees?` skip the closure entirely: they answer
  reachability with a `:depth`-pruned early-exit walk (`depth[src] ≤ depth[tgt]` rejects
  a pair in O(1)), which is what keeps the per-assert `wff` cycle check flat on a deep
  load.
- A **cycle** is refused for `genl` and admitted for `genlCx`, and the potential is
  what makes both work. `wff` (assert path) and `special/wff-violation` (derivation path)
  refuse a `genl` edge that would close one, because a type cycle claims two types are
  coextensive — a claim about *terms*, which is the equality partition's job, and which
  would make a `disjoint` pair disjoint from itself. A **context** cycle claims only that
  the two contexts see each other, which is a thing `genlMt` says (OpenCyc states 49
  of them, BaseKB's own component among them), so it is admitted and the taxonomy holds
  it.
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

The filter keys on `vis = up(K) ∩ ctxs`, where `ctxs` is the relation's context
census (`:ctx-counts`): every edge's context set is a subset of the census, so two
readers with the same `vis` induce the identical filtered edge set — `vis` is the
memo key, interned per `[genlCx-gen ctxs-gen]` (`:vis-index`), and the scoped
walk memoizes one level deeper under it, bounded by `*scoped-memo-budget*` distinct
vissets per relation (the census on the OpenCyc import [kbs.md](kbs.md) is the route to:
~450 asserting contexts, ~560 distinct vissets across ~13k readers). Depth pruning
survives unchanged — the potential holds over
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
component is a reason to keep walking and never an answer. (A `genl` cycle is refused at
assert time and reachable anyway: defeat an edge, assert its reverse — the check reads
the *active* adjacency, which no longer holds the defeated one — then revive the first.
`genlCx` admits cycles outright.)

The **`genlCx` closure itself is the stated exception and stays global**:
visibility scoped by visibility would be circular, every `genlCx` edge is forced
universal, and the interning above rests on it. So do the identity, storage, trigger,
and stratification reads. The scoped-or-not split per check, and the exposure of clashes
only a descendant can see whole, are docs/contexts.md's story.

### The global readers, and who may use one

Every one of those reads goes through a reader whose **name** says it is global —
`genls-global`, `specs-global`, `genl?-global`, `context-up-global` — rather than through
a shorter arity of the scoped one. The reason is that the two agree far more often than
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
| assert-time refusals (`wff`, `checks`) | a refusal is a claim about the KB: a cycle refused when asked from one context and allowed from another is a coin toss, not a rule |
| the forward join and the trigger keys (`rules/trigger-keys`, `chain`, `inherit/moved-predicates`, `vantage`) | a firing is placed in a context the join decides, so the candidate fan cannot be scoped by one — the narrowing happens at placement |
| the exception re-check triggers (`special`) | a trigger over-approximates in the direction the answer is: a declaration this edge cannot see still qualifies a rule in some context that can, and a missed trigger is a wrong belief where a spare one is a query |
| settle's candidate discovery | an over-approximated candidate merely checks and yields nothing; the arbitration that follows is scoped |
| `resolution`'s exception index and `hidden-fn` | the visibility filter cannot be scoped by the filter it is itself derived from |
| `quality/taxonomy-coverage` | a report on the whole taxonomy has no vantage to read from |
| `quality/clash-partners` | a rule pair is decided from a common descendant of the two rules' contexts, a vantage belonging to neither, so the candidate fan cannot be scoped by either |

One caller reads **both** on purpose: `settle/genl-view` compares `genls-global` with the
scoped answer, because where the two are equal every asker between them reads the same set
and an unchanged reading is unchanged for all of them at once.

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
`[kind key]` — to the six flat caches too: `disjoint`, the disjoint metatypes and their
members, the `sibling_disjoint` marks and their exemptions, the predicate properties
(`transitive`/`symmetric`/`asymmetric`/`reflexive`/`functional`), `inverse`, and the
declared `arity`. Only `genlCx` is forced-decontextualized, so only it is guaranteed one
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

The depth potential is not the only thing a batch of `genl` edges is quadratic in. Three
passes read the hierarchy *per arriving edge*, and each one's memoization is keyed on
the node a walk **began** at — so nested roots share nothing and n edges cost n²/2. The
edges arrive nested because that is what a hierarchy is, and what a load writes.

- **The retroactive arity report expands the union, not the sum.**
  `settle/report-arity-reach!` takes its extent through `tax/specs-of-all`, which seeds one
  traversal with every arriving edge's root under one `seen`. Expanding each root's spec
  subtree separately instead costs 1,024 chained edges ~250 ms — none of it bounded, since
  the instance budget counts facts examined and this examines none — where the shared walk
  takes 512 edges from ~60 ms to ~1, growth from 59.5× to 7.5–11.3× per doubling. `lein
  perf`'s `arity-reach-batch-roots` pins it at 25.0.
- **The `functional` and `asymmetric` marks are read down, once per pass.** Four gates
  ask the one question — is a mark at or above this predicate: `could-clash?` per
  candidate sentex, `declaration-implicates` per arriving edge, and the cross-context
  exposure pass's region filter and `genl` arm per binary fact. Answering each ask with its
  own `props-over` — `genls(f)` and two sets built off it — is a walk per asker.
  `settle/clash-marked-below` walks `specs-of-all` over the **marked roster** instead, once
  per pass behind a `delay`, with the gates asking set membership of the result: 1,000
  askers over a 1,000-predicate chain go from ~210 ms to ~1, and 2,000 from over a second
  to ~3, with no closure memo behind it. Warm, it is ~20 ms to ~1 and ~150 to ~2. The
  roster reading grows with the chain where the per-asker one grows with its square, and the
  deferred batch *around* it moves 1.04–1.21×, the marks being a small share of a pass that
  also pairs and reports.

  What that gives up is the form a hybrid would win — a pass carrying a single trigger
  under a mark near the root of a wide hierarchy. The shipped ontology is not it,
  declaring eleven marked predicates with no sub-predicate between them.
- **The two `special` arms decide before reading the subtree.** `equate-under-edge` reads
  `tax/props` once before it looks at anything; ungated, every `genl` write on every KB
  materializes the subtree's extent to discover nothing was functional. `entail-under-edge`
  is gated on the KB storing an argument constraint. Both take their extent through one
  `subtree-sentexes`, filtered by index cardinality first. No curve moves —
  `subsumption-seeds` walks the same subtree and must.

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
  `(sibling_disjoint C)` sentex), and `disjoint?` reads `C`'s specializations off `specs`
  the way the metatype arm reads its members. So nothing quadratic is stored, dropping
  the mark releases every pair at once, and a specialization added later — an `(A C)`
  membership is a mistake, but a `(genl A C)` edge is the shape — is separated the
  moment it is believed.

  The genl-relatedness exception is essential and not a special case: a type and its
  own supertype are both specializations of `C`, so without it the mark would separate
  a subtype from the very type it refines. It is read over the **whole** KB, not the
  reader's context ancestor set — the same global test `(disjoint a b)` applies when it refuses
  a genl-related pair as ill-formed — which is what keeps the sibling arm monotone on
  visibility, so a descendant context never separates a pair the whole edge set knows
  overlaps.

  **Covering is out of scope.** `sibling_disjoint` says the specializations do not
  *overlap*; it does not say they *exhaust* `C`. There is no declaration that an
  instance of `C` must belong to one of its specializations, so a bare `C` with no
  further membership violates nothing. Disjointness is the half a truth-maintained KB
  can refuse a write against; exhaustiveness would be a closed-world claim over an
  open-world extent.
- `(siblingDisjointException X Y)` — an escape hatch exempting the one pair `X`, `Y` that
  a `sibling_disjoint` mark (or a `disjoint_metatype`) would otherwise force disjoint. It is
  keyed as an unordered pair exactly like `disjoint` (`:sib-exception-index`,
  reference-counted on the `(siblingDisjointException X Y)` sentex) and read by
  `disjointness-test` as one map lookup behind the `genl-related?` guard the sibling and
  metatype arms already carry; the explicit-`disjoint` arm is deliberately *not* exempted,
  since `(disjoint X Y)` is a hard assertion you retract to undo. A Braille reading, both a
  `reading` and a `touch_perception`, is the case it exists for.

  **Pair-local, and it does not leak to subtypes.** The exemption spares `X`, `Y` alone:
  each stays disjoint from the parent's *other* specializations, and an exception on
  `(X, Y)` leaves `(X', Y)` disjoint for a subtype `X'` of `X`. That falls out for free —
  each read tests the *exact* pair drawn from the two `genl` closures, so nothing wider is
  ever spared.

  **Read globally, not through the reader's ancestor set**, exactly as `genl-related?` is. An
  exception *removes* a clash, so a context-scoped exception would let a more-specific
  reader see *fewer* clashes than the KB holds — the non-monotone direction `disjoint?`
  forbids. The sentex still carries a context and retracts / rebuilds normally; only its
  read is unscoped. This is the deliberate divergence from Cyc's per-Mt exceptions, and in
  fact more faithful to disjointness — Cyc has no scoped variant. Asserting an exception
  releases a standing clash and retracting one re-arms the pair (`clash-vocabulary`
  compares the exception set, so its move re-derives every known pair); an exception
  present *ab initio* whose pair therefore never entered the clash set is re-armed on
  retract by the settle's own sweep off `:sib-exc-dirty`.

**All three separating mechanisms — `disjoint`, `disjoint_metatype` and `sibling_disjoint` — separate any term, not only individuals.** `checks/checkable-term?`
admits every non-variable symbol, so the predicate meta-ontology is enforced the same
way the domain is: `(relation_kind …)` is a `disjoint_metatype` over
`instance_relation_predicate` and `type_relation_predicate`, and a predicate declared both
is refused exactly as `Muffet` being both a `dog` and a `cat` is. The same widening makes
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
alone, so `settle` asks each candidate's question from the maximal common descendant of
its context and each context holding a sentex it could pair with, beside its own
(`settle/clash-askers`, and [nmtms.md](nmtms.md) for what the one-sided answer cost).
Every one of those asks is the same scoped read from a context that already sees both
halves.

### What a declaration reaches back over

A declaration changes what already-stored content *means*, so the settle that admits
one re-examines the content written before it — or the KB would answer differently
depending on whether the separation or the memberships were written first, which is
the invariant [nmtms.md](nmtms.md) opens with. Eight sentence shapes reach back:
`disjoint`, `disjoint_metatype`, `sibling_disjoint`, a new `(M T)` member of a metatype,
`genl`, `genlCx`, and (for the nogood path) `functional` and `asymmetric`.

The reach is **two questions**, and keeping them apart is what makes a bounded sweep
buy real coverage:

- **what to enumerate** — one record fetch per instance below the declared types,
  which on a real ontology is the *extent* rather than the moved region. This is what
  `tax/*exposure-instance-budget*` bounds.
- **what an enumerated term is a candidate for** — a `believed-memberships` read, a
  pairwise disjointness probe, and behind that a witness enumeration. Far more
  expensive per term, and needed only for terms that could really be convicted.

The extent below one side of a separation is **not** the candidate set. A clash needs
a membership from *each* side, so the terms `(disjoint A B)` implicates are those
holding a spec of A **and** a spec of B — an intersection, answered by enumerating the
cheaper side (sized off `count-with-functor` over the spec closures, so choosing costs
no walk) and probing each of its terms against the other side's closure through the
argument-1 root. `settle/two-sided-reach` is that rule, and the metatype-member route
`(M T)` is the same thing between `T` and `M`'s other members. A side whose spec
closure is **empty** reaches nobody at all — which is what a separation naming a
non-symbol says, and OpenCyc declares thousands against reified NATs like `(AbnormalFn
chromosome)`. That is stated in the code rather than left to the sizing arithmetic
picking the empty side, because what makes it true lives two functions away:
`believed-memberships` reads a clash half only from a sentence whose functor is a
symbol, so a compound-functor membership could not be one end of a pair even if it
were enumerated.

A bound decides *which* candidates get looked at, so ordering matters — and it is applied
at the **trigger** level and not below it. The moved region is walked in content order
(`settle/content-order`), which a region is small enough to afford. The enumerations
under a trigger — the down-closure (`settle/instances-below`), the context ancestor set
(`settle/members-in-ancestors`), a predicate's posting list — are **lazy and unsorted**, so a
budgeted consumer realizes only its prefix. Sorting to choose that prefix would force the
whole extent, which is the cost the cap was added to refuse, and the perf gate says so:
sorting the ancestor set took `retract-context-cycle-scaling` from 0.08 to 0.28 ms/op at 2048
contexts, since a context cycle makes the ancestor set the whole graph.

So a cut past the budget reaches a prefix the index chose. The `functional` /
`asymmetric` route is where that is widest, since a declaration there reaches every
predicate beneath the one it names: the spec subtree is walked in content order, so which
predicates a bounded pass reaches is a function of the vocabulary, while within a
predicate the prefix is still the posting list's own. What it costs is bounded: the pairs not reached
are **undecided this settle** rather than decided the other way — discovery accumulates in
`:clashes` and is re-examined every settle after, and the standing whole-KB question
(`core/exposed-clashes`) takes no budget at all. Arrival order can move *when* a pair is
arbitrated, not which way it goes.

**One cap in the engine is the exception to that last sentence**, and it is not one of
settle's: `special/equate-under-context-edge`'s merge-deriving sweep takes a handle-ordered
prefix of the ancestor set a `genlCx` edge widens, and nothing re-triggers on an edge that has
already landed. So past *that* cap arrival order decides whether a merge is derived at
all, not only when. It is bounded by the same dial, reported on every cut
(`:context-edge-exposure-truncated`), and exact below the cap; the residual is stated in
full in [equality.md](equality.md).

**No cut is silent.** A bounded sweep that read as full coverage is the failure every
half guards against, so each files one entry per settle: `:exposure-truncated` from
`settle/expose-clashes!`, `:arbitration-truncated` from
`settle/report-arbitration-cut!`, and `:arity-truncated` from
`settle/report-arity-reach!` — the first two carrying `:triggers` `:sample` `:budget`
`:message`, the third `:predicates` in place of `:triggers`, because its budget is spent
walking a subtree of predicates rather than a list of triggers. A fourth,
`:partner-sweep-truncated`, comes from the one bounded read with no settle-wide budget to
debit: `settle/partner-contexts` runs at the assert entry point as well as inside a pass, so its
unnarrowed `functionalInArg` arm (a declared position covering the whole tuple, leaving no
argument root to narrow by) caps locally and reports through a volatile the pass binds and
the entry point leaves nil. It carries `:sweeps` `:budget` `:message`, and what its cut costs is
a **vantage** rather than a pair — a context that would have seen the clash is never
asked — so it is the one notice whose loss no other entry's counts can reflect. They stay separate kinds because a reader acts differently on *went
unreported* than on *went undecided*, and because the two paths sweep for different
things. The deciding path sweeps for a `functional` or `asymmetric` **declaration** and
for a `genl` edge that carries one down; the reporting path sweeps for the edge and not
for the declaration (`settle/expose-constraint-clashes!`, docs/nmtms.md), since on an
ordinary write it reads the moved region's own binary facts — both halves of a
cross-context clash have to be stated, and a declaration states neither. The consequence to keep in view is the
same one either way: a reader watching only the exposure entry would never learn that a
predicate declared functional after its facts was swept short.

**A third notice, covering two bounds that pass shares.** Its two edge triggers each
reach out of the region — a `genlCx` edge over the ancestor set it newly sees, a `genl` edge over
the spec subtree beneath the predicate it newly puts under a mark — both budgeted exactly
as the disjointness sweep beside it; and its *entries* are not bounded by the region
either — a functional slot filled from N contexts one vantage sees is N−1 pairs off a
single arriving fact, where the ledger keeps the newest 1000. So the pass stops its walk
at `tax/*exposure-instance-budget*`, files at most **8** entries whatever it found,
and files one **`:constraint-exposure-truncated`** naming whichever bound it met —
`:pairs` `:filed` `:cap` `:unswept` `:sample` `:budget` `:message`. One kind rather than two because a
reader acts on them the same way: pairs are visible and unreported, and nothing went
*undecided*, which is what separates this from `:arbitration-truncated`. The arbitration notice accumulates across the settle's
passes and is filed once, since `settle/constraint-nogoods` re-runs its sweep every pass
and one declaration cut in nine of them is one fact about the settle. Both notices are off
while `settle/*rebuilding?*`; the arbitration **sweep** is not, because that flag does not
promise the region is everything — `core/recover` binds it around two settles and the
second one's region is only what re-recording the refusals moved.

The **arbitrating** path reads the same rule. `settle/declaration-implicates` — which
runs under the KB's constraint policy (`checks/arbitrating?`: `open-kb`'s
`:constraints :arbitrate`, or the process default) and hands `settle` a nogood rather
than a ledger entry — narrows through `declaration-reach` too, since the two answer one
question about one KB: a pair that one reached and the other did not would be reported
as merely *visible* by `violations` or as *decided* by `contradictions` depending on
which route happened to run.

**Seven of the eight shapes are named by a functor and the eighth is not**, which is the
one thing both routes have to spell out separately. `(M T)` is an ordinary unary
membership whose functor is whatever the metatype is called, so no fixed vocabulary of
declaration functors can recognize it — only `tax/disjoint-metatype?` says it declares
anything at all. Both routes therefore gate on the taxonomy rather than on the sentence:
`settle/metatype-member?` for the arbitrating one, the same read inline for the exposure
one. It is the shape most likely to be reached by one and not the other, and the
consequence is exactly the split above — the clique closes, the exposure pass files the
pair, and nothing ever weighs it.

Measured on the OpenCyc import [kbs.md](kbs.md) is the route to, in one run. Over its
~27k distinct declared disjoint pairs, sweeping below
*either* side asks for roughly 26M instance enumerations against the intersection's
roughly 1.7M — **about 16×** — so the 4,096-instance budget is spent after **27**
declarations rather than several thousand. The candidate sets are further apart than the
enumerations: on a 2,092-declaration spread the union rule calls roughly 1.8M terms
candidates, of which 34 can convict.

Run per trigger over all ~38k `disjoint` sentexes with the budget out of the way, the
pass costs under a minute where the union rule costs several for the first 3,000 alone —
**roughly 50× on the same 3,000**. And it loses nothing: `core/exposed-clashes`, which
uses no candidate
rule and no budget at all and is complete by construction, reports **638** clashes;
the narrowed pass reports the same 638, with both set differences empty. The union
rule reaches 638 from only 3,000 of those triggers precisely *because* it
over-collects — those extra reports are clashes it stumbles on while sweeping a
declaration that does not implicate them, filed against the wrong trigger.

Under a budget the difference is coverage rather than time, which is the point. One
settle whose region holds 2,000 declarations leaves **536** of them unswept at the
4,096-instance budget under the union rule and **69** under the intersection; raised to
100,000 the two are 466 and 5.

Two arms cannot narrow that far and say so. `genl` and `genlCx` move what a
membership *means* rather than separating two named types, so the second half of a
clash could be any other membership the term holds; all they can apply is the O(1)
`pairable?` gate — a term with one fact about it at argument 1 cannot be half of a
pair. That gate is **over-approximating on purpose**, where the intersection is exact:
the argument root is not belief-filtered and spans every predicate and either polarity,
so a count above one is only evidence that a pair is possible, where one is proof that
it is not. Both directions are safe because a candidate that convicts nobody merely
checks and yields nothing — the rule may over-collect, never under-collect.

The budget bounds the **enumeration**, never the survivors. Budgeting what survives
would make a candidate rule that rejects everything walk the whole extent looking for
one keeper and then report full coverage — which is the one thing a bounded pass may
not do, and is what `exposure_test`'s
`a-sweep-that-convicts-nobody-still-stops-at-the-bound` pins.

The sweep is what the *incremental* question needs — which instances a changed
declaration implicates — and it is why the pass is bounded. The **standing** question
needs none of it: a term is a candidate iff it holds two believed memberships, so
walking the memberships finds every candidate exactly, which is what
`core/exposed-clashes` does. It is complete where the settle pass is budgeted, and it
is the one to ask of a KB that arrived all at once — a `recover` rebuilds belief rather
than changing it, so the settle pass sits it out (`settle/*rebuilding?*`) and left
unbounded there it was a quarter of the wall clock of an OpenCyc import — the one
[kbs.md](kbs.md) is the route to, measured the once.

## Predicate metadata

Beyond types, the taxonomy caches predicate properties, declared as sentexes and
maintained by `integrate-sentex`:

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
  machinery above.

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
  antecedent is `(causes ?a ?c)` fires across two stored hops and not only across one —
  and `TransitivePredicateProver` is a `provers/SupportingProver`, so each answer carries
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
  `(P b a)` are contradictory, so a claim whose converse is believed `:monotonic` is
  refused (`ex-info` `:type` `:asymmetric`). A strict order like `largerThan` is the
  usual case. The conviction needs a believed **opposing** sentex, and a self tuple has
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
  (check kb '(fatherOf Bob Ann) 'CxUniverse)
  ;; [{:type :asymmetric :sentence (fatherOf Bob Ann) :pred parentOf
  ;;   :opposing (parentOf Ann Bob) :opposing-handle 3 :opposing-class :monotonic
  ;;   :message "asymmetric: parentOf cannot hold both ways, and (parentOf Ann Bob) is known true"}]
  ```

  The functor of `:sentence` is the spelling the caller wrote; `:pred` is the declaration
  it ran into. Several supers may carry the mark and each contributes its own violation,
  so one sentence can yield several entries differing only in `:pred`. `:opposing` and
  `:opposing-handle` name the believed claim on the other side and `:opposing-class` is
  its defeat class — `:monotonic` there is what makes the entry a refusal rather than a
  pair `settle` arbitrates.
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
- `(arity P n)` — the declared arity, cached rather than re-queried because the
  per-assert arity check reads it on every fact.
- `(functional P)` — a *constraint*: `assert` rejects a second, different value
  for the same first argument (`checks/functional-problems`). With equality this would
  instead unify the two values.
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

  It resolves exactly as `functional` does: two symbol fillers derive `(equals V1 V2)`
  and merge, two non-symbols are refused outright, and a merge rests on **every**
  declaration constraining that position, so a predicate carrying both `(functional P)`
  and `(functionalInArg P 2)` keeps its merge when either is retracted
  (`checks/functional-declaration-supporters`). It is read up the hierarchy for
  `functional`'s reason, through a reader of its own — `tax/functional-in-arg-over`,
  since the table is keyed `pred → #{n …}` and a `:props` roster has nowhere to put the
  integer, which is also why `functionalInArg` is not a `::prop-kind`.

  The degenerate end is worth naming: `(functionalInArg P 1)` on a *unary* predicate
  leaves an **empty** determinant, which reads as "at most one filler, full stop" — every
  believed tuple of `P` is then comparable to every other. `settle`'s partner discovery
  narrows by a single argument root and has none to use in that shape, so it falls back
  to an extent sweep bounded by `tax/*exposure-instance-budget*`; a cut there files
  `:partner-sweep-truncated` ([operations.md](operations.md)). The same fallback carries
  a *composite* determinant whose `n` is the **last** argument — `(functionalInArg P 3)`
  on a ternary — for the same reason: several positions together are no more a single
  argument root than none are. What settle-time discovery does **not** reach is a mark on
  a position that is not the last, `(functionalInArg P 2)` on a ternary, which its
  candidate gate (`marked-at-final-arg?`) never asks about. The entry point checks that one
  correctly like any other; it is cross-context *discovery* that stops there.
- `(irreflexive P)` — a *constraint*, and the strict counterpart of `reflexive`: a self
  tuple `(P a a)` is contradictory and refused at the entry point (`ex-info` `:type`
  `:irreflexive`). Stronger than `asymmetric`, which **admits** the self tuple — asymmetry
  needs a believed opposing sentex to convict and a lone tuple names none, where
  irreflexivity refuses it outright. For the same reason it is never an arbitrable nogood:
  there is no pair. A declaration arriving after a self tuple was stored is the `arity`
  case rather than the `asymmetric` one — the tuple stands and the late mark reports rather
  than defeats. `(genl asymmetric irreflexive)` classifies every asymmetric predicate as an
  irreflexive one for a *query*, but does not set the `:irreflexive` property on it, so an
  asymmetric predicate still admits its self tuple.
- `(anti_symmetric P)` — a *constraint* that resolves by **merging**: a believed converse
  `(P b a)` beside `(P a b)` forces the two arguments to be one thing, so the KB derives
  `(equals a b)` and merges (`special/derive-antisymmetric-equalities`), the antisymmetric
  twin of what `functional` does with two symbol values and the same three arrival
  directions (fact, declaration, `genl` edge). The merge is justified by both facts and the
  declaration, so retracting any one un-merges. A converse no equality could reconcile —
  two numbers, a compound — is the hard contradiction refused at the entry point instead (`:type`
  `:anti-symmetric`), like a numeric functional clash. A self tuple's converse is itself
  and `(equals a a)` is trivial, so it is admitted.
- `(anti_transitive P)` — a *constraint* whose conviction spans **three** claims: `(P a b)`
  and `(P b c)` believed make `(P a c)` contradictory, the dual of `transitive`. The three
  are one nogood rather than three pairs, weighed by the same rule any contradiction is
  (`settle/decide-nogood` over the whole member set): a chain that is known true refuses
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
  refused at the assert entry point exactly as a directly written mark is. The **audited**
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
  no `arg` pair gets the enforced half and no audit, which is the honest answer rather
  than a requirement quantified over `thing`. `genlArg` is not read, so a
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
`checks/declared-arity` reads it off the arity table and the predicate-type memberships,
falling back to `inherited-arity` where the predicate declares nothing of its own. And
`inverse` has a reader of its own, `tax/inverses-under`, which walks the hierarchy the
other way.

| mark | descends? | why |
|---|---|---|
| `arity`, and the predicate-type memberships | yes — read where the sub-predicate declares none of its own, and where it declares one the two are held to **match** | a ternary `fatherOf` fact is a ternary `parentOf` tuple |
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
*are* the super's and tuples of different lengths are not the same tuples. The arity
table still answers one value per predicate and `(functional arity)` still has a single
value to be functional about — now because the second, disagreeing value never lands.

`tax/props-over` gates on the `:props` roster for the kind being empty, which it is on
nearly every KB, so a descending read is one map lookup where nothing is declared — the
gate `tax/inverses-under` takes on the empty `:inverse` map, and what keeps a closure
walk off the goal paths that ask `has-prop?` per goal.
- `(decontextualized_predicate P)` — every `(P ...)`, asserted or concluded by a rule,
  is also deduced into CxUniverse, which every context sees, so the fact stops
  being a claim of one theory. The target is fixed rather than named, because the
  definitional checks are context-scoped and only cover the copy when the stating
  context can see where it lands (see [contexts.md](contexts.md)).
- `(forced_decontextualized_predicate P)` — stronger: every `(P ...)` is *stored* in
  CxUniverse directly (its context forced there on assert, no justification). Declared
  for `genlCx`, so the context topology has one canonical home (see
  [contexts.md](contexts.md)).

Accessors: `has-prop?`, `inverse-of`, `props` (the set carrying a property).

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
seen KB-wide (the definitional reads and the structural ones agree), while a bare KB keeps
it in its declaring context. Arity memberships are likewise direct (every genl type is
looped into `unary_predicate`). So `isa? siblingOf symmetric`, `isa? siblingOf
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
- `disjoint` / `disjoint_metatype` — arguments are types; two genl-related types can't
  be declared disjoint (one contains the other, so they overlap).
- `arg` / `genlArg` — a predicate, a positive-integer position, and a type. One
  check serves both (`wff/arg-constraint-problems`): they are structurally identical
  and differ only in what they demand of the argument, which is `checks`' business.

These are structural checks; the *content* check that an argument actually reaches its
`arg` type is `checks/constraint-checks`.

## Two argument constraints

`(arg P n T)` asks argument *n* to be an **instance** of T; `(genlArg P n T)` asks
it to be a **subtype** — `arg` one level up. An `instance_relation_predicate` takes
the first, a `type_relation_predicate` the second, and the same symbol answers them
differently: `penguin` satisfies `(genlArg partType 1 physical_object)` and fails
`(arg partOf 1 physical_object)`, which is exactly the distinction between a claim
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
hierarchy **everywhere** is excused unless it is an **individual** (which
`wff/genl-problems` refuses `genl` of, so it can never acquire the edges that would
excuse it — a global probe on purpose, since a reified NAT is indistinguishable from an individual by
spelling and is minted with real `genl` edges into `CxUniverse`, which not
every writer sees); and an argument whose edges are merely *out of the writer's
sight* is excused too, since a NAF check that convicted on invisible evidence would
convict harder the less a context sees.

### Arity

`checks/arity-problem` holds a sentence to the arity its predicate is **bound** to —
from `(arity P N)` or from a `unary_predicate` / `binary_predicate` / `ternary_predicate`
membership, which the CxCore rules derive from each other, so either spelling binds, and
from a super-predicate's where the predicate declares nothing of its own (below). One
predicate binds one length: the three classes are pairwise `disjoint` (above), so a second
classification never lands to derive a second value. The **top literal only**, exactly like `arg`: a rule reaches the check as its
`implies` form, whose own arity is 2 and is checked as such, and its antecedents are
not. Open-world in the same shape — a predicate the KB has never declared can be used
at any arity, since the declaration may simply not have arrived.

`(variable_arity P)` exempts a predicate outright. `lessThan` is declared binary *and*
reads a chain of any length (`(lessThan 1 2 3)` is `1 < 2 < 3`); the declaration is what
says so, rather than the check carrying a roster of predicates it quietly skips.

**A predicate that declares no arity takes its super-predicates'**, and only then: a
`fatherOf` tuple is a `parentOf` tuple, so a ternary `fatherOf` fact is a ternary
`parentOf` tuple that `(binary_predicate parentOf)` says does not exist. The restriction
to predicates that declare nothing is what keeps this a *check* rather than a preserved
fact — `(arity fatherOf ?n)` answers the one value somebody wrote of `fatherOf`, and
nothing where nobody wrote one. Supers that disagree bind nothing, which is the stance
`tax/declared-arity` already takes toward two contradictory declarations of one
predicate, and a `variable_arity` super releases the inheritance for the reason it exempts
the predicate carrying it. Both spellings are read up the hierarchy, the `(arity P n)`
table first because it costs a map read where the predicate-type membership costs a
retrieval.

**A predicate that declares one is held to match its super-predicates'**, and the two
arrival orders are both refused: `checks/edge-arity-problem` refuses a `genl` edge
arriving onto two predicates already declared at different lengths, and
`checks/declaration-arity-problem` refuses an arity declaration arriving onto a predicate
a visible edge already relates to a differently declared one. Either way the **arriving**
sentence is refused, so the KB never holds the pair, and which of the three sentences is
refused is the first-writer-wins every entry point refusal has. The refusal is `:arity` and its
message names both predicates, both lengths, and the two ways out:

    arity does not descend: 3 arguments declared of fatherOf, 2 declared of parentOf,
    and (genl fatherOf parentOf) says every fatherOf tuple is a parentOf tuple —
    tuples of different lengths are not the same tuples (give the two one arity, or
    declare one variable_arity)

A specialization therefore does not carry a signature of its own. This is the one point
where an arity constraint is stricter than the argument constraints beside it, and the
reason is that a length cannot be narrowed: `arg` on a sub-predicate *adds* to what
the super demands of a tuple, while a second length says the two tuple sets are one set
and are shaped differently, which is not a stricter claim but an unmeanable one. Own
declarations only, on both sides — what a predicate inherits is what the descension is
for, and supers that disagree with *each other* are not a pair, since they are not
genl-related and the sub takes nothing from them. `variable_arity` on **either** side
releases the match, for the reason it exempts the predicate carrying it.

That strictness is also what keeps `(functional arity)` honest through the hierarchy.
`(arity P n)` is functional, so one predicate never has two lengths; refusing a
mismatched pair extends the same guarantee across a `genl` edge, so preserving arity
downward can never make a child answer both an inherited and an explicit value.

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
collection)` beside `(genlArg P 2 animal)` says the slot holds a kind of animal, and
`dog` satisfies it — an instance of `collection`, a subtype of `animal`, which is how a
converted ontology ordinarily declares a type-valued position. The two checks are
independent and each is open-world on its own, so declaring both narrows the slot rather
than emptying it.

Each arm needs a declaration to contradict, so a predicate the KB has said nothing
about stays unconstrained. `(functional arity)` closes the matching hole on the
declarations themselves: a second, different arity for one predicate is a clash rather
than a second belief, and since two numbers can never merge it is the hard rejection
rather than an inferred equality.

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
  value kinds carry the declaration that makes the case above bite —
  `(disjoint string predicate)` and `(disjoint number predicate)` in CxAbstract, text and
  a number each being a thing no relation is, and the second carrying `integer` with it.
  `symbol` deliberately carries neither: a name is exactly how a predicate is written, so
  the disjointness would be false. CxCore adds `(disjoint function predicate)`, which is
  what `function`'s own comment has always said in prose, and it is what refuses
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
  finds is **cached per `[direction predicate node context]` on the KB** and dropped —
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
fact is not stored; where it says "reaches back", the fact is stored and then weighed or
reported. So a violating set can leave a KB holding different content depending on which
half arrived first, and that is the documented contract rather than a gap in order
independence — `kb/constraint-policies` spells out why (admitting a clash against
known-true content would store what the KB can never believe). What order independence
demands, and what `:constraints :arbitrate` delivers for the three arbitrable kinds, is
that **belief** over the content that *is* stored comes out the same. `arity` does not
offer that entry point: it refuses under either policy, so its two orders differ in what is
stored and always will until somebody decides a wrong-arity fact may be admitted.

| declaration | declaration first | facts first | why |
|---|---|---|---|
| `disjoint` | refuses, or arbitrates under `:arbitrate` | reaches back: a nogood under `:arbitrate`, an exposure entry under `:refuse` | two memberships to weigh |
| `disjoint_metatype` | same | same | the members separate each other |
| `genl` / `genlCx` | same | same | closes a separation over content already stored |
| `functional` | refuses, or arbitrates | reaches back as a nogood under `:arbitrate`, over the spec subtree of the predicate it names and not that predicate alone | two values to weigh |
| `asymmetric` | refuses `:monotonic`, arbitrates `:default` | same | the converse is the second side |
| `arity` | **refuses, under either policy** | **reaches back and reports** — one `:arity` entry per convicted predicate of the swept subtree, carrying `:count`, a `:sample`, `:via` and the declaration in `:declared-after`, and at most **8** of them for one pass, past which an `:arity-report-truncated` entry counts the rest | names a second sentex, but it is the *vocabulary* one |
| `arg` / `genlArg` / `interArg` | refuses | **nothing** | convicted by an absence; no second sentex at all |
| a predicate-level `genl` edge, under an *argument* constraint above it | refuses what follows | **nothing** — the entailment reaches back, the refusal does not | the family's non-reach, one ingredient further out |
| a predicate-level `genl` edge, under a `functional` / `asymmetric` mark above it | refuses what follows, on the marked predicate's terms — `tax/props-over` reads the mark at every predicate above the sentence's own functor | the edge is admitted, neither mark refusing one, and it reaches back over the sub's stored facts: a nogood under `:arbitrate`, a cross-context exposure entry under `:refuse`, and the merges a `functional` mark now licenses (`special/equate-under-edge`) | the sub's tuples *are* the super's, so a clash among them is the super's |
| a predicate-level `genl` edge, under an **arity** above it | refuses what follows | **reports** — the edge binds the sub-predicate's length, so it files the same `:arity` entry a declaration would, `:via` naming the super | a binding is a binding whichever of the three ingredients supplied it |
| a predicate-level `genl` edge, across two declared **arities** | **refuses the edge** | **refuses the edge** | there is no order in which the pair means anything, so the arriving sentence is refused whichever it is |
| a **context** edge, under an **arity** in the ancestor set it opens | refuses what follows — the entry point reads the declaration through the visibility edge like any other | **reports** — the edge names two contexts and no predicate, so the pass sweeps its ends for the facts it newly convicts | a binding is read *from* a context, so an edge that moves what a vantage sees binds as a declaration does |

**A row's two halves answer one question about one KB, so they answer it in one
vocabulary.** Both are true statements either way, which is what makes a disagreement
between them expensive: a reader who meets one and greps for the other finds nothing, and
a reader who meets both concludes there are two problems. So the halves owe each other the
predicate blamed, whether the constraint was inherited or declared outright, and which
stored sentex convicted — `entry_point_and_report_test` is the roster over these rows, the cells
reading "nothing" included. The arity binding is where a wording has most to drift over,
and `checks/arity-binding-clause` is its one spelling: *is declared with 2 arguments* for a
predicate carrying its own declaration, *takes 2 arguments through `parentOf`* for one
whose length descends, since crediting a predicate with a declaration nobody wrote sends
an author looking for it.

**`arg` and its family have no retroactive reach.** A constraint arriving after a fact
whose argument is the wrong type does not reach back over it. It is the one family that
**cannot** become a nogood — the conviction rests on the *absence* of a path to the
constraint type, which is open-world negation as failure, so there is no second sentex to
weigh and nothing for a defeat class to compare — and a retroactive pass over it would
have to decide whether silence about a pre-existing argument's type is a violation or
merely silence. That is a policy question nobody has answered, and answering it by
accident in a sweep would quietly turn an open-world check into a closed-world one.

**The descension makes it a third ingredient rather than a second**, and the non-reach
covers that one too. `(fatherOf TheRock1 Mary)` stored, `(arg parentOf 1 person)`
stored, then `(genl fatherOf parentOf)`: the edge is admitted, the fact it now convicts
stays stored and believed, nothing is reported, and the next such claim is refused. That
is the same reading the row above it takes, one ingredient further out — the conviction
still rests on an absence, so there is still no pair to weigh. What *does* reach back is
the entailment, which is a different question and answered in
[argtypes.md](argtypes.md): a minted type is justified content, so it has to exist in
every arrival order or belief would depend on which.

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
binding's arrival order decide. Nor is it reported by the settle, and the asymmetry with
the row above is the argument. A wrong-length *fact* is content an `assert` admitted
because it could not have known, so there is a **newly** only the settle knows about. A
stranded declaration is inert — it constrains nothing, refuses nothing, mints nothing —
and reads the same an hour later, so it belongs to `kb-quality`, whose `:declarations`
reading names them. Cheaper there, too: the census enumerates the declarations, which are
vocabulary and therefore few, where a settle-side sweep would probe every predicate of a
subtree per write.

`interArg` inherits that argument verbatim, and shows the other side of the same gap. A
conditional constraint has **three** ingredients, not two — the fact, the declaration, and
the trigger argument's type — and it is the *third* arriving last that nothing reaches:
`(eats Rex Chunk)` and `(interArg eats 1 carnivore 2 meat)` both stored, then
`(carnivore Rex)`, and the violation `Chunk` now commits goes unreported. `arg` has
exactly this, less visibly: an argument that acquires its first type after the fact was
admitted was excused by open-world when it was written and is not re-examined. Both are the
same non-reach, and closing either means answering the policy question above.

**`arity` reaches back but does not arbitrate**, and it is the case worth reading twice
because the pair looks exactly like the three arbitrable ones. It *does* name a second
believed sentex — the `(arity P n)` declaration, or the predicate-type membership saying
the same thing. That sentex is the **vocabulary entry the conviction is read through**:
`declared-arity` answers from the arity cache, which follows belief, so a nogood that
defeated the declaration would destroy its own premise. Measured, on a known-true
`(P A B C)` against a `:default` `(arity P 2)`: the declaration is defeated in the settle
that admits the pair, revived by the next settle's `clear-defeats!` while the table it was
uninstalled from is still empty, and with the table empty the clash is not re-derived — so
it is reported once and then by nobody, and while the declaration was out a *fourth*-arity
fact of the same predicate was admitted too. One wrong fact would disable a declaration for
every other use of the predicate, and belief would depend on how many settles had run. The
other members of the family defeat a *fact* and leave the vocabulary standing, which is
why they are stable. Do not promote `arity` to a nogood without first making the
vocabulary read independent of the belief the nogood moves.

**And it reaches back through the hierarchy and through visibility, because that is where
the binding comes from.** A length binds a predicate through its own declaration *or*
through a super-predicate's, and every one of those is read *from a context* — so `arity`
has **four** ingredients where `interArg` has three: the fact, the declaration, the
`genl` edge that inherits one, and the `genlCx` edge that lets a vantage see either. The
report fires on whichever arrives last. Three of the four name a predicate, and there the
sweep reads the **spec subtree** of what it triggered on rather than one predicate's
extent, so a declaration landing on `parentOf` finds the wrong-length `fatherOf` fact that
`parentOf` itself does not have.

**The fourth names two contexts and no predicate**, so what it convicts is worked out from
its two ends: the facts stored below `sub`, whose vantage the edge moved, and the bindings
stored above `super`, which is everything that vantage newly reaches. Either end alone is
complete — a fact newly convicted sits under one and the binding that convicts it over the
other — so the pass sizes both ancestor sets with `count-in-context`, an O(1) read apiece, and
enumerates the smaller. Neither is the cheap one in general: a fresh context joining the
root is nothing below and the whole vocabulary above, and a root context gaining a parent
is the reverse, and an ontology writes both. Sizing off stored content rather than off the
edge's spelling is also what makes two arrival orders reaching one KB choose the same end.

The entry's `:via` says which predicate the length was read off, and an inherited one is
worded as such — `fatherOf takes 2 arguments through parentOf`, not "is declared with",
which would send an author looking for a declaration nobody wrote. **The entry point reads the
same `:via` and words it the same way**, so one binding does not get two descriptions
depending on which half of the check a reader meets; a length declared of the predicate
itself still reads `is declared with` at both.

That leaves the two halves saying the same thing in every order: a believed wrong-arity
fact is **refused** if the binding was already there and **reported** if it was not.
Which of the two happens still depends on the order, for the reason the note above the
table gives, and that is the whole of the difference. Three things bound the property and
none of them is the arrival order — what the sweep can see, how much of the subtree it
gets to, and how many entries one pass may file.

**What it sees is belief.** The pass enumerates each predicate's *believed* facts
(`predicate-sentexes`), so a wrong-length fact stored but defeated when the binding
arrives is neither refused nor reported nor counted, and reviving it runs no entry point either:
the entry point ran on the assert that stored it, and a relabel re-asks nothing. So the finding is
about the content a binding convicts *and the KB believes*, which is not everything the
store holds.

**A subtree is a budget question, so the pass says when it ran out.** Sweeping the specs
rather than one extent means the instance budget can be spent with predicates still
unlooked-at, and the *first* of them to spend it may convict nothing at all — leaving no
finding for a `:truncated` flag to ride on, and every predicate after it examined zero
facts deep. A context edge whose ancestor set the budget cut is the same reading one ingredient
earlier: predicates the pass never got as far as looking *for*. The pass therefore files
one **`:arity-truncated`** entry naming how many predicates went unswept and how many
`genlCx` edges went unreached (`:predicates` `:sample` `:edges` `:edge-sample` `:budget`
`:message`) **whether or not anything was found**, which is `settle/expose-clashes!`'
reading and holds the property the descension exists for: a believed wrong-length fact is
refused, or reported, or the reader is told the sweep did not reach it — never none of the
three.

**A wide subtree is a ledger question, so the pass caps its own entries.** One binding
can convict a thousand predicates, against a ledger that keeps the newest 1,000 entries
and logs each at `:warn` — so a pass filing one apiece evicts every other violation in it,
which is the failure `settle/expose-clashes!` records at tens of thousands of identical
complaints. The findings are therefore capped at **8** for a pass, the content-first 8 of
the predicates convicted, and a ninth brings one **`:arity-report-truncated`** entry: how
many predicates
convicted in all, how many entries were filed, how many facts between them, and up to
three predicates no entry names (`:predicates` `:filed` `:facts` `:sample` `:message`).
Read it as `:constraint-exposure-truncated` and not as the notice above it. Nothing is
swept short and nothing goes undecided — every one of those predicates is reached,
examined and convicted, and the cap costs the entry naming it rather than the looking.
Nothing is lost by summarizing, either, which is what separates this from an exposure: the
wrong-arity facts of `P` are re-derivable from the store by anyone who wants the list, so
what the ledger owes a reader is which predicates convicted and how many facts each.
