# Taxonomy: types, genl, and disjointness

- **Covers:** how the `genl` type hierarchy is cached and queried, how `disjoint` /
  `disjointMetatype` are enforced, and how `argIsa` / `argGenl` constrain arguments as a
  rejection check.
- **Not here:** `genlContext`, the sibling closure over contexts rather than types →
  [contexts.md](contexts.md); `argIsa` / `argGenl` read as an entailment that mints a
  stored, justified fact → [argtypes.md](argtypes.md).
- **Assumes:** sentex, context, belief, justification → [glossary.md](glossary.md).

`vaelii.impl.taxonomy`. Transitivity is the lifeblood of common sense, so it is **not**
done with rules — the direct adjacency of the type graph is stored and the transitive
closure is answered on demand (read-memoized per edge generation), never materialized.

## genl: the type hierarchy

`(genl Sub Super)` — every `Sub` is a `Super`. Types are unary predicates, rooted
at `thing`. We cache the reflexive-transitive closure both ways:

- `genls tax t` — supertypes of `t`, incl. `t` (up-closure).
- `specs tax t` — subtypes of `t`, incl. `t` (down-closure).
- `genl? tax sub super`.

### Three uses of genl

1. **Arg constraints.** `(argIsa pred n type)` sentexes constrain arguments;
   `assert` checks arg *n* with `isa?` (does the arg have a type whose `genls`
   reaches the constraint). Open-world: an untyped arg can't violate.
2. **Specificity.** Matching a unary type predicate fans out over `specs`, so an
   antecedent `(animal ?x)` is satisfied by a stored `(dog Muffet)` — no need to
   materialize `(animal Muffet)`. `isa?` answers membership on demand.
3. **(genlContext is the sibling relation over contexts — see contexts.md.)**

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
  added or removed. It costs ~28µs on the starter, against ~130ms for a chained
  assert.
- **Reference counting.** The same edge asserted in two contexts is two sentexes.
  Retracting one leaves the edge standing while the other still asserts it.
- **Derived edges count.** A rule concluding `(genl a b)` reaches the taxonomy via
  `integrate-transitive` on the derivation path, not just the assert path. Without
  it the running KB and `recover` (which reads the store) disagree about what the KB
  entails, so a restart silently changes the answer.

`recover` calls `clear-relations!` — which empties all eight caches — before rebuilding.
A rebuild that merged into the existing cache could only ever *add*, so an edge whose
sentex was gone would survive the recovery meant to re-derive it. `rebuild-taxonomy`
reads **stored** rather than believed sentexes, so `:support` / `:cache-support` record
every asserting sentex; the `refresh-beliefs` in `recover`'s closing `settle` then
applies belief, giving the same answer either side of a restart. Belief-filtering the
replay would drop a disbelieved supporter, and clearing its defeat could never revive
the entry.

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
  see below). No closure is touched. A redundant re-assert of an already-active edge is
  a no-op.
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
- A **cycle** is refused for `genl` and admitted for `genlContext`, and the potential is
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
- Maintaining it: an edge that closes a cycle merges two components, which is a question
  about the whole graph rather than about the edge, so `activate` surrenders the potential
  (`:loose?`) and `restore-depths` recomputes both parts in one O(V+E) pass — Tarjan for
  the components, then Kahn for the heights over the condensation. A deletion can *split*
  a component, and a stale component is the one thing here that would answer **true** for a
  pair no longer connected, so `deactivate` dissolves the component of either endpoint
  immediately and goes loose until the repair. Cycles are rare enough that paying a full
  repair for each is nothing.

### Reads are scoped by the asking context

A read asked from context K uses exactly the edges K can see: an edge counts iff some
**believed** supporter asserts it from K's `genlContext` up-cone, the same filter
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
memo key, interned per `[genlContext-gen ctxs-gen]` (`:vis-index`), and the scoped
walk memoizes one level deeper under it, bounded by `*scoped-memo-budget*` distinct
vissets per relation (OpenCyc's census: 445 asserting contexts, 561 distinct vissets
across 13,196 readers). Depth pruning survives unchanged — the potential holds over
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
`genlContext` admits cycles outright.)

The **`genlContext` closure itself is the stated exception and stays global**:
visibility scoped by visibility would be circular, every `genlContext` edge is forced
universal, and the interning above rests on it. So do the identity, storage, trigger,
and stratification reads, each marked `global on purpose` at its site. The
scoped-or-not split per check, and the exposure of clashes only a descendant can see
whole, are docs/contexts.md's story.

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
O(1) (measured 1340× on an 8k-deep chain), and `wff` runs one per taxonomy edge
asserted. Deferring by simply marking the relation loose would only move the
quadratic: child-first would get cheap and parent-first — the order hierarchies are
actually written in — would get expensive. The local lift is what keeps *both* orders
flat, since parent-first arrival never breaks an edge above a fresh node.

Three consequences worth stating:

- **A settle repairs on both sides of its belief reconcile.** The batch above is not the
  only thing that surrenders the potential: `refresh-beliefs` changes the active edge set
  with no sentex added or removed, so an edge defeated out of a component dissolves it
  and one revived into a cycle closes a new one — and the reconcile goes loose either
  way. Repairing only before it would leave that state standing until the *next* settle,
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
  rests on a cycle check made *with* that base.

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
either way, which is the shape the potential ranks by component. The second oracle holds
three readers of one question to one answer — the closure, the reachability, and the
witness the reachability rests on — since a scoped `genl?` disagreeing with the scoped
`genls` is the failure a DAG-only stream cannot produce.

**Scope.** The belief discipline applies to the two transitive relations, to the
equality partition, and — through the shared `:cache-support` reference count, keyed by
`[kind key]` — to the five flat caches too: `disjoint`, the disjoint metatypes and their
members, the predicate properties
(`transitive`/`symmetric`/`asymmetric`/`reflexive`/`functional`), `inverse`, and the
declared `arity`. Only `genlContext` is forced-decontextualized, so only it is guaranteed one
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

That reconcile is gated on `:cache-support-handles`, the flat set of every supporter of
any flat-cache entry: a settle whose moved handles miss it entirely reconciles nothing
rather than walking the vocabulary. The set is therefore a **contract** — it must hold
exactly the live `:cache-support` map's handles, or the gate quietly stops gating.
`support-add` / `support-drop` are the one place it moves, with a single exception:
unmarking a metatype drops its members' entries wholesale (`forget-metatype`, below), so
it owes the same removal by hand. A handle left behind after its entry is gone makes
every settle that relabels *that* sentex scan the whole vocabulary to find nothing, for
the life of the KB, since nothing ever removes it.

## Disjointness

Two mechanisms declare that types share no instance; both are closed under `genl`
(subtypes of disjoint types are disjoint):

- `(disjoint TypeA TypeB)` — an explicit pair.
- `(disjointMetatype Metatype)` — a metatype whose member types (`(Metatype T)`
  facts) are pairwise disjoint. Membership is **recorded, not materialized**: the
  metatype and its members are cached (`:metatype-members`, reference-counted on the
  `(M T)` sentex) and `disjoint?` consults them, so the clique is a property of the
  code rather than of the store. Asserting the metatype after its members, or a
  member after the metatype, both work; neither writes a `(disjoint …)` sentex.

  Asserting the clique instead would mean n(n-1)/2 stored premises for n members, and
  premises rather than justifications is a teardown no retraction can reach.
  Recording makes teardown exact: dropping the metatype releases every pair
  at once, and dropping one `(M T)` releases exactly that member's pairs while the
  remaining members stay separated. The cost is that membership is in-memory, so
  `recover` re-reads the `(M T)` sentexes after marking the metatypes. The browser's
  disjointness list computes the induced disjoint pairs rather than querying for them,
  for the same reason — there are no `(disjoint …)` sentexes to query.

**Both mechanisms separate any term, not only individuals.** `checks/checkable-term?`
admits every non-variable symbol, so the predicate meta-ontology is enforced the same
way the domain is: `(relationKind …)` is a `disjointMetatype` over
`instanceRelationPredicate` and `typeRelationPredicate`, and a predicate declared both
is refused exactly as `Muffet` being both a `dog` and a `cat` is. The same widening makes
`argIsa` constrain predicate-valued positions — `(argIsa typeToInstancePred 1
typeRelationPredicate)` refuses a link whose first argument is not classified
type-level. Numbers, strings and compounds stay outside both checks, since no type
membership can be asserted of one (a NAT reifies to its constant first, so a reified
term is checked under its constant). Open-world is unchanged: a term carrying no type
membership at all still cannot violate anything.

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
closure, the visibility cone, the adjacency and the metatype roster read once
(`separation-frame`), returning a predicate over candidate types. `disjoint?` is that
asked once; `checks/disjoint-problem` asks it of every type the term already holds,
which is what it exists for.

### Enumerating instead of testing

A goal with an open argument — `(disjoint a ?t)` — asks the other question: not *is
this candidate separated* but *which types are*. Answering it by testing every type
in the KB makes the cost of an answer a function of the vocabulary, which on an
imported ontology is six figures ([kbs.md](kbs.md)) where a term's own declarations
are three or four.

So it is read off the same frame, the other way round. `tax/separating-partners` is
every `y` a visible declaration separates `a` from — the pairs `a`'s supertypes carry
in `:disjoint-index`, plus the other members of any disjoint metatype one of them
belongs to. Every type disjoint from `a` is a subtype of one of those partners and
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
`genlContext` edge is visible from neither of the two contexts they are written in
alone, so `settle` asks each candidate's question from the maximal common descendant of
its context and each context holding a sentex it could pair with, beside its own
(`settle/clash-askers`, and [nmtms.md](nmtms.md) for what the one-sided answer cost).
Every one of those asks is the same scoped read from a context that already sees both
halves.

### What a declaration reaches back over

A declaration changes what already-stored content *means*, so the settle that admits
one re-examines the content written before it — or the KB would answer differently
depending on whether the separation or the memberships were written first, which is
the invariant [nmtms.md](nmtms.md) opens with. Seven sentence shapes reach back:
`disjoint`, `disjointMetatype`, a new `(M T)` member of a metatype, `genl`,
`genlContext`, and (for the nogood path) `functional` and `asymmetric`.

The reach is **two questions**, and keeping them apart is what makes a bounded sweep
buy real coverage:

- **what to enumerate** — one record fetch per instance below the declared types,
  which on a real ontology is the *extent* rather than the moved region. This is what
  `settle/*exposure-instance-budget*` bounds.
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

The **arbitrating** path reads the same rule. `settle/declaration-implicates` — which
runs under the KB's constraint policy (`checks/arbitrating?`: `open-kb`'s
`:constraints :arbitrate`, or the process default) and hands `settle` a nogood rather
than a ledger entry — narrows through `declaration-reach` too, since the two answer one
question about one KB: a pair that one reached and the other did not would be reported
as merely *visible* by `violations` or as *decided* by `contradictions` depending on
which route happened to run.

**Six of the seven shapes are named by a functor and the seventh is not**, which is the
one thing both routes have to spell out separately. `(M T)` is an ordinary unary
membership whose functor is whatever the metatype is called, so no fixed vocabulary of
declaration functors can recognize it — only `tax/disjoint-metatype?` says it declares
anything at all. Both routes therefore gate on the taxonomy rather than on the sentence:
`settle/metatype-member?` for the arbitrating one, the same read inline for the exposure
one. It is the shape most likely to be reached by one and not the other, and the
consequence is exactly the split above — the clique closes, the exposure pass files the
pair, and nothing ever weighs it.

Measured on OpenCyc. Over its 27,195 distinct declared disjoint pairs, sweeping below
*either* side asks for 26,518,841 instance enumerations against the intersection's
1,694,193 — **15.7×** — so the 4,096-instance budget is spent after **27** declarations
rather than 8,372. The candidate sets are further apart than the enumerations: on a
2,092-declaration spread the union rule calls 1,808,288 terms candidates, of which 34
can convict.

Run per trigger over all 37,701 `disjoint` sentexes with the budget out of the way, the
pass costs 52 s where the union rule costs 321 s for the first 3,000 alone — **49× on
the same 3,000**. And it loses nothing: `core/exposed-clashes`, which uses no candidate
rule and no budget at all and is complete by construction, reports **638** clashes;
the narrowed pass reports the same 638, with both set differences empty. The union
rule reaches 638 from only 3,000 of the 37,701 triggers precisely *because* it
over-collects — those extra reports are clashes it stumbles on while sweeping a
declaration that does not implicate them, filed against the wrong trigger.

Under a budget the difference is coverage rather than time, which is the point. One
settle whose region holds 2,000 declarations leaves **536** of them unswept at the
4,096-instance budget under the union rule and **69** under the intersection; raised to
100,000 the two are 466 and 5.

Two arms cannot narrow that far and say so. `genl` and `genlContext` move what a
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
unbounded there it was 27% of an OpenCyc import.

## Predicate metadata

Beyond types, the taxonomy caches predicate properties, declared as sentexes and
maintained by `integrate-sentex`:

- `(transitive P)` / `(symmetric P)` / `(reflexive P)` — drive the generic
  relation provers (see [inference.md](inference.md)).

  A declared-transitive `P` is **metadata only** — it is not a cached relation. Nothing
  about `P` enters the adjacency, so there is no closure to maintain, no depth potential
  to repair, and nothing an arrival order could make expensive; asserting `(largerThan A
  B)` is an ordinary fact assert. The cost is entirely at query time, where
  `TransitivePredicateProver` walks the believed facts (memoized per search step,
  `observe/*reach-memo*`). A **closed** goal stops at its answer, so a near pair is
  cheap; an **open** one enumerates and needs the whole reach, which is inherent. Both
  guard with a `seen` set, because nothing refuses a cycle in a user-declared transitive
  predicate the way `wff` refuses a `genl` cycle — and a cycle there genuinely entails
  reflexivity around the loop rather than being an error.

  `genl` and `genlContext` are cached instead precisely because the engine reads them on
  every match, placement and visibility check, where recomputing a reach per read would
  not survive. That is the whole difference, and it is why only those two carry the
  machinery above.
- `(asymmetric P)` — a *constraint*, and the mirror of a claim denies it: `(P a b)` and
  `(P b a)` are contradictory, which makes `P` irreflexive too, so `(P a a)` is refused
  (`ex-info` `:type` `:asymmetric`). A strict order like `largerThan` is the usual case.
  It is also what gives the converse standing to deny a preserved claim, so it decides
  whether `ArgPreservingProver` finds anything *against* one
  ([inherit.md](inherit.md)).
- `(inverse P Q)` — `P` and `Q` are inverses (a bidirectional map).
- `(arity P n)` — the declared arity, cached rather than re-queried because the
  per-assert arity check reads it on every fact.
- `(functional P)` — a *constraint*: `assert` rejects a second, different value
  for the same first argument (`checks/functional-problems`). With equality this would
  instead unify the two values.
- `(decontextualizedPredicate P)` — every `(P ...)`, asserted or concluded by a rule,
  is also deduced into UniverseContext, which every context sees, so the fact stops
  being a claim of one theory. The target is fixed rather than named, because the
  definitional checks are context-scoped and only cover the copy when the stating
  context can see where it lands (see [contexts.md](contexts.md)).
- `(forcedDecontextualizedPredicate P)` — stronger: every `(P ...)` is *stored* in
  UniverseContext directly (its context forced there on assert, no justification). Declared
  for `genlContext`, so the context topology has one canonical home (see
  [contexts.md](contexts.md)).

Accessors: `has-prop?`, `inverse-of`, `props` (the set carrying a property).

## The predicate meta-ontology

Predicates are **reified** and classified in the genl hierarchy under `predicate`
(itself a `thing`):

- by arity — `unaryPredicate` (every type, plus one-place properties like `flies`),
  `binaryPredicate` (relations like `parentOf`), `ternaryPredicate` (`argIsa`);
- by algebra — `symmetricPredicate` / `asymmetricPredicate` / `transitivePredicate` /
  `reflexivePredicate` / `functionalPredicate`, all subtypes of `binaryPredicate`.

The algebraic memberships are **derived from the metadata**: CoreContext carries rules
`(implies (and (symmetric ?p)) (symmetricPredicate ?p))` (and likewise for the others),
so one declaration drives both the generic prover and the type membership. The rule
names **no** context, and that is load-bearing rather than incidental — the conclusion
places by the ordinary rule, in the context the declaration was made in, so a predicate
declared symmetric privately gets its membership privately too
([contexts.md](contexts.md), "Do not name CoreContext in them"). Arity memberships are asserted directly
(every genl type is looped into `unaryPredicate`). So `isa? siblingOf
symmetricPredicate`, `isa? siblingOf binaryPredicate`, and `isa? siblingOf
predicate` all hold, and `isa? dog unaryPredicate` / `isa? argIsa ternaryPredicate`.

The same algebraic memberships are *also* answerable straight from the metadata by
the `PredicateTypeProver` (via `taxonomy/props`), so `ask (symmetricPredicate ?p)`
returns the declared predicates without touching the materialized facts. Belt and
suspenders: `isa?` reads the facts, `ask` reads the metadata (see
[inference.md](inference.md)).

## Well-formedness (`vaelii.impl.wff`)

Before storing, `assert` checks the special predicates are structurally sound:

- `genl` / `genlContext` — both arguments are types / contexts (not individuals), not
  equal, and don't create a cycle (the reverse relation must not already hold).
- `disjoint` / `disjointMetatype` — arguments are types; two genl-related types can't
  be declared disjoint (one contains the other, so they overlap).
- `argIsa` / `argGenl` — a predicate, a positive-integer position, and a type. One
  check serves both (`wff/arg-constraint-problems`): they are structurally identical
  and differ only in what they demand of the argument, which is `checks`' business.

These are structural checks; the *content* check that an argument actually reaches its
`argIsa` type is `checks/constraint-checks`.

## Two argument constraints

`(argIsa P n T)` asks argument *n* to be an **instance** of T; `(argGenl P n T)` asks
it to be a **subtype** — `argIsa` one level up. An `instanceRelationPredicate` takes
the first, a `typeRelationPredicate` the second, and the same symbol answers them
differently: `penguin` satisfies `(argGenl partType 1 physical_object)` and fails
`(argIsa partOf 1 physical_object)`, which is exactly the distinction between a claim
about a kind and a claim about a thing.

Which constraints apply is context-scoped for both, and so are the `genl` tests
themselves: a closure read asked from K walks only the edges K can see, so an
argument is judged against the hierarchy the writer's own cone holds. Open-world
holds for both, with a global floor and a scoped one: an argument outside the
hierarchy **everywhere** is excused unless it is an **individual** (which
`wff/genl-problems` refuses `genl` of, so it can never acquire the edges that would
excuse it — a global probe on purpose, since a reified NAT reads as an individual by
spelling and is minted with real `genl` edges into `UniverseContext`, which not
every writer sees); and an argument whose edges are merely *out of the writer's
sight* is excused too, since a NAF check that convicted on invisible evidence would
convict harder the less a context sees.

### Arity

`checks/arity-problem` holds a sentence to the arity its predicate is declared with —
from `(arity P N)` or from a `unaryPredicate` / `binaryPredicate` / `ternaryPredicate`
membership, which the CoreContext rules derive from each other, so either spelling
binds. The **top literal only**, exactly like `argIsa`: a rule reaches the check as its
`implies` form, whose own arity is 2 and is checked as such, and its antecedents are
not. Open-world in the same shape — a predicate the KB has never declared can be used
at any arity, since the declaration may simply not have arrived.

`(variableArity P)` exempts a predicate outright. `lessThan` is declared binary *and*
reads a chain of any length (`(lessThan 1 2 3)` is `1 < 2 < 3`); the declaration is what
says so, rather than the check carrying a roster of predicates it quietly skips.

### The declarations are checked against each other

`checks/declaration-problem` runs on an `argIsa` / `argGenl` sentence itself, not on
the content it constrains, and refuses three ways one can contradict what the KB
already says about its predicate:

- **A position the predicate does not have** — `(argIsa parentOf 5 animal)` where
  `parentOf` is declared binary. The constraint would never fire, so it reads as
  enforced while enforcing nothing. The arity comes from `(arity P N)` or from a
  `unaryPredicate` / `binaryPredicate` / `ternaryPredicate` membership; the CoreContext
  rules derive each from the other, so either spelling is enough, and both are read
  because a `{:chain? false}` assert has only what was written.
- **Both constraints on one position** — one asks the argument to be an instance of
  the type, the other a subtype. No term satisfies both readings of one slot.
- **A constraint disagreeing with the predicate's `relationKind`** — `argGenl` on an
  `instanceRelationPredicate`, or `argIsa` on a `typeRelationPredicate`.

Each arm needs a declaration to contradict, so a predicate the KB has said nothing
about stays unconstrained. `(functional arity)` closes the matching hole on the
declarations themselves: a second, different arity for one predicate is a clash rather
than a second belief, and since two numbers can never merge it is the hard rejection
rather than an inferred equality.

`argIsa` reads **two ways**: as a *constraint* when asserting (`checks/args-problem`
rejects a wrongly-typed argument), and as an *inference* when querying — the
`ArgTypeProver` (see [inference.md](inference.md)) concludes an individual's type
from the argIsa-constrained position it fills, so a thing's type can follow from
how it is used, not only from a stored membership.

## What is not cached, and why

- **Transitive-predicate closures have no cache beyond one query.** This is distinct
  from the `genl`/`genlContext` closures above, which *are* cached and incremental.
  `reach` (in `vaelii.impl.provers`) walks the stored facts, and a ground goal pays for
  the whole closure with no early exit. `observe/*reach-memo*` holds one closure cache
  for the life of a search step, so a rule's join does not re-walk it per binding, but
  two separate `ask` calls share nothing.

  A cache that outlived a query would have to be invalidated on every JTMS relabel, and
  `settle` relabels the whole moved region — so the invalidation would be as coarse as
  the thing it protects. Note that genl changes are **not** a dependency here: subtype
  fan-out applies only to unary goals, and `(P x y)` is binary.
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
offer that door: it refuses under either policy, so its two orders differ in what is
stored and always will until somebody decides a wrong-arity fact may be admitted.

| declaration | declaration first | facts first | why |
|---|---|---|---|
| `disjoint` | refuses, or arbitrates under `:arbitrate` | reaches back: a nogood under `:arbitrate`, an exposure entry under `:refuse` | two memberships to weigh |
| `disjointMetatype` | same | same | the members separate each other |
| `genl` / `genlContext` | same | same | closes a separation over content already stored |
| `functional` | refuses, or arbitrates | reaches back as a nogood under `:arbitrate` | two values to weigh |
| `asymmetric` | refuses `:monotonic`, arbitrates `:default` | same | the converse is the second side |
| `arity` | **refuses, under either policy** | **reaches back and reports** — one `:arity` entry per declaration, with `:count`, a `:sample`, and the declaration in `:declared-after` | names a second sentex, but it is the *vocabulary* one |
| `argIsa` / `argGenl` / `interArgIsa` | refuses | **nothing** | convicted by an absence; no second sentex at all |

**`argIsa` and its family have no retroactive reach.** A constraint arriving after a fact
whose argument is the wrong type does not reach back over it. It is the one family that
**cannot** become a nogood — the conviction rests on the *absence* of a path to the
constraint type, which is open-world negation as failure, so there is no second sentex to
weigh and nothing for a defeat class to compare — and a retroactive pass over it would
have to decide whether silence about a pre-existing argument's type is a violation or
merely silence. That is a policy question nobody has answered, and answering it by
accident in a sweep would quietly turn an open-world check into a closed-world one.

`interArgIsa` inherits that argument verbatim, and shows the other side of the same gap. A
conditional constraint has **three** ingredients, not two — the fact, the declaration, and
the trigger argument's type — and it is the *third* arriving last that nothing reaches:
`(eats Rex Chunk)` and `(interArgIsa eats 1 carnivore 2 meat)` both stored, then
`(carnivore Rex)`, and the violation `Chunk` now commits goes unreported. `argIsa` has
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
