# Qualitative constraint networks — one engine, six algebras

- **Covers:** how the generic path-consistency engine turns a relation algebra
  and a network into entailment, refutation and support that every calculus reuses.
- **Not here:** the specific spatial algebras (RCC-8, direction, distance) →
  [space.md](space.md); the temporal algebras (Allen's intervals, the point algebra) →
  [time.md](time.md).
- **Assumes:** sentex, context, genlCx, belief → [glossary.md](glossary.md).

`vaelii.impl.qcn` reasons about relations that have no numbers behind them: *inside*,
*north of*, *before*. You rarely know where a region's boundary runs or what o'clock a
meeting started, but you do know how things stand relative to one another — and that is
enough to derive relations nobody stated.

The engine knows nothing about a KB, a context, or belief. Pure data in, pure data out.
A relation **algebra** is a parameter and a **network** is a value, so a new calculus is
a table and a prover rather than a second reasoner. Six ship — the three standard
qualitative-spatial questions (topology, orientation, distance) and three about time and
frame:

| Namespace | Calculus | Base relations | Doc |
|-----------|----------|----------------|-----|
| `vaelii.impl.space` | RCC-8 topology — do two regions touch, overlap, nest? | 8 | [space.md](space.md) |
| `vaelii.impl.orientation` | cardinal direction — which way is one place from another? | 9 | [space.md](space.md) |
| `vaelii.impl.relative` | relative direction — left, right, in front, behind | 9 | [space.md](space.md) |
| `vaelii.impl.distance` | qualitative distance — how far apart, in classes | 7 | [space.md](space.md) |
| `vaelii.impl.interval` | Allen's interval algebra — how are two stretches of time ordered? | 13 | [time.md](time.md) |
| `vaelii.impl.point` | the point algebra — before, equal, after, over instants | 3 | [time.md](time.md) |

Three of the six composition tables are written out by hand — Allen's 13×13
(`interval/allen-composition`), RCC-8's 8×8 (`space/rcc8-composition`) and the point
algebra's 3×3 (`point/point-composition`). The other three are **computed**: the two
direction algebras from two independent axis projections, distance from the triangle
inequality over its class bounds.

The two direction algebras are computed by the same code, `vaelii.impl.projection`, from
one table each — nine relations onto the nine `[x y]` pairs of two three-valued axes.
That table has to be a **bijection** onto all nine, and the constructor refuses one that
is not (`:bad-algebra`) rather than letting composition discover it: a missing pair
composes to `nil` and gets stored as though it were a relation, and a repeated pair still
covers all nine while the inverse map silently drops one of the two relations sharing it.
So the count is checked as well as the coverage. Both shipped tables are bijections; the
refusal is for a caller building a calculus of their own.

A transcribed table can be mistyped into a wrong entailment reported with full
confidence, so two of the three are re-derived from first principles by their tests and
compared entry for entry: `interval_test` lays out three intervals every way six
endpoints admit and reads the three relations off, `point_test` does the same over three
instants. **RCC-8's table has no such derivation** — regions have no coordinates to
enumerate, so there is nothing to derive it from.

What stands over its 64 entries instead is `qcn_algebra_test`, which holds the
relation-algebra laws over all six algebras: converse a total involution on the universe,
composition closed and never empty, a singleton two-sided identity, `(a∘b)⌣ = b⌣∘a⌣`, and
Peirce's cycle law `c ∈ a∘b ⟺ a⌣∘c meets b`. Those read every cell against its transposed
and cycled counterparts rather than reading it again, which is what makes a mistyped cell
in a corner nothing queries visible: every single-cell mutation of the table but three
fails one of them, and the three are one shape — dropping a symmetric relation from its
own square, where both sides of every law move together. Associativity is deliberately
not among the laws, because `distance` composes weakly and is not associative, which
costs path consistency nothing.

`time.txt` and `space.txt` state each Allen and RCC-8 base relation's properties inert:
`(set/inert (inverse P Q))` per converse pair, `(set/inert (asymmetric P))` per relation
whose converse is another, and `(set/inert (negates P Q))` per pair of base relations.
They form no nogood and change no belief. `qcn_algebra_test` reads every such stored
sentence, the cardinal and relative calculi's `inverse` pairs included, and fails on one
its calculus's algebra contradicts.

Two things nearby are deliberately *not* calculi. `vaelii.impl.stp` is metric time —
numeric bounds closed by shortest paths, not a relation algebra, and forcing it through
one would be a category error ([stp.md](stp.md)). `vaelii.impl.scenario` is the search
that turns a network's per-pair *sets* into one concrete arrangement, and it is generic
over every calculus here ([scenario.md](scenario.md)).

Each gets path consistency, the inconsistency verdict, the entailment reading, the
refutation reading, support-carrying derivation and the caches unchanged. They are
mutually independent: no shared predicate, and no network ever sees another calculus's
facts.

The split is two namespaces, not one. `vaelii.impl.qcn` is the algorithm and knows
nothing about a KB. `vaelii.impl.qcn-kb` is the *other* half of the boundary — reading
believed facts in, reading entailments back out — and it is the same half for every
calculus, so it is written once. A **calculus** is what actually differs:

```clojure
{:name       :rcc8                ; names the cache and the report
 :algebra    rcc8-algebra         ; the qcn relation algebra
 :denotation {'partOfRegion #{:tpp :ntpp :eq} …}}   ; predicate -> base relations
```

`qcn-kb/calculus` bundles those three; the reader, the caches, the four goal shapes and
the prover follow from them. Each algebra namespace is then its table, its vocabulary,
and a dozen lines of delegation.

## The algebra and the network

A **relation algebra** is a map:

```clojure
{:universe  #{…}          ; every base relation — the constraint on an unknown pair
 :identity  #{…}          ; the singleton constraint on the diagonal (i,i)
 :compose   (fn [s1 s2])  ; composition of two relation sets
 :converse  (fn [s])}     ; the converse of a relation set
```

The base relations must be **jointly exhaustive and pairwise disjoint** — exactly one
holds of any two objects — which is what makes a *set* of them a constraint saying "one
of these", and an empty set a contradiction.

A **network** is `{[i j] → #{base relations}}`, both directions stored; an unrecorded
pair is the universe. A network is a plain value, which is what lets a caller memoize an
expensive pass on its content.

`constraint` reads a pair: the identity on the diagonal, the recorded set, else the
universe. Note the order — the diagonal answers the identity *whatever* is recorded
there, because the only relation a thing can stand in to itself is the identity.

## Path consistency

`path-consistent` enforces composition closure — for every triple `(i j k)`, tighten
`R(i,k) ∩= R(i,j)∘R(j,k)`, to a fixpoint. Tightening is monotone over a finite universe,
so it terminates; both directions are written on every tightening, so `constraint` never
has to consult the converse.

`nodes` is the second argument and it is where the triples come from, so passing every
node the network mentions is the **caller's** obligation: tightening reaches only the
nodes it is given, and one left out is a path composition left unmade — a silently
weaker answer, never a wrong one. Extra nodes are always safe, which is why every
algebra passes the network's own nodes plus whatever the goal names. The result does not
depend on the *order* of `nodes`: tightening only narrows and composition is monotone in
⊆, so the loop lands on the unique greatest fixpoint below the network it was handed,
and the order decides how many revisits that takes and nothing else.

It returns the tightened network, or **`:inconsistent`** the moment a constraint
empties — an empty constraint says two nodes can stand in no relation at all, which no
model satisfies. Two shapes of contradiction are unsatisfiable *as given* and can never
be reported by tightening, so both are checked up front, over the whole network rather
than over the node list:

- A constraint that arrives **already empty**. The loop only reports a constraint it
  narrows to nothing, and an empty one cannot be narrowed further, so without the check
  the verdict on two contradictory facts about one pair would depend on whether some
  third node happened to route through it.
- A **diagonal** constraint that excludes the identity — a claim that a thing stands to
  itself in some relation it cannot. Every triple has `i ≠ k`, so no triple ever visits a
  diagonal, and `constraint` answers the identity there regardless; the claim would
  otherwise be silently dropped instead of reported. A reader produces one exactly when
  an asserted `(P a a)` survives intersection with its own converse, i.e. when P is
  symmetric: `(spatiallyDisconnected A A)` records `#{:dc}` on the diagonal and is
  unsatisfiable, where `(nonTangentialProperPart A A)` empties and is caught by the first
  check. A believed `(not (spatiallyEqual A A))` is the negative way to write one.

### Greatest, not least

The loop lands on the **greatest** fixpoint, and which end it comes from is not a detail
of the implementation — it is what the answer means.

A fixpoint is a network `X` with `tighten(X) = X`, and there is generally more than one.
Tightening is monotone over a finite lattice, so a smallest and a largest both exist, and
you reach them by iterating from the corresponding end: from the empty network upward, or
from the network as given downward. Path consistency starts at the top — every pair
unconstrained, every base relation still possible — and only ever removes. That is the
greatest fixpoint below the input, and it says **nothing is ruled out that the constraints
do not rule out**.

Which end the loop starts from is not a free choice: the least fixpoint of the same
operator is a different, degenerate answer — every constraint set to `#{}`, stable but
claiming that every KB's theory is contradictory. [why greatest, not
least](defenses.md#path-consistency-computes-the-greatest-fixpoint-not-the-least)

Both are unique, which is what makes both order-independent. That is the property the
engine actually needs, and it is available at either end — but only at an end.

[why path consistency is not a Datalog or ASP
program](defenses.md#path-consistency-runs-in-the-engine-not-as-a-datalog-or-asp-program)

### The arc queue

That order-independence is what lets the loop be **PC-2** rather than a re-sweep. A triple
needs visiting only if one of the two constraints it *reads* has narrowed since it was
last looked at. Each narrowed pair goes on a queue in both directions (both are written on
every tightening, and either can be an input); draining it visits, for a pair `[a b]`, the
triples `(a b m)` and `(m a b)` — every triple with that pair as an input, and nothing
else. Draining can enqueue more, and it terminates because every entry costs a strict
narrowing over a finite universe.

At the fixpoint every triple has been examined since its inputs last changed, which is
the same closure the repeated sweep reaches: a pair *being* narrowed never invalidates a
triple that reads it, since a subset of a set that was already contained is still
contained.

Revisiting is done by **whichever is cheaper**, and the two costs are directly
comparable: draining is `2 × changed × (n-2)` triple visits, another sweep is
`n(n-1) × (n-2)`. A sparse network moves a handful of pairs and drains for a rounding
error; a network that determines nearly *every* pair would cost about two sweeps to drain, and
sweeping again is less work. That is not a heuristic with a threshold in it — it is the
two counts, compared. Either route runs the same step to the same fixpoint, so the choice
is cost and nothing else.

**The first look need not be a sweep either.** A network read out of a KB records a
constraint at a handful of pairs and leaves the rest unknown, and a triple reading two
unknowns narrows nothing where the algebra composes the universe to itself — so on a first
pass the recorded pairs are the only ones a triple can learn from. There are `m` of those
against the `n(n-1)` a sweep visits, and where `m` is small, seeding the queue with them is
the same saving the queue makes *after* a sweep, made before one. Where most pairs are
recorded, the first look is a sweep: a queue seeded with all n(n-1) pairs visits each
triple twice.

What the estimate cannot see is how much the network will turn out to narrow: a sparse
input can still close to a dense output, and then draining costs more than sweeping. So the
first drain is **budgeted** at one sweep's worth of pops and gives up rather than run away.
Giving up adds no work that was earned — the array only ever narrows, and the fixpoint
below the network it started from is unique — so the sweep route simply finishes from
there. The two outcomes are exactly the two shapes: the containment tree closes with **no
sweep at all**, the total order bails and sweeps, and `qcn_queue_test` asserts both by
counting sweeps and checking each answer against the re-sweeping reference.

`path-consistent-naive` is the re-sweeping reference, kept and public. `qcn_queue_test`
runs both over randomized networks across four algebras (3, 8, 9 and 13 base relations)
and several node counts, seeded so a failure reproduces, and asserts they agree network
for network and verdict for verdict. Two implementations that share their tightening step
and differ only in which triples they revisit can agree only by both being right.

One shortcut sits inside the step, and it is decided once per run rather than per triple:
a triple both of whose inputs are *unknown* can narrow nothing when the algebra composes
the universe to itself, which every jointly-exhaustive algebra does. Where the runtime
check says otherwise, nothing is skipped. In a sparse network that is most of the triples.

### Warm-starting: semi-naive over the network

A KB being loaded asks for the pass again after every arriving fact, and all but a handful
of the pairs are exactly where the last run left them. Closing the whole network again is
the cubic loop redoing work it has already done.

So a run that can be told what moved starts from the previous answer:
`qcn/path-consistent-from` takes a network and an earlier *result* for a network the new
one **narrows**, and revisits only the triples reading a pair that moved. The seeds go
straight onto the arc queue — there is no first sweep to make, since the previous run
already made it — and the same cost comparison decides between draining and sweeping, for
the same reason.

The identity that licenses it falls out of ["greatest, not least"](#greatest-not-least).
Path consistency computes the greatest fixpoint below the network it is handed, so for any
narrowing `c`:

    PC(N ∩ c) = PC(PC(N) ∩ c)

Both sides sit below `N ∩ c`. The left is a fixpoint below `PC(N)` (monotonicity), so it
is below the right; the right is a fixpoint below `N ∩ c`, so it is below the left. Hence
equal — warm-starting is not an approximation, it is the same answer reached without
re-deriving what did not move.

**It applies to narrowing only.** A retraction or a withdrawn belief *widens*, and there
is no such identity: a fixpoint cannot be run backwards, because its result does not
record which of its narrowings the departing constraint was behind. `qcn/narrowing-of?` is
the precondition, checked by the caller against the network the previous answer was computed
from, and a widening pays the whole pass. The cost of a widening is a trade rather than a
gap — and retraction is rare where loading is not.

Two things are deliberately outside it. The **support-carrying** pass is never warm-started:
a warm start keeps the supports the previous run accumulated, so which handles an
entailment names would become a function of the order the facts arrived in — and those
handles become a firing's antecedents. The closed network is a unique greatest fixpoint
and so is order-independent whichever way it is reached; the support is one witness among
several, and only a run from nothing picks the same witness every time. And **nodes are
read off the merged network** rather than taken from the caller: a warm start is taken
exactly when facts have arrived, and an arriving fact routinely names a node the previous
network never held. A node left out is a node no triple visits, so its every composition
goes unmade — and the answer comes back looking merely uninformative rather than wrong,
which is the failure mode a test has to be built to see.

`qcn_queue_test` walks a randomized *narrowing sequence* over each algebra — one arriving
constraint at a time, nodes appearing as it goes — warm-starting each step off the last
answer and checking it against a run of the re-sweeping reference from nothing. Passing
the warm call no node set at all is part of that test rather than an oversight.

### Cost

Measured by `lein bench-qcn` on two shapes — a containment tree of regions (RCC-8, the
sparse realistic case) and a total order of intervals (Allen, the dense worst case) —
each the fastest of three runs, with `path-consistent-naive` alongside as the reference:

| nodes | triples/sweep | tree | tree, re-sweeping | order | order, re-sweeping |
|-------|---------------|------|-------------------|-------|--------------------|
| 10  | 720 | 0.08 ms | 0.06 ms | 0.11 ms | 0.09 ms |
| 20  | 6,840 | 0.17 ms | 0.23 ms | 0.43 ms | 0.44 ms |
| 40  | 59,280 | 0.54 ms | 1.7 ms | 2.2 ms | 2.6 ms |
| 80  | 492,960 | 2.1 ms | 8.6 ms | 14 ms | 23 ms |
| 160 | 4,019,520 | 7.3 ms | 65 ms | 99 ms | 122 ms |

The queue's win is **8.9× on the sparse tree** at 160 nodes and grows with size (1.4× at
20, 3.2× at 40, 4.1× at 80); on the dense total order it is 1.2–1.7× and does not, because
that shape determines every pair and the driver ends up sweeping either way. Both shapes are
below the noise at ten nodes, where a whole pass is a tenth of a millisecond.

The **re-sweeping** column is the floor a sweep-based pass cannot get under: cubic in
nodes, not in facts, since it visits n(n-1)(n-2) triples however few constraints there are.
The queue is only bounded by that floor when the network actually closes dense — a sparse
one never sweeps at all and is bounded by what it narrows instead, which is why the tree
column pulls away as *n* grows and the order column does not. A couple of hundred nodes in
one context is the working range for the dense case.

Two constant factors apply whichever route a run takes. Skipping a triple whose two
inputs are both unknown is worth **2.6×** on the tree with the queue held out of it, and
the bitmask representation below is worth **31×** on it.

### Bitmasks, not sets

Relation sets are the *public representation* — what a calculus writes, what a caller reads, what
every example above is stated in. They are not the arithmetic. A pass does exactly three
things to a constraint: intersect it, compose it with another, take its converse. An
algebra has a handful of base relations — eight for RCC-8, thirteen for Allen, the widest
that ships — so a constraint fits in the bits of a long, and then intersection is
`bit-and`, emptiness is `zero?`, the containment an entailment asks about is one `bit-and`
compared against its argument, and composition and converse are array reads.

So `path-consistent` encodes the network into a flat `long[n·n]` for the duration of the
run, tightens it in place, and decodes the pairs it touched back into sets on the way out.
The array is local to the run and never escapes; a caller sees an immutable network
value. Two kinds of entry cannot live in the array and are carried through
untouched: a **diagonal** pair, which no triple visits and which `constraint` answers the
identity for anyway, and one naming a node outside the `nodes` argument, which tightening
was never going to reach.

Nothing about this reaches a calculus. The compilation derives everything from the algebra
exactly as written — the base relations ordered **by name**, so the encoding is a function
of content rather than of set iteration order — and is cached on the algebra value itself.
The two tables are built by dynamic programming over the *base* relations: composition and
converse both distribute over union, R∘S being by definition the union of the pairwise
compositions, so `f(s) = f(s minus its lowest relation) | f(that relation)` and a
whole-mask table costs k² calls into the algebra plus one OR per entry rather than k·2^k
calls. Allen's thirteen relations make the widest table at 106,496 entries; an algebra too
wide for one falls back to reading the base table a pair at a time, which allocates nothing
either way. That distributivity is the one assumption in the layer, and a wrong table entry
would be a wrong *entailment* reported with full confidence rather than a crash — so
`qcn_mask_test` holds both tables against the algebra's own set-valued `:compose` and
`:converse`, exhaustively where 2^k allows and over a seeded sample where it does not,
across all six calculi and a synthetic one wide enough to take the fallback.

#### Two numbers bound this layer, and neither is a cache

The compiled algebras and the decode tables are caches with rows on the page
([caches.md](caches.md)). These two are not: nothing holds entries, nothing is dropped,
and each decides one thing at compile time.

| Number | Value | What it decides |
|---|---|---|
| the algebra **width** | 62 base relations | above it `compile-algebra` **refuses**: a constraint is the bits of a long, and that is what one holds |
| the **dense-table** threshold | 2^18 = 262,144 entries | at or under it the composition table covers whole masks; over it, base relations only |

The width is a refusal rather than a fallback because there is nothing to fall back to —
an algebra of 63 base relations has a constraint lattice no representation here works in,
and the widest that ships is Allen's thirteen. The threshold is a **build decision** and
nothing else: under it a composition is one array read per relation on the left, over it
one read per pair, which is `|s2|`× the reads and allocates nothing either way. Allen's
106,496 entries are the widest table any shipped calculus asks for, so every one of them
takes the dense side, and the sparse side is exercised by the synthetic algebra above.

Measured on the same two shapes, against the same pass over relation sets. **These are
not the numbers above**: that table measures the incremental queue against a full
re-sweep with relations already held as masks, and this one measures the mask
representation against Clojure sets over the whole naive pass — so the same shape at the
same size reads differently in each, and only the ratio within a table means anything.

| nodes | tree, sets | tree, masks | order, sets | order, masks |
|-------|-----------|-------------|-------------|--------------|
| 20  | 3.4 ms | 0.25 ms | 7.4 ms | 0.44 ms |
| 40  | 22 ms | 0.99 ms | 63 ms | 2.6 ms |
| 80  | 154 ms | 5.6 ms | 0.53 s | 17 ms |
| 160 | 1.15 s | 37 ms | 5.0 s | 121 ms |

**31× on the tree and 41× on the total order**, at 160 nodes, and the gap widens with size
because what it removes is allocation. Every `determined` count is identical, which is the
check that matters: the representation changed, the answers did not.

Composition and converse run through `IRelationOps`'s primitive methods, and the triple
walk is an ordinary closure. [why each, as
measured](defenses.md#composition-runs-through-irelationops-the-triple-walk-is-a-closure)

**Soundness.** Path consistency is sound, and decides each of these algebras over its
maximal tractable subclass. On the full language it can leave a network path-consistent
yet globally unsatisfiable, so an entailment reported here is real but a *non*-entailment
means **"not provable", never "provably false"** — the same open-world reading `arg`
and `exceptWhen` take.

## What every algebra does with it

The six provers are line-for-line the same shape, so the pattern matters once.

**Reading in.** One `res/matches-visible` per predicate of the calculus — belief- and
context-filtered, so a defeated or invisible fact never reaches the network. Each
asserted `(P a b)` intersects the `(a b)` constraint with P's denotation and the `(b a)`
constraint with its converse, so two facts about one pair narrow it together.
Intersection is commutative and associative, so the network is a function of the believed
facts alone, never of the order they were asserted or read in. Believed **negative**
facts narrow it too — see [Negation](#negation-refutation-and-negative-facts-as-constraints).

**Reading out.** A goal `(P a b)` is answered by **entailment**: it holds iff every
relation still possible between a and b satisfies P —

```
possible(a, b) ⊆ denotation(P)
```

Base predicates denote singletons; **derived** predicates denote disjunctions, and so are
entailed by more networks than any base one. An emptied constraint means the connected
component holding it is unsatisfiable, and then no goal naming a node of that component is
answered ([below](#unsatisfiability-is-per-component)).

Four goal shapes, on which arguments are bound:

- **ground / ground** — a check: `[{}]` when entailed, nothing otherwise.
- **ground / variable** (either side) — enumerate the nodes, binding the variable to each
  entailed one.
- **two distinct variables** — enumerate the entailed pairs, off the diagonal, which a
  reflexive denotation would otherwise report for every node on its own.
- **one variable twice** (`(P ?x ?x)`) — the diagonal itself, so a denotation containing
  the identity answers every node and an irreflexive one answers none.

A calculus names the predicates whose `arg` declarations are narrower than its nodes
(`:typed`), and a positive goal on one is answered only over arguments those declared
types admit. A type admits a node unless the node holds a type the context sees as
disjoint from it. The interval calculus names `subintervalOf` and
`properSubintervalOf` ([time.md](time.md)). Refutation reads the network alone.

The admission reads the absence of a disjoint membership, and no support handle names an
absence. So a membership of a type a separation holds apart from a declared type, arriving
or leaving, queues every rule with an antecedent on the predicate for a re-check and a
fresh join, and every rule whose exception mentions the predicate for a re-check
(`special/recheck-typed-admission`); a `genl` edge into such a type queues the same rules.
The re-check withdraws a firing whose arguments the declared types no longer admit at its
placement context (`chain/entailment-withdrawn?`).

A positive goal on a **super-predicate** of a calculus predicate is answered by lifting:
`(genl subintervalOf subtimeOf)` and `(genl subtimeOf partOf)` make every entailed
`subintervalOf` tuple a `subtimeOf` and a `partOf` tuple, so a `subtimeOf` or `partOf` goal
is solved as one goal per calculus predicate below it that the context sees. A lifted goal is answered at completeness 50, beside the super-predicate's stored
tuples and its other specs. Lifting is the prover's alone: forward chaining claims an
antecedent by a calculus predicate (`qcn-kb/calculus-for`), so a forward rule on `partOf`
does not join on an entailed `subintervalOf` tuple.

### Unsatisfiability is per component

The constraint graph of a network joins two nodes when a recorded pair names both, and its
connected components (`qcn/components`) are independent: a pair between two components is
the universe, and the universe composes to itself, so the pass over one component narrows
nothing in another. When the pass over the whole network empties a constraint,
`qcn-kb/split` runs the pass over each component and blocks the nodes of each component
whose pass empties one (`qcn-kb/blocked-nodes`). No goal naming a blocked node is answered,
in any of the four shapes, and no variable binds one. Every other goal is answered off the
pass over the satisfiable components, as in a satisfiable network. An algebra whose
universe composes to less than itself can leave the satisfiable components unsatisfiable
together, and the whole network is then one blocked component.

A term no fact names lies in no component, so `(subintervalOf D D)` holds of such a `D`
beside a contradiction between `A` and `B`. The `reflexive` and `transitive` declarations
on a calculus predicate keep their provers (`ReflexiveProver`,
`TransitivePredicateProver`), and those answer no goal naming a blocked node either
(`provers/unblocked`). A goal that a rule concluding the predicate sends down the union
path therefore gets the answers the calculus gives alone.

The verdicts on the whole network stay whole: `inconsistent?`, `unsatisfiable-somewhere?`,
`qualitative-network`'s `:consistent?`, the scenarios and the violations entry report a
network with one unsatisfiable component as unsatisfiable, and a forward re-join over one
joins every pair (`join-delta`'s `:all`). The split runs one pass per component when the
whole network is unsatisfiable and none otherwise. Each component's pass is memoized in
`:pc-cache` on its network value, and the split is resident beside the network under the
change clock.

### A network can have a second reader

Stored facts of the calculus are one source of constraint on a pair, and they need not be
the only one. A calculus may carry a **narrowing**: a function of the KB and the context
(`:fn`), or of the network's node set alone (`:over-nodes`), answering the same `{:net …
:support …}` a read produces, which `build-network` folds in by intersecting each pair's
constraint and unioning each pair's support. A node-set narrowing is also run over the
nodes a goal names and no fact does, so what it says about a node reaches a question about
that node. A calculus whose nodes are not all symbols names its node test (`:node?`). A
narrowing names the dynamic vars it reads (`:bindings`), and their values are part of the
resident network's key, so a read under a rebound var reads that binding's network.

Two calculi carry one. The interval algebra reads the metric temporal layer
([stp.md](stp.md)) — an interval is bounded by two instants, so a numeric bound on the gap
between two intervals' endpoints rules out Allen relations no stored fact mentions — and
the point network, where instant facts over two things' start and end points do the same.
The metric reading snaps magnitudes to `provers/*quantity-tolerance*`, which is its one
binding.
The point algebra reads its own node terms: a thing's start before its end, and calendar
moments in calendar order ([time.md](time.md), "The points of a temporal thing"). Nothing
about the pass, the entailment reading or the support changes for either — what all three
consume is one network value either way. The delta join changes for a node-set narrowing
alone. A goal naming a node no fact states is answered over the network extended by that
node, and `join-delta` measures the network without it, so no moved pair holds the node.
`solve-goal` therefore enumerates such a goal in full on every re-join, and a rule on
`(instantNotEqual ?x (InstantFn 2000 1 1 0 0 0))` fires for each dated fact in every
arrival order.

Three things make the fold sound rather than merely convenient:

- **It only narrows.** Intersection is commutative and associative, so the network is a
  function of what both readers saw and never of which ran first. A pair the narrowing
  leaves at the universe it does not record, which is the same claim as recording it. An
  unsatisfiable component of the source network, or a refused source, empties pairs
  joining the nodes whose endpoints it holds (`stp/unsatisfiable-narrowing`), so the
  component of the network reading it that holds those nodes is unsatisfiable too and
  answers no goal naming one. Answering nothing from the source instead would widen the
  network when a fact arrives, and a firing resting on an entailment the widening lost
  would stay believed, since `chain/entailment-withdrawn?` withdraws on a blocked node and
  on a typed argument no longer admitted, not on a widened network. The emptied pairs are
  a **stand-in** for the source's clash, and no fact of the calculus contradicts them, so
  `qualitative-network`'s `:unsatisfiable` and the ledger entry's `:pairs` leave them out.
  The narrowing describes the source instead (`qcn-kb/unsatisfiable-sources`), one
  description per unsatisfiable component of it, and `qualitative-network` answers the
  descriptions as `:unsatisfiable-sources`: the source network (`:metric` or `:point`),
  the component's pairs unsatisfiable as written, the instants on a negative cycle for
  `:metric`, and the handles of the facts behind them. A component of the source network
  holding no node's endpoint empties nothing and is not described. A refused
  `:metric` source names its `:dimensions` instead of pairs and a cycle.
- **It carries support.** A pair narrowed by a second reader names the facts *that* reader
  read, so a conclusion drawn through it is withdrawn by retracting one of them, exactly as
  a conclusion drawn through a stored fact is. A node-set narrowing reads no fact and names
  none: the terms fix what it adds, and no retraction can move it.
- **Its sources are declared.** What moves a network is wider than what the calculus
  answers, and a datum on one of the narrowing's `:sources` re-checks and re-joins the rules
  carrying an antecedent of the calculus — the same job `SupportingProver`'s
  `support-sources` does for a computed antecedent ([inference.md](inference.md)). Without
  it a constraint stated after the rule and the facts would never reach a join, and the same
  three sentences would derive a conclusion or not depending on which arrived last. One
  predicate can move two networks — an instant fact is answered by the point network and
  read by the Allen one — and a datum on such a predicate re-joins the rules of both. A
  narrowing also names the subset of those that puts a **node** into a network, which is
  what makes a context worth reading one at (`reader-contexts`).

Each direction is folded **as given** rather than mirrored through the algebra's converse,
which is the one way this differs from absorbing a stored fact: a narrowing answers ordered
pairs and answers both, so mirroring would intersect a pair with the converse of a claim
about itself.

## Negation: refutation, and negative facts as constraints

The base relations are jointly exhaustive and pairwise disjoint, so **exactly one** holds
of any pair. That is what makes a negation informative here where the engine's
open-world default rightly refuses it elsewhere: "not P" is not an absence of knowledge,
it is the constraint "one of the relations P does not denote". Both directions of that
are wired.

**A negative goal is answered by refutation.** `(not (P a b))` holds iff *no* relation
still possible between a and b satisfies P —

```
possible(a, b) ∩ denotation(P) = ∅
```

Note the asymmetry with the positive reading, which needs containment where this needs
disjointness. A pair the network leaves genuinely open satisfies neither, and answers
nothing either way. So a chain of NTPPs answers `(not (spatiallyDisconnected A D))` as
readily as it answers `(partOfRegion A D)` — the composition determined the pair, and DC is
not in what is left. The soundness runs one way only: **a refutation is real, and a
failure to refute is still "not provable", never "provably true".** All four goal shapes
behave identically under either polarity.

A negative goal reaches the prover in the form the caller wrote it, `(not (P a b))` —
the same surface convention `FactProver` hands to `matches-visible`, which reads the `not`
frame as the pattern's polarity.

**A negative fact is a constraint.** A believed `(not (P a b))` intersects the `(a b)`
constraint with the **complement** of P's denotation, and `(b a)` with the complement of
the converse — which is the same thing, since converse is a bijection on the base
relations and so commutes with complement. So `(not (regionConnectedTo A B))` rules out
all seven relations C denotes and leaves `#{:dc}`, and a *negative* fact has entailed a
*positive* goal nobody stated. Order-independence survives unchanged: intersection is
still commutative and associative, and a complement is a fixed function of a denotation.

A negative fact that empties a constraint — `(nonTangentialProperPart A B)` alongside
`(not (partOfRegion A B))` — is an inconsistency, and it reaches the violations ledger
through the existing `unsatisfiable-as-given?` path with no special case. Nothing outside
the calculus sees that clash: the two are different predicates, so there is no nogood, no
defeat, and both stay believed. Only the network knows they cannot both hold.

**So a negative fact owes every trigger a positive one owes**, and the one thing standing
in the way is its own functor. A calculus is claimed by a *predicate*, and `(not (ntpp A
B))`'s outermost functor is `not`, which claims nothing — so both places that ask "did a
fact of some calculus just arrive?" read the sentence's **body under the `not`** before
asking which calculus claims it. `special/recheck-on-qualitative` is handed
`sentex/underlying-body`, the same peel the predicate-keyed re-check trigger takes;
`chain`'s per-datum test compares the functor first and pays `kb/body-under-not` only for
a `not`, which reads the already-canonical stored sentence structurally where
`underlying-body` would rebuild and re-intern it to answer the same question.
Those two are the whole of it: `chain`'s re-join, which is what finds the relation a
negative fact has newly entailed, and `special/recheck-on-qualitative`, which is what puts
a firing in front of `entailment-withdrawn?` when a negative fact is what made the theory
impossible. Miss them and the arrival order of a rule and a negative fact decides what the
KB believes — a network that answers `(not (regionConnectedTo A D))`'s entailment to `ask`
while no forward rule ever fires on it, and an unsatisfiable network still licensing the
conclusion it drew before.

The negative half of the read is fetched differently from the positive half, for an index
reason stated here. A negative fact's trie key carries its whole body as a single token
(`[:false (P a b) ctx]`), so the trie answers a *ground* negative lookup and nothing else
— an open `(not (P ?a ?b))` compares the token `(P ?0 ?1)` against `(P A B)` and matches
nothing. The **predicate extent** indexes either polarity under the positive body's functor,
so that is what enumerates them, with belief, context visibility and `except` removal
applied exactly as `matches-visible` applies them to the positive read. It is the
predicate's own extent, with no fan over the genl spec closure — under negation
subsumption runs the other way (a negated *super*-predicate entails the negated sub, never
the reverse), so the positive read's spec fan would be unsound, and nothing is lost
because a wider predicate contributes its own larger complement when it is read in turn.

## Support: what an entailed relation rests on

`path-consistent-with-support` carries `{[i j] → #{handle}}` alongside the constraints. An
**asserted** constraint's support is the handles of the sentexes the reader intersected
into it, and for a fact read on a sub-predicate the `genl` edges of one path from its
predicate, so a conclusion drawn over the pair goes when the edge does; a **tightened** one's is the union of the supports of the two constraints that
composed to narrow it, plus its own prior support. `qcn-kb/support` asks it of the KB —
"which stored sentexes support this entailed relation?" — and `qcn-kb/inconsistency-culprits`
asks the same of the pair that emptied in an impossible network. `qcn-kb/closure-with-support`
answers the whole pass at once, for a caller reading many pairs: the interval network's
point narrowing reads 4n² comparisons and their support off it for n things
([time.md](time.md), "The points of a temporal thing").

```clojure
(qkb/support space/rcc8 kb 'CxUniverse 'A 'D)   ; => #{h1 h2}, the chain behind A ⊏ D
```

The calculus prover is a `SupportingProver`, so an `argue` leaf it answers names that
support ([inference.md](inference.md#an-answer-no-record-holds)), with the `genl` edges a
lifted goal climbs and, on a positive diagonal, the `(reflexive P)` statements the context
sees.

Two things it is **not**, and both matter.

It is not **minimal**. Support accumulates on every narrowing, so a pair narrowed twice
keeps the first narrowing's support even where the second subsumed it.

It is not **every** derivation. Support propagates only where a constraint *moves*, so a
second route that re-derives a value a first route already reached contributes nothing:
what comes back is *a* witness, not the set of all of them. That is deliberate, and it is
exactly what a justification is — one support list, with a second derivation earning a
second justification rather than a longer one. Unioning across re-derivations would mean
iterating the support system to its own fixpoint over every triple whether or not anybody
asked. So retracting the reported set destroys *that* derivation; where the network has an
independent second route the relation survives, and asking again names the survivor.

And it is the witness **the route the fixpoint took** accumulated, so which triples the
pass visits in which order decides which handles come back. The tightened network cannot
move — it is the unique greatest fixpoint — but the support can, and a change to the
driver's cost decisions moves it. It stays a deterministic function of `[network,
asserted support]`, which is what order-independence needs: the same believed facts name
the same handles however they were asserted. It is not additionally stable across engine
versions, and nothing should be built on a particular witness.

The direction a caller needs is guaranteed: every handle named is a sentex really
read into this network, and the reported set is enough to have produced the relation on
its own.

The pass is memoized in the calculus's own `:support-cache`, keyed on the network **and
its asserted support** — where `tighten`'s key is the network alone. That difference is
required: retracting a fact and re-asserting the same sentence yields the identical
network at a different handle, so the network alone does not determine the support.

Which pair is blamed for an inconsistency only *composition* finds depends on which one
the fixpoint empties first, so the culprits are a diagnosis rather than a canonical
explanation — the verdict does not depend on that, only the blame does. That is why the
violations ledger records `unsatisfiable-pairs`, a function of the network alone, and
leaves the culprit set to a caller who asks for it.

**Reporting an impossible network.** When the pass returns `:inconsistent`, the calculus
appends a `:qualitative-inconsistency` entry to the KB's violations ledger — the
`(violations kb)` a caller already reads — naming the calculus, the context, the nodes,
and the pairs that are unsatisfiable *as written* (absent when only composition found it).
When a narrowing's source is unsatisfiable, the entry's `:sources` carries the source
descriptions `qualitative-network` answers as `:unsatisfiable-sources`.
Otherwise a KB with an impossible component answers nothing about its nodes and says
nothing about why.

**The settle asks every write.** A settle whose relabelled region holds a believed fact
that moves a registered calculus (a fact on a predicate the calculus triggers on, a `genl`
edge into one, or a `genlCx` edge) asks each governing context of that calculus whether
its network is unsatisfiable (`qcn-kb/report-moved!`). The entry is therefore filed by the
write that made the network unsatisfiable, whether or not a rule or a read consults the
network. A KB with no calculus registered runs no check.

The settle records each governing context's pass, and the next settle closes it again
from the constraints its region adds (`qcn/path-consistent-from`, seeded at the pairs they
narrow), with no network read. That holds when every member of the region is a believed
fact of the calculus, a rule, or a fact on a predicate the calculus does not trigger on
and the engine does not read (core.txt's types and inert terms excepted). A region holding
anything else (an OUT member, a `genl` or `genlCx` edge, an `except`, a defeat, an equality
edge, a fact on a sub-predicate), and every region of a calculus with a narrowing (`:allen`,
`:point`), reads each governing context's network whole. A pass that closes
`:inconsistent` is read and tightened whole, which files the entry and replaces a recorded
pass that a withdrawal the region does not show left too tight. A fact a governing
context does not see adds nothing to that context's pass. A plain
listener's feed event carries the entry under `:unsatisfiable`, once per
network per KB and context under a marker of its own (`qcn-kb/fed-inconsistencies`). A
standing query's event carries none, since `watch` refuses a goal a calculus answers
([feed.md](feed.md#what-is-refused)).

**The feed event is the record a caller reads forward.** The ledger is in memory, holds
its newest 1000 entries, is not persisted and has no cursor. A daemon subscription keeps
the events in a ring a cursor reads, and its `:lagged` count names the events the ring
dropped ([feed.md](feed.md#across-the-wire)).

**`try-assert` refuses the write.** After the write stores, chains and settles,
`try-assert` looks for an unsatisfiable component, at a governing context of a calculus the
write moved, whose support-carrying pass blames a sentex the write premised newly or a
conclusion its firings placed (`qcn-kb/unsatisfiable-write`). A context whose recorded
pass is satisfiable, with no mutation since the settle, is not read. The first such component
refuses the write as `:definitional-clash` with `:violation :unsatisfiable-network`, and
the write is taken back. `:clashes-with` names the other blamed facts, and `:detail` the
calculus, the context, the component's nodes and its pairs unsatisfiable as written. A
component the pass blames on none of the write's sentexes was unsatisfiable before the
write, and does not refuse it. `{:refuse-unsatisfiable? false}` skips the check. A
`genlCx` edge that puts two satisfiable networks into one unsatisfiable reader is stored:
the blame names facts and never an edge.

It is deliberately **not** a `wff` check. [why not a wff
check](defenses.md#an-impossible-network-is-reported-off-the-pass-not-thrown-as-a-wff-check)

The entry is filed once per network **per KB and context**, which is not the same thing as
once per pass. The pass is memoized on the network *value* and so is shared — two contexts
seeing the same constraints, or two KBs holding them, run it once between them — and a
report riding on it would fire for whichever asked first and leave the rest answering
nothing with an empty ledger to explain it. So it hangs off `observe/newly-seen?`, which
asks whether *this* KB has said *this* about *this* context yet. A query loop still reports
once, and a change of belief yields a different network and reports again. The network
reported is the one the believed facts give, never one a goal's nodes extended: a goal
first tightens the network as read, and when that network is unsatisfiable, extends only
its satisfiable components, which the pass does not report. Queries naming different
goal-only nodes therefore neither re-report nor list those nodes.

**Cost, completeness, registration.** `cost` is **`:compute`** — a fixpoint over the
stored facts before the first answer, a closure rather than a search. `completeness` is
**100**: nothing else reasons about these predicates, and the answer is a property of the
*whole* network rather than of any one stored fact, so the dispatcher runs the prover
alone and a raw fact match would add nothing it does not already entail. `est-bindings`
is bounded by the node count, itself bounded by the number of stored facts on that
prover's own predicates — a sum of O(1) predicate-extent reads, because an estimate must not
cost what it estimates.

A believed `(inverse P Q)` between two predicates of one registered calculus leaves the
prover answering alone when the algebra's converse of `Q`'s base relations lies inside
`P`'s (`qcn-kb/converse-entailed?`): the network reads both predicates and applies the
converse itself. An `inverse` naming a predicate outside the calculus is a source the
network does not read, and `provers/shadowing-channels`' `:inverse` channel sends the goal
to the union of every applicable prover.

Three caches, answering different questions:

* the **pass** is memoized on the network **value**, in an atom the calculus owns. Sound
  because the network is derived from the believed facts: any change to them yields a
  different map and so a different key. The key is the network alone, not the node set —
  a node the goal names but no fact mentions is isolated, every constraint it takes part
  in is the universe, and the universe composes to itself, so it can tighten nothing.
* the **network read is resident**, on the KB's own `:qcn` atom, keyed `[calculus context]`
  plus the values of the narrowing's `:bindings`, and keyed by `observe/change-clock` —
  the KB is read once and the network reused until the engine mutates something. See the
  next section.
* the **support-carrying pass** has its own atom, so an ordinary query never pays to
  propagate support nobody asked for. Its key is the network *and* the asserted support,
  for the reason given above.

Both passes are held **resident in front of** their content key as well, and that is a
cost fix rather than a second cache: a network is a map with an entry per node pair, so
looking one up *as a key* costs a full map comparison at every hit — at a hundred nodes,
more work than the read it was saving. A resident network is the same object read after
read, so `identical?` settles it in a reference compare. It stays a fast path and never an
authority: a caller passing some other network falls straight through to the content key
and is answered about the network it actually asked about.

## The network is resident, and the clock is what makes that sound

A network is read out of the KB once and then lives on the KB until the engine mutates
something. What decides "until" is `observe/change-clock`, a single global counter bumped
at three kinds of place:

* a sentex is **stored** (`kb/create-sentex`) or **leaves** (`integrate/sentex-removed!`);
* any mutating **`jtms`** entry point runs — every one of them, bumped on the wrappers
  rather than inside the two representations, so one bump apiece is exhaustive by
  construction and neither representation can forget one;
* the **taxonomy** is written, by a watch on its atom rather than a bump per mutator —
  there are nearly thirty of those, and the point of a clock is that no write can forget it.

Two bulk operations bump it by hand, because they move a whole store without passing
either choke point: `core/clear!` and `reindex/reindex`.

Between them those cover what a network is a function of: which sentexes exist, which of
them are believed, and the `genlCx` ancestor set and `genl` spec fan the read looks through.
The narrowing's `:bindings` are the one other input, and the key holds their values. So an
unmoved clock under the same bindings says rebuilding would produce the identical map.

The clock is deliberately **coarse** — it says only that something moved, never what, and
not even in which KB. A network is therefore re-derived more often than it strictly must
and never less, which is the direction a correctness argument wants: residency is reused
only across a stretch in which the engine performed no mutation at all, and that is
exactly the stretch a settle pass, a query, or a prover loop spends reading. Making it
finer would mean deciding, at each choke point, which caches a change is relevant to —
the judgement that gets a cache wrong.

The clock is the only invalidation here. The expensive *derivations* over a resident value
stay keyed on that value, so two KBs that reach the same network still share one pass; this
layer is about not reading the KB again, and reading the KB again is a per-KB question.

**A write reads the network again, and an equal read keeps the resident value.** Every
write moves the clock, the arriving fact's own included, so on the write path each
consultation reads the network again, linear in the calculus's stored extent. A read equal
to the resident value in both the network and its support answers that value
(`qcn-kb/read-network`), so a write that did not move a network leaves the same object
resident. Each pass over it then answers by `identical?`, and `join-delta` reports no
moved pair without comparing the n(n−1) pairs a chain of n regions closes to. `lein
perf`'s `qcn-arrival-beside-an-unmoved-network` bounds an arrival in a sibling context of
such a chain at 2.5× over 6× the regions; the pair-by-pair comparison reads 4.3×. The read
itself stays. Invalidating finer than the clock would need every relabelled handle tested
against the calculus's extent in both TMS representations, and the standing nogoods, the
stored `except`s and the merges besides.

**One thing the clock cannot supply**, and it is the reason `observe/*held-values*` exists.
Forward chaining writes while it reads: a rule's join is a lazy seq, and each solution
taken off it is *placed* — a store and a justification — before the next is realized. With
the clock as the only cache key, such a join would re-derive the network per solution and
join half of its bindings against a state the other half never saw. So the resident values
are **held fixed** for the length of one agenda datum (`chain/process-datum`) and one backward
search step (`observe/with-search-scope`). That is not an
approximation of the fixpoint,
it *is* the fixpoint: an immediate-consequence step is by
definition computed from one
state, and what a step enables is picked up by the next round
rather than mid-step. Outside such a scope there is nothing to hold fixed and the clock
answers alone.

Residency is **not** conditional on a prover being registered. `qualitative-network` and
`possible-relations` are reads, and a network is a property of the stored facts whether or
not anybody opted in to reasoning with it.

`vaelii.impl.stp`'s metric network is resident on the same atom under a key of its own,
for the same reasons. The **join baseline** is kept apart, in the KB's `:qcn-joined` map,
because it outlives a clock tick: it says what has changed since a moment the clock has
moved past ([below](#the-re-join-is-semi-naive-over-the-pairs-that-moved)). The resident
atom's wholesale clearing at its bound leaves it in place, and `core/clear!` empties it.
Losing one costs one full re-join. The map holds one entry per calculus and reader
context and is never trimmed.

Each prover is **opt-in**, on top of a vocabulary that is itself a separate upper
context, and they are independent: register any, all, or none. A KB that loads the
vocabulary without a prover stores and retrieves the facts as ordinary facts, without
paying for a network:

```clojure
(v/add-reasoner kb :rcc8 :cardinal :allen)         ; topology, direction, intervals
(v/reasoners)                                      ; the list, sorted
```

`add-reasoner` names them, so opting in needs nothing from `vaelii.impl.*` — the
provers themselves are impl values, and a subsystem only reachable past the public
boundary is one an embedding application cannot ask for. It resolves every name before
registering any (a typo registers nothing) and is idempotent per reasoner: sameness is
the prover **value**, since the six algebras share one record type and differ only in
the calculus they carry. `(v/reasoner :allen)` hands back the prover itself for a caller
assembling a registry of its own, and `add-prover` still takes any `Prover`.

## What a registered prover is reachable from

Registration puts the prover in the KB's own list, and several parts of the engine read
that list rather than the shipped default — so the reach is wider than "answers `ask`":

- **`ask` / `query-plan` / the level stack.** Level 6 (`:solved`) is the registry, so a
  qualitative goal is answered there.
- **Rule antecedents, backward.** A backward search discharges each antecedent through
  the registry at its leaf, so a rule can join on a relation the network entails and
  nobody stored.
- **`exceptWhen` and `unknown`.** Both evaluate at level 6, so a rule can state its
  exception as a qualitative goal — "birds fly, except when the bird is a proper part of
  the cage" works on a containment the network composed.

**Forward chaining too, on a relation nobody stored.** A forward rule's antecedents are
matched against stored facts, and an entailed relation is not one — it has no handle, so
on its own it gives a justification nothing to rest on, and a conclusion nothing can
withdraw is worse than a conclusion never drawn.

Support is what closes it, and the shape is smaller than materializing anything. The join
does not store the entailment; it contributes the **handles the entailment rests on**.
`chain/solve-qualitative` answers a qualitative antecedent by entailment and hands back
`support` as the firing's antecedent handles, so the conclusion is withdrawn when any
fact behind the entailment goes — the same contract an ordinarily matched antecedent has.
A **negated** qualitative antecedent is matched only: what a refutation rests on is the
whole network rather than a support list, so `chain/qualitative-antecedent` claims a
positive binary literal alone.
Nothing is materialized, so the O(n²) relations a network entails add no work until a
rule asks for one.

Three things follow, and each needed its own wiring:

- **The trigger index cannot see it.** A rule is fired by a datum whose predicate keys it,
  and a new `nonTangentialProperPart` fact licenses a `partOfRegion` antecedent — two
  predicates unrelated by `genl`, so the index would never connect them. A qualitative
  fact therefore re-joins every forward rule mentioning *any* predicate of its calculus,
  rather than firing one at a trigger position, since the arriving fact need not unify
  with the antecedent it enabled. Bounded by the rules that mention the calculus at all,
  and narrowed to the pairs that moved
  ([below](#the-re-join-is-semi-naive-over-the-pairs-that-moved)). A fact on a
  sub-predicate of a calculus predicate is a fact of the calculus, since the network reads
  it through the matcher's spec fan, and a `(genl sub super)` edge moves what a `super`
  fact does: `qkb/calculi-triggered-by` reads a predicate's `genls` closure, and the
  re-join and the re-check below both ask it, of an edge's supertype for an edge.
- **Union, not replacement.** The ordinary matcher still runs; entailment is added to it.
  Entailment subsumes assertion, but the two disagree at the edges — a literal whose
  arguments are not network nodes is outside the calculus — so nothing that fired before
  stops firing. Duplicate justifications from the two routes are set-deduped by the TMS.
- **An unsatisfiable network withdraws what it licensed**, and the justification's
  antecedents cannot say so. Adding a constraint only ever *narrows* what is possible, and
  narrowing makes a positive entailment more likely rather than less — so an entailment is
  never lost by learning more. The right to use it is what is lost, when the facts turn out
  unsatisfiable: the supporting facts are all still believed, and some *other* fact made
  the component holding the antecedent's nodes impossible. So a firing whose calculus
  antecedent names a blocked node at its placement context
  ([above](#unsatisfiability-is-per-component)) is **blocked**, exactly as an `exceptWhen`-excepted
  one is (`chain/entailment-withdrawn?`, queued by `special/recheck-on-qualitative`), which
  means it is also *revived* by the same machinery when the clash is retracted. A settle
  puts a standing firing in front of it only while some network is unsatisfiable, or when
  the firing is blocked already
  ([exceptions.md](exceptions.md#two-withdrawals-a-firing-carries)), so an arrival over a
  satisfiable network re-decides none of them.

The **diagonal** rests on the `(reflexive P)` statements the reader sees
(`res/declared-by`). With `(reflexive partOfRegion)` visible, a forward rule over
`(partOfRegion ?x ?x)` fires once per node of the network. The firing rests on every visible
declaration and on a fact naming the node, one justification per such fact
(`qcn-kb/node-statements`), so it is placed where the node is, and retracting the
declaration withdraws every one. In the join two distinct variables answer the diagonal too,
unlike a query's four goal shapes ([above](#what-every-algebra-does-with-it)), so the
antecedent that binds first decides no firing. A term no fact names, a node only a narrowing
names included, gets no diagonal firing, even where an earlier antecedent binds it. A
diagonal the algebra alone gives, on a predicate holding the identity with no declaration
(`hasRegionPart`), supports nothing and is dropped rather than answered with a groundless
justification. An arriving `(reflexive P)` re-joins every rule with an antecedent on `P` in
full (`chain/reflexive-rejoin-rules`), and a delta re-join adds the diagonal of each node
its moved pairs name.

Support names *a* witness rather than every witness (above), so a relation reachable two
ways gets one justification; the second route is re-derived after a retraction rather than
having been recorded in advance.

#### Which networks it joins against

There is one network per **reader**, not one per context that holds a fact, and the
difference is the whole of `qcn-kb/reader-contexts`. A reader sees the entire
`genlCx` ancestor set above it, so a context inheriting two contexts holds both their
facts in one network and composes what neither composes alone — `(ntpp A B)` in one and
`(ntpp B D)` in the other entail `A ⊏ D` for that reader and for nobody else. `ask`
answers there, because a query is asked *from* a context; a re-join has to be told
which contexts to stand in.

A fact-holding context stores a fact that puts a node into a network: a fact on a calculus
predicate, on a sub-predicate of one, or on a predicate the narrowing names (`:contexts`).
A context storing a `genl` edge into such a sub-predicate counts too, because the edge
decides whose facts a reader's spec fan reads. `unsatisfiable-somewhere?` reads the same
set over every predicate that moves a network (`qcn-kb/held-contexts` answers both). The
fact-holding contexts are read from the store rather than from belief, so a context
whose only fact of the calculus is defeated is enumerated and reads an empty network. The
set is resident on the `:qcn` atom under the change clock, and chaining memoizes it per
agenda datum besides (`chain/*qcn-contexts*`; `chain/process-datum` binds it).

So the set is the fact-holding contexts **closed under where they meet** —
`taxonomy/meet-closure`, which is `maximal-common-descendant-contexts` over pairs to a
fixpoint, the same primitive placement uses ([contexts.md](contexts.md), where the
closure argument and its cost live; equality's migration is the other caller). A context
maximal for no subset costs one network read and cannot cost an answer here, because a
more specific reader sees a superset of the facts and narrowing only ever adds
entailments.

**A calculus whose facts are all in one context takes neither step**, which is every KB
that has not divided its spatial or temporal claims between contexts: with one fact
context there is nothing for a second to meet.

The same set answers a second question, which is why it lives in `qcn-kb` rather than in
the chainer. A goal whose context is a **variable** means "in some context", as it does
for every other prover, and it is answered by fanning the prover over the readers and
unioning their answers — never by reading every context's facts into one network, and
never by reading wherever happens to be convenient. [why the reader set is exact, not a
convenience](defenses.md#a-variable-context-goal-fans-over-readers-rather-than-reading-one-unioned-network)
The union network is still what `qcn-kb/network` returns for a variable context, and it is
a diagnostic reading of everything stored rather than anything a reader sees; no goal is
answered off it. Placement is unaffected either way: a conclusion is placed from the
contexts of its support handles, so one solved at the meeting context lands there because
the facts that entailed it meet there.

### The re-join is semi-naive, over the pairs that moved

A qualitative fact cannot be matched at a trigger position, so every forward rule
mentioning its calculus is re-joined when one arrives. Joining over *every* pair the
network entails means the *n*th fact redoes the O(n²) work the (n−1)th already did — every
conclusion of it a duplicate justification the TMS dedups, correct and entirely wasted.

So the join runs over the **delta**: the pairs whose entailment has moved since these same
rules were last joined (`qcn-kb/join-delta`, `chain/rejoin-qualitative`). A pair that has
not moved licenses exactly the firings it licensed then, and those were derived then.

Three things make that sound rather than merely plausible.

**The baseline is the last *join*, not the last pass.** Those are different moments — a
query, or a settle's `entailment-withdrawn?` re-check, runs a pass without joining anything
— so the warm start's own seed set, which is exactly the delta against the last pass, is
deliberately *not* what is reported here. The baseline is recorded by the one caller that
re-joins all the rules at once, and by nothing else: a single rule's full join when that
rule arrives does not, or the next delta would claim the others were covered too.

**A moved constraint is not the only thing that moves a firing** — the handles behind it
count as well, and cannot be diffed pair by pair, since a derived support is a union along
whatever chain narrowed it and a handle swapped out at one pair moves the support at pairs
that did not themselves move. So that half is answered coarsely and from the input: if the
handle set the network was read out of has **lost** a member, the delta is `:all` and the
re-join is full. Losing one is what invalidates a justification and sweeps a conclusion,
which is the case that must be re-derived; gaining one only ever adds a second route to
something already believed. That is also the whole of retraction's story here, and the same
boundary the warm-started pass has: what a widening invalidated is not computable from the
answer it invalidated.

**One antecedent is narrowed, not all of them.** For a rule with two qualitative
antecedents, narrowing both at once would drop every firing pairing a moved binding with an
unmoved one. So the join runs once per qualitative antecedent, each time with a different
one narrowed — the delta rule, `Δ(A ⋈ B) = (ΔA ⋈ B) ∪ (A ⋈ ΔB)` — and the overlap
re-derives conclusions the TMS dedups.

The narrowing does change the **number of justifications**, and only downward. A
full re-join would record a fresh witness for a conclusion every time the support-carrying
pass happened to pick a different one, so a conclusion would accumulate alternate supports
as a side effect of redundant joining; the narrowed join records a subset of them. Belief
is identical either way — pair for pair, conclusion for conclusion, across a mid-load
retraction — and every conclusion keeps at least one justification. What the narrowing
drops is redundancy the stated contract never promised: support names *a* witness rather
than every witness ([above](#support-what-an-entailed-relation-rests-on)).

`qcn_integration_test` asserts both halves separately, because "the conclusions are right" is
also what a delta that always answered `:all` would produce. Three tests compare an
interleaved load against a deferred one and against a KB that saw only the survivors of a
retraction — including the rule with two qualitative antecedents, and a second calculus,
since nothing here knows an algebra. Three more are about the delta itself: `:all` until a
baseline exists and empty immediately after one, `:all` again when a handle is retracted or
defeated out of the network, and empty in a sibling context the arriving fact is invisible
from. One counts what the join enumerated — thirteen regions in a chain entail 78 nested
pairs and an arrival answers at most 26 of them. And one grows a chain split across two
contexts a fact at a time, since the contexts a delta is taken for and the contexts
the join runs against have to be the same set.

Over the protocol as a whole the guard is an **order oracle**, because every failure here is a
missing answer rather than a wrong one, and a KB that is merely less informative than it
should be reads as correct against anything except another order of the same content. So a
rule, four facts of mixed polarity, two contexts and the context below both are
asserted in eight seeded orders into a KB built from nothing each time — rules permuted
along with facts, since "the rule arrived last" is what a rule's own full join would
otherwise paper over — and every order must reach the identical derived set, placement
contexts included.

**Cost at load, measured.** None of this runs until a calculus prover is registered *and*
a forward rule mentions one of its predicates — registering a prover alone changes
nothing, which the numbers below confirm. Loading a containment chain of *n* regions, by
`lein bench-qcnchain`:

| regions | no prover | prover, no rule | prover + rule | deferred chaining |
|---------|-----------|-----------------|---------------|-------------------|
| 10 | 1.3 ms | 1.2 ms | 12 ms | 17 ms |
| 20 | 1.7 ms | 1.7 ms | 19 ms | 29 ms |
| 40 | 3.1 ms | 3.0 ms | 81 ms | 100 ms |
| 80 | 5.5 ms | 5.8 ms | 528 ms | 647 ms |

The cost grows faster than the input and slower than *n*³: 40 → 80 regions is 2× the
facts for 6.5× the time — super-quadratic (4× would be quadratic), sub-cubic.
`lein perf`'s `qcn-chain-load` reads the prover + rule column per fact at 20 and 80
regions, and holds it under 40× for the 4× step, under the 64× a cubic pass reads. At 80 regions the network reads are
about 3% of that load, and the two passes below most of the rest.
Deferring the chaining is no penalty, because the one big datum it produces
joins over a delta like any other.

Three things hold that shape, and the order of them is the useful part. **The read is the
first half, and it is not the pass**: without residency a load pays a full network read
per consulting call — seventeen thousand of them against thirty-nine asserts at 40
regions, where the pass itself costs about a millisecond of the seventy an assert takes.
Residency takes those seventeen thousand to seventy-eight. Two regression tests enforce that, from
the two sides a cost has: `qcn_chain_test/network-reads-grow-with-the-calls-and-not-with-the
-asserts` counts the builds (exact, and blind to a loaded box), and `lein perf`'s
`qcn-network-residency` prices a repeated consultation against 8× the stored extent of the
calculus the asking context cannot see. Neither subsumes the other — a count cannot see a
slower read, and a ratio cannot see a constant. **Then the pass**, which
warm-starts ([above](#warm-starting-semi-naive-over-the-network)). **Then the join**,
which is this section.

**The support-carrying pass is what none of that reaches**, and it is the one that cannot
warm-start. The plain pass costs a delta; the support pass runs whole, once per arriving
fact, because keeping the supports a previous run accumulated would make which handles a
firing rests on a function of arrival order. Counted at 80 regions it is 79 passes and
2.7 s against the warm-started plain pass's 78 and 0.4 s — the instrumentation inflates
both absolutes, so read the ratio, but nothing else in the load is near it.

**Carrying the support is not what makes it expensive.** Measured on the same network,
`path-consistent-with-support` costs **1.0–1.2×** what `path-consistent` costs — 1.01× on
the tree at every size, 1.10–1.18× on the total order. The union of handles at each
narrowing and the object array that holds them are a rounding error; what the support pass
pays for is the *tightening*, which it must redo from the raw network because supports
propagate only where a constraint moves. So it is not a pass that answers too many pairs,
it is a **cold** pass beside a warm one. Answering fewer pairs would buy the 10–20%;
answering them without a cold pass needs a support that is a function of the closed network
rather than of the propagation history, which is a different algorithm.

**Which shape a KB has decides all of this**, and the chain above is the worst one. The
same load over the branching-3 containment tree — the form a mereology KB really produces,
where only pairs sharing an ancestor line compose:

| regions | no prover | prover, no rule | prover + rule | deferred chaining |
|---------|-----------|-----------------|---------------|-------------------|
| 20 | 1.5 ms | 1.4 ms | 7.1 ms | 14 ms |
| 40 | 2.5 ms | 2.7 ms | 20 ms | 23 ms |
| 80 | 5.1 ms | 5.8 ms | 64 ms | 48 ms |

**8.25× cheaper than the chain at 80 regions**, and it is the same code — the difference is
entirely how much of the network the facts constrain. The table reports both columns: the
chain says what the worst case costs, the tree says what a KB is likely to pay.
