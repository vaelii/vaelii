# Scenarios — one arrangement out of a constraint network

- **Covers:** how `scenarios` extracts one concrete, deterministic arrangement
  from a tightened constraint network by fewest-possibilities-first backtracking.
- **Not here:** the path-consistency engine and entailment reading it searches over
  → [qcn.md](qcn.md); the spatial algebras it runs over → [space.md](space.md);
  the temporal algebras it runs over → [time.md](time.md).
- **Assumes:** constraint network, base relation, path consistency →
  [glossary.md](glossary.md).

Path consistency ([qcn.md](qcn.md)) answers what is *entailed*: a set of relations on every
pair, narrowed as far as composition allows. That is the right answer to "what follows?" and
the wrong shape for "show me". A drawing of the regions, a timeline of the intervals, an
example to put in front of someone — each needs a single relation per pair, not a set.

`vaelii.impl.scenario` extracts one. A **scenario** is a consistent choice of a single base
relation for *every* pair of nodes — a singleton-valued network that survives path
consistency, and so an arrangement nothing believed rules out.

```clojure
(scenario iv/allen kb 'CxUniverse)
;=> {[A B] #{:meets} [B A] #{:met-by} [A D] #{:equal} …}

(relations (scenario iv/allen kb 'CxUniverse))
;=> {[A B] :meets [B A] :met-by [A D] :equal …}
```

## The search

The search is ordinary backtracking with two refinements that bound it:

* **fewest possibilities first.** The most constrained undecided pair is chosen next, so a
  wrong choice is made where it is cheapest to be wrong about.
* **re-tighten after every choice.** A relation is chosen, path consistency runs again, and
  a choice that empties some *other* pair is abandoned at once rather than at the leaf.

A choice is made on a pair, never on a node, because a constraint network's variables *are*
its pairs. Pairs no fact reaches are decided too: they are as much a part of an arrangement
as the ones that were stated, and their constraint is simply the universe.

## Calculus-generic

`scenarios` takes a [qcn-kb](qcn.md) calculus, a KB and a context, so it runs unchanged over
RCC-8 topology, cardinal direction, Allen's intervals, the point algebra, and anything added
later. Nothing in it names a relation, a predicate or a table: everything it needs is on
`qcn` and `qcn-kb`'s public surface — the network, its nodes, a constraint, the converse, and
the pass.

`qcn-kb` takes the same arrangement: a new calculus is a table and a prover, and scenario
extraction, the caches and the entailment reading run over it with no further code.

## Determinism

The same believed facts give the same scenario every time, and two KBs built by asserting
the same facts in different orders give the same scenario as each other. Both orderings the
search makes break their ties on **content**:

| Choice | Ordered by |
|--------|-----------|
| which pair to decide next | fewest possibilities, then node order by how the nodes are written |
| which relation to try first | the relation's own name |

Neither ordering reads a handle id or map iteration order. Handles are allocated in
assertion order, so a tie broken on a handle would carry assertion order into the answer and
break order independence. The JTMS breaks its ties on content for the same reason.

The network itself is already order-independent: it is built by intersection, which is
commutative and associative, and path consistency computes the unique greatest fixpoint below
it. So everything downstream of the facts is a function of the facts.

## Laziness and bounds

The number of scenarios is **exponential** in the node count, so nothing here enumerates
eagerly.

`scenarios` is a lazy sequence — one scenario costs one path down the search tree, not the
tree — built with `res/lazy-mapcat` rather than `mapcat`, because each branch is a whole
subtree and chunked `map` would expand all of them before yielding the first answer. It takes
an optional `{:limit n}` for a caller who would rather say how many it wants than remember to
bound the sequence:

```clojure
(scenarios sp/rcc8 kb ctx {:limit 10})   ; at most ten
(take 3 (scenarios sp/rcc8 kb ctx))      ; the same thing, said by the caller
```

`scenario` is the first of them, and nil when there is none.

## Edge cases, and what they mean

| Network | Scenarios |
|---------|-----------|
| unsatisfiable | none — an arrangement nothing rules out cannot exist when everything is ruled out |
| fully determined by the facts and their composition | exactly one, equal to the tightened network |
| fewer than two nodes | exactly one, the empty scenario: no pair to decide is not the same as no arrangement |

## Checking one

The independent check on the search is to run path consistency over a scenario as a network
of its own and see that nothing empties — which is exactly what the search claimed it had
established at every step. `scenario_test` does that for every scenario it takes, on two
calculi.

Note what a scenario is *not*: path consistency is sound but not in general complete outside
an algebra's tractable subclass, so a singleton-valued network that survives the pass is one
no *local* reasoning refutes. For the algebras that ship, that is the strength of the
claim, and it is the same strength every other answer read off the pass carries.
