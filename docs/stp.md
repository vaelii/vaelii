# Metric time — the simple temporal problem

- **Covers:** how a simple temporal problem bounds the numeric gap between two
  instants by shortest-path closure, and narrows Allen relations through the
  startOf/endOf bridge.
- **Not here:** the generic relation-algebra engine this deliberately does not use →
  [qcn.md](qcn.md); the qualitative ordering algebras it narrows →
  [time.md](time.md); the interval-length arithmetic it sharpens →
  [duration.md](duration.md).
- **Assumes:** NAT, context, Allen's interval algebra → [glossary.md](glossary.md).

`vaelii.impl.stp` is the quantitative layer under [time.md](time.md). Allen's algebra says
*that* one meeting ended before another began; the point algebra says the same about two
moments. Neither says **how long** the gap was, and neither can tell you that a train
leaving at the hour and arriving ninety minutes later cannot also arrive within the hour.

A **simple temporal problem** is a set of bounds on the gaps between timepoints,

```
lo ≤ t(Q) − t(P) ≤ hi
```

closed by all-pairs shortest paths over the distance graph they describe. The closure gives
the tightest gap the constraints entail between *any* two instants, including pairs nobody
wrote a constraint for, and a **negative cycle** is the proof that no assignment of times
satisfies them all.

## Why it is not a relation algebra

[qcn.md](qcn.md)'s engine takes an algebra as a parameter, and this is deliberately not one.
There is no finite set of jointly-exhaustive base relations, and there is no composition
table: the constraint on a pair is an interval of the reals, composition is addition, and
tightening is `min`. Forcing that shape through a table-driven path-consistency loop would
buy nothing and hide the algorithm.

What it *does* borrow is the discipline. `vaelii.impl.stp` is split down the middle in the
same place `qcn` is:

| Half | Knows about |
|------|-------------|
| the algorithm | pure data. A network is `{[p q] → [lo hi]}`, a closure is a function of it, and a **closed state** is that closure beside the distance matrix it was read off — also a function of the network, and what the next arriving constraint is relaxed into |
| the KB half | measures, the unit table, belief, context, the violations ledger, the prover |

So the closure is testable with no KB in sight, and memoizable on the network *value*, for
exactly the reason `qcn`'s pass is.

## The network and the closure

A **network** is `{[p q] → [lo hi]}`, both directions stored — `[q p]` holds `[-hi -lo]` —
and an unrecorded pair is `unbounded`, `[-∞ ∞]`. `narrow` intersects a constraint into it
(`[max of the los, min of the his]`), which is commutative and associative, so a network is
a function of the constraints alone and never of the order they arrived in.

`close` builds the distance graph — an edge `p → q` of weight `hi`, which is exactly
`t(q) − t(p) ≤ hi`, and the reverse edge of weight `-lo` — runs Floyd–Warshall over it, and
reads the result back as bounds. Two ways it answers `:inconsistent`:

* a **negative cycle**, which the closed diagonal reports: `d[p][p] < 0` says a chain of
  gaps leads from an instant back to itself having lost time.
* a constraint **unsatisfiable as written**, which no path would visit: bounds that cross
  (`lo > hi`), or a non-zero gap from an instant to itself. Both are the metric echo of
  `qcn/unsatisfiable-as-given?`, and both are checked before the pass for the same reason —
  otherwise the verdict on one self-contradicting fact would depend on how many *other*
  instants happened to be present.

As with `qcn`, passing every node the network mentions is the **caller's** obligation, and
passing extra ones is always safe: an isolated node has a finite edge in neither direction,
so it can tighten no pair and lie on no cycle.

### Warm-starting: an arriving constraint is relaxed in

A KB being loaded asks for the closure again after every arriving fact, and all but a
handful of the bounds are exactly where the last pass left them. The memo cannot help
there — an arriving constraint is a different network and so a different key — so closing
again is the cubic loop redoing work it has already done.

The identity that licenses starting from the last answer is the one shortest paths already
rest on. A closed matrix `D` is the least-weight path between every pair, so adding an edge
`p → q` of weight `w` improves exactly the paths that run `i ⇝ p → q ⇝ j`:

```
D'[i][j] = min(D[i][j], D[i][p] + w + D[q][j])
```

That is the whole update, over every pair at once — O(n²) rather than O(n³), and not an
approximation but the same closure reached without re-deriving what did not move. One round
is enough: a path using the new edge twice decomposes into two that use it once, so a
shorter one exists unless one of those rounds is *negative*, and that is exactly what the
verdict catches — `D'[p][p]` becomes `min(0, w + D[q][p])`, which is the weight of the cycle
the new edge closes. Tightening both sides of a `[lo hi]` bound is two such updates, since
the network stores the pair both ways round.

`close-state` is therefore the pass answering `{:net :node-vec :d}` — the closure beside the
matrix it was read off — and `close-state-from` relaxes a network into an earlier state. The
matrix rides along rather than being rebuilt from the closed network, because rebuilding it
costs a map lookup per instant pair, which at four hundred instants is more than the update
it precedes. It is written once and every reader clones it before touching it, so a state
is a value the way the network in it is; `close` is `close-state`'s `:net` and is what every
caller with no next constraint coming takes.

**It applies to tightening only.** A retraction, a defeat, a loosened bound — anything that
*widens* a constraint — has no such identity: the closed matrix does not record which of its
bounds the departing constraint was behind, and a shortest path cannot be run backwards. So
a widening recomputes from nothing and pays the whole pass, and the memo on the network
value is what keeps it paid once. `tightening-of?` is the precondition, checked by the
caller against the network the previous answer was computed from. That is the honest trade
rather than a gap, and it is the same trade [qcn.md](qcn.md) makes on the qualitative side —
retraction is rare where loading is not.

Two further things bound the work. Only the bounds a relaxation actually moved are read
back, so an arriving constraint that pins one new instant rewrites that instant's row and
leaves the rest of the closed network the object it already was. And **relaxing more edges
than there are instants costs more than one full pass** — `k` updates are `k·n²` against the
closure's `n³` — so past that it takes the pass; the branch is a cost decision and cannot
change the answer.

**The answer is the same one, in every order.** `stp_incremental_test` is where that is held
rather than assumed: generated networks, three permutations of each, every permutation
folded in one constraint at a time with each step warm-started off the last, all checked
against a single run from nothing — the closed network bound for bound and the inconsistency
verdict alike. A KB loading one fact at a time and a KB recovered from a dump close the
same constraints by two different routes, and order independence is the claim that they
agree ([nmtms.md](nmtms.md)).

### Both verdicts are read to the tolerance

A magnitude reaches the network multiplied by a stored conversion factor, so two spellings
of one figure arrive a last bit apart: `1.1 Hour` normalizes to 3960.0000000000005 seconds
and `66 Minute` to 3960. Held to an exact comparison, a KB that states one gap in both
units intersects them into `lo > hi` and is unsatisfiable — over two facts its own
`sameQuantity` calls equal, and with every metric goal in the context refused as the price.

So there are two lines, and they catch different things.

* **Each stated magnitude is snapped to the tolerance grid on the way in**
  (`provers/round-magnitude`), which is the same call `duration` makes on a stored `length`
  before comparing it. A separation and a duration are written the same way, so they are
  read to the same grid, and the pair above becomes one constraint.
* **`unsatisfiable-as-given?` and `negative-cycle-nodes` read to
  `provers/*quantity-tolerance*`**, the epsilon the measure comparisons themselves use, for
  the noise a *chain* accumulates rather than one a conversion introduced: ten tenths of a
  second are each exact and sum to 0.9999999999999999, which against a stated second is a
  cycle of −1.1e-16. No snapping at the boundary sees that one, because every input to it
  was already on the grid.

`point-possibilities` reads the same band when it decides a sign, which is what stops one
network from being satisfiable and its orderings undecidable at once. A contradiction wider
than the epsilon is still a contradiction: the band is what a conversion can lose, not a
licence.

## Constraints are measures

There is no numeric syntax here. A stated constraint is the ordinary ternary fact

```clojure
(temporalDistance Departure Arrival (QuantityFn 90 Minute))        ; exactly 90 minutes
(temporalDistance Departure Arrival (QuantityIntervalFn 1 2 Hour)) ; somewhere in between
```

with the measure structural NATs of [quantity.md](quantity.md), and a **negative** magnitude saying
the second instant falls first. Every magnitude normalizes through
`provers/normalize-quantity` against the KB's `dimensionOf` / `conversionFactor` table, so
constraints stated in minutes and in hours compose without anything being said about it, and
the answer is rendered back in the dimension's **base unit** — read out of the same table
the normalization used, so nothing separate can disagree with the unit the arithmetic
happened in. That is the contract [duration.md](duration.md) follows, so a separation and a
duration are written the same way and compare directly.

Constraints spanning **more than one dimension** are refused rather than mixed: `problem`
returns nil, and no metric goal is answered. Gaps in metres are not durations, and summing
them would produce a number that means nothing — the same gate `totalDuration` applies to
its components.

That refusal is **reported** to the `(violations kb)` ledger as
`:metric-temporal-mixed-dimensions`, naming the context, the dimensions and the base units
they would have been summed in. Its reach is what earns the entry: `totalDuration` refusing
a mismatched sum withdraws one goal, while this withdraws every metric goal in the context —
including gaps stated outright, in the dimension that was never in question — and it is
usually one mis-spelt unit that does it. One entry per KB and context, so a query loop says
it once.

## Bind or check

`TemporalDistanceProver` answers `(temporalDistance P Q M)` for ground `P` and `Q`:

* **bind** — an open `M` takes the tightest bound entailed, rendered as a point
  `(QuantityFn …)` when the bounds coincide and a `(QuantityIntervalFn …)` when they do not.
  Both bounds must be finite: a half-bounded gap is real knowledge but not a measure, and
  there is no honest structural NAT for it, so the goal has no answer rather than a fabricated one.
* **check** — a ground `M` is **entailed** exactly when the derived bound is *contained* in
  it. A stated bound is a weaker claim than a tighter derived one, so the derived one
  implies it: after the closure pins `P → Q` at 13 minutes, both `(QuantityFn 780 Second)`
  and the original loose `(QuantityIntervalFn 10 20 Minute)` are answered, and anything
  tighter than 13 minutes is not.

`cost` is `:compute` (a closure over the stored constraints before the first answer),
`est-bindings` is 1 (a computation has at most one answer), and `completeness` is 100 — the
answer is a property of the whole set of constraints rather than of any one stored fact, and
it entails every stated bound it is contained in, so unioning a raw fact match in would add
nothing.

The prover is **opt-in**; the vocabulary is not.

```clojure
(v/add-reasoner kb :metric-time)
```

## What a derived bound rests on

A forward rule may join on a bound nobody stated — `(temporalDistance Dawn Dusk ?d)` where
only the two legs through noon are written down. The firing then has to say what the bound
rested on, or retracting a leg would leave the conclusion standing on a reason the JTMS
cannot reach ([nmtms.md](nmtms.md)). `TemporalDistanceProver` implements
`prover-types/SupportingProver` for exactly that: each answer comes back paired with the handles
behind it.

**The support is the path, not the network.** A bound between P and Q is the least-weight
chain between them, so the constraints on that chain are what produced it and the rest of
the network was not read. Naming the whole network would be sound — every derived bound
follows from all of it — but it would withdraw the conclusion whenever any unrelated
constraint anywhere was retracted, and locality is one of the four properties the engine
holds everywhere. Both directions count: `hi` is the chain from P to Q and `lo` the chain
back, in general two different chains, so the support is their union. Each constraint
brings the `dimensionOf` / `conversionFactor` rows its magnitude converted through, since
the conversion is part of what it contributes.

The chain is walked off a **successor** table filled by the same shortest-path pass, on its
own cache — support is asked for rarely, and every metric goal would otherwise pay to fill
an `int[n²]` nothing reads. The walk is bounded by the instant count: a shortest path over
a network with no negative cycle can be taken simple, but a chain of gaps that closes
*exactly* is a zero-weight cycle a successor chain is free to go round. Past the bound the
answer falls back to the whole network's supporters — a sound superset, at the cost of
locality in the one case a local answer is not available.

It over-approximates one derivation on the two counts [qcn.md](qcn.md) states for the
qualitative side: a pair narrowed by two constraints keeps both, and a second chain
reaching the same figure contributes nothing. The guarantee is the piece a
justification needs — every handle named was really read into this network, and the
reported set is enough to have produced the bound on its own.

`support-sources` names `temporalDistance` and the unit table, so a constraint or a
conversion factor arriving *after* a rule has fired re-joins it
([inference.md](inference.md), "What a computed answer rests on").

## An unsatisfiable network is reported

A negative cycle goes to the accumulating `(violations kb)` ledger as
`:metric-temporal-inconsistency`, naming the context, the unit, the instants in the network
and the ones lying on the cycle. It is deliberately **not** a `wff` check, for the metric
reading of the three reasons [qcn.md](qcn.md) gives:

* `wff` **throws**, and the constraint it would throw on is whichever arrived last. No
  single member of a negative cycle is the wrong one — the cycle is a property of the set —
  so blaming a member would make the stored KB depend on assertion order.
* the check costs an all-pairs closure, and `wff` runs per assert. Every temporal fact would
  pay an O(n³) pass to be stored.
* the prover is opt-in. A KB that never registered it would be held to an arithmetic it
  never asked to reason with.

It is recorded on the way past, once per network **per KB and context**. The closure itself
is memoized on the network *value* — with `provers/*quantity-tolerance*` beside it, since
both verdicts are read to that band and it is a dynamic var — and is therefore shared: two
contexts seeing the same constraints, or two KBs holding them, close it once between them. A report riding on that
pass would fire for whichever asked first and leave the rest answering nothing with an empty
ledger — so the entry hangs off `observe/newly-seen?` instead, which asks whether *this* KB
has said *this* about *this* context yet. A query loop still reports once, and a change of
belief reports again. While the network is unsatisfiable **no** metric goal is answered, not
even one that was stated outright: an unsatisfiable theory is not mined for numbers.

## The bridge: startOf and endOf

```clojure
(startOf Meeting MeetingStart)
(endOf   Meeting MeetingEnd)
```

Two binary predicates naming an interval's bounding instants. With them a metric constraint
and an Allen relation are claims about the same thing, and the metric layer can say what the
qualitative one could not.

`allen-narrowing-with-support` reads the closure back as an Allen network
`{[i j] → #{base relations}}` with the handles behind each pair. It runs **one way only** —
metric narrows qualitative — asserts nothing and mutates nothing.

The mechanism is `endpoint-signature`: each of Allen's thirteen relations forces a specific
ordering on each of the four endpoint comparisons — A's start against B's start, A's start
against B's end, A's end against B's start, A's end against B's end. A relation survives the
narrowing while every ordering its signature demands is still possible under the closure. The
thirteen signatures are distinct, so reading them is a decision rather than a filter that
could pass two, and `stp_test` derives all thirteen a second time from numeric interval
layouts — the table and the definitions share nothing, so they can only agree by both being
right.

```clojure
;; A lasts two hours, B lasts three, and B begins an hour after A ends
(stp/allen-narrowing kb ctx)   ;=> {[A B] #{:before}  [B A] #{:after}}

;; loosen the gap to "somewhere between one and five hours after A begins"
(stp/allen-narrowing kb ctx)   ;=> {[A B] #{:before :meets :overlaps} …}
```

The reading is **sound but not sharp**: the four bounds are read independently, so a
combination of them that no single assignment of times realizes is not noticed. That can
only leave a relation in that the metric network in fact excludes, never take out one it
permits — which is the direction a narrowing must err in.

Only pairs the constraints actually narrow are recorded; a pair still open to all thirteen
is the absence of a claim. An interval missing one of its bounding instants — or with one
stated of two *different* instants, which is a disagreement no reasoning should paper over —
is not read at all.

### The interval algebra reads it

This is not a value a caller may or may not intersect. `vaelii.impl.interval` declares it
as the Allen calculus's **narrowing** ([qcn.md](qcn.md), "A network can have a second
reader"), so every read of an interval network in a context takes it, and a KB that states
two meetings' endpoints and the gap between them answers `(before A B)` with no interval
relation written anywhere:

```clojure
(startOf Standup StandupStart)   (endOf Standup StandupEnd)
(startOf Review  ReviewStart)    (endOf Review  ReviewEnd)
(temporalDistance StandupStart StandupEnd (QuantityFn 15 Minute))
(temporalDistance StandupEnd   ReviewStart (QuantityFn 1 Hour))
(temporalDistance ReviewStart  ReviewEnd  (QuantityFn 30 Minute))

(v/ask? kb '(before Standup Review) ctx)          ;=> true
(v/ask? kb '(not (sharesTimeWith Standup Review)) ctx)   ;=> true
```

The two readers compose in the pass, not before it: one pair narrowed metrically and the
next by a stored fact compose exactly as two stored facts do, because what
`qcn/path-consistent` runs over is one network value either way.

**The support is the same shape a derived bound's is.** A pair's handles are the
`startOf` / `endOf` facts naming both intervals' instants, plus the constraints along the
shortest chain each of the four gaps was composed out of — `path-support` again, over
`endpoint-gaps`, so the two readings name the same four gaps and cannot drift. Not the
whole metric network: a conclusion drawn from `(before A B)` must go when a constraint
behind it goes and must **not** go when an unrelated interval's does. So a forward rule
joining on a metrically-entailed relation is an ordinary firing — it names the measures,
the endpoints and the unit rows as its antecedents, and the JTMS withdraws it when any of
them is retracted.

**What moves the network is wider than what it answers**, which is why the calculus
declares two predicate sets. `:sources` — `temporalDistance`, `startOf`, `endOf`,
`dimensionOf`, `conversionFactor` — is what re-checks and re-joins the rules carrying an
interval antecedent, since none of those is a predicate such a rule mentions and a
constraint arriving after the rule would otherwise never reach a join. `:contexts` is the
subset that puts an interval *into* a network, and so names a context worth reading one
at; a `conversionFactor` changes what a bound comes to but a context holding one and no
interval has nothing to narrow.

**A KB that registered no metric prover still pays the read**, and that is the same rule
the qualitative networks follow: a network is a property of the stored facts rather than
of the query engine, so `qualitative-network` and `possible-relations` answer whether or
not anybody opted in. What the opt-in buys is `TemporalDistanceProver` answering a
`temporalDistance` *goal*. The cost when there is nothing to read is one belief-filtered
read of `temporalDistance` per context and clock tick, which `problem` holds resident and
which answers nil before any closure runs.

## Sharpening an overlap

`overlap-window-with-support` is the other half of the bridge and the reason
[duration.md](duration.md)'s `overlapDuration` stops guessing. The shared stretch of two
intervals runs from the later of the two starts to the earlier of the two ends,

```
overlap = max(0, min(a-end, b-end) − max(a-start, b-start))
```

and `min(x,y) − max(p,q)` is `min(x−p, x−q, y−p, y−q)` — four gaps the closure already
bounds. A minimum lies above the least of the lower bounds and below the least of the upper
ones, so both sides carry through soundly, and clamping at zero is monotone and carries
through with them.

`duration` **intersects** what comes back with the bound it computes from the stored lengths
and the qualitative relation set. Both are sound, so their intersection is; and a KB stating
no `temporalDistance` gets the qualitative answer back untouched, which is the whole of the
compatibility guarantee — the metric layer can only narrow.

## Vocabulary

`temporalDistance` (ternary), `startOf` and `endOf` (binary) are declared in
`resources/kb/upper/CxTime.txt` beside the interval and instant relations, each with
its own `comment` sentex. Instants and intervals are ordinary individuals; nothing declares
them, and nothing here is about clocks or calendars.

## Cost

One closure is O(n³) in the **instant** count, not in the number of constraints, and it is
memoized on the network value — so a query loop over one belief state pays for it once. The
network read is **resident on the KB** under a key of this namespace's own, stamped with the
change clock exactly as a qualitative network is ([qcn.md](qcn.md), "The network is
resident, and the clock is what makes that sound"), which
is what stops a rule joining a metric antecedent from re-reading the KB once per binding —
and a settle from re-reading it once per firing. The closed answer is resident on the same
atom, which is what an arriving constraint is relaxed into.

Measured by `lein bench-stp` over a chain of instants — the form a sequence of events
produces, and the dense case for the read-back, since a chain pins a bound between *every*
pair however few constraints were written. The closure figure is the fastest of five runs;
each per-arrival figure is the mean of twenty arrivals.

**The algorithm**, no KB and no belief, both routes side by side:

| instants | one closure | constraint arriving, closing | …, relaxed in | instant arriving, closing | …, relaxed in |
|---|---|---|---|---|---|
| 25  | 0.26 ms | 0.31 ms | 0.23 ms | 0.41 ms | 0.32 ms |
| 100 | 3.2 ms  | 3.5 ms  | 0.47 ms | 4.0 ms  | 0.54 ms |
| 400 | 78 ms   | 94 ms   | 12 ms   | 86 ms   | 1.9 ms  |

**Through the engine**, where the belief-filtered read and the magnitude normalization sit
in front of the pass:

| instants | belief read | assert, then ask | repeat ask |
|---|---|---|---|
| 25  | 0.76 ms | 1.4 ms | 2.2 µs |
| 100 | 1.4 ms  | 2.5 ms | 1.4 µs |
| 400 | 3.6 ms  | 19 ms  | 1.7 µs |

Three things to read off them.

**The memo is the whole of what a query loop costs.** A repeat ask is a couple of
microseconds at four hundred instants and at twenty-five alike — the network is the same
object read after read, so the resident lookup is a reference compare and the content key
behind it is never reached. Against that, an ask *after* a constraint arrived is three to
four orders of magnitude larger, which is what makes an arriving fact and not a query the
thing worth making cheaper.

**What a warm start saves is the pass, and what it cannot save is the bounds that moved.**
The two arriving columns are the two ends of that. A constraint spanning half the chain and
far tighter than the chain implies moves most of the n² bounds, and relaxing it in reads
12 ms against 94 — the read-back is most of what is left. A constraint naming an **instant
the network has never held** — a timeline being loaded, which is the ordinary shape — moves
that instant's own row and nothing else, and reads 1.9 ms against 86: forty-five times.

**The belief read is linear where the closure is cubic**, so which one dominates is a
question of size. At four hundred instants the read is 3.6 ms against a 78 ms pass and
disappears into it; at twenty-five it is most of what an ask costs, and no closure work
would be noticed there at all.

`lein perf`'s `metric-closure-warm-start` is the gate over the arriving-instant column: 8×
the instants under 35× per arrival. It reads 12.6× to 13.4× across full runs, and 99.5×
with the same check driving `close-state` on the whole network instead — the cubic shape the
bound exists to catch.

A **widening** is outside all of this. A retraction, a defeat or a loosened bound recomputes
from nothing at the full O(n³), and the memo on the network value is what keeps that paid
once rather than once per question.
