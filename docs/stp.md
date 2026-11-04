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
tightening is `min`. A table-driven path-consistency loop would hide the algorithm.

`vaelii.impl.stp` borrows qcn's discipline instead, split down the middle in the same place:

| Half | Knows about |
|------|-------------|
| the algorithm | pure data. A network is `{[p q] → [lo hi]}`, a closure is a function of it, and a **closed state** is that closure beside the distance matrix it was read off — also a function of the network, and what the next arriving constraint is relaxed into |
| the KB half | measures, the unit table, belief, context, the violations ledger, the prover |

So the closure is testable with no KB in sight, and memoizable on the network *value*, for
the reason `qcn`'s pass is.

## The network and the closure

A **network** is `{[p q] → [lo hi]}`, both directions stored — `[q p]` holds `[-hi -lo]` —
and an unrecorded pair is `unbounded`, `[-∞ ∞]`. `narrow` intersects a constraint into it
(`[max of the los, min of the his]`), which is commutative and associative, so a network is
a function of the constraints alone and never of the order they arrived in.

`close` builds the distance graph — an edge `p → q` of weight `hi`, which is
`t(q) − t(p) ≤ hi`, and the reverse edge of weight `-lo` — runs Floyd–Warshall over it, and
reads the result back as bounds. It answers `:inconsistent` in two cases:

* a **negative cycle**, which the closed diagonal reports: `d[p][p] < 0` says a chain of
  gaps leads from an instant back to itself having lost time.
* a constraint **unsatisfiable as written**, which no path would visit: bounds that cross
  (`lo > hi`), or a non-zero gap from an instant to itself. Both are the metric counterpart
  of `qcn/unsatisfiable-as-given?`, and both are checked before the pass, so the verdict on
  one self-contradicting fact does not depend on how many *other* instants are present.

As with `qcn`, passing every node the network mentions is the **caller's** obligation, and
passing extra ones is always safe: an isolated node has a finite edge in neither direction,
so it can tighten no pair and lie on no cycle.

### Warm-starting: an arriving constraint is relaxed in

A KB being loaded asks for the closure again after every arriving fact, and all but a
handful of the bounds are where the last pass left them. The memo cannot help there — an
arriving constraint is a different network and so a different key.

A closed matrix `D` is the least-weight path between every pair, so adding an edge `p → q`
of weight `w` improves exactly the paths that run `i ⇝ p → q ⇝ j`:

```
D'[i][j] = min(D[i][j], D[i][p] + w + D[q][j])
```

That update covers every pair at once in O(n²) rather than O(n³), and reaches the same
closure. One round is enough: a path using the new edge twice decomposes into two that use
it once, so a shorter one exists only if one of those rounds is *negative*, and the verdict
catches that case — `D'[p][p]` becomes `min(0, w + D[q][p])`, the weight of the cycle the
new edge closes. Tightening both sides of a `[lo hi]` bound is two such updates.

`close-state` is the pass answering `{:net :node-vec :d}` — the closure beside the matrix it
was read off — and `close-state-from` relaxes a network into an earlier state. The matrix is
kept rather than rebuilt from the closed network, because rebuilding it costs a map lookup
per instant pair, which at four hundred instants is more than the update it precedes. It is
written once and every reader copies it before an update, so a state is a value; `close` is
`close-state`'s `:net`.

**It applies to tightening only.** A retraction, a defeat, a loosened bound — anything that
*widens* a constraint — has no such identity: the closed matrix does not record which of its
bounds the departing constraint was behind, and a shortest path cannot be run backwards. A
widening therefore pays the whole pass, and the memo on the network value keeps it paid
once. `tightening-of?` is the precondition, checked by the caller against the network the
previous answer was computed from. [qcn.md](qcn.md) makes the same choice on the qualitative
side, since retraction is rare where loading is not.

Two further limits bound the work. Only the bounds a relaxation moved are read back, so a
constraint that determines one new instant rewrites that instant's row and leaves the rest of the
closed network the same object. And relaxing `k` edges costs `k·n²` against the closure's
`n³`, so at `n` or more moved edges it runs the pass; the branch cannot change the answer.

**The answer is the same in every order.** `stp_incremental_test` folds three permutations
of each generated network in one constraint at a time and in batches, every step
warm-started off the last, and checks each against a single run from nothing — the closed
network bound for bound and the verdict alike. A KB loading one fact at a time and a KB
recovered from a dump close the same constraints by these two routes
([nmtms.md](nmtms.md), order independence).

### Both verdicts are read to the tolerance

A magnitude reaches the network multiplied by a stored conversion factor, so two spellings
of one figure arrive a last bit apart: `1.1 Hour` normalizes to 3960.0000000000005 seconds
and `66 Minute` to 3960. Under an exact comparison, a KB stating one gap in both units
intersects them into `lo > hi`, although its own `sameQuantity` calls them equal, and every
metric goal in the context is refused.

Two mechanisms handle two sources of noise:

* **Each stated magnitude is snapped to the tolerance grid on the way in**
  (`provers/round-magnitude`), the same call `duration` makes on a stored `length`. A
  separation and a duration are written the same way, so they are read to the same grid,
  and the pair above becomes one constraint.
* **`unsatisfiable-as-given?` and `negative-cycle-nodes` read to
  `provers/*quantity-tolerance*`**, the epsilon the measure comparisons use, for the noise a
  *chain* accumulates: ten tenths of a second are each exact and sum to
  0.9999999999999999, which against a stated second is a cycle of −1.1e-16. Snapping the
  inputs cannot remove that one, because every input was already on the grid.

`point-possibilities` reads the same band when it decides a sign, so one network is never
satisfiable while its orderings are undecidable. A disagreement wider than the epsilon is
still a contradiction.

## Constraints are measures

There is no numeric syntax here. A stated constraint is the ordinary ternary fact

```clojure
(temporalDistance Departure Arrival (QuantityFn 90 Minute))        ; exactly 90 minutes
(temporalDistance Departure Arrival (QuantityIntervalFn 1 2 Hour)) ; somewhere in between
```

with the measure structural NATs of [quantity.md](quantity.md), and a **negative** magnitude
saying the second instant falls first. Every magnitude normalizes through
`provers/normalize-quantity` against the KB's `dimensionOf` / `conversionFactor` table, so
constraints stated in minutes and in hours compose, and the answer is rendered in the
dimension's **base unit**, read out of the same table the normalization used.
[duration.md](duration.md) follows the same contract, so a separation and a duration compare
directly.

Constraints spanning **more than one dimension** are refused rather than mixed: `problem`
returns nil, and no metric goal is answered. Gaps in metres are not durations — the same
dimension check `totalDuration` applies to its components. The interval network reading the refused
problem is unsatisfiable in the component holding the intervals the constraints bound ("The
interval algebra reads it"), so no Allen goal naming one of those intervals is answered in
the context either, and every firing that rested on an Allen entailment over one is
withdrawn until the refusal ends.

That refusal is **reported** to the `(violations kb)` ledger as
`:metric-temporal-mixed-dimensions`, naming the context, the dimensions and the base units
they would have been summed in. `totalDuration` refusing a mismatched sum withdraws one
goal; this refusal withdraws every metric goal in the context, the gaps stated outright
included, and every Allen goal over an interval a constraint bounds, and one mis-spelt unit
is enough to cause it. It is reported once per KB and context.

## Bind or check

`TemporalDistanceProver` answers `(temporalDistance P Q M)` for ground `P` and `Q`:

* **bind** — an open `M` takes the tightest bound entailed, rendered as a point
  `(QuantityFn …)` when the bounds coincide and a `(QuantityIntervalFn …)` when they do not.
  Both bounds must be finite: no structural NAT denotes a half-bounded gap, so the goal has
  no answer.
* **check** — a ground `M` is **entailed** exactly when the derived bound is *contained* in
  it, in the same base unit. After the closure narrows `P → Q` to 13 minutes, both
  `(QuantityFn 780 Second)` and the original loose `(QuantityIntervalFn 10 20 Minute)` are
  answered, and anything tighter than 13 minutes is not.

`cost` is `:compute` (a closure before the first answer), `est-bindings` is 1 (a computation
has at most one answer), and `completeness` is 100 — the answer is a property of the whole
constraint set and entails every stated bound it is contained in, so a raw fact match adds
nothing.

The prover is **opt-in**; the vocabulary is not.

```clojure
(v/add-reasoner kb :metric-time)
```

## Calendar moments

A calendar moment is an `InstantFn` term, or a point term of a calendar term or a range,
such as `(StartFn (DatetimeFn "1990-05-17T14:32"))` (`timepoint/moment`, [time.md](time.md)).
The network places one at its frame's **epoch node**, offset by its seconds after
1970-01-01T00:00:00 (`datetime/epoch-second`). The epoch node is `(InstantFn 1970 1 1 0 0
0)` for a wall-clock moment and `(StartFn (DatetimeFn "1970-01-01T00:00:00Z"))` for an
absolute one (`stp/epochs`). A network naming both epoch nodes bounds the second within 18
hours of the first either way (`stp/epoch-bound`), the range `java.time.ZoneOffset` gives
every zone offset, so a wall-clock moment and an absolute one are at most 18 hours from the
same reading in the other frame, and a placement that needs a wider offset is the network's
inconsistency. A network naming one epoch node joins no moment of the other frame. The
offset is read in the base unit through `Second`'s rows of the unit table, and every
bound it enters rests on those rows.

- **A goal.** `(temporalDistance P Q ?d)` over two moments of one frame answers the
  difference of their offsets, exact, with no constraint stated. Over a moment and an
  instant, it answers the network's bound between the epoch node and the instant, shifted by
  the moment's offset.
- **A stated constraint.** A `temporalDistance` fact naming a moment constrains its epoch
  node instead, shifted by the offset (`stp/placed`).
- **A placed instant.** A visible `(includesInstant T X)`, `T` a calendar term or a range
  and `X` a symbol, is the constraint from `T`'s epoch node to `X` between the offsets of
  `T`'s start and end (`stp/instant-constraints`). Both ends are closed: the end of a
  half-open interval is the least upper bound of the gap. Two such instants inside two
  minutes are bounded to a 120-second width.

A moment and a placed instant join the network only under `Second`'s `[dimension
base-unit]` key, when the stated constraints use that key or there are none, so neither
causes the mixed-dimension refusal.

## What a derived bound rests on

A forward rule may join on a bound nobody stated — `(temporalDistance Dawn Dusk ?d)` where
only the two legs through noon are written down. The firing has to name what the bound
rested on, or retracting a leg would leave the conclusion standing on a reason the JTMS
cannot reach ([nmtms.md](nmtms.md)). `TemporalDistanceProver` implements
`prover-types/SupportingProver` for that: each answer comes paired with the handles behind
it.

**The support is the path, not the network.** A bound between P and Q is the least-weight
chain between them, so the constraints on that chain produced it. Naming the whole network
would be sound but would withdraw the conclusion whenever any unrelated constraint was
retracted, and locality is one of the five properties the engine holds everywhere. `hi` is
the chain from P to Q and `lo` the chain back, so the support is the union of the two. Each
constraint brings the `dimensionOf` / `conversionFactor` rows its magnitude converted
through. A check additionally names the stated measure's own conversion rows.

The chain is walked off a **successor** table filled by the same shortest-path pass, on its
own cache, so a metric goal that asks for no support fills no `int[n²]`. The walk is bounded
by the instant count, because a chain of gaps that closes *exactly* is a zero-weight cycle a
successor chain can go round. Past the bound the answer falls back to the whole network's
supporters, a sound superset.

The support over-approximates one derivation on the two counts [qcn.md](qcn.md) states for
the qualitative side: a pair narrowed by two constraints keeps both, and a second chain
reaching the same figure contributes nothing. Every handle named was read into this network,
and the named set is enough to produce the bound on its own.

`support-sources` names `temporalDistance` and the unit table, so a constraint or a
conversion factor arriving *after* a rule has fired re-joins it
([inference.md](inference.md), "What a computed answer rests on").

## An unsatisfiable network is reported

A negative cycle goes to the `(violations kb)` ledger as `:metric-temporal-inconsistency`,
naming the context, the unit, the instants in the network, any pair unsatisfiable as
written, and the instants on the cycle. It is deliberately **not** a `wff` check, for the
metric reading of the three reasons [qcn.md](qcn.md) gives:

* `wff` **throws**, and the constraint it would throw on is whichever arrived last. No
  single member of a negative cycle is the wrong one, so blaming a member would make the
  stored KB depend on assertion order.
* the check costs an all-pairs closure, and `wff` runs per assert. Every temporal fact would
  pay an O(n³) pass to be stored.
* the prover is opt-in. A KB that never registered it would be held to an arithmetic it
  never asked to reason with.

The closure is memoized on the network *value*, with `provers/*quantity-tolerance*` in the
key beside it, and is therefore shared: two contexts seeing the same constraints, or two KBs
holding them, close it once between them. A report on that memoized pass would reach only
whichever caller asked first, so the report is keyed through `observe/newly-seen?` on this
KB, this context and this network. A query loop reports once, and a change of belief reports
again. While the network is unsatisfiable **no** metric goal is answered, not even one
stated outright.

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
thirteen signatures are distinct, so reading them decides one relation per layout, and
`stp_test` derives all thirteen a second time from numeric interval layouts.

```clojure
;; A lasts two hours, B lasts three, and B begins an hour after A ends
(stp/allen-narrowing kb ctx)   ;=> {[A B] #{:before}  [B A] #{:after}}

;; loosen the gap to "somewhere between one and five hours after A begins"
(stp/allen-narrowing kb ctx)   ;=> {[A B] #{:before :meets :overlaps} …}
```

The reading is **sound but not sharp**: the four bounds are read independently, so a
combination of them that no single assignment of times realizes is not noticed. That can
only leave in a relation the metric network excludes, never take out one it permits.

Only pairs the constraints narrow are recorded; a pair still open to all thirteen is the
absence of a claim. An unsatisfiable metric network is read one connected component at a
time (`qcn/components` over the instants its constraints join). An unsatisfiable component
narrows every pair of the intervals it bounds to nothing, and the reading empties pairs
joining those intervals (`unsatisfiable-narrowing`), supported by the component's
constraints: the component of the interval network holding them is then unsatisfiable,
answers no goal naming one of them, and withdraws the firings that rested on one
([qcn.md](qcn.md), "Unsatisfiability is per component"). A negative cycle through instants
that bound no interval leaves the interval network satisfiable. The satisfiable components
narrow the intervals no unsatisfiable component bounds as a satisfiable network does. Each
unsatisfiable component is described as a `:metric` source: its pairs unsatisfiable as
written, the instants on a negative cycle, and the handles behind the constraints among
them, so `qualitative-network` over `:allen` names the cycle. A problem refused for spanning
more than one dimension empties pairs joining the intervals its constraints bound,
supported by every constraint read, its `:metric` source naming the `:dimensions` in place
of pairs and a cycle. An interval missing one of its bounding instants, or with one stated
of two *different* instants, is not read at all.

### The interval algebra reads it

`vaelii.impl.interval` declares the narrowing as the Allen calculus's **narrowing**
([qcn.md](qcn.md), "A network can have a second reader"), so every read of an interval
network in a context takes it, and a KB that states two meetings' endpoints and the gap
between them answers `(before A B)` with no interval relation written anywhere:

```clojure
(startOf Standup StandupStart)   (endOf Standup StandupEnd)
(startOf Review  ReviewStart)    (endOf Review  ReviewEnd)
(temporalDistance StandupStart StandupEnd (QuantityFn 15 Minute))
(temporalDistance StandupEnd   ReviewStart (QuantityFn 1 Hour))
(temporalDistance ReviewStart  ReviewEnd  (QuantityFn 30 Minute))

(v/ask? kb '(before Standup Review) ctx)          ;=> true
(v/ask? kb '(not (sharesTimeWith Standup Review)) ctx)   ;=> true
```

The two readers compose in the pass: one pair narrowed metrically and the next by a stored
fact compose as two stored facts do, because `qcn/path-consistent` runs over one network
value either way.

**A pair's support is built as a derived bound's is**: the `startOf` / `endOf` facts
naming both intervals' instants, plus `path-support` over the four `endpoint-gaps`, the same
four gaps the relation was read off. A conclusion drawn from `(before A B)` goes when a
constraint behind it goes and stays when an unrelated interval's does, so a forward rule
joining on a metrically-entailed relation is an ordinary firing.

The calculus declares two predicate sets. `:sources` — `temporalDistance`, `startOf`,
`endOf`, `dimensionOf`, `conversionFactor` — re-checks and re-joins the rules carrying an
interval antecedent, since none of those is a predicate such a rule mentions. `:contexts` is
the subset that puts an interval *into* a network and so names a context worth reading one
at; a `conversionFactor` changes what a bound comes to, but a context holding one and no
interval has nothing to narrow.

**A KB that registered no metric prover still pays the read**, as the qualitative networks
do: a network is a property of the stored facts, so `qualitative-network` and
`possible-relations` answer whether or not anybody opted in. The opt-in adds
`TemporalDistanceProver` answering a `temporalDistance` *goal*. With nothing to read the
cost is one belief-filtered read of `temporalDistance` per context and clock tick, which
`problem` holds resident and which answers nil before any closure runs.

## Sharpening an overlap

`overlap-window-with-support` is the other half of the bridge and what lets
[duration.md](duration.md)'s `overlapDuration` answer a figure. The shared stretch of two
intervals runs from the later of the two starts to the earlier of the two ends,

```
overlap = max(0, min(a-end, b-end) − max(a-start, b-start))
```

and `min(x,y) − max(p,q)` is `min(x−p, x−q, y−p, y−q)` — four gaps the closure already
bounds. A minimum lies above the least of the lower bounds and below the least of the upper
ones, so both sides carry through soundly, and clamping at zero is monotone.

`duration` **intersects** what comes back with the bound it computes from the stored lengths
and the qualitative relation set. Both are sound, so their intersection is; and a KB stating
no `temporalDistance` gets the qualitative answer back untouched.

## Vocabulary

`temporalDistance` (ternary), `startOf` and `endOf` (binary) are declared in
`resources/kb/upper/time.txt` beside the interval and instant relations, each with
its own `comment` sentex. Instants and intervals are ordinary individuals, and nothing
declares them. A calendar moment is placed by its fields ("Calendar moments").

## Cost

One closure is O(n³) in the **instant** count, not in the number of constraints, and it is
memoized on the network value, so a query loop over one belief state pays for it once. The
network read is **resident on the KB** under a key of this namespace's own and the
tolerance, keyed by the change clock as a qualitative network is ([qcn.md](qcn.md), "The
network is resident, and the clock is what makes that sound"), so a rule joining a metric
antecedent does not re-read the KB once per binding, and a settle does not re-read it once
per firing. The closed state is resident on the same atom, and an arriving constraint is
relaxed into it. The tolerance is in both keys, so a rebound `*quantity-tolerance*` reads
and closes its own network.

Measured by `lein bench-stp` over a chain of instants — the form a sequence of events
produces, and the dense case for the read-back, since a chain determines a bound between *every*
pair. The closure figure is the fastest of five runs; each per-arrival figure is the mean of
twenty arrivals.

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

**A repeat ask is the resident lookup**: a couple of microseconds at four hundred instants
and at twenty-five alike, because the network is the same object read after read and the
lookup is a reference compare. An ask *after* a constraint arrived is three to four orders
of magnitude larger.

**A warm start saves the pass but not the read-back of the bounds that moved.** A constraint
spanning half the chain and far tighter than the chain implies moves most of the n² bounds,
and relaxing it in reads 12 ms against 94. A constraint naming an **instant the network has
never held** — a timeline being loaded — moves that instant's own row only, and reads
1.9 ms against 86: forty-five times.

**The belief read is linear where the closure is cubic.** At four hundred instants the read
is 3.6 ms against a 78 ms pass; at twenty-five it is most of what an ask costs.

`lein perf`'s `metric-closure-warm-start` is the perf check over the arriving-instant column: 8×
the instants under 35× per arrival. It reads 12.6× to 13.4× across full runs, and 99.5×
with the same check driving `close-state` on the whole network instead.
