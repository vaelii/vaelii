# Interval duration arithmetic

- **Covers:** how `totalDuration` and `overlapDuration` compute real-unit lengths
  and overlaps from stored length facts, sharpened where a metric gap narrows them.
- **Not here:** the generic constraint-network engine underlying the ordering →
  [qcn.md](qcn.md); the qualitative ordering the relation sets come from →
  [time.md](time.md); the metric gaps that sharpen an overlap window →
  [stp.md](stp.md).
- **Assumes:** Allen's interval algebra, NAT, context → [glossary.md](glossary.md).

`vaelii.impl.duration` is the quantitative half of interval reasoning. Allen's algebra
([time.md](time.md)) says *that* two intervals overlap; this says *how long* for, in real
units, and adds up the lengths of several. Two computed predicates, neither ever stored:

```clojure
(totalDuration (list I1 I2 …) D)   ; D is the sum of the components' lengths
(overlapDuration I1 I2 D)          ; D is how long I1 and I2 overlap
```

An interval's own duration is an ordinary stored fact, `(length I M)`, whose measure `M`
is one of [quantity.md](quantity.md)'s structural NATs — `(QuantityFn 2 Hour)`, or
`(QuantityIntervalFn 1 2 Hour)` when only bounds are known. The index answers those; this
prover only reads them.

So it sits on top of three existing subsystems and adds nothing to any of them: it
normalizes each length through `provers/normalize-quantity` against the KB's
`dimensionOf` / `conversionFactor` table ([quantity.md](quantity.md)), reads the
qualitative relation set straight off `interval/possible-allen-relations`
([time.md](time.md)), and takes the metric overlap window from
`stp/overlap-window-with-support` ([stp.md](stp.md)). `res/matches-visible` is its only
touch of the KB.

## Bounds, not points

Every computation carries `[lo hi]` magnitude bounds, and the render decides the shape:
bounds within tolerance give a point `(QuantityFn …)`, anything wider gives
`(QuantityIntervalFn lo hi …)`.

That is what keeps the answer honest. A stored length may itself be an interval measure,
and an overlap is often only bounded rather than known — so an over-approximation renders
as an interval and *says* it is one, instead of as a point that would claim more than the
KB knows. Two hours overlapping half an hour "somewhere" is
`(QuantityIntervalFn 0 1800 Second)`, not a figure.

## Which unit the answer is in

The result is rendered in the dimension's **base unit**, read back out of the same
`conversionFactor` table the normalization used: `(conversionFactor U Base F)` names the
base, and a unit declaring no factor is its own base. So no separate declaration says
which unit to render in, and none can disagree with the unit the arithmetic actually
happened in. Every unit of a dimension converts to a single base — the direct-to-base
contract — so which component the base is read from cannot change the answer.

A caller who wants another unit uses the **check** form instead. A ground `D` is compared
after normalization, so all three of these are answered from lengths stated in hours and
minutes:

```clojure
(totalDuration (list A B) (QuantityFn 9000 Second))
(totalDuration (list A B) (QuantityFn 2.5 Hour))
(totalDuration (list A B) (QuantityFn 150 Minute))
```

**Bind or check** is the `EvaluateProver` shape: a variable `D` takes the rendered
measure; a ground `D` succeeds iff it names the same dimension and the same bounds within
`provers/*quantity-tolerance*` — the same epsilon policy the measure comparisons use. A
magnitude is snapped to that same grid before rendering, so cross-unit normalization's
last-bit noise never reaches the answer, and an integral result comes back as an integer
so the bound answer is `=` to the obvious way of writing it.

`interval-length-with-support` snaps each stored length to that grid before comparing two
of them, which is why one interval's duration written as `66 Minute` and as `1.1 Hour` is
one length and not a disagreement. [stp.md](stp.md) snaps a stated `temporalDistance` the
same way and for the same reason — a separation and a duration are written alike, so they
are read to one grid, and the two subsystems cannot reach different verdicts about the
same pair of facts.

## totalDuration

Read every component's length, require them all to share **one dimension**, sum the `lo`
and `hi` bounds separately, render. The dimension gate is the whole of the unit
consistency check: magnitudes only add up once they are in one unit, so two hours plus
five metres is refused outright rather than summed into a number that means nothing.

`(list I1 I2 …)` is **one argument**, so `totalDuration` is declared
`binary_predicate` — the arity check holds a stored sentence to that, and the goal shape
the prover reads has to agree with it.

Three things yield no answer rather than a wrong one: a component with no stated length
(an open-world gap is not zero), a component with two stated lengths that *disagree* once
normalized, and an empty component list (zero of no unit is not a measure). Duplicates are
not a disagreement — the lengths are compared as normalized values, so the same duration
restated in another context or written in another unit collapses to one, and the verdict
cannot depend on the order the facts were read in.

## overlapDuration

`overlap-bounds` is a pure function of the possible-relation set and the two lengths.
Three of its four cases are named by the qualitative vocabulary itself, and it reads their
denotations out of `vaelii.impl.interval` rather than restating them, so the two cannot
drift apart:

| Every possible relation is… | Overlap |
|------------------------------|---------|
| `temporallyDisjoint` — before, after, meets, met-by | exactly `[0 0]` |
| `subintervalOf` — during, starts, finishes, equal | the whole of the first, `[lo1 hi1]` |
| `hasSubinterval` — the mirror | `[lo2 hi2]` |
| anything else | `[0, min(hi1, hi2)]` |

The last is the sound over-approximation: they may not overlap at all, and can overlap by
no more than the shorter of them. An unconstrained pair gets exactly that, which is the
right answer to "how long do these two overlap?" when nothing has been said — and it
renders as an interval, so it reads as ignorance rather than as a measurement.

The relation set comes from the *tightened* network, so a relation nobody asserted works
as well as one that was: `(during A B)` and `(during B D)` compose to put A inside D, and
the overlap of A and D is all of A. Nor need the constraint be qualitative at all: the
interval network reads the metric narrowing beside its stored facts ([stp.md](stp.md)),
so a pair pinned only by endpoint measures arrives here already narrowed. An
**inconsistent** network yields an empty relation set and therefore no answer at all — the
same rule the qualitative prover follows, since an unsatisfiable theory should not be mined
for a number either.

## Sharpened by the metric network

The last row of that table is the honest answer to "how long do these two overlap?" when
nothing is known, and it is a poor answer when something is. If the KB says where the two
intervals' endpoints fall relative to one another — `(startOf I P)` / `(endOf I P)` and the
`temporalDistance` constraints of [stp.md](stp.md) — there is a real figure, and
`stp/overlap-window-with-support` computes it: the shared stretch runs from the later of
the two starts to the earlier of the two ends, which is four gaps the metric closure
already bounds.

`sharpen-overlap` **intersects** that with the qualitative bound. Both are sound, so the
tighter of them is:

```clojure
;; A lasts two hours, B lasts half an hour, no Allen relation stated
(overlapDuration A B ?d)                      ;=> (QuantityIntervalFn 0 1800 Second)

;; add: A's own span is two hours, B's is thirty minutes, B begins 105 minutes into A
(overlapDuration A B ?d)                      ;=> (QuantityFn 900 Second)
```

Fifteen minutes, exactly, from a KB that never stated an interval relation at all.

Three properties hold it together:

* **the metric layer can only narrow.** A KB stating no `temporalDistance` — or none
  reaching these two intervals, or one whose network is unsatisfiable — gets the qualitative
  answer back to the digit. Naming an interval's endpoints is not itself a constraint.
* **dimensions must match.** The metric answer is used only when it is in the same dimension
  and base unit as the lengths, since two magnitudes must be commensurable before they can be
  intersected. Gaps in metres never narrow a duration.
* **a sharpened bound that is still a range renders as one.** Halving a ceiling without
  pinning it gives a `(QuantityIntervalFn …)`, exactly as an unconstrained pair does — the
  honesty rule does not relax because the answer got better.

Sharpening is all the metric layer does here, and that is a **dependency** as well as a
guarantee: the qualitative bound is what gets narrowed, and it is computed from the two
stored lengths. A KB that names all four endpoints and pins every gap between them still
gets no `overlapDuration` answer while either interval has no `(length I M)` — there is
nothing for the window to narrow, and the prover does not read the window as a bound in its
own right.

Two sound bounds with nothing in common mean the KB says two incompatible things about the
same overlap — a stated `(before A D)` against gaps that put D inside A — and there is then no
number to report at all. Bounds that cross by no more than the tolerance are float noise from
two routes to one figure, and collapse to a point rather than a contradiction.

## What a computed duration rests on

Neither `totalDuration` nor `overlapDuration` is ever stored, so a forward rule joining on
one draws its conclusion from facts no other antecedent names — the component `length`
rows, the interval network, the metric constraints. `DurationProver` implements
`prover-types/SupportingProver` so the firing names them: each answer comes back paired with the
handles it was read from, and retracting any of them withdraws the conclusion through the
ordinary relabel ([inference.md](inference.md), "What a computed answer rests on").

- **`totalDuration`** rests on every component's `length` facts and the unit rows each
  converted through. A sum moves when any of its terms does, so all of them are named.
- **`overlapDuration`** rests on those plus two more sources, each only where it was read:
  the Allen network's support for the pair (`interval/allen-support`, empty for an
  unconstrained pair — the `[0, min(len1, len2)]` fallback found nothing narrowing it), and
  the metric constraints where the window actually narrowed the qualitative bound. A KB
  with no `temporalDistance` gets a conclusion resting on nothing metric, which is the same
  compatibility guarantee the sharpening itself has.
- **The check arm** adds the stated measure's own conversion, since whether the computed
  bounds agree with it is decided after normalizing it through the table.

Every `length` fact matched is named, not the one whose value survived the collapse: two
rows that agree once normalized are one reading, and a third that disagrees declines it, so
the reading is a property of the set.

`support-sources` names `length`, the unit table, the interval relations, the
`startOf`/`endOf` bridge and `temporalDistance` — so a datum on any of them re-joins a rule
that has already fired, and the answer does not depend on whether the lengths or the rule
came first.

## Vocabulary and registration

`length`, `totalDuration` and `overlapDuration` are declared in
`resources/kb/upper/CxTime.txt`, beside the Allen relations — they are *about*
intervals. `length` is a duration, not a spatial extent. The measure terms and the unit
table stay CxMeasure's.

The prover is **opt-in**, and needs no other prover registered — `possible-allen-relations`
and `stp/overlap-window-with-support` are both functions of the believed facts rather
than queries, so duration arithmetic works whether or not the `:allen` or `:metric-time`
reasoner is registered:

```clojure
(v/add-reasoner kb :duration)
```

`cost` is `:compute` (a handful of belief-filtered reads and some arithmetic),
`est-bindings` is 1 (a computation has at most one answer), and `completeness` is 100 —
a duration is never a stored fact and no rule concludes one, so this is the sole complete
method and the dispatcher runs it alone.
