# Interval duration arithmetic

- **Covers:** how `totalDuration` and `overlapDuration` compute real-unit lengths
  and overlaps from stored length facts, sharpened where a metric gap narrows them.
- **Not here:** the generic constraint-network engine underlying the ordering →
  [qcn.md](qcn.md); the qualitative ordering the relation sets come from →
  [time.md](time.md); the metric gaps that sharpen an overlap window →
  [stp.md](stp.md).
- **Assumes:** Allen's interval algebra, NAT, context → [glossary.md](glossary.md).

`vaelii.impl.duration` is the quantitative half of interval reasoning. Allen's algebra
([time.md](time.md)) says *that* two intervals overlap; this prover says for *how long*, in
real units, and adds up the lengths of several. It answers two computed predicates:

```clojure
(totalDuration (list I1 I2 …) D)   ; D is the sum of the components' lengths
(overlapDuration I1 I2 D)          ; D is how long I1 and I2 overlap
```

Neither is ever stored: `assert` refuses either one with `:not-well-formed`.

An interval's own duration is an ordinary stored fact, `(length I M)`, whose measure `M`
is one of [quantity.md](quantity.md)'s structural NATs: `(QuantityFn 2 Hour)`, or
`(QuantityIntervalFn 1 2 Hour)` when only bounds are known. The prover reads those facts
through `res/matches-visible`, its only direct KB read. A calendar term or range has a
length without a fact: the seconds between its bounds (`datetime/extent`,
`datetime/epoch-second`), read as a stated `(QuantityFn n Second)` would be, so `(totalDuration
(list (YearFn 2000)) ?d)` is 31,622,400 seconds. The rest it takes from three other
subsystems and adds nothing to them: each length normalizes through
`provers/normalize-quantity` against the `dimensionOf` / `conversionFactor` table
([quantity.md](quantity.md)), the qualitative relation set comes from
`interval/possible-allen-relations` ([time.md](time.md)), and the metric overlap window
comes from `stp/overlap-window-with-support` ([stp.md](stp.md)).

## Bounds, not points

Every computation carries `[lo hi]` magnitude bounds, and the render picks the shape:
bounds within tolerance give a point `(QuantityFn …)`, and anything wider gives
`(QuantityIntervalFn lo hi …)`. A stored length may itself be an interval measure, and an
overlap is often only bounded, so an over-approximation renders as an interval. Two hours
overlapping half an hour at an unknown offset is `(QuantityIntervalFn 0 1800 Second)`.
A `length` whose lower bound is negative is stored and read as no length.

## Which unit the answer is in

The result is rendered in the dimension's **base unit**, read out of the same
`conversionFactor` table the normalization used: `(conversionFactor U Base F)` names the
base, and a unit declaring no factor is its own base. No separate declaration names the
render unit, so the render unit is always the unit the arithmetic ran in. Every unit of a
dimension converts to one base (the direct-to-base contract, [quantity.md](quantity.md)),
so the component the base is read from does not change the answer.

A caller who wants another unit uses the **check** form. A ground `D` is compared after
normalization, so all three of these are answered from lengths stated in hours and
minutes:

```clojure
(totalDuration (list A B) (QuantityFn 9000 Second))
(totalDuration (list A B) (QuantityFn 2.5 Hour))
(totalDuration (list A B) (QuantityFn 150 Minute))
```

**Bind or check** follows the `EvaluateProver` shape: a variable `D` takes the rendered
measure, and a ground `D` succeeds iff it names the same dimension and base unit and the
same bounds within `provers/*quantity-tolerance*`. A unit with no `conversionFactor` is its
own base, so `(QuantityFn 5 Fortnight)` does not check against a total of five seconds. A
magnitude is snapped to the tolerance grid before rendering, and an integral result comes
back as an integer, so the bound answer is `=` to `(QuantityFn 9000 Second)` written by
hand.

`interval-length-with-support` snaps each stored length to the same grid before comparing
two of them, so one interval's duration written as `66 Minute` and as `1.1 Hour` is one
length. [stp.md](stp.md) snaps a stated `temporalDistance` with the same call, so the two
subsystems read one pair of facts alike.

## totalDuration

The prover reads every component's length, requires them all to share **one dimension**,
sums the `lo` and `hi` bounds separately, and renders the sum. The dimension check is the
whole of the unit consistency check: two hours plus five metres has no answer.

`(list I1 I2 …)` is **one argument**, so `time.txt` declares `totalDuration` a
`binary_predicate`.

Three cases yield no answer:

- a component with no stated length and no calendar extent (an open-world gap is not zero);
- a component with two stated lengths that differ once normalized;
- an empty component list (zero of no unit is not a measure).

A length stated twice, in another context or another unit, is not a disagreement: the
lengths are compared as normalized values, so the duplicates collapse to one, whatever
order the facts arrive in. [quantity.md](quantity.md), "A declaration the KB disagrees
with itself about", gives the rule.

## overlapDuration

`overlap-bounds` is a pure function of the possible-relation set and the two lengths. It
reads the denotations of `temporallyDisjoint`, `subintervalOf` and `hasSubinterval` out of
`vaelii.impl.interval` rather than restating them:

| Every possible relation is… | Overlap |
|------------------------------|---------|
| `temporallyDisjoint`: before, after, meets, met-by | exactly `[0 0]` |
| `subintervalOf`: during, starts, finishes, equal | the whole of the first, `[lo1 hi1]` |
| `hasSubinterval`: the mirror | `[lo2 hi2]` |
| anything else | `[0, min(hi1, hi2)]` |

The last row is the sound over-approximation: the two may not overlap at all, and overlap
by no more than the shorter of them. An unconstrained pair gets that row.

The relation set comes from the *tightened* network, so a composed relation answers as an
asserted one does: `(during A B)` and `(during B D)` put A inside D, and the overlap of A
and D is all of A. The interval network also reads the metric narrowing beside its stored
facts ([stp.md](stp.md)), so a pair determined only by endpoint measures arrives already
narrowed. An **inconsistent** network yields an empty relation set and no answer, as the
qualitative prover gives none.

## Sharpened by the metric network

When the KB places the two intervals' endpoints relative to each other, through
`(startOf I P)` / `(endOf I P)` and the `temporalDistance` constraints,
`stp/overlap-window-with-support` bounds the shared stretch ([stp.md](stp.md), "Sharpening
an overlap"). `sharpen-overlap` **intersects** that overlap window with the qualitative bound. Both
are sound, so the intersection is:

```clojure
;; A lasts two hours, B lasts half an hour, no Allen relation stated
(overlapDuration A B ?d)                      ;=> (QuantityIntervalFn 0 1800 Second)

;; add: A's own span is two hours, B's is thirty minutes, B begins 105 minutes into A
(overlapDuration A B ?d)                      ;=> (QuantityFn 900 Second)
```

The KB in the second query states no interval relation.

Five properties hold:

* **The metric layer only narrows.** A KB stating no `temporalDistance`, or none reaching
  these two intervals, gets the qualitative answer unchanged. Naming an interval's
  endpoints is not a constraint.
* **An unsatisfiable metric network sharpens nothing.** While the context's metric network
  is unsatisfiable, `stp/overlap-window-with-support` gives no overlap window. A negative
  cycle through instants that bound neither interval leaves the qualitative answer
  unchanged. An unsatisfiable component holding either interval's instants empties the
  pair's Allen relations ([stp.md](stp.md#the-bridge-startof-and-endof)),
  so `overlapDuration` answers nothing, as for an inconsistent interval network.
* **Dimensions must match.** The overlap window is read in only when its dimension and base unit
  are the lengths'. Gaps in metres never narrow a duration.
* **A sharpened range renders as a range.** An overlap window that halves the ceiling
  without fixing the figure gives a `(QuantityIntervalFn …)`.
* **The overlap window narrows a bound; it is not one.** The qualitative bound comes from the two
  stored lengths, so a KB that fixes every gap between all four endpoints still gets no
  `overlapDuration` answer while either interval has no `(length I M)`.

Two bounds with no value in common mean the KB says two incompatible things about one
overlap, for example a stated `(before A D)` against gaps that put D inside A, and the
prover gives no answer. Bounds that cross by no more than the tolerance are float noise
from two routes to one figure, and collapse to a point.

## What a computed duration rests on

`DurationProver` implements `prover-types/SupportingProver`, so a forward rule joining on
either predicate names the handles the answer was read from, and retracting any of them
withdraws the conclusion ([inference.md](inference.md), "What a computed answer rests on").

- **`totalDuration`** rests on every component's `length` facts and the unit rows each
  converted through.
- **`overlapDuration`** rests on those, on the Allen network's support for the pair
  (`interval/allen-support`, empty for an unconstrained pair), and on the metric overlap window's
  support wherever an overlap window of the lengths' dimension was intersected in. A KB with no
  `temporalDistance` gets a conclusion resting on nothing metric.
- **The check arm** adds the stated measure's own unit-table rows, since the check
  compares after normalizing it.

Every `length` fact matched is named, not only the one whose value survived the collapse:
the reading is a property of the set.

`support-sources` names `length`, the unit table, the interval relations, the
`startOf`/`endOf` bridge and `temporalDistance`, so a datum on any of them re-joins a rule
that has already fired, and the answer does not depend on whether the lengths or the rule
came first.

## Vocabulary and registration

`length`, `totalDuration` and `overlapDuration` are declared in
`resources/kb/upper/time.txt`, beside the Allen relations. `length` is a duration, not a
spatial extent. The measure terms and the unit table are `measure.txt`'s.

The prover is **opt-in**. It needs no other prover registered, because
`possible-allen-relations` and `stp/overlap-window-with-support` are functions of the
believed facts rather than queries, so duration arithmetic answers whether or not the
`:allen` or `:metric-time` reasoner is registered:

```clojure
(v/add-reasoner kb :duration)
```

`cost` is `:compute` (a few belief-filtered reads and some arithmetic), `est-bindings` is 1
(a computation has at most one answer), and `completeness` is 100: a duration is never a
stored fact and no rule concludes one, so this prover is the sole complete method and the
dispatcher runs it alone.
