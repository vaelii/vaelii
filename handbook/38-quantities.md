# 38. Quantities and units

- **Covers:** stating an amount as a measure term, `QuantityFn` or `QuantityIntervalFn`,
  with its unit; typing a measured relation's value position `measure`; a point or a
  bounded figure; adding a unit to a shipped dimension with `dimensionOf` and
  `conversionFactor`; adding a dimension; comparing two measures in a query or a rule with
  the five quantity comparisons; numbers, measures and quantities as three different
  things.
- **Not here:** why a measure function is unreifiable → [ch. 22](22-functions.md); the
  length of an interval and the durations between time points →
  [ch. 40](40-durations.md); the sign and the trend of a quantity nobody has put a figure
  on → [ch. 42](42-signs-and-trends.md); the prover's arithmetic, its tolerance and its
  rounding → [quantity.md](../docs/quantity.md); a sum or an average over measures →
  [aggregate.md](../docs/aggregate.md).
- **Assumes:** [ch. 18](18-argument-types.md), [ch. 19](19-relation-properties.md)
  (`functional`, `transitive`), [ch. 22](22-functions.md), [ch. 29](29-rules.md).

A **measure** is a figure in a unit: `(QuantityFn 5 Kilogram)` is five kilograms, and
`(QuantityIntervalFn 1 2 Meter)` is somewhere between one and two metres. Both functions
are `unreifiable_function`, so an application stays a structural NAT with its magnitude
and its unit readable inside the sentence. `QuantityProver` compares two ground measures
by converting each to its dimension's base unit through the `dimensionOf` and
`conversionFactor` rows the asking context sees. The comparison is computed at the read
and stored nowhere.

The KB keeps three things apart. A **number** is a value with no unit, such as a year or a
count, and `lessThan` and `greaterThan` compare numbers. A **measure** is a number with a
unit, and the five quantity comparisons compare measures. A **quantity** is the magnitude a
measure would measure, such as a water level, and the sign vocabulary of
[ch. 42](42-signs-and-trends.md) relates quantities with no figure at all.

## a figure carries its unit
*State an amount in a unit as a measure term, and type its position `measure`*

**Practice.** When the value of a relation is an amount in a unit, write the value as a
`QuantityFn` application and declare the position `(arg P n measure)`. Write a plain number
only where the value has no unit. Name the relation for what it measures (`weightOf`), not
for the unit it was first recorded in.

**Example.** `measure.txt` declares the measure function, and its value type is `measure`:

```clojure
(unreifiable_function QuantityFn)
(binary_function QuantityFn)
(functionCorrespondingPredicate QuantityFn measureInUnit 3)
(result QuantityFn measure)
```

`measure.txt` declares `weightOf` with its value position typed `measure`:

```clojure
(set/monotonic (instance_relation_predicate weightOf))
(arg weightOf 1 tangible)
(arg weightOf 2 measure)
(set/monotonic (functional weightOf))
```

`life.txt` types a birth year `(arg birthYearOf 2 integer)`, since a year is counted and
carries no unit.

**Why.**

- *Logical.* A magnitude without its unit does not say how much. `(weightOf Muffet 20)`
  is true of a twenty-kilogram dog and false of a twenty-gram one, and nothing in the
  sentence says which the author meant.
- *Engine.* The `measure` declaration convicts a bare number. `(weightOf Muffet 20)` is
  stored and held inert with an `:arg-type` conviction ("20 must be a measure"): the fact
  is never believed and fires no rule, and `try-assert` refuses the write.
- *Engine.* The provers read the magnitude and the unit off the term itself. A weight in
  grams and a weight in kilograms compare with no rule and no restatement, because both
  normalize to kilograms.
- *Engine.* No prover answers `measureInUnit`, the predicate corresponding to
  `QuantityFn`: `(measureInUnit 5 Kilogram (QuantityFn 5 Kilogram))` answers nothing. Write
  the `QuantityFn` term in the position; `measureInUnit` records the correspondence.

**Why not the other ways.** A relation named for its unit, such as a weight-in-kilograms
predicate over a plain number, puts the unit in the predicate's name. A second unit then
needs a second predicate and a rule converting between the two, and no quantity
comparison reads either one. A reifiable measure function mints each application to an
opaque constant, so the provers have no magnitude and no unit to read
([ch. 22](22-functions.md)). `sameAs` or `equals` between two measures is not a way to say
they agree: the equality closure holds symbols only, and `assert` refuses an `equals`
over two `QuantityFn` terms as not well formed.

**Audit.** For each new relation whose value is an amount, read its `arg` declarations
with `describe` and confirm the value position names `measure`. Run `violations` after
loading the facts; each `:inert-argument` entry with an `:arg-type` conviction against
`measure` is a value written without its unit.

## Point or interval

**Practice.** State `(QuantityFn N U)` when the figure is known. State
`(QuantityIntervalFn Lo Hi U)` when the figure is known only within bounds, and do not
replace a range with its midpoint. Under a `functional` relation, state one measure per
subject.

**Example.** The `comment` on `heightOf` in `measure.txt` names both forms: "A measure of
Length, exact as (QuantityFn 2 Meter) or bounded as (QuantityIntervalFn 1 2 Meter)."

**Why.**

- *Engine.* A comparison holds of an interval only when it holds of every point in it.
  `(QuantityIntervalFn 1 2 Meter)` is less than `(QuantityFn 5 Meter)`;
  `(QuantityIntervalFn 1 4 Meter)` is not less than `(QuantityIntervalFn 3 6 Meter)`,
  because the two ranges overlap. A midpoint of 2.5 written for the first range and 4.5
  for the second would make the comparison hold where the knowledge does not support it.
- *Engine.* A sum or an average over interval measures comes back as an interval, and a
  minimum or a maximum over a genuine interval is refused, since bounds order measures
  only partially ([aggregate.md](../docs/aggregate.md)).
- *Engine.* The `functional` check compares the two values as terms. A second `weightOf`
  for one subject is recorded as a `:functional` contradiction even when it agrees with the
  first: `(QuantityIntervalFn 18 22 Kilogram)` clashes with `(QuantityFn 20 Kilogram)`, and
  `(QuantityFn 1000 Gram)` clashes with `(QuantityFn 1 Kilogram)`.

**Why not the other ways.** A midpoint says more than the source knows, and every
comparison downstream inherits the false precision. Stating a figure and a range
for the same subject under a functional relation leaves a contradiction for the KB to
report rather than a refinement it can use. When a better figure arrives, retract the
range and assert the figure.

**Audit.** Run `contradictions` after loading measured facts. Each entry with `:kind
:functional` whose `:grounds` name a measured relation is two measures stated for one
subject; keep the more precise one.

## Adding a unit

**Practice.** Give each new unit both rows in one context: `(dimensionOf U D)` and
`(conversionFactor U Base F)`, where `Base` is the base unit of `D` and `F` is how many
base units one `U` is. State the factor against the base unit directly, never against a
neighbouring unit. Ship a unit only when its factor is a definition, as a gram is a
thousandth of a kilogram; a measurement of a particular thing goes with that thing's
facts.

**Example.** `measure.txt` states the gram against the kilogram, and the kilogram against
itself:

```clojure
(dimensionOf Gram Mass)
(conversionFactor Gram Kilogram 0.001)
(dimensionOf Kilogram Mass)
(conversionFactor Kilogram Kilogram 1)
```

**Why.**

- *Engine.* The prover reads one `dimensionOf` row for the unit's dimension and one
  `conversionFactor` row for its base and factor, then multiplies the magnitude by the
  factor once. A unit with no `dimensionOf` is its own dimension, and a unit with no
  `conversionFactor` is its own base at factor 1.
- *Engine.* A unit with only one of the two rows answers wrongly or not at all. A
  `(dimensionOf Foot Length)` with no factor converts at factor 1, so one foot compares as
  the same quantity as one metre. A `conversionFactor` with no `dimensionOf` leaves the
  unit its own dimension, so it compares only against itself.
- *Engine.* Conversion does not chain. A factor stated against a non-base unit is applied
  once and the result is read as base units: a `Length` unit stated as 40 rods compares as
  40 metres.
- *Engine.* Two different factors, or two different dimensions, for one unit in the
  contexts a reader sees are declined, not adjudicated: the declined reading falls back to
  the unit itself, as an undeclared one does. Choosing one row would make the answer depend
  on which row was stored first. The same row restated in two contexts is one reading.
- *Maintenance.* A forward rule that fires on a comparison records the unit rows the
  comparison converted through among its antecedents. Retracting a row withdraws the
  conclusion, and `why` names the rows. The rows may arrive before or after the rule and
  the facts. A rule and a fact in a context that does not see the rows derive nothing, so
  put the rows in an ancestor of every context that holds the rules and the measured facts.

**Why not the other ways.** A unit table where each unit converts to its neighbour
(millimetre to centimetre to metre) states the same definitions, and the prover, which
multiplies once, reads every unit but the first as if it were the base. A second
spelling of a unit the shipped table has, such as a KB's own gram, compares with the
shipped one only if its rows repeat the shipped definition.

**Audit.** For each new unit, `query` `(dimensionOf U ?d)` and
`(conversionFactor U ?base ?f)` from the context the facts are stated in, and confirm
exactly one answer each, with `?base` the dimension's base unit. Then `ask?` a
`sameQuantity` between one of the new unit and its stated value in the base unit.

## Adding a dimension

**Practice.** A new dimension is an individual. State one base unit for it with
`(conversionFactor Base Base 1)`, give every other unit of the dimension both rows against
that base, and name the base unit in the dimension's `comment`. A speed or a density is
a dimension of its own with its own units; the engine derives no unit from two others.

**Example.** `measure.txt` comments a shipped dimension with its base unit: "The dimension
of spatial extent. Its base unit is Meter." A composed table for volume:

```clojure composed
(comment Volume "The dimension of how much space a thing takes up. Its base unit is Liter.")
(dimensionOf Liter Volume)
(conversionFactor Liter Liter 1)
(dimensionOf Milliliter Volume)
(conversionFactor Milliliter Liter 0.001)
```

**Why.**

- *Engine.* `dimensionOf` declares its arguments `unit_of_measure` and
  `physical_dimension`, so the first row derives `(unit_of_measure Liter)` and
  `(physical_dimension Volume)` with no membership written.
- *Engine.* Two measures compare only within one dimension. `(QuantityFn 1 Liter)` is
  neither greater than nor less than `(QuantityFn 1 Kilogram)`: every comparison between
  them fails, and none throws. A mismatch answers "not comparable", which is different
  from false.
- *Maintenance.* The base unit's own row, at factor 1, makes the base a stated fact. A
  `query` of `(conversionFactor ?u ?u 1)` lists every base in the table, and a reviewer can
  check that each other unit of the dimension names that base.

**Why not the other ways.** A volume stated under `Mass` through a density factor states a
measurement of water as a definition of the litre, and a litre of anything else then
compares as a kilogram. A unit algebra (metres per second as Length over Duration) is not
built, so a speed stated in metres per second compares with nothing unless metres per
second are units of a speed dimension the table states.

**Audit.** `isa?` the new dimension against `physical_dimension` and each unit against
`unit_of_measure`. `ask?` a comparison between a unit of the new dimension and a unit of a
shipped one, and confirm it answers nothing in either direction.

## Comparing measures in a rule

**Practice.** Compare two measures with `sameQuantity`, `quantityLessThan`,
`quantityGreaterThan`, `quantityLessThanOrEqual` or `quantityGreaterThanOrEqual`, never
with `lessThan` or `greaterThan`, which take numbers. Derive an ordering between things as
a rule over their two measures, and declare the derived relation a strict order, so that
stated comparisons with no measure compose with the derived ones.

**Example.** `CxSize.txt` derives `heavierThan` from two weights:

```clojure
(set/backwardRule
  (implies (and (weightOf ?x ?wx) (weightOf ?y ?wy) (quantityGreaterThan ?wx ?wy))
           (heavierThan ?x ?y)))
```

`measure.txt` declares `heavierThan` transitive and asymmetric:

```clojure
(set/monotonic (transitive heavierThan))
(set/monotonic (asymmetric heavierThan))
```

**Why.**

- *Engine.* The five comparisons are check-only. Each holds or fails over two ground
  measures, and a goal with a variable in either position, such as
  `(sameQuantity ?x (QuantityFn 1 Kilogram))`, is refused rather than enumerated. In a
  rule, the planner places each comparison after the literals that bind its measures, so
  the order the antecedents are written in does not decide whether the rule runs.
- *Engine.* The comparisons are in the forced-monotonic set and are never stored. A
  forward firing over a comparison rests on the facts that bound the measures and on the
  unit rows the comparison read, and its conclusion goes when one of those goes.
- *Logical.* `heavierThan` is a strict order. The transitive mark answers a chain of
  stated comparisons with no measure anywhere, and the measured route agrees with the
  chain wherever both answer, since a chain of strict measure comparisons is a strict
  measure comparison.
- *Maintenance.* The rule is backward. A forward rule would store one `heavierThan` fact
  per ordered pair of weighed things, which grows with the square of their number;
  `CxSize.txt` gives the same reason in its header.

**Why not the other ways.** `greaterThan` and `lessThan` declare both arguments
`number`, and a measure is not a number. A rule that compares the two magnitudes as
numbers ignores the units, so 4500 grams outweighs 20 kilograms. A stored `heavierThan`
fact per pair restates what two weights already entail, and the stored fact stays after
one of the weights is corrected.

**Audit.** `prove` the derived relation for a pair whose measures are stated in two
different units, and for the reverse pair; the first proves and the second does not. For a
forward rule over a comparison, run `why` on a conclusion and confirm it names the
`conversionFactor` rows the comparison read.
