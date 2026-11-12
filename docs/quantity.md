# Measures: the measure-evaluating quantity prover

- **Covers:** how two ground measures are compared by normalizing against a
  `dimensionOf` / `conversionFactor` table, with an epsilon tolerance.
- **Not here:** why a measure term stays structural instead of reifying to a
  constant → [nat.md](nat.md); interval arithmetic like total or overlap duration →
  [duration.md](duration.md); reasoning about a quantity nobody has put a figure on →
  [sign.md](sign.md).
- **Assumes:** sentex, context, structural NAT, deferred literal →
  [glossary.md](glossary.md).

A **measure** is a structural NAT — an `unreifiable_function` application that stays *structural*
so its magnitude and unit are readable ([nat.md](nat.md)):

```clojure
(QuantityFn 5 Kilogram)            ; a point measure — 5 kilograms
(QuantityIntervalFn 1 2 Meter)     ; an interval measure — [1, 2] metres
```

`QuantityProver` (`vaelii.impl.provers`) answers five comparisons over two ground
measures by **normalizing** each against the KB's `dimensionOf` / `conversionFactor`
table and comparing:

```clojure
(sameQuantity M1 M2)
(quantityLessThan M1 M2)          (quantityGreaterThan M1 M2)
(quantityLessThanOrEqual M1 M2)   (quantityGreaterThanOrEqual M1 M2)
```

Nothing is stored or asserted. A comparison is a **computed** result, never an
asserted equality — the equality closure ([equality.md](equality.md)) refuses numbers
and compounds, so `sameQuantity` deliberately routes nowhere near it.

## The table

Two ordinary stored facts drive normalization, both read through
`res/matches-visible` (belief- and context-filtered):

```clojure
(dimensionOf Kilogram Mass)            ; Kilogram measures the Mass dimension
(conversionFactor Gram Kilogram 0.001) ; one Gram = 0.001 of the base unit Kilogram
```

Put them in a context every querent sees (e.g. `CxUniverse`) so the prover finds
them from any asking context. A quantity comparison in a **rule antecedent** is a
deferred literal, and the forward join asks the registry at the wildcard `'?ctx` where a
backward search asks at its goal's context ([inference.md](inference.md)). The forward
read does not reach past scoping: the firing's justification names the table rows the
comparison converted through ([below](#what-a-comparison-rests-on)), so placement puts the
conclusion only in a context that sees those rows as well as the rule and the fact, and a
rule and a fact in a sibling of the table derive nothing
(`computed_support_test/a-unit-table-the-rule-cannot-see-compares-nothing`). A table
split across contexts therefore derives only where one context sees every row a
comparison used.

**Three dimensions ship filled in.** `resources/kb/upper/measure.txt` states Length in
`Meter`, Mass in `Kilogram` and Duration in `Second`, with the ordinary units of each,
and `CxUniverse` sees it — so a KB that loads the starter compares measures without
declaring anything first. The test for a shipped unit is that its factor is a
*definition*: a minute is sixty seconds by stipulation, where how heavy a particular
thing is, is a measurement and belongs wherever that thing's facts do. A KB measuring
something else states its own units the same way, and a `starter-test` case holds the
shipped ones to converting direct-to-base within one dimension.

The table types its terms. `dimensionOf` declares its arguments `unit_of_measure` and
`physical_dimension`, so `(dimensionOf Kilogram Mass)` derives `(unit_of_measure
Kilogram)` and `(physical_dimension Mass)` ([argtypes.md](argtypes.md)). `QuantityFn` and
`QuantityIntervalFn` declare `measure` as their result, and every shipped position that
holds a measure (`weightOf`, `heightOf`, the five comparisons, `time.txt`'s durations) is
declared `measure`. An application there whose function declares a result that does not
reach `measure` is convicted with `:arg-type`, as is a number or a string: `assert` stores
the fact inert, never believed, and `try-assert` refuses it
([argtypes.md](argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert)).

## `normalize-quantity`

`(normalize-quantity kb measure context)` → `[dimension lo-base hi-base]`.

- **Dimension** is `(dimensionOf U ?d)`, or **the unit `U` itself** when the unit
  declares none. So two measures in the *same unit* are always comparable (their
  dimension is that unit), while two distinct undeclared units are not (their
  dimensions differ). A declared `dimensionOf` is what lets separate units share one
  dimension and compare.
- **Base magnitude** is `N × (conversionFactor U ?base ?factor)`, the factor defaulting
  to `1` when the unit declares none (it is then its own base). Conversion is
  **direct-to-base** — one multiply, no chaining — so every unit of a dimension must
  convert to a *single* base unit for the magnitudes to line up.
- A point `(QuantityFn N U)` has `lo-base = hi-base`; an interval keeps both bounds.

### A declaration the KB disagrees with itself about

Both reads take the binding every believed, visible match **agrees** on. Restating one
declaration in several contexts of the ancestor set is not a disagreement — the matches carry the
same bindings and collapse to one. Two declarations that differ are: the unit then falls
back to being its own dimension and its own base, exactly as an undeclared unit does, and
compares only against itself.

Reading the first match instead would answer whichever the index yields, and that is a
handle order — the same knowledge loaded in the other order would convert by the other
factor and give a different number out of the same KB, which is the one thing the engine
does not allow. So a doubly-stated reading is declined rather than adjudicated, the rule
`duration/interval-length-with-support` follows for two lengths and `stp/endpoints-with-support` for
two starts.

The base and the factor are **one** reading, taken together: a base from one declaration
and a factor from another would convert into a unit nothing said it converts to, and
`base-unit-of` — which decides the unit a computed answer is *rendered* in — would then
disagree with the arithmetic that produced it.

**An aggregate** over several measures answers only when every value has one dimension
and one base unit, the key a comparison requires, and renders in that base
(`provers/measure-bounds`). On a KB that has broken the direct-to-base contract, two units
of one dimension naming different bases, a sum over the two has no answer in any arrival
order.

## Comparison semantics

Comparisons hold only **within one dimension and one base unit**
(`provers/measure-with-support`). A dimension mismatch (`5 Kilogram` vs `5 Meter`) is
never equal or comparable — every comparison fails, and none throws. A unit with a
`dimensionOf` and no `conversionFactor` is its own base at factor 1, so `(QuantityFn 1
Foot)` under `(dimensionOf Foot Length)` alone compares with a foot and with no metre. An
aggregate over measures of two bases has no answer either (`provers/measure-bounds`).

The interval reading is **necessary** (definite): a comparison holds only when it holds
of every point of each interval. For points (`lo = hi`) it collapses to ordinary number
comparison:

| goal | holds iff |
|------|-----------|
| `sameQuantity A B` | `A.lo = B.lo` and `A.hi = B.hi` |
| `quantityLessThan A B` | `A.hi < B.lo` |
| `quantityGreaterThan A B` | `A.lo > B.hi` |
| `quantityLessThanOrEqual A B` | `A.hi ≤ B.lo` |
| `quantityGreaterThanOrEqual A B` | `A.lo ≥ B.hi` |

So `[1,2] < 5` holds, `[1,4] < [3,6]` does not (they overlap), and `[1,2] ≤ 2` holds
while `[1,2] < 2` does not.

## A functional measure slot

A `functional` slot that holds measures (`weightOf`, `heightOf`) holds one magnitude, not
one term. `provers/measures-agree?` decides whether two fillers clash: two measures agree
when they normalize under one `[dimension base-unit]` key and their bounds meet within the
tolerance. So `(QuantityFn 20 Kilogram)` agrees with `(QuantityFn 20000 Gram)`, with
`(QuantityIntervalFn 18 22 Kilogram)` and with `(QuantityIntervalFn 20 25 Kilogram)`, and
clashes with `(QuantityFn 30 Kilogram)` and with `(QuantityFn 20 Meter)`.

The functional check (`checks/functional-problems`) reads the agreement at the writing
context, so `try-assert` stores an agreeing filler. The settle reads it at each placement
context of the pair's nogood: a placement where the two agree is excluded
(`tuple/routes`' `:excluded-at`), so nothing is placed and both facts stay believed. A
unit-table row that is stored, retracted or relabelled re-places the pairs naming its
unit (`chain/unit-row-members`), so the table may arrive after the facts
(`quantity_test/a-unit-row-arriving-or-leaving-moves-a-functional-measure-clash`).

A reader below the placement context that declares a unit a second, different way reads
that unit as its own dimension, and no placement is made for it there.

The shipped table rows are `set/monotonic` (`measure.txt`'s header): a factor is a
definition, so a conclusion drawn through one keeps the strength of the facts and the
rule it rests on.

## Float policy: an epsilon tolerance

Cross-unit normalization multiplies a magnitude by a stored (usually floating-point)
factor, so exact `=` would make `5 Kilogram` and `5000 Gram` unequal on a last-bit
rounding difference. `provers/*quantity-tolerance*` (default `1e-9`, absolute) is the
slack: two base magnitudes are **equal** when they differ by at most it, and strict
`<` / `>` demand a gap **wider** than it — so exactly one of `<`, `=`, `>` holds for
any pair. Rebind the dynamic var for a coarser or finer policy.

The **rounding grid follows it**. A computed magnitude is snapped before it is rendered,
so a sum of converted magnitudes does not come back as `2.5000000000000004`, and the
number of decimal places that snap keeps is derived from the bound tolerance
(`-⌊log₁₀ tol⌋`: nine places at the shipped `1e-9`, three under a `1e-3` rebinding).
Grid and comparison are one policy, so two magnitudes the comparisons call equal are
never snapped to two different figures.

## Check-only, and deferred in rules

The prover is **check-only**: it claims a comparison only when *both* arguments are
ground measures, so `(sameQuantity ?x M)` is refused — not enumerated — and appears in
no query plan. It reports `cost :lookup` and `completeness 100` (a comparison is never
a stored fact and no rule concludes one, so it is the sole complete method and the
dispatcher runs it alone).

The five comparisons are **deferred predicates** (`vaelii.impl.sentex/deferred-predicates`),
so in a rule antecedent the planner places each after the literal that binds its measure
variable — like `evaluate` / `lessThan`:

```clojure
(implies (and (mass ?o ?q)
              (quantityGreaterThan ?q (QuantityFn 100 Kilogram)))
         (heavy ?o))
```

`(mass ?o ?q)` binds `?q` to a stored measure; the comparison is then computed against
it. Being deferred is *all* they share with the arithmetic comparisons — they are kept
out of `comparison-siblings` and `chained-comparisons`: `sameQuantity` is symmetric, not
directional, and a `quantityLessThan` chain crosses units, so folding one would smuggle
in a normalization the prover has not run.

## What a comparison rests on

`(quantityGreaterThan (QuantityFn 5000 Gram) (QuantityFn 1 Kilogram))` holds *because* a
gram is declared a thousandth of a kilogram. In a backward query that is a detail; in a
**forward** rule it is the whole question, because the firing stores a conclusion and no
other antecedent of the rule names the `conversionFactor` row. A firing that omitted it
would keep the conclusion after the row was retracted.

`QuantityProver` therefore implements `prover-types/SupportingProver`: `solve-with-support`
answers the same comparisons `solve` does, each paired with the `dimensionOf` and
`conversionFactor` handles both sides normalized through. The forward join adds them to the
firing's antecedents, so retraction reaches them, `why` names them, and placement requires
a context that can see them ([inference.md](inference.md), "What a computed answer rests
on"). The measure *terms* are not in that set and need not be: a comparison is check-only
over two ground measures, so whatever bound them was an ordinary matched antecedent and is
already there.

The support is **every** visible declaration the reading was taken over, not one of them —
`table-read` reads an agreement, and a second row that agrees collapses into it while a
second that disagrees declines it outright, so the reading is a property of the set. The
cost is that retracting one of two agreeing rows withdraws a conclusion the survivor would
still license; naming only the survivor would make belief depend on which row arrived
first, which is worse.

A unit that declares neither predicate contributes **no** handles, and that is not a gap:
"a unit is its own dimension" and "a unit with no factor is its own base" are what the
*absence* of a declaration means, and an absence is not a sentex a retraction can take
away. A declaration arriving *later* does change the answer, and `support-sources` is what
puts it in front of the rules concerned — a `conversionFactor` datum re-joins every forward
rule carrying a comparison antecedent, so the table may arrive after the rule and the facts
and still be believed the same.

## Where it lives

- `vaelii.impl.provers` — `QuantityProver`, `normalize-quantity`, `measure-comparisons`,
  `*quantity-tolerance*`. Registered in `default-provers`, so every KB has it.
- `resources/kb/upper/measure.txt` — the vocabulary: `QuantityFn` /
  `QuantityIntervalFn` (`unreifiable_function`), `dimensionOf` / `conversionFactor` (the
  table predicates), and the five comparisons, each documented by a comment sentex. An
  *upper* context, not the vocabulary head: measurement is subject matter, and only the
  grammar it is declared in (`unreifiable_function`, `binary_predicate`, …) is `core.txt`'s.
  The sign vocabulary shares the file ([sign.md](sign.md)) — same quantities, no
  figures — and shares nothing else: a measure is never read into a sign, and a sign is
  never rendered as a measure.
- `vaelii.impl.sentex/deferred-predicates` — the five comparisons, for rule-antecedent
  planning.

## Out of scope

- Interval *arithmetic* (total or overlap duration) — that is `vaelii.impl.duration`
  ([duration.md](duration.md)), which reads `normalize-quantity` and this tolerance but
  adds nothing to either.
- Derived-unit algebra (`m/s`, `kg·m`) and transitive conversion chains.
- An offset unit (Celsius against Kelvin): `conversionFactor` is a multiply, and no
  declaration carries an additive term.
- Binding mode: `(sameQuantity ?x M)` enumerates nothing; it is refused.
