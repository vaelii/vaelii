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
them from any asking context. That is not only convenience: a quantity comparison in a
**rule antecedent** is a deferred literal, and the forward join asks the registry at the
wildcard `'?ctx` where a backward search asks at its goal's context
([inference.md](inference.md)). So a unit table split across contexts reads whole
forward and per-ancestor-set backward, and one stated where every reader sees it is the one
arrangement under which the two agree.

**Three dimensions ship filled in.** `resources/kb/upper/CxMeasure.txt` states Length in
`Meter`, Mass in `Kilogram` and Duration in `Second`, with the ordinary units of each,
and `CxUniverse` sees it — so a KB that loads the starter compares measures without
declaring anything first. The test for a shipped unit is that its factor is a
*definition*: a minute is sixty seconds by stipulation, where how heavy a particular
thing is, is a measurement and belongs wherever that thing's facts do. A KB measuring
something else states its own units the same way, and a `starter-test` case holds the
shipped ones to converting direct-to-base within one dimension.

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
`duration/interval-length-with-support` follows for two lengths and `stp/endpoints-of` for
two starts.

The base and the factor are **one** reading, taken together: a base from one declaration
and a factor from another would convert into a unit nothing said it converts to, and
`base-unit-of` — which decides the unit a computed answer is *rendered* in — would then
disagree with the arithmetic that produced it.

**Which unit a reduction renders in** is the same question one step out. An aggregate over
several measures of one dimension reads `base-unit-of` off one of them, and the values
reach it in solution order — so on a KB that has broken the direct-to-base contract, two
units of one dimension naming different bases, the unit the answer came back in would be a
function of which measure was stored first. `provers/measure-bounds` takes the
**content-least** unit instead: still arbitrary where the KB is inconsistent, and the same
answer whatever the arrival order. Where the contract holds, every base agrees and the
choice never arises.

## Comparison semantics

Comparisons hold only **within one dimension**. A dimension mismatch (`5 Kilogram` vs
`5 Meter`) is never equal or comparable — every comparison fails, and none throws.

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
so in a rule antecedent the planner pins each after the literal that binds its measure
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
- `resources/kb/upper/CxMeasure.txt` — the vocabulary: `QuantityFn` /
  `QuantityIntervalFn` (`unreifiable_function`), `dimensionOf` / `conversionFactor` (the
  table predicates), and the five comparisons, each documented by a comment sentex. An
  *upper* context, not the vocabulary head: measurement is subject matter, and only the
  grammar it is declared in (`unreifiable_function`, `binary_predicate`, …) is CxCore's.
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
- Binding mode: `(sameQuantity ?x M)` enumerates nothing; it is refused.
