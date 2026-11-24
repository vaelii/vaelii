# Sign arithmetic — which way a quantity is going

- **Covers:** the three-valued sign domain, the `signOf` / `trendOf` vocabulary and the
  `derivativeOf` edge between them, the three qualitative arithmetic relations and their
  tables, the one ambiguous entry and the comparison that resolves it, the fixpoint the
  prover runs, and what a derived sign rests on.
- **Not here:** comparing two *measures* against a unit table →
  [quantity.md](quantity.md); how long an interval is →
  [duration.md](duration.md); relation algebras over jointly-exhaustive base relations →
  [qcn.md](qcn.md); what a `SupportingProver` owes a forward join →
  [inference.md](inference.md).
- **Assumes:** context, belief, handle, support, prover, forward join →
  [glossary.md](glossary.md).

Nobody knows how fast the tap runs or how fast the drain empties, and everybody knows the
tub fills when the tap runs faster than the drain. `vaelii.impl.sign` draws that
inference. A quantity's **sign** is one of `SignNegative`, `SignZero`, `SignPositive`,
and three declared relations say which quantities add, subtract and multiply into which.
The layer holds no numbers.

## The vocabulary

```clojure
(signOf   Tap      SignPositive)      ; the tap adds water
(signOf   Drain    SignNegative)      ; the drain takes it away
(qualitativeSum Tap Drain NetFlow)    ; the net flow is their sum
(derivativeOf   NetFlow WaterLevel)   ; and the net flow is how fast the level moves

(greaterInMagnitudeThan Tap Drain)    ; the tap runs faster than the drain

(v/ask? kb '(signOf  NetFlow    SignPositive) ctx)   ;=> true
(v/ask? kb '(trendOf WaterLevel SignPositive) ctx)   ;=> true — the tub fills
```

The seven predicates live in `resources/kb/upper/measure.txt`, beside the measures:

| | |
|---|---|
| `(signOf Q S)` | Q is negative, zero or positive |
| `(trendOf Q S)` | Q is falling, steady or rising — the sign of its rate of change |
| `(derivativeOf R Q)` | R is the rate at which Q changes |
| `(qualitativeSum A B Q)` | Q is A + B |
| `(qualitativeDifference A B Q)` | Q is A − B |
| `(qualitativeProduct A B Q)` | Q is A × B |
| `(greaterInMagnitudeThan A B)` | A is further from zero than B |

The arithmetic relations say which quantities stand in the relation; no fact states what
any of them amounts to. Every position that holds Q, R, A or B is declared `quantity`, so
`(signOf Tap SignPositive)` derives `(quantity Tap)`.

The three sign values are individuals of the type `sign_value`, **jointly exhaustive and
pairwise disjoint** over the reals, the property a relation algebra's base relations have
([qcn.md](qcn.md)). So a set of them is a constraint, and excluding a value proves the
negation.

## The tables

**Addition.** Zero is the identity, like signs keep theirs, and opposite signs take the
sign of the larger addend:

| + | − | 0 | + |
|---|---|---|---|
| **−** | − | − | ? |
| **0** | − | 0 | + |
| **+** | ? | + | + |

At `?` **all three values survive**, and a goal about the sum is answered with nothing.
A stated `(greaterInMagnitudeThan A B)` resolves it: the sum takes A's sign, and is not
zero, since the order is strict. The comparison is between two quantities with no figure;
`quantityGreaterThan` compares two ground `(QuantityFn …)` terms ([quantity.md](quantity.md)).

**Subtraction** is addition with the subtrahend negated, so two quantities of the *same*
sign make the ambiguous difference, and the same comparison of the two quantities
resolves it.

**Multiplication** is never ambiguous: anything times zero is zero, like signs give a
positive and opposite signs a negative.

## Trends are signs, one edge along

`(derivativeOf R Q)` says R is the rate at which Q changes, and `(trendOf Q S)` is R's
sign read at Q. One arithmetic and one fixpoint serve both, and the edge constrains
**both ways**:

- *down* — a rate with a known sign makes its quantity rising, falling or steady.
- *up* — a stated trend determines the rate, which can then be an addend elsewhere, and two
  rates declared of one quantity take the same sign.

A rate is an ordinary quantity, so **the rate of a sum is stated as a sum of the rates**.
No rule infers rate arithmetic from quantity arithmetic: `d(A+B) = dA + dB` holds, and
`d(A×B)` is not a function of `dA` and `dB`. `trendOf` is stated directly where the rate
has no name.

## The fixpoint

The reading is a **greatest fixpoint** over sets of possible signs, computed as a
path-consistency pass is (`resolve-state` documents the state and constraint maps). Each
arithmetic relation is one constraint and each `derivativeOf` edge two; a stated sign
narrows its quantity to one value, and two stated signs that disagree narrow it to
nothing. Every step shrinks a set in a three-element lattice over finitely many keys, so
the pass terminates, and intersection is commutative and associative, so the fixpoint
does not depend on constraint order. The pass re-applies a constraint only after one of
its inputs moved, and a narrowed quantity's support shares the supports it was derived
from rather than copying them, so a chain of n links costs n narrowings and a rebuild of
the reading is linear in the sign facts (`lein perf`'s `sign-chain-rebuild`).

**A set narrowed to nothing is a contradiction.** The reading is then `:inconsistent`, and
**no** sign goal in that context is answered, a stated one included. The settle of the
write that empties a set stores one `(contradicts …)` per region (`sign/unsatisfiable-regions`).
A region is the quantities the constraints link to an emptied one. Its members are the
stated signs of those quantities and the facts of the constraints that narrow them. It files a
`:sign-inconsistency` entry naming the emptied quantities and the sentence, and
`try-assert` refuses the write, as for a qualitative network
([qcn.md](qcn.md#support-what-an-entailed-relation-rests-on)). It is not a `wff`
refusal ([why not](defenses.md#an-impossible-network-is-reported-off-the-pass-not-thrown-as-a-wff-check)).

`signOf` is **not** declared `functional`, though a quantity has one sign. `functional`
merges two symbol arguments through the equality partition ([equality.md](equality.md)),
so a KB that said both positive and negative would have `SignPositive` and
`SignNegative` made one term instead of the contradiction reported.

## What a derived sign rests on

`SignProver` implements `prover-types/SupportingProver`, so each answer carries the
handles behind it, and the JTMS withdraws a forward firing on a derived sign when one of
them goes.

A narrowing's support is the union of its inputs' supports, the relation's handle and,
where a stored comparison decided the result, the comparison's handle, added **only when the
set moved**. A comparison decides only a sum whose addends can have opposite signs, so a
product, or a sum of like signs, does not rest on one. It
over-approximates one derivation on the two counts [qcn.md](qcn.md#support-what-an-entailed-relation-rests-on)
states. The constraints run in an order fixed by their **content** (relation, arguments,
edge direction), so which witness a narrowing names does not depend on arrival order
([nmtms.md](nmtms.md)).

`support-sources` names all seven predicates, so a `greaterInMagnitudeThan` arriving
*after* the rule and the facts re-joins the rules carrying a sign antecedent
([inference.md](inference.md), "What a computed answer rests on").

## Reading out

A goal `(signOf Q S)` is answered by **entailment**: the possible set must be exactly
`S`. An open `S` binds when the set is a singleton; an open `Q` enumerates the quantities
the reading records, in content order. `(not (signOf Q S))` is answered by
**refutation**: the possible set excludes `S`. An open `S` under a negation is not
answered.

A quantity the reading never reached is answered with nothing under either polarity:
the engine knows no sign for it and can rule none out.

`core/sign-reading` returns the reading itself: each quantity's possible signs and trends
as sign terms, `:consistent?`, and no entry for a quantity the reading never reached. An
inconsistent reading keeps its sets there, an emptied quantity's set `#{}`, though no goal
is answered from it. It is a read, as `qualitative-network` is, and answers whether or
not the prover is registered. The browser's `/signs` page draws it
([web.md](web.md#the-sign-drawing)).

`cost` is `:compute` and `completeness` is 100. The reading is **resident** on the KB,
keyed by the change clock as a qualitative network is ([qcn.md](qcn.md), "The
network is resident, and the clock is what makes that sound"), so a rule joining a sign
antecedent over many bindings computes it once.

## Opt-in

```clojure
(v/add-reasoner kb :sign)
```

The prover is opt-in and the vocabulary is not. Until the prover is registered a KB
stores and retrieves `signOf` and the rest as ordinary facts and composes none of them.
`QuantityProver` sits in `default-provers` because it computes from the two ground
measures in the goal at `:lookup` cost; a sign is read off a network of stored facts, and
registering the prover changes what a KB derives.

## What is not here

- **No magnitudes.** A KB with figures compares them with [quantity.md](quantity.md)'s
  measures. The two layers do not meet: a measure is not read into a sign, and a sign is
  not read out as a measure.
- **No reverse arithmetic.** A sum's sign is derived from its addends' and never the other
  way about, though the total and one addend bound the other. The `derivativeOf` edge is
  the one constraint that runs both ways.
- **No chained comparison.** `greaterInMagnitudeThan` is declared `transitive`, and the
  reading consults only the stored comparisons: `A > B` and `B > C` leave a sum of `A`
  and `C` ambiguous although `(greaterInMagnitudeThan A C)` is answered true.
- **No division.** The sign of a quotient is the sign of a product, and a KB states the
  product the other way round.
- **No time.** A trend is the sign of a rate and says nothing about *when*. What holds at
  a moment is the event calculus in [time.md](time.md), and the two are not connected.
