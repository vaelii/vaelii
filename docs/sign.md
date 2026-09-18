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

Nobody knows how fast the tap runs. Nobody knows how fast the drain empties. Everybody
knows that the tub fills when the tap runs faster than the drain, and that is a real
inference over quantities with no figure attached to any of them.

`vaelii.impl.sign` is that inference. A quantity's **sign** is one of three values —
`SignNegative`, `SignZero`, `SignPositive` — and three declared relations say which
quantities add, subtract and multiply into which. There are no numbers anywhere in the
layer.

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

Seven predicates, all in `resources/kb/upper/CxMeasure.txt`, beside the measures because
they are about the same quantities the measures measure:

| | |
|---|---|
| `(signOf Q S)` | Q is negative, nil or positive |
| `(trendOf Q S)` | Q is falling, steady or rising — the sign of its rate of change |
| `(derivativeOf R Q)` | R is the rate at which Q changes |
| `(qualitativeSum A B Q)` | Q is A + B |
| `(qualitativeDifference A B Q)` | Q is A − B |
| `(qualitativeProduct A B Q)` | Q is A × B |
| `(greaterInMagnitudeThan A B)` | A is further from zero than B |

The three arithmetic relations are **declarations about which quantities stand in the
relation**, not sentences about numbers. `(qualitativeSum Tap Drain NetFlow)` says the
net flow is the sum of the two; what either of them *is* nobody has said, and the whole
point is that nobody has to.

The three sign values are individuals of the type `sign_value`, and they are **jointly
exhaustive and pairwise disjoint** over the reals: exactly one holds of any quantity.
That is the same property a relation algebra's base relations have ([qcn.md](qcn.md)),
and it is what makes a *set* of them a real constraint rather than an absence of
knowledge — and what licenses a refutation.

## The tables

**Addition.** Zero is the identity, like signs keep theirs, and opposite signs are the
whole problem:

| + | − | 0 | + |
|---|---|---|---|
| **−** | − | − | ? |
| **0** | − | 0 | + |
| **+** | ? | + | + |

`?` is not a failure to compute. The total takes the sign of whichever addend is larger
and is nil when they are equal, so **all three values survive**, and a goal about the sum
is answered with nothing at all. Guessing one of three is the single thing this layer
exists not to do.

**What resolves it** is `(greaterInMagnitudeThan A B)`: the sum then takes A's sign, and
it is not zero, because "further from zero" is strict. The comparison is between two
*quantities*, which is what separates it from `quantityGreaterThan` — that one compares
two ground `(QuantityFn …)` terms through the unit table ([quantity.md](quantity.md)) and
is the wrong tool here, since the case sign arithmetic is for is exactly the one where
nobody has a figure. It is declared `transitive` and `asymmetric`, a strict order, so a
cycle of magnitude claims is a contradiction the KB reports.

**Subtraction** is addition with the subtrahend negated, so it shares the table and its
ambiguity — with the cases turned round. Two quantities of the *same* sign are the
ambiguous difference, and the same comparison resolves it.

**Multiplication** is never ambiguous. Anything times nothing is nothing, like signs give
a positive, opposite signs a negative, and magnitudes do not come into it — so no
comparison is ever read for a product.

## Trends are signs, one edge along

`(trendOf Q S)` is not a second theory. `(derivativeOf R Q)` says R is the rate at which Q
changes, and a trend is that rate's sign read at the other end of the edge. So there is
one arithmetic and one fixpoint, and the edge is a constraint **both ways**:

- *down* — a rate whose sign is known makes the quantity it is the rate of rising, falling
  or steady. That is the tub.
- *up* — a quantity stated rising pins the rate that produced it, which can then be an
  addend of something else, and it makes two rates declared of one quantity agree rather
  than sit side by side.

A rate is an ordinary quantity, so **the rate of a sum is stated as a sum of the rates**
rather than read off the sum. That is deliberate: `d(A+B) = dA + dB` is true and
`d(A×B)` is not a function of `dA` and `dB` at all, so a rule inferring rate arithmetic
from quantity arithmetic would be right for two of the three relations and quietly wrong
for the third. Writing the rate relation down is one sentence and it is always right.

`trendOf` is stated directly where the rate has no name worth giving it — a cooling body's
temperature falls, and nothing needs to be called the cooling.

## The fixpoint

The reading is a **greatest fixpoint** over sets of possible signs, and it is the same
shape as a path-consistency pass:

- a **state** is `{[attribute quantity] → [#{signs} #{handle}]}`, where the attribute is
  `:sign` or `:trend` and an unrecorded key is all three values — nothing known;
- a **constraint** narrows one key by what its inputs allow. Each arithmetic relation is
  one; each `derivativeOf` edge is two, one per direction;
- a stated `(signOf Q S)` narrows Q to that one value, and **two that disagree narrow it
  to nothing**;
- the pass runs every constraint until nothing shrinks.

It terminates because every step shrinks a set in a three-element lattice over finitely
many keys, and it reaches the same state whatever order the constraints are taken in:
intersection is commutative and associative, so the fixpoint is unique.

**A set narrowed to nothing is a contradiction.** The reading is then `:inconsistent`, an
entry goes to the `(violations kb)` ledger as `:sign-inconsistency` naming the quantities
that emptied, and **no** sign goal in that context is answered — not even one stated
outright, since an unsatisfiable theory is not mined for conclusions. It is a report and
not a `wff` refusal for the three reasons [qcn.md](qcn.md) gives: `wff` throws and would
blame whichever fact arrived last where the clash is a property of the set, the check
costs a fixpoint and `wff` runs per assert, and the prover is opt-in.

`signOf` is deliberately **not** declared `functional`, though a quantity has one sign.
`functional` merges two symbol arguments through the equality partition
([equality.md](equality.md)), so a KB that had said both positive and negative would have
`SignPositive` and `SignNegative` made one term instead of the contradiction reported.

## What a derived sign rests on

`SignProver` implements `prover-types/SupportingProver`, so each answer comes back with the
handles behind it and a forward rule joining on a derived sign is an ordinary firing that
the JTMS withdraws when one of them goes.

A narrowing's support is the union of its inputs' supports, the relation's own handle, and
the comparison's handle where one was read — accumulated **only when the set actually
moved**, so a constraint that merely agrees with what is already known adds no handle and
a conclusion rests on what pinned it. It over-approximates one derivation on the two
counts [qcn.md](qcn.md) states for the qualitative side, and what is guaranteed is the
piece a justification needs: every handle named was really read, and the set is enough to
have produced the answer on its own.

**Which** witness a narrowing names is one among several, so the constraints are taken in
an order fixed by their **content** — the relation and its arguments, and for a derivative
edge which way it runs. A run keyed on arrival order would make what a conclusion rests on
depend on when its facts were stored, which is the thing [nmtms.md](nmtms.md) refuses. The
same reason `qcn-kb/tighten-with-support` declines a warm start.

`support-sources` names all seven predicates, so a `greaterInMagnitudeThan` arriving
*after* the rule and the facts re-joins the rules carrying a sign antecedent
([inference.md](inference.md), "What a computed answer rests on"). Without it the tub
would fill or not depending on which of the five sentences was written last.

## Reading out

A goal `(signOf Q S)` is answered by **entailment**: the possible set must be exactly the
sign named, since anything wider leaves the question open. An open `S` binds when the set
is a singleton; an open `Q` enumerates the quantities the reading records, in a content
order. `(not (signOf Q S))` is answered by **refutation** — the possible set excludes that
sign — licensed by the three values being jointly exhaustive and pairwise disjoint, so
ruling one out proves the negation rather than failing to prove the claim.

A quantity the reading never reached is answered with nothing at all, under either
polarity. There is no closed world here: a term nobody mentioned has no sign the engine
knows and no sign it can rule out.

`cost` is `:compute` (a fixpoint over the stored facts before the first answer),
`est-bindings` is 1 for a ground check and a small constant otherwise — an estimate must
not cost what it estimates, and counting the reading's quantities is the whole pass — and
`completeness` is 100: the stated facts are read *into* the reading and answered back out
of it, so unioning a raw fact match in would add nothing.

The reading is **resident** on the KB, stamped with the change clock exactly as a
qualitative network is ([qcn.md](qcn.md), "The network is resident, and the clock is what
makes that sound"), so a rule joining a sign antecedent over many bindings reads the KB
once rather than once per binding.

## Opt-in

```clojure
(v/add-reasoner kb :sign)
```

The prover is opt-in and the vocabulary is not — the same split every calculus takes. Until
it is registered a KB stores and retrieves `signOf` and the rest as ordinary facts, and
composes none of them.

It is opt-in rather than a member of `default-provers`, where `QuantityProver` sits,
because of what it reads. A measure comparison is computed from the two ground measures in
the goal against a small table, answers at `:lookup` cost, and is never a stored fact. A
sign is a property of a *network* of stated facts and relations, and registering the prover
changes what a KB **derives** from what it has stored — which is exactly what
`add-reasoner` is the documented opt-in for. The namespace boundary agrees:
`default-provers` lives in `vaelii.impl.provers`, which this namespace requires, so a
default registration would be a require cycle. The six calculi and the three temporal
reasoners are exposed the same way for the same two reasons.

## What is not here

- **No magnitudes.** Two positives are two positives; nothing here holds "how much", and
  a KB that does have figures compares them with [quantity.md](quantity.md)'s measures.
  The two layers do not meet: a `weightOf` measure is not read into a sign, and a sign is
  not read out as a measure.
- **No reverse arithmetic.** A sum's sign is derived from its addends' and never the other
  way about: knowing the total and one addend does bound the other, and that is a second
  pass this does not run. The `derivativeOf` edge is the one constraint that runs both
  ways, because it is an identity rather than an implication.
- **No division.** `qualitativeProduct` covers the sign of a quotient — the sign table is
  the same — but nothing declares one, so a KB that wants it states the product the other
  way round.
- **No time.** A trend is the sign of a rate and says nothing about *when*. What holds at
  a moment is the event calculus in [time.md](time.md), and the two are not connected.
