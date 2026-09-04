# The predAll quantifier family

- **Covers:** the eight `pred*` relations that quantify one argument position of a binary
  predicate and fix the other, in three semantic classes — the *Instance* pair that stamps
  a rule, the *Exists* four that derive nothing, and the *Specified* pair that audits; the
  `indeterminate_term` determinacy category behind the audit; the identity exemption that
  category carries; and the entry points that run the audit.
- **Not here:** the generator mechanism the *Instance* pair is built on →
  [generators.md](generators.md); the equality closure and the unique-name assumption the
  exemption is carved out of → [equality.md](equality.md); a skolem constant and how one is
  minted → [skolem.md](skolem.md); tying membership to a defining condition →
  [defns.md](defns.md).
- **Assumes:** collection, binary predicate, rule, forward chaining, `genl`, belief
  filtering → [glossary.md](glossary.md), [taxonomy.md](taxonomy.md),
  [inference.md](inference.md).

A binary predicate has two argument positions. A quantifier-family declaration says how
each position is filled: one position ranges over a collection's members and the other
holds a fixed term, or both range over collections. Each relation names its two positions
in order, so `predAllInstance` quantifies position 1 universally and fixes position 2,
while `predInstanceAll` fixes position 1 and quantifies position 2.

| | fixed second argument | collection second argument |
|---|---|---|
| **universal first** | `predAllInstance` (stamps a rule) | `predAllExists` (inert) · `predAllSpecified` (audit) |
| **existential first** | `predExistsInstance` (inert) | `predExistsAll` (inert) |
| **fixed first** | — | `predInstanceAll` (stamps a rule) · `predInstanceExists` (inert) |
| **audited first** | — | `predSpecifiedAll` (audit) |

The three classes differ in what the engine does with a declaration, and the difference is
the whole design. *Instance* declarations produce inference. *Exists* declarations produce
none. *Specified* declarations produce a report a caller asks for.

## Instance: the declaration stamps a rule

`predAllInstance` and `predInstanceAll` are **rule generators**
([generators.md](generators.md)). The CxCore declaration beside each one is a rule whose
consequent is a rule:

```clojure
(implies (predAllInstance ?pred ?indep ?fixed)
         (set/defaultRule (implies (?indep ?x) (?pred ?x ?fixed))))
```

Asserting `(predAllInstance sign negative_integer "negative")` grounds `?pred`, `?indep`
and `?fixed`, and the firing stamps the concrete rule `(implies (negative_integer ?x)
(sign ?x "negative"))`. Every rule the index keys therefore carries a concrete functor,
which is what a generator buys over a rule with a variable in its consequent
([indexing.md](indexing.md)).

Descent to the members is ordinary chain inference from there. A member asserted later
fires the stamped rule, the conclusion carries a justification, and retracting the
membership retracts the conclusion. Backward, the stamped rule's antecedent is discharged
inside a `query` or `prove` proof, so `(sign -212 "negative")` is provable from the bare
literal `-212` — the membership `(negative_integer -212)` comes from the evaluative
`defnSufficient` prover ([defns.md](defns.md)). `ask` answers the same goal false, because
no member of the prover registry expands a rule ([levels.md](levels.md)).

## Exists: the declaration is a record and nothing else

The four relations with `exist` in the name are **inferentially inert**. Each declaration
is stored and queryable like any other fact, and the engine derives nothing from it: no
stamped rule, no skolemized witness, no materialized membership.

Each cell instead sanctions a **placeholder functor** an author may use to name the
required filler — `PredAllExistsFn`, `PredExistsAllFn`, `PredExistsInstanceFn` and
`PredInstanceExistsFn`, one per cell and carrying that cell's full argument list. Each is
an `unreifiable_function`, so a ground application stays a structural NAT the reader keeps
readable inside the sentence ([nat.md](nat.md)). Asserting one into a sentence is the
author's act. The engine never asserts a placeholder, and a placeholder an author did
assert counts as a determinate filler for the audit below.

Inertness is also what makes all four cells expressible. `predExistsInstance` and
`predInstanceExists` are pure existentials with no universal to range over, so a generator
has no collection to range a stamped rule over and fails range restriction there. The
alternative — a plain rule with a variable functor in its consequent — files under the
concluding-rule catch-all and makes the query planner see a candidate rule for every
predicate in the KB. A declaration that stamps nothing has neither problem.

## Specified: an integrity audit a caller runs

`predAllSpecified` and `predSpecifiedAll` state a requirement rather than a fact:

```clojure
(predAllSpecified hasPet person)   ; every person should have a determinate pet
```

Binary on purpose: the required filler type is never restated in the declaration — it is
**derived from the predicate's own slot contract** (`(arg hasPet 2 pet)` here; a
`genlArg`-typed slot derives a subtype constraint instead, and multiple constraints
compose conjunctively). A declaration over a predicate with no visible slot typing is a
**declaration-contract gap** the audit reports explicitly, never a silently unconstrained
audit.

Nothing fires on assert. The requirement is checked when a caller asks:

```clojure
(v/specified-violations kb 'hasPet 'person 'CxUniverse)
;; => {:status :audited :violations #{Bob}}   ; Bob has no filler
(v/all-specified-violations kb 'CxUniverse)
;; => {[predAllSpecified hasPet person] {:status :audited :violations #{Bob}}}
```

Discriminate on `:status`, not key presence — a `{:status :gap …}` result carries no
`:violations` key, and a bare `(:violations r)` read would nil-pun the gap into a
clean pass. Two gap kinds ship: `:missing-slot-typing`, and
`:legacy-ternary-declaration` for a stored pre-migration ternary sentex the bulk
import path can carry past the assert-time refusal.

`specified-violations` audits one declaration and reports the instances with no admissible filler.
`all-specified-violations` audits every declaration visible in the context and omits the
ones that hold — but never a `{:gap …}` — so an empty map is a clean sweep and a gap
cannot pass as one. Both read the KB and store nothing. `predSpecifiedAll` is the
argument-swapped twin, audited by passing `:first` as the argument position; its filler
contract derives from slot 1.

The membership arm rides the KB's own reading: with `(arg hasPet 2 pet)` visible,
argument-type inference types a stored filler off that very declaration, so the
instance-position bite is existence + determinacy (plus any actively refuted membership) —
the conformance bite for instance-positions lives at the assert-time checker, and an
audit stricter than the contract it derives from would be a second type system. The
subtype arm still convicts on its own: nothing derives a `genl` edge for a filler, so a
kind the checker excused as evidence-free still violates.

**The function marks derive both.** `(injection P)`, `(surjection P)` and `(bijection P)`
are declared of a predicate rather than of a pair of collections, and CxCore rules read
only the quantified side — the domain off `(arg P 1 D)` for totality, the range off
`(arg P 2 R)` for ontoness — to derive `(predAllSpecified P D)` and
`(predSpecifiedAll P R)`; the filler types are the audit's to derive:
`predAllSpecified` is that family's totality, and `predSpecifiedAll` its ontoness
([taxonomy.md](taxonomy.md)). A derived declaration is a stored sentex like a written one,
so the sweep above reports it with no extra entry point, and retracting the mark or either
`arg` declaration withdraws it.

The cost is one read per member of the quantified collection, plus one membership read per
candidate filler. This is a sweep to run at a checkpoint, not a check to run per write.

## indeterminate_term: what makes a filler determinate

A filler satisfies a *Specified* requirement only when it is **determinate**. A term is
indeterminate exactly when it belongs to the `indeterminate_term` category, which is
extensible:

- **Skolem constants** are the built-in first member. A skolem's membership is never a
  stored fact, because a firing mints one dynamically, so it is read off the `SkolemFn`
  expression the constant was minted from ([skolem.md](skolem.md)).
- **A further kind** joins with `(genl NewKind indeterminate_term)`. Membership in the
  subkind then reaches the category through the ordinary `genl` closure.

Everything else is determinate: a bare individual, a literal, and a non-skolem NAT
including an *Exists* placeholder. That is what makes the *Specified* class the exact
antagonist of the *Exists* class. A placeholder an author wrote down satisfies the
requirement, and a witness the engine skolemized does not.

Membership is what the KB **holds** — a stored or derived fact, or a `genl` edge into the
category — and not what a prover can infer on demand. An argument-type declaration that
makes `(vague_kind Hazy)` answerable at query time does not put `Hazy` in the category.
One implementation answers the question (`vaelii.impl.provers/indeterminate-term?`), and
both the audit and the prover below call it, so the two cannot disagree about a term.

## The identity exemption

The unique-name assumption is **suspended** for an unpinned indeterminate term. Distinct
symbols normally denote distinct individuals, and `(different X Y)` is provable exactly
when the arguments lie in no shared equivalence class ([equality.md](equality.md)). An
indeterminate term stands for some object without pinning down which, so it is not provably
different from anything:

```clojure
(v/ask? kb (list 'different skolem-constant 'Alice) 'CxUniverse)   ; => false
(v/assert kb (list 'rewriteOf 'Real skolem-constant) 'CxUniverse)  ; pin it
(v/ask? kb (list 'different skolem-constant 'Alice) 'CxUniverse)   ; => true
```

A merge is the lifting condition. `rewriteOf`, `sameAs` or `equals` moves the term's
representative off the term itself, and the exemption reads that self-representative state
rather than a mark of its own.

Two consequences follow. A `different` goal with an indeterminate argument is
unprovable as a whole, even where two of its other arguments are determinate and distinct.
And `same-class?` is no longer the complement of a provable `different`: both read false of
an unpinned indeterminate term, so a caller wanting *provably different* asks `different`
and reads that answer.

## Stratification

`different` is negation as failure over two things: the equality closure, and the
`indeterminate_term` category. Asserting into either one **withdraws** a `different` that
held before. A rule that concludes into either from a `different` antecedent is therefore a
cycle through negation, and the stratification check refuses it at assert
([exceptions.md](exceptions.md)):

```clojure
(v/assert kb '(implies (and (pRel ?x ?y) (different ?x ?y)) (sameAs ?x ?y)) 'CxUniverse)
;; => :not-stratified
(v/assert kb '(implies (and (pRel ?x ?y) (different ?x ?y)) (indeterminate_term ?x)) 'CxUniverse)
;; => :not-stratified
```

The negative edge runs to the relations that can withdraw a difference, not to `different`
itself, because nothing ever concludes `different`. Those relations are `rewriteOf`,
`sameAs`, `equals`, `indeterminate_term`, every subkind of `indeterminate_term` the
taxonomy holds, and `genl`. The last one is an over-approximation: only a `genl` into the
category's closure withdraws anything, and the consequent's second argument is a variable
when the check runs, so the two cannot be separated there. No shipped rule reads
`different`, so no KB the bundled ontology builds pays for it.

## A `different` guard is re-checked, not supported

A rule guarded by `(different ?x ?y)` is order-independent, and the mechanism is worth
naming because the obvious one does not work. `SupportingProver` is how a prover-answered
antecedent keeps a firing honest: the prover reports the handles its answer was read from,
the join adds them to the firing's antecedents, and the ordinary relabel withdraws the
conclusion when one goes. `different` can report nothing. It holds by the **absence** of a
merge, it is not assertible, and so no handle for it exists anywhere in the KB.

The re-check index answers it instead — the same index `unknown`, `exceptWhen`, aggregates
and closed-extent negatives use. A rule reading `different` is registered under the
predicates that can flip it (`rules/different-flip-predicates`: the three equality
relations, `indeterminate_term` and `genl`), a fact arriving on one queues the rule, and
`chain/different-blocks?` re-evaluates the guard against the firing's settled bindings.
The firing is blocked where the guard has stopped holding and comes back when it holds
again, so a merge, an indeterminacy declaration and their retractions all reach it:

```clojure
(v/assert kb '(implies (and (pRel ?x ?y) (different ?x ?y)) (qRel ?x ?y)) 'CxUniverse)
(v/assert kb '(pRel Aa Bb) 'CxUniverse)
(v/ask? kb '(qRel Aa Bb) 'CxUniverse)          ; => true
(v/assert kb '(indeterminate_term Aa) 'CxUniverse)
(v/ask? kb '(qRel Aa Bb) 'CxUniverse)          ; => false, withdrawn
```

Asserting the same three sentences in the other order reaches the same belief, which is
the order independence [README.md](../README.md) requires. An index written before this
registration existed does not carry the posting until `recover` rebuilds it.

## Where the engine stops

Existential inference is not attempted. Nothing derives a filler from a `predAllExists`
declaration, so `(thereExists ?x (parts Lain ?x))` is unprovable from one. The placeholder
functor is the vocabulary an author uses instead.
