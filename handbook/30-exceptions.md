# 30. Exceptions

- **Covers:** stating a rule's exception with `exceptWhen`; the exception as a closed
  query; stating the excepted case's own conclusion beside it; the stratification check a
  rule set with exceptions passes; and the case where a more specific claim undercuts an
  inherited one with no `exceptWhen` at all.
- **Not here:** whether a default with exceptions or an enumeration fits a case →
  [ch. 25](25-default-or-enumerate.md); an `unknown` antecedent, the per-literal form of
  the same mechanism → [ch. 32](32-negation.md); argument-position preservation →
  [ch. 21](21-claims-about-kinds.md); strength classes → [ch. 24](24-strength.md).
- **Assumes:** [ch. 24](24-strength.md), [ch. 25](25-default-or-enumerate.md),
  [ch. 29](29-rules.md).

## The exception goes on the rule

**Practice.** When a general rule has a known class of exceptions, wrap the rule in
`(exceptWhen <condition> <rule>)`. The condition names the excepted case over the rule's
own variables.

**Example.** `CxNormalPhysicalConditions.txt` states that metal is solid at room
temperature, except mercury:

```clojure
(exceptWhen (mercury ?x)
  (set/defaultRule (set/forwardRule (implies (and (metal_stuff ?x)) (solid ?x)))))
```

`CxBiology.txt` states the same shape for a state that changes:

```clojure
(exceptWhen (dead ?x)
  (set/defaultRule (set/forwardRule (implies (and (organism ?x)) (alive ?x)))))
```

**Why.**

- Logical: `exceptWhen` is undercutting. For a binding under which the condition holds,
  the rule concludes nothing, so no contrary conclusion exists and nothing has to be
  arbitrated. For a portion of mercury the rule concludes no `solid` membership, so the
  portion's `liquid` membership meets no `solid` one and nothing clashes.
- Engine: under forward chaining, the excepted firing is stored with a guard `defeat`
  resting on the facts the condition holds through, and a reader that sees the defeat does
  not believe the conclusion. Retracting the blocker takes the defeat out, and the
  conclusion is believed again with nothing re-chained. Under backward chaining the
  argument is built and then reported as excepted, so `why-not` answers `:excepted` with
  the rule, the ground exception and the antecedents it went through. A conclusion the
  exception does not block is `:default` whatever the rule's own strength, because a
  later fact can block it.
- Maintenance: the exception is stored once, as a meta-sentex naming the rule, and
  re-evaluated per firing. It does not materialize a probe per non-excepted member, so
  the store grows with the exceptions that hold, not with the members they do not
  apply to. `kb-quality`'s `:clashes` reading lists rule pairs that would contradict each
  other if both fired, and marks `:excepted` a pair where one rule's `exceptWhen` names
  the other's case.

**Why not the other ways.** Two unrelated default rules concluding `P` and `(not P)`
connect nothing: both derive, and the two defaults tie, so the pair is reported in
`contradictions` as a dilemma rather than decided. Nothing records which one the author
meant to win, and `why` of each side is a separate tree. A third strength class between
`:monotonic` and `:default` would rank the specific rule above the general one, and the
engine has exactly two classes: an intermediate one would turn every unequal pair into a
three-way comparison, for a case `exceptWhen` handles with no rank. Ranking colliding
defaults by how specific their antecedent types are works only when the exception happens
to be keyed on a narrower type, so the engine builds no such ranking.

**Audit.** Read `kb-quality`'s `:clashes`. A pair the author intends one way carries
`:excepted true`; a pair with no exception is a dilemma the change states as one, or
gains its `exceptWhen`.

## The excepted case's own conclusion

**Practice.** When the excepted case has a positive contrary, state it as its own rule
beside the excepted one. The exception keeps the two from clashing.

**Example.** `CxBiology.txt` blocks the flight default for a penguin and, a few lines
below, concludes that a penguin cannot fly:

```clojure
(exceptWhen (penguin ?x)
  (set/defaultRule (set/forwardRule (implies (and (bird ?x)) (able ?x flying)))))
(set/forwardRule (implies (and (penguin ?x)) (not (able ?x flying))))
```

**Why.** The excepted rule declines to conclude for a penguin; the second rule concludes
something, that this penguin cannot fly, which an application can query and argue from.
Neither follows from the other. With the exception in place, the default's firing for a
penguin sits under a guard defeat and is not believed, so the negative meets no believed
positive and nothing is arbitrated. The same
file states death as a positive claim for the same reason: `(not (alive ?x))` follows from
`(dead ?x)` by its own rule, so a query for `(not (alive X))` has an answer, where
"never concluded alive" supports nothing.

**Why not the other ways.** The negative rule alone, with no exception, rebuts the
default instead of undercutting it. For a penguin known true, the negative is monotonic
and defeats the flight conclusion, so the KB stores a conclusion and its defeat. For a
penguin stated at the default strength, the two conclusions tie, and the pair is a
dilemma in `contradictions`. The exception alone leaves the KB unable to
answer `(not (able X flying))` for a penguin.

**Audit.** For each `exceptWhen`, decide whether the excepted case has a contrary worth
concluding, and state it or say in a `;;` note why not.

## The exception is a query

**Practice.** Write the condition as a closed query over the rule's bindings: one
literal, a vector of literals that must all hold, or a `thereExists` that binds its own
local variable. Make sure what the condition reads is stored: a fact, or the conclusion
of a forward rule.

**Why.**

- Logical: every free variable of the condition is bound by the rule's antecedents before
  it runs, so the condition is an existence check that stops at its first answer. An
  exception that no stored or forward-derived fact answers does not hold, and the rule
  fires: the open-world reading, matching `arg`, where an argument of unknown type
  violates nothing.
- Engine: the condition runs at level 6, the full prover stack without rule
  backchaining. It reaches through `genl` subsumption, `genlCx` visibility, transitive,
  symmetric and inverse metadata, disjointness and arithmetic, but a fact derivable only
  by a backward rule does not count. The bound keeps an exception from starting an
  unbounded proof search inside the belief fixpoint. A free variable no antecedent binds
  is refused at assert (`:exception-not-closed`), and a `thereExists` binder the
  antecedents also name is refused `:quantifier-not-local`.
- Context: the condition is evaluated in the conclusion's placement context, and an
  exception stated in a context below the conclusion's blocks nothing there.

**Why not the other ways.** A condition read through a backward rule never holds, so the
rule fires on exactly the case its author excepted. Blocking on "cannot tell" would let a
missing fact suppress knowledge silently.

**Audit.** For each predicate an exception reads, name the stored facts or the forward
rule that supply it.

## Stratification

**Practice.** Keep every rule set stratified: no rule's exception may depend, through
other rules, on what that rule concludes.

**Example.** `CxChange`'s inertia rule depends negatively on `clipped`, and the rule
concluding `clipped` reads nothing `holdsAt` concludes, so the theory is stratified and
loads as written.

**Why.**

- Logical: a cycle through negation is a program with zero or several stable models.
- Engine: `wff/negation-cycle` walks the rule dependency graph on every rule assert, and
  `wff/genl-negation-cycle` on every `genl` assert, and refuses a cycle crossing one or
  more negative edges with `:type :not-stratified`. The predicate edges fan out over the
  `genl` spec closure, so a cycle that exists only through a subtype is caught. A
  positive cycle is ordinary recursion and is accepted. A derived `genl` edge that would
  close a cycle is dropped and reported in `violations`.
- Order independence: which stable model a reader got would depend on which rule settled
  first. Refusing the cycle keeps every stored rule set stratified, so the exception
  evaluator stays within one settle pass and hosts no model selection.

**Why not the other ways.** Accepting the cycle and picking one model makes belief depend
on arrival order, which breaks the property every other mechanism keeps.

**Audit.** `assert` refuses the cycle, so a change that loads clean is stratified. After
a load, read `violations` for a dropped derived edge.

## When specificity already does the work

**Practice.** When the general claim is inherited down `genl` by argument-position
preservation, state the exception as a more specific claim about the nearer kind, not as
an `exceptWhen`.

**Example.** `CxBiology.txt` states flight of the kind once and its exception of the
nearer kind:

```clojure
(abilityType bird flying)
(not (abilityType penguin flying))
```

`(transitiveInArgInverse abilityType 1 genl)` carries the first claim to every kind of
bird. The second claim stops it at `penguin` and leaves the siblings of `penguin`
flying.

**Why.**

- Logical: a stated claim about a nearer kind undercuts the claim inherited from a
  further one. The general claim does not fire for that pair, so nothing is derived and
  `contradictions` stays empty.
- Engine: two claims are compared along the relation the inheritance travels, here the
  `genl` edges the KB holds. Claims that are incomparable come back `:ambiguous`, and the
  prover answers nothing. A `:monotonic` general claim is never undercut: a contrary
  specific claim is the weaker member of the nogood. So the strength the general claim is
  asserted at decides whether it is strict or typical, with no second declaration.
- There is no rule to except: the reach is the taxonomy's, not a chainer's. An
  `exceptWhen` names a rule by handle, so it has nothing to attach to here.

**Why not the other ways.** A rule that descends the kind claim to each species, with an
`exceptWhen` for penguins, states as a rule what the declaration already carries. Leaving
the penguin claim unstated lets the inherited default reach a kind it is false of.

**Audit.** For each kind-level claim a `transitiveInArg` or `transitiveInArgInverse`
declaration carries, list the subkinds it is false of and check each has its stated
contrary claim.
