# Rule generators: a rule whose consequent is a rule

- **Covers:** the generator form, the hole/own-variable scoping rule, nesting and what
  the extra level buys, what a firing mints, how a mint is retracted, and the things a
  generator is refused for.
- **Not here:** the direction wrappers a generated rule carries →
  [inference.md](inference.md); why a *variable-predicate* rule is refused →
  [indexing.md](indexing.md); skolemizing a head existential →
  [skolem.md](skolem.md); the shipped quantifier family two of whose cells are
  generators → [predall.md](predall.md).
- **Assumes:** sentex, rule, handle, justification, hole-free range restriction →
  [glossary.md](glossary.md), [inference.md](inference.md).

A rule normally concludes a fact. A **generator** concludes a *rule*, and its firing
stores that rule:

```clojure
(implies (and (plan_verb ?outcome) (outcomeEmotion ?outcome ?emotion))
         (set/defaultRule
           (implies (and (planOf ?a ?p) (?outcome ?a ?p))
                    (feels ?a ?emotion))))
```

Given `(plan_verb succeededAt)` and `(outcomeEmotion succeededAt Joy)`, the firing
stores one ordinary rule:

```clojure
(set/defaultRule (implies (and (planOf ?a ?p) (succeededAt ?a ?p)) (feels ?a Joy)))
```

Concrete functors, keyed by the rule index, triggered and proved through exactly the
paths a hand-written rule is. Add `(outcomeEmotion failedAt Regret)` and a second rule
appears; retract it and that rule goes.

## The scoping rule

Two kinds of variable live in a generator's consequent, and **nothing in the spelling
marks them apart** — the split is computed:

| | which variables | what happens to them |
|---|---|---|
| **holes** | those an *enclosing* level's antecedents also mention | bound by that level's join, ground in what it generates |
| **the generated rule's own** | everything else | survive as variables; they belong to the rule being generated |

In the example `?outcome` and `?emotion` are holes; `?a` and `?p` are the generated
rule's own. Sharing a variable name with the antecedents *is* how an author says "fill
this in", so there is nothing to declare and no second spelling that could disagree
with the first.

Two consequences follow, and both are easy to trip over:

- **A hole may stand in functor position.** `(?outcome ?a ?p)` is a rule *antecedent*,
  where a variable functor is otherwise refused, and it is legal here because by mint
  time it holds `succeededAt`. This is what lets one generator range over a family of
  predicates while every antecedent the index keys on has a concrete functor. A variable
  functor no enclosing level binds is refused (`:not-indexable`) — nothing will ever bind
  it.
- **Range restriction moves one level in.** The generator's own is vacuous: its
  consequent is a rule rather than a conclusion, and the generated rule's free variables
  are unbound on purpose. The *generated* rule's is what is checked, with the holes
  counted as bound. So `(implies (marker ?p) (implies (?p ?x) (dst ?x ?loose)))` is
  refused for `?loose`, at the generator, before any firing.

## Nesting

A generated rule may itself be a generator, and then the mint generates in turn. The nesting
is **not capped**, because the scoping rule composes without needing anything added to
it: a variable belongs to the **outermost** level whose antecedents mention it, which is
the level whose firing grounds it. One reading of the sentence decides every level, and
`rules/nesting` is that reading — it peels a rule into levels and carries each level's
`:bound` set down.

The extra level gives a **functor**. A hole is ground before the rule holding it
is stored; a variable bound by a literal *beside* it is not, because both are stored at
once. So these two say the same join and only one of them can be stored:

```clojure
;; refused :not-indexable — ?type is bound by the antecedent next to it, so the rule
;; that gets stored still has a variable in functor position
(implies (typeVersion ?ipred ?tpred)
         (implies (and (?tpred ?type ?ability) (?type ?instance))
                  (?ipred ?instance ?ability)))

;; accepted — ?type is a hole of the middle level, so it is filled before the rule
;; using it as a functor is stored
(implies (typeVersion ?ipred ?tpred)
         (implies (?tpred ?type ?ability)
                  (implies (?type ?instance)
                           (?ipred ?instance ?ability))))
```

The second is a type-level/instance-level bridge stated once rather than once per pair.
`(typeVersion able abilityType)` generates a generator:

```clojure
(implies (abilityType ?type ?ability)
         (implies (?type ?instance) (able ?instance ?ability)))
```

`(abilityType bird flying)` generates that generator's rule:

```clojure
(implies (bird ?instance) (able ?instance flying))
```

and `(bird Tweety)` concludes `(able Tweety flying)`. Three levels, three
firings, and the only thing ever keyed by the index is the concrete rule at the bottom
and the two generators above it — filed under `implies`, which is where every generator
is filed at every depth.

**Every level owes what a generator owes**, because every level reaches the store as a
rule in its own right and the mint reads the same check list the assert entry point does. A
`set/backwardRule` around a middle level is `:not-indexable` at the sentence rather than
one firing later; an `exceptWhen` on any generated level is `:not-well-formed`; and a level
that fills **no hole an enclosing level has not already filled** is
`:not-range-restricted` — it would generate the same rule at every firing, which is a rule
its author could have written.

**A top-level rule antecedent is not covered by any of this.** Nothing encloses it, so a
variable functor there is what it always was: a key no fact and no goal can spell
([indexing.md](indexing.md)). The nesting rule admits a variable functor exactly where a
level further out fills it.

## The generated rule's direction

The wrapper rides **inside** the consequent, where substitution never touches it, and
sets the direction of the rule that gets stored: `set/forwardRule`,
`set/forwardOnlyRule`, `set/backwardRule`, `set/lazyForwardRule`, `set/inertRule`. `set/defaultRule` rides there too and makes the
generated rule defeasible rather than setting its direction. That is the only place
either can be written for a rule nobody types out. A generated rule with no direction
wrapper is **backward** like any other bare rule, so a generator whose generated rule is
meant to materialize facts writes `set/forwardRule` or `set/forwardOnlyRule` inside the
consequent — the shipped `predAllInstance` generator writes the first, and
`relationTypeByArity` the second, since the converse it generates beside it is
lazy-forward and the two would otherwise be a backward cycle. The lazy-forward converse
`(binary ?r) ⇒ (arity ?r 2)` lets a forward rule guarded on `(arity ?r ?n)` fire for a
relation its exact-arity class declares, and stores no arity
([inference.md](inference.md#a-lazy-forward-rule)).

The **generator itself defaults to forward**, even bare. Its conclusion is a rule, and no
backward goal asks for one — `res/concluding-rule-handles` reads a goal's predicate, and a
generator's consequent predicate is `implies`, which nothing queries — so the backward
default an ordinary rule takes would leave the generator firing in neither engine. A
`set/backwardRule` generator is refused rather than stored claiming a capability it
cannot exercise. `set/inertRule` stays legal, since it claims nothing. Under nesting the
same holds of each level that generates: only the **innermost** rule's wrapper is a free
choice, and it is the one that sets the direction of the rule that concludes a fact.

## A mint is derived content

This is what separates a generator from a load-time macro, and it is the reason to
have one.

A minted rule is **justified** by the firing — antecedent handles plus the generator's
own handle — not marked a premise. Both chainers ask belief of a rule before using it
(`res/rule-believed?`) — the forward chainer on **every** firing path, the trigger match
and the qualitative and preservation re-joins alike, since all three reach a rule off the
storage-posted antecedent index — so when what licensed a mint goes, the ordinary relabel
un-believes the mint, and the mint stops firing. Nothing has to hunt it down:

```clojure
(v/retract! kb pairing-handle)   ; (outcomeEmotion succeededAt Joy)
;; the generated rule is no longer believed, and neither is anything it concluded
```

A defeat of a `:default` fill hides the mint and its conclusions the same way, though the
network keeps them IN. The mint's class is the fill's, and it caps the class of each firing
of the mint, so the read that hides the fill reaches every conclusion resting on it
([nmtms.md](nmtms.md#strength-propagates-from-the-antecedents)).

Dedup is the ordinary sentex dedup, so two generators that generate the same rule share
one handle and collect a justification each — and the rule survives until the last of
them goes.

Both **arrival orders** agree, with no retroactive sweep of a generator's own. A
generator is a rule, and a newly asserted rule is a datum that joins over the facts
already stored (`chain/process-datum`); a newly *minted* rule is returned to the agenda
the same way, so it too sees what is already there.

## What a firing does

The mint goes through the same check list the assert entry point runs
(`checks/check-rule!`, read by both entry points so neither can drift): range restriction,
indexability, naming, stratification, no imperative, disjunction shape, NAF closure,
the argument constraints the rule's own variables carry, and the generator's own three. A
generated rule concluding a conjunction is polycanonicalized into one rule per conjunct,
and one whose antecedent disjoins into one rule per alternative, exactly as an asserted
one is. The expansion happens at the **mint**, not at the generator's own assert: the
holes are ground by then, so the alternatives stored are the alternatives of the rule
that was generated ([canonicalization.md](canonicalization.md)). A ground application of
a reifiable function in the generated rule is reified to its constant first, as `assert`
reifies one in a rule it stores, so the generated rule's literals are spelled the way the
facts they match are stored ([nat.md](nat.md), "Derivation path").

That the list is one list is what makes nesting safe rather than merely legal: a middle
level is checked **twice** — once as the pattern its author wrote, and again as the rule
it became, with the outer fills substituted in. A fill that turns a middle level into
junk is caught at the second reading, where the sentence alone could not have said so.

A mint that **cannot stand is dropped and recorded**, never thrown — a fixpoint may not
abort halfway through itself, and an exception escaping a firing would make the belief
set depend on which rule fired first. The drop lands in the violation ledger
(`core/violations`) naming the generator that produced it.

## What is refused

| written | refused as |
|---|---|
| an `exceptWhen` on a generated rule, at any level | `:not-well-formed` |
| `set/backwardRule` on a level that generates | `:not-indexable` |
| a generated variable functor no enclosing level binds | `:not-indexable` |
| a level sharing no *new* variable with the rule it generates | `:not-range-restricted` |
| the innermost rule not range-restricted | `:not-range-restricted` |
| a generator cycle | `:not-stratified` |

**An `exceptWhen` on a generated rule** is refused because an exception is not a rule
field: it is a separate meta-sentex keyed by the rule's handle, split off and stored by
the assert path, which a firing does not run. The mint would be a rule whose guard had
evaporated in silence, firing on exactly the bindings its author wrote it not to — so
it is refused rather than dropped. Two things do work: an `(unknown …)` antecedent
*inside* the generated rule, which lives in the rule sentence and so survives
substitution; and an `exceptWhen` on the **outermost** rule, which states when the
generator does not fire.

**A level sharing no new variable** is the per-level form of "every firing generates the
same rule", and under nesting it is a mistake an outer fill *creates*: in
`(implies (aa ?x) (implies (bb ?x) (implies (cc ?x) (dd ?x))))` the middle level's only
shared variable is `?x`, which the first level has already ground, so the rule it generates
is fixed before it is stored. Share a variable the levels above it do not.

A head existential *inside* the generated rule is fine, and skolemizes one firing later,
keyed on the generated rule's own content — the generator's firing deliberately does not
skolemize, since the generated rule's free variables are its own ([skolem.md](skolem.md)).

**What bounds a generator is the cycle check, not the depth.** A nested generator generates
one level further and stops; a cycle generates forever. That is why the refusal is on the
cycle and the nesting is left to the author.

**A generator cycle** is a path of feeds that returns to the generator it starts from. One
generator feeds another when its **innermost** conclusion is a predicate the other reads in
an antecedent it generates from; a generator that feeds itself is a cycle of one. The
innermost, because that is the only level that concludes a fact: the levels above it
conclude rules, filed under `implies`, which no fact carries and no goal asks for. A
variable functor names no predicate, so a generator concluding one feeds nothing and a
generator reading one is fed by nothing. A feed with no path back is a finite chain:
core.txt's `partitionedByType` generator concludes `genl`, and a generator reading `genl`
to conclude a predicate no generator reads passes. A cycle is refused outright rather than
depth-capped ([why](defenses.md#a-generator-cycle-is-refused-not-depth-capped)) — the call
[exceptions.md](exceptions.md) makes for a cycle through negation, for the same reason.
Each generator's assert walks the feeds from the arriving generator over every stored one.
Every stored generator passed the same walk, so a cycle the arrival closes runs through the
arrival, and the refusal falls on whichever member of the loop arrives last.

## What this is not

**Not storage compaction.** Materializing N rules stores N rule records. What it provides
instead is that only the fills that actually *occur* become rules: a hand-authored
cross-product is `predicates × types`, while a generator mints one rule per instance
fact that exists, and the family grows and shrinks with the data. Matching cost is
unchanged either way — the rule index is keyed by predicate, so N concrete rules are
never scanned, and each is reachable only through its own functors.

**Not a variable-predicate rule.** A rule that reaches the store with a variable functor
in an **antecedent** is still refused (`:not-indexable`, [indexing.md](indexing.md)): the
antecedent cell is keyed on a concrete symbol, and a variable names none for an arriving
fact to trigger. (The consequent cell has a catch-all for a variable there, which is why
the refusal falls on one half and not both.) Nesting does not weaken it — nesting is what
makes it affordable, since a functor an enclosing level fills is concrete by the time
anything is keyed on it. A rule nothing encloses is refused exactly as it is anywhere
else.

**Not a rule about rules.** A generator concludes a rule; nothing reads one as a term,
and no rule can take a rule as an antecedent. The one way to speak *about* a stored
rule remains the `(sentexHandle H)` meta-sentex layer
([exceptions.md](exceptions.md), [contexts.md](contexts.md)).

## Where the code is

- `vaelii.impl.rules` — `generated-rule`, `generator?`, `holes`, `nesting` (the peel
  every generator question is read off), `innermost-rule`, the generator arm of
  `range-problems`, and the level-aware `variable-functor-literals`.
- `vaelii.impl.sentex` — `connective-problems`, whose consequent arm reads a rule in
  consequent position as the next level and recurses.
- `vaelii.impl.naming` — `applied-literals`, which tags a generated rule's literals
  `:generated-antecedent` / `:generated-consequent` — at every depth — so the index
  check can tell them from the author's own.
- `vaelii.impl.checks` — `check-rule!` (the list both entry points read), `check-generator!`
  (the three a generator owes — the `exceptWhen` and forward-only refusals per level,
  the cycle once), `rule-violation` (the value form, for the firing), `generator-cycle`.
- `vaelii.impl.chain` — `mint-rule`, and the `place-conclusion` dispatch that routes a
  rule-valued conclusion to it — including a minted rule that is itself a generator.
- `vaelii.impl.resolution` — `rule-believed?`, which is what makes a mint retractable.
