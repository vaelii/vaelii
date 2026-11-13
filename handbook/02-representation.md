# 2. Representation over code over prose

- **Covers:** where a piece of knowledge is stated: as a KB sentence, as engine code, or
  as prose; stating a term's definition as rules; and stating a declined decision as a
  negation, because absence is not negation.
- **Not here:** what a comment holds once the definition is stated →
  [ch. 7](07-comments.md); negation as failure and closed extents →
  [ch. 32](32-negation.md).
- **Assumes:** [ch. 1](01-true-and-useful.md).

Knowledge can live in three places. A KB sentence is read by the engine, scoped to a
context, justified, retractable and queryable. Engine code is tested, but no query reads
it and no context can hold it differently from another. Prose, in a `comment` string or a
review thread, is read only by a person. The three principles below rank the places and
apply the ranking to definitions and to decisions not to do something.

## OE over code over text

*Prefer representation over code over prose*

**specPrinciple:** represent the definition, references in seeAlso

**Practice.** State a constraint, a policy or a relationship as a KB sentence where vaelii
can express it. Fall back to engine code only for what no sentence can state, and to prose
only for what neither can state.

**Example.** The abduction policy of CxBiology is a sentence in that context, not an entry
in a code table (CxBiology.txt):

```clojure
(abducible_predicate asleep)
```

The engine reads the grant from the asking context's `genlCx` ancestor set, so CxBiology
and every context below it may hypothesize that an animal is asleep, and a context that
does not see CxBiology hypothesizes nothing. A second case from core.txt states a
well-formedness condition as argument declarations instead of a code check: a
per-argument closure grant at position N names a predicate with N or more arguments.

```clojure
(interArgEqual closedExtentForArg 2 2 1 at_least_binary)
(interArgEqual closedExtentForArg 2 3 1 at_least_ternary)
```

**Why.**

- **Logic.** A KB sentence has a precise meaning fixed by the vocabulary it is written in.
  A code check means whatever the code does, and prose means whatever a reader takes from
  it. Of the three, only the sentence can be compared with other sentences for
  consistency.
- **Engine.** A sentence takes part in every mechanism the engine runs. It is scoped:
  `(abducible_predicate asleep)` holds where CxBiology is seen and nowhere else, which a
  global code table cannot express. It is checked: under the entailing reading of argument
  types, a grant past a predicate's arity derives a membership that the arity classes'
  separation rules out, and `try-assert` refuses it, so the `interArgEqual` declarations
  do the work a code check would do and report through the same clash path as every other
  separation. It is justified and retractable: retracting the grant withdraws the
  abductions resting on it.
- **Maintenance.** A reviewer finds a sentence by querying for it. A constraint hidden in
  code is found only by reading the code, and a constraint in prose is found only by
  reading the prose, and neither is checked against the next change to the vocabulary it
  mentions.

**Why not the other ways.**

- **Code.** Some mechanisms do belong in code, and the KB still states what they
  implement. `decontextualized_predicate` lifts every fact of a declared predicate into
  CxUniverse, and its comment gives the reason the lift is code: it runs wherever content
  is stored, and a rule stating it would match every fact in the store. The declaration
  that switches the lift on is still a sentence, `(decontextualized_predicate transitive)`
  among them. Where code computes something the KB could state, the KB states it inert:
  space.txt writes each converse pair as `(set/inert (inverse eastOf westOf))` so a reader
  finds the pair, while the spatial algebra computes converses itself.
- **Prose.** A sentence in a comment string is opaque to every read: no query matches it,
  no clash names it, and no retraction moves it.

**Audit.** For each constraint a change adds in code or in prose, ask whether the KB could
state it, and state it there when it can. `vocabulary-audit` classifies every term core.txt
comments as `:enforced` (a code path reads it) or `:inert` (nothing does, with the reason),
and lists a term that landed with neither under `:unclassified`.

## represent the definition

*State a new term's definition as rules, not only in its comment*

**genlPrinciple:** OE over code over text

**Practice.** For a new term:

- Consider its `seeAlso` and `termsRelated` partners, so the definition is stated against
  the terms it is read with.
- For each sentence of its comment, state the sentence as a fact or a rule where vaelii
  can express it. Use `set/inertRule` for a rule that must not fire. The comment keeps
  only what no sentence can say.
- Run `kb-integrity` over the new terms.

**Example.** The `properPartOf` comment says that the whole is not a part of the part, and
abstract.txt states that sentence as a rule:

```clojure
(set/forwardRule (implies (properPartOf ?part ?whole) (not (partOf ?whole ?part))))
```

The `dead` comment says that death denies life, and CxBiology states it:

```clojure
(set/forwardRule (implies (and (dead ?x)) (not (alive ?x))))
```

core.txt's comment on `closedExtentForArg` says that a closure of a whole predicate
entails the closure at every position and value. A forward rule would store one grant per
value, so the sentence is stated inert:

```clojure
(set/inertRule (implies (and (closed_extent_predicate ?pred) (admitsArgnum ?pred ?position) (thing ?value)) (closedExtentForArg ?pred ?position ?value)))
```

**Why.**

- **Logic.** A defining rule fixes what the comment's English leaves open: which
  argument is which, which direction an entailment runs, and whether a denial is stated
  or merely absent.
- **Engine.** A forward rule fires on every matching fact and justifies each conclusion
  by the rule and the facts, so retracting either withdraws the conclusion. CxBiology's
  `dead` rule makes `(not (alive Rex))` a stored, queryable claim that an application can
  argue from. An inert rule is stored, believed, indexed under its predicates and browsable,
  and chains in neither direction, so it records an entailment the engine must not run
  without leaving the entailment in prose.
- **Maintenance.** A comment drifts from the definitions around it without any check
  noticing. A rule is checked at the write: the naming invariants read every literal in
  it, and a rule whose variable no term can fill under the argument declarations is held
  inert. `kb-integrity` reads the stored rules as well.

**Why not the other ways.** A definition kept only in the comment is the prose case of
**OE over code over text**: the engine cannot use it, and two readers can take it two
ways. An inert rule is better than the comment even when it fires nowhere, because its
argument order and its quantifiers are explicit.

**Audit.** Apply the three steps to every new term. Run `kb-integrity` with the new terms
as the candidate set, for example `(v/kb-integrity kb #{made natural formation}
'CxUniverse)`. A clean run answers `{:status :audited …}`; a `:gap` names each category
with findings, among them `:definition-inconsistencies` (a term that passes a sufficient
definition and fails a necessary one), `:not-under-thing` and `:implicit-genl`.

## bank the decision

*If you think about something and decide not to do it, bank that decision*

**Practice.** When a modelling question is weighed and answered no, state the no in the KB
as an explicit negation, with a `;;` note giving the reason. A relation decided not
transitive gets `(not (transitive R))`. A separation weighed and declined is banked as
`(orthogonal A B)`, not as `(not (disjoint A B))`; it needs no witness, and the note names
one when one is known. Assert a negation only for a decision someone made, never to fill a
gap: absence is not negation. A decision the KB entails by definition needs no banked
sentence: two types a `genl` edge relates are not disjoint by the edge.

**Example.** abstract.txt weighs antisymmetry for `partOf` and declines it, because two
coextensive regions stay two regions:

```clojure
(not (anti_symmetric partOf))
```

core.txt declines all four preservation declarations for `orthogonal`, because a subtype
of one side may be disjoint from the other and a supertype of one side may subsume the
other:

```clojure
(not (transitiveInArgInverse orthogonal 1 genl))
(not (transitiveInArg orthogonal 1 genl))
```

The `knows` comment in society.txt records in prose that `knows` is not symmetric, since
many people know someone who does not know them. The form this principle asks for adds
the decision as a sentence:

```clojure composed
(not (symmetric knows))
```

abstract.txt banks three declined separations with no witness named:

```clojure
(orthogonal substance formation)
(orthogonal food biological)
(orthogonal food formation)
```

**Why.**

- **Logic.** The KB reads open-world. A missing `(transitive R)` says only that nobody
  stated it, so silence cannot distinguish "considered and declined" from "never
  considered". The negation states the first.
- **Engine.** A stated negation meets a later positive. For a forced-monotonic predicate
  such as `anti_symmetric`, the denial is believed while no `(anti_symmetric partOf)` is,
  and it loses the negation nogood to one that is, so the reversal goes through and the
  denial goes OUT with the nogood named. For an ordinary predicate such as `transitive`,
  the stored body and its negation are placed as a nogood: the weaker loses, and two at
  one strength are a dilemma that `contradictions` reports. Either way the reversing change
  meets the decision as a reported nogood. With no negation stored, the positive lands
  silently.
- **Engine.** `disjointness-audit` reads a declared `orthogonal` as `:orthogonal` with
  `:witness :declared`, so the banked pair leaves the `:unknown` set. The audit reads no
  `(not (disjoint A B))`, and a pair banked that way stays `:unknown`. A later separation
  over the pair, or over a supertype of each, makes the `orthogonal` a one-member clash
  that `conflicts` lists, so the reversing change meets the decision.
- **Maintenance.** A decision in a review thread is lost to the next reviewer. A decision
  in the KB is found by a query, travels with the term through exports and reloads, and
  is retracted on purpose when someone changes their mind.

**Why not the other ways.** A code comment or a review thread holds the decision where the
engine cannot read it, which is the prose case of **OE over code over text**. A negation
asserted to fill a gap, for every property nobody considered, states decisions nobody made
and blocks later positives that nobody weighed against it.

**Audit.** For each property, edge or declaration a vocabulary change weighed and declined,
the KB states its negation, and each `(not …)` mark has a decision behind it. A query such
as `(v/ask kb '(not (symmetric knows)) 'CxUniverse)` confirms the decision is stated.
For a `kb-integrity` rule-macro suggestion that a reviewer declines, `declined_rule_macro`
banks the no: a default run stops reporting a suggestion the rule's context sees declined,
a run that names `:rule-macro-review` lists it, and retracting the record brings the
finding back. core.txt's own example of the form, for a default rule carrying `livesIn`
to `locatedIn`, is:

```clojure
(declined_rule_macro (Quote (genl livesIn locatedIn)))
```

`acknowledgedFinding` records the same decision with its reason
([ch. 28](28-vocab-pr.md#acknowledged-findings)).
