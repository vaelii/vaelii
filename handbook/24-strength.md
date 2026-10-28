# 24. Strength

- **Covers:** the two strengths, `:monotonic` and `:default`; how a text file states each;
  what strength decides when two sentences clash; how a conclusion's strength follows from
  what it rests on; the forced-monotonic set; the strength of a separation a fiction may
  break.
- **Not here:** where a fiction context sits → [ch. 23](23-contexts.md); choosing a default
  rule over a list of cases → [ch. 25](25-default-or-enumerate.md); exceptions to a rule →
  [ch. 30](30-exceptions.md).
- **Assumes:** [ch. 13](13-disjointness.md), [ch. 23](23-contexts.md).

Every assertion carries one of two strengths. `:monotonic` is known-true and is never
defeated. `:default` is defeasible, and most of a common-sense KB is stated at it. The
order is total, `:monotonic` above `:default`, and derivation adds no third class.

## Known-true or typical

**Practice.** State a sentence `:monotonic` when it is true of every case the KB will ever
hold: a definition, a classification fixed by the meaning of the terms, a relation mark.
State it `:default` when it holds typically and an exception is possible. In a text file,
wrap a known-true sentence in `set/monotonic`; a sentence with no wrapper is `:default`.

**Example.** `abstract.txt` states the marks of `typeLargerThan` known-true, and `CxBiology.txt`
states mortality as a default rule:

```clojure
(set/monotonic (transitive typeLargerThan))
(set/defaultRule (set/forwardRule (implies (and (organism ?x)) (mortal ?x))))
```

The `comment` on `mortal` in `life.txt` reads "Asserted as a default of every organism, so
it is defeasible: something known not to die defeats it instead of contradicting the KB."

**Why.**

- *Logical.* A `:monotonic` sentence is a claim with no exceptions. A `:default` one is a
  claim the KB gives up when a stronger sentence contradicts it.
- *Engine.* A clash is a nogood, and the verdict reads its members' defeat classes. A unique
  weakest member loses and is defeated at the nogood's placement. A minimum several
  `:default` members share is a dilemma: every member stays believed and `contradictions`
  reports it. A minimum several `:monotonic` members share is a hard clash, and `conflicts`
  reports it.
- *Engine.* A re-assert takes the stronger of the two strengths and never the weaker.
  Narrowing a sentence to `:default` is a retraction and a re-assert.
- *Maintenance.* A sentence stated `:monotonic` turns every later contrary sentence into
  a loser or a hard clash, so the author who writes it commits every later author to it.

**Why not the other ways.** Stating everything `:monotonic` turns each exception into a
hard clash nobody can resolve by adding knowledge. Stating a definition `:default` lets a
mistaken fact defeat it.

**Audit.** For each `set/monotonic` in a change, name the case that would break it and say
why the case cannot exist. Read `conflicts` after the load: each entry is a pair of
known-true sentences, and at least one of them is false.

## A conclusion is as strong as what it rests on

**Practice.** Decide the strength of a rule's conclusions by the rule's form. A bare rule
passes on the strength of its antecedents. Use `set/defaultRule` when the rule itself is
the defeasible step.

**Example.** `CxKinship.txt` states parenthood from fatherhood as a bare rule, so a
`:monotonic` `fatherOf` fact concludes a `:monotonic` `parentOf` and a `:default` one
concludes a `:default` `parentOf`:

```clojure
(set/forwardRule (implies (and (fatherOf ?child ?father)) (parentOf ?father ?child)))
```

**Why.**

- *Engine.* A firing confers the lower of the rule's own strength and the weakest of its
  antecedents' classes. A bare rule confers `:monotonic`, so its conclusion is capped by
  what it rests on. A `set/defaultRule` confers `:default`. A guarded rule, one with an
  `(unknown S)` antecedent or an `exceptWhen` stored against it, confers `:default`
  whatever its antecedents, since a blocker arriving takes the conclusion OUT.
- *Engine.* The taxonomy edges a firing names are grounds as the facts are. A `:default`
  `genl` edge a match climbed caps the conclusion at `:default`.
- *Maintenance.* A known-true premise reaches its conclusions as known-true with no
  wrapper on the rule, and a default premise reaches them as a default.

**Why not the other ways.** A `set/defaultRule` over known-true facts makes every
conclusion defeasible, including ones that follow by definition. A bare rule whose step is
itself only typical concludes `:monotonic` from known-true premises, and a later exception
then meets a hard clash.

**Audit.** For each rule, say whether the step from antecedents to consequent can fail when
the antecedents hold. If it can, the rule is a `set/defaultRule` or carries an
`exceptWhen`.

## The forced-monotonic set

**Practice.** Know which predicates the engine holds forced-monotonic before choosing a
strength for one of their sentences. A forced-monotonic sentence written `:default` is
stored at `:default`, and the strength does not let it lose a nogood.

**Example.** `core.txt` declares the set in the `comment` on `forced_monotonic_predicate`,
which lists `genlCx`, the relation marks, the function classes, the definitional
declarations, the arity bindings and policies, the term kinds, the argument declarations,
the correspondence premises, `except`, `exceptWhen` and the equality relations, and states:

```clojure
(forced_monotonic_predicate genlCx)
```

**Why.**

- *Engine.* A forced-monotonic sentence is never the loser of a nogood, and a denial of it
  loses to it at either strength. It goes OUT only by retraction.
- *Engine.* The separations, `disjoint`, `covering`, `partition`, `sibling_disjoint` and
  `siblingDisjointException`, are in the set as grounds of the membership family. A
  membership nogood's members are the memberships and denials alone; the separation is
  read through and is never a member, so its strength never decides the verdict. The
  denial a separation answers reads a believed separation as `:monotonic` whatever
  strength it was written at.
- *Engine.* A forced-monotonic sentence keeps its written strength as a cap on what is
  derived from it. A firing of a rule whose antecedent is a `:default` declaration is
  `:default`. A `genlCx` edge is the one exception and confers `:monotonic` at any
  strength.
- *Maintenance.* The written strength of a forced-monotonic sentence still records the
  author's claim, and a reader of the file sees it.

**Why not the other ways.** A denial stated to defeat a forced-monotonic sentence loses.
To remove one from a context and below, state an `except` ([ch. 23](23-contexts.md)); to
remove it everywhere, retract it.

**Audit.** For each `:default` sentence of a forced-monotonic predicate, confirm the
author means the strength as a record of the claim, and does not expect a nogood to defeat
the sentence.

*In development:* the separations' place in the forced-monotonic set is in development.
The engine holds the five forced-monotonic: `core.txt` declares each with
`forced_monotonic_predicate`, and the membership family's `:grounds` name them in code, so
removing the declaration moves nothing. `catbus_test`'s
`a-default-separation-yields-to-a-fiction-that-states-the-overlap` states the defeasible
reading and is marked `^:red`. This section and [catbus principle](#catbus-principle)
describe the engine as it runs.

## catbus principle
*Monotonic until a real fiction needs the overlap*

**Practice.** State a separation `:monotonic` in `CxUniverse` unless an existing fictional
work shows a member of both types. One such work is enough: state the `CxUniverse`
separation at `:default`, and restate it `:monotonic` in `CxRealWorld`, which fiction
contexts do not see. A hypothetical example is not enough.

**Example.** The Catbus in *My Neighbor Totoro* is both a cat and a bus. `abstract.txt`
states the one separation it breaks at `:default`, between two that are `:monotonic`:

```clojure
(disjoint animal vehicle)
(set/monotonic (disjoint building furniture))
(set/monotonic (disjoint building vehicle))
```

The note above the first reads "animal and vehicle are disjoint at the default strength
rather than monotonic: a fiction below CxWell may except the default and hold a term that
is both." `CxRealWorld.txt` states `(set/monotonic (disjoint animal vehicle))`.

**Why.**

- *Logical.* The default strength says the separation holds of the real world and of
  ordinary cases and that a fiction may break it. The `CxRealWorld` copy says the real
  world never does.
- *Engine.* `catbus_test` places a fiction under `CxWell` and asserts a term as both a cat
  and a bus at `:default`. The two memberships are a dilemma: both stay believed and
  `contradictions` reports the pair. In `CxRealWorld`, a `:monotonic` cat membership beside
  a `:default` bus membership is a nogood with a unique weakest member, and the bus
  membership loses.
- *Engine.* The separation's own strength decides neither outcome. `disjoint` is
  forced-monotonic, so a `:default` separation is never defeated, and the membership
  nogood's verdict reads only the members' strengths. An `except` stated in the fiction
  hides the `CxUniverse` separation there at either strength. The `CxRealWorld` copy holds
  the separation for the real world when an `except` of the `CxUniverse` copy is stated in
  a context `CxRealWorld` sees, such as `CxWell`. The default strength also caps at
  `:default` a firing whose antecedent is the separation.
- *Maintenance.* The strength and the restatement record, in the KB, which separations a
  known fiction breaks. A reader of `abstract.txt` sees the decision and its reason beside
  the sentence.

*In development:* the separation's strength deciding the fiction case is in development
([the forced-monotonic set](#the-forced-monotonic-set)).

**Why not the other ways.** A hypothetical member of two types exists for nearly every
separation, so accepting one would weaken every separation in the KB. A fiction placed
below `CxRealWorld` holds no overlap the real world rules out.

**Audit.** For every `:default` separation in `CxUniverse` with a `:monotonic` copy in
`CxRealWorld`, name the fictional work and the member that justify it. For every
`:default` separation without a copy, either name the work and add the copy, or restate
the separation `:monotonic`.
