# 37. Coreference

- **Covers:** stating that two names denote one thing with `rewriteOf`, `sameAs` or
  `equals`; what a merge does to matching and belief; guarding a rule with `different`;
  why a quoted term and a value stay out of a merge; what a `functional` collision
  concludes; retracting or hiding a merge.
- **Not here:** a schematic `equals` with variables, oriented into a rewrite rule →
  [equational.md](../docs/equational.md); a `(rewriteOf T E)` whose `E` is a function
  application, which makes the application reify to `T` → [ch. 22](22-functions.md),
  [nat.md](../docs/nat.md); the relation marks themselves → [ch. 19](19-relation-properties.md);
  equality of two measures → [quantity.md](../docs/quantity.md); a skolem witness →
  [ch. 33](33-existentials.md); the mechanism in full → [equality.md](../docs/equality.md).
- **Assumes:** [ch. 8](08-kind-of-term.md), [ch. 19](19-relation-properties.md)
  (`functional`), [ch. 23](23-contexts.md) (`except`), [ch. 24](24-strength.md) (the
  forced-monotonic set).

The KB treats two distinct symbols as two things until an equality sentence says
otherwise. Facts arrive under several names for one thing: two sources spell a town
differently, an import brings its own predicate for a relation the KB already has, and a
`functional` slot receives a second name for its one value. Three relations state the
identity, and one query relation reads it.

## Choosing the relation

**Practice.** State `(rewriteOf Kept Retired)` when one spelling is to stop being used: a
duplicate term minted by mistake, or an imported predicate or type aligned onto the KB's
own. State `(sameAs A B)` when two names for one individual both stay in use. State
`(equals A B)` for any two terms where neither name is to be preferred. Write both sides
as symbols.

**Example.** A composed block aligns an imported predicate and identifies two names for
one town:

```clojure composed
(rewriteOf livesIn residesIn)
(sameAs Dover DoverKent)
```

**Why.**

- *Logical.* All three state that two terms denote one thing. They feed one equivalence
  partition and differ only in what they say about the names.
- *Engine.* Each class has one representative, and every believed answer names it. A
  `rewriteOf` names its first argument preferred and its second deprecated, so
  `livesIn` represents `residesIn` and `deprecated?` answers true of `residesIn`. A
  `sameAs` or `equals` deprecates neither name, and the representative is the
  lexicographically smallest symbol in the class, so `Dover` represents `DoverKent`. The
  election reads content and never arrival order, and chains compose: with
  `(rewriteOf A B)` and `(sameAs B Aardvark)` the representative is `A`.
- *Engine.* `assert` refuses a `rewriteOf` self-edge, a `rewriteOf` that closes a cycle
  over the stated preferences, and a `rewriteOf` whose two sides have different roles
  (an individual with a predicate, a predicate with a type). A bare lowercase word such
  as `dog` is accepted beside a predicate or a type, and a namespaced symbol beside
  anything. A compound argument is refused for all three relations, apart from the two
  forms *Not here* routes elsewhere and a ground application of a reifiable function,
  which reifies to a constant before the check.
- *Engine.* The three relations are forced-monotonic. A merge is never the loser of a
  nogood, whatever strength it is written at.

**Why not the other ways.** No check holds `sameAs` to individuals: `core.txt` types both
arguments `thing`, so `(sameAs dog canine)` is stored and merges two types without
retiring either name. Vocabulary alignment uses `rewriteOf`, which records the retired
name. A rule copying each `residesIn` fact to `livesIn` stores two sentences per fact,
leaves the two predicates distinct, and leaves `(different livesIn residesIn)` provable.
An author who wants a particular name to represent a `sameAs` class adds a `rewriteOf`;
the smallest symbol is the default only.

**Audit.** For each equality in a change, ask `representative` and `deprecated?` of every
name in the context the change targets, and confirm the representative is the name new
content uses.

## What a merge does to matching and belief

**Practice.** State the merge in the context where the identity holds: `CxUniverse` for an
identity every context accepts, a story's context for an identity only the story makes.
Ask under either name, and read answers under the representative.

**Example.** A composed session: the fact arrives under one name, the merge under the
other.

```clojure composed
(v/assert kb '(livesIn Ann DoverKent) 'CxStory)
(v/assert kb '(sameAs Dover DoverKent) 'CxStory)
(v/ask? kb '(livesIn Ann DoverKent) 'CxStory)     ; => true
(v/ask kb '(livesIn Ann ?town) 'CxStory)          ; binds ?town to Dover
```

**Why.**

- *Engine.* The merge restates every stored sentence naming a retired term, at any
  nesting depth, as a twin under the representative. The twin `(livesIn Ann Dover)` is
  derived and justified by the original and the equality. When the restated sentence is
  already stored, the stored sentex gains a second justification and keeps its handle.
- *Engine.* The original stays stored and its handle stays valid, but the original is not
  believed and fires no forward rule. `why-not` on its handle reports
  `:superseded` and names the representative. A rule naming a retired term is restated
  the same way and fires under the representative.
- *Engine.* A goal naming a retired term is rewritten before lookup, so the closed goal
  above succeeds and the open goal binds `Dover`. `handle-of` reads storage and does not
  rewrite.
- *Context.* A merge applies in its own context and in every context that sees it through
  `genlCx`. A context outside that set keeps both names as two things, so a story can
  merge two characters without merging them in another story.
- *Maintenance.* A merge can create a clash. `(dog Rex)`, `(cat Fluffy)` and a merge of
  `Rex` with `Fluffy` make one individual a member of two disjoint types; the twins are
  stored and the clash is reported in `contradictions` or `conflicts` like any other.

**Why not the other ways.** A merge stated in `CxUniverse` for an identity one source
asserts applies in every context, including one that holds the other source's account. A
fact restated by hand under the representative is a second premise that stays after the
merge is retracted.

**Audit.** After a merge, run `contradictions` and `conflicts` and account for each clash
naming a member of the class. Run `why` on one twin and confirm it names the
original and the equality.

## different

**Practice.** Guard a rule with `(different ?x ?y)` when two bindings must be two things.
Write it in rule antecedents and goals only, with every argument bound by the time it is
read.

**Example.** `CxSocial.txt`:

```clojure
(set/forwardRule
  (implies (and (dwellsIn ?x ?d) (dwellsIn ?y ?d) (different ?x ?y))
           (roommateOf ?x ?y)))
```

**Why.**

- *Logical.* `different` is the unique-name assumption read as a relation. A goal holds
  when no two of its arguments share an equivalence class visible from the asking
  context. It takes two or more arguments and is pairwise.
- *Engine.* A merge reaching the conclusion's context withdraws a firing the guard
  licensed, and retracting the merge brings the firing back. Belief therefore does not
  depend on whether the merge or the facts arrived first.
- *Engine.* The unique-name assumption is suspended for an unmerged indeterminate term,
  a skolem witness included ([ch. 33](33-existentials.md)): neither `different` nor
  `equals` is provable between it and a determinate term until a `rewriteOf` or a merge
  identifies it.
- *Engine.* A rule concluding an equality from a `different` antecedent is refused at
  assert, because the conclusion would remove the antecedent it rests on. Two `different`
  literals in one rule stay two literals: `(different ?a ?b)` and `(different ?b ?c)`
  say nothing about `?a` and `?c`.

**Why not the other ways.** `assert` refuses a `different` sentence, since the prover
answers it and nothing stores it. A goal with an unbound argument is not answered, since
it would enumerate every other term in the KB. A stated `(not (sameAs A B))` loses to any
merge of the two ([below](#retracting-or-hiding-a-merge)), and the prover does not read
it.

**Audit.** For each rule whose conclusion is wrong when two bindings name one thing,
confirm a `different` guard is present. For each such rule, `ask?` the guard over a pair
the change merges and confirm the answer is `false`.

## identity, not likeness

*Merge names, never mentions or values*

**Practice.** Use an equality relation only between two names whose referents are one
thing. Name a term as syntax with `Quote`. Compare measures, positions and extents with
the predicates their vocabularies define, and keep the equality relations away from
numbers, strings and compound terms.

**Example.** `core.txt` gives the example of a quoted term:

```clojure
(positiveExampleComment Quote "(Quote Muffet), which names the symbol Muffet and not the dog")
```

The `comment` on `sameQuantity` in `measure.txt` states the boundary for values: "Never an
equality: it says two measures agree and not that two names denote one thing." Its
`implementationNote` gives the engine's side: "The equality closure is a partition over
symbols and holds no numbers or compounds." The `comment` on `spatiallyEqual` in
`space.txt` states it for regions: "two coextensive regions are still two regions."

**Why.**

- *Logical.* `(Quote Muffet)` names the symbol, and a merge of `Muffet` with another name
  of the dog does not make the two symbols one symbol. A proposition inside
  `(believes Agent P)` is what the agent holds, and an identity the asker knows is not
  one the agent knows.
- *Engine.* A mention is exempt from the merge: the arguments of `Quote` and
  `Quasiquote`, and the proposition of a `modal_predicate`. A `sameAs` or `equals` does
  not rewrite them. A `rewriteOf` does, because it renames a spelling. The agent's own
  merges rewrite the proposition in the agent's context ([ch. 36](36-agents-and-hypotheses.md)).
- *Engine.* The partition holds symbols. `assert` refuses a structural compound, such as
  a `QuantityFn` application, as an argument to the three relations. A `functional`
  collision between two numbers is a nogood, and an `interArgEqual` trigger compares
  values that no merge changes.
- *Maintenance.* A predicate stating agreement keeps two things two. Two coextensive
  regions keep their own facts, and a later fact about one does not move to the other.

**Why not the other ways.** A `sameAs` between two regions that occupy one extent merges
the regions, so every fact about either is restated about the representative, and
`different` fails between them. An `equals` between two measures is refused.

**Audit.** For each equality in a change, name the one thing both sides denote. If the
sides agree in a measure, a position or an extent, the change uses the vocabulary's own
predicate.

## A functional collision

**Practice.** Declare `functional` where a subject has one value, in each time slice for
a value that changes over time ([ch. 19](19-relation-properties.md#functional)). State
facts `:monotonic` only where a second name for the value is to merge with the first. State
a value whose second value is a distinct thing, such as a status, at `:default`, so that
two values in one context are a reported dilemma and not a merge. State an identity that
may be wrong with a predicate that does not merge.

**Example.** `life.txt`:

```clojure
(set/monotonic (functional birthYearOf))
```

A birth year has one integer value; two distinct years conflict rather than becoming
one integer. Generic parenthood is not a uniqueness constraint: several mothers can
remain distinct. The `comment` and the `implementationNote` on `signOf` in `measure.txt`
record the opposite decision: a quantity has one sign, and the predicate is not declared
functional, because a merge would make `SignPositive` and `SignNegative` one term where
the contradiction is to be reported.

**Why.**

- *Engine.* Two `:monotonic` facts naming two symbols for one subject derive
  `(equals V1 V2)`. The derivation is justified by both facts, every declaration of the
  mark, the `genl` edges the facts descended through, and the `genlCx` edges that make the
  pair visible together. The relation is `equals` because a value need not be an
  individual.
- *Engine.* Every other collision is a nogood: two numbers, two strings, a compound, or a
  pair with a `:default` fact. A `:default` fact loses to a `:monotonic` one, and two
  `:default` facts are a dilemma `contradictions` reports. A merge is never defeated, so
  it rests on `:monotonic` evidence only.
- *Engine.* The mark is read up the predicate hierarchy, and a mark arriving after the
  facts merges them as a fact arriving after the mark does. `anti_symmetric` and
  `functionalInArg` derive merges by the same rule.

**Why not the other ways.** A `functional` mark on a relation whose values are distinct
things by design, such as the three signs, turns each clash between two `:monotonic`
facts into a merge of two terms the KB uses everywhere. A `:monotonic` fact stated for an
uncertain value merges on a guess, and every fact about either name moves to the
representative.

*In development:* a second distinct symbol value refused by `try-assert`, and a stated
`(not (equals V1 V2))` that keeps two `:monotonic` values from merging, are in development
(`functional_clash_test/try-assert-refuses-a-second-symbol-value-of-a-functional-predicate`,
`functional_clash_test/a-monotonic-denial-of-equality-makes-a-second-value-a-clash`, red).
Today `try-assert` stores the second value, and two `:monotonic` values merge with the
denial out.

**Audit.** For each `functional`, `functionalInArg` or `anti_symmetric` mark, name two
symbols a collision would merge. Confirm they could denote one thing, or that the facts
are stated `:default` so that the collision is reported. After loading a change, run
`why` on each derived `equals` and confirm the facts it names.

## Retracting or hiding a merge

**Practice.** Undo a stated merge by retracting the equality. Undo a derived merge by
retracting one of the facts or the declaration it rests on. Hide a merge in one context
and below it with an `except` ([ch. 23](23-contexts.md)). Do not state a denial.

**Example.** A composed session continuing the one above:

```clojure composed
(def eq (v/handle-of kb '(sameAs Dover DoverKent) 'CxStory))
(v/retract! kb eq)
(v/ask? kb '(different Dover DoverKent) 'CxStory)   ; => true
```

**Why.**

- *Engine.* Retracting the equality collects every twin it justified, and the originals
  are believed again under their own names. The class splits into what its remaining
  equalities still connect.
- *Engine.* A derived `equals` has no premise of its own, and retracting any fact, mark,
  `genl` edge or `genlCx` edge in its justification un-merges the pair.
- *Engine.* An `except` of the equality hides it from the excepting context and every
  context below. A goal there is not rewritten by the hidden merge, and `different` holds
  there between two names only the hidden merge joined.
- *Engine.* A late `rewriteOf` can move a representative. Every sentence already restated
  under the old one is restated again under the new one.

**Why not the other ways.** The equality relations are forced-monotonic, so a stated
`(not (sameAs Dover DoverKent))` loses to the merge at either strength and leaves it
standing. A twin is not a premise: the twin rests on the original and the equality, and
retracting either of those withdraws it.

**Audit.** After a retraction, ask `same-class?` of the two names in each context the
merge reached and confirm `false`, and run `why-not` on an original handle and confirm the
reason is no longer `:superseded`.
