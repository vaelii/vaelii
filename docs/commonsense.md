# Common sense, and how it is checked

- **Covers:** what counts as a common-sense test, and the sweep of questions it asks per
  reasoning subsystem.
- **Not here:** what each subsystem does with the questions → the subsystem's own page,
  from [README.md](README.md).
- **Assumes:** context, defeasible, `abducible_predicate` → [glossary.md](glossary.md).

Two test namespaces ask this knowledge base the questions it exists to answer, one per
reasoning subsystem.

| | |
|---|---|
| [`common_sense_test.clj`](../test/vaelii/common_sense_test.clj) | reasoning over the shipped schema and the test-world's cast |
| [`common_sense_qualitative_test.clj`](../test/vaelii/common_sense_qualitative_test.clj) | the six algebras plus duration and metric time, over networks |

## What counts as a common-sense test

**A question with no stored answer.** That is the whole selection rule, and it is what
separates these two namespaces from the three hundred beside them: a test that reads back what
its fixture asserted is testing storage, and belongs next to the subsystem it exercises.
What is left is knowledge the KB produced — a type nobody stated, a comparison nobody
computed, a containment nobody wrote down.

The second rule is that each one is phrased the way somebody would ask it. *A cup in a box
in a room is in the room.* *Half an hour and an hour are ninety minutes.* *Which of two
animals is heavier is read off their weights.* If the name of a test needs the engine's
vocabulary to make sense, it is a subsystem test wearing the wrong hat.

## The sweep

| subsystem | the question it is asked | doc |
|---|---|---|
| taxonomy | is a penguin a thing; is a dog a cat | [taxonomy.md](taxonomy.md) |
| disjointness | can one animal be two kinds that exclude each other | [taxonomy.md](taxonomy.md) |
| inheritance | are dogs bigger than ants, given only that mammals are bigger than insects | [inherit.md](inherit.md) |
| argument types | what is Bone1, given only that Muffet eats it | [argtypes.md](argtypes.md) |
| evaluables | is 1970 before 1995; what is 3 × (2 + 4) | [inference.md](inference.md) |
| backward chaining | who is older, given two birth years | [inference.md](inference.md) |
| defaults | does the eagle fly, and does the penguin | [nmtms.md](nmtms.md) |
| exceptions | told the cat is asleep, is it still awake | [exceptions.md](exceptions.md) |
| belief | known-true against a default, and default against default | [nmtms.md](nmtms.md) |
| aggregation | how many children has Bob; how many of the people are parents | [aggregate.md](aggregate.md) |
| negation as failure | is anything known about whether the cat is asleep | [naf.md](naf.md) |
| inertia | the cat fell asleep at three and woke at five — asleep at four | [time.md](time.md) |
| change over time | told later that it was let out, is it still indoors | [time.md](time.md) |
| joined NAF | is any child of Tom a sibling of Ann — one witness, not two | [naf.md](naf.md) |
| universals | is every child of Bob a parent; is every child of a childless cat | [naf.md](naf.md) |
| closed extents | told the sibling relation is completely known, are these two not siblings | [naf.md](naf.md) |
| abduction | why would a dog not be awake | [abduction.md](abduction.md) |
| equality | two names arrive for one person | [equality.md](equality.md) |
| non-atomic terms | who is the mother of this dog, named or not | [nat.md](nat.md) |
| skolemization | every dog had a mother, whether or not anyone knows who | [skolem.md](skolem.md) |
| quantity | does a kilogram outweigh 999 grams; which animal is heavier | [quantity.md](quantity.md) |
| mereology | where is the piston, given where the car is | [contexts.md](contexts.md) |
| contexts | can the social theory see the natural world's facts | [contexts.md](contexts.md) |
| levels | how hard was each of these to answer | [levels.md](levels.md) |
| RCC-8 | a cup in a box in a room | [space.md](space.md) |
| scenarios | write down one arrangement that satisfies all of it | [scenario.md](scenario.md) |
| refutation | three intervals each before the next, in a ring | [qcn.md](qcn.md) |
| Allen | breakfast before lunch before dinner | [time.md](time.md) |
| point algebra | one moment before another before a third | [time.md](time.md) |
| events on a clock | is the hare asleep while the tortoise goes past | [time.md](time.md) |
| cardinal direction | north of something east of something | [space.md](space.md) |
| relative direction | left of a thing left of a thing | [space.md](space.md) |
| distance | two things very close to a third | [space.md](space.md) |
| duration | half an hour and an hour; two meals that cannot overlap | [duration.md](duration.md) |
| metric time | six hours then six hours | [stp.md](stp.md) |
| sign arithmetic | does the tub fill while the tap beats the drain | [sign.md](sign.md) |
| trends | does a cooling body's temperature fall | [sign.md](sign.md) |

**What is deliberately not here.** Anytime evaluation bounds a computation rather than
answering about the world, and *within fifty milliseconds* is not a common-sense question.
The `Solver` protocol wants a labelling context and `set/assumptionRule` rules to ground, which
is a mechanism rather than a story — the belief question it settles is asked above, at the
level a person would ask it. Equational rewriting, `preview`, `watch`, overlay and the
foreign bridge are not claims about the world at all.

## What the schema carries for these questions

Four things the questions need live in the **shipped KB** rather than in the tests,
because a gap a test papers over locally is a gap every other consumer still has.

**The unit table.** `measure.txt` ships Length in `Meter`, Mass in `Kilogram` and
Duration in `Second`, so the measure vocabulary is something a query can compute with
rather than a grammar. The test for admitting a unit is the one `core.txt` applies to
its own vocabulary: **a unit belongs when its factor is a definition rather than a
measurement**. A minute is sixty seconds by stipulation; how much a particular dog weighs
is not.

**`weightOf` / `heightOf`, and the comparisons over them.** `heavierThan` and `tallerThan`
are backward rules in `CxSize` reading two measures through the quantity provers —
the same shape `olderThan` has over two birth years. All three are also declared
**transitive**, which is the route a common-sense KB actually takes: nobody weighs an
elephant, and two stated comparisons compose into a third off the closure. The two halves
of `CxSize` are deliberately not connected: a dog being a larger *kind* than a cat does
not make this dog heavier than that cat.

**The sign vocabulary, and no numbers at all.** `measure.txt` also ships `signOf` /
`trendOf`, the three `qualitative*` arithmetic relations, the `derivativeOf` edge and
`greaterInMagnitudeThan` — which is the layer for the questions a person can answer and a
measure cannot, because nobody has the figure. A tub fills while the tap beats the drain,
and the KB says so from four sentences none of which mentions a litre
([sign.md](sign.md)).

**`motherOf` / `fatherOf`, with `MotherFn` / `FatherFn` beside them.** The reified
functions are what let a KB name somebody by their role before it knows their name, and
the correspondence merges the constant `(MotherFn Pup)` mints with a mother already
stored, so a read of either name finds the other's facts. Both predicates are functional,
so a second mother merges rather than piling up.

**The event calculus, and the fluents to run it on.** `CxChange` ships the inertia
axioms and `time.txt` the vocabulary they are stated in, so *asleep at four* is a question
about the shipped KB rather than about a theory the test wrote for itself. The fluents are
the test-world's, because a fluent is contingent: `(AsleepFn Whiskers)` is one animal's
state, and `CxWell` is where the cast declares its reifiable functions so the natural world
and the fables can both use them.

**One abducible grant.** `CxBiology` declares `(abducible_predicate asleep)` and
nothing else, which is what makes *why is this dog not awake* answerable and *why does it
not fly* refused with the dead end named. A grant is a policy the context states, and
the whole value of abduction here is what is **not** granted.

## Running it

```sh
lein test vaelii.common-sense-test vaelii.common-sense-qualitative-test
```

Both are ordinary members of `:default`, so `lein gate` runs them.
