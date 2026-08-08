# Common sense, and how it is checked

- **Covers:** what counts as a common-sense test, the sweep of questions it asks per
  reasoning subsystem, and how an outside model judges the derived answers.
- **Not here:** reading English into the KB → [reading.md](reading.md); the LLM
  edit-proposal pipeline the oracle sits beside → [llm.md](llm.md).
- **Assumes:** context, defeasible, `abduciblePredicate` → [glossary.md](glossary.md).

Two test namespaces ask this knowledge base the questions it exists to answer, one per
reasoning subsystem, and a third instrument puts its answers to an outside reader.

| | |
|---|---|
| [`common_sense_test.clj`](../test/vaelii/common_sense_test.clj) | reasoning over the shipped schema and the test-world's cast |
| [`common_sense_qualitative_test.clj`](../test/vaelii/common_sense_qualitative_test.clj) | the six algebras plus duration and metric time, over networks |
| [`vaelii.impl.llm.oracle`](../src/vaelii/impl/llm/oracle.clj) | the conclusions glossed into English and judged by a model |

## What counts as a common-sense test

**A question with no stored answer.** That is the whole selection rule, and it is what
separates these two namespaces from the hundred beside them: a test that reads back what
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
| aggregation | how many children has Bob; how many people are there | [aggregate.md](aggregate.md) |
| negation as failure | is anything known about whether the cat is asleep | [naf.md](naf.md) |
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
| cardinal direction | north of something east of something | [space.md](space.md) |
| relative direction | left of a thing left of a thing | [space.md](space.md) |
| distance | two things very close to a third | [space.md](space.md) |
| duration | half an hour and an hour; two meals that cannot overlap | [duration.md](duration.md) |
| metric time | six hours then six hours | [stp.md](stp.md) |

**What is deliberately not here.** Anytime evaluation bounds a computation rather than
answering about the world, and *within fifty milliseconds* is not a common-sense question.
The ASP solver seam wants a labelling context and an `assumptionRules` declaration, which
is a mechanism rather than a story — the belief question it settles is asked above, at the
level a person would ask it. Equational rewriting, `preview`, `watch`, overlay and the
foreign bridge are not claims about the world at all.

## What the schema carries for these questions

Four things the questions need live in the **shipped KB** rather than in the tests,
because a gap a test papers over locally is a gap every other consumer still has.

**The unit table.** `MeasureContext` ships Length in `Meter`, Mass in `Kilogram` and
Duration in `Second`, so the measure vocabulary is something a query can compute with
rather than a grammar. The test for admitting a unit is the one `CoreContext` applies to
its own vocabulary: **a unit belongs when its factor is a definition rather than a
measurement**. A minute is sixty seconds by stipulation; how much a particular dog weighs
is not.

**`weightOf` / `heightOf`, and the comparisons over them.** `heavierThan` and `tallerThan`
are backward rules in `SizeContext` reading two measures through the quantity provers —
the same shape `olderThan` has over two birth years. The two halves of that file are
deliberately not connected: a dog being a larger *kind* than a cat does not make this dog
heavier than that cat.

**`motherOf` / `fatherOf`, with `MotherFn` / `FatherFn` beside them.** The reified
functions are what let a KB name somebody by their role before it knows their name, and
the correspondence is what stops `(MotherFn Pup)` from minting a second name for a mother
already stored. Both predicates are functional, so a second mother merges rather than
piling up.

**One abducible grant.** `BiologyContext` declares `(abduciblePredicate asleep)` and
nothing else, which is what makes *why is this dog not awake* answerable and *why does it
not fly* refused with the dead end named. A grant is a policy the context states, and
the whole value of abduction here is what is **not** granted.

## The judge, and which way the trust runs

`vaelii.impl.llm.text` reads English **into** the KB, where the danger is a model writing
something false into the store and the defence is a reviewer between the two
([reading.md](reading.md)). The oracle is the same seam pointed the other way: the KB
makes the claims and the model is asked whether an ordinary person would agree.

Nothing a verdict says can reach the store. The namespace calls no writer, a test greps it
for one, and a second test judges a whole computed claim set and asserts not one sentex
moved. A
disagreement is **a finding for a person to read** — never a retraction, never a defeat
class, and never a reason to edit the KB until the number goes up.

That is what the instrument is for. The engine can check that a conclusion follows and
that a sentence is well formed; nothing in it can check that the knowledge is *true*, and
a KB full of well-formed nonsense passes every other gate in this repo.

Four decisions carry the design:

- **The claim is glossed, and one the KB cannot gloss is not sent.** A model handed
  `(genl penguin bird)` is judging our notation. `vaelii.impl.gloss` composes the English
  from the KB's own comments, so what the judge sees is the knowledge base's sentence. A
  sentence the KB documents nothing about glosses to `:named` and is skipped and counted:
  an unanswerable question dressed up as a low score measures the prompt.
- **A derived claim is shown its situation, and never its rule.** *Muffet is awake* is not
  judgeable — nobody knows Muffet. *Given: Muffet is a dog. Claim: Muffet is awake.* is. The rule
  is left out because showing it turns the question into *does this follow*, which is
  validity, the one thing the engine already guarantees. The `genl` edges the firing went
  through are left out too: an edge is vocabulary, not a situation.
- **Three verdicts.** Most of this KB is defaults, and a judge forced to answer yes or no
  about *an animal is awake* picks one — measuring the coin. `unsure` is where a claim that
  turns on particulars nobody supplied belongs, and it is counted apart.
- **A control group.** Five claims the ontology's own content says are false go into the
  same batch, three about kinds and two about things, none of them contradicting anything
  stored. Without them the headline number is not a measurement: on a run made only of
  sound conclusions, a judge that answers `true` to everything scores exactly as well as a
  judge that is reading.

## What it measured

`phi4:14b`, pinned at the `num_ctx` 4096 its host already serves — a different model or a
different window costs an evict-and-reload, which on a shared host is not a private act.
81 derived conclusions plus 5 planted falsehoods, 5 batches of 20, three runs:

| | claims | agreed | disputed | unsure | agreement over the decided |
|---|---|---|---|---|---|
| **the KB's own conclusions** | 81 | 60–63 (74–78%) | 1–2 | 17–19 | **97–98%** |
| **the planted falsehoods** | 5 | 1 (20%) | 3 | 1 | **25%** |

46–51 s a run, wall clock, warm. The controls answered identically in all three runs; the
sound half moved by three claims between them, so a difference under about five points
across runs is noise.

The gap between 97% and 25% is the result. The absolute numbers on their own would say
very little.

## What it found

**A definitional gloss reads as a definition, not as a claim.** The one disagreement in
every run is `(ancestorOf Dave Eve)`, glossed *Dave is a parent of Eve, or a parent of an
ancestor of Eve* — and the judge answers the definitional question behind it (*is a parent
an ancestor?*) rather than the substituted one, which given *Dave is a biological parent of
Eve* is plainly true. `ancestorOf`'s comment opens with a disjunctive definition, and
substituting arguments into a definition produces a line that invites the reader to argue
with the definition. The knowledge is right and the inference is right; the sentence put to
the judge is the wrong shape.

**A default gets disputed, and says which it is.** One run disputed *Piston1 sits within
Garage1* — the mereology default carrying location down parthood — on the ground that it
does not follow "unless explicitly stated". That is a fair thing to say about a default,
which is why every disagreement carries the strength the claim is held at: `[default]`
beside one is not an excuse for it, it is the fact a reader needs to decide whether the
judge found a bad claim or a defeasible one.

**An inverted argument is invisible to this instrument.** The falsehood that got through,
in all three runs, is `(eats Kibble Muffet)` — *Kibble takes Muffet as nourishment* — which the
judge agreed with, noting that kibble is what dogs like Muffet eat. It read the sentence as
the sensible claim rather than the one written. This is the sharpest limit of the method
and it is worth stating plainly: **a judge repairs an implausible reading instead of
disputing it**, so a KB bug that swaps two arguments of a plausible relation is exactly the
class this cannot catch. It is also the class `reading.md` names as the reason the reading
direction needs a reviewer, which makes it the same hole seen from the other side.

**A premise about a named individual has no situation.** `(not (mortal Rex99))` came back
`unsure` — *without knowing what Rex99 is, we cannot determine if it will die* — because a
premise rests on nothing, so nothing is shown with it. Most of the 17–19 unsure verdicts
are this shape. Showing an individual's types alongside a claim about it would move some of
them, at the cost of a longer line.

## What the rate is not

It is not an accuracy and not a benchmark. A careful judge marking a default false is
telling you the default has exceptions, which the KB knows and stores as a default for
exactly that reason. A judge that shrugs at a claim about a made-up dog is right to. The
disagreements are the output; the rate is the index into them.

Nor is it a gate. The live test asserts three things and none of them is a threshold on the
rate: that the judge answered at all, that it disputed some of the planted falsehoods, and
that it agreed with the sound conclusions more readily than with the false ones. A number
that has to stay above a line is a number somebody eventually tunes the KB to.

## Running it

```sh
lein test vaelii.common-sense-test vaelii.common-sense-qualitative-test
lein test vaelii.llm-oracle-test                 # the machinery, offline
VAELII_LLM_LIVE=1 lein test :only \
  vaelii.llm-oracle-test/a-live-model-judges-what-the-kb-concluded
```

The first two are ordinary members of `:default`, so `lein gate` runs them. The oracle's
own tests are too — the stub provider means the pipeline is checked without a host. Only
the last needs a model, and it needs two separate consents to reach one: the `^:llm` mark,
which `:default` and `:all` both exclude, and `VAELII_LLM_LIVE=1`. A reachable Ollama on
the machine is not consent ([llm.md](llm.md)).  It asks the Ollama at `localhost:11434`
unless `VAELII_OLLAMA_HOST` names another, and skips with that address printed when
nothing answers there — so a run against a host on the network says so in the command
rather than in the source.
