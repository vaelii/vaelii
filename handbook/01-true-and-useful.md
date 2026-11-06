# 1. True and useful

- **Covers:** the test every modelling choice answers to: an option has to be true, and it
  has to let the engine conclude or rule out something; and the boundary test that applies
  it to the question "does X belong in concept Y?".
- **Not here:** where a choice is stated (the KB, code or prose) →
  [ch. 2](02-representation.md); how to find what separates a type from its neighbours →
  [ch. 9](09-differentia.md).
- **Assumes:** nothing. This chapter opens the handbook.

A vaelii KB holds sentences that an inference engine reasons over. The engine walks the
`genl` closure, fires forward and backward rules, separates disjoint types, derives the
type an argument declaration names, and keeps every conclusion under truth maintenance, so
a conclusion leaves when what it rests on leaves. A modelling choice is good when it is
true and when it gives that machinery something to do. The two principles below are the
first questions a reviewer asks of any change, and later chapters specialize them.

## no OE calligraphy

*True and useful, not OE calligraphy*

**Practice.** Weigh each modelling option on two counts: whether it is true, and what it
lets the engine do. For each option, list the derivations it licenses, the clashes it lets
the KB detect, the conclusions it carries forward over time, and the cases it forbids.
Choose a true option that does inference work. An option that is true and licenses
nothing loses to one that is true and licenses conclusions. A type defined so narrowly
that almost nothing can be a member also loses, because no rule over it ever fires.

**Example.** The shipped KB has no `ability` type. An ability is the ability to be the
doer of an event of some kind, so the second argument of `able` and
`abilityType` is an event kind, and the event kinds carry the hierarchy (abstract.txt,
life.txt, CxBiology.txt):

```clojure
(genl flying travelling)
(genl travelling causal_event)
(transitiveInArg able 2 genl)
(abilityType bird flying)
```

The `transitiveInArg` declaration carries a `able` claim up the `genl` hierarchy
of event kinds. For a bird `Tweety` believed to fly, the variable-free goal `(able
Tweety travelling)` is therefore answered at retrieval, with no rule and no stored record. The fact that travelling is a
`causal_event` is stated once and holds for the events and for the abilities together.

**Why.**

- **Logic.** A sentence is useful for what it entails beyond itself. `(genl flying
  travelling)` entails that every flying event is a travelling event, and, read through
  `able`'s declaration, that whatever can fly can travel. An ability modelled as
  an individual entails neither, because an individual has no subtypes for an entailment
  to run along.
- **Engine.** vaelii acts on structure. Matching a unary antecedent fans out over the
  `specs` closure, so a rule on `(animal ?x)` fires on a stored `(dog Muffet)`.
  `transitiveInArg` reads a `genl` edge at retrieval. A separation of two types separates
  every subtype of each. An argument declaration derives the declared type for each
  argument that fills the position. A distinction stated in these forms produces
  conclusions and clash checks. A distinction held only in a string, or only in the
  spelling of an individual's name, produces neither. Truth maintenance follows the
  structure as well: CxBiology defeats a penguin's flight, and the travelling answer for
  that penguin leaves with it, because the retrieval has no believed flight to read from.
- **Maintenance.** A representation that licenses conclusions is tested by every query
  that reaches it, so a mistake in it surfaces as a wrong answer or a placed clash. A
  representation that licenses nothing is read by no query, and a mistake in it stays
  until a person happens to read the line. New content also benefits: an event kind added
  below `travelling` gets the ability inference with no further sentence.

**Why not the other ways.**

- **True and inert.** A sentence that is true and licenses nothing still costs a stored
  sentex, a line for every reviewer and an entry in every census, and returns no
  conclusion. A type defined as "necessarily part of something" is the standard case: it
  sounds like a classification, and almost nothing follows from membership in it.
- **Useful and false.** An option that licenses many conclusions licenses false ones when
  it is not true. `doneBy` declares `thing` at its second argument, because a machine, a
  process or a storm brings events about. Under the entailing reading of argument types, a
  narrower type such as `agent` at that position would conclude every doer a member of
  it, a machine included. Inference work counts only when the conclusions are true.

**Audit.** For each option a vocabulary change weighs, write out the conclusions it adds
and the cases it rules out as queries a reviewer can run, and run them with `ask` and
`why`. Two `kb-quality` readings point at sentences that license nothing on the KB as it
stands: `:rules` lists the rules that never fired (`:never`) and the rules whose every
conclusion is defeated (`:all-defeated`), and `:declarations` lists under `:typed-thing`
the argument declarations that type a position `thing`, which derive no membership. A
rule in `:never` is a finding to explain: the change names the facts the rule is for.

## does it have rules?

*Include X in concept Y? Compare what's true of each side*

**genlPrinciple:** no OE calligraphy

**Practice.** For a boundary question, such as "are prosthetics body parts?" or "is a
sentient construct a human?", list the facts and rules that are true of X-with-Y and of
X-without-Y.

- A side with nothing true of it beyond the membership, or with only exceptions to what
  is true of the other side, is not a concept to represent.
- When both sides carry facts and rules of their own, the question names two concepts,
  and often one of them is a type and the other a role relation.
- A word in English that names each side is weak supporting evidence, because natural
  language draws its boundaries loosely.

**Example.** `person` and `human` are two concepts, and the KB says how they relate
(organism.txt, society.txt):

```clojure
(genl human mammal)
(genl human person)
(arg friendOf 1 person)
(arg marriedTo 1 person)
```

The boundary question is whether a sentient construct belongs in `human`. The rules true
of humans come from `mammal` and the kinds above it: CxBiology concludes every organism
alive and mortal by default, and every mammal warm-blooded through `(genl mammal
warm_blooded)`. None of those holds of a construct. The rules true of persons come from
the social relations, whose arguments are typed `person`, and all of those apply to a
construct. Both sides carry rules of their own, so the KB holds two types, with `human`
below `person`, and the comment on `person` names the construct as the case that makes
`person` broader.

**Why.**

- **Logic.** A type is a predicate, and two predicates with different entailments are
  two concepts. Folding one side into the other makes the folded side's rules true of
  members they are false of.
- **Engine.** Every rule on a type reaches every member of every subtype, because
  matching fans out over `specs`. Placing constructs under `human` would make the
  `organism` defaults in CxBiology fire on each construct and conclude it alive and
  mortal. Placing a type in the hierarchy is therefore a claim about which rules apply to
  its members, and the engine acts on that claim at the next write.
- **Maintenance.** A side that holds only exceptions turns every later rule on the
  concept into a rule with an `exceptWhen` for that side. A rule written by an author who
  does not know about the exception concludes the falsehood with no warning. Two concepts
  with a stated relation between them need no such exception.

**Why not the other ways.** Deciding by the word alone admits a prosthetic leg into
`body_part` because English calls it an artificial leg. The shipped `body_part` comment
defines a body part by growth: "A part an organism grew. It stays a body part once
transplanted into another organism or shed from its own." The rules true of grown parts
come from `biological` and are false of a device. A prosthetic shares with a leg the work
it does for a body, and a role relation between the device and the body states that work,
typed by what each filler is. Deciding by a definition alone also fails: a
definition can admit or exclude a case and still license nothing, and **differentia from
near-misses** ([ch. 9](09-differentia.md)) tests the definition, where this principle
tests whether any rule or fact holds of the concept's members.

**Audit.** For each boundary decision, the change lists the facts and rules true of each
side and where each is stated. `describe` on a type answers its `:genls`, `:specs` and
`:disjoint` lines and `:predicates-for-type`, the predicates whose argument declarations
admit it, which is the list of relations that say something about its members. For rules
that would contradict each other if both fired, `kb-quality`'s `:clashes` reading lists
the pairs and marks with `:excepted` a pair already carrying an `exceptWhen`. A concept
whose rules each need such an exception for one side is the "only exceptions" case.
