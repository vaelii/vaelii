# 25. Default or enumerate

- **Covers:** choosing between a default rule with stated exceptions and a list of the
  known cases; the three questions that decide; where the default lives and which readers
  it reaches.
- **Not here:** the forms an exception takes (`exceptWhen`, a nearer claim, `except`) →
  [ch. 30](30-exceptions.md); the strength of a separation → [ch. 24](24-strength.md);
  writing a rule → [ch. 29](29-rules.md).
- **Assumes:** [ch. 21](21-claims-about-kinds.md), [ch. 23](23-contexts.md),
  [ch. 24](24-strength.md).

A generalization over a type can be stated two ways. A default rule concludes the property
for every member and names the exceptions. A list states the property for each known case
and says nothing about any other. The two agree on every listed case and differ on every
member nobody listed.

## default or enumerate
*Default + exception vs. enumeration*

**Practice.** Before choosing, ask three questions about a member that is not listed:

- If something new were discovered, would you expect the rule to apply to it?
- If you hypothesized something, would you want the rule to apply to it?
- In a fictional or counterfactual context, would you expect the rule to apply?

The more of the answers are yes, the better a default with stated exceptions fits. Where
the rule should not reach new, hypothesized or fictional members, list the known cases and
conclude nothing about the others. The questions are considerations and not a required
check.

**Example.** `CxNormalPhysicalConditions.txt` uses both forms in one file. It lists three
kinds of stuff as solid, one edge each, and states metal as solid by default with mercury
the exception:

```clojure
(genl stone solid)
(genl wood solid)
(genl glass_stuff solid)
(genl mercury liquid)
(exceptWhen (mercury ?x)
  (set/defaultRule (set/forwardRule (implies (and (metal_stuff ?x)) (solid ?x)))))
```

The note above the rule reads "A default rule with its exception rather than a genl edge
per known metal: a metal newly found, hypothesized or made up comes out solid unless the
KB says otherwise."

**Why.**

- *Logical.* The default says every metal is solid unless the KB says otherwise. The list
  says stone, wood and glass are solid and says nothing about a substance it does not
  name.
- *Engine.* Matching fans the rule's `metal_stuff` antecedent over its `genl` spec closure,
  so a type placed below `metal_stuff` later is covered with no new sentence. The rule is a
  `set/defaultRule` with an `exceptWhen`, so each conclusion is `:default`, and a stronger
  contrary fact defeats it instead of meeting a hard clash.
- *Engine.* The `exceptWhen` blocks the rule for a portion of mercury before it concludes.
  `abstract.txt` separates `solid` from `liquid` through the `:monotonic`
  `(disjoint_metatype stuff_type_by_state_of_matter)`, so a solid conclusion beside the
  portion's liquid membership would be a nogood. With the exception, the note says, "the
  portion's liquid membership meets no solid one and nothing clashes."
- *Maintenance.* The default is one rule and one exception per known outlier. A list grows
  by one sentence for each case, and a case nobody added gets no conclusion.

**Why not the other ways.** A `genl` edge for each known metal concludes nothing about a
metal the KB has not been told of, so a newly found or hypothesized metal has no state. The
same rule with no `exceptWhen` concludes solid for a portion of mercury, and the
conclusion is a nogood with the portion's liquid membership.

**Audit.** For each generalization a change states, answer the three questions in a `;;`
note above it, and confirm the form matches the answers: a default with its exceptions
named when the answers are yes, a list when they are no.

## A default and the readers it reaches

**Practice.** After choosing a default, place it in the context whose readers the three
questions were about. A default reaches the contexts that see the context it is stated in,
and no others.

**Example.** `CxBiology.txt` states the flight default in a theory `CxWell` sees, so every
context below `CxWell`, a fiction included, reads it:

```clojure
(exceptWhen (penguin ?x)
  (set/defaultRule (set/forwardRule (implies (and (bird ?x)) (able ?x flying)))))
```

The metal default sits in `CxNormalPhysicalConditions`, which sees `CxRealWorld` and which
`CxWell` does not see. Its header says it "excludes every fiction" and that the contexts
below `CxWell` "assume no temperature and serve a story set on Mars as well as one set in
a kitchen."

**Why.**

- *Engine.* A rule fires only where its context is visible, and its conclusion is placed
  where the rule and the facts it read are both seen. A fiction placed under `CxWell`
  reads the flight default and not the metal default.
- *Logical.* A state of matter depends on temperature and pressure, so the metal default
  is a claim about ordinary conditions. Stating it where the conditions are fixed keeps it
  from concluding a state for a setting whose conditions differ.
- *Maintenance.* The context choice answers the third question for a whole theory at once,
  and a reader finds the answer in the file's header.

**Why not the other ways.** A default stated in a context every fiction sees reaches
fictions the author meant to exclude. A default stated below `CxRealWorld` does not reach
a fiction, even where the author's answer to the third question was yes; the
`metal_stuff` rule is in that case, so a fiction under `CxWell` gets no state for a metal
from it.

**Audit.** For each default, name the context it is stated in and the contexts that see
it, and confirm the set matches the answer given to the third question.
