# Contexts

- **Covers:** how a sentex is scoped to a context, how the `genlCx` closure orders
  contexts into the shipped spindle, where a forward-derived or lifted fact is placed, and
  the three **query contexts** — `Cx…` symbols that name a way of reading rather than a
  place.
- **Not here:** `genl`, the sibling closure over types rather than contexts →
  [taxonomy.md](taxonomy.md); a storage-level private copy of a whole KB, which a context
  does not provide → [overlay.md](overlay.md).
- **Assumes:** sentex, belief, `genl`, taxonomy → [glossary.md](glossary.md).

Every sentex is in exactly one **context** (a `Cx`-prefixed CapitalCamelCase symbol). Contexts
partition and scope belief.

## genlCx: the context hierarchy

`(genlCx Sub Super)` means `Sub` *sees* `Super` — a specific context inherits the
assertions of the more general ones. `vaelii.impl.taxonomy` caches the reflexive-
transitive up/down closure (`context-up`, `context-down`, `sees?`), recomputed when a
`genlCx` edge is asserted/retracted. A context `K` sees a sentex in context `Y`
iff `Y ∈ context-up(K)`.

**A `genlCx` edge is `:monotonic` and undeniable.** `genlCx` is on the forced-monotonic
roster ([nmtms.md](nmtms.md#the-forced-monotonic-roster)): every edge is held
`:monotonic` whatever strength it was written at, so it caps no firing's class, and a
denial of one is held OUT.

**A `genlCx` cycle is refused at assert, like a `genl` cycle.** The context hierarchy
is a partial order: `wff/genlCx-problems` reads the global `genlCx` closure and refuses
an edge whose super already sees its sub, so mutual visibility is not a claim the edge
set may assert. A cycle a recovered or foreign store replays past that check
(`recovery/recover`) is still held — reachability over a cycle is well defined, so the
closures answer it directly; the taxonomy keeps its depth potential over the
**condensation** and reads a mutually-visible pair in O(1) (see [taxonomy.md](taxonomy.md)).

A held cycle is not a merge. The contexts stay distinct records with distinct
extents, because a context is where a sentex is **stored** and not only what it can see:
`sentexes-matching` is exact-context, `(ist CxA S)` and `(ist CxB S)` are two
sentexes, and collapsing them would throw away which context an assertion was made
in — the one thing an ontology import exists to carry. The claim "each sees the other"
is weaker than "these are the same place", and the taxonomy holds only the weaker one.

The single point where the engine needs a unique answer is **placement**, since every
member of a component is an equally maximal common descendant and the conclusion should
land once rather than once per name. `taxonomy/placement-rep` picks the component's
`term-min` — content-keyed, so it cannot depend on the order a firing's antecedents were
listed in — and every one of `maximal-common-descendant-contexts`' exits runs through it,
the single-context fast path included.

That answer is only as good as `:scc`, which makes the component map the one piece of
derived state here that is **more than a pruning**. A dissolved-but-unrepaired component
does not merely cost `sees?` a walk; it leaves the group with no name, so
`placement-rep` hands back whichever member the caller happened to ask about. Belief is
what can dissolve one without a sentex moving — an edge defeated out of a cycle, or
revived back into one — so `settle` repairs the potential **after** it reconciles belief
as well as before, and no firing ever runs against a component the reconcile unmade.
Deferred to the next settle instead, one conclusion would land in `CxAlpha` and the
next in `CxBeta` for no reason but how many settles had run since the defeat.

## The context spindle

**A spindle is three layers**: a **head** every member sees, a set of **members** that
see the head and not each other, and a **collector** that sees every member. The default
topology is **two spindles stacked**, most general (top) to most specific (bottom):

| | head | members | collector |
|---|---|---|---|
| the upper spindle | CxCore | `resources/kb/upper/` — eight contexts | CxUniverse |
| the middle spindle | CxUniverse | `kb/middle/` — seven contexts, beside four opt-in theories | CxWell |

CxUniverse is the joint, the first spindle's collector and the second's head, and it can
be the second's head *because* it is the first's collector: a head is a context every
member sees, and collecting the whole upper spindle is what makes CxUniverse one.
Data hangs below CxWell.

- **CxCore** — the upper spindle's *head*: the code-supported vocabulary (every
  special predicate the engine interprets), asserted by `vaelii.host.core-context`. The
  root — every context in the spindle sees it, and a context no `genlCx` edge names
  sees nothing but itself ([A context outside the
  spindle](#a-context-outside-the-spindle)). It also holds the collections at the top
  of the ontology — the parts of the three partitions of `thing`
  ([taxonomy.md](taxonomy.md#the-three-partitions-of-thing)), `spatiotemporal`,
  `nowhere_never`, `logical`, `linguistic`, `quantitative`, `biological`, `organism`
  and `measure` — which the
  engine reads by no name (`vaelii.impl.predicates` classifies each inert) and which are
  here for the reason below: the members of a spindle see each other not at all, so a
  term two of them extend has to be defined in the head.
  `starter_test/a-term-two-spindle-members-touch-is-defined-in-the-head` holds that.
- **the upper spindle's members** (`resources/kb/upper/`) — what things *are*, always
  true, like `genl`. One context per domain (`vaelii.host.starter`), each seeing CxCore
  and seen by CxUniverse:
  - `CxAbstract` — the kinds hanging off the skeleton CxCore holds (`made`,
    `food`, `substance`, `body_part`, `context`, …) plus the
    structural relations `partOf`/`locatedIn`.
  - `CxOrganism` — the biological taxonomy and its disjointness.
  - `CxLife` — the organism relations (`parentOf`, `siblingOf`, `flies`, `mortal`,
    `birthYearOf`, `olderThan`, …) with their arg and metadata.
  - `CxSociety` — the social relations (`marriedTo`, `likes`, `owns`).
  - `CxMeasure` — the theory of measurement: the two measure terms, the
    `dimensionOf`/`conversionFactor` table, the five comparisons
    ([quantity.md](quantity.md)), and measurement said as coarsely as it can be said —
    `signOf` / `trendOf`, the three qualitative arithmetic relations and the
    `derivativeOf` edge, for the quantities nobody has a figure for
    ([sign.md](sign.md)).
  - `CxReflection` — the language the KB is written in, as something the KB can talk
    about: the expression lattice (atomic and non-atomic expressions, open and closed,
    well-formed and ill-formed) and the use/mention vocabulary `proposition`, `means`,
    `denotes` and `expresses`. CxCore keeps the expression kinds the engine or its own
    declarations name (`symbol`, the value kinds, `formula`, `sentence`,
    `non_atomic_term`) and `linguistic`.
  - `CxSpace` — qualitative space, four independent calculi in one context because
    all four are *about* space: RCC-8 topology, cardinal direction, relative direction
    and qualitative distance, fifty predicates between them ([space.md](space.md)).
  - `CxTime` — qualitative time in three layers over the same subject: Allen's
    thirteen interval relations plus seven derived disjunctions, the point algebra over
    instants with the endpoint predicates that bridge the two, and the metric layer
    (`temporalDistance`) that puts real measures on the gaps ([time.md](time.md),
    [stp.md](stp.md)). The `length` / `totalDuration` / `overlapDuration` vocabulary the
    duration arithmetic computes over lives here too ([duration.md](duration.md)), and so
    do the three calendar constructors `YearFn` / `MonthFn` / `DayFn`, which name an
    interval the calendar already picks out ([context-nat.md](context-nat.md)).
- **CxUniverse** — the upper spindle's *collector* and the middle spindle's *head*, left free for **lifting**: universally-true facts collect here
  (`decontextualized_predicate` justifications and the forced `genlCx` extent). It sees
  every upper member and is seen by every middle member. It also holds hand-authored
  cross-member axioms in `resources/kb/CxUniverse.txt`: a claim naming terms from two
  upper members belongs here, since no member sees a sibling and only the collector
  sees both. It holds `(termsRelated time_interval Duration)`, which names CxAbstract's
  `time_interval` beside CxMeasure's dimension, and the `travelling` and `flying` event
  kinds CxLife's abilities name, whose `genl` edges reach CxAbstract's `causal_event`. It
  also states each shipped context's `context` membership, since it stores every
  `genlCx` edge. `organization` and `animal`, the pair it once separated, are already
  separated by `(partition thing tangible intangible)` in CxCore. Being the one context
  that sees the whole upper spindle is what makes it the head of the next.
- **the middle spindle's members** (`kb/middle/`) — how the definitional things *interrelate*,
  where several overlapping theories can coexist. One context per theory, each seeing
  CxUniverse and seen by CxWell:
  - `CxKinship` — grandparentOf, ancestorOf, olderThan.
  - `CxMereology` — a part is located where its whole is; owning a whole entails
    owning its parts.
  - `CxBiology` — birds fly by default except penguins; organisms are mortal;
    flight enables travel.
  - `CxChange` — a simple event calculus: a state persists until an event ends it,
    so `holdsAt` is inertia over what `initiates` and `terminates` say
    ([time.md](time.md)).
  - `CxAnatomy` — what kinds of thing have what kinds of part, entirely in
    `partType` claims. Nothing here concludes anything about an individual, which is
    deliberate: "birds have wings" to "Pingu has a wing" needs a quantifier reading.
  - `CxSize` — comparative size said the two ways it can be said: `largerThan`
    among kinds, and a comparison computed between two objects' measures. The worked
    example of `transitiveInArgInverse` ([inherit.md](inherit.md)).
  - `CxSocial` — what acquaintance follows from, how employment relates to
    membership, and the general relationship and dwelling vocabulary over two
    persons: `relativeOf`, `romanticPartnerOf`, `coworkerOf`, `roommateOf`,
    `originatorOf` (read by a rule from `parentOf`), `relationshipLabel`, and
    `dwelling`/`dwellsIn` (whose rule derives `roommateOf` for co-dwellers). Every
    rule runs one way only, because `knows` is deliberately not symmetric.
- **CxNormalPhysicalConditions** — an **opt-in** theory in `kb/middle/` that sees
  CxUniverse and that CxWell does **not** see: the states of matter of stuff at ordinary
  room temperature and pressure. Stone, wood and glass are solid, mercury is liquid, and a
  metal is solid by default, with mercury the stated exception. CxWell stays free of any
  temperature, so a context below CxWell serves a story set on Mars as well as one set in a
  kitchen. A context opts in by placing itself under CxNormalPhysicalConditions, and a
  context under both CxWell and CxNormalPhysicalConditions reads the everyday theories at
  room temperature.
- **CxComputing** — an **opt-in** theory in `kb/middle/` that sees CxUniverse and that
  CxWell does **not** see: ten relations over software tools, their invocations and
  receipts, media resources and DNS names, and the sixteen kinds the relations are typed
  over (`computational_system`, `software_tool`, `tool_invocation`, `media_resource`,
  `ip_address` and the kinds below them), each with its comment, its `genl` edges and
  its disjointness. CxComputing states no rule. A context opts in by placing itself
  under CxComputing, and a context that does not see CxComputing reads neither a
  relation nor a kind. `(functional toolName)` is a decontextualized mark, so every
  context that sees CxUniverse reads that mark.
- **CxPerception** — an **opt-in** theory in `kb/middle/` that sees CxUniverse and
  that CxWell does **not** see: perception relations. `perceives` is the general
  relation, and `sees`, `seeImage` and `watchVideo` each specialize it. A context opts
  in by placing itself under CxPerception.
- **CxSocialExtension** — an **opt-in** theory in `kb/middle/` that sees CxSocial,
  and through it CxUniverse, and that CxWell does **not** see: `nestingPartnerOf`
  (read by a rule from CxSocial's `romanticPartnerOf` and `roommateOf`) and
  `chosenSiblingOf`. A context opts in by placing itself under CxSocialExtension,
  which also carries CxSocial's own relations to it. **`<Theory>Extension` names a
  theory that extends an existing starter theory with vocabulary most contexts
  under the base theory have no occasion to see:** the base theory ships to every
  context below CxWell, and the extension only to a context placed under it.
- **CxWell** — the middle spindle's *collector*: it sees every middle member, so it
  (and any context hung beneath it) transitively sees the whole ontology except the
  four opt-in theories, CxNormalPhysicalConditions, CxComputing, CxPerception and
  CxSocialExtension.

**A member sees no member, so a shared term belongs in the head.** That is what makes a
spindle a spindle: `CxLife` does not see `CxOrganism` and `CxOrganism` does not see
`CxAbstract`. A term defined in one member and *extended* from another is therefore
invisible where it is extended, and the closure breaks — an edge placing `animal` under
`organism` in `CxOrganism` against an `organism` defined in `CxAbstract` left `animal` unable to
reach `thing` from `CxOrganism` itself, so every `arg` constraint written there convicted
nothing in its own context. So a term more than one member of a spindle defines or
extends belongs at or above that spindle's head: CxCore for the upper spindle, and
CxUniverse or anything CxUniverse sees for the middle spindle. *Using* a member's term
from another member is a separate question the rule does not cover — extending one is
what breaks a closure.

Each member file wires *itself* in with two `genlCx` edges — one to its spindle's head
and one to its collector — so the topology is **data**: dropping a `Cx<Name>.txt` in
`resources/kb/upper/` or `resources/kb/middle/` adds a member, no code change, and every
context present is loaded on kb start by default. There is **no** direct `(genlCx CxWell
CxCore)` edge; Well reaches Core through both spindles (middle member → CxUniverse →
upper member → CxCore).

`vaelii.host.core-context` loads only the head (CxCore); the members are the starter's,
so a **CxCore-only KB is just the vocabulary** — a head with no spindle under it.

### The shipped KB is schema only

The starter ships **no individuals and no facts** — only types, relation definitions,
and the theory rules. Contingent data (a cast, worked examples, the Aesop fables)
belongs **below CxWell** and lives in the tests that need it: `test/vaelii/world.clj`
hangs `CxNaturalWorld` / `CxSocialWorld` off CxWell, and
`test/vaelii/world_fables.clj` hangs `CxStories` there with a context per fable
beneath it.
Because a middle theory is seen by every CxWell descendant, a rule firing over
cast facts in `CxNaturalWorld` places its conclusion back in `CxNaturalWorld`
(the maximal common descendant), where a query finds it.

### Adding a sibling context

A user adds their **own member** to either spindle. An *upper* member sees
CxCore and is seen by CxUniverse (`(genlCx CxMy CxCore)` and
`(genlCx CxUniverse CxMy)`); a *theory* sibling sees CxUniverse and
is seen by CxWell. Its vocabulary is visible from every data context below Well
without touching the shipped members.

## Context-aware inference

`res/matches-visible` restricts matching to facts visible from a query context
(its `context-up` closure). Backward chaining (`query`, `prove`) uses it, so
proving a goal *in* a specific context can use facts asserted in the general
contexts it inherits — but not the other way around.

## The query contexts: reading modes wearing a context's spelling

Three `Cx…` symbols stand where a context stands and name a **way of reading** rather than
a place. They are resolved at the read entry point (`core/read-in-context`) and never reach the
engine; the write side refuses them at `assert` and in the `genlCx` slots, so nothing is
stored in one and nothing wires one into the lattice.

A **variable** context — `?ctx`, the default of every short arity, or any name you
choose — is the joint reading too. It is not a fourth mode: it is `CxInference` with
somewhere to put the answer.

| you pass | belief | whose view must hold the answer | where the witness goes |
|---|---|---|---|
| `CxEverything` | **ignored** | — *(the store, not a view)* | — |
| `?var` (incl. the default `?ctx`) | followed | every literal in **one** view | unified into that variable |
| `CxInference` | followed | every literal in **one** view | `:context`, beside the bindings |
| a real `Cx…` | followed | every literal in **this** view | — |
| `CxNothing` | followed (vacuously) | the empty view — the provers alone | — |

Two axes, not a ladder. `CxEverything` is the odd one out and not by a degree: it is a
named opt-out of the fourth invariant, so its answers are not belief claims and say a
derivation is *spelled* in the store rather than held. Everything else asks what the KB
holds, and differs only in whose view has to hold it.

Rows two and three are the **same reading**. A variable names somewhere to put the witness,
so it is unified in — and unified, not assoc'd: a variable the goal has already bound to a
different context drops the answer rather than being overwritten. `CxInference` is a
constant, names no variable, and so has nothing to bind; its witness goes beside the
bindings under the keyword `:context`, which cannot collide with the `?`-symbols a goal
spells.

**The exception, and `unknown` is why.** A goal every literal of which is *computed* rather
than matched — `different`, `evaluate`, `unknown` — names no context anywhere, so there is
no witness to pick, and it is read whole-KB with no witness at all
(`vantage/nothing-to-witness?`). Fanning over readers is **existential** over them, and a
fanned `(unknown X)` is answered by the most ignorant reader in the KB
([why](defenses.md#a-goal-every-literal-of-which-is-computed-names-no-context)). A
**mixed** goal needs no rule and gets none: the monotone literals decide which readers can
answer at all, and the `unknown` is then evaluated at those readers and nowhere else, so
`[(p ?x) (unknown (q ?x))]` reads "a reader that sees p and does not know q", which is what
it should.

**Why they must not leak past the entry point.** All three are `Cx…` CapitalCamelCase, so
`nm/context?` calls them contexts and `sx/variable?` does not. Reaching the engine, one
would be read by every unscoped-path test as an ordinary *concrete* context the taxonomy
has never heard of — up-closure itself alone — and the read would answer **empty** rather
than throw. `CxNothing` is that failure mode turned into the feature: it is a context
nothing can wire, so it sees no fact, inherits no vocabulary, and leaves only what a
prover can compute.

### CxInference: the joint reading

A **variable** context reads "in some context", and it reads it *per literal*. The
conjunctive join substitutes the accumulated bindings into each literal but hands every
conjunct the same wildcard, then merges what comes back — so a fact in `CxA` joins a fact
in `CxB` even when no context sees both, and the context binding is overwritten by
whichever literal the plan ordered last. Projection hides that at `query`, which is why it
has been invisible rather than wrong.

`CxInference` is that reading made joint: an answer survives only if some one reader's
`genlCx` ancestor set covers the whole derivation, and the reader that covered it comes back
**beside** the bindings, under the keyword `:context` (`vantage/witness-key`) — the same
place rows two and three of the table above put it. `CxInference` is a constant and names
no variable, so there is nothing for the witness to bind; write the context as a variable
instead and it unifies into that variable, under whatever name you chose. The witness is
the **most general** such reader (`tax/maximal-contexts`) — the
readers below it see a superset of the same knowledge and add no claim, so reporting all
of them would make the answer count a fact about how finely the KB is divided rather than
about the question.

Two implementations, in `vaelii.impl.vantage`, chosen by `vantage/*strategy*`:

- **`:fan`** (the reference) enumerates the readers and asks each the ordinary scoped
  question. Sound by construction — every answer is one a real vantage really gives — and
  it inherits `except`, retired-spelling and closure scoping for free, since each reader
  runs the path a named context runs. It is the one place a read is **not lazy**: which
  witness is maximal is a property of the whole answer set.
- **`:post-hoc`** asks once, unscoped, carrying what each answer *rested on*, and places
  the result with `maximal-common-descendant-contexts` — the backward twin of what a
  forward firing does. One pass instead of |readers|.

Post-hoc is the one that can be wrong, because an unscoped pass sees the KB with three
filters off and has to put them back by reasoning about the placement rather than the read:
the **`genl` edges a match subsumed through** (a reader that sees the fact but not the edge
does not have the answer), the **exceptions** (`'?ctx` runs where the hidden set is empty,
so an answer can land in the context that `except`s one of its own facts), and the
**retired spellings** (supersession is per reader, so a placement below an equality merge
sees both a fact and its twin). Each was a real divergence from the fan before it was a
line of code.

What post-hoc cannot do is declared rather than guessed. A *computed* answer — a closure
walk, an evaluable, an inferred argument type — names no context to place by, so
`placeable?` asks the registry whether the stored-fact prover is the only one applicable to
each literal, and a rule-expanding read is out by construction (an antecedent fact is not
one of the goals, so its context never reaches a placement). Anything else is handed back
to the fan, which reports that it was.

The strategy is a cost decision that must not change the answer set, exactly as
`res/*hierarchical-retrieval*` is for retrieval, and `query_context_test` compares the two
directly. `:post-hoc` is the default because it is **bounded**, not because it always
wins: the join meters the rows it builds, a run past `lattice contexts ×
vantage/*rows-per-reader*` (20) is abandoned mid-stage, and the fan answers whatever was
abandoned —
[why](defenses.md#post-hoc-placement-is-the-default-because-it-is-bounded).

The readers are the `genlCx` lattice plus any context holding a fact the goal could match.
The second half is not redundant: a context wired by **no** edge is not a node of the
closure, so `tax/contexts` does not list it — while a fact asserted into it is real and
that context is its own (only) reader.

### CxEverything: syntactic, and a named opt-out of belief filtering

`CxEverything` drops both filters: no context scoping and no JTMS read, so it answers what
the store *spells*. It is the cheapest question the engine takes and the only one that can
see a defeated default. It is therefore an explicit opt-out of the fourth invariant, and
an answer taken under it is not a justification — it says a derivation is spelled in the
store, not that the KB holds it.

It drops those two filters and **not** the derived relations: the `genl` / `genlCx`
closures and the equality partition are computed from believed edges either way, so a
subsumption over a *defeated* `genl` edge stays invisible under it. The reading is
"what does the store spell", not "what would the store spell with the TMS switched off".

Two implementation notes that are easy to get wrong and silent when you do. The flag is a
dynamic var, so a plain `binding` around a read entry point would be popped before the lazy seq
realized and the flag would simply not take (`res/blind-seq` re-establishes it per
realization step). And it belongs in **every** cache key on the path, because a blind read
asks the same question at the same wildcard context as an ordinary one and moves no clock
doing it: `matches-visible`'s literal cache and the reach cache under `provers/closure-key`
both hold it, or whichever ran first answers for both — an ordinary read reporting a
defeated default.

## Context placement of justifications

Forward chaining matches antecedent facts across *any* context, then places the
derived sentex in the **maximal** contexts that see the rule and all the matched
facts: `taxonomy/maximal-common-descendant-contexts` = the most-general elements of the
intersection of the facts' + rule's `context-down` closures. This can be several
(incomparable maxima) or none (no common view ⇒ no justification). When no member sees
every other, the maxima are found by walking down the `genlCx` edges from the member with
the smallest down closure, through the contexts that are not common descendants, to the
first that are; the intersection is closed downward, so every maximum is among them, and
the walk never reads the common descendants below them. A universal rule
firing on specific facts lands its conclusion in the specific context. A rule names no
target of its own: an `(ist Ctx S)` consequent is refused
([below](#ist-find-or-create-in-a-context)).

The placement's own sightings are **antecedents of the firing**: the `genlCx` edges the
conclusion's context sees the rule and the facts over join its justification, so
retracting or defeating one withdraws what it licensed rather than leaving it stored in a
context that can no longer see its reasons. The mechanism and its cost are with the rest
of the scoping rules in
[The consumers](#the-consumers-and-what-each-of-them-may-reach) below.

### Enumerating the readers

`taxonomy/meet-closure` is the same primitive asked the other way round: given the
contexts some knowledge is *stated* in, which contexts *read* it — the members
themselves, closed under `maximal-common-descendant-contexts` over their pairs. Two
subsystems need it, and neither can settle for "the contexts holding a fact":

- a qualitative network composes only what one reader can see, so a context inheriting
  two contexts entails what neither entails alone ([qcn.md](qcn.md));
- an equality election runs only over the edges one reader can see, so a fact above a
  merge is restated differently by different readers ([equality.md](equality.md)).

Pairs reach every subset: a common descendant of three is a common descendant of two of
them, hence under a maximal one, hence under a maximal common descendant of *that* and
the third. The closure may therefore hold a context that is maximal for no subset, which
costs a read and cannot cost an answer — a more specific reader sees a superset of the
knowledge, so it either agrees with a more general one or refines it. **Fewer than two
contexts closes immediately**, which is every KB that has not divided the knowledge in
question between contexts: there is nothing for a second to meet.

The starter's owns-parts rule shows both outcomes. The rule `(implies (and (owns ?p
?whole) (partOf ?part ?whole)) (owns ?p ?part))` is a middle theory (`CxMereology`,
seen by every data context below Well), and the test-world cast supplies the facts. It
derives `(owns Tom Roof1)`: both `(owns Tom House1)` and `(partOf Roof1 House1)` sit in
CxSocialWorld, so the intersection is non-empty and the conclusion lands there.
But `(owns Tom Engine1)` is **not** derived — `(owns Tom Car1)` is in CxSocialWorld
while `(partOf Engine1 Car1)` is in CxNaturalWorld (sibling data contexts with no
common view), so the placement intersection is empty and no justification is made.

## except: removing visibility down a context subtree

`(except (sentexHandle H))` asserted in context C removes visibility of the sentex `H`
from C **and every context that sees C** — its `context-down` closure — while leaving
the more general contexts C sees untouched. It is a **meta-sentex**: `(sentexHandle H)`
is the term form of a stored sentex's handle (`sentex/sentex-handle`), so the except
names the sentex it hides rather than restating it. `except` is on the forced-monotonic
roster's engine baseline ([nmtms.md](nmtms.md#the-forced-monotonic-roster)): an except is
never the loser of a nogood and a denial of one is held OUT, so retracting the except is
what restores
the hidden sentex. It rides the ordinary `genlCx` up-closure, visible from exactly the
contexts where it hides its target.

`assert` and `check` refuse an except when no sentex is stored under `H`
(`:unknown-handle`, `checks/check-except-target`). Handles are allocated in assertion
order, so an except asserted before its target would hide whichever sentex next received
that number. Every admitted except names a handle below its own, and the except graph is
acyclic. A target retracted after its except leaves the except naming nothing, and a
handle is never reissued. A store written by import or recovery may still hold a cycle;
the cascade reads an except it meets a second time on one walk as not in force.

**The meta-except cascade.** An except can itself be excepted. `(except H)` hides H;
`(except E)`, where E is that except, takes E out of force and H is visible again;
`(except M)`, where M is the meta-except, takes M out of force and H is hidden again. The
toggle repeats at each depth, and is read at query time off the index
(`exc/exception-status` returns the forest for one handle). A read follows the cascade
from the excepts naming the asked handle, one trie read per except it meets, so the
cascade costs the excepts on that handle and none elsewhere.

The removal is **total**, not just for reads:

- **Reads.** `res/matches-visible` and `sentexes-matching` drop a handle hidden from the
  view context — the believed excepts visible from there, resolved through `context-up`.
- **Derivations.** A rule firing whose antecedent is `H`, or rests on `H` through any
  chain of justifications, and that placed its conclusion in the ancestor set rests on a
  fact that context can no longer see, so the conclusion is **blocked and swept** — the
  derivation-side twin of `exceptWhen`, run through the same block/sweep/revive machinery
  (`chain/justification-excepted?` and `place-conseq` ask per placement). A placed nogood
  is swept the same way. A firing that arrives *after* the except is never placed in the
  ancestor set; a late except sweeps what already fired; and retracting the except
  **re-derives** what it was hiding, in every arrival order. A firing is blocked on the
  excepts alone (`exc/except-closure-hidden-fn`: an except in force names the antecedent or
  a handle every route of it rests on), never on a placed `defeat` (below). The except re-checks the firings over `H`'s consequence closure and re-joins from
  that closure when it leaves (`special/recheck-except`, `special/drain-except-moves!`),
  so its cost is the consequences of `H` and not the extent of the rules they use
  (`lein perf`'s `except-beside-unrelated-firings`). A conclusion placed *above*
  the ancestor set (a context that does not see the except) stays stored and believed
  there. A read from a context that sees the except does not find that conclusion when
  every justification it has rests on a hidden handle (the read walk, `exc/hidden-fn`,
  [nmtms.md](nmtms.md#a-nogood-placed-as-a-conclusion)). An argument-type derivation
  is dropped and drawn again the same way ([argtypes.md](argtypes.md#an-except-of-an-ingredient)).
- **Rules.** `H` may itself be a rule — a firing rests on its rule exactly as it
  rests on its facts (the rule handle is in the stored justification), so excepting a
  rule sweeps its conclusions from the ancestor set, blocks late firings there, and revives
  them when the except is retracted (`special/recheck-except` re-chains a rule
  target on departure). The backward chainers honor the same removal:
  `provers/candidate-rules` drops a rule the asking context cannot see, so `query`
  and `prove` do not rebuild through a hidden rule what forward chaining swept.

**`defeat` beside `except`.** `(defeat (sentexHandle H))` has the same shape and is read
the same way, by target off the trie, and differs in what it removes and when:

| | `except` | `defeat` |
|---|---|---|
| written by | a user's `assert` | the engine alone: a placed nogood for its unique weakest member, a guard below a firing's placement for the firing's conclusion; `assert` refuses it in any literal (`:derived-only`) |
| removes `H` from | visibility at the excepting context and below | belief at the defeat's context and below |
| applied | at read time, and by sweeping the firings resting on `H` placed at or below it | at read time only; it sweeps nothing, and `chain` reads no `defeat` |
| read by a placement | yes: a firing or a nogood is not placed where an except hides an ingredient | no |

Both are applied by one walk over the asked handle's support (`exc/hidden-fn`), and a
meta-except of a `defeat` takes it out of force at the excepting context and below. A
placed nogood's `defeat` rests on the loser it hides, so the walk reads that loser at its
label for the nogood's own placed sentexes (the **exemption**,
[nmtms.md](nmtms.md#a-nogood-placed-as-a-conclusion)); an `except` of the loser, the
winner, a ground or the defeat takes the defeat out of force below the except. A placed
`defeat` and `contradicts` are stored sentexes: `why` names the members and grounds they
rest on, `why-not` of a hidden target names the defeat, and `sentexes-matching` answers
`(defeat ?h)` and `(contradicts ?a ?b)` at the contexts that believe them.

**What the two of them read.** Both are read off the index. The trie keys a positive
`(except (sentexHandle H))` as `[except m sentexHandle H context]`, `m` the handle term's
arity marker, so the level above the context lists the contexts stating an except of H
and each leaf holds their handles (`reads/as-stored-naming`); the `except` predicate
extent lists the contexts stating one (`reads/stores-in?`). A KB that excepts nothing
reads 0 off the trie's `[except]` count, and that is the gate: one count read. A KB that
excepts something pays one membership test per context stating an except of the handle
asked about, plus a `jtms/in?` per except naming it — **belief stays a read**, since an
except can be defeated or revived with no sentex arriving or leaving. `recover` and a
fork rebuild nothing for either.

Callers with particular handles in hand — a firing's two or three antecedents, or matches
arriving one at a time — take `exc/hidden-fn`, a predicate over one view context, rather
than `exc/excepted-handles`, which materializes every handle hidden anywhere in the ancestor set.
The set costs one pass over the reader's excepts however few handles will be asked about;
the predicate costs a lookup per question, and the questions are bounded by the answer set
while the excepts are not. On a chaining run over a KB with 1,000 excepts the difference
is 16× the whole run (`lein bench-hotreads`).

The re-check triggers are the except arriving or leaving (`special/recheck-except`,
keyed on the handle it names rather than a predicate) and a `genlCx` edge change
(`special/recheck-except-ancestors` — a visibility move changes which contexts see the
excepting context, hence what each hides). A `(genlCx sub super)` edge re-checks only the
excepts stated in a context `super` sees, read off the `except` extent, and the
derivations under `sub`: `lein perf`'s `genlcx-edge-beside-excepted-declarations` holds
an edge flat in the excepts it does not move.

## ist: find or create in a context

`ist` — "is true in", the operator from the literature — expresses that S holds in
Ctx. `(ist Ctx S)` is **not** stored as a sentex; given to `assert` (or via
`ist kb Ctx S`) it finds or creates S in context Ctx and returns S's handle
(idempotent).

- `ist kb Ctx S` — find or create S in Ctx.
- `contexts-of kb S` — the contexts S is asserted in.
- `find-sentexes kb S` — any sentex containing S (via the term index).

**ist in a query.** Every read taking a sentence and a context takes `(ist Ctx S)` as its
goal, asking `S` in `Ctx` with the **named context winning over the argument** — the same
resolution `assert` makes, so one form means one thing on both sides of the KB. That is
`sentexes-matching`, `handle-of`, `ask`, `prove`, `query`, `query-plan`, `ask-within`,
`prove-within`, `why-not`'s sentence arity, and the three level diagnostics; `contexts-of`
and `find-sentexes` take no context and ask *which* contexts hold a sentence, so the form
is not a question they have, and `isa?` / `genls` take a context but a **term** rather
than a sentence.

Each entry point answers at its own notion of a context, and the two families differ:
`sentexes-matching` is an exact-context retrieval, so it returns the sentexes stored in
`Ctx`, while the reasoning entry points answer from everything `Ctx` inherits. Both are "in
`Ctx`" — a fact `Ctx` inherits is true in `Ctx` — so the difference is the entry points', not
`ist`'s.

Two shapes are refused rather than answered empty, since a read reporting nothing looks
like a true negative: a wrong arity is `assert`'s own `:shape`, and an `(ist …)` standing
as a **conjunct** of a join is `:not-well-formed`, a join's conjuncts sharing their
bindings and so having no per-literal context. Ask the whole conjunction in `Ctx` instead.

**A rule is refused `ist` in every position.** `(ist Ctx S)` as an antecedent, an
`exceptWhen` query, a NAF body or a consequent is `:not-well-formed`
(`sentex/ist-rule-problem`), and the reason differs by position.

As a read, the literal is indexed and matched under the functor `ist`, which no sentex
carries, so it satisfies nothing — and the way that falls out depends on the frame it
sits in. A positive antecedent is never satisfied and the rule cannot fire; an
`exceptWhen` query never matches, so the conclusion it was written to block stands
believed; an `(unknown (ist …))` is satisfied by that same emptiness, so the rule fires
unconditionally. The middle two are why this is a refusal rather than an inert shape: a
rule that does nothing announces itself, and an exception that blocks nothing does not.

As a consequent, the frame would place the conclusion in `Ctx` instead of the maximal
contexts that see the rule and the facts, whether or not `Ctx` sees either. Three
properties fail with it:

- `Ctx` believes a sentex whose justification rests on handles `Ctx` cannot read. The
  context-scoping property fails on the write side.
- The rule's `exceptWhen` query is evaluated in the placement context, so it runs in
  `Ctx` and misses the facts stated where the rule is. An exception holding beside the
  rule does not block the conclusion.
- The backward chainers read only the rules the asking context sees
  (`res/rule-visible-from?`), so a backward rule with the same consequent answers
  nothing where the forward rule stored an answer. A rule's direction would change what
  the KB believes.

The reading a rule wants is that `S` be **visible** in some context, which is what the
two mechanisms below this section say — `(decontextualized_predicate P)` takes every
`(P ...)` into CxUniverse, which every context below the joint sees, and a `genlCx` edge puts `Ctx` in
another context's ancestor set. Under either the literal is written plainly, and the
`genlCx` topology rather than a per-rule annotation decides what is readable from where.
An `ist` into a context that already sees the rule and the facts adds nothing, because
that context inherits the conclusion from the maximal placement above it.

**Why the query takes what the rule is refused**, since it is one form treated two ways:
the query grants no visibility the context argument did not already grant.
`(sentexes-matching kb S CxA)` has always answered `CxA`'s facts from anywhere, and
`(ist CxA S)` is a spelling of it — the caller asking about `CxA` has said so. A rule is
the other case: nobody asked, the rule's own context may not see `Ctx`, and what comes
back decides *belief* rather than answering one caller. `context_scoping_test` pins the
query half and `check_test` pins the refusal.

**The predicate meta-ontology** is a worked example. Predicates are reified as
individuals under `predicate` (itself a `thing`): `unary_predicate` (types and
one-place properties), `binary_predicate`, `ternary_predicate`, and the algebraic
subtypes of `binary_predicate` — `symmetric` / `asymmetric` / `transitive` /
`reflexive` / `functional`. The algebraic marks **are** the classification: each is one
predicate that maintains its property *and*, through `(genl symmetric binary_predicate)`,
is a membership, so a `(symmetric siblingOf)` declaration makes `isa? siblingOf symmetric`
and `isa? siblingOf binary_predicate` hold — exactly as `isa? dog unary_predicate` does for
a type. The two families scope **oppositely**, on purpose: the **arity** memberships are
derived by CxCore rules that name no context, so they place where the declaration was made
(a predicate declared binary in one theory is binary *there*, not KB-wide — see "The
consumers" below), while the algebraic marks are `decontextualized_predicate`s, lifted into
CxUniverse and seen by every data context. A predicate's algebra is a claim about the
predicate itself and belongs to the whole KB; its arity, read off whatever theory declared
it, stays with that theory.

## decontextualized_predicate: a fact that belongs to the KB, not to one theory

`(decontextualized_predicate P)` takes every `(P ...)` out of the context it was stated
in. Each one — asserted, or concluded by a rule — is additionally **deduced into
CxUniverse**, supported by the placement sentex *and* the
`(decontextualized_predicate P)` sentex. Since every context below the joint sees CxUniverse,
the fact becomes visible everywhere, even from a *sibling* context that cannot see
where it was stated. Retracting or defeating either the original or the declaration
withdraws the copy through the JTMS, and declaring it retroactively lifts the `(P ...)`
facts already present. A declaration that revives lifts the facts stored while it was
OUT, which its arrival could not reach (`special/revived-declaration-sweeps`, run by the
settle for every revived datum).

The mechanism is documented in the KB by the `comment` on `decontextualized_predicate` in
`CxCore.txt`. It is implemented in code rather than as a rule, because a rule stating it
would match every fact in the store and would name its target with an `ist` consequent,
which a rule is refused. The declaration is ordinary predicate metadata, read back with
`(has-prop? kb :decontextualized pred)`.

**The mark itself is read globally, not through the asserting fact's ancestor set.** A
`(decontextualized_predicate P)` stated *anywhere* lifts every `(P ...)` in the KB,
including facts stated in contexts that cannot see the declaration. That is
deliberate (`special/deduce-lifts` says so at the read): the lift decides the
*storage* context, and gating it on what could see the declaration would be circular
— the whole point of the copy is to make the fact visible to readers the stating
context knows nothing about. What it costs is stated here rather than hidden: a
declaration in one theory publishes a sibling theory's `(P ...)` extent KB-wide, so
the mark belongs in a schema context, not a contingent one.

### Why CxUniverse, and not a target the declaration names

A lift into a context the declaration picks out is the obvious generalization, and it
is unsound. The definitional checks — disjointness, functionality, `arg` — are
**context-scoped**: they run where the fact is stated, against what is visible from
there. Lifting into a context the stating context cannot see moves the fact somewhere
those checks never looked, and two facts that are each admissible where they were
stated meet in the target as a violation nothing reports:

```clojure
(disjoint dog mouse)
(dog Rex)   @CxA   →  copy in CxT      ; fine in A — B is invisible from A
(mouse Rex) @CxB   →  copy in CxT      ; fine in B — A is invisible from B
;; CxT now believes Rex is both, and no check ever considered the pair
```

CxUniverse is the target that closes this, because every context that lifts sees it:
the middle spindle and the data contexts below the joint all reach CxUniverse, so the
first copy is visible to the *next* assert, and the settle weighs the clash where the
second assert is made. The upper
spindle sits above the joint and reaches CxCore instead, which is why a declaration
written in CxCore constrains every context in the tree. That is not a lucky property of a well-known context — it is the
whole reason the target is fixed.

The residual case is a context wired outside the spindle, which sees neither its
siblings nor CxUniverse. There the stating context could not have run the check
either, so the lift runs it on the copy itself (`unchecked-target?` — one `sees?` per
lift, and only that case pays anything more). A sweep over stored facts, the one a
declaration arriving last runs and the one `recover` runs, asks `sees?` once per stating
context. The copy is asked what a rule's
conclusion is asked (`checks/derivation-violation`): a clash with a believed member is
stored and placed as a nogood, and only an inadmissible copy, an argument
conviction or a malformed form, is dropped, recording a `violations` entry that names
the context it was lifted from.

### The lift is about the predicate, so derived content is lifted too

The declaration runs at **both** points new content is stored: `assert`, and forward
chaining's `place-conclusion`. A rule concluding `(P ...)` gets its conclusion lifted
exactly as a caller asserting `(P ...)` does, because the declaration is a claim about
the *predicate*, not about how a particular sentence arrived.

That is not a convenience — lifting only asserted content makes belief depend on
arrival order, which [nmtms.md](nmtms.md) forbids. Declare, then let a rule conclude
`(P a)`: the conclusion stays where it was concluded. Let the rule conclude first and
declare afterwards: the retroactive sweep lifts it. Same three sentences, two different
answers. The engine's own invariant decides the question, and it decides it in favour
of lifting.

Each copy is a **new datum in a context that did not have it**, so it goes on the
chaining agenda and reaches the derivation-path choke point like any rule conclusion:
its arrival re-triggers any `exceptWhen` stated over that predicate, and rules keyed on
the predicate fire on the copy as well as on the original.

That second firing is the point, and it is about **placement**, not about what a rule
can see — forward chaining already matches antecedents across every context. Firing on
the original places the conclusion in the source context; firing on the copy places
it in CxUniverse. So a consequence of a decontextualized fact is decontextualized
in turn, which is what you want (if `(edgeTo A B)` holds everywhere, so does what a
universal rule concludes from it) and what it costs: **two stored sentexes for one
conclusion**, and the rule fires twice.

The fixpoint still terminates for the ordinary reason — re-deriving a sentence already
stored adds a justification, not a handle, so the agenda drains — and each copy carries
`1 + max` antecedent depth, so the `:max-depth` guard bounds a chain of lifts exactly as
it bounds a chain of rules.

**A copy merges what it licenses, as any new content does.** A `functional` or
`anti_symmetric` mark derives its equalities where the mark is visible, and the copy is
what makes it visible from CxUniverse, so the copy runs the same four merges the assert
entry point and `chain/place-fact-conclusion` run for what they store
(`special/copy-merges`). Without them the merge followed arrival order: a mark stated in a
theory before the facts merged them at CxUniverse, and the same mark stated after them
merged below that theory alone. `relation_properties_test`'s
`a-merge-mark-in-a-sibling-merges-from-every-context-in-either-order` pins both orders.

Two boundaries, both deliberate:

- **A negative fact is not lifted.** `(not (P a))` has functor `not`, so a declaration
  about `P` does not reach it. The positive extent becomes universal and the negative
  one stays in its context.
- **Declaring is O(extent).** The retroactive sweep creates one copy per stored
  `(P ...)` inside a single synchronous `assert` — measured at ~0.09 ms a fact, flat, so
  a predicate with a large extent is a long assert. Declare before loading where you
  can.

### What the shipped ontology declares it of

Every shipped declaration is a claim about a **predicate** rather than about a world.
`functional`, `functionalInArg`, `inverse`, `reflexive`, `irreflexive`, `symmetric`, `commutative`,
`commutativeInArgs`, `commutativeInArgAndRest`, `anti_symmetric`, `asymmetric`,
`transitive`, `anti_transitive`, `equivalence_relation`, `injection`, `surjection` and
`bijection` carry the mark — so a `(symmetric P)` stated in one theory is the KB's
claim about `P` and not that theory's — and `genlCx` carries the forced variant below.
**No domain relation carries either**, and two things hold that line:

- **A domain fact is what a theory is for.** A marriage, an ownership, a location holds
  in the context that states it, and a story, a jurisdiction or a hypothesis is entitled
  to state one the rest of the KB does not share. A mark on `marriedTo` makes every
  fiction's marriage a claim of the whole KB.
- **The mark travels down the rules.** A conclusion drawn from a lifted copy is lifted
  in turn (above), so a mark on one predicate reaches whatever the rules over it
  conclude: `CxSocial`'s `(implies (and (marriedTo ?x ?y)) (knows ?x ?y))` would put
  `knows` within reach of every data context without `knows` being declared anything.

`abducible_predicate` is the near-miss on the other side, and is scoped for the
converse reason: willingness to assume a `(P …)` is a policy of the context that grants
it rather than a property of `P` ([abduction.md](abduction.md)).

### Where a relation property is read from

A relation property is read where a sentex declaring it is visible, which is the rule
every definitional read follows (`has-prop?` with a context, the provers, the checks, the
supporter a firing names). The shipped ontology makes every one of them visible from
every context by declaring it a `decontextualized_predicate`, and that is the reading the
engine holds to: a relation's algebra is a claim about the relation and not about a
subject matter. Two theories that disagree about whether `partOf` composes are not
something a mark can represent, since canonicalization, the property tables and the
definitional checks all key on the predicate; such a KB states the closure as a rule in
the theory that holds it, or uses two predicates. Whichever path reads a property, it
answers from the same sentexes, and neither answer depends on whether the declaration
arrived before the facts it governs or after them.

**The four permuting marks are lifted by the engine itself.** `symmetric`, `commutative`,
`commutativeInArgs` and `commutativeInArgAndRest` decide the order a `(P …)` sentex's
arguments are stored in, and the store sorts a fact by a mark stated in any context
(`res/kb-sentex`) from the moment one is stated anywhere. A `defeat` or an `except` of
every statement takes the mark away from the readers that see it, which read the fact as
written ([canonicalization.md](canonicalization.md#a-mark-a-reader-does-not-believe)). Every
other reader reads it where its sentex is visible, so a KB with no lift answered the
mirror of a fact from a sibling through the store and denied it through `has-prop?`, the
symmetric prover and the supporter a mirrored firing names. `special/deduce-lifts`
therefore deduces a permuting mark into CxUniverse whether or not the KB declares the lift,
resting the copy on the statement alone. On a KB carrying CxCore, which declares it, the
copy is the same copy. A context that sees neither a statement nor the copy reads the
four as the store does ([A context outside the spindle](#a-context-outside-the-spindle)).

**A KB without CxCore holds the other twelve where they are stated.** Nothing lifts
them, so every reader reads `(transitive R)` stated in `CxA` from `CxA` and below, alike.
`inherit_test`'s `the-transitivity-licence-is-read-from-the-asking-context` pins that half,
and `a-permuting-mark-is-read-from-every-context-on-this-kb-too` beside it pins the four
permuting marks. Such a KB still holds the forced-monotonic roster's engine baseline, so a
`genlCx` edge, a `functional` or `irreflexive` mark, a definitional declaration, an arity
binding, an `except` or an equality stated `:default` is never a loser and a denial of
one is held OUT, as under CxCore ([nmtms.md](nmtms.md#the-forced-monotonic-roster)).

Measured on a lattice of two siblings `CxA` and `CxB` under CxUniverse and `CxD` below
both, with the mark stated in `CxA` and the facts it governs in CxUniverse, each in both
arrival orders:

| mark | read from, with CxCore | read from, without | what reads it |
|---|---|---|---|
| `symmetric` | every context | every context | the stored key, and `:props :symmetric` |
| `commutative` | every context | every context | the `:commuting` table, and `:props :commutative` |
| `commutativeInArgs` | every context | every context | the `:commuting` table |
| `commutativeInArgAndRest` | every context | every context | the `:commuting` table |
| `transitive` | every context | `CxA`, `CxD` | `:props :transitive` — the closure prover, `usable-relation?` |
| `reflexive` | every context | `CxA`, `CxD` | `:props :reflexive` — the reflexive prover |
| `irreflexive` | every context | `CxA`, `CxD` | the mark's supporters and their contexts — the placed nogood's ground |
| `asymmetric` | every context | `CxA`, `CxD` | `:props :asymmetric` — the refusal and the settle's nogood |
| `anti_symmetric` | every context | `CxA`, `CxD` | `:props :anti-symmetric` — the merge, placed where the mark is visible |
| `anti_transitive` | every context | `CxA`, `CxD` | `:props :anti-transitive` — the refusal and the settle's nogood |
| `inverse` | every context | `CxA`, `CxD` | the `:inverse` table — the inverse prover |
| `functional` | every context | `CxA`, `CxD` | `:props :functional` — the merge, placed where the mark is visible |
| `injection` `surjection` `bijection` | every context | nowhere | CxCore rules deriving `functional` and `functionalInArg`; inert without them |
| `functionalInArg` | every context | `CxA`, `CxD` | the `:functional-in-arg` table — the merge, placed where the mark is visible |

Each table entry records its supporting sentexes with their contexts
([taxonomy.md](taxonomy.md#reads-are-scoped-by-the-asking-context)): the statement in `CxA`
and, where the mark is lifted, the copy in CxUniverse, which is what every reader outside
`CxA`'s descendants answers from.

### A context outside the spindle

A context no `genlCx` edge names sees nothing but itself: not CxUniverse, and not CxCore.
The lattice has no implicit root. A reader of such a context reads what was stated there,
which is what an agent context's independence rests on
([belief.md](belief.md#independence-and-inheriting-base)), and an edge is how a KB puts the
context under the spindle. The contexts above the joint, CxCore and the upper spindle's
members, do not see CxUniverse either, so they read a lifted copy no more than an
unwired context does.

For the twelve marks lifted by declaration, "every context" in the table above therefore
means every context that sees CxUniverse. A context that does not:

- reads a mark only from a statement it sees, its own included. `(functional R)` stated in
  it merges its facts there, and one stated in a sibling does not.
- has its own statements lifted like any other context's, so every context that sees
  CxUniverse reads a mark stated in it.
- runs no definitional check whose declaration it cannot see. It sees none of CxCore's
  argument declarations, so it admits what a context under CxCore refuses, and a lift out
  of it runs the check on the copy (`unchecked-target?`, above).
- gets no CxCore rule firing over its facts, since no context sees both the rule and the
  fact. Each such firing files a `:no-placement` entry.

The four permuting marks are the exception, because of the stored key. The store sorts a
fact by a mark stated in any context, so a fact stated in such a context is sorted by a mark stated
anywhere, and its reader answers the fact's mirror. Every other reader of the property
reads it where the store does:

- `has-prop?` answers `:symmetric` and `:commutative` from any context as whether that
  context believes a statement, every statement read as visible from it (`tax/has-prop?`),
  and the symmetric prover reads the property through it.
- A forward firing that read a fact through its mirror names the mark statement, so
  retracting the mark withdraws the firing, and is placed by the rule and the facts it
  matched alone (`chain/placement-antecedents`). Were the statement's context to
  constrain the placement as well, a context that sees no statement would lose the firing
  to a `:no-placement` when the mark arrives first, and keep the firing it made before the
  mark when the mark arrives last. The statement named is the CxUniverse copy where it is
  believed, since it stands while any statement does.

The mark asked as a sentence, `(ask? kb '(symmetric R) Ctx)`, is answered where a
statement is visible, as any sentence is.

`relation_properties_test`'s
`a-merge-mark-reaches-a-context-with-no-edge-only-from-its-own-statement` pins the twelve,
`inherit_test`'s `a-permuting-mark-is-read-from-a-context-with-no-edge` pins the property
reads, and `order_independence_test`'s
`a-firing-a-mark-no-statement-of-reaches-is-placed-in-every-order` pins the firing, in an
unwired context and in one above the joint.

## forced_decontextualized_predicate: a canonical home in CxUniverse

`(forced_decontextualized_predicate P)` is the stronger variant. Instead of leaving the
original where it was asserted and deducing a copy, it **forces the storage context
of every `(P ...)` to CxUniverse** on assert — no separate justification, the fact's
extent simply lives there. `genlCx` is declared this way (the vocabulary head asserts
`(forced_decontextualized_predicate genlCx)` before any `genlCx` edge), so the whole context
topology has one canonical home rather than being scattered across the contexts each
edge was asserted in.

**A declaration arriving after its facts moves them.** Each `(P …)` premise stored outside
CxUniverse is asserted there at its own strength and the original retracted
(`core/rehome-forced-extent!`), so the KB is the one the other order builds. A text load
puts the context topology first (`text/load-entries!`), which puts every `genlCx` edge
ahead of the declaration; the move is what keeps those edges out of the contexts they were
written in, and out of the `(context …)` entailments a fact there draws.

Both are wff-checked at assert time, like the other special predicates:
`decontextualized_predicate` routes through the same `prop-problems` check as
`transitive` / `symmetric` / `functional`, since it is a one-argument mark on a
predicate like they are.

## Context-scoped constraint checks

`arg` arg checks and disjointness checks are **not global**: when asserting in
context K they consider only constraints and type memberships *visible from* K
(its `context-up` closure). So shared vocabulary must live in a context K sees — in the
starter, the CxCore vocabulary and the upper definitional contexts sit at the top
of the spindle (every data context reaches them through the axis), so their `arg`
constraints, comments, and type memberships are visible everywhere.

The `genl` closure reads are scoped the same way (docs/taxonomy.md): `genls` /
`specs` / `genl?` / `disjoint?` take a context, and a read asked from K walks only
the edges some believed supporter asserts from K's ancestor set.  The **`genlCx`
closure itself stays global, as a stated exception** — visibility scoped by
visibility would be circular, `forced_decontextualized_predicate` already forces
every `genlCx` edge universal, and the scoped reads' interning is keyed on
that closure being context-independent.  A clash no single writer could see —
admissible where each half was stated, jointly visible from some descendant — is
**weighed** at that descendant, never by refusing a writer on grounds it cannot see.

`settle` runs each candidate's definitional question from its own context *and* from the
maximal common descendant of that context and each context holding a sentex it could
pair with — and, where a separation or a mark is visible only below that maximum, from
the context where it comes into view. That chooses the asker rather than widening what
an asker sees — a vantage already sees both halves and what separates them — and it is
what stops the same three sentences from landing on
a defeat or on two coexisting claims according to which half was written last
([nmtms.md](nmtms.md)). The defeat a vantage lands is scoped to that vantage and below, so a context
reading one half alone keeps what it holds.

A separation derivable only from a context below the maximal common descendant is
decided at the most general context that reads it: CxW sees `(t1 Pip)` in CxA and `(t2
Pip)` in CxB, CxV sees CxW and the `(disjoint t1 t2)` in CxDecl, so CxV and the contexts
below it believe one membership while CxW keeps both
([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)), and `exposed-clashes` names
every such pair with the contexts that see it whole.

**The pass asks its question of the scoped read, not of an enumeration.** For a
candidate pair of held memberships it must answer "does any context see both of these
*and* a complete derivation of their disjointness". Read forwards, that is a search
over derivations — one witness per ancestor path per separated pair per supporter
choice, which is exponential in a multiply-inheriting hierarchy, and a pair that turns
out *not* to be jointly visible exhausts every one of them to find out. Read
backwards it is a property of a context: `disjoint? t1 t2 K` scoped to K walks only
edges visible from K, so it is true exactly when K sees some whole derivation. So the
pass asks `∃K ∈ common-descendants(c1, c2)` off the cached closures, and enumerates a
witness only for the *report* — where one is now known to exist, so the search stops
at it rather than running out. The two directions decide the same question, and the
gate is what keeps the sweep bounded on a large ontology.

Both answers are memoized per pass on the pair `[t1 c1 t2 c2]`, which is what they
are functions of — the term appears in the reported message and nowhere else — so a
corpus where thousands of individuals hold the same two types in the same two
contexts asks once.

## The consumers, and what each of them may reach

Scoping the closure reads is half the job; the other half is every place the engine
reaches for an edge, a rule, an equality, or a metadata mark *on some context's
behalf*. `context_scoping_test` is the standing guard, one pair of tests per mechanism
— the leak and its control, since a scoping test that only checks the negative passes
just as well when the feature is broken outright.

- **A forward firing rests on three ingredients, not two** — the rule, the antecedent
  facts, and the `genl` edges the match subsumed through — and **one rule governs all
  three**: the conclusion is placed in the maximal contexts that see every one of them,
  and it **names every one of them in its justification**. A rule on `(parentOf ?x ?y)`
  matched by a stored `(fatherOf Tom Bob)` is using `(genl fatherOf parentOf)`, so
  `chain/placement-ingredients` asks `taxonomy/reach-support` for a *witness* path from
  the fact's functor up to the antecedent's, and feeds its supporters' asserting
  contexts to `maximal-common-descendant-contexts` beside the rule's and the facts'.
  Every placement that comes back sees every named edge by construction — the scoping
  guarantee is structural rather than a filter — and the witness joins the antecedent
  list, so the conclusion goes when the edge does. Both halves are required: a
  placement decided by re-deriving reachability that the justification does not then
  record leaves the conclusion standing on nothing once the edge is retracted. The
  join itself stays global (which facts exist is not
  placement's question), and the links are collected only for a matched fact whose
  functor is not the functor of the antecedent it satisfied, so an ordinary firing pays
  a `not=`.

  The witness is chosen to **constrain the placement least**, which is what makes this a
  widening of the two-ingredient rule rather than a different one. Where a maximal
  context seeing the rule and the facts can also see a path, the edges add no constraint
  and the placement is unchanged — asked per candidate, since two incomparable
  candidates may see different supporters of one edge and a single global witness would
  drop whichever cannot see it. Only where a candidate sees no path is the taxonomy
  binding, and the conclusion **descends** to the maximal contexts that see the edges
  too. A rule and a fact in one context, over a hierarchy stated in a sibling, therefore
  conclude in the contexts below both instead of concluding nowhere.

  The descent places the conclusion once per route that no other route **covers**
  (`chain/descent-placements`, `taxonomy/reach-supports`). A route covers another when
  its weakest supporter is at least as strong and each of its asserting contexts is seen
  from one of the other's. Of two routes stated in sibling contexts neither covers
  the other, so each places the conclusion below its own context, and a candidate that sees
  a path of its own keeps its placement beside the descent's:

  ```
  CxUniverse   (dog Fido)   forward rule (animal ?x) ⇒ (alive ?x)
   ├─ CxA      (genl dog mammal) (genl mammal animal)
   ├─ CxB      (genl dog animal)
   └─ CxD      sees CxA and CxB
  ```

  CxUniverse sees no path, so the conclusion descends; the CxA route places
  `(alive Fido)` in CxA and the CxB route places it in CxB, and CxD reads both. A descent
  over one route would place it in CxB alone, the shorter path, and CxA would read it
  only in the orders where the rule fired over the CxA route before the CxB edge
  arrived. `second_route_test` builds this shape in every order. A drop is a
  `:no-placement` entry naming the
  subsumption and the contexts that would have taken it but for the edges, since "your
  context cannot see that edge" is a different thing to fix from "your facts are in
  sibling contexts".

  Which fact satisfied which antecedent is not recoverable from the justification's
  handle list — the join runs in cost order — so `chain/join-antecedent` records the
  pairing as it matches (`:matched`), and `subsumption-links` reads the links off that.

  **The sightings that decided the placement are named too, and by the same rule.**
  "Sees the rule and the facts" is a `genlCx` reachability, supported by ordinary
  sentexes somebody asserted and can take back, so `chain/visibility-support` asks
  `taxonomy/reach-support` of the *context* closure — one path from the placement up to
  each ingredient context, one supporter per edge — and those handles join the
  antecedent list beside the `genl` ones. Naming the contexts and not the edges reaching
  them would leave a conclusion stored and believed where nothing it rests on can be
  seen, and a KB built without the edge derives nothing at all, so belief would depend on
  which of the two the caller did. Retracting or defeating such an edge withdraws what it
  licensed, through the ordinary dependency-directed path and with no removal machinery
  of its own. The ingredient contexts are the rule's and the facts' — and the
  named `genl` supporters', since seeing an edge is a sighting like any other. **The
  ordinary firing pays one
  `=` per ingredient and reads nothing**: a rule and its facts in the placement's own
  context reach it reflexively, and a reflexive reach rests on nothing. `genlCx` is a
  `forced_decontextualized_predicate`, so an edge has exactly one supporter and the
  per-edge choice between supporters that `genl` makes does not arise here.
  `placement_context_witness_test` is the standing guard.

  The witness is **one path, one supporter per edge**, chosen by content — the walk
  expands neighbours in name order, and per edge it takes the *most general* supporter
  available (the one every other supporter's context sees), since a needlessly specific
  choice would drag the conclusion down with it. Nothing about it depends on the order
  the hierarchy was built in. A second route — the same edge asserted from a second
  context, or a second path around it — does not carry a second justification, because
  that would be one justification per path through a hierarchy where paths multiply. It
  costs a **re-derivation** instead: the same bargain the qualitative support makes
  (docs/qcn.md), and the same one `exceptWhen` revival makes. Across *paths* the witness
  is the shortest one, and the placement is asked per candidate, so a route no candidate
  sees is the only case where the edges bind at all, and there the descent names every
  route no other covers, as above. The witness a `transitiveInArg` claim names is chosen
  the other way, by the contexts it was stated in rather than by length, because that
  path decides the placement on its own ([inherit.md](inherit.md)).

  The same edge has to work in both time directions. Arriving **after** the facts, it
  makes them matchable at a supertype they did not have, and the semi-naive agenda
  never sees that (the arriving datum is the edge); `special/subsumption-seeds` puts
  the sub's spec subtree back on the agenda — the taxonomy twin of the retroactive
  `decontextualized_predicate` lift, and free on the ordinary load order, where a
  hierarchy arrives before the facts under it. **Leaving**, it withdraws what it
  licensed through the ordinary dependency-directed sweep, and
  `special/resubsumption-seeds` puts the same subtree back when the reachability
  outlives the supporter that went — so the surviving route re-derives, at a fresh
  handle. `subsumption_support_test` is the standing guard for all of it.

  **A `genlCx` edge owes the same debt through the other closure**, and
  `special/visibility-seeds` is the twin that pays it. Matching fans an antecedent up the
  *visibility* ancestor set, so an edge arriving after both the rule and the facts changes which
  facts the rule can see — and again the arriving datum is the edge, so firing the rules
  keyed on `genlCx` is not the same thing as re-joining the rules the edge just gave
  a wider view.

  **The seed set is what the lower contexts see, not the edge's two ends.** The edge grows
  the view of every context `X` below `sub` by `super`'s ancestor set, `up`. A pairing it
  makes new takes one ingredient from that growth and the other from anywhere in `X`'s
  view, and that view holds more than the edge's endpoints: `sub`'s other ancestors, and
  in a diamond the ancestors of `X`'s other parents. So the second set, `seen`, is the
  union of the ancestor sets of every context in `sub`'s descendant set, less `up` — the
  contexts some lower context sees that `super` does not. A pair both inside `up` met at
  `super` before the edge, and a pair both inside `seen` met at the context that sees
  both. The `up` half narrows once more, to `fresh`: the contexts of `up` that `sub` did
  not already see through its other parents (`taxonomy/context-up-besides`), since every
  lower context saw the rest before the edge. The old ancestor set is read the way
  placement reads it: the walk does not cross an edge with a stored negation, which the
  taxonomy's closure does not apply. So a new pairing has an ingredient in `fresh`, or the lower context saw all of
  it, and one in `seen`, or `super` saw all of it, and its rule sits in one of three
  places: in `seen`, with a fact in `fresh`; in `fresh`, with a fact in `seen` — a rule
  stated *above* inherited into the context newly wired under it, placing its conclusion
  there; or in the rest of `up`, which every lower context saw before, with a fact on each
  side — a two-antecedent rule above both parents of a diamond, whose two facts only the
  context below both sees together. Seeding is by fact, so the seeds are the believed
  sentexes of the sets a pairing needs a fact from. The equality twins read the same
  union for the same trigger (`special/context-edge-reader-ancestors`).

  **A `genl` edge is an ingredient too.** A match through a subtype reads the `genl`
  edges on a route from the fact's type to the antecedent's, and a route edge stated on
  the other side of the new edge from both the rule and the fact makes a pairing new that
  the three placements above do not name: `(dog Rex)` and a rule on `(animal ?x)` in
  `CxHigh`, `(genl dog animal)` in `CxLow`, and `(genlCx CxLow CxHigh)` last. An edge
  stated in `seen` meets the facts of `up` as it would on arriving there. An edge stated
  in `fresh` meets the facts of `seen`, which are seeded whatever rule `fresh` states,
  and, when `seen` states a rule, the facts of the rest of `up`. Each half runs only when
  its side states a `genl` edge or a cover (`taxonomy/supporter-count-in`, one census read
  per context).

  **The `seen` half reads the cheaper of two sides** (`special/under-seen-edges`). A
  context wired under a new parent usually already sees `CxCore`, so `seen` holds the
  whole ontology's edges while `up` holds a handful of facts. When the facts of `up`
  under the roster's fan cost no more postings than `seen` states edges, those facts are
  the seeds; otherwise each edge `seen` states seeds the facts of `up` under it, with the
  functors `subsumption-seeds` reads. The cost is the smaller of the edges `seen` states
  and the rule-relevant postings of `up`, and `perf`'s `genlcx-edge-under-a-seen-taxonomy`
  holds it flat in the edges `seen` states.

  **It is enumerated from the rules, and each half is gated on where a rule is stated.**
  Both are about cost, and the cost is asymptotic rather than constant. Walking the ancestor set
  and keeping the facts a rule could match is a record fetch per sentex *in the ancestor set*, so
  wiring N contexts under a `CxUniverse` holding K facts is O(N·K) against
  O(N+K) without it, and a spindle D deep is O(D²) because each edge's ancestor set is the
  whole chain above. Measured: 3.9x on the first shape, 5x and climbing with depth on the
  second, and 1.8x on the starter load. Two reads of the rule index turn it around: the
  antecedent keys some stored rule takes (`reads/as-stored-rule-keys`), and the contexts
  a rule is stated in (the rule extent, `reads/stores-rule-in?`): walk those predicates' extents and keep what
  falls in the sets to seed, or walk those sets' own contents when they hold fewer
  postings (`special/seeds-in`). `fresh` is seeded when a rule is stated in `seen`, and
  `seen` when one is stated in `fresh`; when neither holds but a rule is stated in the
  rest of `up`, a pairing it makes has a fact on each side and seeding either finds the
  other, so the side holding fewer sentexes is seeded. Wiring an *empty* context under a
  full one is the commonest edge there is and seeds nothing, since `seen` is the new
  context alone and holds nothing, where the ungated version re-seeded the whole ontology
  above it and re-joined rules that had already fired on every fact of it. Measured on the starter
  load against the same load with no visibility seeding: 4.7x ungated, 1.03–1.04x with
  both gates over `fresh` and `seen`. A gate over `up` in place of `fresh` measured 2.5x,
  because a context already under `CxCore` re-seeds its second parent's facts for the
  rules stated in `CxCore`.

  **Each roster predicate's extent is read fanned by `genl`**, the way the matcher fans
  it (`special/roster-antecedent-functors`): down the spec closure for a positive
  antecedent, and up the genl closure for a negated one, since a negation reverses the
  fan. Reading the antecedent's own functor alone finds the facts a rule *names* and not
  the facts it *matches*, so the edge re-joins the rule over half of what it newly sees,
  and one type standing between the rule and the fact is enough to leave the conclusion
  in the orders that wired the contexts first and nowhere else. A predicate outside the
  hierarchy closes to itself, so the fan costs a KB with no type hierarchy under its rule
  antecedents nothing.

  **The extents read include the functors that move what an antecedent answers without
  being on it** (`special/licensing-functors`), one per re-join family of
  `chain/fire-rules-for`: the predicates a `SupportingProver` reads, a registered
  calculus's constraint predicates, a `(transitive P)` declaration and the inverse
  partners a walk takes hops from, and the declarations and relation a preservation reads
  ([inherit.md](inherit.md)). A unit table decides whether `(quantityGreaterThan ?q
  (QuantityFn 1 Kilogram))` holds of a mass in grams, and no rule names
  `conversionFactor`, so an edge that shows a lower context the table pairs it with a rule
  and a fact that met before the edge; two `nonTangentialProperPart` facts composed below
  the edge entail a `partOfRegion` no one stated. A seeded datum of such a functor queues
  the re-join its arrival would have. The permuting marks are not among them: the engine
  lifts each into `CxUniverse`, where every reader sees it before any edge does.

  **Withdrawal needs no twin of it**: dropping an edge *narrows* what a rule sees, and a
  firing names the edges its placement was seen over, so the dependency-directed sweep
  already collects a conclusion whose antecedent stopped being visible. Revival is the
  half that does, and it is the same function read the other way —
  `special/resubsumption-seeds` puts a removed `genlCx` edge's `up` and `seen` back on the
  agenda beside a removed `genl` edge's spec subtree, because a sighting can outlive the
  edge that witnessed it when the contexts are wired together a second way.

  **That pass has one condition, and the rule gate above is not it.** It runs only where
  the sweep collected more than the record asked for: a justification naming the departing
  edge is deleted with it, so a conclusion that survived kept a second justification and
  needs nothing, while one that did not is in the swept set. Retracting an edge that
  licensed nothing — the common case — is therefore one functor read per removed record
  and no chaining at all. The edge's own argument-type mint does not count as more: its
  justification takes the edge as the fact typed, not as a route
  (`special/edge-own-mints`), so `(genlCx CxA CxUniverse)` with `(arg genlCx 1 context)`
  in view retracts without re-joining CxUniverse's ancestor set. Where it does run the re-join is **unconditional**, and
  `visibility-seeds` is called in the **ungated** arity it keeps for this caller: the
  rule-holding gate two paragraphs up is skipped on purpose, not inherited. That gate is
  sound for an *arriving* edge because an arriving edge is the only new reachability there
  is — nothing can newly match except through it, so a new pairing has an ingredient in
  `fresh` and one in `seen`, and its rule is stated in `seen`, `fresh` or the rest of
  `up`.
  The ungated arity seeds all of `up` beside `seen`. A
  departing edge says nothing of the kind. Whether a surviving route still licenses the
  firing being revived is `place-conseq`'s question, answered from the taxonomy as it
  stands after the removal, and a gate here would guess that answer from the departing
  edge's two sets alone.

  So most of the re-join finds nothing to place, and that pass files no `:no-placement`
  (`chain/*report-no-placement?*`): a firing the caller's own retraction just killed is
  the retraction restated, and one ledger entry per killed firing would cost the ledger
  its real ones, which cap at 1000.

- **A rule is a sentex**, so a context backward-chains with the rules it inherits and
  no others (`res/rule-visible-from?`, shared by every caller of
  `provers/candidate-rules`). Without it the two chainers disagree about one KB: the
  forward firing of a sibling's rule correctly evaporates for want of a placement while
  a backward search answers from it.

- **An equality applies where it is visible on the question as well as on the answer.**
  Migration and supersession check per sentex; the *goal* rewrite has to check too, or
  an invisible `(rewriteOf Superman Clark)` renames a context's question to a
  spelling that exists nowhere and it loses a fact it still believes, under either
  name. `kb/rewrite-goal` takes the context, `different` reads the scoped partition
  (the unique-name assumption is what a context holds until *it* is told
  otherwise), and the public reads take the context too (docs/taxonomy.md).

- **`transitiveInArg` walks the edges the asker can see** — `inherit/witness-terms`
  scopes its `genl` walk as it already scoped its `fact-reach`, and re-reads the
  relation's transitivity from the same vantage.

- **The predicate arity meta-ontology concludes where it was declared.** The arity
  rules in `kb/CxCore.txt` place by the ordinary rule and name no context, so an
  `(arity myRel 2)` stated in a context concludes `(binary_predicate myRel)` *there*.
  **Do not name CxCore in them.** Doing so publishes the conclusion: `isa?` would answer
  from a context that cannot see the declaration, while `has-prop?`, asked of the same
  declaration from the same context, answers false. (The *algebraic* marks — `symmetric`,
  `transitive`, … — go the other way on purpose: they are `decontextualized_predicate`s,
  so a declaration is lifted to CxUniverse and read KB-wide.)

A rule cannot choose its own target: an `(ist Ctx S)` consequent is refused
([ist](#ist-find-or-create-in-a-context)), so every forward conclusion is placed by the
rule above. `forced_decontextualized_predicate` is the one way a sentence's storage
context is fixed, and it fixes that context per predicate, for every writer.
