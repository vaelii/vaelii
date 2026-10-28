# Contexts

- **Covers:** how a sentex is scoped to a context, how the `genlCx` closure orders
  contexts into the shipped topology, where a forward-derived or lifted fact is placed, and
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

**A `genlCx` edge is `:monotonic` and undeniable.** `genlCx` is forced-monotonic ([nmtms.md](nmtms.md#the-forced-monotonic-set)): every edge is held
`:monotonic` whatever strength it was written at, so it caps no firing's class, and a
denial of a stored edge loses to it and moves no edge.

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

`placement-rep` reads the taxonomy's component map, so an unrepaired component leaves the
group with no name and the placement lands on whichever member the caller asked about.
`settle` repairs the map after it reconciles belief as well as before, because an edge
defeated out of a cycle or revived into one moves a component with no sentex moving
([taxonomy.md](taxonomy.md)).

## The context topology

The default topology is three levels, most general (top) to most specific (bottom):

| context | holds | sees |
|---|---|---|
| CxUniverse | the upper ontology: every file under `resources/kb/upper/` | nothing |
| the middle contexts | `kb/middle/` — seven theories, beside three opt-in theories | CxUniverse |
| CxWell | no content of its own | the seven theories |

Data hangs below CxWell.

- **CxUniverse** — the root: every context the middle layer wires in sees it, and a
  context no `genlCx` edge names sees nothing but itself ([A context outside the
  topology](#a-context-outside-the-topology)). `vaelii.host.core-context` loads every
  file under `resources/kb/upper/` into it as one batch. `core.txt` is the
  code-supported vocabulary (every special predicate the engine interprets) and the top
  of the ontology: the parts of the three partitions of `thing`
  ([taxonomy.md](taxonomy.md#the-three-partitions-of-thing)), `physical`, `spatiotemporal`,
  `nowhere_never`, `logical`, `linguistic`, `quantitative`, `biological`, `organism`
  and `measure`. Each other file is one domain:
  - `abstract.txt` — the kinds below the skeleton `core.txt` holds (`made`, `food`,
    `substance`, `body_part`, `context`, …), the structural relations
    `tangiblePartOf`/`locatedIn`, and the `travelling` and `flying` event kinds.
  - `organism.txt` — the biological taxonomy and its disjointness.
  - `life.txt` — the organism relations (`parentOf`, `siblingOf`, `flies`, `mortal`,
    `birthYearOf`, `olderThan`, …) with their arg and metadata.
  - `society.txt` — the social relations (`marriedTo`, `likes`, `owns`).
  - `measure.txt` — the theory of measurement: the two measure terms, the
    `dimensionOf`/`conversionFactor` table, the five comparisons
    ([quantity.md](quantity.md)), and measurement said as coarsely as it can be said —
    `signOf` / `trendOf`, the three qualitative arithmetic relations and the
    `derivativeOf` edge, for the quantities nobody has a figure for
    ([sign.md](sign.md)).
  - `reflection.txt` — the language the KB is written in, as something the KB can talk
    about: the expression lattice (atomic and non-atomic expressions, open and closed,
    well-formed and ill-formed) and the use/mention vocabulary `proposition`, `means`,
    `denotes` and `expresses`. `core.txt` keeps the expression kinds the engine or its
    own declarations name (`symbol`, the value kinds, `formula`, `sentence`,
    `non_atomic_term`) and `linguistic`.
  - `space.txt` — qualitative space: RCC-8 topology, cardinal direction, relative
    direction and qualitative distance, fifty predicates between them
    ([space.md](space.md)).
  - `time.txt` — qualitative time in three layers over the same subject: Allen's
    thirteen interval relations plus seven derived disjunctions, the point algebra over
    instants with the endpoint predicates that bridge the two, and the metric layer
    (`temporalDistance`) that puts real measures on the gaps ([time.md](time.md),
    [stp.md](stp.md)). The `length` / `totalDuration` / `overlapDuration` vocabulary the
    duration arithmetic computes over is here too ([duration.md](duration.md)), and so
    are the three calendar constructors `YearFn` / `MonthFn` / `DayFn`, which name an
    interval the calendar already picks out ([context-nat.md](context-nat.md)).

  CxUniverse is also the target of **lifting**: `decontextualized_predicate` copies and
  the forced `genlCx` extent are stored here. It states each shipped context's `context`
  membership, since it stores every `genlCx` edge.
- **the middle contexts** (`kb/middle/`) — how the definitional things *interrelate*,
  where several overlapping theories can coexist. One context per theory, each seeing
  CxUniverse and seen by CxWell:
  - `CxKinship` — grandparentOf, ancestorOf, olderThan.
  - `CxMereology` — a part is located where its whole is; owning a whole entails
    owning its parts. Both are `transitiveInArgInverse` declarations along
    `tangiblePartOf`.
  - `CxBiology` — birds fly by default except penguins; organisms are mortal;
    flight enables travel.
  - `CxChange` — a simple event calculus: a state persists until an event ends it,
    so `holdsAt` is inertia over what `initiates` and `terminates` say
    ([time.md](time.md)).
  - `CxAnatomy` — what kinds of thing have what kinds of part, entirely in
    `partType` claims. Nothing here concludes anything about an individual, which is
    deliberate: "birds have wings" to "Pingu has a wing" needs a quantifier reading.
  - `CxSize` — comparative size said the two ways it can be said: `typeLargerThan`
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
  room temperature and pressure. Stone, wood and glass are solid, mercury is liquid, and
  any `metal_stuff` is solid by default, with mercury the stated exception. CxWell stays free of any
  temperature, so a context below CxWell serves a story set on Mars as well as one set in a
  kitchen. A context opts in by placing itself under CxNormalPhysicalConditions, and a
  context under both CxWell and CxNormalPhysicalConditions reads the everyday theories at
  room temperature.
- **CxTra** — an **opt-in** theory in `kb/middle/` that sees CxUniverse and that
  CxWell does **not** see. CxTra holds vocabulary that is generally useful but specific
  to one domain, and no starter context CxWell sees states that vocabulary. A context
  opts in by placing itself under CxTra, and a context that does not see CxTra reads
  none of its relations or kinds. CxTra holds three vocabularies:
  - **computing** — ten relations over software tools, their invocations and
    receipts, media resources and DNS names, and the sixteen kinds the relations are
    typed over (`computational_system`, `software_tool`, `tool_invocation`,
    `media_resource`, `ip_address` and the kinds below them), each with its comment,
    its `genl` edges and its disjointness. The computing relations state no rule.
    `(functional toolName)` is a decontextualized mark, so every context that sees
    CxUniverse reads that mark.
  - **content and carriers** — `information` is content apart from its medium, and
    `conceptual_work` is information composed as one work. `(carries ?carrier ?info)`
    types position 1 `temporal` and position 2 `information`, so a tangible paper copy
    and an intangible event, e.g. a bird's chirp, are both accepted; not functional in
    position 2, so one carrier holds more than one piece of information.
    `subInformationOf` specializes the upper ontology's `intangiblePartOf`,
    `tangiblePartOf`'s twin for things without mass, for a chapter in a book or a frame
    in a video.
    `(agentClaims ?agent (sentexHandle H))` says that `?agent` presents sentex H as
    true; no rule concludes it from `carries`. `(dataContent ?info ?string)` is
    functional over the exact symbol sequence `?info` holds, and
    `(propositionalContent ?info ?proposition)` is not functional over the existing
    `proposition` type; neither is derived from an information's author, encoding or
    context. `agentClaims` is `target_following_predicate`, so retracting H retracts
    the claims that name it.
  - **perception** — `perceives` is the general relation and `sees` specializes it.
    `seeImage` and `watchVideo` conclude `sees` by a rule guarded by its `spatial`
    second argument, since an image or a video need not be located.
- **CxSocialExtension** — an **opt-in** theory in `kb/middle/` that sees CxSocial,
  and through it CxUniverse, and that CxWell does **not** see: `nestingPartnerOf`
  (a spec of CxSocial's `romanticPartnerOf` and `roommateOf`, and read by a rule from
  the two) and `chosenSiblingOf` (a spec of `relativeOf`). A context opts in by
  placing itself under CxSocialExtension, which also carries CxSocial's own
  relations to it. **`<Theory>Extension` names a
  theory that extends an existing starter theory with vocabulary most contexts
  under the base theory have no occasion to see:** the base theory ships to every
  context below CxWell, and the extension only to a context placed under it.
- **CxWell** — sees every middle context except the three opt-in theories, so it (and any
  context below it) transitively sees the whole ontology except
  CxNormalPhysicalConditions, CxSocialExtension and CxTra. A
  `kb/middle/` file is one of the seven theories when it states `(genlCx CxWell <its
  context>)`, and an opt-in theory when it does not.

**CxUniverse is locked to the shipped files where it speaks the engine's vocabulary.**
`vaelii.host.sync/sync!` makes CxUniverse's premises about the engine's own terms exactly
what the shipped files produce, with three exceptions: a premise naming a term no shipped
premise names, which is about an author's vocabulary; a `genlCx` premise, which CxUniverse
stores whichever context states it; and a sentex that is not a premise (a lifted copy, a
rule firing). A premise an author writes into CxUniverse naming only shipped terms is
retracted at the next sync, and a shipped premise held at another strength is restated at
the shipped one. The cost of the vocabulary rule is a premise the engine stopped shipping
together with the last mention of a term in it: the term is no longer the engine's, and
the premise stays. `assert` does not refuse a premise written into
CxUniverse. An author's own vocabulary goes in a context of the author's own
([Adding a context](#adding-a-context)), which sync does not read.

**A middle context sees no other middle context, so a term two of them extend belongs
in CxUniverse.** `CxBiology` does not see `CxSocial`. A term defined in one middle context
and *extended* from another is invisible where it is extended, and the closure breaks:
an edge placing `animal` under `organism`, written where `organism` is not visible, leaves
`animal` unable to reach `thing` from there, so every `arg` constraint written there
convicts nothing in its own context.
`starter_test/a-term-two-middle-contexts-touch-is-defined-in-cxuniverse` holds that.
*Using* another context's term is a separate question the rule does not cover;
extending one breaks a closure.

Each middle file wires *itself* in with its `genlCx` edges, so the topology is **data**:
dropping a `Cx<Name>.txt` in `resources/kb/middle/` adds a context, and dropping a
`<domain>.txt` in `resources/kb/upper/` adds to CxUniverse, with no code change. Every
file present is loaded on kb start by default. There is **no** direct `(genlCx CxWell
CxUniverse)` edge; CxWell reaches CxUniverse through each middle context.

`vaelii.host.core-context` loads the upper layer alone, and the middle contexts are the
starter's, so a **vocabulary KB** holds CxUniverse's content and no `genlCx` edge.

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

### Adding a context

A user adds a context of their own to the topology. A context CxUniverse sees
(`(genlCx CxUniverse CxMy)`) holds universal vocabulary, visible from every data context
below CxWell. A theory sees CxUniverse and is seen by CxWell (`(genlCx CxMy CxUniverse)`
and `(genlCx CxWell CxMy)`), so every data context below CxWell reads it. Neither touches
a shipped file or a premise of CxUniverse, so sync leaves both in place.

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
| `CxEverything` | **ignored** | — *(the store, not a context's view)* | — |
| `?var` (incl. the default `?ctx`) | followed | every literal in **one** context's view | unified into that variable |
| `CxInference` | followed | every literal in **one** context's view | `:context`, beside the bindings |
| a real `Cx…` | followed | every literal in **this** context's view | — |
| `CxNothing` | followed (vacuously) | the empty view — the provers alone | — |

`CxEverything` is the only row that ignores belief, so its answers say what the store
spells rather than what the KB holds ([below](#cxeverything-syntactic-and-a-named-opt-out-of-belief-filtering)).
The other rows differ only in whose view has to hold the answer.

Rows two and three are the **same reading** and differ in where the witness goes. A
variable is unified with the witness, so a goal that already binds it to a different
context drops the answer. `CxInference` names no variable, so its witness goes beside the
bindings under the keyword `:context` (`vantage/witness-key`), which cannot collide with a
goal's `?`-symbols.

A goal every literal of which is *computed* — `different`, `evaluate`, `unknown` — names no
context, so it is read whole-KB with no witness (`vantage/nothing-to-witness?`,
[why](defenses.md#a-goal-every-literal-of-which-is-computed-names-no-context)). A **mixed**
goal is read jointly: `[(p ?x) (unknown (q ?x))]` reads "a reader that sees p and does not
know q".

**The query contexts are resolved at the entry point because the engine cannot tell them
from a context.** All three are `Cx…` CapitalCamelCase, so `nm/context?` calls them
contexts and `sx/variable?` does not. Reaching the engine, one would read as a context no
edge names, whose ancestor set is itself, and the read would answer empty. `CxNothing` is
that reading on purpose: it sees no fact and inherits no vocabulary, so only a prover
answers. A read entry point that does not resolve a query context refuses one
(`:unsupported-context`). The reads that resolve one are `query`, `query?`, `ask`, `ask?`,
`prove`, `provable?` and `sentexes-matching`.

**An unscoped read refuses a goal spelling `?ctx`** (`:shape`). Retrieval matches every
sentex's context slot against the marker `?ctx`, whatever variable the caller named the
context, so a goal variable spelled `?ctx` would be bound to the context instead of its
argument. A goal read at a named context may spell it.

### CxInference: the joint reading

The engine's unscoped join, at the marker `?ctx`, reads *per literal*: it hands every
conjunct the same wildcard and merges what comes back, so a fact in `CxA` joins a fact in
`CxB` even when no context sees both. The read entry point never answers with that join.
`CxInference` and a variable context read it **jointly**: an answer survives only if some
one reader's `genlCx` ancestor set covers the whole derivation, and that reader is the
answer's witness.

The witness is the **most general** such reader (`tax/maximal-contexts`), computed per
answer from every reader that gave it. The readers below it see a superset of the same
knowledge and add no claim, so reporting all of them would make the answer count a fact
about how finely the KB is divided. Under `:proof?` an answer is one derivation, so two
proofs of one binding keep a witness each, and a variable witness is unified inside
`:bindings`.

Two implementations, in `vaelii.impl.vantage`, chosen by `vantage/*strategy*`, call one
witness function, so they maximize alike:

- **`:fan`** (the reference) enumerates the readers and asks each the ordinary scoped
  question. Every answer is one a reader gives, and each reader runs the path a named
  context runs, so `except`, retired-spelling and closure scoping apply unchanged. The fan
  is the one read that is **not lazy**: which witness is maximal is a property of the
  whole answer set. With no reader at all (no context, no stored fact the goal matches,
  and no stored ingredient of a computed answer to it) it reads unscoped and the answers
  carry no witness: such an answer rests on no fact a reader holds, so it holds from every
  reader. `sentexes-matching` takes the fan's record form
  (`vantage/fan-distinct`), which attaches no witness, since a record carries its own
  `:context`, and is lazy over the readers.
- **`:post-hoc`** asks once, unscoped, carrying what each answer *rested on*, and places
  the result with `maximal-common-descendant-contexts`, as a forward firing places its
  conclusion. One pass instead of one per reader. The join keeps one row per derivation,
  not one per binding: a binding two derivations give is placed by each, so a placement
  that drops one keeps the other.

An unscoped pass reads the KB with three filters off, so post-hoc restores each at the
placement: the **`genl` and `genlInverse` edges a match subsumed through** (a reader that
sees the fact but not the edge does not have the answer; one row per `genl` route no other
route covers, `provers/subsumption-routes`, where a route resting on an edge a defeat or an
`except` can hide covers only the routes resting on that edge too), the **exceptions**
(`'?ctx` reads with an empty hidden set, so an answer could land in a context that
`except`s one of its facts), and the **retired spellings** (supersession is per reader,
so a placement below an equality merge sees both a fact and its twin).
`vantage_differential_test` compares the two strategies over generated lattices holding
all three.

Post-hoc answers only a goal it can place, and hands every other goal to the fan, which
reports `:strategy :fan`:

- A *computed* answer is out unless its prover names the stored sentexes it rests on, one
  answer per derivation, and rests on no absence (`provers/placeable-prover?`). The
  stored-fact prover and `ArgTypeProver` qualify: an inferred type carries its usage, its
  `arg` declaration and the `genl` routes from the usage's predicate to the declared one
  and from the declared type to the asked one (`SupportingProver`). A walk over stored
  hops names one chain where several may derive the pair, and an answer under NAF, a
  closed extent or an `except` can be lost to the unscoped pass, which sees facts a reader
  does not; those go to the fan. `placeable?` asks the prover registry of each literal.
- A literal that reaches other provers once the join binds it is out: the join compares
  the provers a substituted literal dispatches to with those of the literal as written,
  and abandons the goal to the fan when the two sets differ. `ArgTypeProver` answers an
  open `(t1 ?a)` where a declaration typing `t1` has no stored membership covering it
  ([argtypes.md](argtypes.md#the-open-membership-goal)), so under the constraint-only
  reading `(t1 ?a)` and `(t1 X)` reach the same two provers and the join places them.
  Under the entailing reading the mint covers a type `arity/mintable-type?` admits, so
  `(t1 ?a)` reaches the stored-fact prover alone, `(t1 X)` reaches `ArgTypeProver` too,
  and the join abandons the goal.
- A rule-expanding read is out: an antecedent fact is not one of the goals, so its context
  never reaches a placement.
- A goal a merge rewrote is out. A reader above the merge asks the goal as written, and
  one unscoped pass asks one question.

The strategy is a cost decision that must not change the answer set, exactly as
`res/*hierarchical-retrieval*` is for retrieval, and `query_context_test` compares the two
directly. `:post-hoc` is the default because it is **bounded**, not because it always
wins: the join meters the rows it builds, a run past `lattice contexts ×
vantage/*rows-per-reader*` (20) is abandoned mid-stage, and the fan answers whatever was
abandoned —
[why](defenses.md#post-hoc-placement-is-the-default-because-it-is-bounded).

The readers are the `genlCx` lattice, plus any context holding a fact the goal could
match, plus any context holding an **ingredient** of a computed answer to one of its
literals (`provers/ingredient-contexts`). A context wired by **no** edge is not a node of
the closure, so `tax/contexts` does not list it, and a fact asserted into it has that
context as its only reader. Such a context sees only itself, so it answers a computed
literal from stored facts only when it holds every one of them, and the readers name it by
one ingredient each such answer rests on:

| prover | the ingredient | read |
|---|---|---|
| `ArgTypeProver` | the usage: a sentex naming the individual, or for an open argument a fact on a predicate a declaration no stored membership covers types | the term index, one record fetch per posting; the predicate extent's contexts for an open argument |
| `SymmetricProver`, `TransitivePredicateProver`, `InverseProver` | a fact on the predicate, a spec of it, or an inverse partner; for a negated goal, a denial on a partner or a genl of one | the predicate extent's contexts |
| `MetaConstraintProver` | a declaration of the goal's functor | the predicate extent's contexts |
| `ReflexiveProver` | a `(reflexive P)` statement | the taxonomy's supporter contexts |
| `TransitivityProver` on `genl`, `CommonGenlProver` | a `genl` edge out of a ground subtype or into a ground supertype | the taxonomy's edge contexts |
| `DisjointnessProver`, `DisjointnessNegationProver` | a separating declaration | the predicate extent's contexts |
| `NegatesProver` | a `negates` declaration on the negated predicate or a supertype of it | the taxonomy's supporter contexts |
| `CoveringProver` | a `covering` or `partition` declaration naming the part | the taxonomy's supporter contexts |
| `ClosedExtentProver` | a `closed_extent_predicate` or `closedExtentForArg` grant | the predicate extent's contexts |
| `DefnSufficientProver`, `DefnNecessaryNegationProver` | a `defnSufficient` or `defnNecessary` declaration, or a `defnIff` | the predicate extent's contexts |
| `TransitiveInArgProver` | a `transitiveInArg` or `transitiveInArgInverse` declaration on the predicate | the declarations' contexts (`inherit/positions`) |
| `EqualityProver` | a stored `sameAs`, `equals` or `rewriteOf`, or a schematic equation | the predicate extent's contexts, one record fetch per schematic equation |
| a `SupportingProver` | a fact on one of its `support-sources` | the predicate extent's contexts |
| a calculus prover (`qcn-kb/CalculusProver`) | a fact on a predicate that puts a node into its network | the predicate extent's contexts |

A computed prover outside the table rests on no stored fact of its own, so it adds no
reader: the provers that answer a subgoal (`unknown`, `thereExists`, `forall`, the
aggregates, `believes`, `bravely` and `cautiously`), `different`, which holds by the
absence of a merge, and the provers that read only the goal's terms or a table every
context reads alike (the evaluables, `evaluate`, the expression-kind and argument-position
readers, `admitsArgnum`, the calendar). The reader set needs no `tax/meet-closure`: a
context outside the lattice meets no other context, and the lattice is closed under meets.
Finding the matched contexts costs one record fetch per match of the goal, paid before the
first answer: the index enumerates no census of the contexts holding facts.

### CxEverything: syntactic, and a named opt-out of belief filtering

`CxEverything` drops two filters, context scoping and the JTMS read, so it answers what the
store *spells* and is the only reading that sees a defeated default. It opts out of belief
filtering by name: an answer taken under it says a derivation is spelled in the store, not
that the KB holds it.

It keeps the derived relations: the `genl` / `genlCx` closures and the equality partition
are computed from believed edges either way, so a subsumption over a *defeated* `genl` edge
stays invisible under it.

The flag is the dynamic var `res/*belief-blind*`, and `res/blind-seq` re-binds it at each
realization step of the lazy answer, since a `binding` around the entry point is popped
before the seq realizes. The flag is part of every cache key on the path
(`matches-visible`'s literal cache and the reach cache under `provers/closure-key`),
because a blind read asks the same question at the same wildcard context as an ordinary
one and moves no clock.

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

The test world's owns-parts rule shows both outcomes. The forward rule `(implies (and
(owns ?p ?whole) (tangiblePartOf ?part ?whole)) (owns ?p ?part))` is stored in CxWell, which
every data context sees, and the test-world cast supplies the facts. The starter states the
same reach as `(transitiveInArgInverse owns 2 tangiblePartOf)` in `CxMereology`, which
answers at query time and stores no conclusion to place ([inherit.md](inherit.md)). The rule
derives `(owns Tom Roof1)`: both `(owns Tom House1)` and `(tangiblePartOf Roof1 House1)` sit in
CxSocialWorld, so the intersection is non-empty and the conclusion lands there.
But `(owns Tom Engine1)` is **not** derived — `(owns Tom Car1)` is in CxSocialWorld
while `(tangiblePartOf Engine1 Car1)` is in CxNaturalWorld (sibling data contexts with no
common view), so the placement intersection is empty and no justification is made.

## except: removing visibility down a context subtree

`(except (sentexHandle H))` asserted in context C removes visibility of the sentex `H`
from C **and every context that sees C** — its `context-down` closure — while leaving
the more general contexts C sees untouched. It is a **meta-sentex**: `(sentexHandle H)`
is the term form of a stored sentex's handle (`sentex/sentex-handle`), so the except
names the sentex it hides rather than restating it. `except` is in the baseline
forced-monotonic set ([nmtms.md](nmtms.md#the-forced-monotonic-set)): an except is
never the loser of a nogood and a denial of one loses to it, so retracting the except is
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

**An except on a `genlCx` edge.** An except of a `genlCx` edge E in force at a reader R
removes E from R's ancestor set. It also removes every `genlCx` edge whose every
justification rests on E, for reads and for a firing's placement alike: a hidden `genlCx`
edge is on no second route (`exc/witness-paths`), so the read walk forces out what rests
on E as chain's placement does. The read is stratified, with no fixpoint over the
hierarchy. The excepts in force at R are those stated in a context of R's ancestor set
with no except applied (`tax/context-up-global`), so which excepts R reads depends on no
edge's visibility.

Take CxQ, CxB and CxS, each under CxUniverse, with `(genlCx CxQ CxB)`, the forward rule
`(genlCx CxQ ?b) ⇒ (genlCx CxS ?b)`, and an except of the first edge stated in CxS. CxS does
not see CxB: a fact in CxB is not asked true at CxS, and a firing that joins it with a fact
in CxS is not placed at CxS. Asserting `(genlCx CxS CxB)` directly gives the edge a
justification resting on no excepted edge, and CxS sees CxB
(`except_gnarly_test/a-genlCx-edge-resting-on-an-excepted-genlCx-edge-leaves-the-excepting-reader-for-reads-and-chain`).

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
reads 0 off the trie's `[except]` count, and that is the presence check: one count read. A KB that
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
keyed on the handle it names rather than a predicate) and a `genlCx` move (below).

### One context move

A `genlCx` move is a `genlCx` edge stored, removed or relabelled, or an `except` that
moved reaching the support of an active edge's supporter. `tax/context-move` computes what
one move shows or hides, from the taxonomy as it stands, in two strata:

- **raw**: `super`'s global ancestor set with `super`, less `sub`'s global ancestor set
  without the edge. The excepts in force at a reader are read off its raw ancestor set, so
  the excepts that come into or leave force at a reader under `sub` are the ones stated in
  these contexts.
- **effective**: the readers under `sub` fall into classes by the contexts of their global
  ancestor set that state an `except` on a `genlCx` supporter's support, or on one of those
  excepts (`exc/genlCx-except-contexts`). Readers of one class read every `genlCx` supporter
  alike. Each class's moved contexts are `super`'s ancestor set under the class's scope,
  less the class's ancestor set of `sub` without the edge; the union over the classes holds
  every context whose facts a reader under `sub` gains or loses through the edge.

An except that comes into force through the edge hides its target at the readers below,
and the except family re-checks that target, so the effective stratum names the edge's own
contribution. After a removal it names a superset of what a reader lost.

The settle computes each move once a pass and hands the value to every family the move
reaches (`special/drain-context-moves!`, rows in `special/move-families`). The moves are the
`genlCx` facts out of the lower ends J5 recorded since the placement cursor (J6) that the
touched set holds, the removed edges `integrate/sentex-removed!` queued (Q8), and the
active edges the excepts that moved this pass reach (Q3). The rows are the excepted rules
whose firings lie under `sub`, the excepts stated in the raw stratum (and the excepts those
name), the facts the effective stratum makes matchable, the restatements, merges and
argument-type mints a shown edge owes, the mints a hidden edge gives back, and the rules a
correspondence declaration meets differently once a declaration or a rule is in the
effective stratum. The
placement families and the inherited clashes read the moves' reach: `:under`, the contexts
at or below a moved lower end, and `:below`, what those see that an active edge's upper end
does not. The `genlCx` integrate arms update the taxonomy alone, so an asserted,
rule-concluded, computed or relabelled edge reaches the families by one path.

A move that shows contexts is also split by what each reader gains (`:gains`): per
reader under `sub`, the contexts it sees after the move and did not see without every edge
the drain moves, the readers grouped by that set. A pair, a meeting or a verdict the move
makes new at a reader holds an ingredient stored in its gain, so when the gain states
facts alone (no cached relation, `except`, `defeat` or definition) and the readers see no
`except` (`checks/plain-gain?`), the merge, argument-type and mint-withdrawal sweeps and
the argument holds read what the gain's facts meet in place of everything the readers saw,
and a group whose gain is empty reads nothing. Otherwise a group reads its own `below`, as
the whole move did. The merge sweep derives a group's candidates at its own readers and at
the readers of other groups above them, so a pair two groups gain is merged at the more
general reader only
(`genlcx_move_gain_test/a-merge-lands-at-the-most-general-reader-in-every-order`). So
adding an edge over an empty or small context to a context holding
millions of facts costs what the new context holds (`lein perf`'s
`genlcx-edge-over-a-small-context-under-a-large-one`); `genlcx_move_gain_test` holds the
split against the whole sweep (`checks/*whole-move-sweeps?*`).

An except stated in a context a reader sees only through a hidden edge is still in force
there: with `(genlCx CxSup CxTop)` excepted at CxSup and an except of `(ff Aa)` stated in
CxTop, the edge `(genlCx CxSub CxSup)` puts CxTop in CxSub's raw ancestor set, and the
firing over `(ff Aa)` at CxSub is swept in every order
(`except_gnarly_test/an-except-in-a-context-the-sub-reaches-past-a-hidden-edge-is-rechecked-when-the-edge-arrives`).
A reader below `sub` can gain contexts `sub` already saw: with the edge from CxSub to CxY
excepted at CxR under CxSub, an edge from CxSub to CxSup under CxY shows CxR the facts of
CxY (`except_gnarly_test/a-genlCx-edge-shows-a-reader-below-its-sub-what-the-sub-already-saw`).
`lein perf`'s `genlcx-edge-beside-excepted-declarations` and
`genlcx-edge-beside-seen-excepts` hold an edge flat in the excepts it does not move, and
`genlcx-edge-revealing-one-except` in the firings that do not rest on the target of the
one it moves.

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
carries, so it satisfies nothing. A positive antecedent is never satisfied and the rule
cannot fire. An `exceptWhen` query never matches, so the conclusion it was written to
block stands believed. An `(unknown (ist …))` is satisfied by the same emptiness, so the
rule fires unconditionally. The last two change belief without any sign, which is why the
shape is refused rather than stored inert.

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

The reading a rule wants is that `S` be **visible** in some context, and the two
mechanisms below state it: `(decontextualized_predicate P)` takes every `(P ...)` into
CxUniverse, and a `genlCx` edge puts `Ctx` in another context's ancestor set. Under
either the literal is written plainly. An `ist` into a context that already sees the rule
and the facts adds nothing, because that context inherits the conclusion from the maximal
placement above it.

**A query takes the form a rule is refused** because the query grants no visibility the
context argument did not already grant: `(ist CxA S)` asked from anywhere is
`(sentexes-matching kb S CxA)`, which the caller asked for. A rule's answer decides
*belief*, and the rule's own context may not see `Ctx`. `context_scoping_test` asserts the
query half and `check_test` asserts the refusal.

**The predicate meta-ontology** shows the lift in place of an `ist`. The algebraic marks
(`symmetric`, `transitive`, `functional`, …) are types under `binary_predicate`, so
`(symmetric siblingOf)` makes `isa? siblingOf binary_predicate` hold, and the marks and
the arity classes are `decontextualized_predicate`s, so each is read from every context
that sees CxUniverse ([the arity rules](#the-consumers-and-what-each-of-them-may-reach)).

## decontextualized_predicate: a fact that belongs to the KB, not to one theory

`(decontextualized_predicate P)` takes every `(P ...)` out of the context it was stated
in. Each one — asserted, or concluded by a rule — is additionally **deduced into
CxUniverse**, supported by the placement sentex *and* the
`(decontextualized_predicate P)` sentex. Since every context the topology wires in sees CxUniverse,
the fact becomes visible everywhere, even from a *sibling* context that cannot see
where it was stated. Retracting or defeating either the original or the declaration
withdraws the copy through the JTMS, and declaring it retroactively lifts the `(P ...)`
facts already present. The retroactive sweep copies what is stored, not what is believed,
so a fact out of belief at the declaration's arrival has its copy, which rests on the fact
and follows its label. A declaration that revives lifts the facts stored while it was OUT,
which its arrival could not reach (`special/revived-declaration-sweeps`, run by the
settle for every revived datum).

The mechanism is documented in the KB by the `comment` on `decontextualized_predicate` in
`core.txt`. It is implemented in code rather than as a rule, because a rule stating it
would match every fact in the store and would name its target with an `ist` consequent,
which a rule is refused. The declaration is ordinary predicate metadata, read back with
`(has-prop? kb :decontextualized pred)`.

**The mark itself is read globally, not through the asserting fact's ancestor set.** A
`(decontextualized_predicate P)` stated *anywhere* lifts every `(P ...)` in the KB,
including facts stated in contexts that cannot see the declaration
(`special/deduce-lifts`). The lift decides the *storage* context, and making it
conditional on what sees the declaration would be circular: the copy exists to make the
fact visible to readers the stating context does not see. A declaration in one theory
therefore publishes a sibling theory's `(P ...)` extent KB-wide, so the mark belongs in a
schema context, not a contingent one.

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
the middle contexts and the data contexts below them all reach CxUniverse, so the first
copy is visible to the *next* assert, and the settle weighs the clash where the second
assert is made. The same reach is why a declaration written in CxUniverse constrains
every context in the tree, and it is the reason the target is fixed.

The residual case is a context outside the topology, which sees neither its
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

Lifting only asserted content would make belief depend on arrival order, which
[nmtms.md](nmtms.md) forbids: with the declaration first, a rule's `(P a)` would stay where
it was concluded, and with the declaration last the retroactive sweep would lift it.

Each copy is a **new datum in a context that did not have it**, so it goes on the
chaining agenda like any rule conclusion: its arrival re-triggers any `exceptWhen` stated
over that predicate, and rules keyed on the predicate fire on the copy as well as on the
original.

The second firing decides **placement**; forward chaining already matches antecedents
across every context. Firing on the original places the conclusion in the source context,
and firing on the copy places it in CxUniverse. A consequence of a decontextualized fact
is therefore decontextualized in turn: if `(edgeTo A B)` holds everywhere, so does what a
universal rule concludes from it. The cost is **two stored sentexes for one conclusion**,
and the rule fires twice.

The fixpoint still terminates for the ordinary reason: re-deriving a sentence already
stored adds a justification, not a handle, so the agenda drains. Each copy carries
`1 + max` antecedent depth, so a `:max-depth` bounds a chain of lifts exactly as it
bounds a chain of rules.

**A copy merges what it licenses, as any new content does.** A `functional` or
`anti_symmetric` mark derives its equalities where the mark is visible, and the copy is
what makes it visible from CxUniverse, so the copy runs the same four merges the assert
entry point and `chain/place-fact-conclusion` run for what they store
(`special/copy-merges`). Without them the merge would follow arrival order: a mark stated
in a theory before the facts would merge them at CxUniverse, and the same mark stated
after them below that theory alone. `relation_properties_test`'s
`a-merge-mark-in-a-sibling-merges-from-every-context-in-either-order` asserts both orders.

Two boundaries, both deliberate:

- **A negative fact is not lifted.** `(not (P a))` has functor `not`, so a declaration
  about `P` does not reach it. The positive extent becomes universal and the negative
  one stays in its context.
- **Declaring is O(extent).** The retroactive sweep creates one copy per stored
  `(P ...)` inside the declaring `assert`, so a predicate with a large extent is a long
  assert. Declare before loading where you can.

### What the shipped ontology declares it of

Every shipped declaration is a claim about a **predicate** rather than about a world.
`functional`, `functionalInArg`, `inverse`, `reflexive`, `irreflexive`, `symmetric`, `commutative`,
`commutativeInArgs`, `commutativeInArgAndRest`, `associative`, `idempotent`,
`meetFunctionOf`, `anti_symmetric`, `asymmetric`, `transitive`, `anti_transitive`, `equivalence_relation`, `injection`, `surjection` and
`bijection` carry the mark — so a `(symmetric P)` stated in one theory is the KB's
claim about `P` and not that theory's — and `genlCx` carries the forced variant below.
The fourteen length bindings (`sx/arity-binding-functors`: `arity`, `arityMin`, the nine
exact-arity classes and the three `variable_arity` classes) carry it at `:monotonic`, so a
copy keeps its binding's strength and a relation's length reads the same at every context
([taxonomy.md](taxonomy.md#arity)). A tuple breaking that length is inert at every
context, and two lengths that disagree are one `contradicts` stored in CxUniverse.
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
subject matter. Two theories that disagree about whether `tangiblePartOf` composes are not
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
resting the copy on the statement alone. On a KB carrying the upper layer, which declares it, the
copy is the same copy. A context that sees neither a statement nor the copy reads the
four as the store does ([A context outside the topology](#a-context-outside-the-topology)).

**A KB without the upper layer holds the other twelve where they are stated.** Nothing lifts
them, so every reader reads `(transitive R)` stated in `CxA` from `CxA` and below, alike.
`inherit_test`'s `the-transitivity-licence-is-read-from-the-asking-context` asserts that half,
and `a-permuting-mark-is-read-from-every-context-on-this-kb-too` beside it asserts the four
permuting marks. Such a KB still holds the baseline forced-monotonic set, so a
`genlCx` edge, a `functional` or `irreflexive` mark, a definitional declaration, an arity
binding, an `except` or an equality stated `:default` is never a loser and a denial of
one is held OUT, as under the upper layer ([nmtms.md](nmtms.md#the-forced-monotonic-set)).

Measured on a lattice of two siblings `CxA` and `CxB` under CxUniverse and `CxD` below
both, with the mark stated in `CxA` and the facts it governs in CxUniverse, each in both
arrival orders:

| mark | read from, with the upper layer | read from, without | what reads it |
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
| `injection` `surjection` `bijection` | every context | nowhere | `core.txt` rules deriving `functional` and `functionalInArg`; inert without them |
| `functionalInArg` | every context | `CxA`, `CxD` | the `:functional-in-arg` table — the merge, placed where the mark is visible |

Each table entry records its supporting sentexes with their contexts
([taxonomy.md](taxonomy.md#reads-are-scoped-by-the-asking-context)): the statement in `CxA`
and, where the mark is lifted, the copy in CxUniverse, which is what every reader outside
`CxA`'s descendants answers from.

### A context outside the topology

A context no `genlCx` edge names sees nothing but itself, not even CxUniverse. The
lattice has no implicit root. A reader of such a context reads what was stated there,
which is what an agent context's independence rests on
([belief.md](belief.md#independence-and-inheriting-base)), and an edge is how a KB puts the
context into the topology. A context above CxUniverse that sees no context below it does
not see CxUniverse either, so it reads a lifted copy no more than an unwired context
does.

For the twelve marks lifted by declaration, "every context" in the table above therefore
means every context that sees CxUniverse. A context that does not:

- reads a mark only from a statement it sees, its own included. `(functional R)` stated in
  it merges its facts there, and one stated in a sibling does not.
- has its own statements lifted like any other context's, so every context that sees
  CxUniverse reads a mark stated in it.
- runs no definitional check whose declaration it cannot see. It sees none of CxUniverse's
  argument declarations, so it admits what a context under CxUniverse refuses, and a lift out
  of it runs the check on the copy (`unchecked-target?`, above).
- gets no CxUniverse rule firing over its facts, since no context sees both the rule and the
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
`a-merge-mark-reaches-a-context-with-no-edge-only-from-its-own-statement` asserts the twelve,
`inherit_test`'s `a-permuting-mark-is-read-from-a-context-with-no-edge` asserts the property
reads, and `order_independence_test`'s
`a-firing-a-mark-no-statement-of-reaches-is-placed-in-every-order` asserts the firing, in an
unwired context and in one that sees a context other than CxUniverse.

## forced_decontextualized_predicate: a canonical home in CxUniverse

`(forced_decontextualized_predicate P)` is the stronger variant. Instead of leaving the
original where it was asserted and deducing a copy, it **forces the storage context
of every `(P ...)` to CxUniverse** on assert — no separate justification, the fact's
extent simply lives there. `genlCx` is declared this way (`core.txt` states
`(forced_decontextualized_predicate genlCx)`), so the whole context
topology has one canonical home rather than being scattered across the contexts each
edge was asserted in.

The reads that look a sentence up by the context it names go to the same home:
`handle-of`, `sentexes-matching` and `why-not` given `(P …)` or `(ist CxA (P …))` at a named
context read CxUniverse, through the `assert-entry/storage-context` call that `assert`
stores with.

**A declaration arriving after its facts moves them.** Each `(P …)` premise stored outside
CxUniverse is asserted there at its own strength and the original retracted
(`core/rehome-forced-extent!`), so the KB is the one the other order builds. A text load
puts the context topology first (`text/load-entries!`), which puts every `genlCx` edge
ahead of the declaration; the move is what keeps those edges out of the contexts they were
written in, and out of the `(context …)` entailments a fact there draws. The moves are one
`edit!` batch with one settle, which seeds each fact the moved `genlCx` edges reach once
rather than once per edge (`lein perf`'s `forced-declaration-over-edges-stated-below`).

Both are wff-checked at assert time, like the other special predicates:
`decontextualized_predicate` routes through the same `prop-problems` check as
`transitive` / `symmetric` / `functional`, since it is a one-argument mark on a
predicate like they are.

## Context-scoped constraint checks

`arg` arg checks and disjointness checks are **not global**: when asserting in
context K they consider only constraints and type memberships *visible from* K
(its `context-up` closure). So shared vocabulary must live in a context K sees. In the
starter, the upper layer sits in CxUniverse, which every data context reaches, so its
`arg` constraints, comments, and type memberships are visible everywhere.

The `genl` closure reads are scoped the same way (docs/taxonomy.md): `genls` /
`specs` / `genl?` / `disjoint?` take a context, and a read asked from K walks only
the edges some believed supporter asserts from K's ancestor set.  The **`genlCx`
closure itself stays global, as a stated exception** — visibility scoped by
visibility would be circular, `forced_decontextualized_predicate` already forces
every `genlCx` edge universal, and the scoped reads' interning is keyed on
that closure being context-independent.

A clash no single writer could see, admissible where each half was stated and jointly
visible from some descendant, refuses no writer. `settle` weighs it at its **vantage**, the
most general context that sees both halves and what separates them, and the defeat it
places is scoped to that vantage and below, so a context reading one half alone keeps
what it holds ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)).

**`exposed-clashes` asks the scoped read, not an enumeration.** For a pair of held
memberships `[t1 c1]` and `[t2 c2]` it must answer whether some context sees both and a
whole derivation of their disjointness. Enumerated forwards, that is one witness per
ancestor path per separated pair per supporter choice, exponential in a multiply-inheriting
hierarchy, and a pair that is not jointly visible exhausts every witness. The scoped
`disjoint? t1 t2 K` walks only edges visible from K, so it holds exactly when K sees some
whole derivation, and the pass asks it at each of `common-descendants(c1, c2)`. It
enumerates witnesses only for the report, once one is known to exist. Both answers are
memoized per pass on `[t1 c1 t2 c2]` (`clashes/exposure-probes`), so individuals holding
the same two types in the same two contexts ask once.

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
  `special/move-seeds` is the twin that pays it, from the settle's drain
  ([One context move](#one-context-move)). Matching fans an antecedent up the
  *visibility* ancestor set, so an edge arriving after both the rule and the facts changes which
  facts the rule can see — and again the arriving datum is the edge, so firing the rules
  keyed on `genlCx` is not the same thing as re-joining the rules the edge just gave
  a wider view.

  **The seed set is what the lower contexts see, not the edge's two ends.** The edge grows
  the view of every context `X` below `sub` by `super`'s ancestor set, `up`. A pairing it
  makes new takes one ingredient from that growth and the other from anywhere in `X`'s
  view, and `X`'s view holds more than the edge's endpoints: `sub`'s other ancestors, and
  in a diamond the ancestors of `X`'s other parents. So the second set, `seen`, is the
  union of the ancestor sets of every context in `sub`'s descendant set, less `up` — the
  contexts some lower context sees that `super` does not. A pair both inside `up` met at
  `super` before the edge, and a pair both inside `seen` met at the context that sees
  both. The `up` half narrows once more, to `fresh`: the contexts of `up` some reader
  below `sub` did not already see (`tax/context-move`'s effective stratum). The old
  ancestor set is read the way
  placement reads it: the walk does not cross an edge with a stored negation, which the
  taxonomy's closure does not apply. So a new pairing has an ingredient in `fresh`, or the lower context saw all of
  it, and one in `seen`, or `super` saw all of it, and its rule sits in one of three
  places: in `seen`, with a fact in `fresh`; in `fresh`, with a fact in `seen` — a rule
  stated *above* inherited into the context newly wired under it, placing its conclusion
  there; or in the rest of `up`, which every lower context saw before, with a fact on each
  side — a two-antecedent rule above both parents of a diamond, whose two facts only the
  context below both sees together. Seeding is by fact, so the seeds are the believed
  sentexes of the sets a pairing needs a fact from. The equality twins read the same
  union for the same trigger (`tax/context-move`'s `:seen`).

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
  context wired under a new parent usually already sees CxUniverse, so `seen` holds the
  whole ontology's edges while `up` holds a handful of facts. When the facts of `up`
  under the rule-key set's fan cost no more postings than `seen` states edges, those facts are
  the seeds; otherwise each edge `seen` states seeds the facts of `up` under it, with the
  functors `subsumption-seeds` reads. The cost is the smaller of the edges `seen` states
  and the rule-relevant postings of `up`, and `perf`'s `genlcx-edge-under-a-seen-taxonomy`
  holds it flat in the edges `seen` states.

  **It is enumerated from the rules, and each half is conditional on where a rule is stated**
  ([why](defenses.md#the-visibility-seeds-are-read-off-the-rule-index)). Two reads of the
  rule index give the seeds: the antecedent keys some stored rule takes
  (`reads/as-stored-rule-keys-deferred`), and the contexts a rule is stated in (the rule extent,
  `reads/stores-rule-in?`). The seeding walks those predicates' extents and keeps what falls
  in the sets to seed, or walks those sets' own contents when they hold fewer postings
  (`special/seeds-in`). `fresh` is seeded when a rule is stated in `seen`, and `seen` when
  one is stated in `fresh`. When neither holds but a rule is stated in the rest of `up`, a
  pairing it makes has a fact on each side and seeding either finds the other, so the side
  holding fewer sentexes is seeded. Wiring an *empty* context under a full one seeds
  nothing, since `seen` is the new context alone and holds nothing.

  **A batch seeds what was stored before the edge arrived.** Under `with-deferred-settle`
  every assert chains as it arrives and the drain runs once, at the batch's close, so a
  fact, rule or `genl` edge stored after the edge was chained or joined with the edge
  already in the taxonomy. When the touched set created every believed supporter of
  the edge, its least one is the floor (`special/seed-floor`): handles are allocated in
  assertion order, so the checks on `seen` read only the rules and `genl` edges below the
  floor, and the seeds keep only the facts below it. The batch then seeds what a settle
  right after the edge's assert would have seeded. An edge with a believed supporter from
  before the settle has no floor, since it may have come into belief after the facts
  beside it. The argument-type sweep of the move (`special/entail-under-context-edge`)
  reads the same floor. `perf`'s `deferred-facts-after-a-context-edge` holds the closing
  drain to one posting read per fact stored after the edge.

  **Each rule-key predicate's extent is read fanned by `genl`**, the way the matcher fans
  it (`special/rule-key-functors`): down the spec closure for a positive
  antecedent, and up the genl closure for a negated one, since a negation reverses the
  fan. Reading the antecedent's own functor alone finds the facts a rule *names* and not
  the facts it *matches*, so the edge re-joins the rule over half of what it newly sees,
  and one type standing between the rule and the fact is enough to leave the conclusion
  in the orders that wired the contexts first and nowhere else. A predicate outside the
  hierarchy closes to itself, so the fan costs a KB with no type hierarchy under its rule
  antecedents nothing. The seeding builds the fan only when the contexts it reads hold
  more postings than there are antecedent keys (`special/key-fan`). Below that count,
  each fact's functor is walked up its genl closure to a positive key, so an edge from an
  empty context reads no closure, and of the rule-key set its count alone. `perf`'s
  `genlcx-edge-to-an-empty-context-under-a-rule-fan` holds that cost flat in the size of
  the hierarchy under a rule antecedent, and `visibility-seeds-beside-rule-keys` in the
  key count.

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
  half that does: a sighting can outlive the edge that witnessed it when the contexts are
  wired together a second way, and the firing must then be placed again.

  `special/resubsumption-seeds` re-seeds the **antecedents of the firings that named the
  removed `genlCx` edge**, less what the sweep removed (`special/sighting-seeds`). The
  set is exact because of two properties of the chainer. Every firing records its
  justification, including a re-derivation of a conclusion already stored
  (`chain/place-fact-conclusion`). And a firing names a witness path for every context its
  placement sees an ingredient over (`chain/visibility-support`). Removing an edge only
  shrinks the contexts that see a firing's ingredients. So a firing whose placement set
  changes either lost a placement whose every path ran through the edge, or held one whose
  named path did, and in both cases its justification named the edge. A conclusion the
  sweep removed that another firing still licenses is re-derived by that firing, which
  named the edge or rests on a removed conclusion that is re-derived first and arrives as
  a new datum. The seeds are read off the removed justification records before the
  teardown deletes them, and they include the antecedents of a firing whose conclusion a
  second justification kept: that firing can be owed a placement in a lower context that
  now sees the rule only by another route.

  The pass costs the firings the edge licensed, not the contexts it joined. Retracting an
  edge that licensed nothing reads one justification record per swept justification and
  chains nothing. The rules that join over the `genlCx` closure itself
  (`closure-reader-rules`) are re-joined only where the sweep collected more than the
  record asked for, and the edge's own argument-type mint does not count as more: its
  justification takes the edge as the fact typed, not as a route
  (`special/edge-own-mints`). Whether a surviving route still licenses a re-seeded firing
  is `place-conseq`'s question, answered from the taxonomy as it stands after the removal.

  Most re-seeded firings find no placement, and that pass files no `:no-placement`
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
  rules in `kb/upper/core.txt` place by the ordinary rule and name no context, so an
  `(arity myRel 2)` stated in a context concludes `(binary_predicate myRel)` *there*.
  **Do not name a context in them.** The KB-wide reading comes from the lift: the
  declaration and the conclusion are both `decontextualized_predicate`s, so each has a
  copy in CxUniverse, and the rule fires on the declaration's copy there.
