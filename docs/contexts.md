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

**Two contexts may see each other.** Unlike `genl`, a `genlCx` cycle is admitted:
visibility is a preorder, not an order, and mutual visibility is a claim an ontology
makes — OpenCyc's `genlMt` graph has 49 such components, one of them BaseKB's own
(`BaseKB ↔ UniversalVocabularyMt ↔ CycAgencyTheoryMt ↔ …`). Reachability over a cycle
is perfectly well defined, so the closures answer it directly; the taxonomy keeps its
depth potential over the **condensation** and reads a mutually-visible pair in O(1)
(see [taxonomy.md](taxonomy.md)).

What a cycle is *not* is a merge. The contexts stay distinct records with distinct
extents, because a context is where a sentex is **stored** and not only what it can see:
`sentexes-matching` is exact-context, `(ist BaseKB S)` and `(ist UniversalVocabularyMt S)` are two
sentexes, and collapsing them would throw away which context an assertion was made
in — the one thing an ontology import exists to carry. The claim "each sees the other"
is weaker than "these are the same place", and only the weaker one was made.

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

The default topology is a **five-layer spindle**, most general (top) to most specific
(bottom): the vocabulary head, a *definitional* band, a mid anchor, a *theory* band,
and a bottom anchor. Data hangs below the bottom.

- **CxCore** — the spindle *head*: the code-supported vocabulary (every special
  predicate the engine interprets), asserted by `vaelii.impl.core-context`. The root —
  every context sees it.
- **upper** — the *definitional* band, between Core and Universe: what things *are*,
  always true, like `genl`. One context per domain (`vaelii.impl.starter`), each
  seeing CxCore and seen by CxUniverse:
  - `CxAbstract` — the abstract type skeleton (`intangible`/`physical_object` and
    their kinds) plus the structural relations `partOf`/`locatedIn`.
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
- **CxUniverse** — the mid *anchor*, left free for **lifting**: universally-true
  facts collect here (`decontextualized_predicate` justifications and the forced `genlCx`
  extent). It sees every upper context and is seen by every middle context.
- **middle** — the *theory* band, between Universe and Well: how the definitional
  things *interrelate*, where several overlapping theories can coexist. One context
  per theory, each seeing CxUniverse and seen by CxWell:
  - `CxKinship` — grandparentOf, ancestorOf, olderThan.
  - `CxMereology` — a part is located where its whole is; owning a whole entails
    owning its parts.
  - `CxBiology` — birds fly by default except penguins; living things are mortal;
    flight enables travel.
  - `CxChange` — a simple event calculus: a state persists until an event ends it,
    so `holdsAt` is inertia over what `initiates` and `terminates` say
    ([time.md](time.md)).
  - `CxAnatomy` — what kinds of thing have what kinds of part, entirely in
    `partType` claims. Nothing here concludes anything about an individual, which is
    deliberate: "birds have wings" to "Pingu has a wing" needs a quantifier reading.
  - `CxSize` — comparative size said the two ways it can be said: `largerThan`
    among kinds, and a comparison computed between two objects' measures. The worked
    example of `transitiveInArg` ([inherit.md](inherit.md)).
  - `CxSocial` — what acquaintance follows from, and how employment relates to
    membership. Every rule runs one way only, because `knows` is deliberately not
    symmetric.
- **CxWell** — the bottom *anchor*: it sees every middle theory, so it (and any
  context hung beneath it) transitively sees the whole ontology.

Each upper/middle file wires *itself* into the axis with two `genlCx` edges, so
the topology is **data** — dropping a `Cx<Name>.txt` in `resources/kb/upper/` or `resources/kb/middle/`
adds a context, no code change, and every context present is loaded on kb start by
default. There is **no** direct `(genlCx CxWell CxCore)` edge; Well
reaches Core through the whole axis (middle → Universe → upper → Core).

`vaelii.impl.core-context` loads only the head (CxCore); the bands are the starter's,
so a **CxCore-only KB is just the vocabulary** — no spindle bands at all.

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

A user adds their **own sibling** in either band. A *definitional* sibling sees
CxCore and is seen by CxUniverse (`(genlCx CxMy CxCore)` and
`(genlCx CxUniverse CxMy)`); a *theory* sibling sees CxUniverse and
is seen by CxWell. Its vocabulary is visible from every data context below Well
without touching the shipped bands.

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
(incomparable maxima) or none (no common view ⇒ no justification). A universal rule
firing on specific facts lands its conclusion in the specific context — unless the
consequent is an `(ist Ctx S)` form, which directs it into `Ctx` explicitly (below) — a
**query context** excepted, which is refused there as at every other write entry point, so the
firing drops its conclusion rather than storing into a way of reading.

The placement's own sightings are **antecedents of the firing**: the `genlCx` edges the
conclusion's context sees the rule and the facts over join its justification, so
retracting or defeating one withdraws what it licensed rather than leaving it stored in a
context that can no longer see its reasons. The mechanism, its cost and its
`(ist Ctx S)` exception are with the rest of the scoping rules in
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
names the sentex it hides rather than restating it. Like every other fact it is
belief-following — retracting or defeating the except restores the hidden sentex — and
it rides the ordinary `genlCx` up-closure, visible from exactly the contexts where
it hides its target.

The removal is **total**, not just for reads:

- **Reads.** `res/matches-visible` and `sentexes-matching` drop a handle hidden from the
  view context — the believed excepts visible from there, resolved through `context-up`.
- **Derivations.** A rule firing that used `H` as an antecedent and placed its
  conclusion in the ancestor set rests on a fact that context can no longer see, so the
  conclusion is **blocked and swept** — the derivation-side twin of `exceptWhen`, run
  through the same block/sweep/revive machinery (`chain/justification-excepted?` and
  `place-conseq` ask per placement). A firing that arrives *after* the
  except is never placed in the ancestor set; a late except sweeps what already fired; and
  retracting the except **re-derives** what it was hiding. A conclusion placed *above*
  the ancestor set (a context that does not see the except) is untouched.
- **Rules.** `H` may itself be a rule — a firing rests on its rule exactly as it
  rests on its facts (the rule handle is in the stored justification), so excepting a
  rule sweeps its conclusions from the ancestor set, blocks late firings there, and revives
  them when the except is retracted (`special/recheck-except` re-chains a rule
  target on departure). The backward chainers honor the same removal:
  `provers/candidate-rules` drops a rule the asking context cannot see, so `query`
  and `prove` do not rebuild through a hidden rule what forward chaining swept.

**What the two of them read.** Both go through the KB's `:excepted` roster —
`{context → {hidden-handle → #{except-handle}}}`, maintained O(1) at the store and
removal choke points (`kb/note-excepted!`) exactly as the `:opposed` coincidence set is,
and rebuilt by `recover` because it is derived from storage and no store holds it. A KB
that excepts nothing has an empty roster, and that is the gate: a deref, and no index
read. A KB that excepts something pays one map lookup per context stating an except, plus
a `jtms/in?` per except naming the handle asked about — **belief stays a read**, since an
except can be defeated or revived with no sentex arriving or leaving, which is the same
line `:opposed` draws.

Callers with particular handles in hand — a firing's two or three antecedents, or matches
arriving one at a time — take `res/hidden-fn`, a predicate over one view context, rather
than `res/excepted-handles`, which materializes every handle hidden anywhere in the ancestor set.
The set costs one pass over the reader's excepts however few handles will be asked about;
the predicate costs a lookup per question, and the questions are bounded by the answer set
while the excepts are not. On a chaining run over a KB with 1,000 excepts the difference
is 16× the whole run (`lein bench-hotreads`).

The re-check triggers are the except arriving or leaving (`special/recheck-except`,
keyed on the handle it names rather than a predicate) and any `genlCx` edge change
(`special/recheck-except-ancestors` — a visibility move changes which contexts see the
excepting context, hence what each hides).

## ist: find or create in a context

`ist` — "is true in", the operator from the literature — expresses that S holds in
Ctx. `(ist Ctx S)` is **not** stored as a sentex; given to `assert` (or via
`ist kb Ctx S`) it finds or creates S in context Ctx and returns S's handle
(idempotent).

- `ist kb Ctx S` — find or create S in Ctx.
- `contexts-of kb S` — the contexts S is asserted in.
- `find-sentexes kb S` — any sentex containing S (via the term index).

**ist in a rule consequent.** A rule whose consequent is `(ist Ctx S)` places `S`
into the named context `Ctx` instead of the computed placement — overriding the
default maximal-contexts rule. `Ctx` may be a variable bound by an antecedent (e.g.
`(genlCx ?c CxUniverse) ⇒ (ist ?c ...)`). The rule is indexed by `S`'s predicate,
not by `ist`, and range-restriction covers the inner sentence and the context slot.

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

**ist places, and never reads on a rule's behalf.** There is no `ist` on the antecedent
side: a rule cannot qualify a premise by the context to read it from, and `(ist Ctx S)` in
antecedent or
`exceptWhen` position is refused as `:not-well-formed`. Such a literal is indexed and
matched under the functor `ist`, which no sentex carries, so it satisfies nothing — and
the way that falls out depends on the frame it sits in. A positive antecedent is never
satisfied and the rule cannot fire; an `exceptWhen` query never matches, so the guard
never guards and the conclusion it was written to block stands believed; an `(unknown
(ist …))` is satisfied by that same emptiness, so the rule fires unconditionally. The
middle two are why this is a refusal rather than an inert shape: a rule that does nothing
announces itself, and a guard that passes everything does not.

The reading a rule wants is that `S` be **visible** where it is stated, which is what the
two mechanisms below this section say — `(decontextualized_predicate P)` takes every
`(P ...)` into CxUniverse, which every context sees, and a `genlCx` edge puts
`Ctx` in the rule's own ancestor set. Under either the premise is written plainly, and it is the
`genlCx` topology rather than a per-rule annotation that decides what is readable
from where. `sentex/ist-read-problem` carries the refusal and names both.

**Why the query takes what the antecedent is refused**, since it is one form treated two
ways: the query grants no visibility the context argument did not already grant.
`(sentexes-matching kb S CxA)` has always answered `CxA`'s facts from anywhere,
and `(ist CxA S)` is a spelling of it — the caller asking about `CxA` has said
so. A rule antecedent is the other case: nobody asked, the rule's own context may not see
`Ctx`, and what comes back decides *belief* rather than answering one caller.
`context_scoping_test` pins both halves.

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
`(decontextualized_predicate P)` sentex. Since every context sees CxUniverse,
the fact becomes visible everywhere, even from a *sibling* context that cannot see
where it was stated. Retracting or defeating either the original or the declaration
withdraws the copy through the JTMS, and declaring it retroactively lifts the `(P ...)`
facts already present.

The mechanism is documented in the KB in its own representation by an inert rule,
`(set/inertRule (implies (?pred . ?args) (ist CxUniverse (?pred . ?args))))` — the
dotted rest pattern quantifies over any predicate and its arguments (see
[inference.md](inference.md)). It is `inertRule` because the behavior is implemented
in code, so the rule is never indexed or fired; it only records the intent. The
declaration is ordinary predicate metadata, read back with
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
first copy is visible to the *next* assert, the ordinary context-scoped check catches
the clash at its source, and the second assert is refused where it is made. The upper
spindle sits above the joint and reaches CxCore instead, which is why a declaration
written in CxCore constrains every context in the tree. That is not a lucky property of a well-known context — it is the
whole reason the target is fixed.

The residual case is a context wired outside the spindle, which sees neither its
siblings nor CxUniverse. There the stating context could not have run the check
either, so the lift runs it on the copy itself (`unchecked-target?` — one `sees?` per
lift, and only that case pays anything more), dropping the copy and recording a
`violations` entry that names the context it was lifted from.

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
`functional`, `functionalInArg`, `inverse`, `reflexive`, `irreflexive`, `symmetric`,
`anti_symmetric`, `asymmetric`, `transitive`, `anti_transitive`, `equivalence_relation`,
`injection`, `surjection` and `bijection` carry the mark — so a `(symmetric P)` stated in one theory is the KB's
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

## forced_decontextualized_predicate: a canonical home in CxUniverse

`(forced_decontextualized_predicate P)` is the stronger variant. Instead of leaving the
original where it was asserted and deducing a copy, it **forces the storage context
of every `(P ...)` to CxUniverse** on assert — no separate justification, the fact's
extent simply lives there. `genlCx` is declared this way (the vocabulary head asserts
`(forced_decontextualized_predicate genlCx)` before any `genlCx` edge), so the whole context
topology has one canonical home rather than being scattered across the contexts each
edge was asserted in.

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
reported by `settle`'s exposure pass in `(violations kb)`, never by refusing a
writer on grounds it cannot see.

Under a KB's `:arbitrate` constraint policy it is also **weighed**, and by the same
scoped check: `settle` runs each candidate's definitional question from its own context
*and* from the maximal common descendant of that context and each context holding a
sentex it could pair with. That chooses the asker rather than widening what an asker
sees — a vantage already sees both halves — and it is what stops the same three
sentences from landing on a defeat or on two coexisting claims according to which half
was written last ([nmtms.md](nmtms.md)). Under `:refuse` the pass files the report and
belief is untouched.

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
  drop whichever cannot see it. Only where *no* candidate can is the taxonomy binding,
  and the conclusion **descends** to the maximal contexts that see the edges too. A rule
  and a fact in one context, over a hierarchy stated in a sibling, therefore
  conclude in the contexts below both instead of concluding nowhere. An `(ist Ctx S)`
  consequent is not lowered: the target is named rather than derived, so it places
  where the author said or not at all. A drop is a `:no-placement` entry naming the
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
  named `genl` supporters', since seeing an edge is a sighting like any other — while an
  `(ist Ctx S)` placement names the supporters' alone: the target is not derived from the
  rule or the facts, so it does not rest on seeing them. **The ordinary firing pays one
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
  is the shortest one; a longer route through more general contexts might place the
  conclusion higher, and is deliberately not searched for.

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

  It seeds **both** ancestor sets, because an edge pairs rules and facts in two directions. A
  rule below can now see facts above; and a rule stated *above* is inherited into the
  context newly wired under it, so the edge equally hands the general rule the
  context's own facts and places the conclusion there. Seeding is by fact, so the
  seeds are the believed sentexes of `super`'s ancestor set together with those of `sub`'s
  descendant set.

  **It is enumerated from the rules, and each half is gated on the other holding one.**
  Both are about cost, and the cost is asymptotic rather than constant. Walking the ancestor set
  and keeping the facts a rule could match is a record fetch per sentex *in the ancestor set*, so
  wiring N contexts under a `CxUniverse` holding K facts is O(N·K) against
  O(N+K) without it, and a spindle D deep is O(D²) because each edge's ancestor set is the
  whole chain above. Two ref-counted rosters maintained at the rule index/unindex choke
  points — `:rule-antecedents`, the predicates some rule takes as an antecedent, and
  `:rule-contexts`, the contexts rules are stated in, both beside `:opposed` and both
  replayed by `recover` — turn it around: walk those predicates' extents, keep what falls
  in the ancestor set, and skip a half entirely when the other side holds no rule to benefit.
  Wiring an *empty* context under a full one is the commonest edge there is and now
  seeds nothing, where the ungated version re-seeded the whole ontology above it and
  re-joined rules that had already fired on every fact of it. Measured on the starter
  load: 1.80x ungated, 1.04x with both.

  **Each roster predicate's extent is read fanned by `genl`**, the way the matcher fans
  it (`special/roster-antecedent-functors`): down the spec closure for a positive
  antecedent, and up the genl closure for a negated one, since a negation reverses the
  fan. Reading the antecedent's own functor alone finds the facts a rule *names* and not
  the facts it *matches*, so the edge re-joins the rule over half of what it newly sees,
  and one type standing between the rule and the fact is enough to leave the conclusion
  in the orders that wired the contexts first and nowhere else. A predicate outside the
  hierarchy closes to itself, so the fan costs a KB with no type hierarchy under its rule
  antecedents nothing.

  **Withdrawal needs no twin of it**: dropping an edge *narrows* what a rule sees, and a
  firing names the edges its placement was seen over, so the dependency-directed sweep
  already collects a conclusion whose antecedent stopped being visible. Revival is the
  half that does, and it is the same function read the other way —
  `special/resubsumption-seeds` puts a removed `genlCx` edge's two ancestor sets back on the
  agenda beside a removed `genl` edge's spec subtree, because a sighting can outlive the
  edge that witnessed it when the contexts are wired together a second way.

  **That pass has one condition, and the rule gate above is not it.** It runs only where
  the sweep collected more than the record asked for: a justification naming the departing
  edge is deleted with it, so a conclusion that survived kept a second justification and
  needs nothing, while one that did not is in the swept set. Retracting an edge that
  licensed nothing — the common case — is therefore one functor read per removed record
  and no chaining at all. Where it does run the re-join is **unconditional**, and
  `visibility-seeds` is called in the **ungated** arity it keeps for this caller: the
  rule-holding gate two paragraphs up is skipped on purpose, not inherited. That gate is
  sound for an *arriving* edge because an arriving edge is the only new reachability there
  is — nothing can newly match except through it, so an ancestor set holding no rule newly matches
  nothing. A departing edge says nothing of the kind. The firing being revived saw the
  rule down whichever branch it liked and the facts down another, and neither branch need
  be the one that went, so an edge whose own two ancestor sets hold no rule is precisely the case
  that would lose a firing a surviving route still licenses. Whether the reachability
  really survived is `place-conseq`'s question, answered from the taxonomy as it stands
  after the removal, and a gate here guessing it from the departing edge alone would miss
  a route running anywhere but between that edge's own endpoints.

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

An **`(ist Ctx S)` consequent remains an explicit escape hatch** and is not scoped —
that is what it is for. A rule author writing one is choosing the target, the same way
`forced_decontextualized_predicate` chooses CxUniverse; the engine holds them to
the subsumption check above and nothing else.
