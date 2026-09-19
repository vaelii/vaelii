# Adding a predicate the engine interprets

- **Covers:** the declaration every term of the engine's own grammar carries in
  `vaelii.impl.predicates` — its eleven fields, the five closed vocabularies they are
  written from and the contract each facet commits an entry to — how it is joined to the
  arms in `vaelii.impl.special`, which rosters derive from it, what is refused at namespace
  load, what a new interpreted term owes and what adding one comes to, and the three things
  the declaration deliberately does not carry.
- **Not here:** adding an ordinary domain predicate, which is a KB edit and no code at all
  → [naming.md](naming.md), [taxonomy.md](taxonomy.md), [argtypes.md](argtypes.md); what
  any one existing declaration *does* → the subsystem page that owns it; the public
  functions that read the answer back → [api.md](api.md).
- **Assumes:** predicate, sentex, context, handle, belief, taxonomy prop, `genl` →
  [glossary.md](glossary.md).

## Most new predicates need no code

A domain predicate is knowledge, not machinery. `marriedTo` is added by writing it down:

```
(comment marriedTo "Spouse of, as a civil or religious status. Symmetric, and holding at a time rather than forever.")
(binary_predicate marriedTo)
(arg marriedTo 1 person)
(arg marriedTo 2 person)
(symmetric marriedTo)
```

Every line there is a sentex like any other — asserted, indexed, believed, retractable.
Nothing in `src/` mentions `marriedTo`, and nothing has to: the predicate is *described*
using declarations the engine already interprets, and `symmetric` is doing the work. That
is the normal case and the rest of this page does not apply to it.

The question that sends you further is narrow:

> **Does a code path have to run when a sentex with this functor is asserted, retracted or
> recovered?**

If a new term maintains a cache, or refuses a malformed sentence at the entry point, or is
answered by a prover rather than stored, then the engine reads the *functor itself* and
the term has to be declared. `symmetric` is such a term. `marriedTo` is not, and the
distance between them is the whole subject below.

## One term, one entry

An interpreted predicate is a fact about a functor that nine different namespaces each
need a piece of, and the twenty-odd rosters keyed on functor names are all projections of
it. `vaelii.impl.predicates` is where the fact is written once; a roster that reads the
entry is a **view**, not a second copy, and cannot drift from it.

Five namespaces read it today — `special`, `taxonomy`, `settle`, `spec` and `vocabulary`,
enumerated below, and a roster one of them owns can itself be a view read once more
(`provers/transitive-predicates` *is* `taxonomy/closure-relations`). The rest still hold
their own list: `checks`' four, `provers/evaluable-predicates`, `sentex`'s three
(`sentex/aggregate-functors`, `sentex/rule-direction-wrappers`,
`sentex/default-rule-wrapper`), `kb/equality-predicates` and `inherit/declarations`. A term
that belongs in one of those is enrolled there by hand, and that is the part of adding a
predicate this structure does not do for you.

The namespace requires nothing but `clojure.*`, which is not an accident. The arms need
functions from four layers — `taxonomy`, `wff`, `checks`, `settle` — so a namespace
holding data *and* arms could only ever sit at the top of the stack, where `taxonomy` and
`wff` cannot reach it. Splitting them puts the data at the bottom, where everyone can
([defenses.md](defenses.md#what-a-term-says-lives-below-what-the-engine-does-about-it)):

```
predicates  ←  taxonomy  ←  wff  ←  checks  ←  special  ←  settle  ←  vocabulary
```

`entries` is a **vector**, not a map, because the order is content: `special/entries` is
that order filtered, and `special/rebuild-taxonomy` replays it top to bottom with a
rebuild arm allowed to read what an earlier one wrote.

## The declaration record

Eleven fields. Six are structure the engine dispatches on; five are prose — one finding,
the two exclusive answers to *does anything read this*, and two the facet validator holds
an entry to.

| Field | Says |
|---|---|
| `:shape` | how the term is written as a sentence — `{:args [kind …]}`, optionally `:optional [kind …]` for a trailing argument that may be omitted or `:variadic kind` for an open tail. Arity is `(count :args)`. `nil` for a term that is never a sentence functor (a collection: `string`, `thing`, `binary_predicate`) |
| `:storage` | `[kind target]` — which of a closed set of storage shapes the declaration is cached under, and which table it lands in. `[:none]` for a term nothing caches |
| `:checked` | does `special/entries` give the functor a structural well-formedness arm |
| `:facets` | a set from the closed `facets` vocabulary — the lanes the term takes part in |
| `:family` | the family whose spellings must move together, or `nil` |
| `:sweeps` | what this declaration *arriving after* the content it constrains puts back in question, or absent |
| `:notes` | prose, only where the term does something the facet vocabulary has no word for. A note is a **finding**, not a description |
| `:enforced` | prose naming the code path that reads the term — what `interpreted` hands a KB author who asks whether a declaration does anything |
| `:inert` | prose recording that nothing reads the term **and that this is a decision**. Written by the `inert` constructor, which sets the facet with it, so the class is never a second opinion about the facets |
| `:stops-short` | facet → prose: an implication of `facet-contract` this entry does not satisfy, and the reason. Checked against the set actually owed, in both directions, so the record can neither be missing nor go stale |
| `:opposing-read` | prose, required on every `:arbitrable` entry: what the conviction's opposing side is **read through**, and whether that read survives the nogood defeating either member. Not decidable from the declaration, so it is a stated claim |

`:enforced` and `:inert` are exclusive and the constructor is what makes them so — an entry
cannot claim a lane and be classified inert, because claiming a lane means carrying a facet
and `inert` replaces the facet set outright. The **class** is read off `:facets`, never off
which key the prose was written under.

Entries are written through constructors — `prop`, `mark`, `pair`, `wff-only`, `operator`,
`collection`, `structural` — for the same reason the vocabularies below are closed: an entry
a couple of parameters *construct* has no way for its fields to disagree with each other,
and the twenty-seven predicate marks `prop` builds differ in exactly one keyword.
`symmetric`'s entry is the whole of what the engine is told about it:

```clojure
['symmetric (enforced (prop :symmetric :facets #{:answers})
                      (str "taxonomy prop :symmetric — canonical argument order, so both"
                           " spellings are one sentex; also a binary_predicate type"))]
```

`prop` fills in the rest: the sentence shape `(symmetric P)` with argument 1 a predicate,
`[:prop :symmetric]` storage, `:checked true`, and `:cached` with `:derived` — the
`:derived` facet because a mark that arrives by *derivation* has to install like an asserted
one, or a restart changes the answer. The one facet written by hand is the one no
constructor could know: `(symmetric P)` arriving changes what a level-6 query says about
`P`, so the term carries `:answers` and owes an exception re-check for it.

A mark that also convicts stored content says so, says what it sweeps, and states what its
conviction reads the opposing side through — the last a field no constructor fills, so the
entry `assoc`s it on:

```clojure
['asymmetric (enforced (assoc (prop :asymmetric
                                    :facets #{:reach :convicts :arbitrable :answers}
                                    :sweeps :predicate-marked)
                              :opposing-read
                              (str "the nogood pairs the tuple with its converse; the"
                                   " (asymmetric P) mark is not a member of it, so defeating"
                                   " either direction leaves the mark standing and the"
                                   " conviction re-derivable."))
                       "checks/asymmetry-problem — a nogood against the converse; also a binary_predicate type")]
```

## The five closed vocabularies

Closed on purpose. Growing one is a single commit that adds the keyword *and* the rule
governing it, so a keyword can never come to mean whatever its first user assumed.

| Vocabulary | Members | What a member commits you to |
|---|---|---|
| `argument-kinds` | `:predicate` `:relation` `:relation-name` `:type` `:context` `:function` `:position` `:integer` `:term` `:sentence` | a kind here is one a well-formedness arm can be **generated** from; a position no kind fits is a position whose check stays hand-written |
| `storage-kinds` | `:prop` `:mark` `:edge` `:keyed-pair` `:pred-position` `:none` | each names what the add / drop / rebuild triple looks like. `:prop` means the `tax/props` roster specifically, whose keys `spec/::prop-kind` pins — a one-term mark into a table of its own is `:mark`, not `:prop` |
| `facets` | `:cached` `:derived` `:migrates` `:arbitrable` `:reach` `:query-only` `:answers` `:retriggers` `:convicts` `:inert` | the lanes that read the term. Six are reconstructible from a live data structure and are pinned that way; `:answers`, `:retriggers`, `:convicts` and `:inert` are *claims*, which is exactly why they are the ones that go wrong quietly |
| `sweep-kinds` | `:type-separating` `:predicate-marked` `:both` | carrying one **is** being a clash declaration, so `settle`'s exposure pass has an arm for it. Absent is the answer for a term whose retroactive half is a different mechanism |
| `mark-families` | `:functional` `:argument-constraint` | a family lives in more than one lane. Naming it once is what makes a third spelling reach every lane at once |

`facets` is the one that is not written out. `facet-contract` gives every facet a row — the
facets carrying it *implies*, and whether a mark family has to agree about it — and `facets`
is that map's keys. So for this vocabulary the single commit above is not a rule to keep to
but the only edit available: a keyword with no row is not a facet, and there is no second
list to fall out of step with the first.

The distinction worth reading twice is `:predicate` against `:relation` in the first row. A
mark read off a sentence's functor holds its subject to a symbol that is not an individual.
An argument *constraint* is looser on purpose: a function has argument positions exactly as
a predicate does, a function is CapitalCamelCase and so is indistinguishable from an individual, and a
relation may be denoted by a NAT rather than named. Collapsing the two refuses the
conventional spelling and waves the exotic one through.

A family is **not** a storage roster. `functional` stores under the `:functional` prop where
`functionalInArg` stores `[pred n]` pairs; the two have no common storage to be rostered by,
only a common family and a common argument 1.

## The arms, and the join

`vaelii.impl.special` holds what the engine *does* — the `:integrate` / `:disintegrate` /
`:rebuild` triple and the structural `:wff` check — as a **map** keyed by functor. It has
no order of its own, deliberately: the order is the declaration's, so the table cannot have
two orders that must agree and no way to notice when they stop.

`special/entries` is the join. It walks `predicates/entries`, keeps the functors this table
holds an entry for, and merges each declaration's half (the `:props` kind a mark maintains,
and whether its arms run on the derivation path as well as the assert path) with the arms.
That single ordered vector is *the* enumeration all four walks use — integrate,
disintegrate, rebuild and wff — so a predicate declared and armed joins all four at once.

## What the declaration is read for

Once the entry exists, these follow from it. None of them is a list you also edit.

| Reader | What it takes |
|---|---|
| `special/entries` | the table's order, each `:props` kind, each derivation-path flag |
| `taxonomy/closure-relations` | every term whose storage kind is `:edge` — being cached as a closure and being in this set are one fact |
| `taxonomy/arg-declaration-props` | the `:argument-constraint` family, each paired with its own prop keyword |
| `taxonomy/functional-family-marks` | the `:functional` family, each spelling with the shape its own argument list implies |
| `settle`'s eight clash and trigger rosters | `:arbitrable` marks paired with their prop keyword, the `:sweeps` field grouped by kind, and the `:edge` storage kind |
| `spec/::prop-kind` | the set of `tax/props` keywords the grammar declares |
| `vocabulary/roster` | the `:enforced` / `:inert` prose, classed by `:facets` — and through it `interpreted` and `vocabulary-audit` |

Case conversion is not an alternative to pairing a functor with its prop keyword and never
was: `anti_transitive` stores under `:anti-transitive`. The declaration states the keyword.

## Refused at namespace load

Five validators, twenty refusals, and **one** `ex-info` `:type` between them —
`:bad-table-entry`, discriminated by a `:mismatch` key. Whichever way the table is bad, the
caller catching it is the namespace load, and there is nothing a second keyword would let
that caller do.

| Validator | Refuses |
|---|---|
| `predicates/check-families` | a mark family whose spellings disagree about what they sweep (`:mismatch :family`); a term that sweeps and declares no shape (`:mismatch :sweeps`) |
| `special/check-entries` | an entry with *some* of the cache triple — the cache would fill on assert and leak on retract, or come back wrong after a recover (`:mismatch :partial-cache-triple`); and an entry with no arm at all, which is a typo (`:mismatch :no-arm`) |
| `special/check-declarations` | a functor with arms and no declaration or the reverse (`:mismatch :enumeration`); a `:cached` declaration whose arms have no triple, or the reverse (`:mismatch :cached`); a `:checked` declaration with no `:wff` arm, or the reverse (`:mismatch :checked`) |
| `settle/clash-declaration-kinds` | a sweep kind the exposure pass has no arm for, and a definitional mark that does not sweep what it convicts (`:mismatch :reach`) |
| `predicates/check-facets`, run at `settle`'s load | a field value outside its closed vocabulary (`:vocabulary`); `:cached` disagreeing with the storage kind (`:storage`); a `:sweeps` with no `:reach` (`:sweep-reach`); an `:arbitrable` term with no `:opposing-read` claim (`:arbitrable`); an `:inert` term carrying a second facet or a storage (`:inert`); a roster that reads a mark family as a family and enumerates something other than that family (`:family-roster`); a facet the entry is committed to and neither carries nor records — by `facet-contract` (`:implication`), by a sibling spelling of its family (`:family-lane`), or by answering goals about a predicate and posting no exception re-check (`:recheck`); and a `:stops-short` record that is not owed or carries no reason (`:stops-short`) |

`check-entries` and `check-declarations` are two validators at two layers rather than one
duplicated: the first sees only the arms and so can check only that they mirror each other,
and the second is the cross-layer half. Neither can catch an arm attached to the *wrong*
functor, which is what the tests are for.

`check-facets` is a third layering of the same kind, and the reason it runs at **`settle`'s**
load rather than at `predicates`' own: two of its rules ask whether an arm exists, and a
namespace that sits below `taxonomy` and `wff` by construction cannot see one. It takes the
facts that live above as arguments — the set of functors `special/declaration-subjects` posts
re-checks for — so the layering is unchanged and only the call site moves. Merging it into
`check-entries` would put the arm check at the top of the stack, where a `special` load would
no longer prove anything on its own.

**One rule has no `:stops-short` escape, and the reason is the distinction the field
rests on.** A facet is a *claim* — nothing in the tree states `:answers` or `:convicts`, so
an entry that falls short of one can answer for itself in prose. A **roster** is not a
claim: it is a set sitting in another namespace, and two enumerations of one fact do not
get to disagree. `quotedArg` is why the rule exists. Three rosters read the argument
constraints as a family — the declarations here, `checks/constraint-declaration-functors`
at the entry point, `provers/meta-constraint-functors` on the query surface — and the third held
three of the four for as long as nothing compared them, so one declaration meant one thing
to `assert` and another to `ask`. The lane rule below caught the missing facet and offered
a record; a record was the wrong answer, and `:family-roster` is what refuses instead.
`special/entailing-declarations` is deliberately a *proper* subset of the family and so is
not one of these rosters — a `quotedArg` mints nothing, and that absence is recorded on the
entry where it belongs.

The rule's **reach** is the map `settle` hands the validator, and a map of rosters is a
roster with the same failure: one that reads a family and is not named there is one the
rule says nothing about. So `predicates_test` reads the loaded tree for any var whose
members are a subset of a family's spellings — subset and not equality, because the
`quotedArg` bug *was* a roster holding three of four — and holds each to being named at
that call site or recorded as derived from these declarations, which is the one way a
roster cannot disagree with them.

An implication is a refusal **unless the entry records the exception**, in `:stops-short`,
which maps the facet to prose saying why. The record is checked against the set actually owed
in both directions, so it can neither be missing nor go stale once the term gains the facet —
a recorded exception, not a suppression. Five entries carry one today. Where a constraint is
real and not decidable from data at all, the encoding is a required field instead: every
`:arbitrable` term states in `:opposing-read` what its conviction's opposing side is read
through, because a nogood whose read follows the belief it moves destroys its own premise, and
no facet set says that. `arity` carries the same field with the negative answer, which is why
it names a second sentex exactly as the four arbitrable marks do and is still not one of them.

The failures these prevent are the ones the engine cannot report. A family joined to one
lane and not another does not throw — the merge simply does not happen, or the clash simply
is not reported, in the one arrival order that route was the only way into.

## Adding one, end to end

1. **Write the term into the ontology.** `resources/kb/CxCore.txt`, term-centric: a
   `comment`, the predicate class, an `arg` per position, and any marks it carries. This is
   the KB half and it is data.
2. **Declare it** in `predicates/entries`, through a constructor where one fits. Position
   matters: the functors `special/entries` holds come first, in the table's own order.
3. **Give it arms** in `special`'s `arms` map, if it is `:cached` or `:checked` — the
   triple, the `:wff` check, or both. Declaring `:checked true` with no `:wff` arm will not
   load, and neither will the reverse.
4. **Answer for it.** Either `:enforced` prose naming the path that reads it, or the `inert`
   constructor with the reason nothing does. A term CxCore comments and nobody answers for
   lands in `vocabulary-audit`'s `:unclassified`.
5. **Satisfy the facet contract, or record what it stops short of.** Each facet you carry
   implies others, a family holds its spellings to the same lanes, and a declaration that
   answers goals about a predicate has to post an exception re-check. Whichever you cannot
   meet goes in `:stops-short` with the reason, and an `:arbitrable` term states its
   `:opposing-read` outright. `settle`'s load is where you find out.
6. **Let the views follow.** Do not add the functor to `taxonomy`'s three rosters,
   `settle`'s eight, `spec/::prop-kind` or `vocabulary/roster` — they are reads, and adding
   it by hand puts back exactly the drift this structure removed. The rosters that are *not*
   views, listed under "One term, one entry" above, are the ones that still need the entry
   written into them.

### What a new term owes

| Test | Because |
|---|---|
| `predicates_test` | the declaration's own contract: every inert term carries a stated reason, every note names a lane the facet vocabulary does not reach, every `:arbitrable` term claims its `:opposing-read`, and a roster that has moved states its value as a **literal** — reconstructing a derived var proves the wiring and nothing about what it holds. The validators' enforcement are driven here too, one deliberately broken declaration per rule |
| `special_table_test` | the table's order, each `:props` kind and each derivation-path flag, frozen in a table written out that nothing derives |
| `vocabulary_audit_test` | `:unclassified`, `:retired` and `:contradicted` are empty on the shipped ontology |
| `core_context_test` | the CxCore sentex count, which [kbs.md](kbs.md)'s shipped-KB table quotes and nothing else pins — update both together |
| `refusal_roster_test`, `type_contract_test` | a new `ex-info` `:type` needs both, with its changelog entry. Reusing `:bad-table-entry` with a new `:mismatch` value is the cheaper move and needs one line — `type_contract_test`'s `discriminants`, where the `:mismatch` vocabulary is pinned as the `:type` one is. Check there first that the condition is not one another validator already has a word for |

Then `lein gate`, and `lein test-matrix --owed`: a declaration change reaches inference,
TMS and planning, so the matrix is owed — thirteen of the fifteen configurations, for a mark
that touches `checks`, `settle` and `taxonomy`.

### What that comes to

The heaviest shape a declaration has is a predicate mark that caches a table of its own,
convicts stored content and is arbitrable — `functional`'s shape, and `asymmetric`'s. Adding
one is a dozen-odd files, and the **split** is what the structure above is for rather than
the total:

| Kind of file | Where |
|---|---|
| the **declaration** | one row of `predicates/entries`, and nothing else in the namespace |
| **arms** carrying semantics nothing derives | the table and its add / drop / rebuild triple in `taxonomy`, plus the readers that follow belief through it; the check itself in `checks` and the two call sites that ask it; the arms map in `special` and the shape refusal in `wff`; `settle`'s partner posting and its message arm; the `(comment …)` block in `CxCore.txt`; the term's own test namespace |
| **frozen surfaces**, each named by a **failing test** rather than found by reading | `special_table_test`'s order, `type_contract_test`'s `:type` vocabulary, `predicates_test`'s roster pins, `vocabulary_audit_test`'s sweep pin, and `troubleshooting.md`'s `:type` row, which `refusal_roster_test` requires. All five are in "What a new term owes" above |
| **rosters that are not views** | `checks/arbitrable-kinds`, and `settle`'s hand-unions — the two under "Where this stops" below |

`web.clj`'s clash chip is the one surface nothing names, and it does not need to: an
unlisted `:type` renders as its own keyword name, which is a worse word than a chosen one
and not a wrong one.

Eleven rosters take a new functor with **no edit at all**: `special/entries`' four walks,
`taxonomy`'s three, `spec/::prop-kind`, `vocabulary/roster`, and five of `settle`'s. The one
to notice is `settle/trigger-functor-kind`, which recognizes the term *at its own arity* off
`predicates/mark-shape` and the declared argument list — so a spelling cannot be swept at an
arity its own arguments contradict, and the two lanes a family lives in cannot be joined one
at a time.

## Where this stops

Three things sit outside the declaration. Each is a decision about what a declaration is,
not a part of it that has yet to be written.

**A prover is not a predicate's property**, and the registry is unreachable from
`predicates` on purpose. `applicable?` reads a *goal's shape*, not a functor's name —
`EvaluableProver` reads the arguments in front of it, `QuantityProver` reads a unit table
first, `ArgTypeProver` answers a goal on any predicate carrying a declared argument type, and
none of the three has an entry to write. `add-prover` is public API and registers with no
entry at all: nine opt-in provers ship in-tree and third-party ones are the point of the
extension, so a framework requiring an entry either breaks them or grows an escape hatch that
makes the entry advisory — and an advisory entry is a roster again. And `sole-prover` already
answers the coordination question a per-predicate binding would be reaching for, as a question
about the KB rather than about the vocabulary. What the declaration carries instead is
`:answers`: not who answers a goal, but that this term's *arrival* moves what a level-6 query
says about some predicate, which is what obliges it to post an exception re-check. A prover's
**shape** table stays with the prover; its **enrolment** is the declaration's, which is the
line `provers`' four functor rosters sit on either side of ([inference.md](inference.md)).

**The structural connectives are declared for their shape and nothing else.** `not`, `and`,
`or`, `implies` and the rule-direction wrappers are written through the `structural`
constructor: `[:none]` storage, no facets, no arms. The canonicalizer reads `implies`,
`and` and the wrappers into *slots of the record* — antecedent, consequent, direction —
and keeps a `not` as the head of a negative literal's sentence, where the index reads it
as the sign. So no sentex is ever indexed under one of these functors, and there is no
assert path to join, no cache to maintain and no
retraction to mirror. `:shape` is the whole of what the engine is told, and the well-formedness
that shape implies is enforced before the record exists. This is permanent: the day a
connective needed an arm would be the day it stopped being a connective.

**Two joins are stated by hand.** They are of a piece with the rosters under "One term, one
entry" above — a set some namespace holds itself because no field of the eleven carries the
fact it needs — and they are the two an *arbitrable* mark runs into.

- **Which violation `:type` a conviction files under is not on the entry.**
  `checks/arbitrable-kinds` names the four that `settle` arbitrates, and it is *nearly*
  `(second (:storage spec))` — right for `disjoint`, `functional`, `asymmetric` and
  `anti_transitive`, and wrong for `functionalInArg`, which generalizes `functional` off its
  fixed slot and so files under the kind of the mark it generalizes rather than one of its
  own. `predicates_test` reconstructs the set with that exception named as a second
  assertion, which is the only place the two facts are held together.
- **`settle/definitional-marks` is the arbitrable marks that store a taxonomy prop** —
  `(prop-marks :arbitrable)` — and not every arbitrable mark. `functionalInArg` stores
  `[pred n]` pairs and has no prop keyword to be paired with, so it is correctly out of that
  roster and correctly in the sweep rosters beside it. The readers that want the wider set
  union `tax/functional-in-arg-predicates` in themselves: `clash-marked-below`,
  `tuple-marks?`, `clash-vocabulary`, and the `:type` filter that decides which violations
  become exposure entries. That last one filters on the prop keywords, which admits every
  arbitrable mark the grammar has because each files under one of them — a coincidence of the
  current five, not something either roster says about the other.

## Reading the answer back

`(interpreted term)` returns `{:enforced "where"}`, `{:inert "why"}`, or `nil`, and
`(vocabulary-audit kb)` gives the whole picture — including `:unclassified`, the finding it
exists to surface: a declaration that landed in the grammar without anybody deciding whether
the engine reads it. Both are on `vaelii.core`; see [api.md](api.md).

`nil` is **not** "nothing reads it". The question is asked of the engine's own grammar, so
an ordinary domain predicate — `marriedTo`, at the top of this page — is simply not a term
this question is about.
