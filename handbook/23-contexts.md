# 23. Contexts

- **Covers:** where a sentence goes: `CxUniverse` and the upper files, the middle theories
  one per file, `CxWell`, `CxRealWorld` and fiction; wiring a context with `genlCx`;
  hiding a sentex below a context with `except`; lifting a predicate's facts with
  `decontextualized_predicate`.
- **Not here:** the strength a sentence is stated at → [ch. 24](24-strength.md); the
  layout inside one file → [ch. 26](26-file-layout.md); contexts named by a function →
  [context-nat.md](../docs/context-nat.md).
- **Assumes:** [ch. 2](02-representation.md), [ch. 8](08-kind-of-term.md) (a context is
  spelled `Cx` followed by CapitalCamelCase).

Every sentex holds in exactly one context. A context sees its own sentences and every
sentence in its `genlCx` ancestor set, and nothing else: facts, rules, taxonomy edges and
the definitional checks all read from that set. Choosing the context is therefore choosing
which readers a sentence reaches.

## The shipped topology

**Practice.** Put definitional vocabulary, the terms and the claims that hold in every
theory, in an upper file. Put a theory, a set of rules and relations one domain shares, in
a middle file of its own. Put individuals and contingent facts in a context below `CxWell`.

**Example.** Each middle file wires itself in with its first two sentences. `CxBiology.txt`
opens:

```clojure
(genlCx CxBiology CxUniverse)
(genlCx CxWell CxBiology)
```

The shipped files give this layout:

| context | holds | sees |
|---|---|---|
| `CxUniverse` | every file under `resources/kb/upper/` | nothing |
| a middle theory | one file under `resources/kb/middle/` | `CxUniverse` |
| `CxWell` | no content of its own | the seven middle theories that name it |
| `CxRealWorld` | the real world's own restatements | `CxWell` |

Two middle files are opt-in theories and state no `(genlCx CxWell …)` edge: `CxTra.txt`
(computing, perception and narrow relationship vocabulary, which sees `CxSocial` as well as
`CxUniverse`) and `CxNormalPhysicalConditions.txt` (which sees `CxRealWorld`). A context reads an opt-in
theory only by placing itself under it.

**Why.**

- *Engine.* The upper files load into `CxUniverse` as one batch, and every context the
  middle layer wires in sees it, so a type, a separation or an argument declaration
  stated there constrains every context in the tree.
- *Engine.* Sync locks the premises of `CxUniverse` and of each shipped middle context
  about the engine's own terms to what the shipped files produce. A premise an author
  writes into one of those contexts naming only shipped terms is retracted at the next
  sync, and a shipped premise held at another strength is restated at the shipped one.
  `assert` does not refuse such a premise, so nothing at the write reports the loss.
- *Engine.* A middle theory sees no other middle theory. A term defined in one and
  extended from another is invisible where it is extended. An edge placing a type under a
  parent the stating context cannot see leaves the type unable to reach `thing` from
  there, and every `arg` constraint written there then convicts nothing. A term two middle
  theories extend therefore belongs in `CxUniverse`.
- *Maintenance.* The topology is data. A new file under `resources/kb/middle/` adds a
  context with no code change, and its own `genlCx` edges say where it sits.

**Why not the other ways.** A theory written into `CxUniverse` reaches every context,
including the ones that hold a different theory of the same domain. A fact written into a
middle theory reaches every data context below `CxWell`, so the theory stops being a
theory and becomes a dataset every reader inherits.

**Audit.** For each new sentence, name the context and the readers that need it. Run
`(context-up kb 'CxMy)` for a new context to read its ancestor set, and confirm with
`sees?` that the context stating a term it extends is in that set.

## Adding a context of your own

**Practice.** Write an author's vocabulary into a context of the author's own. Wire it as a
theory with two edges, or under `CxUniverse` as universal vocabulary with one edge.

**Example.** A theory sees `CxUniverse` and is seen by `CxWell`, as each shipped middle file
does. `CxTra.txt` shows the other pattern, a theory that also sees the theory its
vocabulary builds on, since its relationship terms specialize `CxSocial`'s relations.

```clojure
(genlCx CxTra CxSocial)
```

**Why.**

- *Engine.* Sync reads `CxUniverse` and the shipped middle contexts and no other context,
  so a context of the author's own holds what the author states across restarts and
  upgrades.
- *Engine.* `genlCx` is forced-monotonic and is stored in `CxUniverse` whichever context
  states it (`core.txt` declares `(forced_decontextualized_predicate genlCx)`). A cycle is
  refused at assert, so the context hierarchy is a partial order.
- *Maintenance.* A narrow extension placed under its base theory reaches only the contexts
  that opt in, and leaves every other reader of the base theory unchanged.

**Why not the other ways.** A context with no `genlCx` edge sees only itself: no type
reaches `thing` there, and no shipped declaration constrains it.

**Audit.** For each new context, state which shipped context it sees and which contexts see
it, and confirm the edges are in the context's own file.

## The real world and fiction

**Practice.** Place a context for an invented setting as a sibling of `CxRealWorld` under
`CxWell`, never below `CxRealWorld`. Restate in `CxRealWorld`, at `:monotonic`, a claim
that holds of the real world and that a fiction may break. In the fiction, deny the
`CxUniverse` claim `:monotonic` to state what the setting breaks.

**Example.** `CxRealWorld.txt`:

```clojure
(genlCx CxRealWorld CxWell)
(set/monotonic (disjoint animal vehicle))
```

Its header reads "A context representing an invented setting is a sibling under CxWell
instead of a context under CxRealWorld, so an exception a fiction states never reaches what
holds of the real world." `catbus_test` places a fiction context with
`(genlCx CxTotoro CxWell)`.

**Why.**

- *Engine.* An `except` or a sentence stated in a fiction is visible at the fiction and
  below it. A sibling of `CxRealWorld` is neither, so nothing a fiction states reaches the
  real world.
- *Engine.* `catbus_test` shows the outcomes. A fiction that denies `(disjoint animal
  vehicle)` `:monotonic` defeats the `:default` `CxUniverse` copy there, and a term that is
  both a cat and a bus clashes with nothing in the fiction. `CxRealWorld` does not see the
  denial, and its `:monotonic` copy stays believed. In a fiction that states no denial, a
  term that is both at `:default` is a dilemma `contradictions` reports. In `CxRealWorld`,
  a `:monotonic` cat membership beside a `:default` bus membership defeats the bus
  membership. [Ch. 24](24-strength.md#catbus-principle) says which strength decides each
  outcome.
- *Maintenance.* `CxNormalPhysicalConditions.txt` sees `CxRealWorld`, and its header says
  this "excludes every fiction". A theory that holds only of the real world goes under
  `CxRealWorld` in the same way.

**Why not the other ways.** A fiction below `CxRealWorld` inherits every real-world
restatement, so the overlap it was written to hold is the weaker member of a nogood there.

**Audit.** For each fiction context `CxF`, confirm `(sees? kb 'CxF 'CxWell)` holds and
`(sees? kb 'CxF 'CxRealWorld)` does not.

## except

**Practice.** To make a sentex not hold in one context and below, state
`(except (sentexHandle H))` in that context, where `H` is the handle of the sentex. Do not
retract a shared sentence to remove it from one reader.

**Example.** The shipped files state no `except`. A fiction states an overlap by denying
the separation ([The real world and fiction](#the-real-world-and-fiction)), which a
`:default` separation loses. An `except` is for a sentence the fiction must not read at
all, such as a `CxUniverse` rule whose conclusions the setting does not follow, or a
`:monotonic` sentence a denial cannot defeat.

**Why.**

- *Engine.* An `except` removes the sentex from reads, derivations and rules at the stating
  context and every context that sees it, and leaves the more general contexts untouched.
  A firing resting on the hidden sentex is blocked and swept below the `except`, and
  retracting the `except` re-derives what it hid, in every arrival order.
- *Engine.* An `except` hides a sentex at any strength, a forced-monotonic one included
  (`except_monotonic_test`). `except` is itself forced-monotonic: no nogood takes it OUT,
  and the hidden sentex comes back when the `except` is retracted or is itself excepted.
- *Engine.* `assert` refuses an `except` naming a handle no stored sentex holds, as
  `:unknown-handle`. A handle names a record and not a sentence, and handles are allocated
  in assertion order. An `except` accepted before its target existed would therefore hide
  whichever sentex next took that number, so the refusal keeps every `except` pointing at
  the sentex it was written for.
- *Maintenance.* The hidden sentence stays stored, and every other reader keeps it.
- *Maintenance.* `export-text!` writes no `except`: an `except` names its target by handle,
  and a handle means another record, or none, in the KB that reloads the text. The summary
  counts each one under `:skipped`. A KB moved by text loses its excepts, and `export!`
  keeps them.

**Why not the other ways.** Retracting the sentence removes it from every reader. A denial
stated in the context is a contradiction with the sentence, decided by strength, where an
`except` hides the sentence from the context and below with no contradiction to report.

**Audit.** For each `except`, name the context it is stated in, confirm the target is the
sentex meant, and confirm no reader that should keep the sentex sees that context.

## decontextualized_predicate

**Practice.** Declare `(decontextualized_predicate P)` for a predicate whose every fact is a
claim about the KB's vocabulary and holds for every reader. Do not declare it for a domain
relation whose facts belong to one theory or one dataset.

**Example.** `core.txt` lifts the relation marks:

```clojure
(decontextualized_predicate transitive)
(decontextualized_predicate symmetric)
(decontextualized_predicate functional)
```

`CxTra.txt` states `(set/monotonic (functional toolName))` in an opt-in theory, and the
lift makes the mark visible from every context that sees `CxUniverse`.

**Why.**

- *Engine.* Each `(P …)` fact, asserted or concluded, is copied into `CxUniverse`,
  supported by the original and the declaration. Retracting either withdraws the copy.
- *Engine.* The mark is read globally. A declaration stated anywhere lifts every `(P …)` in
  the KB, including facts in contexts that cannot see the declaration, so one declaration
  publishes a sibling theory's extent of `P` to every reader.
- *Engine.* The target is fixed at `CxUniverse` because the definitional checks are
  context-scoped. Every context that lifts sees `CxUniverse`, so the next write meets the
  copy and the settle weighs any clash where that write is made.
- *Maintenance.* A mark that holds in every context is stated once, in whichever theory
  defines the relation.

**Why not the other ways.** An `ist` rule that copies facts into another context is refused:
a rule may not use `ist` in any position. Restating the mark in every context that needs it
repeats one claim per reader.

**Audit.** For each new `decontextualized_predicate`, confirm every fact of the predicate is
true for every reader, and confirm the declaration sits in a schema context and not a data
context.
