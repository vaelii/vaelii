# Labeling: `do/` imperatives and brave/cautious solve

- **Covers:** how `do/labeling` reaches the ASP backend to commit one reversible
  resolution of a represented dilemma, and how the `(bravely S)` / `(cautiously S)` prover
  reads the same brave/cautious classification at query time without committing.
- **Not here:** the assumption-rule vocabulary and its persistent, inert labeling path →
  [solving.md](solving.md); the ASPIF encoding and solver backends →
  [asp.md](asp.md).
- **Assumes:** contradiction, defeat-class, context → [glossary.md](glossary.md).

How the ASP backend is reached from the KB, and why it is reached by *asking* rather
than by the engine deciding on its own.

## Why a caller has to ask

`vaelii.impl.asp.label` classifies a `Program` into `:true` / `:supportable` /
`:false` by brave/cautious enumeration, and materializes a labeling as a
specialization context. Nothing routes a KB to it on its own, and that is the
engine's stance rather than an oversight.

A coexisting `P`/`¬P` pair at `:default` is a **represented dilemma**
(docs/exceptions.md): both sides stay believed, `contradictions` hands over both
handles with both sides' justifications, and the engine arbitrates nothing. So
`settle` builds no `Program`, and `core/last-program` — which `label/classify` reads —
is **nil in exactly the cases where labeling is interesting**.

`asp_label_test`'s preamble names the bridge: *"an application that wants to rank a
dilemma can still do so through this machinery — it just has to ask for it rather than
have the engine decide behind its back."*

`do/labeling` is that asking.

## The `do/` channel

Imperatives enter through `assert`, as a virtual functor in the `do/` namespace, and
are **never stored**. The precedent is `ist`: a form given to `assert` that is not a
fact about the world but an instruction about what to do with one.

| namespace | meaning | example |
|---|---|---|
| `set/` | set a field on the enclosed rule | `(set/forwardRule (implies …))` |
| `do/` | perform an action; store nothing | `(do/labeling CxLabel)` |

Why the assert channel at all, when this could be a plain function call:

* One API. A labeling can be written into a seed EDN alongside the ontology it
  labels, and replayed by the same loader.
* It is *about* the KB in the KB's own language, which is the same argument that put
  the vocabulary's documentation in `comment` sentexes.
* What labeling actually does is assert — a `genlCx` edge and a set of
  strengthened copies — so the handles it made come back in the answer. `imperative/run`
  returns the imperative's **result map**, though, not a handle: an imperative stores
  nothing of its own, and `assert` returning one is the third shape it can answer with.
  `do/labeling`'s is `{:context :program :classification :handles}`.

### The one hard constraint: never inside a fixpoint

A `do/` form is refused as a rule antecedent, a rule consequent, an `exceptWhen`
query, and anything derived. This is not tidiness. Forward chaining is a fixpoint
whose defining property is that the same knowledge in any order yields the same
beliefs; an imperative that runs *during* it would execute a number of times that
depends on firing order, and would mutate the KB the fixpoint is still computing over.
Order independence and locality are the two invariants the whole TMS is built on
(docs/nmtms.md), and a side effect inside the fixpoint breaks both at once.

So `do/` is legal only as a top-level `assert`, where it happens once, after settling,
at a point the caller chose. It throws `:type :not-assertible` anywhere else.

## `(do/labeling Ctx)`

Four steps, in an order the imperative fixes so a caller cannot get it wrong:

1. **Build a `Program` from the current dilemmas.** Not from `last-program` — see
   above, that is nil here. `contradictions` supplies the nogoods, their members are
   the contested assumptions, and `label/sides-content` supplies what each side asserts
   (the settle path has a private helper of its own for the same job).
   Known-true content is never contested, so it enters as `:fixed` background exactly
   as it would have from `settle`.
2. **Classify** brave/cautious over the optimal answer sets.
3. **Record** the `Program` in the KB's `:program` slot, so `last-program` and
   `label/classify` answer about this labeling afterwards. `settle` never writes that
   slot for a dilemma — it builds no Program for one — so nothing is overwritten.
4. **Materialize** one optimal labeling into `Ctx` and return the handles.

Classification runs *before* materialization because materializing entrenches:
what it writes are ordinary assertions, and an assertion is evidence, so the recorded
side ends up in a second nogood against its rival. A tie that classifies
`:supportable` on both sides classifies `:true`/`:false` once labeled. That is not a
bug — it is what recording a choice means — but it means the classification must be
taken first. Making the imperative do both in one call is how that ordering stops
being a thing a caller has to remember.

### Where the labeling comes from, and why it differs from `label-context`

`label/label-context` reads the labeling from the **TMS**, and `label.clj`'s namespace
docstring is emphatic about refusing to re-solve: *"A re-solve would usually agree, and
'usually' is not a property worth building on."*

`do/labeling` on a dilemma reads it from the **solve**. That is not a reversal. Both
follow the same rule — *report what actually decided it* — applied to two different
situations:

| situation | who decided | so read from |
|---|---|---|
| a tie `settle` arbitrated | the engine committed to one side | the TMS |
| a dilemma `settle` declined | nobody; **both sides are IN** | the solve |

Reading current belief for a dilemma would copy *both* sides of the contradiction
into the labeling context, which just recreates the dilemma one level down. There is
no committed answer to be faithful to, so the solve is the only thing that decides.

### `Ctx` inherits, and the labeling is recorded by strengthening

`Ctx` is a `genlCx` specialization of the base, and each kept assumption is
re-asserted inside it at `:monotonic`. Nothing needs to be said about the side that
lost: the strengthened copy out-ranks it and `decide-nogood` defeats the strictly
weaker member. So `Ctx` is a **world** — the uncontested background is inherited, and
the contested atoms are decided within it.

Both halves of that are required, and the two neighbouring designs are the
argument:

* **A copy at `:default`** merely ties with the side it is supposed to beat, so it
  reports a second dilemma instead of deciding the first — `contradictions` **1 to 2**,
  and a second labeling would report it three times. Entrenchment is correct for
  `label-context`, where the loser is already defeated and the copy meets no live
  rival; here both sides are IN and a tying copy walks straight into a fresh nogood.
* **A detached `Ctx`** avoids that double-report and leaves the base bit-for-bit
  untouched, but then holds only the labeled literals and inherits no background — a
  record to read rather than a world to query.

The `:monotonic` copy into an inheriting context leaves `contradictions` at **1**: the
base still holds both sides, and inside `Ctx` the dilemma is decided rather than
duplicated.

### The commitment is scoped to `Ctx`

The strengthened copy and the losing side form a nogood whose vantage is `Ctx`, since
`Ctx` sees the base and the base does not see `Ctx`. The losing side is defeated at `Ctx`
and below, and nowhere else ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)): a
read from `Ctx` finds one side, and a read from the base finds both.

This is the one place where "the KB represents dilemmas, it does not solve them"
bends, and it bends only inside `Ctx`:

* The engine still refuses to arbitrate **on its own**. `settle` decides no
  default/default clash; the commitment happens only because a caller wrote the
  imperative, and it binds the context the caller named.
* It is undoable. `retract!` on the returned handles revives the dilemma inside `Ctx`.

Rival labelings stand **side by side**: two `do/labeling` calls naming two contexts give
two sibling contexts, each deciding the dilemma its own way, while the base reports the
one dilemma throughout.

### The labeling solve and the classification solves must agree

`do/labeling` runs **three** solves: brave and cautious for the classification, and one
more for the labeling itself. The third is irreducible — brave and cautious give the
union and the intersection of the optima, and neither is a single answer set — so the
labeling has to be solved for separately.

Separate solves have to be *reconciled*. `classify-program` needs to enumerate optima,
which only ASP does, so it goes straight to the backend and ignores `(:solver kb)`. A
labeling taken from the installed solver — on a default KB, the greedy `local-solver` —
would answer from a different search procedure, and the two diverge in practice.
Measured on two nogoods sharing a member, where greedy spends two defeats and the
optimum spends one:

```
stub  defeats {1,3} -> labels {2}     classification: {:true {1,3} :false {2}}
ASP   defeats {2}   -> labels {1,3}
```

The stub's labeling keeps an assumption holding in **no** optimum and drops two
holding in **every** one. Under commit semantics that materializes an impossible world
and defeats, inside `Ctx`, the atoms classification calls forced.

Two things hold them together. The labeling solve uses the **ASP edge solver whenever a
backend is reachable**, deliberately bypassing `(:solver kb)` so both answers come from
one search procedure; with no backend the two degrade together, since `classify-program`
then claims nothing and any labeling satisfies it. And the invariant is **checked before
committing** rather than assumed:

```
:true ⊆ labeled        :false ∩ labeled = ∅
```

A violation throws `:type :labeling-inconsistent`. Refusing to commit is the right
failure: an impossible labeling entrenched as monotonic assertions is much worse than
an error.

The nogoods the engine builds have two members apiece — a `P`/`¬P` pair, a definitional
clash — and greedy cannot diverge from optimal on a plain pair, so no sequence of
`assert`s reaches the check. It is pinned at the `Program` level instead, where a
divergence can be handed to it directly.

### One caveat about which level you ask at

`Ctx` is consistent at level 3 (`:visible`) — the belief-filtered view of stored
facts — and that is the level at which "is this world consistent" means anything.

One neighbouring level will mislead you, and one will not:

* **`sentexes-matching` (level 2) is context-exact.** It does not show inherited facts at all, so
  it reports the background missing from `Ctx` even though `Ctx` sees it.
* **`prove` and `query` (level 7) expand rules, and agree with belief about the
  answers.** Backward chaining opens the rule that concluded the defeated side and
  proves it again — and then drops the answer, because belief has already decided that
  datum is OUT under the current state (`res/defeated-answer?`,
  [inference.md](inference.md)). So both sides read the same way here as at level 6,
  where `ask` answers from what is stored or cached and no member of its prover registry
  expands a rule ([levels.md](levels.md)). What the two levels still differ about is
  *reach* — level 7 answers what a rule derives and level 6 does not — never about which
  side of a settled clash holds.

### Why an arbitrary pick is legitimate here

The engine refuses to arbitrate a dilemma because doing so silently would destroy the
thing an application wants to rank. Three things make the same pick acceptable when it
comes through `do/labeling`:

* **It was asked for.** The caller wrote the imperative.
* **It is reversible.** Retracting the returned handles revives the dilemma exactly as
  it was, so the commitment is a move that can be taken back rather than knowledge
  destroyed. This is checked, not assumed.
* **It is one of several, and says so.** The classification recorded alongside it
  marks every side `:supportable` that genuinely was, so the context is legible as one
  choice among the optima rather than as the answer. Rival answer sets can be built as
  sibling contexts and compared.

### Determinism

Which optimum is materialized may not depend on assertion order, on handle ids, or on
solver nondeterminism — the engine-wide invariant (docs/nmtms.md) does not get an
exception for being inside a solver. The choice is keyed on **content**, through the
same `solve/content-key` that orders the stub solver, and the ASP encoding's
three-level objective already ends in a content-keyed tiebreak for this reason.

### Without an ASP backend

`local-solver` produces one labeling deterministically but cannot enumerate optima. So
on a plain build:

* materialization works — the stub's pick is well-defined and content-keyed;
* classification reports every contested assumption `:supportable`, which is honest
  (each *is* one of several) and never overclaims `:true`.

A build without clingo behaves like one with it, minus the ability to distinguish
forced from arbitrary — which is precisely the thing enumeration buys.

## Reading brave/cautious without committing: `(bravely S)` / `(cautiously S)`

`do/labeling` commits — it re-asserts the kept side at `:monotonic` and defeats the loser
everywhere, taking `contradictions` from 1 to 0. That is right for making a choice, but it
is the wrong tool for merely *asking* which beliefs are forced and which are arbitrary,
because asking would destroy the dilemma it asks about. The `(bravely S)` / `(cautiously
S)` prover answers that question as a read.

```clojure
(v/add-reasoner kb :brave-cautious)          ; opt in, like any other reasoner
(v/ask? kb '(bravely    (pacifist Nixon)) 'CxUniverse)   ; => true — S in some optimum
(v/ask? kb '(cautiously (pacifist Nixon)) 'CxUniverse)   ; => false — not in every optimum
```

`(cautiously S)` holds when `S` is in **every** optimal labeling of the current dilemmas,
`(bravely S)` when `S` is in **some** — the cautious and brave halves of one classification
the prover reads through `label/classify-dilemmas`: the ASP backend when one is reachable
(`dilemma-program` then `classify-program`), and otherwise the solve-free JTMS bracket
below. Over a datum in no dilemma both reduce to ordinary belief, since every resolution
agrees there. The read **commits nothing**: after asking, belief, `contradictions` and
`last-program` are exactly as they were.

Three limits, none silent:

* **It is opt-in**, so the ASP stack stays off a KB's load path until asked
  (docs/asp.md). Without a backend the prover reads the solve-free bracket below rather
  than an enumeration, so `bravely` and `cautiously` still answer.
* **`bravely` / `cautiously` are not assertible** (they join `unknown` and the aggregates as
  reserved query operators, docs/naming.md): a stored one would be a computed value with no
  way to keep it current.
* **Ground `S` only, and a query rather than an antecedent.** An open `(bravely (pacifist
  ?x))` is not applicable — the same restraint `different` takes. As a rule antecedent the
  answer carries no support (the prover is not a `SupportingProver`), so the forward join
  drops it and it derives nothing. Threading its support — the dilemma's contested handles —
  so a rule could rest on it is deferred until a use asks for it.

### The solve-free bracket

`label/classify-dilemmas` reads the ASP backend when one is reachable and
`label/classify-local` otherwise. `classify-local` classifies the current dilemmas from
the JTMS dependency graph, with no answer-set enumeration and no backend, so a plain build
answers `bravely` and `cautiously` rather than reporting every contested datum
`:supportable`.

It rests on one JTMS read. `jtms/grounded-in-region` recomputes belief with a set of datums
**forced OUT** — the forward consequence closure of that set, and within it the datums that
stay believed, belief outside the closure read per datum rather than materialized
(`grounded-forcing-out` splices the same read back into full belief, equal to `(jtms/defeat
…)` of the set). A **resolution** is a minimum-cardinality set of dilemma members whose
forcing OUT satisfies every nogood — leaves no nogood with all its members still believed —
which is a dilemma set's optimal labelings. `classify-local` reads belief under each
resolution and splits a believed datum by which resolutions keep it: `:true` when every
resolution keeps it (skeptical), `:supportable` when some but not every do (credulous),
`:false` when none do.

`(hasEthicalStance Nixon)` drawn from **both** the pacifist and non-pacifist side is `:true`:
every resolution keeps one side, so one support survives. `(opposesWar Nixon)` resting on
the pacifist side alone is `:supportable`, so `(cautiously (opposesWar Nixon))` is false —
where the member-only `classify-program` leaves that conclusion to base belief (which
believes both sides and so reports it cautious). `(weird Nixon)` drawn from `(and (pacifist
Nixon) (not (pacifist Nixon)))` is `:false`: it is believed only because base belief holds
both sides at once, and every resolution drops one, so it holds in none.

**Coupled dilemmas are enumerated together, independent ones apart.** Two nogoods that share
a member, or that move a member of each other through the derivation graph, form one cluster
(`cluster-indices`), and a cluster's resolutions come from `min-resolutions`, which
enumerates the cluster's member subsets by increasing size and keeps the first size at which
a subset satisfies every nogood. It searches whole subsets rather than branching on one
nogood's members, which is what keeps it belief-faithful: a member a defeat drops by cascade
counts as forced OUT, so a subset that forces no member of a nogood can still satisfy it —
defeating `pb` satisfies `pa`'s nogood when `¬pa` derives from `pb`. A datum is classified by
the joint resolutions of the clusters that move it — the cartesian product of those clusters'
optima, since a cluster that does not move the datum leaves it at base whatever it resolves to.
Two coupled nogoods `{a,b}` and `{b,c}` resolve by defeating `b` alone, so `a` and `c` are
`:true` and `b` is `:false` — the outcome a per-dilemma reading misses, since dropping `a`
looks like a resolution of a's own dilemma until the shared `b` shows it is not minimal. And a
`(f N)` from `(and (e1 N) (e2 N))`, where `e1` and `e2` are each `:true` in a separate diamond,
is `:true`: it holds in every combination of the two diamonds' resolutions.

`classify-local` is **sound** — nothing is `:true` that a resolution gives up, nothing
`:false` that one keeps — and **complete for a datum whose clusters it enumerates**: the one
cluster its support touches, or the several whose product of resolutions stays within
`VAELII_CLASSIFY_MAX_JOINT_OPTIMA`. The residual a backend still refines is a datum whose
product of clusters exceeds that cap, or a cluster past `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS`
or the `VAELII_CLASSIFY_RESOLUTION_BUDGET` search ceiling; each degrades to `:supportable`,
which claims neither forced nor excluded. An operator tunes each cap through its
`VAELII_CLASSIFY_*` switch (docs/operations.md). Its cost is
the clusters' consequence closures: **linear** in the number of independent dilemmas
(`grounded_forcing_out_test`), exponential only inside one interacting cluster or across the
clusters one datum joins, and capped at both.

## Naming

No `!`. Labeling creates a context and asserts into it; retracting the handles it
returns undoes it. The `!` convention marks operations that *lose* knowledge, and this
only adds.

## Status

`labeling_test` covers this channel in 14 tests: the `do/` channel itself, the
dilemma-to-`Program` bridge (`label/dilemma-program`), the solve-sourced labeling, and
`label/label-dilemmas`. `label/classify-program`, `label/label-context`,
`edge/edge-solver` and the clingo/clasp backends are `asp_label_test` /
`asp_edge_test`'s subject. The `(bravely S)` / `(cautiously S)` prover and the
prover-driven `classify-local` classifications are `asp_prover_test`'s; the backend-free
property tests for the solve-free bracket (`jtms/grounded-forcing-out`, `classify-local`
order-independence and scaling) are `grounded_forcing_out_test`'s.

Limits, none of them silent:

* **`sentexes-matching` reports the inherited background missing** — the caveat above.
  It is context-exact, so it shows a labeled context's own extent and nothing it sees
  through `genlCx`. It holds in the base context too; a labeled context is only where
  you are most likely to trip over it.
* **`label-context` and `label-dilemmas` overlap.** The former materializes a labeling
  the engine committed to and reads the TMS; the latter commits to one and reads the
  solve. Both are correct for their situation, and the table above says which is
  which.
