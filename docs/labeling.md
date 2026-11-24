# Labeling: `do/` imperatives and brave/cautious solve

- **Covers:** how `do/labeling` commits one reversible resolution of a represented
  dilemma, and how the `(bravely S)` / `(cautiously S)` prover
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

`do/labeling` is the bridge: an application that wants a dilemma ranked asks for it.

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
   the contested assumptions, and `label/sides-content` supplies what each side asserts.
2. **Classify** brave/cautious over the optimal resolutions, read from the dependency
   graph (the solve-free bracket below).
3. **Record** the `Program`, carrying that classification, in the KB's `:program` slot,
   so `last-program` and `label/classify` answer about this labeling afterwards. `settle` never writes that
   slot for a dilemma — it builds no Program for one — so nothing is overwritten.
4. **Materialize** one optimal resolution into `Ctx` and return the handles.

Classification runs *before* materialization because materializing entrenches:
what it writes are ordinary assertions, and an assertion is evidence, so the recorded
side ends up in a second nogood against its rival. A tie that classifies
`:supportable` on both sides classifies `:true`/`:false` once labeled. That is not a
bug — it is what recording a choice means — but it means the classification must be
taken first. Making the imperative do both in one call is how that ordering stops
being a thing a caller has to remember.

### Where the labeling comes from, and why it differs from `label-context`

`do/labeling` on a dilemma reads the labeling from a **resolution** computed for the
purpose, since `settle` declined the dilemma and **both sides are IN**. It records the kept
assumptions with the `Program` as `:keep`. `label/label-context` copies that set, less each
assumption its own context no longer believes. Reading current belief for a dilemma would
copy *both* sides of the contradiction into the labeling context, which recreates the
dilemma one level down
(`asp_label_test/label-context-copies-the-side-label-dilemmas-kept-while-its-own-context-believes-it`).

### `Ctx` inherits, and the labeling is recorded by strengthening

`Ctx` is a `genlCx` specialization of the base, and each kept assumption is
re-asserted inside it at `:monotonic`. Nothing needs to be said about the side that
lost: the strengthened copy out-ranks it and `decide/verdict` defeats the strictly
weaker member. So `Ctx` is a **world** — the uncontested background is inherited, and
the contested atoms are decided within it.

The `:monotonic` copy into an inheriting context leaves `contradictions` at **1**: the
base still holds both sides, and inside `Ctx` the dilemma is decided rather than
duplicated. A copy at `:default` and a detached `Ctx` each fail
([defenses.md](defenses.md#a-labelings-copies-are-monotonic-in-an-inheriting-context)).

### The commitment is scoped to `Ctx`

The strengthened copy and the losing side form a nogood whose vantage is `Ctx`, since
`Ctx` sees the base and the base does not see `Ctx`. `Ctx` and the readers below it decide
the nogood, and no reader above it does ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)): a
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

### The labeling and its classification must agree

`do/labeling` reads both from one place: the optimal resolutions the solve-free bracket
below enumerates from the dependency graph. The labeling is the resolution whose members
sort first by content, and an assumption is kept when it stays believed with that
resolution forced OUT, so a member a defeat drops by cascade is dropped with it. A
`Program` encodes no derivation between members, and a solve over it misses the cascade.
With three defaults where `b` rebuts both `a` and `c` and each rebuts `b`, the one optimal
resolution defeats `b`, and the `¬a` and `¬c` it derives go with it; a `Program`'s optima
spend a defeat per dilemma, and one of them gives up `a`, `b` and `c` together.

A cluster past the bracket's caps is labeled by a solve over its dilemmas' `Program`
instead, and with a backend a member of one whose members derive from none of each other is
classified by brave and cautious solves, where the `Program` is exact. That is up to three
solves, and separate solves have to be *reconciled*.

Two things hold them together. The labeling solve uses the **ASP edge solver whenever a
backend is reachable**, bypassing `(:solver kb)` so both answers come from one search
procedure ([defenses.md](defenses.md#a-labelings-solve-ignores-the-installed-solver-when-a-backend-is-reachable)). And the invariant is **checked before
committing** rather than assumed:

```
:true ⊆ labeled        :false ∩ labeled = ∅
```

A violation throws `:type :labeling-inconsistent`. Refusing to commit is the right
failure: an impossible labeling entrenched as monotonic assertions is much worse than
an error.

The nogoods the engine builds have two members apiece — a `P`/`¬P` pair, a definitional
clash — and greedy cannot diverge from optimal on a plain pair, so no sequence of
`assert`s reaches the check. It is asserted at the `Program` level instead, where a
divergence can be handed to it directly.

### One caveat about which level you ask at

`Ctx` is consistent at level 3 (`:visible`) — the belief-filtered reading of stored
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
exception for being inside a solver. The choice is keyed on **content**: the resolution
whose members' `solve/content-key`s sort first, the key that orders the stub solver, and
the ASP encoding's three-level objective ends in a content-keyed tiebreak for the clusters
a solve labels.

### Without an ASP backend

`local-solver` produces one labeling deterministically but cannot enumerate optima. So
on a plain build, for a cluster past the bracket's caps:

* materialization works — the stub's pick is well-defined and content-keyed;
* classification reports every contested assumption `:supportable`, which is correct
  (each *is* one of several) and never overclaims `:true`.

That holds for a cluster past the bracket's caps only. Everywhere the bracket enumerates,
labeling and classification read the dependency graph, and a build without clingo labels
and classifies as one with it does.

## Reading brave/cautious without committing: `(bravely S)` / `(cautiously S)`

`do/labeling` commits — it re-asserts the kept side at `:monotonic` and defeats the loser
at `Ctx` and below, while the base still reports the dilemma in `contradictions`. That is right for making a choice, but it
is the wrong tool for merely *asking* which beliefs are forced and which are arbitrary,
because asking would destroy the dilemma it asks about. The `(bravely S)` / `(cautiously
S)` prover answers that question as a read.

```clojure
(v/add-reasoner kb :brave-cautious)          ; opt in, like any other reasoner
(v/ask? kb '(bravely    (pacifist Nixon)) 'CxUniverse)   ; => true — S in some optimum
(v/ask? kb '(cautiously (pacifist Nixon)) 'CxUniverse)   ; => false — not in every optimum
```

`(cautiously S)` holds when `S` is in **every** optimal labeling of the dilemmas the asking
context reads, `(bravely S)` when `S` is in **some** — the cautious and brave halves of one
classification the prover reads through `label/classify-datum`: the solve-free JTMS bracket
below, with or without a backend. Over a datum no dilemma moves — neither a
member nor derived from one — both reduce to ordinary belief, since every resolution agrees
there. The read **commits nothing**: after asking, belief, `contradictions` and
`last-program` are exactly as they were.

**The classification is per asking context.** The prover reads `S` as a ground `ask` does:
the sentexes of `S` stored in the context's `genlCx` ancestor set that the context believes
(`res/believed-at?`) and sees (`exc/hidden-fn`). A sentex a placed defeat hides from the
context is not read there, though it is IN in the network. Each of those sentexes is
classified against the dilemmas `contradictions` reports to the same context
(`clashes/contradictions-at`), so a dilemma placed in a context the reader does not see
classifies nothing for it. `S` stored in two visible contexts is two sentexes, and `S` holds
in a labeling when either does, so its class is the strongest of theirs: `:true` over
`:supportable` over `:false`. A believed sentex that no dilemma of the context moves is
believed in every labeling, so it reads `:true`. In the Nixon diamond over time (`temporal_diamond_test`),
`(pacifist Dick1)` is stored in the life and the republican denial in the term: the youth,
the life and the retirement read no dilemma and answer both modalities true, and the term
reads the dilemma and answers each side brave and not cautious.

A backend refines only a **`:refinable`** member: one in a cluster the bracket did not
enumerate, whose members move none of each other — where a `Program`, which encodes no
derivation between members, is exact. Everywhere else a backend changes no answer. It
classifies the member's **member component**: the dilemmas that share a member with one
naming it, directly or through a chain. The optima of dilemmas that share no member are every
combination of each component's optima, and a member's class over the whole program is its
class over its component. The whole program's optima multiply across independent dilemmas
(twenty Nixon diamonds have 2^20), and one component's do not. Each classification is held
on the KB per asking context until the change clock moves, so two asks with no write between
them classify once (`lein perf`'s `brave-ask-between-writes`), and an ask after a write reads
none of the dilemmas placed in contexts the asking context does not see
(`cautious-ask-beside-unseen-dilemmas`).

Three limits, none silent:

* **It is opt-in**, so the ASP stack stays off a KB's load path until asked
  (docs/asp.md). The bracket below needs no backend, so `bravely` and `cautiously` answer
  on a plain build.
* **`bravely` / `cautiously` are not assertible** (they join `unknown` and the aggregates as
  reserved query operators, docs/naming.md): a stored one would be a computed value with no
  way to keep it current.
* **Ground `S` only, and a query rather than an antecedent.** An open `(bravely (pacifist
  ?x))` is not applicable — the same restraint `different` takes. As a rule antecedent the
  answer carries no support (the prover is not a `SupportingProver`), so the forward join
  drops it and it derives nothing.

### The solve-free bracket

`label/classify-local` classifies the current dilemmas from the JTMS dependency graph,
with no answer-set enumeration and no backend. `label/classify-datum` and
`label/label-dilemmas` read it on every build.

It rests on one JTMS read. `jtms/grounded-in-region` recomputes belief with a set of datums
**forced OUT** — the forward consequence closure of that set, and within it the datums that
stay believed, belief outside the closure read per datum rather than materialized. A **resolution** is a minimum-cardinality set of dilemma members whose
forcing OUT satisfies every nogood — leaves no nogood with all its members still believed —
which is a dilemma set's optimal labelings. `classify-local` reads belief under each
resolution and splits a believed datum by which resolutions keep it: `:true` when every
resolution keeps it (skeptical), `:supportable` when some but not every do (credulous),
`:false` when none do. A datum the read context does not believe, or with no context its
own context, is in no class, so a datum a placed `defeat` removes is never `:true`.

`(hasEthicalStance Nixon)` drawn from **both** the pacifist and non-pacifist side is `:true`:
every resolution keeps one side, so one support survives. `(opposesWar Nixon)` resting on
the pacifist side alone is `:supportable`, so `(cautiously (opposesWar Nixon))` is false,
where base belief, which believes both sides, would report it cautious. `(weird Nixon)`
drawn from `(and (pacifist Nixon) (not (pacifist Nixon)))` is `:false`: it is believed only
because base belief holds both sides at once, and every resolution drops one, so it holds
in none.

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
`VAELII_CLASSIFY_MAX_JOINT_OPTIMA`. A datum whose product of clusters exceeds that cap, or
in a cluster past `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS` or the
`VAELII_CLASSIFY_RESOLUTION_BUDGET` search ceiling, degrades to `:supportable`, which claims
neither forced nor excluded. A backend refines the members of such a cluster when it is
`:refinable`, and nothing else. An operator tunes each cap through its
`VAELII_CLASSIFY_*` switch (docs/operations.md). Its cost is
the clusters' consequence closures: **linear** in the number of independent dilemmas
(`grounded_in_region_test`), exponential only inside one interacting cluster or across the
clusters one datum joins, and capped at both.

## Naming

No `!`. Labeling creates a context and asserts into it; retracting the handles it
returns undoes it. The `!` convention marks operations that *lose* knowledge, and this
only adds.

## Status

`labeling_test` covers this channel: the `do/` channel itself, the
dilemma-to-`Program` bridge (`label/dilemma-program`), the solve-sourced labeling, and
`label/label-dilemmas`. `label/classify-program`, `label/label-context`,
`edge/edge-solver` and the clingo/clasp backends are `asp_label_test` /
`asp_edge_test`'s subject. The `(bravely S)` / `(cautiously S)` prover and the
prover-driven `classify-local` classifications are `asp_prover_test`'s; the backend-free
property tests for the solve-free bracket (`jtms/grounded-in-region`, `classify-local`
order-independence and scaling) are `grounded_in_region_test`'s.

Limits, none of them silent:

* **`sentexes-matching` reports the inherited background missing** — the caveat above.
  It is context-exact, so it shows a labeled context's own extent and nothing it sees
  through `genlCx`. It holds in the base context too; a labeled context is only where
  you are most likely to trip over it.
