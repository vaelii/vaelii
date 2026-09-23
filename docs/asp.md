# The ASP backend

- **Covers:** how the edge solver renders a contested `Program` to ASPIF and solves it
  with clingo or clasp, deterministically.
- **Not here:** the assumption-rule and constraint vocabulary that builds a `Program` in
  the first place → [solving.md](solving.md); committing one labeling of a dilemma into
  base belief → [labeling.md](labeling.md); writing for this engine when answer set
  programming is the language you already think in, which is the paradigm rather than
  this machinery → [from-asp.md](from-asp.md).
- **Assumes:** edge solver, nogood, brave/cautious → [glossary.md](glossary.md).

The real answer-set solver behind the `Solver` protocol. Two layers: a
general-purpose ASP toolkit that
knows nothing about vaelii, and one namespace that renders a
[`Program`](nmtms.md) to it.

```
vaelii.impl.types.solve/Solver          the protocol   (docs/nmtms.md)
  └── vaelii.impl.asp.edge        Program  ->  ASPIF,  answer set -> {:defeat :violated}
        └── vaelii.impl.asp.solver          backend selection
              ├── vaelii.impl.asp.clingo    in-process libclingo, via JNA
              └── vaelii.impl.asp.clasp     subprocess, ASPIF on stdin
        └── vaelii.impl.asp.aspif           the emitter
        └── vaelii.impl.asp.atoms           atom ids and labels

vaelii.impl.asp.label             brave/cautious classification; labeling contexts
```

## Installing it

Nothing uses it until you say so — `local-solver` remains the default, so a build
without clingo behaves exactly as before.

```clojure
(v/set-solver kb :asp)
```

The name is the whole of it — `set-solver` resolves the backend at runtime, so a caller
needs nothing from `vaelii.impl.asp.*` and nothing here reaches the load path of a KB
that never asks. `edge-solver` degrades rather than fails. With no backend reachable it delegates to
`solve/local-solver`, so installing it is always safe, and `(solver/available?)` tells
you whether the selected backend can solve in this environment. Which of the two runs is
not exposed: it is a routing decision the solver makes per program, from the config, from
whether libclingo loaded, and from the program's size.

## Getting a solver

Either backend is enough; both is better.

```sh
brew install clingo          # provides the clingo binary, libclingo, and clasp
lein with-profile +with-clingo test     # points JNA at /opt/homebrew/lib
```

- **clingo** runs in-process through raw JNA — no JNI, no generated bindings, no
  clingo Java library. Fastest for small programs, which is the common case here.
- **clasp** is a subprocess taking ASPIF on stdin and returning JSON. It is the
  deliberate fallback for long-running processes, where an in-process native crash
  would take the JVM with it.

`solver.clj` picks per program size (`VAELII_CLINGO_MAX_BYTES`, default 3000 bytes:
clingo below, clasp above) and loads the clingo namespace lazily via
`requiring-resolve`, so JNA stays genuinely optional. Force one with
`-Dvaelii.asp.solver=clingo|clasp` or `VAELII_ASP_SOLVER`.

The in-process solve writes no ASPIF text. `backend-batch!` interns each program atom as
the symbol `a(<id>)` carrying its label and emits every rule into a live control through
the `clingo_backend_*` accessors; a model's true atoms come back through
`clingo_model_symbols` and map to labels through that symbol association. `clasp` still
reads the rendered ASPIF text. `vaelii.impl.asp.clingo` also holds an incremental session
API — `open-session`, `add-program!`, `declare-external!`, `assign-external!`,
`solve-session`, `close-session!`. A session grows one live control a batch at a time and
changes an external atom's truth between solves without re-grounding. No engine path opens
a session.

### Why size picks the backend

In-process clingo saves the subprocess fork — about 4× faster cold on a small program —
and pays a steeper per-solve slope that loses at scale. The driver is marshaling rather
than model count: an in-process solve makes one JNA call per ground statement to emit the
program into the backend, and then JNA-marshals every witness symbol back across the JNI
boundary.
Both costs scale with program and witness **size**, in every mode rather than only under
brave/cautious enumeration — which is what makes byte length a sound cross-mode proxy, and
one cutoff enough for all of them.

Measured: classify crosses over around 2.9 KB (closure around 80), and a large `:label`
solve also loses in-process — roughly half a second out to a subprocess clasp against
roughly two-thirds of one in-process. Hence the 3000-byte default.

The cutoff is AUTO-mode only; an explicit `VAELII_ASP_SOLVER=clingo` uses clingo whatever
the size. Rerouting a large program to clasp is safe because a program is only ever plain
ASP, which both backends answer identically. And the cutoff yields to availability: on a
machine with libclingo loaded and no `clasp` executable, AUTO keeps large programs
in-process too — a slower solve is a cost regression, where routing to a binary the
machine does not have would be a refusal `available?` had promised away. The clasp probe
forks a process to answer, so it is made once per JVM.

### The time limit

`VAELII_ASP_TIME_LIMIT` (default 60 seconds; 0 lifts it) bounds **one solve**, on both
backends: clasp takes it as `--time-limit`, and in-process clingo — whose control accepts
solver options only and refuses that flag — runs the search asynchronously and cancels
the handle when the budget is spent.

**One solve is not one operation, and the difference is a multiplier.** A solve runs on
the single writer, so an operation that makes several holds every write behind the sum of
their budgets, not behind one:

| operation | solves | worst case |
|---|---|---|
| `do/label` (`:all`, `:one`, `:sat`) | 1 | 1 × budget |
| `edge-solver` on one program | 1 | 1 × budget |
| `classify` / `classify-program` | 2 (`classify-both` runs cautious then brave) | 2 × budget |
| `do/labeling` (`label-dilemmas`) | 3 (classification's two, then the labeling) | 3 × budget |
| one `settle` | one per defeat round | up to \|contested\| × budget |

Measured at `VAELII_ASP_TIME_LIMIT=1` on a 78-atom program that finishes under neither:
`classify-both` returns after **about two budgets**, a single `:label` or `:all-optima`
solve after **about one**. Both are correct — every individual solve was cancelled on
time, and what the readings show is the multiplier rather than a wall clock.

So size the variable against the *solve*, and read the table for what an operation then
costs. `asp_edge_test` and `solve_context_test` pin the counts, because a doc that names
them and code that changes them is worse than either alone.

An interrupted solve that found no model reports `:interrupted`, and **that is not an
answer**. A backend's result is an answer set at `:optimum` or `:sat`, and — since 0.18.0,
in `:label` mode — a best model reached before the interrupt is `:best-effort`, an answer
whose optimality is unproven. `:interrupted` and `:unknown` carry no witness, and every
reader maps an atom's absence to *defeated* or *not kept* — read as an answer, an empty
result would defeat every contested assumption and label every choice head false.

### Refuse rather than degrade, whenever a backend is present

`edge-solver` falls back to `local-solver` in two cases: **no backend at all**, and a
backend's definite `:unsat` (below). With no backend the two degrade together and stay consistent for free, because `classify-program`
without a backend reports every contested assumption `:supportable` and claims nothing.

With a backend present the fallback would be a different solver's answer, and the two
solvers disagree. On two nogoods sharing a member the stub spends two defeats where the
optimum spends one:

```
stub  defeats {1,3} -> labels {2}      ASP classification  {:true {1,3} :false {2}}
ASP   defeats {2}   -> labels {1,3}
```

Pairing that stub labeling with an ASP classification is what `check-agrees` reports as
`:labeling-inconsistent`, blaming the encoding for a disagreement the fallback
introduced. Across a settle's defeat rounds it is worse: round 1 interrupted and round 2
not gives a belief set neither solver would produce, differing run to run on identical
knowledge — and the order-independence invariant in [nmtms.md](nmtms.md) is a claim about
*knowledge*, which a wall clock is not.

So with a backend present an unanswered solve **decides nothing**: `{:defeat #{}
:violated [...] :error e}`, every contested assumption left standing, the failure logged
at `:error` and named in `:error` for a caller that can act on it. The brave/cautious
classification behind `classify` and `label-dilemmas` refuses with `:solver-failed` rather
than return a world nobody computed — `label-dilemmas` by raising that same `:error`, since
an empty defeat set is otherwise the perfectly good answer *keep everything*. `do/label` in
`:one` or `:sat` mode is the one reader that does not refuse when a model was found first:
it returns that model with `:best-effort? true`, a valid labeling whose optimality the
interrupt left unproven. The belief path is unaffected — `edge-solver` treats
`:best-effort` as undecided, so no wall clock moves a belief.

`:unsat` keeps its own reading and is not this case: a definite *no model*, the same
answer in every run, so it costs the invariant nothing. The edge solver degrades on it,
`kept-of` keeps nothing, and an enumeration is empty. It should not arrive from a settle
at all — every contradiction the engine sends is soft.

### A backend that throws

Same policy, same reason. The backends fail in several currencies — clingo's
`:solver-failed` naming the native call that returned zero, clasp's
`:solver-unavailable` when the binary is gone, a JNA `Error` against a missing or
wrong-ABI libclingo — and `edge-solver` catches all of them at the boundary, because the
the boundary is where a native failure crosses into the engine.

Left to propagate, such a throw unwinds whatever arbitration is in progress.
`settle`'s `resolve-contradictions` reaches the solver *after* an earlier round has
already mutated the TMS, so the exception would escape with round 1's defeats landed,
`:conflicts` stale, `settle-finish` never reached and `reset-touched!` never run — a KB
half-way through an arbitration nobody can finish. Deciding nothing leaves it exactly as
the round found it, and the failure comes back as `:error` for a caller to rank.

The imperative readers are not mid-arbitration, so they still throw: a refusal there
adds no work and says more than a result would.

## The encoding

A contested assumption becomes a **choice atom**: true means believed, false means
defeated. Known-true (`:fixed`) members of a contradiction get no atom at all —
they hold by assumption, which is what makes them background rather than something
the solver decides.

A contradiction becomes a violation atom derived from its contested members, plus a
**weak** constraint minimizing it:

```
v :- a_h1, a_h2, ...        # every contested member holds
#minimize { 1@level : v }   # violating this costs, it does not make the program UNSAT
```

Weak rather than hard is the point: a contradiction that cannot be satisfied is
*reported*, not thrown. That is the soft-and-prioritized contract from
[nmtms.md](nmtms.md), expressed directly in the object language.

### The objective

Higher ASPIF minimize priorities dominate lower ones, so the levels read
most-significant first:

| level | minimizes | why |
|---|---|---|
| `2 + rank(p)` | violation atoms | satisfy contradictions, caller priority first |
| `1` | defeated assumptions | give up as little belief as possible |
| `0` | a content-keyed weight | break what remains, *stably* |

Caller priorities are mapped through their ascending rank rather than used as levels
directly, so any integers work and none can collide with the two fixed levels below.

Level 1 is where this beats the stub. The stub walks contradictions in order and
defeats one member of each; ASP optimizes globally, so where two nogoods share a
member it finds the one-atom cover instead of defeating two things.

### Determinism

A tie between equally-good answer sets has no principled winner, but it must not
depend on the order the knowledge arrived — the engine-wide invariant in
[nmtms.md](nmtms.md). Three things enforce it:

- Atom ids are allocated over the ground heads sorted by what each head **says**
  (`solve-context/build`, through `nm/print-key` — printed with the bounds released, so
  no ambient `*print-length*` can collapse the key and drop the allocation back onto the
  answer set the heads were ground from), never in handle order. Every head of one
  program sits in the same context, so this is `solve/content-key`'s order without the
  part that separates two contexts.
- Rule bodies are sorted by atom id; `:nogood` is a set, and an unsorted body would
  render in hash order.
- Level 0 makes defeating the greatest content-key cheapest, mirroring the stub.

`asp_edge_test` pins the three directly, on hand-built configurations whose handles are
swapped so that a handle-keyed allocation would render a different program from a
content-keyed one. It separately runs all 24 orderings of a Nixon diamond through a KB
with `edge-solver` installed and demands one distinct outcome — but that permutation
answers a different question, since the engine routes a plain rebuttal to no solver at
all (below): what it catches is whether the mere *presence* of a backend perturbs the
result, which is the assertion `order_independence_test` makes for the stub.

## Classification: what was forced, what was a coin toss

`vaelii.impl.asp.label` answers a question the TMS cannot. After `settle` resolves a
tie one side is IN and the other OUT — but that flattens two different situations. A
belief can be IN because *every* consistent labeling keeps it, or because the solver
had two equally good options and took one. `in?` reads the same either way.

Asking for all optimal answer sets instead of one separates them:

| class | in every optimum | in some optimum | meaning |
|---|---|---|---|
| `:true` | yes | yes | forced — no consistent labeling gives it up |
| `:supportable` | no | yes | arbitrary — the current belief is one of several |
| `:false` | no | no | excluded — no consistent labeling holds it |

```clojure
(label/classify kb)             ; -> {:true #{h} :supportable #{h} :false #{h}}
```

Where two nogoods share a member, that member is `:false` and its partners `:true` —
dropping the shared one costs a single defeat, so every optimum does it.

**`classify` reads the last `Program` the engine built, and a plain rebuttal builds
none.** The engine does not arbitrate a coexisting `P`/`¬P` pair at `:default`: that is a
represented dilemma, both sides stay IN, and `settle` never reaches the solver. So
`last-program` is nil and `classify` answers `{:true #{} :supportable #{} :false #{}}` —
empty sets, not two `:supportable` handles. A Nixon diamond is exactly that shape, which
makes it the illustration `classify` cannot be shown with: to classify one, commit to a
labeling first with `do/labeling` ([labeling.md](labeling.md)), which is the mechanism
that does build a program from a dilemma. `asp_edge_test`'s
`the-asp-solver-does-not-decide-a-nixon-diamond` pins the absence.

### Two things keep this honest

**The tiebreak comes off.** The level-0 content-keyed objective exists to make an
arbitrary choice *stable*, not to express anything about the world. Left in, it makes
the optimum unique, and every tie would classify as forced. `classify` translates
with `{:tiebreak? false}` so it sees the real set of optima.

**The program is read, not recomputed.** Resolving a tie erases its own evidence: the
defeated side stops matching, so the nogood is no longer derivable from the KB. A
classification built by re-scanning would find nothing contested and report false
certainty. `core/last-program` records what the solver was actually asked, which is
why the KB carries it.

### Concert with the TMS

Two invariants, held by construction and pinned in `asp_label_test`:

```
:true  ⊆ believed          cautious holds in the committed model, which is an optimum
:false ∩ believed = ∅      excluded holds in no optimum, including that one
:supportable               either way — that is what makes it supportable
```

A contradiction settled by *strength* rather than arbitration never builds a program
at all (`decide-nogood` defeats the weaker side directly), so `classify` correctly
reports nothing arbitrary.

Without a backend, `classify` reports every contested assumption `:supportable`. Each
genuinely *is* one of several options, so this understates rather than overclaims.

## Labeling contexts

`label-context` materializes one labeling as a specialization context:

```clojure
(label/label-context kb 'CxNixonA 'CxUniverse)
;; -> {:context CxNixonA :handles [10]}
```

`ctx` sees `base` through `genlCx`, so it inherits the whole KB; what it adds is
an explicit, queryable record of one arbitration. Two labelings of the same tie can
be built as sibling contexts and compared.

The labeling is read from the **TMS**, not from a fresh solve — it records what the
engine committed to, rather than what a second solve might independently choose. A
re-solve would usually agree, and "usually" is not a property to build on.

The context is minted whether or not there was a tie. With no recorded `Program` — a
KB the engine never arbitrated in, or a dilemma it declined — the `genlCx` edge is
written and `:handles` comes back empty, which is what "the engine committed to
nothing" materializes as. `label-dilemmas` ([labeling.md](labeling.md)) is the other
way round on purpose: it *makes* the choice rather than reporting one, so it mints no
context when there is nothing contested.

### It entrenches what it records

Worth knowing before using it: what `label-context` writes are ordinary assertions,
and an assertion is evidence. The recorded side gains a second nogood against its
rival, which makes defeating the rival strictly cheaper than defeating the record. So
a tie that classified `:supportable` on both sides classifies `:true`/`:false`
afterwards.

Belief does not move — the losing side was already OUT — but it stops *looking*
arbitrary, because it no longer is: something now asserts the choice. **Classify
before you label.** Retracting the returned handles reopens the tie.

## Why `:violated` comes back empty

It looks like a gap and is not. An irreducible known-true clash never reaches a
solver: `settle/settle`'s `decide-nogood` classifies it as *hard* and reports it
directly, and `solve/program` drops any nogood with no contested member. What does
arrive always has a contested member, and defeating that member always satisfies it.

The `:doomed` path in `edge.clj` is therefore defensive. It adds no work and stays
correct if nogoods ever grow beyond today's `S` vs `(not S)` pairs.

## Where the ASP layer stops

The engine encodes the contradiction edge and nothing above it: `edge.clj`
translates one settle's nogoods into a program, and `label.clj` classifies and labels
what comes back. There is no multi-context classification and no multi-shot solving — a
solve is one program, built from one region, answered once.

A `do/label` program carries one thing a settle program does not: **cardinality bounds**.
A `asp/atMost` / `asp/atLeast` rule ([solving.md](solving.md)) grounds to a `Program`
`:cardinalities` entry, and `edge/translate` renders each as one ASPIF weight-body
statement (`aspif/weight-constraint` for a hard bound, `aspif/weight-rule` plus a minimize
for a soft one) rather than the `C(n, k+1)` subset nogoods a hand-written bound needs.
`settle` builds no cardinalities — they are a labeling-only construct — so `local-solver`,
which only ever sees a settle program, never receives one.

There is also **no CSP layer**: a program carries no integer constraints, so nothing
emits clingcon theory atoms and a numeric bound reaches the solver only as the handles a
nogood names. Metric bounds are `vaelii.impl.stp`'s, closed by shortest paths outside the
solver entirely ([stp.md](stp.md)).

## Tests

- `asp_aspif_test` — the lower layer. The wire format is pinned *literally*, because
  ASPIF is an external contract with clingo and clasp: a silent encoding change is
  not a refactor, it is a different program. Semantics are then checked by solving.
- `asp_edge_test` — the translation and the `Solver` contract: minimal defeat,
  priority order, deterministic rendering, and the permutation sweep above.
- `asp_label_test` — classification and labeling, every KB-level case re-checking
  the two TMS invariants rather than only the classification itself.

A test that needs a solver skips when no backend is reachable, rather than silently
asserting the stub's behaviour and proving nothing — the whole of `asp_label_test` and
nearly all of `asp_edge_test`. `asp_aspif_test` gates only the tests that solve: the
wire format and the atom table are checkable without a backend, so those always run.
