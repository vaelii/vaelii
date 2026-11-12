# The ASP backend

- **Covers:** how the edge solver renders a contested `Program` to ASPIF and solves it
  with clingo or clasp, deterministically.
- **Not here:** the assumption-rule and constraint vocabulary that builds a `Program` in
  the first place → [solving.md](solving.md); committing one labeling of a dilemma inside
  a context → [labeling.md](labeling.md); writing for this engine when answer set
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
vaelii.impl.asp.solve-context     do/label and do/classify   (docs/solving.md)
vaelii.impl.asp.prover            (bravely S) / (cautiously S)   (docs/labeling.md)
```

## Installing it

```clojure
(v/set-solver kb :asp)
```

`set-solver` installs `edge-solver` as the KB's solver, and `local-solver` is the default.
The installed solver is read on one path: `do/labeling` with no backend reachable, on a
cluster past the solve-free bracket's caps (`label/labeling-solver`), where `edge-solver`
delegates to `solve/local-solver` in turn. `do/label`, `classify` and the brave/cautious
prover call the backend directly. The name resolves the backend at runtime, so a caller
needs nothing from `vaelii.impl.asp.*` and nothing here reaches the load path of a KB
that never asks. `(solver/available?)` tells you whether the selected backend can solve in
this environment. Which of the two runs is not exposed: the solver routes per program,
from the config, from whether libclingo loaded, and from the program's size.

## Getting a solver

A solver is optional. A KB that never calls `set-solver :asp`, `do/label`, `classify` or
`bravely`/`cautiously` runs on the in-process `local-solver` and needs nothing installed.
The edge solver takes either backend, and both is better.

- **The executable** runs as a subprocess: ASPIF on stdin, `--outf=2` JSON on stdout. It
  is `clasp`, found on `PATH`, or the executable `VAELII_CLASP_BIN` (or
  `-Dvaelii.clasp.bin=…`) names. The `clingo` executable takes clasp's flags and writes
  the same JSON, so it serves in clasp's place. An in-process native crash would take the
  JVM with it, so a long-running process wants this backend. A solve reads the subprocess
  on three `future` threads, which are non-daemon and idle out after 60 s, so a program
  that solves and returns from `main` exits up to 60 s later unless it calls
  `shutdown-agents`.
- **The library** is `libclingo`, loaded in-process through raw JNA: no JNI, no generated
  bindings, no clingo Java library. JNA finds it on `jna.library.path`, or at the name or
  absolute path `-Dvaelii.clingo.lib=…` gives. It is the faster backend on small programs,
  which is the common case here.

| Platform | Executable | Library |
|---|---|---|
| macOS (Homebrew) | `brew install clingo` installs `clasp` and `clingo` | the same install puts `libclingo.dylib` in `/opt/homebrew/lib` |
| Debian, Ubuntu | `apt-get install clasp` (Ubuntu universe) | no package; build clingo from source, which installs `libclingo.so` |
| any platform with Python 3 | `pip install clingo`, then a wrapper script that runs `python3 -m clingo "$@"`, named by `VAELII_CLASP_BIN` | none: the wheel's `_clingo` module is a Python extension, not `libclingo` |

No Ubuntu suite packages `clingo` or `libclingo`. Windows has no tested install.

Run from this checkout, `lein with-profile +with-clingo …` points `jna.library.path` at
`VAELII_CLINGO_LIB`, default `/opt/homebrew/lib`. A project that depends on vaelii does not
get the profile, so it passes the property itself:

```clojure
:jvm-opts ["-Dvaelii.clingo.lib=/opt/homebrew/lib/libclingo.dylib"   ; or a libclingo.so path
           "--enable-native-access=ALL-UNNAMED"]                     ; JDK 24+ warns without it
```

`(solver/available?)` answers whether the selected backend can solve, and
`VAELII_ASP_SOLVER=clasp` routes every solve to the executable, the setting CI runs on
Ubuntu. The two executables and the library give one answer per mode on each program
`asp_aspif_test/every-backend-answers-every-mode-alike` solves.

`solver.clj` picks per program size (`VAELII_CLINGO_MAX_BYTES`, default 3000 bytes:
clingo below, clasp above) and loads the clingo namespace lazily via
`requiring-resolve`, so JNA stays genuinely optional. Force one with
`-Dvaelii.asp.solver=clingo|clasp` or `VAELII_ASP_SOLVER`. Whether clingo loads is
decided once per process, and a load that throws is logged at `:warn` and routes every
solve to clasp. A `VirtualMachineError` during the load is the one exception: it answers
clasp for that call only, and the next call loads again.

An in-process `solve` writes no ASPIF text. `backend-load!` interns each program atom as
the symbol `a(<id>)` carrying its label and emits every rule into a live control through
the `clingo_backend_*` accessors; a model's true atoms come back through
`clingo_model_symbols` and map to labels through that symbol association. clingo's
`classify-both` loads the rendered ASPIF text from a temp file, and `clasp` reads it on
stdin.

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

### The solve limit

`VAELII_ASP_SOLVE_LIMIT` (default 100,000; 0 sets no limit) bounds **one solve** by the
conflicts its search may spend, on both backends: clasp takes it as `--solve-limit`, and
in-process clingo's control takes the same flag as a solver option. Every solve also runs
on one thread under clasp's default seed, stated as `--parallel-mode=1 --seed=1` rather
than assumed (`clasp/search-args`). A conflict count does not depend on the machine's
speed or load, so the limit stops a program at the same point on every machine, with the
same model in hand.

Measured on clasp 3.4.0 and libclingo 5.8.0, on a 90-vertex weighted cover (optimum
proved in 1.37 million conflicts) and an 11-pigeon pigeonhole: each clasp mode at two
limits that stop the search, and a `:label` solve at one it finishes under, gave one
output per case over ten runs alone and ten run at once beside ten busy processes (load
average 49 on ten cores), identical but for clasp's timing fields. The four enumerating
modes on clingo gave one result per case the same way.
`asp_aspif_test/a-search-past-the-solve-limit-stops-at-the-same-point-on-every-run`
repeats the check on every backend the machine has.

The default of 100,000 conflicts keeps the limit, not the wall clock, the bound on every
program of the sizes measured. On clasp 3.4.0 it costs 0.6 seconds on the 90-vertex
cover (24 KB of ASPIF) and 2 seconds on a 600-vertex cover (173 KB), about 30 times under
the time limit's 60 seconds, so a machine many times slower still meets the solve limit
first. The default suite's largest solve spends 104 conflicts. A program that needs more
search than the limit stops deciding on every machine: the 90-vertex cover proves its
optimum in 1.37 million conflicts, so at the default the edge solver decides nothing on
it and `do/label :one` returns its best model as best-effort. Raise the limit for such a
program, and raise `VAELII_ASP_TIME_LIMIT` with it when the solve would then run near
60 seconds on the slowest machine that runs it. The core-guided strategy below proves a
weighted cover of that shape in fewer conflicts than the default does.

A search the limit stops reads as one the time limit stops: `:interrupted`, or
`:best-effort` for a `:label` solve holding a model. Neither backend flags it. clasp
reports `More: yes`, a search that did not exhaust its space, and libclingo sets neither
the exhausted bit nor the interrupted one. A `:sat` solve stops at its first model with
its space unexhausted by design, so there only a search with no model has stopped short.

The same program can stop at different points on the two backends, and on two clasp
versions: the backends load a program differently (ASPIF text against the backend
accessors), so their searches differ, and a program near the limit can finish on one and
not the other. Which backend solves is configuration, not speed — `VAELII_ASP_SOLVER`,
and in auto mode the program's size and whether libclingo loads — so two installations
that must agree on such a program set `VAELII_ASP_SOLVER`.

### The optimization strategy

`VAELII_ASP_OPT_STRATEGY` picks how **every solve** optimizes, on both backends:
`bb`, clasp's model-guided branch-and-bound and the default, or `usc`, core-guided
optimization, which `clasp/search-args` passes as `--opt-strategy=usc,k,0,stratify`
beside the solve limit. Branch-and-bound finds a model and descends from its cost.
Core-guided optimization raises a lower bound from unsatisfiable cores, so its first model
comes later and is closer to the optimum. A strategy is a search flag like the seed, so a
solve stops at the same point on every machine under either
(`asp_aspif_test/core-guided-optimization-proves-what-branch-and-bound-stops-short-of`).

Measured on clasp 3.4.0, one thread, seed 1, the `:label` mode, over `asp_aspif_test`'s
`weighted-cover` graphs and the 30-city cap `cardinality_solve_test` stops at the limit:

| program | ASPIF | `bb` at 100,000 conflicts | `usc` at 100,000 conflicts |
|---|---|---|---|
| 60-vertex cover | 5 KB | optimum 149, 8,924 conflicts | optimum 149, 539 conflicts |
| 90-vertex cover | 11 KB | best-effort 261 (optimum in 830,546) | optimum 260, 7,376 conflicts |
| 30-city cap, `C(30, 10)` tied optima | 5 KB | best-effort | best-effort, same cost |
| 600-vertex cover | 437 KB | best-effort 2,728 | best-effort 2,706 |

The enumerating modes return the same optima and the same brave and cautious sets under
both, and the 90-vertex cover's cautious enumeration spends 8,773 conflicts under `usc`
against 2,351,976 under `bb`. The stratified `k` relaxation is the variant passed because
the plain `usc` relaxation holds **no model** of the 600-vertex cover at the limit, where
an interrupted search with no model decides nothing. The default stays `bb` because a change of strategy changes which model
a `:label` solve that meets the limit returns, on every installation that does not set
the variable.

### The time limit

`VAELII_ASP_TIME_LIMIT` (default 60 seconds; 0 lifts it) bounds **one solve** by the wall
clock, on both backends, and is the backstop behind the solve limit: clasp takes it as
`--time-limit`, and in-process clingo — whose control accepts solver options only and
refuses that flag — runs the search asynchronously and cancels the handle when the budget
is spent. Which solves it stops depends on the machine's speed and load, so a round it
cuts short decides nothing on one machine that another machine decides. With
`VAELII_ASP_SOLVE_LIMIT` at 0 it is the only limit
([defenses.md](defenses.md#where-the-five-properties-stop)).

A clasp process still running at twice the limit, or at the limit plus 10 seconds when
that is later, is killed with every process it started, and the solve raises
`:solver-unavailable`, the refusal a missing binary raises (`clasp/run-clasp`). clasp
stops itself at `--time-limit`, so the kill reaches only a process that did not. A limit
of 0 sets no deadline either.

**One solve is not one operation, and the difference is a multiplier.** A solve runs on
the single writer, so an operation that makes several holds every write behind the sum of
their budgets, not behind one:

| operation | solves | worst case |
|---|---|---|
| `do/label` (`:all`, `:one`, `:sat`) | 1 | 1 × budget |
| `edge-solver` on one program | 1 | 1 × budget |
| `classify` / `classify-program` | 2 (`classify-both` runs cautious then brave) | 2 × budget |
| `do/labeling` (`label-dilemmas`) | 0 where the solve-free bracket enumerates; 3 past its caps (classification's two, then the labeling) | 3 × budget |

Measured at `VAELII_ASP_TIME_LIMIT=1` on a 78-atom program that finishes under neither:
`classify-both` returns after **about two budgets**, a single `:label` or `:all-optima`
solve after **about one**. Both are correct — every individual solve was cancelled on
time, and what the readings show is the multiplier rather than a wall clock.

So size the variable against the *solve*, and read the table for what an operation then
costs. `asp_edge_test` and `solve_context_test` assert the counts, because a doc that names
them and code that changes them is worse than either alone.

An interrupted solve that found no model reports `:interrupted`, and **that is not an
answer**. A backend's result is an answer set at `:optimum` or `:sat`, and in `:label`
mode a best model reached before the interrupt is `:best-effort`, an answer
whose optimality is unproven. `:interrupted` and `:unknown` carry no witness, and every
reader maps an atom's absence to *defeated* or *not kept* — read as an answer, an empty
result would defeat every contested assumption and label every choice head false.

### Refuse rather than degrade, whenever a backend is present

`edge-solver` falls back to `local-solver` in two cases: **no backend at all**, and a
backend's definite `:unsat` (below). With no backend the two degrade together and agree, because `classify-program`
without a backend reports every contested assumption `:supportable` and claims nothing.

With a backend present the fallback would be a different solver's answer, and the two
solvers disagree on two nogoods sharing a member
([defenses.md](defenses.md#a-labelings-solve-ignores-the-installed-solver-when-a-backend-is-reachable)).

Pairing that stub labeling with an ASP classification is what `check-agrees` reports as
`:labeling-inconsistent`, blaming the encoding for a disagreement the fallback
introduced. A labeling committed from such a pair would differ run to run on identical
knowledge, and the order-independence invariant in [nmtms.md](nmtms.md) is a claim about
*knowledge*, which a wall clock is not.

So with a backend present an unanswered solve **decides nothing**: `{:defeat #{}
:violated [...] :error e}`, every contested assumption left standing, the failure logged
at `:error` and named in `:error` for a caller that can act on it. The brave/cautious
classification behind `classify` and `label-dilemmas` refuses with `:solver-failed` rather
than return a world nobody computed — `label-dilemmas` by raising that same `:error`, since
an empty defeat set is otherwise the perfectly good answer *keep everything*. `do/label` in
`:one` or `:sat` mode is the one reader that does not refuse when a model was found first:
it returns that model with `:best-effort? true`, a valid labeling whose optimality the
interrupt left unproven. `label-dilemmas` is unaffected — `edge-solver` treats
`:best-effort` as undecided, so no wall clock moves a belief.

`:unsat` keeps its own reading and is not this case: a definite *no model*, the same
answer in every run, so it costs the invariant nothing. The edge solver degrades on it,
`kept-of` keeps nothing, and an enumeration is empty. It should not arrive from a dilemma
program at all — every nogood in one is soft.

### A backend that throws

Same policy, same reason. The backends fail in several currencies — clingo's
`:solver-failed` naming the native call that returned zero, clasp's
`:solver-unavailable` when the binary is gone, a JNA `Error` against a missing or
wrong-ABI libclingo — and `edge-solver` catches all of them at the boundary, because the
boundary is where a native failure crosses into the engine.

Deciding nothing hands the failure back as `:error` for a caller to rank, and
`label-dilemmas` raises it before the labeling asserts anything.

Two throws are not caught this way. A `VirtualMachineError` (`OutOfMemoryError`,
`StackOverflowError`) is rethrown, since the JVM is failing and not the backend. An
`InterruptedException` decides nothing and sets the thread's interrupt flag again, so the
interrupt that was meant to stop the caller still reaches the writing thread (what an
interrupt does to a writing thread: [api.md](api.md)).

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

A `do/label` program adds a solve's **normal rules** (`set/solveRule`,
[solving.md](solving.md)), each ground instance rendered as written over the choice atoms
and the **derived** atoms its heads name:

```
d :- a_1, ..., not a_k.     # a derived atom: no choice rule, no minimize term
```

A derived atom is decided by the rules, so the keep-belief and tiebreak levels below
range over the choice atoms alone.

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

`asp_edge_test` asserts the three directly, on hand-built configurations whose handles are
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

**`classify` reads the last `Program` `do/labeling` recorded, and a settle records
none.** The engine does not arbitrate a coexisting `P`/`¬P` pair at `:default`: that is a
represented dilemma, both sides stay IN, and `settle` never reaches the solver. So
`last-program` is nil and `classify` answers `{:true #{} :supportable #{} :false #{}}` —
empty sets, not two `:supportable` handles. A Nixon diamond is exactly that shape, which
makes it the illustration `classify` cannot be shown with: to classify one, commit to a
labeling first with `do/labeling` ([labeling.md](labeling.md)), which is the mechanism
that does build a program from a dilemma. `asp_edge_test`'s
`the-asp-solver-does-not-decide-a-nixon-diamond` asserts the absence.

### Two things keep `classify` from reporting a tie as forced

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

Two invariants, held by construction and asserted in `asp_label_test`:

```
:true  ⊆ believed          cautious holds in the committed model, which is an optimum
:false ∩ believed = ∅      excluded holds in no optimum, including that one
:supportable               either way — that is what makes it supportable
```

A contradiction settled by *strength* rather than arbitration never builds a program
at all (`decide/verdict` defeats the weaker side directly), so `classify` correctly
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

The labeling is read from the **TMS**, not from a fresh solve: it records what the
engine committed to, rather than what a second solve might choose.

The context is minted whether or not there was a tie. With no recorded `Program` — a
KB the engine never arbitrated in, or a dilemma it declined — the `genlCx` edge is
written and `:handles` comes back empty, which is what "the engine committed to
nothing" materializes as. `label-dilemmas` ([labeling.md](labeling.md)) is the other
way round on purpose: it *makes* the choice rather than reporting one, so it mints no
context when there is nothing contested.

### It entrenches what it records

`label-context` writes ordinary assertions, and an
assertion is evidence. The recorded side gains a second nogood against its
rival, which makes defeating the rival strictly cheaper than defeating the record. So
a tie that classified `:supportable` on both sides classifies `:true`/`:false`
afterwards.

Belief does not move — the losing side was already OUT — but it stops *looking*
arbitrary, because it no longer is: something now asserts the choice. **Classify
before you label.** Retracting the returned handles reopens the tie.

## Why `:violated` comes back empty

It looks like a gap and is not. An irreducible known-true clash never reaches a
solver: `decide/verdict` classifies it as *hard* and reports it
directly, and `solve/program` drops any nogood with no contested member. What does
arrive always has a contested member, and defeating that member always satisfies it.

The `:doomed` path in `edge.clj` is therefore defensive. It adds no work and stays
correct if nogoods ever grow beyond today's `S` vs `(not S)` pairs.

## Where the ASP layer stops

The engine encodes the contradiction edge and nothing above it: `edge.clj`
translates one program's nogoods into ASPIF, and `label.clj` classifies and labels
what comes back. There is no multi-context classification and no multi-shot solving — a
solve is one program, built from one region, answered once.

A `do/label` program carries one thing a dilemma program does not: **cardinality bounds**.
A `asp/atMost` / `asp/atLeast` rule, or a weighted `asp/atMostSum` / `asp/atLeastSum`
([solving.md](solving.md)), grounds to a `Program` `:cardinalities` entry, and `edge/translate` renders each as one ASPIF weight-body
statement (`aspif/weight-constraint` for a hard bound, `aspif/weight-rule` plus a minimize
for a soft one) rather than the `C(n, k+1)` subset nogoods a hand-written bound needs.
`label/dilemma-program` builds no cardinalities, so `local-solver`, which sees a dilemma
program only, never receives one.

There is also **no CSP layer**: a program carries no integer constraints, so nothing
emits clingcon theory atoms and a numeric bound reaches the solver only as the handles a
nogood names. Metric bounds are `vaelii.impl.stp`'s, closed by shortest paths outside the
solver entirely ([stp.md](stp.md)).

## Tests

- `asp_aspif_test` — the lower layer. The wire format is frozen *literally*, because
  ASPIF is an external contract with clingo and clasp: a silent encoding change is
  not a refactor, it is a different program. Semantics are then checked by solving.
- `asp_edge_test` — the translation and the `Solver` contract: minimal defeat,
  priority order, deterministic rendering, and the permutation sweep above.
- `asp_label_test` — classification and labeling, every KB-level case re-checking
  the two TMS invariants rather than only the classification itself.

A test that needs a solver skips when no backend is reachable, rather than silently
asserting the stub's behaviour and proving nothing — the whole of `asp_label_test` and
nearly all of `asp_edge_test`. `asp_aspif_test` makes only the tests that solve conditional on a solver: the
wire format and the atom table are checkable without a backend, so those always run.
