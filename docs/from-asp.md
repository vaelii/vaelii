# Arriving from answer set programming

- **Covers:** the answer set programming vocabulary mapped onto this one — rules,
  choices, constraints, the three negations — and the two structural differences that
  matter more than any of the names: there is no grounding step, and belief is not a
  model.
- **Not here:** the clingo and clasp backend a contested edge is actually solved on,
  which is ASP the machinery rather than ASP the language → [asp.md](asp.md); the
  vocabulary that builds a program for it → [solving.md](solving.md),
  [labeling.md](labeling.md).
- **Assumes:** sentex, context, handle, defeasible → [glossary.md](glossary.md).

A solver you already know is in here, and reaching it feels nothing like writing a
program for it. Read the two structural sections before the tables.

## Word for word

| in ASP | here | what changes |
|---|---|---|
| atom | a ground sentex | a sentence *plus* the context it holds in |
| `h(X) :- b1(X), b2(X).` | `(implies (and (b1 ?x) (b2 ?x)) (h ?x))` | every literal is a predicate applied to arguments — there are no propositional atoms — and a rule is a sentex too, with a handle and truth maintenance → [inference.md](inference.md) |
| `{h(X)} :- b(X).` | `set/assumptionRule` | a choice, and the only thing a solve is free to pick |
| `h(X) :- a(X) ; b(X).` | `(implies (or (a ?x) (b ?x)) (h ?x))` | a body disjunction, stored as one rule per alternative rather than solved |
| `:- b(X).` | `set/hardConstraint` | renders as a genuine integrity constraint; the model is excluded |
| `:~ b(X). [1@l]` | `(set/softConstraint l (implies …))` | a violation atom and a `#minimize` at level `l`; without the leading `l` the level is 1 |
| `#minimize { W@P,X : h(X), w(X,W) }.` | `(asp/minimize P ?w (and (h ?x) (w ?x ?w)))` | the weight is ordinary believed data, an integer inside the solver's 32-bit range → [solving.md](solving.md) |
| `not a(item)` | `(unknown (a Item))` | a query operator, ground-only, storing nothing; over a **choice** head in a constraint body write `(not (a Item))` instead ([below](#negation-and-there-are-three)) |
| `not (a(X), b(X))` over a shared variable | `(unknown (thereExists ?x (and (a ?x) (b ?x))))` | joined, so one witness satisfies both |
| `#false :- p(X), not q(X).` over all X | `(forall ?x (implies (p ?x) (q ?x)))` | sugar for the nested NAF, in a rule body rather than as a constraint |
| `-a` | `(not S)` | a **stored** negative sentex with its own handle, not an absence |
| an answer set | a labeling context | materialized, inert, one per optimal answer set |
| `X` | `?x` | |
| `p/2` | — | arity is not part of a name; declare it with `(arity p 2)` or `arg` |
| `#show` | — | reads are queries; nothing is projected at solve time |
| cautious consequence | `forced` | |
| brave consequence | `supportable` | |
| in no optimal model | `excluded` | |

## There is no grounding step

This is the difference to internalize first. There is no program text, no ground-then-
solve, no moment at which the rule base is handed to a grounder. Facts and rules are
asserted one at a time into a store, indexed as they land, and the truth maintenance
system relabels the affected region after every mutation. Nothing re-grounds because
nothing was ground.

What that buys is incrementality: asserting a fact costs the region it touches, not the
program. It costs whole-program reasoning, which is not automatically available —
you ask for it, over a bounded region, and only where a contradiction actually needs
deciding.

When a solve does run, it grounds the assumption rules visible from its base context and
nothing else. **The ordinary rule base is not emitted to the solver**, so a choice does
not propagate through your `implies` rules the way it would through a program. That is a
real limit and [solving.md](solving.md) states it as one.

## The KB is not a program, and belief is not a model

There is one knowledge base, and almost everything in it is true almost all the time.
There is no "the answer sets of the KB" — the question does not typecheck. Belief is a
single labeling computed by a justification-based truth maintenance system as a least
fixpoint, recomputed from current state rather than accumulated, and it is *the* answer
rather than one of several. → [nmtms.md](nmtms.md)

Defeat is that system's, not the solver's. Two `:default` claims that rebut each other
both stay believed and are reported as a represented dilemma; the engine arbitrates
nothing on its own. ASP is what you reach for when a particular contested edge has to be
decided, and it is opt-in per KB:

```clojure
(v/set-solver kb :asp)          ; the default is a greedy stub that defeats one member per nogood
```

A plain rebuttal with neither side naming the other's case — a Nixon diamond — gets no
program from `settle`, so `do/classify` has no labeling to read over it. That shape is
exactly the one a solve cannot be demonstrated with. The read-path `(bravely S)` /
`(cautiously S)` queries, which the `:brave-cautious` reasoner answers, classify it anyway:
through the backend when one is reachable, and otherwise from the JTMS dependency graph →
[labeling.md](labeling.md).

## Negation, and there are three

| you want | write | what it is |
|---|---|---|
| negation as failure | `(unknown S)` | closed-world, evaluated at level 6, storing nothing → [naf.md](naf.md) |
| classical negation | `(not S)` | a stored sentex with a handle, believed or not like any other |
| "usually, but not when…" | `exceptWhen` | undercuts the **rule**, not the literal; the conclusion is never created → [exceptions.md](exceptions.md) |

`exceptWhen` is the one with no ASP counterpart, and it is the idiomatic way to write a
default here. It is undercutting defeat: the rule states its own exception, the exception
is re-evaluated per firing, and it is never stored.

**Inside a constraint body, a choice head is negated with `(not …)`.** A solve's choice
head is two-valued: the labeling writes `(head)` for a chosen head and `(not head)` for an
unchosen one. Over a choice head the classical negation and ASP's `not h` therefore
coincide, and a solve reads `(not (pick ?c))` in a constraint body as "`pick(C)` is
absent" — a body of nothing but those is an at-least-one → [solving.md](solving.md).
Grounding reads `(unknown (pick C))` in the same place as a background literal and proves
it against base belief. No choice head is believed in the base, so the literal holds for
every binding and constrains nothing; `(unknown (thereExists ?c (pick ?c)))` reads the
same way.

Two constraints on `unknown` that a program would not impose. It is **ground and closed**
— an open `(unknown (flies ?x))` is refused rather than answered — and `thereExists`
projects a variable out so `unknown` can negate the result. And **stratification is
enforced at assert time**: a cycle through negation throws `:not-stratified`, including
the one-rule cycle and a cycle a `genl` edge would close. You learn about it when you
write it, not when you solve. That is the whole of what replaces choosing among stable
models: a program with several is refused rather than resolved.

The conjunction under a quantifier is **joined**, so a grounder's shared variable
transfers directly, and `forall` is sugar for the nested case. What does not transfer is
the grounder's own reading of a domain: a closed extent is declared per predicate
(`(closed_extent_predicate P)`), scoped to the context that declares it, rather than being
what the Herbrand base happens to contain. → [naf.md](naf.md)

## Choices, constraints and the solve

The three wrappers, all assert-time and all canonicalized into the rule record:

```clojure
(v/assert kb '(set/assumptionRule (implies (candidate ?x) (chosen ?x)))     ctx)
(v/assert kb '(set/hardConstraint (implies (and (chosen ?x) (barred ?x)) (banned_choice ?x))) ctx)
(v/assert kb '(set/softConstraint (implies (and (chosen ?x) (costly ?x)) (dear_choice ?x)))   ctx)
```

A constraint's head is a **contradiction marker** rather than a truth, and it is a real
literal held to the ordinary range restriction — every variable in it comes from the
body. A bare symbol there is refused `:not-well-formed`.

Each is a **virtual wrapper canonicalized into the rule record**, not a function you
call — it is part of the sentence, so a choice rule and its bare twin are different
sentexes with different handles. A constraint's head is a contradiction marker rather
than a truth. An assumption rule never chains into belief: `(candidate Item)` does not
derive `(chosen Item)`, and a solve is the only thing that consults it.

A solve is asked for by asserting a `do/` imperative, which is a virtual functor: it is
never stored, and it is refused anywhere but the top level — not as a rule antecedent,
not in a consequent, not inside `exceptWhen`.

| you want | write | what happens |
|---|---|---|
| enumerate and materialize | `(do/label Base Into)` | one **inert** context per optimal answer set, written under `Into` |
| one optimum, persisting nothing | `(do/label Base Into :one)` | |
| first model, no optimization | `(do/label Base Into :sat)` | |
| the three-way classification | `(do/classify Into)` | `forced` / `supportable` / `excluded` |
| label a context in place | `(do/labeling Ctx)` | entrenches what it records — classify *before* you label |

"Inert" is exact: a materialized labeling is stored outside the truth maintenance system
entirely, never believed, never chained, never scanned for contradictions. The base KB is
untouched by a solve. → [solving.md](solving.md)

Optimization is lexicographic: one level per distinct caller priority (the soft
constraints and `asp/minimize`), above defeated assumptions, above a content-keyed
tiebreak — and the tiebreak is what makes a solve deterministic under reordering. Atom ids are allocated in content order, never in handle order.

## The solver you already run is in here

clingo runs **in-process** through raw JNA — no JNI, no generated bindings — and clasp
runs as a subprocess taking ASPIF on stdin. Which one answers is chosen by program byte
size (`VAELII_CLINGO_MAX_BYTES`, default 3000), and either can be forced. With no backend
reachable, the `Solver` degrades to the stub rather than failing. Install with
`brew install clingo`; the test profile is `lein with-profile +with-clingo test`.

`(v/last-program kb)` hands back the last program solved, which is the thing to read when
a solve answers something surprising. → [asp.md](asp.md)

## The call you would have made

| in ASP | here |
|---|---|
| `clingo prog.lp` | `(v/assert kb '(do/label Base Into) ctx)` |
| `clingo -n 0` | the `:all` mode, which is the default |
| `clingo --enum-mode=cautious` | `(do/classify Into)`, reading `forced` |
| the same, brave | `(do/classify Into)`, reading `supportable` |
| `--enum-mode=cautious` for one atom of the current dilemmas, with no solve written | `(v/ask? kb '(cautiously S) ctx)`, after `(v/add-reasoner kb :brave-cautious)` |
| the same, brave | `(v/ask? kb '(bravely S) ctx)` |
| `#show p/1` | `(v/query kb goal ctx)` — an ordinary read → [api.md](api.md) |
| grounding | nothing; there is no such step |
| inspecting the ground program | `(v/last-program kb)` |

## What you keep

- The stable-model intuition for choices, and brave versus cautious consequence
- Integrity constraints that genuinely exclude a model
- Optimization by weak constraints with priority levels
- Determinism: same knowledge, any order, same answer — and it is a property the engine
  holds globally, not only inside a solve → [nmtms.md](nmtms.md)

## What you lose

- Whole-program semantics. A solve sees the assumption rules of one region
- Disjunctive **heads**. Bodies are fine — `(or A B)` in an antecedent is stored as one
  rule per alternative ([canonicalization.md](canonicalization.md)), which is the `;` of
  a body — but a head that disjoins is refused. Belief is a label on a sentex rather than
  on a set of them, so `a | b :- c.` is written as one `set/assumptionRule` per
  alternative, with a `set/hardConstraint` for the combinations that cannot stand, and
  read back from a solve. What that gives up against a disjunctive head is minimality:
  the choice rules admit the model where both are true, and the constraint has to rule it
  out where a disjunctive head would not have offered it
- `#count` and `#sum` as part of the **model**. The five reductions work in a rule body —
  `(agg/count ?n ?v Body)` after the generator antecedent that binds the group, re-checked
  as the census moves — but they are *query* operators a prover computes rather than atoms
  a solve reasons over, and none may be a rule's consequent. GROUP BY falls out of which
  variable an antecedent binds → [aggregate.md](aggregate.md). A **cardinality bound over
  the choices** is the one count a solve does reason over: `(asp/atMost k ?v (p ?v …))` /
  `asp/atLeast` translate to a solver cardinality atom, the `{ … } <= k` you would have
  written, rather than the census `agg/count` is → [solving.md](solving.md)
- `#sum` as a **bound**. A weighted sum exists only as an objective — `(asp/minimize P ?w
  body)` is the `#minimize` over a data weight — and no weighted bound constrains a model
- Multi-shot solving. A solve is one program, built from one region, answered once
- Theory atoms and any constraint layer over integers

## What you gain

- An incremental store with truth maintenance: assert one fact, pay for one region
- Contexts, so the same sentence can hold differently in two places → [contexts.md](contexts.md)
- Defeasible defaults with stated exceptions, which need no choice rule at all
- Cascading retraction, and `why` / `why-not` to ask why something is or is not believed
- Six qualitative relation algebras and metric time → [qcn.md](qcn.md), [stp.md](stp.md)
- Backward chaining over the same rules a forward pass uses
