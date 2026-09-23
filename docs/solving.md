# Solving: assumptionRule and persistent, inert labeling contexts

- **Covers:** how `assumptionRule`, constraint, cardinality, and objective
  (`asp/minimize` / soft-constraint priority) declarations become `do/label`'s
  persistent, inert labeling contexts, without touching base belief.
- **Not here:** the ASPIF encoding and solver backends the resulting program runs on →
  [asp.md](asp.md); committing one labeling live into base belief →
  [labeling.md](labeling.md).
- **Assumes:** sentex, context, premise → [glossary.md](glossary.md).

How a solve is expressed, run, and **kept** — as sentexes in the records, not an
in-memory snapshot — and why the base KB is never disturbed.

## Opt-in, persistent, inert

The KB's job is to be **always available with almost everything true**, and to do
**everything incrementally** — no operation scans the whole KB. So belief carries no
forced/supportable/excluded axis: `settle` solves nothing, and a classification exists
only where a caller asked for one.

A solve is an **opt-in, persistent, inert artifact**. Choices are declared with
`assumptionRules`; a solve grounds them and then either enumerates every optimal answer
set, writing **each one as its own context** whose truth values are ordinary sentexes in
the records, or returns a single answer set and writes nothing. What it does write
persists and is inspectable; the base KB is untouched either way.

## `assumptionRule` — a choice, not a truth

```clojure
(set/assumptionRule (implies <body> <head>))
```

A choice rule (`{head} :- body` in ASP): when `body` is derivable, `head` is an atom a
solve may set true or false. It is a virtual wrapper like `set/defaultRule` / `exceptWhen`,
canonicalized into the `RuleSentex` record's **`:assumption`** field and, being part of the
rule's identity, into the **trie key** — a choice rule and its bare twin are different
sentexes.

`:assumption` is a *firing mode*, **not** a strength class (`strength.clj` keeps its two
classes; there is no third). `forward-sentex?` / `backward-sentex?` return false for a
choice rule, so it **never chains into belief** — asserting `(candidate Item)` does not
derive `(color Item red)`. A solve is the only thing that consults it.

**This is where a disjunctive conclusion lands.** `(implies <body> (or C1 C2))` is
refused at the assert entry point, and the refusal points here: a disjunctive head says one of
two things holds without saying which, and belief is a label on a stored sentex rather
than on a set of them, so forward chaining has nothing to place. What it *is* is a
choice, and a choice has a home — one `set/assumptionRule` per alternative, plus a
`set/hardConstraint` over the combinations that cannot stand together, read back as an
answer set. (A rule **antecedent** that disjoins is a different question with a different
answer: it is polycanonicalized into one rule per alternative and never reaches a solve
at all — [canonicalization.md](canonicalization.md).)

## `hardConstraint` / `softConstraint` — a nogood over the choices

```clojure
(set/hardConstraint (implies <body> <marker>))
(set/softConstraint (implies <body> <marker>))
```

A constraint rule's head is a **contradiction marker**, not a truth, and its body is a
conjunctive nogood mixing background facts with choice-head patterns. Like
`assumptionRule` it is a virtual wrapper canonicalized into the `RuleSentex` record — into
**`:constraint`**, as `:hard` or `:soft` — and, being part of the rule's identity, into
the trie key: `sentex/key-tokens` gives every rule a constant `:constraint` slot, so a
hard constraint, its soft twin and its bare twin are three sentexes. `rules/constraint-of`
reads the class back off the record, `rules/constraint?` the bare fact of one.

It chains in neither direction (`forward-sentex?` / `backward-sentex?` are false for it),
so the marker is never derived: asserting everything its body names concludes nothing. A
solve is the only reader.

**Grounding it is a join.** Every constraint rule visible from the solve's base — the
same `genlCx` up-closure that scopes the `assumptionRules` — has its body split by
predicate: a literal whose predicate names a ground choice head is a **choice literal**,
everything else is a **background** fact. The background literals are proved together
through the ordinary conjunctive prover over the same **registry leaf** as the
assumptionRule antecedents (`prove` in the base, belief-filtered and cost-planned, a
prover- or evaluatable-answered literal reachable like any other); each solution is then
extended across the choice literals against an index of the ground heads. Every satisfying binding yields one nogood over the choice-head ids
it used, with the substituted head riding along as that nogood's description. A negated
choice literal `(not <choice>)` carries through as a head required *absent*, so a body of
nothing but those is an at-least-one. Negated *background* literals are outside the
contract.

```clojure
;; no edge may have the same colour at both ends — two different individuals, which
;; the direct-clash detectors (always one shared individual) cannot express
(assert kb '(set/hardConstraint
             (implies (and (edge ?x ?y) (color ?x ?k) (color ?y ?k))
                      (monochrome ?x ?y)))
        'CxUniverse)
```

**A negated choice literal is joined like a positive one**, against the same index and
after them, so it may be partially ground and its own variables count as bindings:

```clojure
;; every pick must be taken — one nogood per ground (pick c), each forbidding that
;; head's absence.  `?c` is bound by nothing but this literal, and that is enough.
(assert kb '(set/hardConstraint (implies (not (pick ?c)) (must_pick ?c))) 'CxUniverse)
```

A negated literal matching *no* head drops its binding rather than constraining
anything, and that is the right answer either way: an atom that does not exist is
absent in every model, so it can never be false-*together* with the rest and the
requirement it guards is vacuous for that binding.

**Hard and soft differ at the encoding** ([asp.md](asp.md)). A hard nogood renders as an
ASPIF integrity constraint — no violation atom, no minimize term — so a model whose whole
signed body holds is excluded outright. A soft one takes the weak-constraint path the
auto-detected clashes take: a violation atom and a minimize term, so violating it costs
rather than excludes. An adjacency clash is not tradeable, which is what makes `:hard` the
class a colouring wants — and a program whose hard constraints already pin what must be
chosen is the one `:sat` below is for.

## `atMost` / `atLeast` — a cardinality bound over the choices

`functional P` is at-most-one value per subject. A bound past one needs its own
construct, because a hand-written encoding of at-most-`k` grounds one hard constraint per
`(k+1)`-subset of the contending heads — `C(n, k+1)` of them, which an application caps
its own inputs to keep finite. `atMost` / `atLeast` state the bound directly:

```clojure
(asp/atMost 6 ?c (build ?c transport))     ; at most 6 heads (build _ transport) hold
(asp/atLeast 1 ?t (assign ?a ?t))          ; at least 1 (assign a _) per group
(asp/softAtMost 6 ?c (build ?c transport)) ; the soft twins minimize a breach instead
(asp/softAtLeast 1 ?t (assign ?a ?t))
```

The surface mirrors `agg/count`'s projection ([aggregate.md](aggregate.md)): `?c` is the
**counted** variable, and the pattern's **other** variables are the **group**, so a bound
is stated once per ground combination of them. `(asp/atMost 6 ?c (build ?c transport))`
has no other variable, so it is one global bound over every ground `(build _ transport)`
head; `(asp/atMost 1 ?a (ferry ?a ?t))` groups by `?t`, so it is one bound per transport.

**Grounding is one solver cardinality atom per group, not a subset of nogoods.** The rule
is stored as a constraint rule whose consequent marker carries the operator and the count
(`rules/normalize-cardinality`); `solve-context` matches its pattern against the ground
choice heads, groups the matches by the group binding, and emits one `:cardinalities`
entry per group. `edge/translate` renders each as a single ASPIF weight-body statement —
`:- k+1 <= #count{ ... }` for a hard at-most, its default-negated mirror for at-least —
so a cap of 10 over 30 heads is one constraint rather than `C(30, 11)` ≈ 54M. An
application that clamped its inputs to keep the subset expansion finite can drop the clamp
and offer the full set.

**Hard excludes, soft costs once.** A hard bound is a weight-body integrity constraint: a
model reaching it is excluded. A soft bound derives a violation atom the same minimize
path penalizes, so breaching it costs the constraint's weight **once** — not once per unit
of overshoot. A soft bound is the generalization of a soft `set/hardConstraint`'s
per-binding cost, and it composes with `functional` on the same predicate: the two bounds
are separate constraints over the same heads.

**Two degenerate groups read as you would expect.** An at-most-`k` with `k` at least the
group size is vacuous and emits nothing. An at-least-`k` over a group smaller than `k` is
infeasible — a hard one excludes every model, a soft one always costs. An **empty** group
reads by whether the bound is global or grouped. A **global** bound — the counted variable
is the pattern's only variable — is one group even when no head matches, so a global
at-least over a choice predicate that grounds to nothing is infeasible, the way a
single-candidate one under an at-least of two is. A **grouped** bound is only the groups
some head realizes, so a group binding no head holds vacuously, the way a
universally-quantified constraint over an empty domain does.

**Why the bound is not `agg/count`.** The two count different things. `agg/count`
([aggregate.md](aggregate.md)) is a census over *believed* facts, recomputed at query time
outside any solve; a choice head is never believed (an `assumptionRule` does not chain), so
a census would count zero, and a census outside the search cannot prune the models the
solve enumerates. A cardinality bound has to be a **solver** cardinality atom that prunes
inside the search — which is what `atMost` / `atLeast` translate to, and `agg/count` is not
in that path.

**Every head weighs one.** A cardinality bound is `#count` — the unit-weight case
of `#sum`, which is the aggregate `edge/translate`'s weight body actually emits (each
member rides at weight 1). There is no weighted bound — no `asp/atMostSum` /
`asp/atLeastSum`, where each head would contribute a weight read from a fact, so a bound
on total tonnage rather than headcount cannot be stated. The encoding layer carries
arbitrary weights; the surface and the grounding carry none.

## `minimize` / soft-constraint priorities — the objective surface

A soft constraint costs 1 at one objective level. Two surfaces widen that to a *weighted,
prioritized* objective — the weak-constraint tier a lexicographic solve needs to pick one
answer out of a plateau of equal-cost optima:

```clojure
(asp/minimize <priority> ?weight <body>)                   ; sum ?weight over the chosen heads
(set/softConstraint <priority> (implies <body> <marker>))  ; a soft, at a chosen level
```

**`asp/minimize`** is a weak constraint over a choice head weighted by a datum: `body`
names a choice head and binds `?weight` off a background fact, and each chosen head pays
its weight at level `priority`. It is the `#minimize{ W@P, head : head, weight-fact }`
idiom:

```clojure
;; a chosen assignment costs its army→city step-distance; the objective at level 1 is the
;; total distance of the matching, so among equal-size matchings the shortest-march one wins
(assert kb '(asp/minimize 1 ?w (and (assign ?a ?c) (dist ?a ?c ?w))) 'CxUniverse)
(assert kb '(dist A1 C1 3) 'CxUniverse)   ; the weight is ordinary believed data
```

**A leading integer on `set/softConstraint`** tags that soft with an objective level; with
no tag a soft stays at level 1 (unchanged), and `set/hardConstraint` takes no priority — an
integrity constraint is not minimized.

**Grounding rides the soft-constraint path.** Both normalize into an internal
`set/softConstraint` whose consequent marker carries the operands — `(minimizeCost p ?w)` /
`(softPriority p marker)`, the same way a cardinality bound rides `cardAtMost`
(`rules/normalize-solve-surface`). `solve-context` reads the level and per-head weight back
off the ground marker (`rules/soft-cost-of`) onto the nogood's `:priority` / `:weight`, and
`edge/translate` — which already keyed a soft's objective level off `:priority` — emits its
per-literal weight (`[[v w]]` in place of `[[v 1]]`). So `asp/minimize` is just a soft whose
single-head body is penalized by a data weight, and nothing downstream needed a new arm. (It
is the weighted objective the "weighted `asp/atMostSum`" note above anticipated; the
cardinality *bounds* are still unit-weight.)

**Priority is lexicographic.** Distinct caller priorities become distinct ASPIF minimize
levels (`2 + rank(p)`, above the fixed keep-belief=1 and content-tiebreak=0 floors —
[asp.md](asp.md)), and a higher level dominates: the solve proves the higher objective's
optimum first, then the next only disambiguates among its optima. So a lower-priority
minimize is a **tiebreak** — it collapses a plateau of equal-cost optima to a unique answer
without the higher objective ever trading for a cheaper weight. Keep the weights **coarse
and bounded**: a distinct level with a small range proves out cheaply, whereas folding a
tiebreak into one level with big-M weights (to preserve the strict order) widens the range
branch-and-bound must close and is the *slower* encoding, not the faster one.

**A tiebreak singles out the optimum only as far as its weights discriminate.** When many
*distinct* solutions tie on the total weight — cost-degeneracy, not permutation symmetry — a
residual plateau survives, and neither a finer bounded weight nor a permutation symmetry
break removes it (a symmetry break needs interchangeable objects; distinct solutions are not
that). Bounding the problem's size is the lever there. (Empire's target match learned this:
the distance tiebreak turns a dense ~10×10 region from a time-limit stall into ~1 s, but a
fully-dense ~12×12+ region stays degenerate, so its candidate graph is kept sparse.)

## The inert-fact primitive

`core/assert-inert` stores and indexes a sentex but **skips the belief step**
(`add-premise` / `mark-premise`). The sentex lives in the record store and in the index
(trie, `[:context-root ctx]` root, term index), is inspectable via `sentexes-in-context`, and survives
`recover` — but it is **not a JTMS premise**, so it is never IN.

This is what makes labelings coexist, and it needs no ATMS. Every belief-filtered read —
`sentexes-matching`, `in?`, and the `settle` nogood scan (`negation-nogoods`) — sees only IN
sentexes. So an inert `(not head)` sitting in a context that sees a believed `head` forms
**no** nogood and moves **no** belief. Coexistence falls out of *not premising*.

```clojure
(assert-inert kb '(color Item red) 'CxRedWorld)   ; stored, inspectable, never IN
```

**A rule is refused here** (`:not-indexable`), and the reason is that this entry point does not
index one. A rule fires because `index-rule-sentex` posted its predicates, which happens
where a rule sentex is *created* — the assert entry point's new branch, and the generator mint —
so a rule stored inert would be unreachable by either chainer, and would stay unreachable
after somebody asserted it, that assert resolving to the stored sentex and taking the
branch that does not index. What it left was a rule `in?` called believed and no fact
ever fired. A labeling labels atoms and their negations, so nothing this primitive exists
for wants one.

The **other** inertness is a rule's own: `set/inertRule` is believed, indexed and
browsable and chains in neither direction — a rule kept as documentation
([inference.md](inference.md)). One word, two states, and the distinction is whether the
KB believes what it stored.

## `(do/label Base Into [mode])`

Grounds the `assumptionRules` visible from `Base`, constrains the ground heads, solves,
and — under `:all` — materializes **one inert labeling context per optimal answer set**.
The optional third argument is the mode: `:all` (the default), `:one` or `:sat`, and
anything else is refused as `:not-assertible`.

1. **Ground** — each assumptionRule's antecedents are proved over the knowledge visible
   from `Base` (a scoped, belief-filtered join — not a whole-KB scan), its head
   substituted per solution. The join runs over a **registry leaf** (`provers/solve-goal`),
   the same division `vaelii.core/query` runs: an antecedent is answered by a stored fact
   (through `FactProver`), a backward rule, *or a registered prover* — a transitive or
   cached closure, an evaluatable, an app-registered reasoner over Clojure state. So a
   candidate that rests on a computed relation — `(sameLandmass ?a ?b)` over a Clojure
   partition, `(lessThan ?x 10)` — is a legal antecedent, not something the caller must
   pre-project into stored candidate facts. (The leaf costs a prover-answered conjunct by
   the prover's own `est-bindings`, so an open relation plans last rather than enumerating
   first.) A rule's `exceptWhen` guard is honored per binding, evaluated in `Base` —
   grounding is a fourth consumer of a rule's firing beside the three chainers, and a
   choice the exception holds of is not offered. That is how a candidate menu is
   filtered declaratively ("any cell may take any value, except one already ruled
   out"). The grounding stays **in memory**: the Program keys the heads by
   program-local ids — never KB handles — and the menu comes back as `:choices` in
   the result. Nothing about it is stored. A grounding is derived solver working
   state, recomputable from the assumptionRules and the base's believed facts; a
   persisted copy would carry no justification linking it to what produced it, and
   would rot silently the moment the base moved.
2. **Constrain** — clashes among the direct heads become nogoods: a `(not X)`/`X` pair, a
   `functional` predicate given two values, a `disjoint` type clash. Each constraint rule
   visible from `Base` is ground into nogoods over the heads its body names as well —
   hard ones as integrity constraints, soft ones minimized like these.
3. **Solve** — under `:all`, the `:all-optima` solver mode over the tiebreak-off encoding
   (`edge/enumerate-optima`) returns every optimal answer set as a distinct set of
   chosen-true heads; under `:one` / `:sat` a single `:label` solve returns one. The
   tiebreak is off in every mode: singling out one of several equally valid answers is
   not what a solve is for, and the content-keyed program is order-independent without
   it.
4. **Materialize** (`:all` only) — per answer set, a `genlCx` child `Into1`,
   `Into2`, … of `Base` holding `(head)` for a chosen-true head, `(not head)` for a
   chosen-false one, and an inert `(labelingOf <ctx> <Into> <i>)` **ownership marker**.
   A choice head must be a **positive** literal for this round-trip to hold: `(not
   head)` marks a chosen-*false* positive head, so a head that were itself `(not X)`
   would read back as its positive core with the polarity flipped. Grounding refuses a
   negated head (`:choice-head-not-positive`) before any world is written.

The numbered names are for humans; **ownership is recorded in the marker, never
inferred from a name**. Rediscovery (`do/classify`, and the replace sweep below) reads
the markers back through the term index, so a user context that happens to be named
`<Into><i>` is neither aggregated nor swept — and materialization skips any
numbered slot an unrelated context already occupies, so it is never written into
either. Two belt-and-braces guards back this: the sweep refuses to touch a context
holding any *believed* sentex (everything a solve writes is inert by construction),
and `retract!` tears an inert sentex down directly. And the sweep takes a context's
own **extent**, plus — for a marked labeling context only — the one `(genlCx <ctx>
<Base>)` edge that placed it under *this run's* base, matched whole rather than by its
functor: a sentex *about* a solve context asserted from elsewhere (an edge a user hung
under `<Into>Class` or under a context of their own, a claim naming `<Into>1`) is that
user's and survives. Hanging a labeling under contexts of one's own is the ordinary way
to read a solved world beside other knowledge, and a functor-wide sweep would delete
those edges on the next run.

**Replace-on-rerun, under `:all`** (the other two modes write nothing to replace).
Re-running `do/label` with the same `Into` clears the previous run's artifacts before
writing the new ones: every marked labeling context — its truth values, its marker, *and*
its placement edge under the base, so a surplus stale context (a run that shrank from
three labelings to two) drops out of the hierarchy and `do/classify`
cannot sweep it back in — plus the classification. So a solve converges instead of
accreting; without the sweep, two groundings' truth values would union into one
context, and an inert `(head)` beside an inert `(not head)` asserts nothing at all. A
run that grounds *no* choices clears too — "no labelings" is its honest result. The
one exception is `:no-backend`: nothing was computed, so the previous artifact is left
standing.

**A run that cannot replace what is there refuses**, with `:labeling-run-blocked`, and
refuses before the solve rather than after it. Two things stop the sweep, and
proceeding past either is worse than not running at all:

- **A labeling context somebody has asserted believed content into.** The sweep
  declines to touch it — that is the guard above, and it is right — but the old marker
  then survives beside the new run's, and `do/classify` aggregates two groundings into
  one classification.
- **A labeling whose `labelingOf` marker has been retracted.** The marker is an
  ordinary sentex, and rediscovery is the only way the sweep finds a context, so losing
  one hides that context from the sweep forever while its `genlCx` edge goes on holding
  it in the hierarchy — a believed monotonic edge nothing will ever retract, and one
  more leaked slot on every re-run. It is recognized instead by what a marker-less
  artifact still is: a slot name, a non-empty extent with nothing believed in it, and
  this run's own placement edge under `Base`.

Believed content is what distinguishes a user's context from a lost artifact, and it is
decisive in both directions: a context of one's own that occupies a slot — even one hung
under this very base — is neither swept nor refused over. The refusal names what is in
the way; retracting that context's extent, or naming a different `Into`, clears it.
`(do/label _ _ :one)` and `:sat` are unaffected, having nothing to replace.

```clojure
(assert kb '(set/assumptionRule (implies (candidate ?c) (color ?c red))) 'CxUniverse)
(assert kb '(set/assumptionRule (implies (candidate ?c) (color ?c blue))) 'CxUniverse)
(assert kb '(functional color) 'CxUniverse)
(assert kb '(candidate Item) 'CxUniverse)

(assert kb '(do/label CxUniverse CxPlan) 'CxUniverse)
;; => CxPlan1: (color Item red)  (not (color Item blue))
;;    CxPlan2: (color Item blue) (not (color Item red))
;; base belief unchanged; contradictions 0; both worlds coexist
```

### The three modes

* **`:all`** (the default) enumerates every optimal answer set and materializes each, so
  the worlds coexist and persist for `do/classify` to aggregate. This is the mode for
  studying the whole space, and enumeration is infeasible where the optima are
  astronomically many — a large graph colouring has more proper colourings than can be
  listed.
* **`:one`** takes one optimal answer set from a single solve, minimizing defeated
  assumptions (keep as much belief as possible), and returns it **persisting nothing**.
  This is the mode for wanting an answer rather than an artifact, and it stays feasible
  at scale: one solve, no enumeration, no materialization. `Into` is accepted for a
  uniform imperative shape and unused.
* **`:sat`** is `:one` without the keep-belief objective — plain satisfaction, so clingo
  stops at the first model instead of proving cost-optimality over the choice atoms.
  Where the hard constraints already pin what must be chosen, "keep as much as possible"
  adds nothing and the optimization is a scaling wall.

The result is `{:base :into :choices [..] :labelings [{:context :true [..] :false [..]}]
:count n}`, with `:context` nil under `:one` / `:sat`, phase timings (`:ground-ms`,
`:translate-ms`, `:solve-ms`) for a profiling caller, and `:count 0` plus a `:reason`
when there is no labeling to report: `:no-choices` (nothing was ground), `:no-backend`
(nothing could be solved), or `:unsatisfiable`.

**`:unsatisfiable` is the answer when the hard constraints admit no model.** A hard
at-least-one over choices every other hard constraint forbids has no solution, and
"none" is what a solve of it reports. It matters most under `:one` / `:sat`, where a
single answer set comes back: an infeasible program keeps nothing, and *keeping
nothing* is indistinguishable in shape from the one perfectly ordinary world in which
every choice happened to be false — which for such a program is a world its own
constraints exclude. So the count is 0 and the reason says why, rather than one
labeling being reported that no model backs. Under `:all` the same program enumerates
nothing and reports `:count 0` on its own.

## `(do/classify Into)`

Gathers brave/cautious over the labelings a prior `do/label` produced — a pure
aggregation over the persisted contexts, no solver, no whole-KB scan, and one extent
read per labeling (each is loaded once into an in-memory polarity table). A choice
head is:

* **forced** — `(head)` in every labeling (a cautious / skeptical consequence);
* **excluded** — `(not head)` in every labeling;
* **supportable** — otherwise (a brave / credulous consequence only).

The result is written as inert sentexes `(forced H)` / `(supportable H)` / `(excluded H)`
in `<Into>Class`, for inspection — replacing its own previous output, the same
replace-on-rerun discipline `do/label` applies to the labelings.

```clojure
(assert kb '(do/classify CxPlan) 'CxUniverse)
;; CxPlanClass: (supportable (color Item red)) (supportable (color Item blue))
```

## Inspecting a solve

Everything a solve produces is an ordinary sentex in a context, so it is read the way any
context is: `sentexes-in-context`, the term index (`find-sentexes`), and the web browser.
The truth values are **inert**, so `sentexes-matching` / `ask` (belief-filtered) will *not* return
them — read the context's extent, not its belief. Retracting a labeling's sentexes
removes it — `retract!` tears an inert sentex down directly through the removal choke
point, since it is not a TMS datum and the dependency sweep cannot find it — and
re-running `do/label` under `:all` replaces the whole run.

## What a choice constrains

A constraint — an auto-detected clash or a constraint rule alike — reaches the **direct**
ground choice heads and nothing further. Choices do **not** propagate through ordinary
rules — "choosing red makes it warm, and warm things can't be here" is not expressible
as one, because the Program is built from the choice
heads and the nogoods standing over them: nothing runs the chainer with a choice held
hypothetically, and nothing emits the rule base to clingo's grounder. A constraint that
only bites downstream of a rule therefore has nothing to bite on.

## Relationship to dilemmas and `do/labeling`

A defeasible-default **dilemma** (`contradictions`) is *represented*, not solved — both
sides stay believed and the engine arbitrates nothing. Classifying one is an opt-in
solve: `(do/label CxDilemma Into)` then `(do/classify Into)`, which produces persistent
inert contexts. `(do/labeling Ctx)` commits one labeling *live* into base belief (global,
one at a time — docs/labeling.md); `do/label` is the inert, coexisting, persistent path.
