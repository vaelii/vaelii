# Solving: assumptionRule and persistent, inert labeling contexts

- **Covers:** how `assumptionRule`, `solveRule`, constraint, cardinality, and objective
  (`asp/minimize` / soft-constraint priority) declarations become `do/label`'s
  persistent, inert labeling contexts, without touching base belief.
- **Not here:** the ASPIF encoding and solver backends the resulting program runs on →
  [asp.md](asp.md); committing one labeling of a dilemma inside a context →
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
canonicalized into the `RuleSentex` record's **`:effect`** field as `:choose` and, being part
of the rule's identity, into the **trie key** — a choice rule and its bare twin are
different sentexes.

A choice is a *head*, **not** a strength class (`strength.clj` keeps its two classes;
there is no third). A choice rule's `:engines` is `#{:solve}`, so `forward-sentex?` /
`backward-sentex?` return false for it and it **never chains into belief** — asserting `(candidate Item)` does not
derive `(color Item red)`. A solve is the only thing that consults it. So a direction
wrapper, `set/defaultRule` or a `:direction` opt on a choice rule states nothing, and
`assert` refuses it, as it refuses a rule wrapped as both a choice and a constraint
([canonicalization.md](canonicalization.md#rule-wrappers-become-fields)).

**This is where a disjunctive conclusion lands.** `(implies <body> (or C1 C2))` is
refused at the assert entry point, and the refusal points here: a disjunctive head says one of
two things holds without saying which, and belief is a label on a stored sentex rather
than on a set of them, so forward chaining has nothing to place. What it *is* is a
choice, and a choice has a home — one `set/assumptionRule` per alternative, plus a
`set/hardConstraint` over the combinations that cannot stand together, read back as an
answer set. (A rule **antecedent** that disjoins is a different question with a different
answer: it is polycanonicalized into one rule per alternative and never reaches a solve
at all — [canonicalization.md](canonicalization.md).)

## `solveRule` — a derived atom inside a solve

```clojure
(set/solveRule (implies <body> <head>))
```

A normal rule (`head :- body` in ASP) that a solve runs: in each answer set its head holds
exactly when some ground instance of its body does there. It is the third of the solve's
rule forms — `assumptionRule` offers a choice, `solveRule` derives what follows from the
choices, a constraint forbids — and the one that lets a constraint bite downstream of a
choice: "the elements the picked sets cover", "the nodes the picked edges reach".

The wrapper adds `:solve` to the record's `:engines` and leaves `:effect` `:derive`
([canonicalization.md](canonicalization.md#rule-wrappers-become-fields)), so how the rule
runs **in base** is said the ordinary way, beside it:

| written | engines | in base | in a solve |
|---|---|---|---|
| `(set/solveRule R)` | `#{:backward :solve}` | answers backward goals | derives its head |
| `(set/forwardRule (set/solveRule R))` | `#{:forward :backward :solve}` | forward and backward | derives its head |
| `(set/inertRule (set/solveRule R))` | `#{:solve}` | nothing | derives its head |

**Which to write.** A rule true of the domain — `atCapital` holds of whoever is assigned a
capital — is the bare `set/solveRule`: base answers it over what it believes, and every
answer set derives it over what that set chose, so a labeling states what base would state
of the same assignments. A rule that exists only to phrase a constraint — `covered`,
`reach` from a chosen root — is `set/inertRule` beside it: in base it would answer nothing
useful, and a backward walk of a recursive one costs a search per goal. Forward beside it
is for a rule whose base conclusions are worth materializing; a choice head is never
believed, so a forward solve rule fires in base only on facts base holds. A choice or
constraint rule runs in a solve already and takes no `set/solveRule`, and neither does a
`set/defaultRule`, since one answer set has no defeat to apply — both are refused
`:not-well-formed`.

**Grounding runs when `do/label` builds its program**, in memory, and stores nothing. A
solve rule fires forward over the atoms that can become true — every ground choice head,
and every atom an earlier firing concluded — until no firing concludes a new atom. Each
firing becomes one ground rule of the program, `h :- a1, .., not ak`
([asp.md](asp.md)). Unlike a forward rule's firing in base, a firing here puts no sentex
in the records and no justification in the JTMS: the solver reads the ground rules and
decides, per answer set, which derived atoms hold.

**Grounding splits the body by predicate**, as a constraint's is. A literal over a
**program predicate** — a ground choice head's, or the head of a believed solve rule
visible from `Base` — matches the program's atoms; every other literal is background,
proved once over what `Base` believes (the registry leaf `assumptionRule` antecedents are
proved over). A predicate no visible solve rule concludes is therefore background even in
a constraint body, so `(not (covered ?x))` there reads believed negation and forbids
nothing when no rule derives `covered`. A negated program literal `(not (busy ?w))` is
default negation in the answer set, and it must be ground once the positive literals are.
The atoms are grounded by a semi-naive fixpoint from the choice heads, so a rule may read another solve rule's head or its own; recursion is what
reachability needs, and the solver's stable-model reading gives a loop of atoms that only
support each other no atom — two chosen edges `B → C` and `C → B` do not make B reachable
from a root that reaches neither. What `Base` already holds of a solve rule's head is
proved there and enters every answer set as a fact, as a base fact holds in every
labeling context below the base. A head building a larger term from its body's derives
without bound, and grounding refuses past 200 000 atoms.

Each semi-naive round starts a rule's join at the literal that reads the atoms the round
before added, and reads the background bindings by the variables those atoms bind. The
atom indexes carry over from round to round, so a chain of `n` derived atoms costs `n`
rounds of one atom each rather than `n` rounds over all of them; `lein perf`'s
`solve-rule-grounding` check holds the cost per derived atom flat from 500 atoms to
8 000.

A derived atom is recorded like a choice: a labeling context holds `(head)` where it is
derived and `(not head)` where it is not, `do/classify` reads it the same way, and
`do/label` lists the derived atoms in `:derived`. An `exceptWhen` on a solve rule is
honored per binding, evaluated in `Base`.

```clojure
;; pick at most two sets; every element must be covered by a picked one
(assert kb '(set/assumptionRule (implies (candidate ?s) (pick ?s))) ctx)
(assert kb '(asp/atMost 2 ?s (pick ?s)) ctx)
(assert kb '(set/inertRule (set/solveRule
              (implies (and (pick ?s) (member ?x ?s)) (covered ?x)))) ctx)
(assert kb '(set/hardConstraint
              (implies (and (element ?x) (not (covered ?x))) (uncovered ?x))) ctx)
```

An `assumptionRule`'s antecedents are proved over base belief, so a derived atom does not
decide whether a choice is offered: a choice is offered or not by what `Base` holds. A literal over a choice
predicate reads the ground choice heads alone, so what `Base` believes of that predicate
outside an offered choice is not in the program; only a solve rule's head has its base
instances entered as facts. A program needs a choice to solve: solve rules with no ground
choice report `:no-choices`.

### The solve's rule forms side by side

| | `set/assumptionRule` | `set/solveRule` | `set/hardConstraint` / `softConstraint` | `asp/atMost` / `atLeast` |
|---|---|---|---|---|
| **in base** | chains in neither direction | as its direction wrappers say | chains in neither direction | chains in neither direction |
| **body read over** | `Base` belief, the whole body | program literals over the atoms, the rest over `Base` | program literals over the atoms, the rest over `Base` | one pattern over the atoms; a `…Sum` body's other literals over `Base` |
| **reads a derived atom** | no | yes | yes | yes |
| **in the program** | `{h}.` per ground head | `h :- a1, .., not ak` per ground instance | `:- body` per binding, or a violation atom and a `#minimize` | one weight-body statement per group |
| **in a labeling** | `(h)` / `(not h)` | `(h)` / `(not h)` | nothing | nothing |
| **auto clashes** (`functional`, `disjoint`, `X` / `(not X)`) | among the choice heads | not applied | — | — |

## `hardConstraint` / `softConstraint` — a nogood over the choices

```clojure
(set/hardConstraint (implies <body> <marker>))
(set/softConstraint (implies <body> <marker>))
```

A constraint rule's head is a **contradiction marker**, not a truth, and its body is a
conjunctive nogood mixing background facts with choice-head patterns. Like
`assumptionRule` it is a virtual wrapper canonicalized into the `RuleSentex` record — into
**`:effect`**, as `:forbid` (hard) or `:penalize` (soft) — and, being part of the rule's
identity, into the trie key: `sentex/key-tokens` gives every rule a constant constraint
slot, so a hard constraint, its soft twin and its bare twin are three sentexes.
`rules/constraint-of` reads the class (`:hard` / `:soft`) back off the record,
`rules/constraint?` the bare fact of one.

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

A negated literal still holding a variable ranges over the atoms the program has, so it
contributes one nogood per atom it matches and none for an atom that does not exist. A
negated literal the positive join left **ground** names one atom, and when the program
has no such atom it is absent in every model: the literal holds, adds no member, and the
binding stays. A binding whose members all drop so is a nogood with none, and a hard one
admits no model — a task no candidate can take, required taken, is unsatisfiable rather
than silently met.

**Hard and soft differ at the encoding** ([asp.md](asp.md)). A hard nogood renders as an
ASPIF integrity constraint — no violation atom, no minimize term — so a model whose whole
signed body holds is excluded outright. A soft one takes the weak-constraint path the
auto-detected clashes take: a violation atom and a minimize term, so violating it costs
rather than excludes. An adjacency clash is not tradeable, which is what makes `:hard` the
class a colouring wants — and a program whose hard constraints already determine what must be
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
choice heads and the solve rules' derived atoms, groups the matches by the group binding,
and emits one `:cardinalities` entry per group. `edge/translate` renders each as a single ASPIF weight-body statement —
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

### `atMostSum` / `atLeastSum` — a weighted bound

A weighted bound sums a weight per head where `atMost` counts heads:

```clojure
(asp/atMostSum 9 ?w ?c (and (load ?c) (tons ?c ?w)))      ; at most 9 tons loaded
(asp/atMostSum 5 ?w ?c (and (onto ?c ?t) (tons ?c ?w)))   ; at most 5 tons per truck ?t
(asp/atLeastSum 4 ?w ?u (and (deploy ?u) (power ?u ?w)))  ; deployed strength at least 4
(asp/softAtMostSum 9 ?w ?c (and (load ?c) (tons ?c ?w)))  ; the soft twins cost once, as above
```

`?w` is the weight variable and `?c` the counted one, and the body's other variables are
the group, as for `atMost`. The body names exactly one choice or derived literal, the head
the weight counts toward, and binds `?w` off background facts, as an `asp/minimize` body
does. Each distinct binding of the weight, counted and group variables adds its weight to
its head, the way `#sum{W,C : …}` sums distinct tuples, so a head that two facts weigh
counts both weights. The entry renders as the weight body an unweighted bound renders as,
each member at its weight (`edge/card-encoding`): `atMost` is the case of every weight 1.

A weight is data, so the solve that grounds the bound checks it. The solve refuses a
negative or non-integer weight, a group whose weights total past the solver's 32-bit range,
and a body naming no program literal or several, each as `:not-well-formed`. A zero weight
is dropped from the weight body. A weighted bound over integer *variables* (a start time,
a quantity the solve picks) does not exist: a weight is a fact about a head, and the head is
the only thing the solve decides ([asp.md](asp.md#where-the-asp-layer-stops)).

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
per-literal weight (`[[v w]]` in place of `[[v 1]]`). `asp/minimize` is a soft whose
single-head body is penalized by a data weight, and the cardinality bounds stay
unit-weight.

**Priority is lexicographic.** Distinct caller priorities become distinct ASPIF minimize
levels (`2 + rank(p)`, above the fixed keep-belief=1 and content-tiebreak=0 floors —
[asp.md](asp.md)), and a higher level dominates: the solve proves the higher objective's
optimum first, then the next only disambiguates among its optima. So a lower-priority
minimize is a **tiebreak** — it collapses a plateau of equal-cost optima to a unique answer
without the higher objective ever trading for a cheaper weight. Keep the weights **coarse
and bounded**: folding a tiebreak into one level with big-M weights (to preserve the
strict order) widens the range branch-and-bound must close, so a distinct level with a
small range closes sooner.

**A tiebreak singles out the optimum only as far as its weights discriminate.** When many
*distinct* solutions tie on the total weight — cost-degeneracy, not permutation symmetry — a
residual plateau survives, and neither a finer bounded weight nor a permutation symmetry
break removes it (a symmetry break needs interchangeable objects; distinct solutions are not
that). Bounding the problem's size removes it.

## The inert-fact primitive

`core/assert-inert` stores and indexes a sentex but **skips the belief step**
(`add-premise` / `mark-premise`). The sentex lives in the record store and in the index
(trie, `[:context-root ctx]` root, term index), is inspectable via `sentexes-in-context`, and survives
`recover` — but it is **not a JTMS premise**, so it is IN only while a derivation
concludes its sentence (below).

This is what makes labelings coexist, and it needs no ATMS. Every belief-filtered read —
`sentexes-matching`, `believed?`, and the nogood placement (`chain/place-nogoods!`) — sees only
IN sentexes. So an inert `(not head)` sitting in a context that sees a believed `head` forms
**no** nogood and moves **no** belief. Coexistence falls out of *not premising*.

```clojure
(assert-inert kb '(color Item red) 'CxRedWorld)   ; stored, inspectable, never IN
```

A derivation reaches an inert sentex as it reaches any stored sentex. A rule firing that
concludes the sentence, or a `decontextualized_predicate` lift into CxUniverse, gives the
record a node and a justification, and the record is IN while that justification holds.
A sweep that drops the justification removes the node and keeps the record, which carries
the `:inert` provenance mark (`integrate/swept-records`). `retract!` of the record's own
handle deletes the record.

**A rule is refused here** (`:not-indexable`), and the reason is that this entry point does not
index one. A rule fires because `index-rule-sentex` posted its predicates, which happens
where a rule sentex is *created* — the assert entry point's new branch, and the generator mint —
so a rule stored inert would be unreachable by either chainer, and would stay unreachable
after somebody asserted it, that assert resolving to the stored sentex and taking the
branch that does not index. Such a rule is one `believed?` answers true for and no fact fires. A labeling labels atoms and their negations, so nothing this primitive exists
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

The rules a run reads — choice, constraint and cardinality rules, and `set/solveRule`s
(`rules/solve-sentex?`) — come off the rule extent's `:solve` node, a count trie ending in
the context (`reads/as-stored-rules-in`). The extent records storage; a run reads the
leaves for `Base` and its `genlCx` ancestor set and keeps the rules `res/rule-believed?`
holds. Finding the rules
therefore fetches one record per solve rule in that ancestor set and none of its facts
(`solve_context_test`, `finding-a-solves-rules-reads-its-rules-not-the-corpus`).

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
   first.) A `transitive` predicate's literal answers from the closure once the join has
   bound one end, as at `query`: `(ancestorOf ?x Cal)` grounds every `?x` above `Cal`.
   With both ends still open when the join reaches it, the literal answers from the
   stored edges alone ([taxonomy.md](taxonomy.md#predicate-metadata)), and the result's
   `:unenumerated` names the predicate (`:unenumerated-in-guards` the subset read inside
   an `exceptWhen` guard). A conjunct that binds one end, such as `(and (person ?y)
   (ancestorOf ?x ?y))`, makes the join read the closure. A rule's `exceptWhen` guard is honored per binding, evaluated in `Base` —
   grounding is a fourth consumer of a rule's firing beside the three chainers, and a
   choice the exception holds of is not offered. That is how a candidate menu is
   filtered declaratively ("any cell may take any value, except one already ruled
   out"). The grounding stays **in memory**: the Program keys the heads by
   program-local ids — never KB handles — and the menu comes back as `:choices` in
   the result. Nothing about it is stored
   ([defenses.md](defenses.md#a-solves-grounding-is-not-stored)).
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
either. Two guards back this: the sweep refuses to touch a context
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
run that grounds *no* choices clears too — "no labelings" is its result. The
one exception is `:no-backend`: nothing was computed, so the previous artifact is left
standing.

**A run that cannot replace what is there refuses**, with `:labeling-run-blocked`, and
refuses before the solve rather than after it. Three things stop the sweep, and
proceeding past any of them is worse than not running at all:

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
- **A non-empty `<Into>Class` with no `classificationOf` marker.** The classification
  context has one fixed name, so the marker is the only evidence that `do/classify`
  wrote it. Without one the context is a user's context of that name or a
  classification written before the marker existed, and `do/label` and `do/classify`
  both refuse rather than sweep it (`:unmarked` in the `ex-data`).

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
;; => CxPlan1: (color Item blue) (not (color Item red))
;;    CxPlan2: (color Item red)  (not (color Item blue))
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
  Where the hard constraints already determine what must be chosen, "keep as much as possible"
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
in `<Into>Class`, for inspection, beside an inert `(classificationOf <Into>Class <Into>)`
ownership marker — replacing its own previous output, the same replace-on-rerun
discipline `do/label` applies to the labelings.

```clojure
(assert kb '(do/classify CxPlan) 'CxUniverse)
;; CxPlanClass: (supportable (color Item red)) (supportable (color Item blue))
;;              (classificationOf CxPlanClass CxPlan)
```

## The ASP reading of a program

`v/answer-sets kb context opts` grounds a context's program as `do/label` does, and writes
nothing. Its encoding holds neither the keep-belief objective nor the content-keyed
tiebreak, so a solve optimizes the program's own `minimize` and soft constraints alone. Its
optimal answer sets are the ones clingo reports for the same program. In the two-colour
example above, the empty choice is an optimum beside each colour; `do/label`'s keep-belief
objective excludes it. The run file's solve reads call `answer-sets`
([operations.md](operations.md#run-files)), and so does the daemon's `:answer-sets` op.

`:reading` picks what a solve answers. Each reading is one backend solve:

| `:reading` | solves | returns |
|---|---|---|
| `:all` (default) | `:all-optima` | `:answer-sets`, each the choice and derived atoms true in one optimal answer set, and `:answer-set-costs` |
| `:one` | `:label` | `:answer-sets` holding one optimal answer set |
| `:brave` | `:classify-supportable` | `:consequences`, the atoms true in some optimal answer set |
| `:cautious` | `:classify-true` | `:consequences`, the atoms true in every optimal answer set |

A brave or cautious solve enumerates no answer set. The backend's consequence mode
converges on the set over one search ([asp.md](asp.md#the-time-limit) counts the solves).

The other options set the solve. Each is a clingo flag:

| option | readings | clingo flag | effect |
|---|---|---|---|
| `:among :optimal` | all | `--opt-mode=optN` | the optimal answer sets only (the default) |
| `:among :all` | all | `--opt-mode=ignore` | every answer set, the objective ignored |
| `:among [c …]` | all | `--opt-mode=enum,c,…` | every answer set whose cost vector is at most `[c …]`, compared highest level first |
| `:limit n` | `:all` | `--models=n` | at most `n` answer sets |
| `:project pattern` | `:all` | `--project` | one answer set per distinct set of atoms unifying `pattern`, each holding only those atoms |
| `:opt-strategy` | all | `--opt-strategy` | `:bb` or `:usc` (`VAELII_ASP_OPT_STRATEGY` when absent) |
| `:solve-limit n` | all | `--solve-limit` | the conflict limit (`VAELII_ASP_SOLVE_LIMIT` when absent; 0 lifts it) |
| `:time-limit s` | all | `--time-limit` | the seconds one solve may run (`VAELII_ASP_TIME_LIMIT` when absent; 0 lifts it) |

`answer-sets` refuses a key its reading does not read, and a value outside an option's
domain (`:unknown-option`). Under an `:among` other than `:optimal` a solve claims no
optimum: `:costs` is nil, a complete search is `:sat`, and `:answer-set-costs` holds each
answer set's cost vector. The vector is nil under `:among :all`, since the solver computes
no cost when it ignores the objective. Several models can share one projection, and the solver
reports it once.

`:status` is the solve's: `:optimum` under an objective, `:sat` without one, `:unsat` when
no answer set exists, and `:interrupted`, `:best-effort` or `:unknown` when a limit stopped
the search. A search that stops at its `:limit` has its whole answer, so its status is
`:optimum` or `:sat`.

## Inspecting a solve

Everything a solve produces is an ordinary sentex in a context, so it is read the way any
context is: `sentexes-in-context`, the term index (`find-sentexes`), and the web browser.
The truth values are **inert**, so `sentexes-matching` / `ask` (belief-filtered) will *not* return
them — read the context's extent, not its belief. Retracting a labeling's sentexes
removes it — `retract!` tears an inert sentex down directly through the removal choke
point, since it is not a TMS datum and the dependency sweep cannot find it — and
re-running `do/label` under `:all` replaces the whole run.

## What a choice constrains

A constraint rule (hard, soft or `asp/minimize`) and a cardinality bound reach the ground
choice heads and the atoms the solve rules derive from them; an auto-detected clash reaches
the choice heads alone. A choice propagates through a `set/solveRule` and through nothing
else: "choosing red makes it warm, and warm things can't be here" is a solve rule
concluding `warm` and a constraint over it. A rule without the wrapper is not ground into
the program — nothing runs the chainer with a choice held hypothetically — so a
constraint that bites only downstream of one has nothing to bite on.

## Relationship to dilemmas and `do/labeling`

A defeasible-default **dilemma** (`contradictions`) is *represented*, not solved — both
sides stay believed and the engine arbitrates nothing. Classifying one is an opt-in
solve: `(do/label CxDilemma Into)` then `(do/classify Into)`, which produces persistent
inert contexts. `(do/labeling Ctx)` commits one labeling inside `Ctx`, its defeats scoped to `Ctx`
([labeling.md](labeling.md)); `do/label` is the inert, coexisting, persistent path.
