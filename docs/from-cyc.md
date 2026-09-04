# Arriving from Cyc

- **Covers:** the OpenCyc and ResearchCyc vocabulary mapped onto this one — concepts,
  contexts, negation, operations, truth maintenance and rules — and the places where a
  shared name covers a different semantics.
- **Not here:** reading an OpenCyc corpus *in*, which is a plugin and a different task →
  [foreign.md](foreign.md), [kbs.md](kbs.md); the engine itself, which every row below
  links to → [README.md](README.md).
- **Assumes:** sentex, context, handle → [glossary.md](glossary.md). The API this page
  calls is [api.md](api.md).

One-way orientation, not a compatibility claim. The two systems share a great deal of
vocabulary and part company on the semantics more often than the names suggest, so the
third column is the one to read.

## Word for word

| in Cyc | here | what changes |
|---|---|---|
| `Mt` | context | a sentex is in exactly one, and reads see up the `genlCx` ancestor set → [contexts.md](contexts.md) |
| `genlMt` | `genlCx` | cached and recomputed on edge change, not derived by a rule |
| assertion | sentex | a sentence *plus* the context it holds in; the pair is the unit |
| constant | symbol | the role is read off the spelling, and `assert` refuses one that breaks it |
| collection | a type, which is a **unary predicate** | `(dog Muffet)`, never `(isa Muffet Dog)` |
| `genls` | `genl` | |
| `genlPreds` | `genl` | one relation for both, because a type *is* a predicate here |
| `argIsa` | `arg` | positional typing as one ternary declaration: `(argIsa P 1 T)` → `(arg P 1 T)` |
| `arg1Isa` | `arg1` | the binary projection of `arg` at position 1 — bridged to `arg` by rules and sharing its declaration checks, but relating **stored** declarations only; a generalized or inherited reading must be asked of `arg` |
| `arg2Isa` | `arg2` | the projection at position 2, with the same bridging and the same stored-only caveat |
| don't-care variable `??` | a head existential `(exists ?y C)` | syntactic rather than a naming convention, and skolemized to a deterministic NAT on firing → [skolem.md](skolem.md) |
| `wff?` | `check` | returns a vector of problem maps rather than a verdict, so it says *what* is wrong |
| rename | — | no equivalent. `sameAs` / `rewriteOf` **merge** two terms onto an elected representative and mark the displaced spelling superseded, which is a different act → [equality.md](equality.md) |

The four spellings, because `assert` enforces them (→ [naming.md](naming.md)):
`parentOf` is a predicate, `Fido` an individual, `physical_object` a type, `CxCore` a
context. A bare lowercase word like `dog` is both a predicate and a type name, and arity
decides which; a multi-word name commits itself — an underscore to arity 1, an interior
capital to arity 2 and above.

## What a Cyclist's habits do here

**`arg` is a gate first.** `(arg parentOf 1 animal)` — the shipped ontology's own
declaration — refuses `(parentOf Fern Mary)` where `Fern` is a `plant`: `ex-info` with
`:type :arg-type`, exactly as Cyc's constraint would refuse it. What convicts is that the
hierarchy **places** `Fern` and the place it puts him does not reach `animal`. The
`(disjoint animal plant)` sitting beside those types is not what does the work — a type
the constraint's own type does not subsume is enough on its own.

There is one open-world escape and it is deliberate: a **symbol** the `genl` hierarchy
places nowhere *the asserting context can see* cannot contradict anything, so it passes.
`(parentOf Zork Mary)` stores when nothing is known about `Zork`. A **literal** is not in
that escape: its EDN kind is knowable from the value itself and those kinds sit in the
same `genl` lattice, so `(parentOf 212 Mary)` is refused `:arg-type` — 212 is a `number`,
and `number` does not reach `animal` ([argtypes.md](argtypes.md)).

The *entailment* reading — the same declaration minting `(animal Fred)` from
`(parentOf Fred Mary)` — is real but **opt-in**, behind
`checks/*assertive-arg-types?*` (root value false, or `VAELII_ASSERTIVE_ARG_TYPES=1`).
It is additive: turning it on keeps the refusal and adds the derived type, as a justified
sentex that retracts like any conclusion. See [argtypes.md](argtypes.md).

**Undeclared is unconstrained — which is not the same as unchecked.** No predicate has to
be declared before use, so `(fghgwgads 212)` stores and a typo is the same bug class as a
predicate nobody has gotten to yet. But as soon as declarations exist they bind: `assert`
refuses on arity, `arg`, `genlArg`, `interArg`, disjointness, asymmetry and
functionality, on top of the naming, groundness, structural and stratification checks it
always runs. `check` reports the lot without storing → [api.md](api.md).

**A contradictory pair coexists.** Two `:default` claims that rebut each other both stay
believed and are reported as a represented dilemma by `contradictions`; the engine
arbitrates nothing on its own. Insertion-time integrity is not the model —
[nmtms.md](nmtms.md) is why, and `set-solver` is what you reach for when an edge has to
be decided → [solving.md](solving.md).

## Negation and mutual exclusion

| in Cyc | here | what changes |
|---|---|---|
| `negationPreds`, unary | `(disjoint P Q)` | native, because collections *are* predicates; closed under `genl` |
| `negationPreds`, binary and up | a pair of implication rules | no declarative form — see below |
| `disjoint` | `disjoint` | same reading, and `(disjoint_metatype M)` makes every member pairwise disjoint without writing the pairs |
| `SiblingDisjointCollectionType` | `sibling_disjoint` | a mark on the collection; its `genl`-specializations are pairwise disjoint unless one genls the other, the clique keyed off the genl closure rather than written |
| `siblingDisjointExceptions` (plural) | `siblingDisjointException` (**singular**, house style) | exempts one pair the sibling mark or a `disjoint_metatype` would force disjoint; read over the whole KB (no scoped variant, unlike Cyc's per-Mt exceptions), pair-local, and it does not leak to subtypes |
| `SymmetricBinaryPredicate` | `(symmetric P)` | |
| `AsymmetricBinaryPredicate` | `(asymmetric P)` | convicts a claim whose **converse** is believed; it does not make `P` irreflexive, and `(P a a)` is admitted |
| `genlInverse` | a forward rule | `(inverse P Q)` exists but is the stronger biconditional |
| `unk` | `unknown` | negation as failure, ground-only, evaluated at level 6 and storing nothing. A conjunctive argument is joined, so its conjuncts may share a quantifier's variable, and `forall` is sugar for the nested case → [naf.md](naf.md) |
| — | `(contradictions kb)` | no Cyc equivalent: the pairs that coexist, ordered by content |
| `assertedMoreSpecifically` | — | no equivalent. Specificity is behavioral: a stated specific claim undercuts an inherited general one, so nothing is derived to arbitrate → [inherit.md](inherit.md) |
| `completeExtentEnumerable` | `(closed_extent_predicate P)` | a **counterpart**, not a translation. Both say a predicate's extent is complete, and three things differ: it is **belief-following** (a defeated or retracted member leaves the extent) rather than a claim about what is stored; it is **context-scoped**, read from the asking context's `genlCx` ancestor set, so one theory may close what a sibling reading the same predicate leaves open; and the extent it closes is what level 6 derives, so a member reachable only by backward chaining is not in it. Closure stays choosable per goal as well, by `unknown` / `thereExists` / `forall` → [naf.md](naf.md) |
| `notAssertible` | — | no equivalent |

Binary mutual exclusion is written as the two rules, and `(not S)` is a stored sentex
with its own handle rather than an absence:

```clojure
(v/assert-rule kb ['(likes ?x ?y)]    '(not (dislikes ?x ?y)) 'CxSomeContext)
(v/assert-rule kb ['(dislikes ?x ?y)] '(not (likes ?x ?y))    'CxSomeContext)
```

`(inverse P Q)` is worth knowing properly, because it is stronger than `genlInverse` in
three ways: it is stored under an unordered key so one declaration installs both
directions, a predicate may declare **several** partners and all are live, and a partner
declared on a sub-predicate answers the super-predicate's goal.

## Well-formedness: lenient by default, assertive on request

Cyc's three modes, and what each maps to:

| mode | in Cyc | here |
|---|---|---|
| strict | constraints must be provable | no equivalent |
| lenient | constraints must not be disjoint | **the default** — a demonstrated conflict is refused, an argument with no place in the hierarchy is excused |
| assertive | that, plus eagerly concluding tighter `isa`s | `checks/*assertive-arg-types?*`, off by default, and additive rather than a replacement |

One naming collision to hold: `vaelii.impl.wff` is narrower than Cyc's "WFF". It is the
**structural** check on the special predicates — `genl` and `genlCx` acyclicity, the
shape of `disjoint`, `arg`, `genlArg` and `inverse` — and throws `:not-well-formed`.
The content constraints above are a separate stage. `check` runs both.

## The contexts you already have names for

| in Cyc | here | what changes |
|---|---|---|
| `LogicalTruthMt` | — | no analogue; the logical truths are the engine's, not a context's |
| `CoreCycLMt` | `CxCore` | the spindle head: the vocabulary code interprets |
| `UniversalVocabularyMt` / `BaseKB` | `CxUniverse` | the mid anchor, and where a decontextualized claim lands |
| `CurrentWorldDataCollectorMt` | `CxWell` | the collector — sees the whole shipped ontology |
| `InferencePSC` | `CxInference` | a **reading**, not a place: what one reader's ancestor set sees whole |
| `EverythingPSC` | `CxEverything` | likewise, and blind to belief — a syntactic read of the store |

Those last two rows are the ones that catch people. Both spell like contexts and neither
is one: **there is no everything-context to assert into**, and asserting into either is
refused, as is any `genlCx` edge naming one. Scope is a property of the read, and these
are names for readings rather than places to stand.

A **variable** context — `?ctx`, the default of every short arity, or any name you
choose — is the joint reading too, so `?ctx` and `CxInference` are one reading with two
spellings, differing only in where the witness lands:

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
holds, and differs only in whose view has to hold it. That is the row Cyc has no equivalent
of, because an `Mt` there is always somewhere to stand.

**Not naming a context does not mean the union.** A conjunctive read will not join a fact
in `CxA` to a fact in `CxB` when no context sees both, because that is an answer no reader
of the KB actually has; the union is `CxEverything`, and you ask for it by name. The
difference is not exotic in the shipped layout: data contexts hang as *siblings* below
`CxWell`, so nothing sees two of them and a join across `CxNaturalWorld` and
`CxSocialWorld` has no reader at all. It is the read-side face of the `(owns Tom Engine1)`
non-derivation in [contexts.md](contexts.md).

One exception, and `unknown` is why. A goal every literal of which is *computed* rather than
matched — `different`, `evaluate`, `unknown` — names no context, so there is no witness to
pick and it is read whole-KB. Fanning over readers is existential over them, and negation as
failure is not monotone, so a fanned `(unknown X)` would be satisfied by the most ignorant
reader in the KB. A *mixed* goal needs no exception: its monotone literals decide which
readers can answer, and the `unknown` is evaluated at those and nowhere else.

`CxNothing` answers to no Cyc name at all. It is the vantage that sees nothing — no fact,
no inherited vocabulary, not one `genl` edge — leaving whatever the provers can compute:
arithmetic, an evaluable, `different`. What it is for is asking what a goal owes to the
KB rather than to the engine.

## The call you would have made

| in Cyc | here |
|---|---|
| `assert` | `(v/assert kb sentence context opts)` → a handle |
| `unassert` | `(v/retract! kb handle)` → `{:removed-sentexes n :removed-justifications n}` |
| `find-assertion-cycl` | `(v/sentexes-matching kb sentence context)` — literal only, and a collection |
| `ask`, backward and bounded | `(v/query kb goal ctx {:max-depth n})` |
| `ask`, unbounded | `(v/prove kb goal ctx)` — DFS, terminating on the data |
| `ask`, boolean | `(v/provable? kb goal ctx)` |
| `ask`, no inference | `(v/ask kb goal ctx)` — the prover registry, and no member expands a rule |
| `fi-ask` | `(v/query kb goal ctx {:max-depth n})` |
| `wff?` | `(v/check kb sentence context opts)` |
| rename | — |

`prove` returns one binding map per **derivation**, so equal maps repeat; `distinct` if
you wanted a set. Which entry point answers what, and what each costs, is
[levels.md](levels.md).

## Truth maintenance

| in Cyc | here |
|---|---|
| TMS assert | `(v/assert kb s ctx {:strength :monotonic})` for known-true, `:default` — the default — for defeasible |
| TMS retract | `(v/retract! kb handle)`, tearing down whatever rested solely on it |
| `why` | `(v/why kb handle opts?)` — the proof tree, cycle-guarded |
| `why-not` | `(v/why-not kb handle)` → `:defeated` / `:superseded` / `:unsupported` / `:not-stored`; the sentence arity adds `:excepted` |
| — | `(v/in? kb handle)`, `(v/believed kb handles)` — a stored sentex is not a believed one |
| — | `(v/settle-stats kb)`, `(v/with-deferred-settle kb & body)` |

Two strength classes and no third: `:monotonic` and `:default`, total-ordered, with a
justification conferring the weaker of its own class and its weakest antecedent.
[nmtms.md](nmtms.md).

## Rules

A rule is a sentex — same structure, same handle, same truth maintenance, additionally
indexed by its antecedent and consequent predicates. So it can be retracted, asked about,
and believed or not.

| in Cyc | here |
|---|---|
| assert a rule | `(v/assert-rule kb [antecedents] consequent context opts)` |
| `forwardRule` | `{:direction :forward}`, or the `set/forwardRule` wrapper |
| `backwardRule` | `{:direction :backward}`, or `set/backwardRule` |
| both, the default | `{:direction :both}` |
| `:code` direction | `{:direction :inert}`, or `set/inertRule` — believed and indexed, fires neither way |
| rule variables | `?x` |
| range restriction | enforced: every consequent variable appears in an antecedent, the one exception being a marked head existential |

Three refusals to expect. A literal whose functor is a **variable** is `:not-indexable`,
in an antecedent or a consequent and whether or not something binds it — the index is
keyed by predicate, so there is nothing to key on. A consequent variable appearing in no
antecedent is `:not-range-restricted`. A cycle through negation is `:not-stratified`, and
it is refused at assert time rather than diagnosed later.

A rule whose consequent is *itself* a rule is not an error — it is a **generator**, and it
fires, stamping out a real indexed rule with concrete functors, justified by the firing
so that retracting the generator un-believes what it stamped. Variables the enclosing
antecedents also mention are holes filled at mint time, and a hole may stand in functor
position. Nesting is not capped. → [generators.md](generators.md)

## What you keep

- Anytime inference on a budget: `ask-within`, `prove-within`, `resume` → [anytime.md](anytime.md)
- Reactive queries: `(v/watch kb goal context f)` → [feed.md](feed.md)
- Abduction: `(v/abduce kb goal context opts)`, hypotheses minted as defeasible premises in a scratch context → [abduction.md](abduction.md)
- `arg` and `interArg` → [argtypes.md](argtypes.md)
- One equality partition behind `rewriteOf` / `sameAs` / `equals` → [equality.md](equality.md)
- Defeasible defaults with exceptions → [exceptions.md](exceptions.md)
- The relation-property marks, enforced rather than recorded: `symmetric`, `asymmetric`,
  `transitive`, `reflexive`, `functional`, `functionalInArg`, `inverse`, `irreflexive`,
  `anti_symmetric`, `anti_transitive`, `equivalence_relation`, `injection`, `surjection`,
  `bijection`, `arity` and `variable_arity` → [taxonomy.md](taxonomy.md). `functionalInArg` is the one with no Cyc
  counterpart to map from: it names the *determined* argument rather than fixing it at 2,
  so a composite determinant — `(namespace, path) → object` — is sayable in one declaration
  → [taxonomy.md](taxonomy.md)
- Polycanonicalization, so a conjunctive consequent becomes one rule per conjunct and a
  disjunctive antecedent one rule per alternative → [canonicalization.md](canonicalization.md)

## What you lose

- Rename
- Natural-language generation
- `notAssertible`, `assertedMoreSpecifically`
- `negationPreds` above arity 1 — the paired rules above are the translation
- Strict well-formedness mode

`transitiveViaArg` is **not** on this list — it is spelled `transitiveInArg` here:
`(transitiveInArg P n R)` and `(transitiveInArgInverse P n R)` carry a claim about argument
`n` across any declared-transitive `R`, with the direction and the argument position
declared separately → [inherit.md](inherit.md).

## What you gain

- `fork` — a private writable overlay over a shared frozen base → [overlay.md](overlay.md)
- An ASP solver behind the `Solver` protocol, `(v/set-solver kb :asp)` → [asp.md](asp.md)
- Six qualitative relation algebras, plus metric time → [qcn.md](qcn.md), [stp.md](stp.md)
- Export and import of a whole KB → [storage.md](storage.md)
- A browser over terms, sentexes and justifications → [web.md](web.md)
- Rule generators → [generators.md](generators.md)
- A query planner that orders a conjunction on cost, and `query-plan` to read what it
  chose → [inference.md](inference.md)
