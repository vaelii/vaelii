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
| `genlMt` | `genlCx` | cached and recomputed on edge change, not derived by a rule; a cycle is refused, unlike `genlMt`'s mutually-visible Mts → [contexts.md](contexts.md) |
| assertion | sentex | a sentence *plus* the context it holds in; the pair is the unit |
| constant | symbol | the role is read off the spelling, and `assert` refuses one that breaks it |
| collection | a type, which is a **unary predicate** | `(dog Muffet)`, never `(isa Muffet Dog)` |
| `genls` | `genl` | |
| `genlPreds` | `genl` | one relation for both, because a type *is* a predicate here |
| `TruthFunction` | `truth_valued_relation` | `core.txt`'s partitions follow Cyc's: `relation` into `function` and `truth_valued_relation`, and that into `predicate` and `logical_constant`, which holds `quantifier` and `logical_connective`. The name is Cyc's, not logic's: a truth function's value is fixed by its arguments' truth values, which holds of the connectives and of no predicate or quantifier |
| `argIsa` | `arg` | positional typing as one ternary declaration: `(argIsa P 1 T)` → `(arg P 1 T)` |
| `arg1Isa` | `arg1` | the binary projection of `arg` at position 1 — bridged to `arg` by rules and sharing its declaration checks, but relating **stored** declarations only; a generalized or inherited reading must be asked of `arg` |
| `arg2Isa` | `arg2` | the projection at position 2, with the same bridging and the same stored-only caveat |
| don't-care variable `??` | a head existential `(exists ?y C)` | syntactic rather than a naming convention, and skolemized to a deterministic NAT on firing → [skolem.md](skolem.md) |
| `wff?` | `check` | returns a vector of problem maps rather than a verdict, so it says *what* is wrong |
| rename | `rename-term!` | restates every premise using the term under the new name and retracts the original, in one `edit!`; `merge-term!` does the same onto a stored term → [api.md](api.md#contract-notes-term-operations). `sameAs` / `rewriteOf` keep both terms and **merge** them onto an elected representative, which is a different act → [equality.md](equality.md) |

The four spellings, because `assert` enforces them (→ [naming.md](naming.md)):
`parentOf` is a predicate, `Fido` an individual, `physical_object` a type, `CxUniverse` a
context. A bare lowercase word like `dog` is both a predicate and a type name, and arity
decides which; a multi-word name commits itself — an underscore to arity 1, an interior
capital to arity 2 and above.

## What a Cyclist's habits do here

**`arg` derives, it does not refuse.** `(arg eats 1 animal)` — the shipped ontology's
own declaration — over `(eats Fern Kibble)` derives `(animal Fern)`, a justified
sentex that retracts like any conclusion, and refuses nothing on what `Fern` is already
known to be. Where `Fern` is a `plant`, which `(separating organism animal plant)`
separates from `animal`, the derived membership and the stated one are a placed clash, as
two stated memberships are. That is the default, behind `argument/*assertive-arg-types?*`
([argtypes.md](argtypes.md)).

A **literal** is still refused: its EDN kind is knowable from the value itself and those
kinds sit in the same `genl` lattice, so `(parentOf 212 Mary)` is refused `:arg-type` —
212 is a `number`, and `number` does not reach `organism`.

Cyc's refusal is the opt-out reading, `VAELII_ASSERTIVE_ARG_TYPES=0`: there the declaration
refuses `(eats Fern Kibble)` with `:type :arg-type` because the hierarchy places `Fern`
somewhere that does not reach `animal`, and a symbol the hierarchy places nowhere the
asserting context can see passes.

**Undeclared is unconstrained — which is not the same as unchecked.** No predicate has to
be declared before use, so `(fghgwgads 212)` stores and a typo is the same bug class as a
predicate nobody has gotten to yet. But as soon as declarations exist they bind: `assert`
refuses on `arg`, `genlArg` and `interArg`, on top of the naming, groundness, structural
and stratification checks it always runs. A tuple that breaks an arity binding, or that
completes a disjointness, asymmetry or functionality clash, is stored, and the settle
places it as a nogood ([nmtms.md](nmtms.md#1-order-independence)). `check` reports the
lot without storing → [api.md](api.md).

**A contradictory pair coexists.** Two `:default` claims that rebut each other both stay
believed and are reported as a represented dilemma by `contradictions`; the engine
arbitrates nothing on its own. Insertion-time integrity is not the model —
[nmtms.md](nmtms.md) is why, and `set-solver` is what you reach for when an edge has to
be decided → [solving.md](solving.md).

## Negation and mutual exclusion

| in Cyc | here | what changes |
|---|---|---|
| `negationPreds`, unary | `(disjoint P Q)` | native, because collections *are* predicates; closed under `genl` |
| `negationPreds`, binary and up | `(negates P Q)` | read down `genl` on both sides; two tuples of one argument list are a placed nogood, and a ground denial is answered from the other side — see below |
| `disjoint` | `disjoint` | same reading, and `(disjoint_metatype M)` makes every member pairwise disjoint without writing the pairs |
| `SiblingDisjointCollectionType` | `sibling_disjoint` | a mark on the collection; its `genl`-specializations are pairwise disjoint unless one genls the other, the clique keyed off the genl closure rather than written |
| `siblingDisjointExceptions` (plural) | `siblingDisjointException` | exempts one pair from the separation marks: the sibling mark, a `disjoint_metatype` and a `partition` or `separating` declaration, not a stated `disjoint`; read at the reader, so a context that does not see it reads the pair separated, and pair-local |
| `SymmetricBinaryPredicate` | `(symmetric P)` | |
| `AsymmetricBinaryPredicate` | `(asymmetric P)` | convicts a claim whose **converse** is believed; it does not make `P` irreflexive, and `(P a a)` is admitted |
| `genlInverse` | `genlInverse` | same reading: binary `genl` with arguments 1 and 2 swapped, read by the matching fan, so a fact, a rule antecedent and a justification all see it; `(inverse P Q)` is the stronger biconditional |
| `unk` | `unknown` | negation as failure, ground-only, evaluated at level 6 and storing nothing. A conjunctive argument is joined, so its conjuncts may share a quantifier's variable, and `forall` is sugar for the nested case → [naf.md](naf.md) |
| — | `(contradictions kb)` | no Cyc equivalent: the pairs that coexist, ordered by content |
| `assertedMoreSpecifically` | — | no equivalent. Specificity is behavioral: a stated specific claim undercuts an inherited general one, so nothing is derived to arbitrate → [inherit.md](inherit.md) |
| `completeExtentEnumerable` | `(closed_extent_predicate P)` | a **counterpart**, not a translation. Both say a predicate's extent is complete, and three things differ: it is **belief-following** (a defeated or retracted member leaves the extent) rather than a claim about what is stored; it is **context-scoped**, read from the asking context's `genlCx` ancestor set, so one theory may close what a sibling reading the same predicate leaves open; and the extent it closes is what level 6 derives, so a member reachable only by backward chaining is not in it. Closure stays choosable per goal as well, by `unknown` / `thereExists` / `forall` → [naf.md](naf.md) |
| `notAssertible` | — | no equivalent |

Mutual exclusion above arity 1 is one declaration:

```clojure
(v/assert kb '(negates likes dislikes) 'CxSomeContext)
```

A believed `(likes Ann Bob)` beside a believed `(dislikes Ann Bob)` is one placed nogood,
and `ask? (not (dislikes Ann Bob))` is true while `(likes Ann Bob)` is believed. No
`(not S)` is stored per fact ([taxonomy.md](taxonomy.md#predicate-metadata)).

`(inverse P Q)` is the inverse that `ask?`, `query` and a transitive walk read; a forward
rule's antecedent does not join it ([inference.md](inference.md#where-the-machinery-stops)).
`(genlInverse P Q)` is the one-directional form, binary `genl` with the arguments
swapped. The matching fan reads it, so a forward rule's antecedent joins it and the
firing's justification names the edge. `(inverse P Q)` holds in both directions: one
declaration is stored under an unordered key and installs both.

## Well-formedness: assertive by default

Cyc's three modes, and what each maps to:

| mode | in Cyc | here |
|---|---|---|
| strict | constraints must be provable | no equivalent |
| lenient | constraints must not be disjoint | what `VAELII_ASSERTIVE_ARG_TYPES=0` leaves: a demonstrated conflict is refused, and an argument with no place in the hierarchy is excused |
| assertive | that, plus eagerly concluding tighter `isa`s | **the default** (`argument/*assertive-arg-types?*`): the argument is concluded a member of the declared type, and a concluded type disjoint from one it holds is a placed clash, not a refusal |

The assertive reading holds for a declaration stated in the asserting context and for one
the context inherits from an ancestor. A concluded membership is stored at each maximal
context that sees both the fact and the declaration, so a declaration stated below the
fact's context concludes the membership in the declaration's context.
[argtypes.md](argtypes.md#where-a-mint-is-placed) states the rule.

One naming collision to hold: `vaelii.impl.wff` is narrower than Cyc's "WFF". It is the
**structural** check on the special predicates — `genl` and `genlCx` acyclicity, the
shape of `disjoint`, `arg`, `genlArg` and `inverse` — and throws `:not-well-formed`.
The content constraints above are a separate stage. `check` runs both.

## The contexts you already have names for

| in Cyc | here | what changes |
|---|---|---|
| `LogicalTruthMt` | — | no analogue; the logical truths are the engine's, not a context's |
| `CoreCycLMt` / `UniversalVocabularyMt` / `BaseKB` | `CxUniverse` | the root: the vocabulary code interprets, the upper ontology, and where a decontextualized claim lands |
| `CurrentWorldDataCollectorMt` | `CxWell` | sees every shipped context but the opt-in theories, the `kb/middle/` files that state no `genlCx` edge from CxWell ([contexts.md](contexts.md)) |
| `InferencePSC` | `CxInference` | a **reading**, not a place: what one reader's ancestor set sees whole |
| `EverythingPSC` | `CxEverything` | likewise, and blind to belief — a syntactic read of the store |

Those last two rows are the ones that catch people. Both spell like contexts and neither
is one: **there is no everything-context to assert into**, and asserting into either is
refused, as is any `genlCx` edge naming one. Scope is a property of the read, and these
are names for readings rather than places to stand.

A **variable** context (`?ctx`, the default of every short arity, or any name you choose)
is the same reading as `CxInference`, with the witness unified into the variable. The
table of the five readings, and why `CxEverything` alone ignores belief, is in
[contexts.md](contexts.md#the-query-contexts-reading-modes-wearing-a-contexts-spelling).
An `Mt` in Cyc is always somewhere to stand, so Cyc has no equivalent of these readings.

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
| rename | `(v/rename-term! kb old new)` |

`prove` returns one binding map per **derivation**, so equal maps repeat; `distinct` if
you wanted a set. Which entry point answers what, and what each costs, is
[levels.md](levels.md).

## Truth maintenance

| in Cyc | here |
|---|---|
| TMS assert | `(v/assert kb s ctx {:strength :monotonic})` for known-true, `:default` — the default — for defeasible |
| TMS retract | `(v/retract! kb handle)`, tearing down whatever rested solely on it |
| `why` | `(v/why kb handle)` — the justification graph down to premises, each handle once |
| `why-not` | `(v/why-not kb handle)` → `:defeated` / `:withdrawn` / `:superseded` / `:unsupported` / `:not-stored`; the sentence arity adds `:excepted` |
| — | `(v/believed? kb handle)`, `(v/believed kb handles)` — a stored sentex is not a believed one |
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
| `forwardRule` | `set/forwardRule` / `{:direction :forward}` — here that forward-chains **and** answers backward goals (Cyc's forward-only is `set/forwardOnlyRule`) |
| `backwardRule` — the default | bare `(implies …)`, or `set/backwardRule` / `{:direction :backward}` |
| `backchainRequired` | `set/lazyForwardRule` / `{:direction :lazy-forward}` — a backward rule whose conclusion a forward rule's antecedent proves in its join, storing nothing ([inference.md](inference.md#a-lazy-forward-rule)) |
| `:code` direction | `{:direction :inert}`, or `set/inertRule` — believed and indexed, fires neither way |
| rule variables | `?x` |
| range restriction | enforced: every consequent variable appears in an antecedent, the one exception being a marked head existential |

Three refusals to expect. A rule antecedent whose functor is a **variable** is
`:not-indexable`, whether or not something binds it — the antecedent index is keyed by
predicate, so there is nothing to key on. A variable functor in the consequent is legal
and filed under a catch-all key every backward goal reads. A consequent variable appearing in no
antecedent is `:not-range-restricted`. A cycle through negation is `:not-stratified`, and
it is refused at assert time rather than diagnosed later.

A rule whose consequent is *itself* a rule is not an error — it is a **generator**, and it
fires, generating a real indexed rule with concrete functors, justified by the firing
so that retracting the generator un-believes what it generated. Variables the enclosing
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
  `transitive`, `reflexive`, `functional`, `functionalInArg`, `inverse`, `negates`,
  `irreflexive`, `anti_symmetric`, `anti_transitive`, `equivalence_relation`, `injective_predicate`, `surjective_predicate`,
  `bijective_predicate`, `arity` and `variable_arity` → [taxonomy.md](taxonomy.md). `functionalInArg` is the one with no Cyc
  counterpart to map from: it names the *determined* argument rather than fixing it at 2,
  so a composite determinant — `(namespace, path) → object` — is sayable in one declaration
  → [taxonomy.md](taxonomy.md)
- Polycanonicalization, so a conjunctive consequent becomes one rule per conjunct and a
  disjunctive antecedent one rule per alternative → [canonicalization.md](canonicalization.md)

## What you lose

- Natural-language generation
- `notAssertible`, `assertedMoreSpecifically`
- Strict well-formedness mode

`transitiveViaArg` is **not** on this list — it is spelled `transitiveInArg` here, in the
same direction: `(transitiveInArg P n R)` carries a claim about argument `n` along `R`'s
arrow, a stored `(P … X …)` and `(R X Y)` giving `(P … Y …)`, exactly as Cyc's
`(transitiveViaArg P R n)` does. `transitiveViaArgInverse` is `transitiveInArgInverse`,
against the arrow. The argument order differs: vaelii writes `(P n R)` where Cyc writes
`(P R n)`. `R` is any declared-transitive relation → [inherit.md](inherit.md).

## What you gain

- `fork` — a private writable overlay over a shared frozen base → [overlay.md](overlay.md)
- An ASP solver behind the `Solver` protocol, `(v/set-solver kb :asp)` → [asp.md](asp.md)
- Six qualitative relation algebras, plus metric time → [qcn.md](qcn.md), [stp.md](stp.md)
- Export and import of a whole KB → [storage.md](storage.md)
- A browser over terms, sentexes and justifications → [web.md](web.md)
- Rule generators → [generators.md](generators.md)
- A query planner that orders a conjunction on cost, and `query-plan` to read what it
  chose → [inference.md](inference.md)
