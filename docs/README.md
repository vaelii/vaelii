# Vaelii docs

One file per subsystem, read alongside the code. This page is the map, and between them
these files document the whole engine. A subsystem is described in exactly one place; the
model the pages assume is the [README](../README.md), and the vocabulary is
[glossary.md](glossary.md).

Sentexes live in a **record store**, keyed by integer handle, and are found through an
**index store** — derived from the records and rebuildable from them — that holds six
indexes over the same sentexes: a positional **trie**, secondary **roots** (context /
functor / argument), a **rule index**, an **exception re-check index**, an inverted **term
index**, and the **term roster** beside it.

What ships is schema: `vaelii.impl.starter` loads the upper and middle contexts from
`resources/kb/`, and nothing contingent — no cast, no facts of a story — comes with it.
Two worked KBs below that schema exercise all this (no doc of their own), and they are
test-world data under `test/vaelii/`: `vaelii.world-fables` (children's stories as
contexts, each moral *derived* by a rule rather than stored as a string) and
`vaelii.world-narrative` (a story-understanding ontology layered over the fables —
causal / temporal / goal reasoning via predicate metadata and a goal-achievement rule).

## Start from what you are trying to do

| I want to… | Start at | Then |
|---|---|---|
| load a KB and look at it | [kbs.md](kbs.md) | [web.md](web.md), [catalog.md](catalog.md) |
| assert facts and query them from Clojure | [api.md](api.md) | [naming.md](naming.md), [levels.md](levels.md) |
| find out why my query answers nothing | [troubleshooting.md](troubleshooting.md) | [contexts.md](contexts.md) |
| make a rule fire, and see what it concluded | [inference.md](inference.md) | [levels.md](levels.md), [contexts.md](contexts.md) |
| say "usually, but not when…" | [exceptions.md](exceptions.md) | [nmtms.md](nmtms.md), [inherit.md](inherit.md) |
| understand why the KB believes something | [nmtms.md](nmtms.md) | [preview.md](preview.md), [feed.md](feed.md) |
| resolve a contradiction | [nmtms.md](nmtms.md) | [solving.md](solving.md), [asp.md](asp.md), [labeling.md](labeling.md) |
| keep a KB across restarts | [storage.md](storage.md) | [overlay.md](overlay.md) |
| know what a word in these docs means | [glossary.md](glossary.md) | |
| build a type hierarchy that behaves | [taxonomy.md](taxonomy.md) | [argtypes.md](argtypes.md), [inherit.md](inherit.md) |
| reason about time, space or distance | [qcn.md](qcn.md) | [time.md](time.md), [space.md](space.md), [stp.md](stp.md) |
| drive a KB from a shell or over a network | [operations.md](operations.md) | [api.md](api.md) |
| judge whether a KB's knowledge is any good | [quality.md](quality.md) | [taxonomy.md](taxonomy.md), [inference.md](inference.md) |
| read another system's KB in | [foreign.md](foreign.md) | [kbs.md](kbs.md) |
| turn English into sentexes | [reading.md](reading.md) | [llm.md](llm.md) |
| find the code behind a subsystem | [namespaces.md](namespaces.md) | [dependencies.md](dependencies.md) |
| understand what a query costs | [indexing.md](indexing.md) | [density.md](density.md), [anytime.md](anytime.md) |
| find out what shape of question my KB is asked | [profile.md](profile.md) | [indexing.md](indexing.md) |
| know what a change cost the index, per assert | [profile.md](profile.md) | [indexing.md](indexing.md) |
| see what this KB is *for* | [commonsense.md](commonsense.md) | |

Every page opens with three bullets — **Covers**, **Not here**, **Assumes** — so a wrong
page costs a sentence rather than a section.

## Start here

- [cyc-rosetta-stone.md](cyc-rosetta-stone.md) — the vocabulary mapping from OpenCyc/ResearchCyc to Vaelii: where the names match, where the semantics diverge, and what Cyc has that Vaelii does not (and vice versa).
- [kbs.md](kbs.md) — the four knowledge bases you can load and the route to each: what ships here, what the plugin ships, what you supply, and where a KB has to sit to be found.
- [api.md](api.md) — the public API: every fn on `vaelii.core`, with what it takes and returns, and the five thin entry-point namespaces beside it.
- [troubleshooting.md](troubleshooting.md) — indexed by symptom rather than subsystem: an empty query, a rule that will not fire, a refused `assert`, a KB holding facts nobody asserted.
- [glossary.md](glossary.md) — every term used across these docs and the code, tagged by subsystem.
- [commonsense.md](commonsense.md) — the questions this KB is asked, one per reasoning subsystem, what the schema had to grow to answer them, and the outside judge that reads the answers back.

## Core model & storage

- [namespaces.md](namespaces.md) — the file map: what lives in each namespace under `src/`.
- [canonicalization.md](canonicalization.md) — the canonical form: how sentences and rules identical up to variable names, literal order, symmetric arguments or comparison direction dedup to one handle.
- [naming.md](naming.md) — the KB naming invariants (predicates, individuals, types, contexts).
- [storage.md](storage.md) — record + index stores, the protocols, nippy serialization, the single-writer contract.
- [indexing.md](indexing.md) — the count-aware trie, the secondary roots and retrieval from them, the rule index, the inverted term index.
- [density.md](density.md) — the dense backends behind those protocols: tiered int postings, the columnar int-token trie, int-keyed roots, and the record-side codec — what each is measured to buy, and what the measurements refuted.
- [overlay.md](overlay.md) — forks: a private writable overlay over a shared read-only base, so any number of forks in one JVM share one frozen KB while each keeps its own divergent copy.
- [contexts.md](contexts.md) — contexts, the `genlCx` spindle (head / mantle / collector), `ist` reification, justification placement.
- [taxonomy.md](taxonomy.md) — the `genl` type hierarchy, `isa?`, `disjoint` / `disjointMetatype`.
- [inherit.md](inherit.md) — argument-position preservation: `(argPreserving P n R)` / `(argPreservingInverse P n R)`, whether a claim about two kinds reaches their subkinds, the specificity that lets a stated claim undercut an inherited default, the `(asymmetric P)` that lets a strict one conflict instead, and how a forward rule fires on an inherited claim by naming what the claim was read from.
- [argtypes.md](argtypes.md) — `argIsa` / `argGenl` read as **entailments** as well as constraints: the type an argument declaration says a term has, minted as a derived justified sentex, both arrival directions, and why only a locally-written declaration entails. Off by default.

## Inference & belief

- [inference.md](inference.md) — rules as sentexes, rule direction, forward/backward chaining, predicate subsumption, incremental matching, the prover engine.
- [generators.md](generators.md) — a rule whose consequent is a rule: the hole/own-variable split that needs no declaring, what a firing stamps out, why a mint retracts like any conclusion, and the one level of nesting.
- [anytime.md](anytime.md) — resource-bounded / anytime inference: the budget, the resumable partial-result contract, the qualitative `cost` tier.
- [levels.md](levels.md) — the lookup-to-query stack: eight named levels from a raw index read to full backchaining.
- [abduction.md](abduction.md) — `abduce`: what would have to be true for a goal to be provable, minted as a defeasible hypothesis in a scratch context — the dead-end observer, the grant that gates it, and the isolation that makes an ignored call free.
- [exceptions.md](exceptions.md) — `exceptWhen`: how a rule states its own exception, and why the exception is never stored.
- [naf.md](naf.md) — negation as failure: `unknown` / `thereExists`, evaluated at level 6, storing nothing (and why the JTMS `out` slot stays reserved).
- [aggregate.md](aggregate.md) — aggregation as a query operator: the five reductions over a query's solutions, where GROUP BY comes from, and how a firing that rests on a count is maintained.
- [nmtms.md](nmtms.md) — the non-monotonic TMS: assumption strengths, soft prioritized contradictions, the solver seam.
- [preview.md](preview.md) — `preview`: the belief a batch would add and take away, read off and then rolled back at the same handles.
- [equality.md](equality.md) — `rewriteOf` / `sameAs` / `equals` over one belief-following partition, and the `different` that keeps the unique-name assumption.
- [equational.md](equational.md) — symbolic (schematic) equational reasoning: oriented term rewriting by a Knuth-Bendix order, normalizing store and query to one belief-following normal form.
- [nat.md](nat.md) — non-atomic terms: reifiable functions reified to opaque constants before the index, unreifiable applications kept structural.
- [quantity.md](quantity.md) — the measure-evaluating quantity prover: measure comparison over a `dimensionOf` / `conversionFactor` table, with an epsilon float policy.
- [skolem.md](skolem.md) — head existentials `(exists ?y C)` skolemized to deterministic NAT constants on forward firing, and the occurs-check in `unify`.

## Qualitative reasoning

- [qcn.md](qcn.md) — the generic qualitative-constraint-network engine behind all six relation algebras: an algebra as a parameter, a network as a value, arc-queue path consistency, entailment *and* refutation, the support a derived relation carries, and the prover shape every calculus over it shares.
- [space.md](space.md) — the four spatial algebras over it: RCC-8 topology, cardinal direction, relative direction (whose frame of reference is the context) and qualitative distance (whose composition is the triangle inequality over the class bounds).
- [time.md](time.md) — the two temporal algebras over it: Allen's thirteen interval relations, with the composition table written twice so a transcription error is a test failure, and the three-relation point algebra over instants.
- [duration.md](duration.md) — the quantitative half of interval reasoning: `totalDuration` / `overlapDuration` computed over stored lengths and the unit table, on `[lo hi]` bounds so an over-approximation renders as an interval and says so.
- [stp.md](stp.md) — metric time over the same instants: bounds on the gap between two timepoints, closed by all-pairs shortest paths, with `startOf` / `endOf` bridging the numbers back onto Allen's intervals and sharpening an overlap into a figure.
- [scenario.md](scenario.md) — scenario extraction over any constraint network: one consistent base relation per pair, by fewest-possibilities-first backtracking — lazy, because the count is exponential, and deterministic, because every tie breaks on content.

## Contradiction solving (ASP)

- [asp.md](asp.md) — the ASP backend behind the solver seam: the ASPIF encoding, clingo/clasp, determinism.
- [solving.md](solving.md) — `assumptionRules` and persistent, inert labeling contexts.
- [labeling.md](labeling.md) — `do/` imperatives and brave/cautious solve.

## Interface

- [feed.md](feed.md) — `watch`: an application told that belief moved instead of asking again, off the settle that already computed it — one settle one event, standing queries as a filter over the moved region rather than a re-run, and what is refused because the region cannot answer it.
- [operations.md](operations.md) — the operational surface: the `cli` driver, the headless EDN-over-HTTP daemon that is the single writer, and the zero-dep client threading an explicit connection.
- [quality.md](quality.md) — `kb-quality`: four readings about the knowledge rather than the engine — which rules never fire, how skewed the predicate extents are, how deep the rule graph's chains reach, how much of the taxonomy reaches a root — each off state that already exists, and none of them a gate.
- [profile.md](profile.md) — the workload instrument: which shapes of question a KB is asked, which index families answer them, what a trie walk costs in node probes, and what one assert or one retraction costs each family — off by default and a deref when off. Also the count-based gate built on it, which fails the suite when a change adds an index operation to either write path, the class `lein perf`'s ratios cannot see.
- [web.md](web.md) — the reitit-ring browser for terms, sentexes, and justifications;
  a term page opens with its shape drawn, server-side and inside a read budget.
- [catalog.md](catalog.md) — the KB catalog: what a process can load (shipped, generated, corpus, dump, on-disk store), loading one in the background with progress and cancellation, and switching which one every page reads.
- [llm.md](llm.md) — the pluggable LLM that reads a KB through generated tools and *proposes* an edit batch, graded by the engine's own well-formedness checks.
- [reading.md](reading.md) — English in: a candidate generator with a reviewer between it and the store, resolving the document's own words against the KB's vocabulary before anything is asked, carrying the span each candidate came from, reporting what it could not translate — and scored against the hand-written fables.
- [foreign.md](foreign.md) — the formats we read and do not write: no reader ships here, and a bridge is a plugin that declares itself in one edn resource on the classpath.

## Generated

- [dependencies.md](dependencies.md) — which `project.clj` dependencies `lein antq` last reported as outdated, written by `scripts/update-badges.sh --deps`.
