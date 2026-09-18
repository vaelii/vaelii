# Contributing to Vaelii

This file is for human contributors.

Section numbers here are referenced from [`legal/ICLA.md`](legal/ICLA.md),
[`legal/CCLA.md`](legal/CCLA.md) and the pull-request template, so §7 and §9 keep
their numbering across revisions.

## 1. Local setup

Read [`README.md`](README.md) first, through Quick start; that gets you a REPL with
a few sample assertions. There are **no external services** — the default backend is
in-memory, and the durable one is a directory.

```bash
lein deps
lein repl          # a REPL with vaelii.core loaded
lein test          # the suite (see §5 — it owns two space numbers, so one run at a time)
lein browser       # the one to work in: a REPL with the browser running in it, on :3000
```

`lein browser` is `lein repl` with the browser already started *and a reload channel
into it* (§6). `lein run -m vaelii.browser.web` serves the same pages with no way in, so
prefer `lein browser` while you are editing.

### 1.1 Static analysis (`lein lint`) setup

Building, running and testing Vaelii needs only a JDK and Leiningen. `lein lint` is a
separate gate that shells out to four more binaries, none of which Leiningen
installs:

- [`clj-kondo`](https://github.com/clj-kondo/clj-kondo) — `brew install
  borkdude/brew/clj-kondo` (macOS), or the [install
  script](https://github.com/clj-kondo/clj-kondo/blob/master/doc/install.md)
- [`shellcheck`](https://www.shellcheck.net/) — `brew install shellcheck` (macOS), or
  your distro's package
- [`ruff`](https://docs.astral.sh/ruff/) — `brew install ruff` (macOS), or `pipx
  install ruff`. The only optional one: the `tools` check skips with a note when ruff
  is absent, because no CI image this repo uses carries it
- `python3` — usually already present

```bash
lein lint    # glossary, versions, doc links, doc drift, conflict markers, clj-kondo,
             # cljfmt, shellcheck, reflect (a compile pass), unused (a public var nothing
             # calls), prose, tools (ruff over the Python under tools/)
lein fix     # reformats in place; cljfmt is the only auto-repairable check
lein gate    # lint, then the suite — the check before you push
lein release-gate  # ...and the perf claims, before a tag or a perf-sensitive land
```

**`lein gate` is the one to run before opening a pull request.** It runs two stages
that answer two different questions — well-formed, right — and it is
deliberately **not** fail-fast, because the suite takes minutes and learning about both
failures once beats learning about them one cycle at a time. Each stage streams
to its own log under `target/gate/run-<pid>/`, which `target/gate/latest` points at — a
run owns its directory, because two gates share a working tree here and neither may read
the other's verdict. A failing stage prints its tail inline.
**Perf is opt-in**: `lein release-gate` adds the scaling claims before a tag or a
perf-sensitive land, `--perf` adds them without the release framing, and a fast gate
that lands a hot-path change without them prints "perf owed".
`--fail-fast`, `--only <stage>`, `--skip <stage>`, `--quick`, `--all`, and
`PERF_TOLERANCE` on a loaded machine.

You do not need the lint binaries to build, run or test; only to run the gate locally.

**Two of those checks are ratchets: each stops the build rather than printing at you.**
A **reflection or auto-boxing warning fails the build** — `reflect` compiles `src` and
`bench`, and the gate's test stage reads its own log for the tree that pass does not
compile, so both halves are covered. The fix is always a type hint at the call site;
the allow-list is for a third-party release that still reflects, and turning
`*warn-on-reflection*` off to get past it is the one response that is not available.
And **a public var nothing references fails** `unused`, against
`scripts/unused-publics-baseline.txt`. If it really has no caller, delete it. If its
caller is one clj-kondo cannot see — `requiring-resolve`, a quoted-symbol registry, a
REPL affordance — add it to the baseline with that reason, in its own commit: every
line there is a claim somebody should be able to check later, which is why a baseline
refresh never rides along with the change that needed it.

**CI runs the same checks, through the same scripts.** A pull request gets two
workflows, and neither is anything you cannot run yourself: `lint` is `lein lint`, and
`test` is the suite at `:default` on the two ends of the durability axis — everything
in RAM, and everything on disk. Both run with a read-only token and read no secret, so
a pull request from a fork runs them in full.

What the pull-request path leaves out, the `deep` workflow picks up: the `^:slow`
tests, which carry more than half the suite's assertions; the `^:multi-jvm` and `^:fuzz`
ones, which neither `:default` nor `:all` selects; the five record×index pairs
the two-backend gate skips, plus `overlay` (the fork decorator, not a seventh pair); and
the five **sweeps** — the whole suite re-run through the persistent-map JTMS, the
incremental matcher, the node query engine, one of its tacticians, and the reference
retrieval fan-out. Each of those replaces something the engine
otherwise picks for itself, and each must be failing-set-identical with the default it
replaces, since every one is a cost decision rather than a semantic one.

It blocks nothing and nobody waits on it, which is why a change touching storage, the
index, records or recovery still owes those runs locally — a bug that shows up only under
`disk-columnar` should reach you in the pull request, not the next morning. A change
touching inference, matching or retrieval owes the sweep for the same reason: the
retrieval paths disagreeing is exactly the kind of thing only that run can see.
`./scripts/test-matrix.sh` (`lein test-matrix`) is how to pay both at once — the eight
backends and the five sweeps concurrently, one JVM each, ~13 minutes rather than the ~55
the two single-axis scripts take in sequence.

## 2. Project layout, and the one rule that matters

```
src/vaelii/            the six public namespaces: core.clj (the whole API) plus five thin entry points (§2.1)
src/vaelii/impl/       the engine internals and the ontology content
src/vaelii/host/       the tooling above the API: the daemon, the CLI, the loaders, the LLM stack
src/vaelii/browser/    the KB browser, an app on the public API (koinii/ is the other app)
test/vaelii/           the suite, plus the test-world fixtures (world*.clj)
bench/                 the load/scale harnesses (:bench profile, its own source path)
resources/kb/          the starter ontology as term-centric text, read by vaelii.host.seed
resources/public/      browser assets, served verbatim (licences in licenses/THIRD-PARTY.md)
docs/                  one note per subsystem; docs/README.md is the map
```

Layout is the Leiningen default — `src/` + `test/` + `resources/` — not the Maven
`src/main/clojure` tree, so `project.clj` overrides no paths. Keeping tests off the
source path is what stops `:uberjar {:aot :all}` from compiling and shipping them.

### 2.1 The public surface is six namespaces

**`vaelii.core` is the engine's whole API**, and five thin entry points are public
beside it: `vaelii.client`, `vaelii.starter`, `vaelii.web`, `vaelii.serve` and
`vaelii.cli`. Everything else lives under `vaelii.impl.*`, `vaelii.host.*` or one of the
two apps (`vaelii.koinii.*`, `vaelii.browser.*`) and is free to change without notice. Tests reach
into `impl` freely, which is what unit tests are for; nothing outside this repo should.

The five exist so that the entry points a first-time reader is pointed at are ones the
boundary covers: a page cannot send somebody to `vaelii.host.client` and call `impl`
free to change on the same breath. A shim is cheap; a boundary nobody keeps is not a
boundary.

This is not a convention, it is the compatibility boundary: it is what lets the
internals move at the pace they move at. `test/vaelii/public_api_test.clj` pins it
from the outside, deliberately requiring nothing under `vaelii.impl.*` except the test
scaffolding. The API itself is [`docs/api.md`](docs/api.md); what lives in which
namespace is [`docs/namespaces.md`](docs/namespaces.md).

`vaelii.koinii.*` is the one thing in the tree that is neither of the two: an
**application** built on those six ([`docs/koinii.md`](docs/koinii.md)), so it lives at
`src/vaelii/koinii/` rather than under `impl/` and requires nothing from there — the same
test pins that. It is not a seventh public namespace: the engine's rosters (the API
golden, the SPI interfaces, the refusal types) exclude it, because freezing an app's surface
there would put its development inside the engine's compatibility contract. What koinii
needs and the API lacks gets published in `vaelii.core`, never reached around.

### 2.2 Four properties that hold everywhere

Breaking one of these is a bug however well it tests. They are the reason several
tests look more paranoid than a unit test needs to be.

- **Order independence.** The same knowledge, given in any order, yields the same
  beliefs. Belief is computed from current state, never accumulated, and every
  tie-break keys on **content**, never on a handle — handles are allocated in
  assertion order, so a tie-break on one is an order dependence in disguise.
  `order_independence_test.clj` enumerates every permutation of a scenario and demands
  one answer. [`docs/nmtms.md`](docs/nmtms.md)
- **Locality.** No operation recomputes the whole graph; a relabel is scoped to the
  affected region with the rest held fixed.
- **Context scoping.** A read sees what its context sees, up the `genlCx` ancestor set —
  facts, rules, taxonomy edges and the definitional checks alike.
  [`docs/contexts.md`](docs/contexts.md)
- **Belief filtering.** A stored sentex is not a believed one. Matching, the taxonomy
  closures and the cached relations all follow belief.
  [`docs/taxonomy.md`](docs/taxonomy.md)

## 3. Coding conventions

Project-specific; general Clojure idiom otherwise.

### 3.1 Naming invariants

The KB reads a symbol's **role off its spelling**, so these are not style — `assert`
refuses a sentence that breaks one. Full reference, with the regexes and the exact
rejection messages: [`docs/naming.md`](docs/naming.md).

| Role | Convention | Example |
|------|-----------|---------|
| predicate | camelCase, lowercase-initial | `parentOf`, `genl`, `arg` |
| individual | CapitalCamelCase | `Muffet`, `Tom` |
| type | snake_case, a **unary** predicate | `dog`, `physical_object` |
| context | `Cx` followed by CapitalCamelCase | `CxCore`, `CxUniverse` |

What follows from it:

- **Types are unary predicates.** Write `(dog Muffet)`, not `(isa Muffet Dog)`. `thing` is
  the root of the `genl` hierarchy.
- **snake_case implies arity 1.** An underscored functor names a type, and a type is a
  one-place predicate, so `(lives_in ?x cold_place)` is refused — write `livesIn`. A
  bare lowercase word (`dog`, `likes`) is both a predicate and a type name; arity
  decides and nothing is refused.
- **Every literal is checked**, not just the outermost one: a rule's consequent and an
  `exceptWhen` query are held to the same invariants as a fact.
- **A non-ground fact is refused.** `(mortal ?x)` asserts nothing — write a universal
  as a rule, where variables belong.

Every `ex-info` that `assert` throws carries a `:type` (`:naming`, `:not-well-formed`,
`:not-ground`, `:not-range-restricted`, `:arg-type`, `:disjoint`, `:functional`), so
discriminate on that rather than guessing from which keys are present. No check uses
`clojure.core/assert`: it is elidable, and an elided check stores the junk it existed
to refuse.

### 3.2 `!` means irreversible, not "has effects"

Naming a new fn, add `!` only when it destroys or removes stored knowledge. Adding one
to a fn that merely mutates — `assert`, `index-sentex`, `mark-premise`, `relabel`,
`settle`, `forward-chain`, `recover` — is the mistake to avoid, because it dilutes the
signal. The roster is in [`docs/api.md`](docs/api.md).

### 3.3 File ordering, not `declare`

Define functions before they are referenced. Use `declare` only for a genuine
in-file call cycle, and **add a comment explaining the cycle**. Prefer reordering.

### 3.4 Canonicalize sentences

`LazySeq`, `PersistentList` and vector are `=` but freeze to *different* nippy bytes.
`substitute` yields lazy seqs, so the `sentex` constructor normalizes to
`PersistentList` and interns every symbol, so a repeated predicate or type name is one
shared object across all 100M+ facts. **Anything building a sentence for a key or a
value must go through `sentex/sentex`.**

### 3.5 Namespace aliases

The only blessed `:refer :all` is `[clojure.test :refer :all]` in test namespaces;
everywhere else use an explicit `:refer [foo bar]` of exactly the names the file uses.
Foundational vocabulary uses short `:as` aliases by convention — `sx` for
`impl.sentex`, `p` for `impl.protocols`, `cap` for `impl.capabilities`, `v` for
`vaelii.core`, `tax` for `impl.taxonomy`, `nm` for `impl.naming`, `tu` for
`vaelii.test-util`. Follow what the
file you are editing already does.

### 3.6 Comments: current code only, no archaeology

Comments and docs describe what the code does **now**, never what it used to do. Do
not write "was …", "previously", "changed from", "removed the old …", or a superseded
approach's rationale, and do not narrate a migration — the diff already records that,
and in the source it is pure distraction. Where the history carries a real warning,
keep it as a claim about the present: "do not add a third defeat class", not "there
used to be one".

**And nothing about what is coming.** No roadmap, no planned work, no "the next step",
no `## TODO` section. `docs/` documents the engine as it is, and what gets built next is
not something to commit a reader to.

The distinction worth getting right: **an absence is a fact and should be documented.**
"There is no beta network", "a justification has no out-list", a `## What is not built`
section — write all of those, because a reader needs to know where the engine stops.
What does not belong is the promise attached to one. "The rule index is keyed by
predicate, not by antecedent shape" documents the engine; "keying it by shape is the
remaining win" schedules it.

`lein lint` fails on the unambiguous phrasings in both directions, and warns on the
`used to` family.

Otherwise, default to no comment. Add one when the *why* is non-obvious: a hidden
constraint, a subtle invariant, a workaround for a specific bug. Do not explain *what*
the code does — well-named identifiers do that — and do not reference the current task
("added for X flow"); that belongs in the pull-request description.

### 3.7 Vocabulary: our words for our things

Where this engine already has a word, use it rather than the word another system uses
for the same idea. A sentex holds in a **context**, never a *microtheory*; a non-atomic
term is a **NAT**, **reified** or **structural**, never a *NART* or a *NAUT*. Those are
Cyc's coinages, and prose that reaches for them gives the impression that they were ours — which
misleads a reader who then goes looking for them, and, for a term that appears nowhere
in the general knowledge-representation literature, implies a provenance nobody claimed.

Quoting the other system is a different thing and is welcome where it earns its place:
`genlMt`, `BaseKB` and `UniversalVocabularyMt` are identifiers *in* OpenCyc, not words
for anything here, and the OpenCyc reader plugin talks about Cyc's own microtheory slot
because that is the field it reads. The test is whether the word names something of
theirs or something of ours.

`lein lint` fails on the borrowed words. This section is exempt by name, since it has
to spell them to ban them.

### 3.8 What counts as breaking

A change is classified by who can observe it, and the release number follows the
classification. Four classes, and every entry's `*Class:*` line spells one of them —
**Breaking**, **Refusal**, **Additive**, **Fix**:

1. **A contract change a working caller can observe** — a return shape, a `:type`
   keyword, a status code, a documented default. That is **Breaking**: the changelog
   entry carries the label, and the release that ships it bumps the minor version
   (the 0.x digit, pre-1.0). "Working" is the operative word: the caller's code does
   what its author believes, and stops doing it on upgrade.
2. **A new refusal of input whose acceptance corrupts state, stores junk no query
   can match, or silently does nothing.** No working caller exists to break — the
   input never did what whoever sent it believed — so the entry is labeled
   **Refusal** and is patch-eligible; when several accumulate they batch into one
   designated minor rather than each forcing a release. A Refusal entry argues its
   own premise: it says what accepting the input does to the store, because that
   claim is the whole justification for the lighter treatment.
3. **Additive** — a `:type` where none was, a new option key, a new op in the
   daemon's allowlist. Neither label; any release may carry it.
4. **Fix** — the engine does what it already says it does, at an entry point where the two
   disagree: a doc, a docstring, a refusal message or an invariant states one thing
   and the code answers another, and the code moves to the statement. The contract
   holds still, so a caller written against what the engine documents is the caller
   this corrects the answer *for*. **Fix** is patch-eligible and rides any release.
   It owes no `*Breaks:*` line — nothing is retired, so there is no name a sibling
   could be grepped for — and a `*Migration:*` line is optional, reading "none"
   where an entry carries one. A change a working caller can observe *and* is
   entitled to is class 1 however plainly it is a bug: the counterweight below is
   what decides, not the word "fix".

**A configuration name is part of that surface.** Renaming or removing a `VAELII_*`
environment variable or a `vaelii.*` system property is class 1 — a systemd unit or a
deployment script that set it keeps setting it and stops being obeyed — so it takes the
**Breaking** label and a migration line naming the new spelling, plus a regenerated
`test/golden/config-surface.edn` and its row in `docs/operations.md` in the same commit.
Adding one is Additive and owes the same golden and the same row.

**The published API and the extension points are pinned the same way.** Every public var
of the six public namespaces is frozen with its arglists in
`test/golden/api-surface.edn`, and the protocols a doc invites an out-of-tree
implementation of — the storage contracts, `KvBackend`, `Solver`, `Prover`, `Provider` —
in `test/golden/spi-protocols.edn`. Removing a var, or changing an arglist, is class 1
and takes the label with a migration line. Adding one is Additive. **Both move the
golden**, which is the point: a golden that only moved on a break would be regenerated
by whoever hit the break, and the additions — the way a surface actually grows — would
never be read by anyone. `lein regen-goldens` rewrites all three, and the diff belongs
in the same commit as the change that caused it, where a reviewer sees the two together.

Adding a **method to an existing interface** is class 1 rather than Additive, and it is the
case people misfile: an implementer that satisfied the protocol yesterday satisfies it
in part today, and finds out at the call site. Prefer a new protocol advertised beside
the old one.

**The shipped ontology's content is not part of that surface, and the line runs between
the code and the data.** `resources/kb/` is data the engine ships, and a caller takes the
ontology their engine version carries — there is no separate thing to pin, no way to hold
one version of the terms against another of the engine. So an edit to a term, a
declaration or a comment there takes **no** Breaking label however far it moves an
answer, and rides any release. What it owes instead is the roster or golden test that
pins the shipped set, so the change is visible rather than quiet, and a changelog entry
that says what moved.

The engine *code* that reads the ontology is surface as usual, and the distinction is
sharp enough to apply without argument: changing what `decontextualized_predicate` **means**
is class 1, and changing **which terms carry it** is not. The first is a contract every
KB is written against; the second is one KB's content.

The split has citable precedent rather than being this repo's invention:

- **SemVer** defines a patch as "an internal change that fixes incorrect
  behavior" — class 2 is exactly that, even when the fix is a refusal.
- **Go's compatibility promise** exempts bugs and security fixes from "programs
  keep compiling and running": a program depending on buggy behavior is not owed
  the bug. Its `GODEBUG` flags are the escape valve when a corrected behavior
  still needs a temporary opt-out.
- **Rust RFC 1105** is the reference statement that not every breaking change is
  major: a minor release may carry a technically-breaking change no reasonable
  code observes.
- **PostgreSQL** minor releases routinely tighten checks whose acceptance
  produces wrong results; the fix ships in a patch because the accepted input is
  already broken.
- **SQLite** shows the ladder for the other case — input people demonstrably *do*
  rely on: keep the behavior, then warn, then offer an opt-out, then flip the
  default, across releases. That is class 1 handled gently, not class 2.

The counterweight is **Hyrum's law**: with enough callers, every observable
behavior is depended on by somebody. Class 2 therefore demands a positive
argument that no working caller exists — "the stored sentence can never match a
query" is one; "probably nobody does that" is not. When in doubt, treat the
change as class 1.

Three process rules follow:

- **Every Breaking and every Refusal entry carries a one-line *Migration:***
  stating what a caller of the previous release does about it — even when the
  answer is "nothing: no working caller exists", because that sentence is the
  class-2 claim made checkable.
- **At release time the changelog is closed against `git log --oneline
  <last-tag>..`**: every `feat(`, `fix(`, `perf(` and behaviour-moving `build(`
  commit has an entry, including functionality no public entry point reaches yet —
  an engine-internal subsystem, developer tooling, a bench or a lint check. An entry
  postponed to the release where the functionality becomes caller-visible is one
  no release writes. The one exemption is a fix to code no release has shipped. An
  entry written at commit time is cheap; one reconstructed at release time is
  guesswork.
- **Every Breaking and every Refusal entry also carries a `*Breaks:*` line, and
  the release greps the siblings for it.** The line holds one backticked token
  per name a caller would have written — a retired option key or symbol, an
  ex-info `:type`, a fragment of a message somebody matches on, or the API name
  whose behaviour moves. Prefer a token distinctive enough to be worth a grep:
  `sentexes-matching` points at call sites, where a token that is also an
  ordinary English word points at every README beside the code. More tokens than
  fit on a line take a second `*Breaks:*` line.

  `bash scripts/check-breaking-siblings.sh` (`lein check-siblings`) reads those
  tokens off the unreleased section and greps every sibling checkout on the
  machine for each, printing the hits with file and line. It is a **release
  step**, not a gate: it reads other repositories, and which of them are cloned
  is not a fact about this tree, so a missing sibling is named and adds no work
  and the run exits 0 whatever it finds. Every hit gets a verdict in the release
  notes — fixed in the sibling, filed against the sibling, or a non-issue with
  the sentence saying why. **Absence of hits is not proof**: the check greps
  names, and a sibling can depend on a behaviour without spelling one.

  The asymmetry is the argument. An entry that names a sibling it does not break
  costs a maintainer one grep; an entry that names nobody ships a green release
  and a red sibling, found by whoever pulls next — which is how the 0.5.0
  `open-kb` option rename reached `vaelii-foreign`'s test scaffolding and a
  downstream harness's benchmark cells.

### 3.9 Compacting a released changelog section

[`CHANGELOG.md`](CHANGELOG.md) carries the current release in full and every older one as
a summary. When a release stops being the current one, its section is replaced by four
things: the heading it already had, a class census (`**N entries** — n Breaking, n
Refusal, n Additive, n Fix`), a paragraph of three to five sentences saying what the
release did, and **every `*Breaks:*` token the section carried**, merged into one
`*Breaks:*` line with duplicates removed.

**The `*Breaks:*` tokens are the part that must survive verbatim.** An upgrade across
several releases is a grep for the name a caller wrote, and a token dropped in compaction
is a migration the reader cannot find. `scripts/check-breaking-siblings.sh` reads the
current section only, so nothing else re-checks the older ones.

The mechanism paragraphs go, because §8's rule puts a mechanism in the `docs/` page that
owns the subsystem, where it keeps being true. Before dropping one, check that every
argument in it has a home. Mechanism belongs in the subsystem page; a rejected
alternative, or a choice a reader would question, belongs in
[`docs/defenses.md`](docs/defenses.md) under a stable heading the subsystem page links to.
An argument recorded nowhere else is the one thing compaction must not lose. The dropped
prose stays reachable at the tag of the release that shipped it — `git show
v0.16.0:CHANGELOG.md` — and the file's header says so.

Compaction happens at the cut, in the same commit that dates the new section, so the file
has exactly one section in full at any time.

### 3.10 Prose style: literal technical language

Every comment, docstring, doc page and test name states what the code does, in literal
technical language. A reader who knows [`docs/glossary.md`](docs/glossary.md) decodes a
sentence on one pass, with no inference about what a metaphor stands for or what a
pronoun points at. Eight rules:

1. **Name the subject in every sentence.** No `it`, `that`, `this` or `the same` whose
   referent is a preceding clause rather than a noun already written down.
2. **No pseudo-cleft.** Not "What holds the wrap to the library is a version pin."
   Write "A version pin holds the wrap to the nippy release it was written against."
3. **No verbless sentence and no fragment.** Every sentence has a subject and a finite
   verb. Not "Two ways to be wrong, and they are not the same one." Write "This throws
   for two distinct reasons."
4. **No metaphor for a mechanism.** Name the mechanism:

   | Metaphor | What it actually is |
   |---|---|
   | door, at an API | entry point, write entry point, read entry point |
   | door, at a guard | check, allowlist check, refusal |
   | the front door | the public API entry point |
   | cone, up-cone | ancestor set, upward closure |
   | teeth, spine, the ground moves | what enforces it, the chain, the dependency moves |

   `seam` named five different things, so it has five replacements. Pick the one that
   says what is there, and name the thing itself where you can:

   | What it actually is | Write |
   |---|---|
   | a `defprotocol` a backend, prover or solver implements | **the `RecordStore` protocol**, `KvIndexStore`'s methods |
   | a place an out-of-tree implementer plugs in — the foreign plugin manifest, `set-solver`, `add-evaluatable`, a `*dynamic-var*` hook | **extension point** |
   | `vaelii.core` and the five shims | **the public API** |
   | one namespace's public vars, where that is not the API | **the public surface of `vaelii.impl.x`** |
   | a layering cut between two namespaces that nothing plugs into | **boundary** |
   | the point the profiler tallies at | **call site** |

   `interface` stays for one thing: a **network** interface, the thing `--listen` binds.
   A KB modelling convention is a **pattern**, and gets named — "the `exceptWhen`
   pattern", never "the exception interface".

5. **Mechanism first, reason second.** State what the code does, then why.
6. **One claim per sentence.** No second claim chained onto the first with a subordinate
   clause.
7. **Use the glossary term or a plain noun.** No coined synonym for a term that already
   has an entry, and no new coinage without one.
8. **No evaluative adjective without a number behind it** — load-bearing, honest, cheap,
   loud, worth writing down, earns its keep, the tempting alternative. Where the claim
   is quantitative, cite the test or bench that measures it (§8).

**`lein lint`'s `prose` check** (`scripts/check-prose.py`) enforces the mechanical part:
P1 banned metaphors, P2 banned rhetoric, P3 pseudo-cleft, P4 a copula with `are` straight
after it. It reads `src/`, `test/`, `bench/`, `docs/`, `scripts/`, `resources/kb/`,
`tools/` and the root markdown against `scripts/prose-baseline.txt`, a per-file budget
that only
shrinks — a file absent from the baseline is pinned at zero, so new and rewritten files
are clean by default. The sentence-form rules are held by review. This section states the
rule, so it quotes the banned tokens in order to ban them and is exempt by name, the
arrangement §3.6 and §3.7 already use.

P4 is not a style rule but a guard on the other three. P1 and P2 name what to write
instead, and a substitution made across the tree at once is how a batch of their hits
gets fixed, so `is read as a` rewritten to `is are indistinguishable from a` is what such
a pass leaves behind.

The tree is at zero today, so `scripts/prose-baseline.txt` holds no entries and any hit
fails. The file stays because the ratchet is how a batch of new prose lands without
blocking on rewriting all of it at once.

## 4. Adding things

### 4.1 Adding a predicate, type or rule

Just assert it. Add it to the appropriate file under `resources/kb/` if it should
bootstrap with the starter ontology, or assert it at runtime.

If your predicate is transitive, symmetric or functional, assert the meta-predicate
alongside it and the existing machinery picks it up. A declaration the engine does not
read is worse than none, because it is indistinguishable from one that works:
`vaelii.impl.vocabulary` is the roster of what the engine's own grammar actually
enforces, and `vocabulary_audit_test.clj` fails both on a `CxCore` term the roster
does not mention and on a roster entry naming a term the grammar has retired. If you
add a declaration, add it there too.

### 4.2 Adding a prover

Provers are the query primitives: index lookups, transitivity walks, conjunctive
joins. A new one needs a name keyword, an applicability check, a body returning
`{:bindings :supports}` results, and a cost estimate for ordered-join planning. The
registered ones in `vaelii.impl.provers` are the templates; see
[`docs/inference.md`](docs/inference.md).

### 4.3 Adding a foreign-format reader

**Not here.** The engine ships no reader for a format it does not write: a reader is a
separate artifact that declares itself on the classpath, and this repo's
`foreign_contract_test.clj` pins the fact that nothing in this tree names one, carries
one, or declares a format. Readers live in
[`vaelii-foreign`](https://github.com/vaelii/vaelii-foreign), which is Apache-2.0 and
has its own contribution terms. [`docs/foreign.md`](docs/foreign.md)

### 4.4 Changing the public surface

Adding to `vaelii.core` is fine and expected. **Renaming or removing** anything on it
is a breaking change, and `public_api_test.clj` will say so. Say it in the pull request
too, with the migration.

## 5. Testing

```bash
lein test                        # the :default selector, memory stores — the routine loop
lein test :all                   # ...plus the ^:slow half
lein test :slow                  # only the marked ones
lein test-multi-jvm              # the cross-process tests — opt-in, in neither of the above
lein test-fuzz                   # the exhaustive truncation sweep — likewise opt-in
lein test-backends               # the whole suite once per backend (all eight)
lein test-sweeps                 # ...and once per alternative implementation (all five)
lein test-matrix                 # both at once, concurrently — ~13 min, not ~55.
                                 # Shuffled launch order, seed printed; `--ordered`
                                 # schedules the longest first instead
lein test-shuffle                # the thirteen in a seeded random order, memory first,
                                 # stopping at the first red — the fresh-angle smoke walk
```

**Tests are integration tests against the storage backend**, not unit tests over
mocks — the in-memory stores by default, with no external dependency.

- **The suite owns a block of two space numbers**, named by its top: a scratch space
  15 that nearly every test uses, and an isolated space 14 for tests that rebuild
  a KB in a loop. Every test KB shares those numbers and the fixtures clear them, so
  **run one suite at a time**. `VAELII_TEST_SPACE=11` moves the block, which is how two
  concurrent runs get distinct directories.
- **All KB scaffolding lives in `vaelii.test-util`**, which owns the `*kb*` var — a test
  namespace declares none of its own. Reach the KB through `tu/deftest-kb` (a `deftest`
  whose body has `kb` bound) or `tu/with-kb`.
- **Tests are net-neutral.** A test never permanently adds terms: it invents gensym'd
  temporaries with `tu/with-terms`, whose role is inferred from the symbol's own shape
  (§3.1) and whose generated name embeds it, so a failure names what it was about. The
  fixture retracts everything and asserts the live sentex and justification sets are
  back to baseline, which is a real teardown-completeness check.
- **`VAELII_TEST_BACKEND` takes a backend name**, spelled `<records>-<index>`
  (`memory-columnar`, `disk-dense`) — `memory` is the one pair named for a single store
  on both axes, `disk-log` is durable records under the write-ahead-logged index, and
  `overlay` is the fork decorator rather than a pair. The suite must be
  **failing-set-identical across all eight**, and so must the assertion count — which
  the runners check against `config_expected_delta` rather than print for a reader to
  compare, since a configuration that ran fewer assertions than the others is green.
- **`lein gate` runs the memory pair and only that one**, so a change touching storage,
  the index, records, recovery or overlay owes `./scripts/test-backends.sh` a run
  before it lands. A durable-store bug is invisible to the one backend the gate
  exercises, which is the whole reason there are eight.
- **`./scripts/test-sweeps.sh` is the other axis**, and a change touching inference,
  the TMS or context retrieval owes it the same run. Five switches re-run the suite
  through an alternative implementation of something the engine otherwise picks for
  itself — the persistent-map JTMS, the sweep chainer, the node engine, one of its
  tacticians, the reference nested context retrieval — and each is a cost decision rather than a
  semantic one, so the five must be failing-set-identical with each other and with a
  plain `lein test`, and their assertion counts are identical too: where an assertion
  pins an artifact of one implementation (`prove`'s multiplicity, a depthless `query`),
  the test asserts the expectation of the engine in force, read off
  `tu/query-engine-override`, rather than standing aside — so `config_expected_delta`
  expects no shortfall anywhere, and any shortfall is a skip.
- **Run both locally rather than asking CI for them.** The `deep` workflow runs the
  same thirteen configurations, and one run of it is 209 job-minutes — the local
  scripts cost wall time and nothing else, so they are the gate and CI is the
  confirmation.
- **`^:slow` marks a test costing about a second or more on its own**, and `lein test`
  skips those by default. Forty-three of them carry about half the suite's assertions,
  so `:all` is a habit rather than a hook: run it when a change touches inference,
  indexing or the TMS, and occasionally regardless. Mark a *new* test only when it is
  measurably over the line — a mark guessed at is a fast test nobody runs. Not one of
  them is a unit assertion: they are the exhaustive cross-products and the randomized
  oracles — every query pattern against every context, 1200-op index streams compared
  entry-for-entry, 720 orderings of one clash, a 20k-fact generated load. (Measured on
  the memory backend, 2026-08-02: `:default` is 2445 tests / 120,281 assertions, `:all`
  2462 / 238,325. Wall-clock depends on the machine, so read the difference as a ratio
  rather than a target.)
- **`^:llm` marks a test that can reach a language-model provider**, and it is one of
  the three marks `:all` does not select. `lein test` makes no model call, and two
  independent things hold that: the mark picks which tests run, and `VAELII_LLM_LIVE=1`
  grants permission to dial out. A reachable Ollama on your machine is not consent.
  Never write the inverted gate — default-off is the invariant.
- **`^:multi-jvm` marks a test that forks a second JVM**, and it is the second one `:all`
  passes over. These are the cross-process tests — not "integration tests", which is
  what the whole suite already is, and not end-to-end either, since most of them observe
  a single contract from the only vantage that can see it. What they cover is what a
  process boundary makes visible and nothing else does: the single-writer lock refusing
  a second JVM, the OS releasing that lock when a killed one exits, a KB opened cold
  over a directory another process wrote, and the daemon and CLI contending for one
  directory. **Nothing runs them for you** — not `lein test`, not `:all`, not `lein
  gate`. `lein test-multi-jvm` does, and so does `deep`. Fork `java -cp` rather than
  `lein`, give each child its own temp directory, and handshake on a marker rather than
  a sleep.
- **`^:fuzz` marks an exhaustive sweep no configuration varies**, and it is the third
  `:all` passes over — for a different reason than the two above. `^:slow` means
  *deferred until something eventually runs it*; `^:multi-jvm` means *one JVM cannot
  stage this*. `^:fuzz` means *once, not once per configuration*: the truncation sweep
  names its own four durable backends and never asks for the one the row is testing, so
  every row of `lein test-matrix` walks the same 9,717 offsets to reach the same answer.
  (A sweep row's env switch does reach the engine — those alter roots process-wide — but
  over a three-assertion corpus it is not asking a new question.) One test carries the
  mark today. `lein test-fuzz` runs it, and so does `deep`; nothing else does at all.
  Each such sweep keeps a sampled twin at `:default` — a handful of seeded offsets
  through the same harness, so the thing that would otherwise rot silently between deep
  runs is the *harness*, and that part still runs on every commit.
  **Set `VAELII_TEST_TMPDIR` to a tmpfs when you run one.** A probe opens a store over a
  copied directory and closes it, and a close fsyncs, so the whole cost is one device
  cache flush per offset: an *empty* directory measures the same as a real probe, and
  the sweep is ~10 minutes on a disk against a couple on `/dev/shm`. Cheap scratch space
  is also, for now, the only lever: `F_FULLFSYNC` serializes at the device, so four
  workers against APFS measured 0.96× one, and where concurrency does pay (2.7× on a RAM
  disk) a sharded sweep makes a green run print at `:error`. That line is benign —
  `durability.clj` closes the window a close under a queued auto-compaction opens, and
  nothing is written — but it is reported beside real failures, so sweeps stay serial
  until it is classified apart from them.
- **The suite logs at `:error` and no lower.** Trove's default backend prints from
  `:info` up, and the suite provokes `:warn` on purpose — `::dropped-conclusion`,
  `:no-placement` and the aggregate refusals are what the assertions are *checking
  for*, so on a green run they were two thirds of the output and none of it a verdict.
  The `:test` profile's `:injections` raise the floor, through the engine's own dial
  (`vaelii.core/set-log-level`) rather than a copy of it. `VAELII_TEST_LOG_LEVEL=info
  lein test` puts them back, which is what a red run wants; it takes the same five
  levels the dial does — `:error :warn :info :debug :trace` — so `=debug` adds the run
  boundaries (what a chaining run concluded, what a settle cost, the rule behind a
  dropped conclusion) and anything else fails the run by name rather than silencing it.
  **The bench harnesses take the same floor for the same reason**, since a row's
  *reading* is its verdict the way an assertion is the suite's: the clash rows drop
  conclusions by construction and every `fresh-kb` opens over the space the row before it
  filled, so `lein perf` printed 1,307 log lines around its verdicts. `:bench` raises the
  floor, and `VAELII_BENCH_LOG_LEVEL=info lein perf` puts it back.
- **Never gate on a piped test run.** `lein test 2>&1 | tail -30` reports `tail`'s exit
  status, always 0, so a red suite reads as green *and* the failure list is truncated
  out of the log. Redirect to a file, read the status, then grep it.

When verifying a fix has a regression test: stash *only* the fix, run the test, confirm
it fails; restore, confirm it passes.

**Coverage expectation.** Added code should be covered by tests; modified code should
be exercised by existing or new tests. The standard is not a percentage, it is "every
line of new logic is either hit by a test or has been visibly reviewed for correctness
in the diff". Pull requests adding non-trivial logic without tests may be asked to add
them before merge.

## 6. The reload loop

Edit a source file, then at the `lein browser` prompt:

```clojure
(require 'vaelii.browser.web :reload)
```

…and the next request serves the new code. From an editor, connect over nREPL through
`.nrepl-port` and do the same.

The reason `lein browser` exists rather than `lein run -m vaelii.browser.web` is that the
failure it avoids is silent. **A ring handler is a value, and Jetty holds the one it
was started with**, so a reload against a plain `lein run` can redefine every var on
the page and change nothing about what is served: the namespace reloads, the page does
not, and there is nothing to see. `lein browser` serves through a handler that
re-resolves `#'app` per request, so a reload actually lands.

`(vaelii.browser.web/dev-stop)` takes the server down without leaving the prompt.
`VAELII_WEB_PORT` moves it off 3000, and moves `lein run -m vaelii.web` too — an explicit
`--port` still wins.

**Both halves bind loopback, and that pairing is not configurable from here.** The
browser has write routes and no authentication; an nREPL is arbitrary code execution by
design. Either alone is a considered risk on a shared interface — together they are a
remote shell. See [`.github/SECURITY.md`](.github/SECURITY.md).

## 7. Commits & pull requests

- **Target the `develop` branch.** Pull requests land on `develop`; `main` carries
  releases and is pushed by the maintainer, so it is never a pull-request target. The
  required checks live on `develop` and `main` has none, so retargeting is not a
  formality — see §9.4. If the base dropdown offered you `main`, change it.
- **Each commit's `author` is the person who signs it off.** A change someone else
  drafted is landed by re-authoring it, not by committing it under their name with a
  second sign-off appended: a `Signed-off-by:` line is a certification, so it may only
  name someone who can make one — a person who stands behind the account and answers
  for the work. The same holds for the co-author trailers, below.
- **Commit style** is Conventional Commits: `type(scope): subject`, with the scope
  optional. The types in use are `feat`, `fix`, `perf`, `refactor`, `docs`, `test`,
  `style`, `build`, `bench`, `chore`, `deps`. Examples from `git log`:
  - `fix(settle): recompute the touched window instead of reusing the published one`
  - `perf(checks): skip the declaration read when the predicate declares nothing`
  - `docs(kbs): document loading each of the four KBs from a fresh clone`

  A subject says what changed, literally. It is not an aphorism about the change
  (§3.10).
- **Sign off every commit** with `git commit -s`. This appends the `Signed-off-by:`
  trailer required by the [DCO](DCO); the DCO app blocks unsigned pull requests from
  merging. See §9.4.
- **Co-author trailers credit the other people who worked on the change.**
  `Co-Authored-By: Alice <alice@example.com>` and `Co-developed-by:` are how a squashed
  merge preserves that credit, so each names a person who shares authorship: someone who
  can make the DCO (§9.4) and CLA (§9.5) certifications, whose contribution has a
  copyright holder the trailer identifies, and who counts in the contributor statistics.
- **The `committer` field is covered too.** A commit names three parties — who wrote it,
  who applied it, and whoever its trailers credit — and the rule above reaches all of
  them. `committer` differing from `author` is ordinary and welcome: a maintainer
  rebasing your branch, a patch applied by hand, the merge button. Like the author and
  the trailers, it names a person who can stand behind the account.
- **The `authorship` check is where that is decided**, beside `DCO` and `license/cla`.
  A green `license/cla` says the CLA is signed and a green `DCO` says each commit is
  signed off; neither can say a person stands behind the account, and that is the one
  thing this check adds. Every author, committer and trailer on a pull request has to
  appear in
  [`.github/AUTHORS.roster`](.github/AUTHORS.roster), which a maintainer writes on
  `develop`. An account nobody has admitted fails closed, so the first pull request from
  a new contributor waits on being added — a one-line commit, and it carries to every
  later one. That line wants your GitHub login, which is what a commit you push is
  matched on, plus any address you sign a trailer with, which is what a trailer is
  matched on when it names no account. This is a judgement about who stands behind an
  account, never about the tools someone writes with: use whatever you like, and sign
  off as the author of the result. If the check blocks work that is otherwise good, it
  is a rebase and not a rejection — re-author under the person who signs off, drop the
  trailers naming anyone else, force-push.
- **One change per commit** where feasible. Bundle related cleanups.
- **Run `lein gate` before pushing** (§1.1), plus `lein test-matrix` if you touched
  storage, the index, records, recovery, overlay, inference, the TMS or retrieval, and
  `lein test :all` if you touched inference, indexing or the TMS.
- **Don't `--no-verify`**: fix the hook failure rather than bypassing it.
- **Don't amend pushed commits**: make a new one.
- **Merges may be rewritten.** Vaelii may squash, reword or amend your commits when
  merging, so they may not land verbatim.

**A release rewinds `develop`, and we rebase your branch onto it.** Each release is
squashed onto `main` and `develop` is reset to that commit, so an open pull request's
base moves out from under it — and GitHub notifies nobody when a base branch is
rewritten. So we replay your commits onto the new `develop`, force-push your branch,
and say so on the pull request. Your local clone will then be behind the rewritten
branch: resync with `git fetch origin && git reset --hard origin/<your-branch>`, but
only if you have nothing unpushed on it, and rebase your own local work if you do.

This needs **Allow edits by maintainers**, the checkbox on your pull request, which
is ticked by default and yours to control. Leave it on and we do the rebase; untick
it and the pull request gets the commands to run yourself instead. We also leave the
commands rather than touch the branch if the rebase conflicts with the release.

Nothing of yours is lost either way. The `develop` you branched from is kept as
`develop-pre-vX.Y.Z`, and your own commits stay reachable at `refs/pull/<n>/head`
whatever happens to any branch.

**Open an issue before you open a pull request.** Any issue or pull request may be
closed at any time, for any reason, without comment — one with no matching issue
especially. Even with a matching issue, Vaelii may resolve it directly rather than
merge your pull request: the change may be small enough to just apply, may already be
in progress, or may need to land differently than proposed. None of this is a judgment
on your work; filing the issue first lets us coordinate before you spend effort.

## 8. Documentation

`docs/` carries one note per subsystem and is kept current with the code, so a change
to behaviour is a change to a doc. [`docs/README.md`](docs/README.md) is the map, and a
new doc needs a line in it — `lein lint-drift` fails (E6) on a doc the map does not
reach. Every page opens with the same three bullets — **Covers**, **Not here**,
**Assumes** — so write those before the body; E12 fails on a page without them.

| Change | Update |
|---|---|
| New prover | [`docs/inference.md`](docs/inference.md) |
| New backend or index | [`docs/storage.md`](docs/storage.md), [`docs/indexing.md`](docs/indexing.md) |
| Change to the assert path | [`docs/api.md`](docs/api.md), [`docs/nmtms.md`](docs/nmtms.md) |
| New public fn | [`docs/api.md`](docs/api.md) and its `vaelii.core` docstring |
| New term or concept | [`docs/glossary.md`](docs/glossary.md): alphabetical placement within its letter section, and exactly one category badge on the term line (`kb` / `inference` / `tms` / `asp` / `backend` / `qr`). `lein lint`'s glossary check enforces both. |

`lein lint` also checks that every relative link in `README.md` and `docs/` resolves,
and that no link escapes the repository.

**A big measured number is written approximately unless something in the tree pins it.**
A figure precise to the last digit — a sentex count, a µs/read, a wall clock in
milliseconds — is a claim a reader can check, so it stays only where a test, a bench or a
golden reproduces it
(`assert_cost_test`, `lein perf`, `lein bench-*`) or where the page itself states the
workload *and* the method it was measured by. Everywhere else write the magnitude and
name what it was taken on: `~1.2M sentexes on an OpenCyc-sized import`, `about 5 GB`,
`tens of microseconds`, `roughly 7×`. Keep the argument the figure was carrying — a ratio
between rows usually is the argument — and cite the pin or the page that measures it
rather than restating a count of your own. Small exact counts the tree holds (provers,
tool schemas, caches) stay exact, because a test counts them.

**A `clojure` block that is a whole program is run, and it opts in.** Add `run` to the
fence's info string — ` ```clojure run ` — and `vaelii.doc-examples-test` evaluates the
block in a scratch namespace with `v` and `starter` aliased and stores of its own, then
checks it: a comment following a form whose text begins with `=>` states that form's
value, and the runner reads **one** EDN form from it and compares with `=` when what
follows is empty, a `(` opening a parenthetical remark, an em-dash aside or a further
comment — so `;=> true (via genl)` is a claim while `;=> derived, placed in
CxNaturalWorld` and anything holding a `…` are prose the runner leaves alone. Opt-in
rather than opt-out because almost every block in `docs/` is a *fragment* — KB
sentences written bare, a signature listing, a call over a `kb` the prose introduced —
and the marker belongs on the handful that are programs rather than on the rest. A
block that reaches a model provider, a server, or the process-wide log dial never
carries it, and the test refuses one that does.

Its **versions** check holds the coordinates this tree states more than once.
`defproject`'s version reappears in the README install line and in the generated release
badge, and the carve strips `-SNAPSHOT` tree-wide, so a dev tree says the snapshot
everywhere and a cut says the release everywhere; a coordinate left at an older snapshot is
the drift the check catches. The second pair is `lein-cloverage`, declared in
`project.clj` and injected at the root by `scripts/coverage.sh`. Bump each in one commit;
the check names the fix when you do not.

## 9. License & contributor terms

### 9.1 Inbound = outbound

Vaelii is licensed under the Server Side Public License v1 (see [`LICENSE`](LICENSE)).
By submitting a contribution you agree your contribution is licensed under the same
SSPL v1 terms, so downstream recipients receive it on the same footing as the rest of
the Project.

The project intends to move off SSPL-1.0 to an OSI-approved license. The CLA in §9.5
is what makes that move possible without re-collecting permission from every
contributor.

### 9.2 Contributor representations

By submitting a contribution you represent that:

- The contribution is **your original work**, or you have the right to submit it (e.g.
  it is a derivative of work whose license permits this submission, and you preserve
  required attribution).
- You have the **right to grant the license** in §9.1 and the further grants in §§9.3
  and 9.5.
- Your contribution does not **knowingly include code under a license incompatible
  with the outbound license of the repo you submit it to** (for the SSPL v1 engine:
  e.g. proprietary code you do not own, or GPL-family code — the SSPL is GPL-derived
  but not GPL-compatible, so GPLv2, GPLv3, and AGPLv3 code cannot be combined into an
  SSPL work).
- If your **employer** has rights to intellectual property you create, either (a) the
  employer has waived rights to this contribution, (b) the employer has consented in
  writing, or (c) the employer has signed the Corporate CLA (see §9.5).

### 9.3 Patent grant

You grant Vaelii LLC (the Project steward) and downstream recipients a perpetual,
worldwide, non-exclusive, royalty-free patent license to make, use, sell, offer for
sale, import, and otherwise transfer your contribution as part of Vaelii. The license
covers only those patent claims that you can license and that are necessarily
infringed by your contribution alone or in combination with Vaelii. This grant
terminates for any party that initiates patent litigation alleging that Vaelii or your
contribution infringes a patent.

### 9.4 Developer Certificate of Origin

Every commit in a pull request must be signed off under the [DCO](DCO) (Developer
Certificate of Origin 1.1, by the Linux Foundation). To sign off:

```bash
git commit -s          # appends Signed-off-by: Your Name <email>
git commit -s --amend  # add sign-off to the most recent commit
```

A `Signed-off-by:` trailer certifies that the four DCO clauses apply to your commit.
The [DCO GitHub App](https://github.com/apps/dco) checks every commit and blocks the
merge if any is missing a sign-off.

**That check is a required one on `develop`** — the pull-request target (§7) — beside
`lint`, `license/cla` and the suite. `main` carries releases, is pushed by the maintainer,
and requires none of them, so a pull request aimed at `main` is not a lighter path to the same
review: it is a path with no review on it at all, and it will be retargeted rather than
merged.

The **suite** (`memory` / `disk-log`) is required too, and it runs on **every** pull request —
a doc-only one included, which it passes in a few minutes. No path filter narrows it, and
that is what lets it be required: a workflow a filter skips reports nothing at all, not
even a skip, so a required check naming it would block every pull request the filter
matched for ever. A red suite is a change that does not land, at the merge button rather
than at the reviewer's discretion.

The DCO's text says "the open source license indicated in the file", and every `.clj`
file under `src/`, `test/` and `bench/` indicates it — a two-line SPDX header:

```clojure
;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
```

Keep it on a new file. It is what makes a file that travels out of the tree still carry
its license, which is what SSPL §4/§5's "keep intact all notices" is aimed at, and it is
what your sign-off certifies against. Vaelii's license, the SSPL v1, is source-available
rather than OSI-approved (see the README's License section).

If you forgot, you can sign off a range of commits:

```bash
git rebase HEAD~N --signoff   # sign off the last N commits
```

### 9.5 Contributor License Agreement

All contributions also require a signed Contributor License Agreement:

- Individuals: [`legal/ICLA.md`](legal/ICLA.md)
- Corporations (when an employee contributes on behalf of an employer that owns the
  IP): [`legal/CCLA.md`](legal/CCLA.md)

[cla-assistant](https://cla-assistant.io) prompts you to sign the ICLA when you open
your first pull request; the signature is recorded against your GitHub account. That
flow is the only way to sign the ICLA.

Corporations sign the CCLA through our hosted signing form (DocuSeal Cloud), linked
from https://vaelii.com/cla: an authorized representative completes and signs the
agreement, including the schedule of covered contributors (see CCLA §9). An authorized
representative may alternatively email the completed agreement to legal@vaelii.com.
Covered employees still complete the cla-assistant flow so the automated check passes.

**Why we ask for a CLA in addition to inbound=outbound.** SSPL v1 is the default
outbound license, but the Project may need to relicense in the future. Without a CLA,
Vaelii LLC — the Project steward, and the grantee named in both CLAs — would have to
re-collect permission from every contributor to do that. The CLA grants Vaelii LLC
(not downstream recipients, who still receive SSPL v1) the broader rights needed to
keep that option open. It does **not** weaken your ownership of your contribution: you
retain copyright and can use your code in any way you wish.

The CLA applies to every contribution, however small. cla-assistant prompts once, on
your first pull request, and the signature carries to all later ones; a typo fix costs
the same two-minute signature as a feature.

This section summarizes the contributor terms. If it differs from the signed CLA or
from [`LICENSE`](LICENSE), those documents control.

### 9.6 Credit & conduct

Legal credit for your work lives in your DCO sign-offs (§9.4) and the cla-assistant
signature database. [`CONTRIBUTORS.md`](CONTRIBUTORS.md) is separate — a
community-goodwill roll you are welcome (never required) to add yourself to in your
first pull request.

Participation in the project's spaces is governed by the
[Code of Conduct](https://github.com/vaelii/.github/blob/main/CODE_OF_CONDUCT.md)
(Contributor Covenant 2.1). Report concerns to support@vaelii.com.
