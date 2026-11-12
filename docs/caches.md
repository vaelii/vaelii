# What the process holds beside the stores

- **Covers:** the cache register (`vaelii.impl.caches`) — how a derived, droppable
  structure declares itself, what a descriptor says (`:scope` `:unit` `:limit`
  `:counters` `:note`), the two bound policies (a counted cache cleared wholesale, a weighted
  LRU evicted from its cold end), the profile
  that scales every counted bound (`VAELII_CACHE_SCALE`, `cache-profile`,
  `set-cache-scale`, `set-cache-limit`), the memory-pressure guard that shrinks the caches
  under a filling heap and grows them back, the heap mark that refuses a chaining run over
  a nearly full heap, the two reads `caches` / `clear-caches`, and
  the derived-state register: every structure kept between writes, its key, its reads and
  the write events that retire it.
- **Not here:** what the *stores* cost — the JVM heap figure and a loaded KB's estimated
  footprint → [catalog.md](catalog.md); what the index *is* → [indexing.md](indexing.md),
  [density.md](density.md); readings about the *traffic* rather than the held answers →
  [profile.md](profile.md); readings about the *knowledge* → [quality.md](quality.md);
  the two numbers in the relation-algebra mask layer that bound a **build** rather than a
  cache — the algebra width, and the dense-table threshold → [qcn.md](qcn.md).
- **Assumes:** sentex, handle, generation, the `genlCx` closure, the change clock →
  [glossary.md](glossary.md), [taxonomy.md](taxonomy.md).

A cache is a map of answers the engine would otherwise recompute — atoms and plain
maps, none of them a store, all of them droppable without moving a belief. They do
not show up in a heap figure as anything but bytes, and "the second query was fast" is a
demo until a hit rate says *why*. This is the register that names them and the read that
counts them.

## The register

`vaelii.impl.caches` **requires only `config`**, a leaf that holds no cache, so the reader
still has no require edge down to a namespace that holds one. Every such namespace requires
*it* and calls `register-cache` once at load, so there is no list here for a new cache to
be added to twice. The one `config` edge reads `VAELII_CACHE_SCALE`. The register is
open: a cache in a namespace this process never loaded — a qualitative calculus nobody
touched — is absent from the read rather than present as a row of
zeroes.

Each descriptor carries what a reader needs to compare rows that count different things:

- **`:scope`** — `:kb` for a cache hanging off one KB record, `:process` for a static one
  every KB in the JVM shares. It says what `:entries` counts.
- **`:unit`** — what one entry *is*: a literal, a network, a symbol, a mask. A column of
  bare integers compares none of them, so the unit rides every row.
- **`:limit`** — the effective bound: entries held before the cache is cleared, or nil for
  one bounded by something other than a count (a generation, the store lifecycle), named in
  `:note`. A counted bound is the shipped default scaled by the profile (below), so the
  number a row reports is the number the cache enforces now.
- **`:counters`** — `:kb`, `:process`, or nil: what a row's `:hits` / `:misses` count,
  which is not always what its `:entries` count. The closure neighbours count per
  process, and their entries are readable only from inside the search step that holds
  them, so that row reports a rate against a blank count. A row a derived-state tally
  counts is `:kb` (below, "Counting the register").
- **`:note`** — one line: what it holds and what retires an entry.
- **`:read`, `:clear`, `:trim`, `:reset-counters`** — functions of the KB. `:read`, `:clear`
  and `:reset-counters` take the KB even for a process-wide cache and ignore it, so a caller
  needs one calling convention. `:clear` is scoped to its argument: a clear that reached
  past it would make `clear-caches` a process-wide control with a per-KB signature. `:trim`
  is the partial drop the memory-pressure guard uses, bringing a cache down to a target
  while keeping the rest. `:reset-counters` exists only for a cache whose `:counters` are
  `:process`, and stays separate from `:clear` because it is wider than one KB.
- **`:limit` as a thunk.** A descriptor is built once at namespace load, so a constant
  captured into it is fixed. A bound that is a `^:dynamic` var or profile-scaled is written
  `:limit (fn [] *the-var*)` (`limit-thunk` builds the profile-scaled one), and the row
  reads it where it is read; a captured root value would misreport the bound somebody
  rebound.

A row whose `:entries` is nil cannot be counted from outside — it is scope-bound, alive
for the length of one chaining run or one search step and garbage when it returns. It is
registered all the same, so the list is complete rather than merely finite.

## The bound: a counted cache is cleared wholesale

A counted cache past its bound is dropped **whole** (`assoc-bounded`), not trimmed to the
one entry that would make room. Evicting exactly the right entry costs more bookkeeping
than the entry saves, and a cache that has outgrown its bound is one whose questions have
moved on. A nil bound is not unbounded neglect: those caches are retired by a **generation
bump** (a taxonomy edge or context change retires every closure read at once), by the
**change clock** (a per-placement counter, so a chaining run meets its own reads cold), or
they are structural (the symbol pool, the compiled algebras) where dropping entries costs
the sharing they exist for.

A **weighted LRU** (`caches/weighted-lru`) bounds the sum of its entries' weights instead,
and evicts from its cold end until the sum is under the bound. The taxonomy closures
([taxonomy.md](taxonomy.md#reads-are-scoped-by-the-asking-context)), the arity lengths and
the whole `genl` reaches `inherit` walks use it, because their entries differ in size by
orders of magnitude.

Clearing wholesale is cheap and it is fragile in one direction, so **a scan does not get
to fill one**. A read that asks thousands of literals *once* — a transitive closure walk
visits each node once and asks that node's neighbour literal once — pushes the literal
cache past its bound and clears it part-way through, discarding the entries a rule-heavy
query really does re-ask for a pass that had no repeat of its own to serve. A 5 000-node
walk crosses the 4 096 bound before it ends, having asked for a repeat on almost none of
those nodes. So the walk's neighbour probes read with `res/matches-visible`'s `cached?`
false, and the walk keeps its repetition
where the repetition is — the whole closure in `:closure-answers`, the neighbour sets a
join re-walks in the search step's memo. A cache earns its eviction where the questions
repeat; a scan is the read where they do not.

It is the *probe* that opts out, not the walk: the seed read a `(P ?x ?x)` condensation
takes is one extent literal, asked through the ordinary cached entry point, because one literal
asked once is not a scan.

## Tuning the bounds

Every counted bound `caches` reports is a **shipped default** the process scales by one
number. At scale 1.0 — the default — a cache enforces exactly its shipped bound, so a
process that sets nothing holds the bounds it always did. `VAELII_CACHE_SCALE` sets the
scale a process starts with (default `1.0`, read as the engine loads): below 1 shrinks
every counted cache for a small heap, above 1 grows them for a bulk load. A per-cache floor
(`caches/min-limit`, 16 entries) keeps a small scale from taking a cache below the point
where the reads it serves are a fraction of the reads it forces to recompute.

On a running process the same dial is `vaelii.core`:

- `(cache-profile)` — the scale and any per-cache overrides in force.
- `(set-cache-scale x)` — multiply every counted bound by `x`, process-wide; `1.0` restores
  the shipped bounds. Refused when `x` is not a number 0 or more.
  The browser's caches page sets the same scale through `POST /caches/scale`
  ([web.md](web.md#pages)): a write to the whole process, reaching every KB loaded in it,
  and origin-checked like every browser write. The route answers 400 to a value that is not
  a finite number 0 or more, and to no value at all, and changes nothing.
- `(set-cache-limit id n)` — override one cache's bound with `n`, or clear the override with
  `nil`. `id` is a `:cache` keyword from `caches`. The scale leaves an overridden bound alone,
  for a cache measured on its own. The memory-pressure guard does not: an overridden cache
  shrinks under a filling heap like every other counted cache, because the guard's relief has
  to reach every counted cache or an override holds the heap short of the reclaim the guard
  exists to force. An override on a registered cache no override moves is **refused**
  (`:unknown-option`): the three bounds outside the scale below, and the nil-bound caches. An
  `id` no cache has registered yet is warned and recorded, since its namespace may load later
  and take the override.

## The memory-pressure guard

The scale is an operator's standing choice; the **pressure** is the engine's own response to
a heap filling under it. On the servers a post-collection listener reads how full the old
generation is after each garbage collection and moves a second multiplier, `:pressure`,
between two marks:

- over **0.85** it halves pressure and trims the counted caches down to the new, lower bound,
  so the next collection has something to reclaim;
- under **0.60** it raises pressure back toward the operator's scale, so a transient spike
  does not leave the caches small for the rest of the run.

Over **0.92** it also sets `caches/heap-critical?` ([the heap mark](#the-heap-mark)), and the
next collection under 0.92 clears it.

Both multipliers apply: a cache's effective bound is `default × scale × pressure`, floored at
`min-limit`, and `cache-profile` shows both. An overridden cache's bound is `override ×
pressure`, since an override is set against the scale but not against the guard. The trim is **partial**, not a
wholesale clear
(`trim-map!`, or a cache's own shape-aware `:trim`): past the lowered bound a cache keeps that
many entries rather than none, so the reads the survivors serve are not all recomputed the
moment pressure passes. The pressure floor (0.125) keeps a heap under sustained pressure
holding a fraction of each cache rather than running every read cold. A trim that throws is
logged at `:warn` naming its cache and costs that cache alone.

The guard is the **servers'** — attached at startup (`caches/install-memory-guard!`, fed the
live KBs by the host's catalog) and by nothing at engine load, so a library embedding pays
for no listener it did not ask for. A JVM whose collectors emit no such notification, or names
no old-generation pool, keeps pressure at 1.0; the guard is a best-effort relief, not a
guarantee. The pure-heap caches are its charge — the disk hot-record cache stays on its own
`vaelii.disk.cache` cap, since its records are re-thawable from disk and its bound is set at
store open.

`caches` reports the effective bound each cache enforces, so the scale and the row never
disagree. Two bounds stand outside the scale: the **symbol pool**
(`*symbol-pool-limit*`), because its check runs per symbol interned — the hottest path on a
load — and scaling it risks the sharing it exists for (a disk store's open raises it to twice
its token dictionary, [storage.md](storage.md#symbol-interning)); and **hot records**, whose per-kind
LRU has its own knob (`vaelii.disk.cache`). The nil-bound caches
have no count to scale. An override does not move any of these, so `set-cache-limit` refuses one
rather than recording an override nothing reads.

## The heap mark

The heap mark is the crash refusal, and it is separate from the guard's cache trim.
`kb/open-kb` arms it once per JVM (`caches/arm-heap-mark!`), and nothing disarms it. The mark
sets the old generation's collection-usage threshold at **0.92** of the pool's max and
attaches a listener for `MEMORY_COLLECTION_THRESHOLD_EXCEEDED`, which sets
`caches/heap-critical?`. A chaining run reads that flag before each agenda datum, before each
firing, and before each join row under a bound. Inside `chain/*rollback-scope*` the run
refuses `:interrupted :bound :heap` and the write rolls back in the remaining 8%.
`forward-chain` runs inside that scope under either `:on-stop` value. A replay
(`oplog/*replaying?*`) takes no heap stop (`chain/heap-stop?`). Every other run goes
on ([inference.md](inference.md#stopping-a-run)). Below the mark, a
collection runs no engine code, and a firing pays one volatile read per check.

- **The pool** is the one the guard reads: the heap pool named `old` or `tenured` with the
  largest max (G1 Old Gen, PS Old Gen, Tenured Gen, ZGC Old Generation). The guard sets
  and clears the flag at each collection from that collection's usage of the same pool. Shenandoah,
  Epsilon and non-generational ZGC name no such pool, and the mark arms nothing there.
  `memory-guard` reports the armed pool under `:heap-mark`.
- **The flag clears** at a check that reads the pool under 0.92, with or without the guard.
  The reading is the lower of the pool's collection usage and its usage now
  (`caches/pool-fraction`). A young collection's after-usage, which the guard reads, counts
  dead tenured objects. G1's collection usage counts a dead humongous object until a young
  collection reclaims it, so on G1 a dead humongous object holds the flag from the
  concurrent cycle that counted it to the next young collection. The pool is read only
  while the flag is set. A rolled-back run's garbage counts against the pool until
  the next collection of the old generation, so a write retried at once may refuse again.
- **The threshold fires at the collection the guard's reading crosses 0.92**, measured on
  JDK 25's G1 under a heap filling at a steady rate (256 MiB, 1 GiB and 2 GiB heaps). G1
  updates the old pool's collection usage at a mixed collection, a concurrent cycle's end
  and a full collection, and not at a young-only collection; above the initiating occupancy
  a concurrent cycle runs between young collections, so the reading moves at the same
  collection.
- **The opt-out** is `vaelii.heap.mark=false` ([operations.md](operations.md)). The JVM keeps
  one collection-usage threshold per pool and the last writer sets it, so an embedder that
  sets its own turns the mark off.
- **Settle and recover read the flag only in their chaining.** A settle's re-chain and
  `recover`'s refusal re-fire (`rerecord-refusals!`) run the agenda loop and read it there;
  settle's relabel and recover's rebuild of the taxonomy and the network read nothing.
- **An `OutOfMemoryError` that arrives anyway** unwinds through `undoing-refusal`, which runs
  the rollback; a rollback that fails too is attached to the error as suppressed, and the
  error is rethrown. A logged write marks the log `[:unusable [:vm-error op cls]]`
  ([operations.md](operations.md)).

## Reading them

- `(caches kb)` — one row per registered cache: `:entries :limit :unit :hits :misses
  :hit-rate`, plus `:scope` / `:counters` / `:note`, and `:error` where a row's own read
  threw (one broken descriptor costs its row, not the answer). Each row is a count off a
  map the engine already holds, **O(1)**, so the page that shows it can poll. A row is
  data all the way down: the three function slots are dropped and `:clearable?` and
  `:counters` stand for them, because the read is served over RPC and rendered on a page.
  Rows rank by entries descending, ties broken on the cache's name, and a row that cannot be
  counted sorts last, so two processes holding the same caches list them the same way.
- `(clear-caches kb)` — drop every cache that offers a clear and say what went. Bare, not
  `!`: every entry is derived and no belief moves, which makes a clear a *measuring
  instrument* — clear, ask the same question again, watch the miss the second ask no
  longer skips. Scoped to `kb`; `{:counters? true}` also zeroes the process-wide rates, in
  a call that says out loud it reaches past its argument. The hit and miss counters of some caches are process-wide, so zeroing one
  would reset a rate every other KB in the JVM reports mid-measurement; the answer then
  carries `:counters-reset`, and `:tallies-reset` for the derived-state tallies. A cache with
  no `:clear` (the symbol pool, the compiled relation algebras) is left alone, since dropping
  its entries costs the sharing they exist for. A clear that throws costs its own entry and
  no other.

Both are on the remote surface (`vaelii.host.serve`) and drive the browser's caches page.

A bound written per algebra, per calculus or per kind applies to each algebra, calculus or
record kind on its own, and the row's count is the total across them, so the count can
pass the bound with no part past it. The units do not sum: each row counts its own unit,
and a total across rows is a number of nothing.

## The derived-state register

A cache row states a bound. The **derived-state register** states a dependency, and it
covers every structure the engine keeps between writes or across one pass, a cache
`clear-caches` may drop or not. Each namespace that holds one calls
`caches/register-derived` at load, and `(caches/derived-state)` returns the register as
data: `{:rows :events :edges}`. `lein derived-state` prints the two tables below.

`lein derived-state -- --edn <path>` loads the starter ontology into a memory KB and
writes the **export** (`derived-state-test/export`, printed instead when the path is
left out): every row and event cut to its ids, codes, registration site (`path:line`)
and numbers, with the revision it was taken at. A row carries `:held`, the entries it
holds, and every count the register reports; any other value is dropped, so an export
holds no handle and no sentence and a reading of a private store can be shared.
`python3 scripts/derived-state-graph.py <export> <page.html>` draws the dependency
graph from it: the events, the stores and the rows with their read edges, the
event × row table, and the settle features of `scripts/derived-state-features.edn`
with their removability. The page reads a count it finds on a row or event as an
overlay, and opens a second export from a file.

A row declares:

- **`:kind`** — `:cache` (filled at a read, droppable without moving a belief), `:index`
  (kept at the write, rebuilt only by recover), `:journal`, `:queue` (take-and-empty),
  `:counter` or `:pass` (scoped to one pass, run or call).
- **`:keyed-by`** — what an entry is keyed by: handle, functor, type, context, reader,
  node, term, literal, value or global.
- **`:reads`** — the rows and stores it is computed from, by id.
- **`:retired-by`** — each write event that retires entries, with the code saying how:
  **K** per key, **S** per key part, **G** a generation bump, **G\*** the change clock
  every write in the process bumps, **I** identity against a value the write replaces,
  **W** wholesale, **Q** a take-and-empty drain, **C** never stale, **P** pass-scoped,
  **R** rebuilt whole.
- **`:computed`** — where an entry is computed: at the write, in the settle, at a read, or
  in a pass.
- **`:holds-content?`** — whether an entry holds a sentence the KB holds or would hold
  that no store holds: a refused firing, a pending mint or lift. Such a row breaks
  [nmtms.md](nmtms.md#3-separated-state)'s third invariant, and the column `content` below
  marks it.
- **`:covered-by`** — `{:perf [check …] :perf-ab [probe …]}`: the `lein perf` checks
  and perf-ab probes that fail when the row is replaced by a recompute at its read. A row
  no measurement needs costs a retirement path and serves no read faster.
- **`:imaged?`** — which section of a reasoning image carries it. The image's list of
  carried atoms (`reasoning-image/state-atoms`) is read off the register, so the image and
  the register cannot disagree.

The **write events** are a closed set, `caches/events`: each names the vars it passes
through. `derived_state_test` wraps those vars, drives every event on a small KB, reads
every row at each wrapped call's entry and exit, and fails on a row that moved under an
event its `:retired-by` does not name. A move counts as an entry dropped or replaced for
a `:cache` or `:queue` row and as any change for the rest. A move inside a wrapped call
is charged to the innermost call; a move outside every call, or of a row computed at a
read, is charged to the events since that row last moved, and a move with no event since
is a read's own work, which the test lists and does not check. A declared pair no event
moved is listed in the test's output.

`lein lint`'s `derived` check fails on a top-level `defonce`, atom or volatile under
`src/vaelii/impl/`, or a field of the `Reasoning` record, that no register row names. State
that is not derived from knowledge (instrumentation, storage spaces, locks,
configuration) is listed in the check's allowlist with the reason. The check also fails
on a row id in `scripts/derived-state-features.edn` that no row declares, or that two
features name, and on a row that declares no `:holds-content?`. A row declaring it true
fails unless the check's `HOLDS_CONTENT` list names it; an entry there naming a row that
does not declare true fails as well, so the list only shrinks. A row of kind `:index` or
`:cache`, computed at the write or the settle, whose `:reads` do not reach M1 and whose
namespace does not implement `IndexStore`, keeps a belief-free index outside the
IndexStore; the check fails it unless its `OUTSIDE_INDEX` list names it, under the same
shrink-only rule. A row owned by `decide.arity` with no `:covered-by` fails unless the
check's `COVERAGE_OWED` list names it, under the same shrink-only rule, and so does a
`:covered-by` naming a check or probe that `bench/` does not define.

Two `Reasoning` fields hold the entries of several rows, told apart by key: `:taxonomy`
and `:nogood-candidates`. A row locates its entries in one of them by key, as
`[:nogood-candidates :inherited]`, and a symbol inside a key is written `::caches/reader`.
`derived_state_test` watches the two maps while its scenario runs and fails on a key
that no row's `:at` names and that its own allowlist does not name. These keys are
checked at run time and not by the lint, because many namespaces write them and part of
each key is data.

The tables are generated from the register by `lein regen-goldens`, and
`derived_state_test` fails when they differ from it.

<!-- derived-state register: generated by `lein regen-goldens` -->

| id | structure | owner | keyed by | reads | retired by | computed | kind | image | cache | content |
|---|---|---|---|---|---|---|---|---|---|---|
| S5 | Refused firings | `special` | handle | records T1 | E2 K, E3 K, E17 R, E18 R, E19 W, E22 G | write | index | state |  | yes |
| S7 | Last edge program | `kb` | global | records S5 | E18 R | write | index | state |  |  |
| T1 | genl and genlCx relations | `taxonomy` | node | records M1 | E7 K, E8 K, E16 K, E17 R, E18 R | write | index | taxonomy |  |  |
| T2 | Flat declaration caches | `taxonomy` | value | records M1 | E8 K, E9 K, E17 R, E18 R | write | index | taxonomy |  |  |
| T3 | Equality partition | `taxonomy` | term | records M1 | E8 K, E11 K, E17 R, E18 R | write | index | taxonomy |  |  |
| T4 | Rewrite rules | `taxonomy` | handle | records M1 | E2 K, E3 K, E8 K, E17 R, E18 R | write | index | taxonomy |  |  |
| T5 | Taxonomy closures | `taxonomy` | node | T1 M1 | E7 G, E8 G, E17 W, E21 W, every other event G* | read | cache | no | `:taxonomy-closures` |  |
| T7 | Closure filter memo | `taxonomy` | context | T1 M1 index records | E17 W, every other event G* | read | cache | no |  |  |
| T10 | Taxonomy pass caches | `taxonomy` | node | T1 M1 index records | P | pass | pass | no |  |  |
| T11 | Taxonomy supporters | `taxonomy` | value | index | E7 K, E8 K, E9 K, E17 W, E21 W | read | cache | no | `:taxonomy-supporters` |  |
| T12 | Supporter reach memo | `kb` | value | index justifications | E1 G, E3 G, E4 G, E5 K, E6 K, E16 K, E17 R, E18 R | read | cache | no |  |  |
| M1 | Labels | `jtms` | handle | justifications | E5 K, E10 K, E17 R, E18 R | write | index | network |  |  |
| M2 | Touched set | `jtms` | handle | M1 | E5 K, E10 K, E16 W, E17 W | write | journal | no |  |  |
| M3 | Belief hold | `jtms` | global | M1 | E6 K | settle | index | no |  |  |
| M4 | Justification dedup | `jtms` | handle | justifications | E5 W | pass | pass | no | `:justification-dedup` |  |
| J1 | Candidate journal | `decide` | handle | N1 N5 | E1 K, E3 K, E4 K, E7 K, E8 K, E9 K, E15 K, E17 R, E18 R, E22 K | write | journal | no |  |  |
| J2 | Candidates by context | `decide` | context | J1 N1 | E1 K, E3 K, E4 K, E8 K, E15 K, E17 R, E18 R | read | cache | no |  |  |
| J4 | Flat context moves | `taxonomy` | value | T2 | E8 K, E9 K, E17 R | write | journal | no |  |  |
| J5 | Relation moves | `taxonomy` | node | T1 | E7 K, E8 K, E17 R, E18 R | write | journal | taxonomy |  |  |
| J6 | Placement edge cursor | `decide` | global | J5 | E17 R, E18 R, E22 Q | settle | counter | state |  |  |
| N1 | Converse candidates | `decide.tuple` | handle | index records T2 | E1 K, E3 K, E4 K, E7 K, E9 K, E17 R, E18 R | write | cache | state |  |  |
| N2 | Tuple mark candidates | `decide.tuple` | value | index records T1 T2 | E1 K, E3 K, E4 K, E7 G, E8 G, E9 K, E17 R, E18 R, E22 G | read | cache | state |  |  |
| N3 | Arity inert shapes | `decide.arity` | functor | index records M1 T1 J5 N8 | E1 K, E3 K, E5 K, E7 G, E8 G, E17 R, E18 R, E22 Q | write | cache | state |  |  |
| N5 | Membership candidates | `decide.membership` | term | index records T1 T2 J5 | E1 K, E3 K, E4 K, E7 K, E8 K, E9 S, E17 R, E18 R, E22 K | read | cache | state |  |  |
| N6 | Related declaration candidates | `decide.related` | handle | index records T1 J5 | E1 K, E3 K, E4 K, E7 K, E8 K, E9 K, E17 R, E18 R, E22 K | read | cache | state |  |  |
| N7 | Inherited clashes | `decide.inherited` | value | D3 | E15 W, E17 R, E18 R | settle | index | state |  |  |
| N8 | Arity lengths | `decide.arity` | functor | index records T1 J5 | E1 K, E3 K, E7 K, E8 K, E17 W, E21 W, E22 K | write | cache | no | `:arity-lengths` |  |
| N9 | Candidate recover memos | `decide.tuple` | functor | records | P | pass | pass | no |  |  |
| N10 | Argument holds | `decide.argument` | handle | index records M1 T1 J5 | E1 K, E3 K, E5 K, E7 G, E8 G, E17 R, E18 R, E22 Q | write | cache | state |  |  |
| X1 | Sync memo | `decide` | global | N1 T1 | E20 W, every other event I | read | cache | no |  |  |
| X3 | Change clock | `observe` | global |  | every event G* | write | counter | no |  |  |
| X4 | Declaration presence memo | `decide.argument` | global | T2 | every event I | read | cache | no |  |  |
| D3 | Preserved clashes | `discovery` | handle | index T1 Q2 Q3 J4 J6 M2 | E3 K, E15 K, E16 K, E17 R, E18 R, E22 K | settle | cache | state |  |  |
| Q1 | Exception re-check queue | `special` | handle | records | E17 R, E18 R, E22 Q | write | queue | state |  |  |
| Q2 | Supersession moves | `special` | value | Q5 M1 | E16 Q, E17 R, E18 R, E19 W | write | queue | state |  |  |
| Q3 | Except moves | `special` | handle | index T1 | E5 K, E16 Q, E17 W, E22 Q | write | queue | no |  |  |
| Q4 | Respell queue | `special` | functor | index | E6 Q, E17 W | write | queue | no |  |  |
| Q5 | Equality moves | `taxonomy` | term | T3 | E8 K, E11 K, E16 Q, E17 R, E18 R, E22 Q | write | queue | taxonomy |  |  |
| Q6 | Feed accumulator | `feed` | handle | M2 | E16 Q, E17 Q | settle | queue | no |  |  |
| Q7 | Negation placement queue | `decide.negation` | literal | records index | E3 K, E17 R, E18 R, E22 Q | write | queue | state |  |  |
| Q8 | Mint departures | `special` | handle | records | E17 W, E19 W, E22 Q | write | queue | no |  |  |
| Q9 | Unpremised mints | `special` | handle | records | E17 W, E19 W, E22 Q | write | queue | no |  |  |
| Q10 | Owed mint releases | `special` | handle | records Q8 | E18 R, E19 W | write | queue | state |  |  |
| R1 | Literal matches | `literal-cache` | literal | index M1 T1 | E21 W, every other event G* | read | cache | no | `:literal-matches` |  |
| R2 | Closure answers | `provers` | node | index M1 | E21 W, every other event G* | read | cache | no | `:closure-answers` |  |
| R3 | Resident derived values | `observe` | context | index M1 | E19 W, E21 W, every other event G* | read | cache | no | `:resident` |  |
| R4 | QCN join baselines and settled passes | `qcn-kb` | context | R3 M1 records | E19 W | write | cache | no |  |  |
| R5 | Inherit question memo | `inherit` | value | index T1 | P | pass | pass | no |  |  |
| R6 | Preservation crossing reads | `inherit` | global | index records | E1 I, E3 I, E4 I, E17 W, E21 W | read | cache | no | `:preservation-crossing` |  |
| R7 | Search-step memos | `observe` | node | index M1 | P | pass | pass | no | `:closure-neighbours` |  |
| R8 | Stored handles | `observe` | literal | index records | E3 K, E4 K | pass | pass | no | `:stored-handles` |  |
| R9 | Rete alpha memories | `rete` | functor | records | E1 K, E3 K, E4 K, E17 R, E20 W, E21 W | write | cache | no | `:rete-alpha` |  |
| R10 | Hot records | `disk.record-store` | handle | records | E1 K, E3 K, E4 K, E19 W | read | cache | no | `:hot-records` |  |
| R11 | Chaining run memos | `chain` | value | index records | P | pass | pass | no |  |  |
| R12 | Call-scoped memos | `kb` | value | index T1 | P | pass | pass | no |  |  |
| R13 | Mapped index roots | `columnar` | value | index | E1 K, E3 K, E4 K | write | index | no |  |  |
| R14 | Write record | `observe` | value | records index M1 T1 J1 | P | pass | pass | no |  |  |
| K1 | Symbol pool | `sentex` | value |  | C | read | cache | no | `:symbol-pool` |  |
| K2 | Compiled algebras | `qcn` | value |  | C | read | cache | no | `:compiled-algebras` |  |
| K3 | Relation decode tables | `qcn` | value | K2 | E21 W | read | cache | no | `:relation-decode` |  |
| K4 | Path-consistency and support passes | `qcn-kb` | value |  | E21 W | read | cache | no | `:path-consistency` |  |
| K5 | Metric closures and reconstructions | `stp` | value |  | E21 W | read | cache | no | `:metric-closures` |  |
| K6 | Source parses | `source-identity` | value | source | E21 W | read | cache | no | `:source-parses` |  |
| K7 | Last source identity | `source-identity` | value | source K6 | C | read | cache | no |  |  |
| K8 | Storable classes | `checks` | value |  | C | read | cache | no |  |  |
| K9 | Foreign format scan | `foreign` | value | source | C | read | cache | no |  |  |
| K10 | Prover registry summary | `provers` | value |  | every event I | read | cache | no |  |  |
| K11 | Calculus registry memo | `qcn-kb` | value |  | every event I | read | cache | no |  |  |
| K12 | Built calculi | `qcn-kb` | value |  | C | read | cache | no |  |  |
| K13 | Mint rule handles | `special` | value | index | E1 W, E3 W, E17 W, E19 W | read | cache | no |  |  |
| K14 | Lazy-forward rule presence | `special` | value | index | E1 W, E3 W, E17 W, E19 W | read | cache | no |  |  |

| id | event | choke points | names | rows it retires |
|---|---|---|---|---|
| E1 | `stored` | `kb/create-sentex` | handle, sentence, context | T5 T7 T12 J1 J2 N1 N2 N3 N5 N6 N8 N10 X1 X3 X4 R1 R2 R3 R6 R9 R10 R13 K10 K11 K13 K14 |
| E2 | `integrated` | `special/integrate-sentex`, `special/derived-sentex-added`, `special/integrate-twin` | handle, functor | S5 T4 T5 T7 X1 X3 X4 R1 R2 R3 K10 K11 |
| E3 | `removed` | `integrate/sentex-removed!` | record, except target | S5 T4 T5 T7 T12 J1 J2 N1 N2 N3 N5 N6 N8 N10 X1 X3 X4 D3 Q7 R1 R2 R3 R6 R8 R9 R10 R13 K10 K11 K13 K14 |
| E4 | `respelled` | `kb/respell-sentex!` | old and new sentex, one handle | T5 T7 T12 J1 J2 N1 N2 N5 N6 X1 X3 X4 R1 R2 R3 R6 R8 R9 R10 R13 K10 K11 |
| E5 | `relabelled` | `jtms/supersede`, `jtms/ensure-node`, `jtms/add-premise`, `jtms/suspend-premise`, `jtms/add-justification`, `jtms/restrength-informant`, `jtms/set-forced`, `jtms/relabel`, `jtms/set-blocked`, `jtms/retract!`, `jtms/sweep!`, `jtms/drop-justification!` | the handles of the region, held in the network | T5 T7 T12 M1 M2 M4 N3 N10 X1 X3 X4 Q3 R1 R2 R3 K10 K11 |
| E6 | `held` | `settle/hold-belief!`, `settle/publish-belief!` | hold token | T5 T7 T12 M3 X1 X3 X4 Q4 R1 R2 R3 K10 K11 |
| E7 | `edge` | `taxonomy/add-genl`, `taxonomy/del-genl!`, `taxonomy/add-genlCx`, `taxonomy/del-genlCx!` | handle, edge, context | T1 T5 T7 T11 J1 J5 N1 N2 N3 N5 N6 N8 N10 X1 X3 X4 R1 R2 R3 K10 K11 |
| E8 | `edge-belief` | `special/reconcile-belief-change`, `taxonomy/refresh-beliefs` | moved handles, or nil for all | T1 T2 T3 T4 T5 T7 T11 J1 J2 J4 J5 N2 N3 N5 N6 N8 N10 X1 X3 X4 Q5 R1 R2 R3 K10 K11 |
| E9 | `declared` | `taxonomy/add-supported`, `taxonomy/del-supported!` | handle, [kind key], context | T2 T5 T7 T11 J1 J4 N1 N2 N5 N6 X1 X3 X4 R1 R2 R3 K10 K11 |
| E10 | `forced-monotonic` | `checks/force-reach!` | predicate | T5 T7 M1 M2 X1 X3 X4 R1 R2 R3 K10 K11 |
| E11 | `equality` | `taxonomy/add-equality`, `taxonomy/del-equality!` | handle, pair | T3 T5 T7 X1 X3 X4 Q5 R1 R2 R3 K10 K11 |
| E12 | `except` | `special/recheck-except` | except, target, context | T5 T7 X1 X3 X4 R1 R2 R3 K10 K11 |
| E13 | `rule-indexed` | `special/index-rule-sentex` | rule, antecedent predicates, context | T5 T7 X1 X3 X4 R1 R2 R3 K10 K11 |
| E14 | `recheck` | `special/mark-recheck` | rules; a trigger, :all or :all-rejoin | T5 T7 X1 X3 X4 R1 R2 R3 K10 K11 |
| E15 | `inherited` | `decide.inherited/install-inherited!`, `decide.inherited/update-inherited!` | clash rows | T5 T7 J1 J2 N7 X1 X3 X4 D3 R1 R2 R3 K10 K11 |
| E16 | `settle-exit` | `settle/settle-finish` | region | T1 T5 T7 T12 M2 X1 X3 X4 D3 Q2 Q3 Q5 Q6 R1 R2 R3 K10 K11 |
| E17 | `recover` | `recovery/recover-from-records`, `recovery/install-rebuilt!` | the whole store | S5 T1 T2 T3 T4 T5 T7 T11 T12 M1 M2 J1 J2 J4 J5 J6 N1 N2 N3 N5 N6 N7 N8 N10 X1 X3 X4 D3 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 R1 R2 R3 R6 R9 K10 K11 K13 K14 |
| E18 | `image-install` | `reasoning-image/install-from!` | the image | S5 S7 T1 T2 T3 T4 T5 T7 T12 M1 J1 J2 J5 J6 N1 N2 N3 N5 N6 N7 N10 X1 X3 X4 D3 Q1 Q2 Q5 Q7 Q10 R1 R2 R3 K10 K11 |
| E19 | `cleared` | `vaelii.core/clear!`, `reindex/reindex`, `io.import/clearing-on-refusal` | the stores, wiped | S5 T5 T7 X1 X3 X4 Q2 Q8 Q9 Q10 R1 R2 R3 R4 R10 K10 K11 K13 K14 |
| E20 | `closed` | `vaelii.core/close!` | the KB | T5 T7 X1 X3 X4 R1 R2 R3 R9 K10 K11 |
| E21 | `caches-cleared` | `caches/clear-caches`, `caches/shrink!` | the KB, or every live KB | T5 T7 T11 N8 X1 X3 X4 R1 R2 R3 R6 R9 K3 K4 K5 K6 K10 K11 |
| E22 | `settle-pass` | `settle/pass-work`, `settle/apply-pass!` | the region, the queues a pass drains | S5 T5 T7 J1 J6 N2 N3 N5 N6 N8 N10 X1 X3 X4 D3 Q1 Q3 Q5 Q7 Q8 Q9 R1 R2 R3 K10 K11 |

<!-- end of the generated register -->

## Counting the register

A row filled at a read keeps a **tally** beside the structure that holds its entries: in
the metadata of its atom (`caches/tallied`), or in a weighted LRU's own map. A KB's tally
therefore counts that KB's reads alone, and a structure made again (an open, the rebuild
a recover installs, a detached copy) counts from zero. The slots are `:hits`, `:misses`,
`:recompute-ns`, `:retired`, `:compared`, `:spurious` and `:evicted`. A hit and a miss
are one increment each. `:recompute-ns` is the time the misses spent recomputing, and it
includes the time of any row the recompute read in turn. `caches` reports a tally on the
cache row the derived row links to, and `(caches/derived-state kb)` reports it on every
row under `:tally`.

The rows with a tally are T5–T7 and R1–R3. The others have none, for one of four reasons:

- an `:index`, `:journal`, `:queue` or `:counter` row is kept at the write, so no read
  misses it; the same holds of R4 and R9, filled at the write;
- D3, J2, N2, N5, N6 and T11 are brought up to date in place, by a write, a settle or
  a read, rather than looked up and recomputed;
- K1–K12, R6 and X1 are held by the process, so one tally would count every KB's
  reads;
- R10 is the record store's own LRU, on the disk backends only.

The closure LRU also counts its builds and fallbacks on the `:taxonomy-closures` row: an
up-closure `reach-by-parents` built from its parents' closures, and one that fell back to
a walk because a cycle has no `:scc` entry or another thread evicted a parent between
the two reads of it.

### The event instrument

`caches/start-tally!` wraps every var `caches/events` names, reads every row of one KB at
each wrapped call's entry and exit, and charges the entries a row dropped or replaced
between two reads to the innermost event open then. It counts each event's firings and,
per event, the entries it retired of each row; `derived-state`'s `:events` carry
`:fired` and `:retired` while it runs, and each row's tally carries `:retired`.
`stop-tally!` restores the vars and answers the counts, and `with-tally` runs one
function under it. `derived_state_test` checks each row's `:retired-by` with the same
instrument. A move outside every event is a read's own refill and is not charged.

A row whose retired entries stay held until a read replaces them (R1–R3, keyed by the
change clock, and T5, keyed by a generation) declares `:live`, the number of its entries
current now. The instrument charges such a row the fall in `:live` across an event that
retires it, since a diff of its value would see nothing drop. Run without an `:observe`
callback, the instrument reads such a row's `:live` alone and not its value.

The instrument costs a read of every row per event, so it runs only when asked, one at a
time, over one KB. Its `:rows` option names the rows to read, for a KB whose rows are too
large to read at every event, and its `:events` option names the events to wrap. On the
full store a `genl` write fires the re-check event (E14) about 1.4 million times, so a
reading there leaves E14 out.

### Spurious misses

A **spurious miss** is a miss whose recompute returned the value the write retired: the
write retired an entry whose inputs it did not change. While the instrument runs, a miss
compares its recompute with the value it replaces, counts `:compared`, and counts
`:spurious` when the two are equal. The value at hand is the stale entry for a row that
keeps one (R1–R3, T7), the last value computed under
another key for a row keyed by one (T5), and for a row that drops its entries, the
value the instrument saw the event drop (`caches/compare-retired`). A kept value is its hash, and the
comparison is of hashes. Keeping the value itself holds every retired value reachable for
the instrument's run, and on the full store that took a 40 GB heap. With the instrument off, nothing is compared and no value is
kept. `:spurious` over `:compared` is a row's
spurious fraction, the measure of how coarse its retirement is. `caches/tally-ranking` orders the
counted rows two ways: by recompute time times spurious fraction, and by hit rate.

`clear-caches` with `{:counters? true}` zeroes the KB's tallies and lists them under
`:tallies-reset`.
