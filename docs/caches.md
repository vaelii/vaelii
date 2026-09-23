# What the process holds beside the stores

- **Covers:** the cache register (`vaelii.impl.caches`) — how a derived, droppable
  structure declares itself, what a descriptor says (`:scope` `:unit` `:limit`
  `:counters` `:note`), the one bound policy (wholesale clear, never eviction), the profile
  that scales every counted bound (`VAELII_CACHE_SCALE`, `cache-profile`,
  `set-cache-scale`, `set-cache-limit`), the memory-pressure guard that shrinks the caches
  under a filling heap and grows them back, the two reads `caches` / `clear-caches`, and a
  snapshot roster of every registered cache with its bound.
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
touched — is simply absent from the read, which is the honest answer rather than a row of
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
  which is not always what its `:entries` count. The literal cache is the awkward case —
  per-KB entries, process-wide `AtomicLong` counters — and conflating them would bill one
  KB for another's hits. The closure neighbours are awkward the other way: the counters
  are readable at any time and the entries only from inside the search step that holds
  them, so that row reports a rate against a blank count.
- **`:note`** — one line: what it holds and what retires an entry.

A row whose `:entries` is nil cannot be counted from outside — it is scope-bound, alive
for the length of one chaining run or one search step and garbage when it returns. It is
registered all the same, so the list is complete rather than merely finite.

## The bound: cleared wholesale, not evicted

A counted cache past its bound is dropped **whole** (`assoc-bounded`), not trimmed to the
one entry that would make room. Evicting exactly the right entry costs more bookkeeping
than the entry saves, and a cache that has outgrown its bound is one whose questions have
moved on. A nil bound is not unbounded neglect: those caches are retired by a **generation
bump** (a taxonomy edge or context change retires every closure read at once), by the
**change clock** (a per-placement stamp, so a chaining run meets its own reads cold), or
they are structural (the symbol pool, the compiled algebras) where dropping entries costs
the sharing they exist for.

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

Every counted bound in the roster below is a **shipped default** the process scales by one
number. At scale 1.0 — the default — a cache enforces exactly the roster's bound, so a
process that sets nothing holds the bounds it always did. `VAELII_CACHE_SCALE` sets the
scale a process starts with (default `1.0`, read as the engine loads): below 1 shrinks
every counted cache for a small heap, above 1 grows them for a bulk load. A per-cache floor
(`caches/min-limit`, 16 entries) keeps a small scale from taking a cache below the point
where the reads it serves are a fraction of the reads it forces to recompute.

On a running process the same dial is `vaelii.core`:

- `(cache-profile)` — the scale and any per-cache overrides in force.
- `(set-cache-scale x)` — multiply every counted bound by `x`, process-wide; `1.0` restores
  the shipped bounds. Refused when `x` is not a number 0 or more.
- `(set-cache-limit id n)` — pin one cache's bound to `n`, or clear the pin with `nil`. `id`
  is a `:cache` keyword from `caches`. The scale leaves a pinned bound alone, for a cache
  measured on its own. The memory-pressure guard does not: a pinned cache shrinks under a
  filling heap like every other counted cache, because the guard's relief has to reach every
  counted cache or a pin holds the heap short of the reclaim the guard exists to force.

## The memory-pressure guard

The scale is an operator's standing choice; the **pressure** is the engine's own response to
a heap filling under it. On the servers a post-collection listener reads how full the old
generation is after each garbage collection and moves a second multiplier, `:pressure`,
between two marks:

- over **0.85** it halves pressure and trims the counted caches down to the new, lower bound,
  so the next collection has something to reclaim;
- under **0.60** it raises pressure back toward the operator's scale, so a transient spike
  does not leave the caches small for the rest of the run.

Both multipliers apply: a cache's effective bound is `default × scale × pressure`, floored at
`min-limit`, and `cache-profile` shows both. A pinned cache's bound is `override × pressure`,
since a pin is set against the scale but not against the guard. The trim is **partial**, not a
wholesale clear
(`trim-map!`, or a cache's own shape-aware `:trim`): past the lowered bound a cache keeps that
many entries rather than none, so the reads the survivors serve are not all recomputed the
moment pressure passes. The pressure floor (0.125) keeps a heap under sustained pressure
holding a fraction of each cache rather than running every read cold.

The guard is the **servers'** — attached at startup (`caches/install-memory-guard!`, fed the
live KBs by the host's catalog) and by nothing at engine load, so a library embedding pays
for no listener it did not ask for. A JVM whose collectors emit no such notification, or names
no old-generation pool, keeps pressure at 1.0; the guard is a best-effort relief, not a
guarantee. The pure-heap caches are its charge — the disk hot-record cache stays on its own
`vaelii.disk.cache` cap, since its records are re-thawable from disk and its bound is set at
store open.

`caches` reports the effective bound each cache enforces, so the scale and the row never
disagree. Three bounds stand outside the scale: the **symbol pool**
(`*symbol-pool-limit*`), because its check runs per symbol interned — the hottest path on a
load — and scaling it risks the sharing it exists for; the **scoped-closure pass budget**
(`*scoped-memo-budget*`), a per-pass budget rather than a resident cache; and **hot
records**, whose per-kind LRU has its own knob (`vaelii.disk.cache`). The nil-bound caches
have no count to scale.

## Reading them

- `(caches kb)` — one row per registered cache: `:entries :limit :unit :hits :misses
  :hit-rate`, plus `:scope` / `:counters` / `:note`, and `:error` where a row's own read
  threw (one broken descriptor costs its row, not the answer). Each row is a count off a
  map the engine already holds, **O(1)**, so the page that shows it can poll.
- `(clear-caches kb)` — drop every cache that offers a clear and say what went. Bare, not
  `!`: every entry is derived and no belief moves, which makes a clear a *measuring
  instrument* — clear, ask the same question again, watch the miss the second ask no
  longer skips. Scoped to `kb`; `{:counters? true}` also zeroes the process-wide rates, in
  a call that says out loud it reaches past its argument.

Both are on the remote surface (`vaelii.host.serve`) and drive the browser's caches page.

## The roster (a snapshot — `caches` is the truth)

This list drifts; the register does not. Treat the table as orientation and
`(caches kb)` as authority. Presence depends on what is loaded: the qualitative caches
need the QCN/temporal reasoners, `hot-records` needs a disk-backed store.

**KB-scoped** — one set per KB:

| Cache | Unit | Bound | Retired by |
|---|---|---|---|
| Literal matches `:literal-matches` | literals | 4096 | wholesale clear; each entry clock-stamped, so any state change drops it |
| Taxonomy closures `:taxonomy-closures` | reach sets | — | taxonomy generation bump |
| Taxonomy closures, scoped `:taxonomy-scoped-closures` | visibility sets | 128 / relation | flush past budget, or generation bump |
| Taxonomy visibility sets `:taxonomy-visibility` | relation/context pairs | — | generation bump |
| Closure answers `:closure-answers` | closures | 100 000 members | wholesale drop; a single reach past the bound is never stored |
| Resident derived values `:resident` | networks & passes | 256 | wholesale clear |
| Hot records `:hot-records` | records | 65 536 / kind | per-kind LRU (`vaelii.disk.cache`, 0 disables); disk stores only |

**Process-scoped** — shared by every KB in the JVM:

| Cache | Unit | Bound | Retired by |
|---|---|---|---|
| Symbol pool `:symbol-pool` | symbols | 1 000 000 | the older of two generations dropped at half the bound |
| Relation decode tables `:relation-decode` | masks | 8192 | wholesale clear |
| Compiled algebras `:compiled-algebras` | algebras | 64 | wholesale clear |
| Path-consistency passes `:path-consistency` | networks | 256 | wholesale clear |
| Network support passes `:network-support` | networks | 256 | wholesale clear |
| Metric closures `:metric-closures` | networks | 256 | wholesale clear |
| Metric path reconstructions `:metric-reconstructions` | networks | 256 | wholesale clear |
| Stored handles `:stored-handles` | sentences | — | structural |
| Closure neighbours `:closure-neighbours` | neighbour sets | — | structural |
| Pinned values `:pinned-values` | resident values | — | structural |
| Justification dedup `:justification-dedup` | conclusions | — | structural |
| Source parses `:source-parses` | source files | 1024 | wholesale clear; an entry is re-read when its file's modification time or length changes |
| Preservation crossing reads `:preservation-crossing` | KBs | 64 | wholesale clear; an entry's parts are re-read when the `:preserving` roster or a permuting mark's posting moves |

The units do not sum: twenty rows counting twenty different things. A total across
them is a number of nothing.
