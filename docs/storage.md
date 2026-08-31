# Storage

- **Covers:** the `RecordStore` / `IndexStore` protocols and the optional `Prefetching`,
  `Tallying`, `BulkLoading` and `BulkAnnotating` capabilities, what the three enumerations promise and what a
  roster costs per handle, the sink an `import!` writes its records through, the seven legal record×index backend pairings and the optional `:sqlite` and
  `:pg` records adapters, nippy serialization, what one fact of a bulk load costs phase by
  phase, and the single-writer contract.
- **Not here:** the six index families' key layout and retrieval →
  [indexing.md](indexing.md); the dense/columnar backends that replace the default
  map-based structures → [density.md](density.md).
- **Assumes:** sentex, handle, record store, index store → [glossary.md](glossary.md).

`vaelii.impl.protocols` (the declarations), `vaelii.impl.capabilities` (the fallbacks
that go with the optional ones), `vaelii.impl.kv`, `vaelii.impl.memory`,
`vaelii.impl.disk.*`.

## Protocols

Two protocols keep the reasoning code independent of any backend:

- `RecordStore` — canonical sentexes and justifications, keyed by integer handle:
  `put-sentex`, `get-sentex`, `delete-sentex!`, `put-justification`, `get-justification`,
  `delete-justification!`, `next-id`, the provenance triple, premise tracking, and
  `clear-records!` (the whole-db wipe). Both puts honour an `:id` on the record they are
  given — that is how an import lands records at the handles a dump gave them — and
  `next-id` is required to stay above every handle the store holds however it arrived.
  A handle is an identity, so no store may issue one twice. Both backends allocate from
  a counter of their own rather than from a field of the record map, and both lift it
  clear of an explicit `:id` as the record lands: one handle is minted per stored sentex
  and per justification, and forward chaining takes one per firing
  ([inference.md](inference.md)), so the allocation is a compare-and-set on a `Long`
  and not on the store.
- `IndexStore` — the trie, the secondary roots, the rule index, the exception index,
  and the term index (see [indexing.md](indexing.md)), plus `clear-index!` (the
  whole-db wipe `reindex` rebuilds from) and `index-entries` / `index-load`, the
  `[structured-key value]` projection all four index backends share — what a dump
  writes, and why an index written by one loads into another.

**The three record fetches are counted.** `get-sentex`, `get-justification` and
`get-provenance` each tally against their kind through `vaelii.impl.profile`'s
`:fetches` — the record-store twin of the `:reads` tally the index keeps, and its own
number because the two move independently. The worked case is `kb/find-sentex-handle`,
which asks the trie where one sentence is stored. Asked with `p/lookup`, a variable in the
path is a **wildcard**: the walk fans over every stored sentex of the same shape and the
caller reads the record behind each to find the one that is actually this sentence — one
index read by `:reads`, unimpeachable, and a few milliseconds per call at 800 candidates.
`p/leaf-at` is the exact read that answers the same question in one, at ~10 µs and no
record read at all, and the `:reads` count is identical either way. On the durable store
each of those
fetches is a positional slot read, a positional frame read and a nippy thaw past the LRU —
orders above what any index read costs. `test/vaelii/record_fetch_cost_test.clj` is the
gate: a non-ground `handle-of` must fetch **no** records, whatever the extent of the
pattern's shape.

The tally sits on the protocol method rather than inside a backend's own fetch, so it
counts what a caller asked for and not what a backend does to answer: the durable store
re-reads a record inside `mark-premise` where the RAM one reaches into its state map, and
a number covering both would be a reading of which backend is running. An overlay fetch
that consults the base and then the fork counts twice, which is what a fork costs.

A `KB` record bundles the two stores with the thirty-odd other slots the engine hangs off
one value — the prover registry, the solver, the contradiction and violation bookkeeping,
the settle and chain statistics, the resident qualitative networks, the match and naming
caches, the feed. **The engine programs against these protocols and never against a
concrete backend**, so a KB built on any store runs the whole engine unchanged. Records
are in-memory (default) or on-disk; the index has four representations, and the pairings
are below.

## Two stores

| Store | Holds | Standing |
|-------|-------|----------|
| record store | sentexes + justifications (values); a per-handle provenance map | the ground truth |
| index store  | trie, rule index, term index (keys → sets/counts) | derived from the records |

The index is a cache over the records — every entry is recomputable, so
`reindex` throws the whole thing away and rebuilds it from the records — while the
records are what has to survive: lose one and the knowledge is gone. That asymmetry is
why the two are separate stores behind separate protocols rather than one — [why
separate stores](defenses.md#records-and-the-index-are-separate-stores).

That also sets what each backend owes. A record backend must persist; an index backend
need not. Every index representation is resident in RAM, and the log under `:disk-log`
buys a **fast restart** rather than a smaller one: it replays into the same key→value map
`:memory` holds, so nothing is reindexed on open and nothing leaves the heap. The one
exception is the `:disk-columnar` image ("The image", below), which is off by default and
`mmap`s the leaf handles and the routed roots' postings rather than reading them onto the
heap.

One space number (`:space`, default 0) namespaces both stores so several KBs coexist in
one process; each backend uses it as it sees fit — the memory backend keys its registry
by number, the disk backend derives a directory from it. **One number, not one per
axis**: the index is a function of the records, so the two are shared or separate as one
thing, and each backend keys a registry of its own, so no KB can be given a private
index over records it shares.

**A second in-RAM KB defaulting onto space 0 warns**, because both readings are
legitimate and nothing else could tell them apart. `(open-kb {})` twice in one process is
one set of records behind two KB values: the second recovers the first's facts, and from
then on a write through either is invisible to the other, since belief is per-KB and only
the writer's is relabelled. That is also the REPL's ordinary gesture for starting clean.
So the second such open logs a `:warn` naming both fixes — give the KB its own number
(`{:space 2}`), or name `{:space 0}` explicitly to say the sharing is meant and silence
it. A warning rather than a refusal: sharing the space is how `recover` sees the same
records, how the fixtures rebuild over one store, and how a base is mounted. In-RAM
records only — a `:disk` KB is keyed by directory and takes a lock.

**An option `open-kb` does not read is refused, not ignored** (`:type
:unknown-option`), and the space number is why. Every other opt fails loudly when it
is wrong — an unknown `:backend` throws, an impossible axis pair throws, and so does
an unknown `:records` / `:index` / `:tms` kind, all four as `:type :unknown-backend`
([troubleshooting.md](troubleshooting.md#open-kb-refuses-an-unknown-backend) says which
`ex-data` key tells them apart) — but a
*misspelt* one is a key nothing looks at, so the KB opens on the default space and reads
and writes there in silence. Two KBs a caller built to keep apart then share one store:
each one's flush empties the other, and the second reads out of records the first
cleared. Downstream, a KB that took the default is indistinguishable from one that asked
for it, so the mistake is only legible in the opts map itself. `kb/opt-keys` is the set,
and a fork's `:base` and `:overlay` maps are held to it too.

### `Prefetching` — the optional hint

A store whose fetch is expensive enough to be worth avoiding may implement `Prefetching`:
`prefetch-sentexes!` and `prefetch-justifications!`, one per record kind. A caller hands it
the handles it is about to walk,
a chunk at a time, and the store may warm whatever cache it keeps.

**It is a hint and never an answer.** It returns nothing, every record still arrives
through `get-sentex`, and a store that ignores it entirely answers the same query the same
way. That is what makes it safe to leave in the walk: a batched read *returning* records
would have to be proven equal to the per-handle loop on every implementation, and a cache
warmed ahead of that loop is equal to it by construction.

None of the engine's own stores implement it — a record fetch on the RAM and disk backends
is a page touch, and there is nothing a batch could save — so `capabilities/prefetcher`
answers `nil` for them and the retrieval paths run the loop they always ran. The
[Postgres records](#postgres-records-pg-memory-pg-disk-log) adapter implements it, where a
fetch is a network round trip.

The caller's half is `resolution/*prefetch-candidates*`: the chunk size, **`false` by
default**, so no hint is issued at all unless something asks for one. It takes a positive
chunk size or `false` and refuses anything else at the `binding` form — `true` above all,
which is what an off-value of `false` invites and which is truthy enough to reach the
chunk arithmetic before it fails. Both retrieval paths
wrap their candidates in it — the set-algebra path that answers a positive literal by
default, and the `match-one` fan-out behind it — since a hint given to only one of them is
a hint the ordinary query does not get.

**The recovery walks hint unconditionally, and have no setting.** `reindex` fetches every
live record and `recover` every stored justification; both consume every handle they are
given, so a hint there can only save round trips and can never waste one. The query path's
setting exists because a consumer that stops early has over-fetched a chunk — a trade a
recovery walk does not make. `capabilities/recovery-hint-chunk` is the size.

### The enumerations, and what a roster costs

`sentex-ids`, `justification-ids` and `premise-ids` answer **a `java.util.Set` of
handles** — and the gap between that and *a Clojure set of handles* is the whole of what a
store may decide for itself. What the seam promises is what the engine does to them:
`contains?`, `count`, `seq`, `sort`, and `=` against another set. `conj`, `disj` and
`clojure.set` are not on the list, so a caller wanting those converts with `(set …)` and
the copy is paid at the call site that asked for it — [why a Set, not a Clojure
set](defenses.md#the-enumerations-promise-a-set-not-a-clojure-set).

`vaelii.impl.roster` is the substitution that licence exists for: the same handles as a
`Roaring64Bitmap` behind a `java.util.Set`, at a fraction of a `PersistentHashSet<Long>`'s
residency. It is a `java.util.Set` precisely so that no caller can tell the difference,
and `enumeration_shape_test` is where core proves it: one session run
against a store answering rosters and one answering Clojure sets, compared at the KB level
— beliefs, answers, `reindex`, `recover`, `export!` — rather than at the protocol call.

**The engine's own stores answer Clojure sets**, because that is what most of their own
state already is — the memory store's key set, the disk store's premise set. What each
*holds* is a separate question from what it answers, and the disk store's live-handle sets
are the one place the two come apart.

**The disk store holds its live handles as compressed bitmaps.** One per kind — sentexes,
justifications, provenance — resident for as long as the store is open, and the four
things they are asked are the four a bitmap answers directly: membership (`kill!`),
iteration (`sentex-ids`), cardinality (`sentex-tally`) and a first handle (`a-sentex-id`).
As a `PersistentHashSet<Long>` those sets retain **48–75 bytes a handle** (measured with
jol; the hash trie's fill varies with cardinality), which `lein bench-budget` carries to
**9.47 GB at 100M sentexes and j/n 1.1** — the second-largest resident row in the engine,
before a single record is fetched. The same handles as a `Roaring64Bitmap` measure
**33.0 MB**, still linear across both of the bench's steps
([density.md](density.md#the-budget-at-100m)). It is the shape the allocation gives them:
`next-id` mints in assertion order, so a kind's live set is a strided run through the
handle space with holes where records were deleted.

`sentex-ids` still hands back a `PersistentHashSet<Long>`, built from a snapshot at the
call — so no caller can tell, and the *call* still allocates the extent even though
holding it no longer does. That allocation is the door's, not the store's.

The bitmap is mutated in place and is not thread-safe, so **a read of the live set takes
the kind lock**, which the boxed set did not need. That is the whole price: a tally and a
first handle are O(1) under a monitor the writer holds only for two file writes, and a
read that hands the set onward takes a snapshot inside the lock — a bitmap copy, costing
the roster's size rather than the corpus's. Left unsynchronized the failure is real and
measured, not theoretical: an iterator over a bitmap being written throws
`ArrayIndexOutOfBoundsException` once the handle space is spread widely enough for the ART
trie to restructure under it, which a store whose handles interleave with two other kinds'
is (`disk_record_store_test`, the live roster beside a writer).

The premise set is still a `PersistentHashSet<Long>` and still resident, and it needs
neither monitor on the write path — one `swap!` on one atom, and the pair that matters is
a `kill!` the writer makes on the thread that reads it back.

### `Tallying` — the questions that do not need the roster

`(count (sentex-ids store))` is how the engine asks *how many records is this*, and
`(first (sentex-ids store))` how it asks *does this store hold anything*. On a store whose
enumeration is a read of its own state, both cost nothing. On one whose enumeration is a
**query** they cost the whole table — every handle over the wire and a roster built out of
it, to answer with one number — and `open-kb` asks them before the KB has answered
anything: the durable index's coverage gate counts the records, and the recovery branch
asks whether there are any.

So a store that can answer without enumerating implements `Tallying` — `sentex-tally`,
`justification-tally`, and the three `a-…-id` samplers — and every caller goes through
`capabilities/count-sentexes`, `count-justifications`, `some-sentex-id`,
`some-justification-id` and `some-premise-id`, which **fall back to the enumeration**. A
store without the capability therefore reads exactly as it did before the capability
existed, which is what lets the engine call the helpers unconditionally.

Only the questions the engine actually asks are on the seam — there is no premise tally and
no general sampler — so an implementer knows each op there is worth a statement. *Which*
handle a sampler returns is the store's own choice: every caller either tests it for nil or
reads the record to prove the build can read records at all, and none depends on which one
came back.

### `BulkLoading` — the seam an import writes its records through

A record at a time is the wrong unit for a corpus. `import!` reads a dump frame by frame,
and a frame stored one at a time is one `put-sentex` — a map assoc on the RAM store, a WAL
append on `:disk`, and a **round trip** on a store across a socket. So the third optional
capability is a bulk write: `open-sentex-sink` / `open-justification-sink`, each answering
a `RecordSink` a loader writes a stream of records to and then closes.

**It is a sink and not a batched put, and the difference is the handle.** The handle is
decided caller-side — a dump's own `:id`, or one minted from `next-id` — and the sink is
told rather than asked, which is also what lets a dump's numbering survive a bulk load.
The import path is why: it indexes each record from the copy already in hand rather than
reading it back, so it needs the handle *now* — [why a sink, not a batched
put](defenses.md#the-bulk-seam-is-a-sink-not-a-batched-put).

The one restriction that buys this: **do not read a record back before the sink is
closed.** A sink may hold everything it was given until then. Neither import path does,
which is asserted rather than commented — the test wrapper's `get-sentex` throws on a
handle a sink still holds.

`capabilities/sentex-sink` and `justification-sink` are the callers' door, and they fall back
the way `Tallying`'s helpers do: a store with no capability gets a sink that is
`put-sentex` per record plus the premise mark, which is the loop the import paths ran
before. `{:premises? bool}` is the one option — whether a record carrying a `:strength` is
rostered a premise by the write. The records-only pass marks inline and says true; the
belief pass says false, because there the mark is an **aggregate** (dump ids that collapse
onto one handle keep the strongest strength, where the record carries the first frame's)
and only the whole stream decides it.

### `BulkAnnotating` — the two writes that follow a record

The premise mark and the provenance map are per-handle writes that come **after** the
record, and the import path makes both in a loop. Neither can ride the record write:
which strength a handle ends at is decided only once the whole sentex stream is read (a
dump id that collapses onto a stored handle keeps the strongest), and the provenance
stream is a separate file read after the records. So on a store where a write is a round
trip they are `n` round trips each — 20,000 of them on a 10,000-record belief import,
against roughly two-thirds of a second for the records themselves.

`mark-premise-batch` and `put-provenance-batch` are the seam, and
`capabilities/mark-premises` / `put-all-provenance` are the callers' door with the same
fallback: the loop, on a store that implements nothing. It is a **separate protocol from
`BulkLoading`** rather than two more ops in it, because a store may be able to load
records in bulk without being able to bulk-update rows that are already there, and a
half-implemented protocol fails at the call rather than at the `satisfies?`.

Neither op changes what the per-handle version does. A handle with no sentex is still not
marked — over Postgres the batch statement `RETURNING`s the ids it actually touched, since
an update count over a batch cannot say *which* rows matched and a strength cache filled
past that would answer for a handle `premise-ids` does not name.

Measured through `import!` — not through a store directly — on `{:belief? false}`, a dump
of monotonic ground facts:

| records/s | 10k corpus | 30k corpus |
|---|---|---|
| `:pg-memory`, a put per record | 2,348 | 2,784 |
| `:pg-memory`, through the sink (`COPY`) | **13,993** | **17,882** |
| `:sqlite`, a put per record | 7,516 | 7,444 |
| `:sqlite`, through the sink (one transaction per batch) | **13,729** | **16,572** |
| `:disk-log` | 6,514 | 6,790 |

One run per cell on a cold JVM, so read the column against itself rather than as an
absolute. The two A/B figures below are medians of three interleaved runs with the
capability hidden and present, which is the comparison that holds still.

The `:disk` record store answers a sink too, and the same measurement isolated to it —
`:disk-memory`, so the durable index is not in the way — is **14,987 → 18,986 records/s**,
+27%. `:disk-log` gains little, because with the durable index its bulk load is
dominated by the index writes rather than by the records; that is the ceiling the next
section is about, not this one.

**6.4× over a server and 2.2× over SQLite, and the store stopped being what costs.** The
two adapters converge on ~17k/s because what remains is the engine's own per-frame work —
decoding the frame, re-canonicalizing the sentence, the naming tally, the fingerprint and
the inline index build — and a `copy-sentexes!` handed records directly runs at 122.6k/s
against that. A server-backed load is now **faster than the local disk backend**, which is
the sentence that was not true before.

The belief path (`{:belief? :stored}`) is the same dump with the marks and the provenance
on top, and it is `BulkAnnotating` that carries those: **3,038 → 10,343 records/s** over
Postgres on the 10k corpus — 3.4×, one statement for every premise mark and one per 1,000
provenance maps in place of 20,000 round trips. What remains there is the index rebuild,
which is the next section's subject.

## Backend selection: two independent axes

The asymmetry above is a **selection** axis, not only a design note. The records answer
to durability and the index to representation, so `open-kb` chooses them separately —
`:records` (`:memory` / `:disk`, and the adapter axes `:sqlite` / `:pg`) and `:index`
(`:memory` / `:dense` / `:columnar` / `:snapshot` / `:disk-log`) — and `:backend` is sugar
naming a pair, spelled **`<records>-<index>`**.
`vaelii.impl.kb` is the only place a concrete store is named (`record-store-for` /
`index-store-for`); everything above reads the protocols.

| `:backend` | records | index | |
|---|---|---|---|
| `:memory` (default) | RAM | RAM map | one store on both axes |
| `:memory-dense` | RAM | int postings | [density.md](density.md) Phase 1 |
| `:memory-columnar` | RAM | native int-token trie | [density.md](density.md) Phase 2 |
| `:disk-memory` | durable | RAM map | rebuilt on open |
| `:disk-dense` | durable | int postings | rebuilt on open |
| `:disk-columnar` | durable | native trie | rebuilt on open |
| `:disk-snapshot` | durable | native trie, **mapped from an image** | the same trie, read back instead of rebuilt |
| `:disk-log` | durable | durable | the index is a RAM map with a write-ahead log under it |
| `:sqlite` | durable (SQLite file) | RAM map | an Apache adapter, resolved lazily — below |
| `:pg-memory` | durable (Postgres) | RAM map | an Apache adapter — rebuilt on open, every open |
| `:pg-disk-log` | durable (Postgres) | durable, **local** | the index files belong to the writer's host, not to the KB |
| `:overlay` | a decorator | a decorator | a fork over a frozen base — [overlay.md](overlay.md) |

`:memory` is the one pair that is the same store on both axes, named for the store rather
than doubled into `:memory-memory`. `:disk-log` names its two halves separately because
they are two different things: durable records that genuinely page, under an index whose
map is in RAM and whose log buys the restart.

- **Memory records** (`vaelii.impl.memory`) — plain Clojure maps in atoms, **no
  serialization** (records held directly, structured key vectors used as map keys). They
  have **space-number sharing**: a process-global registry keyed by `:space`
  means two KBs constructed over the same number share one store, so a restarted KB
  (`recover`) sees the records the first wrote — the persistence tests' contract.
  Durable within a JVM, not across a process restart.
- **Disk records** (`vaelii.impl.disk.record-store`) — an on-disk log-structured store in a directory
  (`:dir`, or derived from the space number). Durable across a process restart and
  crash-safe, with no server. Selected for the whole suite with
  `VAELII_TEST_BACKEND=disk-log lein test` (durability parity gate: identical results).
  Detailed below.
- **SQLite records** (`com.vaelii/sqlite`, the `vaelii.sqlite.record-store` adapter) — an
  embedded-SQLite store in a single file (`<dir>/records.sqlite`) under `:dir`, durable
  across a restart with no server. It is **not built into the engine**: `record-store-for`
  resolves it lazily (`requiring-resolve`, the way `create-tms` reaches the dense TMS), so
  the SSPL engine carries no JDBC dependency, and the `:sqlite` backend works only when the
  Apache-2.0 adapter is on the classpath. It pairs with a derived RAM index (the `:sqlite`
  sugar is `{:records :sqlite :index :memory}`), rebuilt on open; a `:disk-log` index
  over it is refused, the same rule RAM records meet. Outside the built-in grid below — not
  one of the eight pairings, and the adapter carries its own suite.
- **Postgres records** (`com.vaelii/postgres`, the `vaelii.postgres.record-store`
  adapter) — the records in a database an operator already runs, named by the `:pg` opt
  (a next.jdbc db-spec or a JDBC URL, with an optional `:schema` so one database holds
  several KBs). Resolved lazily exactly as `:sqlite` is, so the SSPL engine carries no
  JDBC dependency. What a server buys and what it does not is
  [below](#postgres-records-pg-memory-pg-disk-log); the short version is that it buys `COPY`,
  an operator's existing backup and replication, and a store bigger than one disk — and
  it does **not** buy a shared KB. Outside the built-in grid below, as `:sqlite` is: the
  adapter carries its own suite, `VAELII_TEST_BACKEND` does not name it, and
  `backend_parity_test`'s "identical across every pair" is a claim about the pairs that
  run by default and not about this one — a backend whose tests need a server is covered
  by the adapter's own run against one, not by the matrix.
- **A derived index** — the RAM map, the dense postings, the columnar trie — holds
  nothing that is not recomputable, so it is never written. Over durable records that
  costs one `reindex` per open (below); in exchange, every density experiment can be run
  against a durable KB instead of only in RAM.

The two built-in axes admit eight pairings and **seven are legal**, each with a name:
RAM records under the durable index is refused — [why that pairing is
refused](defenses.md#ram-records-under-a-durable-index-is-refused). The rule the refusal
states is that **the `:disk-log` index needs durable records**, which is why `:pg`
may take it (`:pg-disk-log`) and `:sqlite` may not: `:sqlite` records already live in a
directory, so a durable index beside them is `:disk-log`'s pairing without its shared
lifecycle, and `:disk-log` is the name for that. So `:records` /
`:index` are for overriding *half* of a name, not for reaching a pair the table left out,
and `VAELII_TEST_BACKEND` takes a name. `./scripts/test-backends.sh` (`lein
test-backends`) runs the whole suite on all seven, one log and one ✔/✘ per run, plus an
eighth over the `overlay` decorator; `./scripts/test-matrix.sh` runs those eight and the
six sweeps concurrently, which is the same coverage in a fraction of the wall
clock, since a durable run's store is `<vaelii.disk.dir>/space-<n>` and each gets its
own directory. A bare matrix run is the **routine** roster, which stands two of the
three durable-records-with-a-derived-index pairs down — one claim written three times,
and `mixed_backend_test` holds the seam in an ordinary `lein test` — and `full` is all
fourteen. `./scripts/test-matrix.sh --owed` runs what the changed files owe and prints
why, from the map in `scripts/lib/suite-configs.sh`. `backend_parity_test` also runs one scripted KB
session across every pair in an ordinary `lein test`, so a divergence fails without
anyone remembering to.

`:overlay` is the one selection that is not a store: it is a **decorator** over whatever
each axis resolved to, naming its frozen base with `:base` and its own writable half with
`:overlay` — the fork of [overlay.md](overlay.md), of which `core/fork` is the ergonomic
spelling.

### A derived index over durable records (`:disk-memory`, `:disk-dense`, `:disk-columnar`)

The records open populated and the index opens empty, so such a KB needs its index
rebuilt before it can answer anything. `recover` alone is **not** that: it rebuilds the
TMS and taxonomy *by reading the index* (`special/rebuild-taxonomy` reads the functor
root), so over an empty one it would recover an empty KB and report nothing wrong. The
repair is `reindex` — rebuild the index from the records, *then* recover — and
`{:recover? :auto}`, the default, runs it and logs how long it took.

That log line is the point of interest: the rebuild is O(records) on **every** open, so
whether it is worth buying back — by persisting a snapshot of the derived index, which
is what `:disk-columnar`'s image below does — is decided by that number at the corpus
size in question. `lein bench-reindex [facts] [rules] [index] [tms]` produces it. Measured on a generated corpus of **105,392 records**, single-threaded:

| index | reindex | records/s | recover | open | extrapolated to 100M |
|---|---|---|---|---|---|
| `:memory` | 2.7 s | 39k | 2.6 s | 5.3 s | ~84 min |
| `:columnar` | 1.7 s | 61k | 2.6 s | 4.3 s | ~68 min |

Only the first column is the price of a derived index: the `recover` half is the TMS and
taxonomy rebuild every durable KB already pays, and it dominates at this scale. So the
open cost of *not* persisting the index is roughly 2× a durable-index open.

#### And until it is rebuilt, the KB does not accept writes

`{:recover? false}` over such a store is a legitimate thing to want — it is how a corpus
past what `recover` scales to gets opened at all — but it leaves a KB that answers reads
out of the records and cannot correctly take a write. Two separate reasons, and the
distinction matters because they have different repairs:

- **No belief.** Every definitional check the assert door runs bottoms out in `jtms/in?`,
  so over an empty network they all match nothing and pass vacuously — and nothing
  re-runs them later, so the store keeps content its own constraints forbid. `recover` is
  the repair.
- **No index.** `assert` dedups through `p/leaf-at`. Over an index that opened empty every
  assert misses and mints a **second handle for a sentence already stored**, and
  `reindex` cannot merge the two afterwards because they are two records rather than two
  index entries. `reindex` is the repair, and `recover` alone is not — it reads the index
  rather than writing it, which is the same reason it is not the repair for a read.

So the write doors — `assert`, `assert-inert`, `retract!`, `edit!`, `preview` — refuse
such a KB by name (`:unrecovered-kb`), reporting which of the two hold and naming the
call that clears them. The ex-data carries **`:hazards`**, a sorted vector of
`:no-belief` (the TMS is empty, so every definitional check passes vacuously) and
`:no-index` (the derived index opened empty, so dedup misses and every assert mints a
second handle for a sentence already stored), plus `:operation` and `:repair` — `recover`,
or `reindex` where the index is the empty one, which `recover` alone does not fix because
it reads the index rather than writing it. `check` and `check-edit` report the same
refusal as a problem, since they answer for the door.

`retract!` has two refusals of its own underneath that one, both about a handle the TMS
has no node for. A **stored premise** is not an inert sentex however alike they look to a
node test, and the dependency sweep a retraction owes cannot be computed over a network
that was never built (`:unrecovered-premise`). A **derived** record is the third case and
is told apart from neither: it carries no strength, so the premise roster does not name
it, while the store holds the justifications that concluded it and any naming it as an
antecedent — and the store keeps no index from a handle to the justifications citing it,
so nothing per-handle can separate it from an inert one. Where belief was never built the
teardown is therefore refused for every record (`:unrecovered-kb`); where it was built, a
record with no node genuinely is inert. `vaelii.core/*write-unrecovered?*` accepts the
first kind of write anyway for a caller who has read what it costs; nothing accepts the
teardown of a handle whose dependents cannot be computed. `*bulk-load?*` deliberately is
not that opt — it skips the dedup walk that is already missing.

`preview` refuses where `edit!` does, which is the point of it. It implements a `:remove`
as a premise suspension gated on `jtms/premise?`, false for every stored handle here, so
it reports that nothing would change while `edit!` on the same batch deletes the record —
a dry run silent about exactly the operation that cannot be taken back.

**What the two unrefused writes leave behind**, which is why they are refused rather than
warned about. A `retract!` deletes its record, reports `{:removed-sentexes 1}`, and leaves
every stored justification naming that handle as an antecedent pointing at nothing; a
re-`assert` of a stored sentence mints a second handle for it. The dangling justification
is the worse of the two, since `recover` skips one — so the loss reads as silent disbelief
rather than as a phantom, and neither is visible to a reader afterwards.

#### The image (`:disk-snapshot`)

`:index :snapshot` writes that rebuilt index to disk and **maps it back** instead of
recomputing it — `vaelii.impl.disk.index-snapshot`.

**It pairs with `:disk` records and with nothing else.** The stamp below is the *disk*
record store's slot fingerprint — a reading of its own slot files, taken under its own
kind locks, which no other record store keeps and the `RecordStore` seam has no method to
ask for. So `{:index :snapshot}` over `:memory`, `:sqlite` or `:pg` records is refused
with `:unknown-backend`, and records on a server take `:pg-disk-log` for a durable index
or `:pg-memory` and the rebuild.

**It is a representation, and it is not a promise that the image is valid.** Those are
two different things and the name carries only the first. What `{:backend
:disk-snapshot}` says is that this KB's index is meant to be read from bytes rather than
rebuilt — recorded in the opts map, where a reader of the KB's own configuration can see
it. What it does *not* say is that an image will be there: the stamp is checked on every
open, any doubt discards it, and the KB reindexes and answers correctly. The difference a
name makes is that such an open **warns**, naming the mismatch class, rather than passing
for a fast one that quietly took an hour.

The compacted trie's CSR arrays and the roots' packed postings are already flat `int`
runs, so the image is a write rather than a serialization. **Resident on open**: the CSR
skeleton, the roots' key and offset columns, the argument roots' scope table, the token
dictionary, and the fallback blob. **Mapped**: the leaf handles and the roots' handle run.
Every handle family routes, argument roots included ([indexing.md](indexing.md), §8).

**A write still thaws the mapped run into heap**, so this is a read-mostly backend: a KB
that writes steadily holds its index in heap between images, exactly as `:disk-columnar`
does, and the residency the image buys is a property of the read phase.

##### The cadence, and whose thread it runs on

The image is written when the directory closes, which a process killed outright never
reaches — so a writer that ran for weeks would reopen onto no image and pay the whole
`reindex` the backend exists to skip. The writer therefore refreshes it mid-life, when the
live index has drifted far enough from the one on disk: `vaelii.index.snapshot-drift`
(default 0.5), measured in **indexed roots** — the count now against the count the image
holds — and floored by `vaelii.disk.compact-min-interval-ms`, the same floor the record
store's compaction takes. A directory with no image drifts from zero, so its *first* image
is written mid-life rather than at a close it may never reach.

**Only `assert` reaches the cadence.** The gate hangs off the write door, so a store filled
by `reindex` or by the importer's inline bulk load — both of which post through
`reindex/index-one!` to `p/index-sentex` directly — never crosses it, and gets exactly one
image, at the close, whatever the threshold says. A batch build is therefore already on the
cadence it wants without asking for anything.

**And it can be declined.** `vaelii.disk.auto-compact=false` turns the mid-life refresh off
and leaves the image to the close and the shutdown hook: a refresh *is* an opportunistic
compaction of a derived structure — `save!` compacts the live trie to write it — so it
answers to the knob that already governs those rather than to one of its own. Note that
`vaelii.index.snapshot-drift` cannot say this: `0` is a *threshold*, so it means "any drift
at all" and is the most eager setting in the range rather than the off one.

**It runs on the writer's thread, and that is forced rather than chosen.** The record
store and the KV hand their compaction to `disk/durability.clj`'s daemon, which runs it on
a background executor; both are built around a monitor and can afford to. The columnar
index is not: its fields are `^:unsynchronized-mutable` because the walk reads them at
every frontier node, and its contract says the caller keeps its reads on the writer's
thread. Writing the image compacts the live trie in place, so queueing that onto the
daemon would mutate this index from a second thread. It is written by whoever writes the
index, or not at all.

The cost is a stall: a refresh is a full CSR write and not a delta, so the writer waits out
an image-sized write. The drift threshold and the interval floor are what keep it rare, and
a KB that cannot afford the pause at all takes `:disk-columnar` and pays the rebuild on
open instead.

The bytes on disk are **derived state**, and everything else follows from that. The image
is stamped with the disk record store's slot fingerprint and checked on every open — never
behind a flag — and any doubt at all (format, `kv/index-layout-version`, byte order,
records that moved, a short section, a missing commit marker) discards it and runs the
same `reindex` above. That is what makes the backend safe to name: the index is
recomputable from the records, so a discarded image costs time and never an answer.

The swap is an atomic rename of the new file over the live one, which Windows will not do
while the target is mapped — so **Windows is the refused platform and everything else is
admitted**. The evidence is one operating system's file-locking model, so "not Windows" is
what the guard reads (`publishable-platform?`); `:index :snapshot` there throws
`:unsupported-platform` naming the OS, the reason and the pairing to take instead
(`{:index :columnar}`), and an image already in the directory is discarded as one more
`decision` mismatch class. Only the publish is
implicated: the durable store's logs, slots and lock run on every platform, and a
`:disk-columnar` KB opens there and rebuilds its index from the records.

One part of it does not hold the acceptance property it was built for. The **token
dictionary** is fact-scaled rather than vocabulary-scaled wherever something mints a
symbol per fact, and it is read into heap whole; `sentex/*min-indexed-depth*` refuses that
by default ([density.md](density.md)), so it is a property of the corpus rather than of
the image. Every other resident section is path- or vocabulary-scaled, which
[indexing.md](indexing.md) §8 states section by section.

The dictionary is also the one mismatch class that **repairs itself**. Its log is keyed
on `tokens/Key`, so `2` and `(int 2)` are one entry; a log written before it was keyed
that way holds both as frames, reloads one entry short per pair, and shifts every id the
mapped edges cite — so the image is condemned, and the rebuilt one is snapshotted against
the same log, condemning the next open too. `:duplicate-tokens` is that diagnosis, and
the open that makes it drops the commit marker and rewrites the log without the pair
before it declines. Rewriting moves ids, which is legal here and only here: this log's
ids are cited by the mapped edges alone, where the record store's log is cited by every
frame it holds (and cannot hold a pair — only symbols and keywords are interned there).

A derived index is shared for the life of the JVM under the **identity of the records it
belongs to** — the space number for RAM records, the canonical directory for a file-backed
store (tagged `:disk` or `:sqlite`, so the two never collide over one path), and the
database identity for `:pg` (host, port, database, schema), which has no directory to key
on. Keying a disk-backed KB's RAM index by the space number instead would hand two KBs
over different directories one shared index whenever they took the default. If the records
are emptied out from under it, the leftover index is dropped on the next open rather than
left describing records that no longer exist.

#### The belief certificate (`vaelii.belief.snapshot`, off by default)

The image is one half of a `:disk-columnar` cold open; `recover` is the other, and its own
expensive pass is the closing settle's definitional-clash scan (`settle/constraint-nogoods`).
On a **clean** corpus that scan defeats nothing — every standing clash an equal-strength
dilemma that disbelieves neither side (`settle/decide-nogood`) — so it is verification, and the
belief it reaches is the belief the rest of the settle reaches without it. The belief
certificate (`vaelii.impl.disk.belief-snapshot`) is to that scan what the image is to
`reindex`: a full recover writes belief's **sparse complement** to `<dir>/belief/` — a
`record-store/slot-fingerprint` stamp, whether the corpus was clean, and the disbelieved
sentexes content-keyed as EDN, human-readable — and the next cold open that still matches the
stamp binds `settle/*skip-constraint-nogoods*` for the closing settle and rederives identical
belief without the scan.

Same cache-of-derived-state discipline as the image, and it reuses the same stamp: checked on
**every** open, never behind a flag, and any doubt — a changed record, an unclean stamp, an
absent or torn file — discards it and runs the full recover, always correct because belief is
derived. Unlike the image it needs no platform guard: the writes are EDN through an atomic
rename, not a mapping a swap has to break. A corpus carrying a strength-differentiated
clash-**loser** — whose defeat cascades through what it supported, and which no post-hoc replay
reconstructs — is stamped **unclean** and never taken on the fast path, the one case where
skipping the scan would believe the wrong thing.

What the certificate never does is *supply* belief: it records that a clean close found no
clash, so the worst a stale one can do is be discarded, never believed. Why a certificate
of a clean bill rather than a stored image of the labels:
[defenses.md](defenses.md#the-belief-certificate-records-a-clean-bill-not-the-labels).

### The index is written once — `KvBackend`

`KvIndexStore` (`vaelii.impl.kv`) is the **generic** `IndexStore`: the whole trie /
roots / rule / exception / term-index logic lives there, in terms of a small `KvBackend`
protocol — scalars, counters, sets, an N-key `kv-intersect`, a `kv-member?` probe, and a
`kv-batch` that lands one sentex's entire path (levels, term index, roots) as one unit. A
backend supplies only that adapter:

- `MemoryKvBackend` (`vaelii.impl.memory`) — one map keyed by the logical vectors, with
  the predicate-scoped argument roots held instead as a counted `pos → term →
  {:union, :preds}` trie under a reserved key; `kv-intersect` is
  `clojure.set/intersection`, `kv-members` returns the stored set by reference.
- `DiskKvBackend` (`vaelii.impl.disk.kv`) — the same in-RAM map, durable behind a
  write-ahead log (below).

There is a **second, optional protocol beside it**: `kv/ArgColumns`, four descent reads
over that argument-root family (`arg-scoped-members` / `arg-scoped-intersect` /
`arg-agnostic-members` / `arg-agnostic-count`). It carries an `Object` default that
rebuilds the four-part vector keys and folds the generic set ops, so a backend that
implements nothing answers exactly what a flat `key → set` map answers and a new adapter
owes it nothing. `MemoryKvBackend` overrides it with the trie; `dense-roots` takes the
default over its packed keys ([indexing.md](indexing.md), §2).

`kv-member?` is there for a *cost* rather than an answer. `exception-rule?` — the gate
the firing path takes once per candidate rule per new datum — asks whether one handle is
in the roster, and a backend that packs a posting (`vaelii.impl.dense-kv`,
`vaelii.impl.dense-roots`) has to answer by probing it, not by materializing the roster
and testing the result. On the two backends above the two roads read identically, which
is exactly why nothing behavioural catches the difference: `lein perf --only
exception-roster-gate` is what defends it, and `kv_membership_test` is what says every
adapter's probe agrees with its own `kv-members`.

So a new backend (SQL, overlay) is a new `KvBackend` rather than a second index,
contract-tested by `kv_backend_test` (every adapter satisfies one spec). The one
`IndexStore` that is *not* a `KvBackend` is `ColumnarIndexStore`
(`vaelii.impl.columnar`), which implements the trie natively over CSR arrays and
delegates the flat families — roots, term index — to an embedded `KvIndexStore` on the
same keys, so the two answer alike. The **record store** stays per-backend
(`MemoryRecordStore` / `DiskRecordStore`) — a handle→blob map is simple enough that
sharing it buys nothing.

## Postgres records (`:pg-memory`, `:pg-disk-log`)

`com.vaelii/postgres`, the `vaelii.postgres.record-store` adapter. Three tables —
`vaelii_record (id, kind, frame, premise, strength)`, `vaelii_record_provenance` and a
`vaelii_record_meta` holding the high-water handle — with the whole record nippy-frozen
into `frame` and the assumption strength on its own column as the authoritative value.
`id` is **`bigint`**: handles are ints in the engine, and a column type is the one place
that decision becomes an `ALTER TABLE` on a table with 100M rows in it.

A KB names the database with `:pg`, and nothing derives a default one — a KB that took a
server by default would hold its records somewhere nobody said, so the opt is required
and its absence is refused at `open-kb`.

```clojure
(v/open-kb {:backend :pg-memory
            :pg {:dbtype "postgresql" :host "db.internal" :dbname "kb"
                 :user "vaelii" :schema "prod"}})
```

`:schema` puts the three tables in a schema of their own, so one database carries several
KBs and an operator drops one with `DROP SCHEMA`.

### What a server buys

- **`COPY`.** The fastest ingest path any of these backends has, and the strongest single
  argument for this one. Measured on 20,000 records against a local server: `COPY … FROM
  STDIN BINARY` loads at **95.8k records/s** where the per-record door manages **4.1k/s**,
  and where the `:disk` store's own per-record path manages 52.7k/s. It is a *load*
  rather than an upsert — `COPY` has no `ON CONFLICT`, so a handle the store already holds
  raises — which is the honest shape for a bulk path.
- **An operator's existing everything** — backup, PITR, replication, monitoring, access
  control, a query surface. None of it is ours to write and all of it is what someone
  running a large KB asks for on day one.
- **A store bigger than one disk**, and one that is not the machine the JVM is on.
- **A consistent read while something else is writing**, which the server can give and
  this adapter does not ask for: nothing sets an isolation level, so every read runs at
  the server's default. The capability is the server's; taking it is not yet wired.

### What a server does not buy

**A shared record store is not a shared KB.** Belief lives in the writing process's RAM —
the JTMS and the taxonomy closures — so a second process connected to the same database
does not see the first's beliefs, and its retraction sweep **deletes records the first
still believes**. That is [the single-writer contract](#the-single-writer-contract), and a
server does not weaken it by one clause. The `:disk` backend can enforce it with a file
lock; a database has no such thing to take, so on this backend the contract is a rule the
operator keeps rather than one the store fails fast on. "Several application servers on
one KB" is the thing a Postgres backend suggests to every reader, and it is not this.

A second process may **read** after `recover`, and `recover` is roughly 8 s per 313k
records on the `:disk` store — call it **the better part of an hour at 100M**, and that
figure is a local store's, not a reader's over a network — so that is a snapshot reader
rather than a replica.

### The round trip, and what is done about it

A point read over a connection is a network round trip where the disk store's is a page
touch. Measured against a local server, `get-sentex`:

| | µs/read |
|---|---|
| Postgres, cache bypassed (`:cache-capacity 0`) | ~50 |
| Postgres, fetch-LRU hit | ~0.3 |
| `:disk` store, warm (its own LRU answering) | ~0.2 |

Both orders of magnitude and both ends of the comparison stated: 30,000 records, a local
server over loopback, 3,000 random handles. Against a **cold** disk-store fetch — a page
touch, ~3 µs ([density.md](density.md)) — the gap is ~18×; against a warm one it is ~230×.
A remote server is the number that matters and it is larger than either.  Level with the
disk store when the LRU answers.
So the LRU is not an optimization here, it is the backend's viability: a working set that
fits it costs what local costs, and a query that pages a record per candidate outside it
costs a few hundred microseconds apiece. The store's answer is that cache
(`:cache-capacity`, 65536 records
per kind by default), plus a **premise-strength cache filled by the `premise-ids` walk
itself** — `recover` asks for every one of those strengths immediately after enumerating
them, and the walk already selects the column, so the pair costs one scan instead of a
scan plus a round trip per premise.

The enumerations (`sentex-ids`, `justification-ids`, `premise-ids`) feed `reindex` and
`recover`, which walk all of them, so they run on a **server-side cursor** — autocommit
off and a set fetch size, which is the pair the driver streams for. Buffering them would
be an `OutOfMemoryError` with a plausible-looking stack trace at corpus scale.

**The prefetch hint** (`Prefetching`, above) is what this store does about a walk that is
about to ask for many records: given a chunk of candidate handles it checks which it
already holds — a RAM lookup apiece, the cache being the exact oracle for "would a batch
help here" — and issues one `WHERE id = ANY(?)` for the rest, or nothing at all when it
holds them already. Measured on a 40k-record corpus whose working set does **not** fit the
cache, 100 queries at 200 candidates each: **~13 ms/query with no hint, ~4 ms at a
256-handle chunk** — roughly 3× that is the round trips going away, after which thawing
the frames is what remains. On the same corpus with a cache that *does* hold it, the hint
finds nothing missing and costs the scan: under a millisecond a query either way.
`:prefetch false` on
the store is the hard off, and `:prefetch-min` is how many uncached handles make a batch
worth issuing (4).

A batched record fetch *returning records* is a different thing and is not on
`RecordStore`: adding one is a protocol change whose value is entirely at the call sites — `resolution`'s match paths, the levels,
`provers` — which is where it would have to reach to be worth anything. A `get-many`
that reaches into all three is its own piece of work with its own oracle, not a detail of
this backend.

### Which host owns a `:pg-disk-log` index

`:pg-disk-log` is Postgres records under the **local** durable index, which puts the two
halves of one KB on what may be two machines, with two lifetimes. The index is derived from the
records, so this pairing puts the derivation on whichever host ran the writer: the files
live under that host's `:dir`, they do not travel with the KB, and a second host
connecting to the same database finds no index and rebuilds it from the records. That
rebuild is correct and automatic — the coverage check compares the index's root count
against the live record count on every open and repairs a short one — and it is O(records)
paid at that host's first open.

So `:pg-disk-log` is worth it for a KB that restarts on one machine, and buys nothing for one
that moves between machines. `:pg-memory` is the pairing that pays the rebuild every time
and owns no files at all.

**And the cheaper open leaves a colder cache**, which is the part that reads backwards.
`:pg-memory` rebuilds its index on every open, and that rebuild walks every record — so
the KB arrives with as much of its fetch LRU full as the LRU holds (65,536 records by
default: the whole store when the corpus is smaller, its tail when it is not), and the
first queries into that much of it make no round trips at all.
`:pg-disk-log` skips that walk, which is the point of it; the cache is therefore empty when
the first query arrives, and every candidate is a miss until it fills. The saving is real
and so is the bill: `:pg-disk-log` moves work out of the open and into the first queries after
it, and on a corpus that fits the cache `:pg-memory` may reach a steady state sooner.

**`:pg-disk-log` requires `:dir`, and the directory remembers which database it describes.**
Neither is ceremony. A derived default directory falls out of the space number
(`<tmpdir>/vaelii-disk/space-<n>`), so two `{:backend :pg-disk-log}` opts that name no
directory are *the same directory* — two KBs over two databases sharing one index, each
answering out of the other's handles. And a directory deliberately pointed at the wrong
database is not caught by the coverage check below it, which compares record **counts**:
two unrelated stores of the same size agree, and what gets through is worse than an empty
index, because a re-assert of a sentence this store does hold mints a second handle for it.
So the index directory is stamped with the database identity on first use, and an open over
a different one is refused (`:type :stale-index-records`) rather than answered. Give each
KB its own `:dir`, or delete the directory to rebuild against the records now behind it.

`close!` releases both halves: the pool the store built, and the index directory's
exclusive lock.

### Durability, and whose it is

`fsync` is a no-op on this store, with a reason rather than an empty function: a commit is
durable when the **server's** WAL says so, `synchronous_commit` is the setting that
decides it, and there is no client-side buffer here for the engine to force. The store
registers its *close* with the durability daemon all the same, so a JVM that exits without
a `close!` still releases the pool.

## The on-disk backend (`:disk`)

`vaelii.impl.disk.*` — a self-contained, durable, crash-safe store in a directory, no
server.  Its substrate (`files`) is append-only `.log` files of length-prefixed nippy
frames plus fixed-width 24-byte `.idx` slots keyed by integer id.

- **`DiskRecordStore`** (`disk.record-store`) — the `RecordStore` protocol over three
  per-kind log/idx pairs (sentexes, justifications, provenance).  A record is **paged**
  from disk on `get`: one positional read of the 24-byte slot, one of the payload it
  points at, then the thaw.  Both are `FileChannel` reads that name their offset, so
  neither uses nor moves the RAF's shared file pointer, and neither pays the seek and
  four primitive reads an unbuffered `RandomAccessFile` would charge for the same bytes
  (measured: that was 52% of a warm fetch).  A **write** is the mirror: the frame is
  packed and lands in one positional write at the log's end, the slot in one positional
  write of its 24 bytes — four syscalls per record, the two length reads included — and
  an append is **all or nothing**: a write that fails partway sets the log back to its
  pre-write length before the failure travels, so no frame ever promises bytes that did
  not land (a torn frame mid-log is what the next dirty open's length walk would stop
  at, truncating every record after it).  Only the live handles per kind sit in RAM (a
  compressed bitmap, for O(1) enumeration), plus a **bounded LRU of hot records**
  (`vaelii.disk.cache`, `:cache-capacity`, 0 disables) — sound because a record is an
  immutable value and the three paths that change what lives at an id all maintain it
  (`store!` replaces, `kill!` evicts, `clear-records!` empties; compaction preserves
  content and so needs nothing).  `next-id` recovers as `max(a counters blob, 1 + the
  highest slot id)` — the highest slot survives deletes and compaction — so a handle is
  never reused.  That `max` is also why the blob is rewritten only when the counter moved:
  persisting it is a temp, an fsync of it, an `ATOMIC_MOVE` and a directory fsync, and the
  daemon ticks every three seconds for the life of the process — so a store nobody is
  writing to would pay those four operations forever for a number that has not changed,
  and a blob left behind the counter is behind only on handles that were minted and never
  stored.  A premise is a sentex with non-nil `:strength`, so the premise set is
  derived from the durable records, not stored — and derived without *reading* them:
  every write puts the answer in two bits of its slot's reserved `flags` word (bit 0 =
  the slot speaks, bit 1 = premise), so an open reads the set off the idx walk it
  already makes for the live handles.  A slot that does not speak — one written before
  the bits existed — sends that one handle to its record, and the record wins wherever
  both do, which is what keeps the bits a cache rather than a second truth.  Two bits
  and not one for the same reason: a legacy slot reads as 0, and 0 has to mean *unknown*
  rather than *not a premise*, so no store needs rewriting and no version needs bumping.
  Two bits further along (bits 2..3) carry the premise's **strength rank**, so
  `premise-strength` — the one field `recover` reads per premise, and the whole record
  fetched for it on disk — answers off the same 24-byte slot the walk already reads.  A
  rank of 0 means *unrecorded* and falls back to the record, exactly as the premise bit
  does, so the strength column is the same no-version-bump cache one field up — and it
  shares that bit's residual: the flags word is not crash-atomic, so a torn flags page can
  leave a stale rank (or bit) across a crash.  A **dirty** open closes it: the marker says
  the last close was unclean, so the open walks the records and rewrites every slot whose
  flags disagree (`reconcile-slot-flags!`), which a clean open — its slots consistent by
  construction — skips entirely.  Between crash and that open the record is the durable
  truth, and a re-mark or a compaction repairs a slot the same way.
- **The frame codec** (`disk.codec`) — a frame holds its record's fields
  **positionally** — [why positional, not
  tagged](defenses.md#frames-are-positional-not-tagged).  A sentex frame is
  `[tag sentence context id truth strength …]`, a justification frame a bare vector (one
  shape needs no tag), and provenance — an open application map — passes through as it
  comes.  Each decoder dispatches on the thawed frame's shape, so **frames written before
  the codec still read** and no store needs rewriting.  Decoding interns the symbols it
  rebuilds, so a paged record shares one vocabulary object per name with the in-memory
  store instead of minting a private copy per fetch.
- **Tokenized bodies** (`disk.tokens`, opt-in via `vaelii.disk.tokens` / `:tokenize?`) —
  the positional frame still spells its sentence out, so the vocabulary is written into
  every frame.  A tokenized frame replaces the s-expression fields with one varint byte
  string of ids from a **durable** `tokens.log` (id = append order, content-keyed,
  first-writer-wins, never reused).  A frame citing an id the dictionary lacks is
  unreadable data, so the ordering is what makes it safe: a token is written **before**
  the frame citing it, and `fsync` fsyncs the dictionary **first, holding the sentexes
  kind lock**, so nothing is appended between the two fsyncs and every record durable
  after a tick has durable tokens.  (fsyncing per *new* token would give the ordering
  too, and it is the wrong trade: a cold load is then fsync-bound, measured ~217
  records/s.)  Between ticks the two logs can still skew on a machine crash, the
  same cross-file skew a log and its idx have; `open-record-store` repairs it as
  `validate-idx-tail!` does, by tombstoning a record whose ids the dictionary lacks.
  Only symbols and
  keywords are interned — numbers and strings ride beside the id stream as literals, so
  a KB of measurements cannot mint an entry per value.  It is two more frame *tags*, not
  a format change: a store reads plain, tokenized and pre-codec frames side by side, so
  turning it on costs no rewrite and turning it off orphans nothing.
- **`DiskKvBackend`** (`disk.kv`, behind `KvIndexStore`) — the index is derived and
  small (and `reindex` rebuilds it from the records), so the whole key→value map lives in RAM,
  exactly as `MemoryKvBackend` holds it, with every mutation appended to a `kv.log`
  write-ahead log that replays on open.  Durability without changing the index logic.
  The WAL is **logical**: a frame is the write op itself (`[:add-to-set k m]`, `[:remove-from-set k m]`,
  `[:put k v]`, `[:delete k]`, `[:increment k]`, `[:decrement k]`), so a set-add logs the one added
  member — O(1) — and a bulk load of N members into one root writes O(N) WAL bytes,
  rather than logging the resulting value — [why the op, not the
  value](defenses.md#the-index-wal-logs-the-operation-not-the-value).  An index batch —
  one `index-sentex`'s ops — is packed into one buffer and lands in **one write**, so
  the batch is on disk whole or not at all, and the RAM map, published after the write,
  never disagrees with the log about which ops happened.
  Replay folds each frame through the same `apply-op` that applies a live op; `compact!`
  rewrites the log as one `[:put k v]` op per live key, so every frame is a uniform op
  and the reader needs no snapshot-vs-delta discrimination.  Compaction is this store's
  snapshot cadence — it bounds replay length and reclaims the delta frames, triggered
  off a delta-accumulation ratio (`dead-ratio` = frames beyond one-per-live-key).

**A bulk sweep claims recency like any other read.**  `export!`, `export-text!` (over the
premises), `reindex`, and the
`recover` a `fork` runs over a live base each fetch every record through `get-sentex`,
so a sweep of a store larger than the cache leaves the LRU holding the last handles it
happened to visit rather than whatever the query workload had warmed.  (The `recover` at
*open* is the one that costs nothing: the cache is empty, so there is nothing to
displace.)

What that displacement costs the queries after it is bounded, and the bound is why it
stays small.  Refilling costs at most one miss per entry the sweep displaced —
`capacity` misses, whatever the store's size — and where the sweep itself pays a read
per record, that is `capacity / records` of the sweep's own cost, a ratio the per-miss
cost cancels out of, so a store too large for the page cache does not change it.
Measured on an 800,000-record store at the 65,536 default: a skewed stream holding a
~84% hit rate at ~1 µs/query drops to ~69% over the 25,000 queries following a full sweep
and is back inside a point five windows later — **tens of milliseconds of added latency
in all, against a sweep that itself took seconds**.  At 200,000 records, three times the
cache and where that ratio is at its worst, the shape is the same and the sweep is the
larger cost by an order of magnitude.  A skewed stream's head is much smaller
than the cache, which is why the refill lands well inside one window: the sweep displaces
65,536 entries, of which a few thousand are ones anything asks for again.

**A closure sweep is the reader with no reuse inside it.**  A transitive-predicate walk
fetches one record per edge it crosses and visits each node once, so nothing it reads it
reads twice — the skew the cache is sized for is absent by construction.  Under the
capacity that costs nothing (a walk over 20,000 records is 1% fetch, and the `:disk`
fetch beats the `:memory` one, a `LinkedHashMap` hit against a nested-map lookup); past
it the fetch is a real page-in at ~3 µs and rises to a fifth of the hop.  The other four
fifths are the retrieval and walk machinery both mounts pay alike, so the fetch is a
minority of the walk at every size measured — `lein bench-walk`, and
[taxonomy.md](taxonomy.md), "What one hop costs".

**Durability + crash-safety.**  A daemon (`disk.durability`) fsyncs every store on a
tick and a JVM shutdown hook closes them.  Logs are recovered on open: finish an
interrupted compaction, truncate a torn tail, tombstone any slot now past EOF.

Finding that torn tail reads the frame **lengths** and decodes nothing
(`files/log-tail-offset`): a prefix, a skip, repeat, through a positional read window,
since a `RandomAccessFile` is unbuffered and a `seek` per frame is syscall-bound —
[why lengths, not frames](defenses.md#torn-tail-recovery-reads-lengths-not-frames).
The length chain suffices because a frame is appended **before** the
slot that points at it, so a torn tail frame is one nothing references, and
`validate-idx-tail!` is what reconciles a slot against a log that lost its end.  A
**non-positive** length ends the walk: no frame payload is empty, so a zero is space
never written, and a filesystem that zero-fills past a tear would otherwise be walked to
EOF four bytes at a time and pronounced intact.

A clean `close!` records each log's length in `clean.nippy` and the next open skips the
walk while the length still agrees; the marker is *consumed* on open, so it only ever
describes a store nobody holds, and any disagreement — stale, absent, unreadable, past
EOF — falls back to the walk.

The walk finds a frame boundary; it cannot say whether what remains is *everything*,
and a short index opens populated-looking and answers short forever — re-asserting a
fact it cannot find mints a second handle for a sentence already stored.  Two
instruments close that, each for the loss that defeats the other, and `open-kb`'s
coverage gate reads both.  The **batch-seal counter** (`kv/sealed-prefix`) is
incremented as the *last* op of every `index-sentex` batch and decremented as the
last op of an unindex's cleanup, so it equals the indexed-sentex count exactly when
every batch landed whole: a torn append-mode tail keeps a batch's prefix — the root
count included, which is why the root count alone is the wrong instrument — and loses
the seal first.  The **length check** compares the file against the clean marker
before the marker is consumed: a compacted log is one flat `[:put]` per key in hash
order, so a tail lost at rest — a short restore, a partial copy — is arbitrary keys,
the seal possibly among the survivors, and only the length says the file is not the
one that was closed.  Either sign, and the gate rebuilds the index from the records.
A store whose seal reads zero — one written before the counter, or an index installed
whole by `import-dump`'s replay — is checked by the root count alone, as before.

The index WAL additionally **compacts on a clean close**
when its dead ratio has earned it (the same switch and threshold the background tick
uses), because opening it is a replay and so costs the frame count rather than the
live-key count.  Measured at 300k facts, that compaction is worth 4.5× on reopen (36.2s
uncompacted against 8.0s), and the index's own share of the open is where nearly all of
it sits (32.9s against 6.5s).

Compaction never edits in place — it rewrites to a temp, fsyncs, drops a commit
marker, then replaces the original, so a crash mid-compaction recovers to the last
durable state.  The record store's compaction is **copy-on-write**: the O(live) record
rewrite (read + thaw + re-freeze + write every live frame) runs *without* the kind
lock, reading the log's immutable region through a private read handle, so reads and
writes of that kind do not stall for it.  Only two brief lock holds bracket it — a
snapshot of the live slots up front, and a delta reconcile + swap at the end that folds
in whatever was stored/killed during the rewrite (a concurrent `clear-records!` sets an
abort flag and the reconcile discards its temps).  `reindex` rebuilds the index from the records on
disk unchanged.

The rewrite preserves every live record and its handle, with one exception: a slot whose
frame the log cannot give back — what a truncated tail leaves under a slot the truncation
did not reach — is **tombstoned rather than carried**, and the handle leaves the live set,
the premise set and the record cache once the install lands.  Re-freezing the `nil` would
put the handle back as a live record fetching to nothing, an id `sentex-ids` names and
`get-sentex` has no answer for; a record disappearing is logged at `:warn` per handle,
since it is something an operator has to be told rather than shown by a later count.

**Two monitors, because three threads touch this store.**  The writer is one; the
durability daemon is another (`fsync`, every `vaelii.disk.sync-ms`); a compaction runs on
a third.  So the store's *resident* state — the live-id set, the hot-record cache, the
compaction delta set, the failure flag, the handle counter and what the counters blob was
last left holding — is not the writer's alone, and a field written outside a monitor is
one another thread can catch mid-pair.

- The **kind lock** covers that kind's log and idx *and* the resident state derived from
  them — on the read side as well, since the live-handle roster is a bitmap mutated in
  place and a read taken beside a concurrent add reads a structure mid-edit. A store, a
  kill, a batch and the compactor's reconcile each take it once and do both halves inside
  it, so no reader finds an id live whose slot says tombstone, or a cleared delta set
  under a writer folding an id into it. The cost is an `addLong` and a map put inside a
  monitor already held for two file writes.
- **A monitor of the store's own** covers the three that belong to no kind and move
  together: the handle counter, `counters.nippy`, and the stamp saying what that blob
  holds. `fsync` reads and writes them on the daemon's thread and `clear-records!` on the
  writer's, and a tick that read the counter before a wipe and wrote the blob after it
  would leave a wiped store stamped with the pre-wipe high-water mark. It is not a kind
  lock because a whole-file blob rewrite held inside one would put a record append behind
  it on every tick that minted a handle.

The premise set needs neither on the write path: each mutation is one `swap!` on one
atom, and the pairing that would matter — a handle in `premise-ids` whose record is gone
— is a delete the writer makes, on the thread that reads it back. Its one mutation from
another thread is the compactor dropping a handle whose frame the log cannot give back,
which takes the kind lock beside the live-set drop it belongs with.

**The switches are checked.**  Every `vaelii.*` property the backend reads — the tick
(`vaelii.disk.sync-ms`), `vaelii.disk.fsync`, `vaelii.disk.auto-compact`,
`vaelii.disk.compact-dead-ratio`, `vaelii.disk.compact-min-interval-ms`,
`vaelii.disk.compress`, `vaelii.disk.cache`, `vaelii.disk.tokens`, `vaelii.disk.lock`,
`vaelii.belief.snapshot` — has a domain in `vaelii.impl.config`, and a value outside it is
refused with `:unknown-option` naming the property, the value and the legal spellings.
`vaelii.index.snapshot` has an empty domain and is refused at every spelling, naming
`{:backend :disk-snapshot}` instead: the mapped index image is a *representation*, and a
representation belongs in the opts map where the KB's own configuration records it.
`open-kb` reads the lot before it opens anything (`config/check!`), which is the earliest
door: two of them are read per fsync tick, where a throw is a log line nobody can
attribute.  The boolean switches share one vocabulary — `true` / `1` / `on` / `yes` and
`false` / `0` / `off` / `no`, case-insensitively, a blank value being unset — so a
spelling that works for one works for all of them, and `=disabled` is an error rather
than the opposite setting.  `vaelii.disk.fsync` takes `dsync` or nothing, and
`vaelii.disk.compress` `zstd`, `lz4` or `none`.

**Single-writer.**  `disk.lock` takes an exclusive OS `FileLock` on `.vaelii.lock`
when a directory opens and fails fast if another JVM holds it — enforcing the
single-writer contract.  `-Dvaelii.disk.lock=false` (or `0` / `off` / `no`) turns the
lock off, for a filesystem whose `FileLock` is unreliable (some network mounts).  It
removes the *enforcement* and not the contract:
a second writer under it corrupts exactly as the contract says one does, with nothing
left to fail fast.

Three things about that refusal are worth knowing, because each of them is a different
fact wearing the same shape:

- **Another JVM** is `tryLock` returning nil, and the holder tag written in the file names
  the process holding it. `:type :disk-locked`.
- **This JVM, through another channel** is `tryLock` *throwing*
  `OverlappingFileLockException` — the OS refuses an overlapping lock inside one process,
  so this says nothing about any other one. It means a second classloader copy of
  `disk.lock`, or code in this process holding the file locked itself; the tag in the file
  is then ours, so the refusal names this JVM from `ProcessHandle` rather than reading it
  back. `:type :disk-locked` with `:same-jvm? true`.
- **This JVM, unable to let go** is a `.release` or `.close` that threw. The directory
  stays marked held rather than being reported free while the descriptor and the OS lock
  are still ours, and re-acquiring it is refused with `:type :unreleased`. Only the process
  exiting drops what is still held.

The switch is read **at acquire time and nowhere else**: it decides whether an entry is
made, and `held?` and `release!` follow the entry.  Toggling `vaelii.disk.lock` under a
directory this JVM already locked therefore cannot strand the OS lock, which is what a
`release!` re-reading the property would do.
`vaelii.core/close!` releases it without the JVM exiting —
flush and close each component, deregister from the durability daemon, drop the lock —
so a long-running process can hand the directory to another process.  An unclean close
still releases: every component gets its close attempt, the lock release and the
registry removal run even when one throws, and the first component failure is rethrown
*after* that cleanup — so a throw from `close!` means the directory is handed back but
the close was not clean.  Within one process, stores are shared per canonical
directory (`disk.backend`, a registry mirroring the memory backend's db registry), so
two KBs over one directory share the durable store — the restart contract the recovery
tests rely on — and the lock, file handles, and durability registration are taken once;
closing either KB closes both.

## The sentex records — `LiteralSentex` and `RuleSentex`

A sentex is stored as one of **two records**, split so a literal sentex does not carry
the seven rule-only slots — there are 100M+ facts, and each dropped reference field is
~4 bytes across all of them (measured: the record shell falls from ~80 to ~48
bytes/instance, ~3.2 GB at 100M). Both share a scalar **core**; `RuleSentex` adds the rule
decomposition. The `sentex/sentex` constructor canonicalizes the structural connectives
and `set/*` wrappers into these fields rather than leaving them as sentence data, and
emits the right record.

The **core** (`LiteralSentex` and `RuleSentex` alike):

- `:sentence` — the readable, normalized form (`(not (flies Tweety))`,
  `(implies (and A B) C)`), kept for display and matching.
- `:context` — the context symbol it holds in.
- `:id` — the integer handle, `nil` until the record store assigns one.
- `:truth` — `:true` / `:false`. A `(not S)` becomes `S` at `:false`, and **double
  negation is eliminated** (`(not (not S))` ⇒ `:true` over `S`, via `peel-not`).
- `:strength` — the assumption strength (`:monotonic` / `:default`) when the sentex is
  asserted as a premise; `nil` for a purely-derived sentex. The record store writes it
  on `mark-premise` and reads it back with `premise-strength`, so premise strength
  lives **on the record** — with the rank mirrored into the disk idx slot (above), so
  `premise-strength` answers off the slot rather than paging the record on every open.

**`LiteralSentex`** is a literal — a fact or its negation, a metadata declaration, or a
query pattern: one signed predicate application, ground or holding variables. It adds
nothing to the core. Reading any rule-only key off a `LiteralSentex` returns `nil`, so
`(some? (:antecedent sx))` is the literal-vs-rule discriminant everywhere — no consumer
needs to know which record it holds.

**`RuleSentex`** is an implication, and adds the decomposition:

- `:antecedent` — the antecedent patterns as a vector (a leading `and` unwrapped).
- `:consequent` — the consequent pattern.
- `:varmap` — `{?var0 ?x, …}` mapping each **canonical variable** back to the name the
  author wrote, so `sentex/originalize` can restore the original form for display.
- `:direction` — the inference direction, set by the rule's `set/*Rule` wrapper:
  `:forward` / `:backward` / `:inert`, or `:both` for a bare `implies`. The wrapper
  canonicalizes into the record exactly like the connectives do, so a rule carries its
  own direction rather than it living in a side index.
- `:defeasible` — `true` for a `set/defaultRule` rule (its conclusions fire at
  `:default` strength and can be defeated); `nil` otherwise. Wrappers may nest, so a
  defeasible forward rule sets both fields.
- `:assumption` — `true` for a `set/assumptionRule` whose head is a *choice* for a
  solve rather than a derived truth; `nil` otherwise. Part of the rule's **identity**
  (it is a constant slot in the trie key), so a choice rule and its bare twin are
  distinct sentexes — see [solving.md](solving.md).
- `:constraint` — `:hard` for a `set/hardConstraint` rule and `:soft` for a
  `set/softConstraint` one, `nil` otherwise: the head is a contradiction the solver must
  avoid rather than a truth to derive. In the trie key on the same footing as
  `:assumption` — see [solving.md](solving.md).

An `exceptWhen` exception is **not** among these. It is a separate meta-sentex naming the
rule's handle, so it is not in the trie key and a rule and its excepted twin are the same
sentex — asserting the exception amends the rule in place. See
[exceptions.md](exceptions.md).

The constructor also puts the sentence into a **canonical form** — canonical
variables, canonical antecedent order, sorted symmetric arguments, and folded /
collapsed comparisons — so logically identical knowledge dedups to one handle. Sorting
symmetric arguments needs the taxonomy, so callers that store or look up a sentex go
through `res/kb-sentex`, which supplies `:symmetric?`. See
[indexing.md](indexing.md) for how this reaches the key.

Both indexes are built from this decomposition: the **term index** is fully
connective-free (heads stripped even nested in a rule), and the **trie key** drops
the `implies` / `and` rule frame — a negative literal keeps its `not` there as its
polarity (see [indexing.md](indexing.md)). `or` reaches neither, having no slot here at
all: a rule whose antecedent disjoins is stored as one rule per alternative before a
record is built ([canonicalization.md](canonicalization.md)). `LiteralSentex` and `RuleSentex` are records (not bare
maps) so each round-trips through nippy (the on-disk backend) with its type intact.

## Provenance — a side map, not record fields

Bookkeeping about *who* asserted a sentex and *when* lives in a **per-handle
provenance entry** keyed by the record handle, deliberately **beside** the record
rather than as fields on a `LiteralSentex` / `RuleSentex` / `Justification`. Two reasons the shape
is a side map:

- The record shapes stay fixed. Adding `:who` / `:when` / `:confidence` / `:source`
  slots to every sentex would bloat the hot on-disk value and the trie-adjacent
  canonical form for metadata belief never reads. The map is open — an application
  puts whatever it wants there — without the record schema ever growing.
- It is **not belief**. Belief is a pure function of the justification graph
  (docs/nmtms.md); provenance is annotation *about* an assertion event. A wall-clock
  `:created` therefore cannot affect order independence — nothing in `relabel` /
  `settle` reads it.

`assert` stamps `{:creator :created}` on the sentex it creates — `:creator` from
`opts :creator` or the dynamic `*creator*`, `:created` from the dynamic `*clock*`
(epoch millis by default; both bindable, which is how tests pin them). Creation is
**first-writer-wins**: re-asserting an existing sentex keeps its original stamp,
while any `opts :provenance` map is merged in. `add-provenance` layers application
fields on later; `provenance` reads the map. It is torn down with the record — a
`retract!` (via `delete-sentex!` / `delete-justification!`) deletes the provenance entry
alongside the record, so it never leaks past the thing it annotates. The store methods
are keyed by any handle, so the seam admits justification-level provenance (derivation
who/when); only asserted sentexes are stamped.

## Serialization

The engine stores Clojure data — records, symbols, keywords, numbers — and every
backend must preserve it type-faithfully (a keyword read back as a keyword, `1970` as
a number, a `LiteralSentex`/`RuleSentex` back as itself), or `lookup`'s wildcard descent silently
matches nothing (`kv_backend_test` and `index_edge_test` guard exactly this).

- **In memory** there is nothing to serialize: records sit in the map directly and
  the structured key vectors are the map keys (equal vectors are equal keys).
- **On disk** values are **nippy**-frozen into the log frames and thawed on read, so
  a `LiteralSentex` round-trips as a `LiteralSentex` and a `RuleSentex` as a `RuleSentex`; the in-RAM index map
  is rebuilt from the WAL frames the same way. nippy freeze is a pure function of its
  value, so equal values freeze to equal bytes.

Because in-memory serializes nothing, a value nippy **cannot** freeze and thaw — a
function, an atom, a non-serializable object — would store in memory and then throw at
write time on the first on-disk backend: the same assert would succeed or fail by
backend. `assert` (hence `assert-rule` / `assert-many`), `assert-inert`, and `check`
refuse it up front (`:type` `:not-encodable`, `checks/check-encodable`), so a stored
sentence's values round-trip in every backend or the sentence is refused in all of
them. The vocabulary and literals — symbols, keywords, strings, numbers, chars,
booleans, `nil` — and any **sequential** of them are always storable; a **map or set**
is refused under the same `:type` for a different reason — it has no canonical form,
so `sentex/canon` cannot normalize it to one set of bytes and `nm/form-rank` cannot
order it ("The canon gotcha" below) — and any other leaf is put through the
freeze/thaw pair the disk backends run, and refused if either throws
(`encodable_test` and `check_test` pin the boundary).

**That thaw is the guarded one** (`vaelii.impl.io.thaw`), which is what makes the front
door and the file readers hold one opinion rather than two that agree today. A leaf whose
class round-trips only through Java serialization — `java.time.LocalDate` and the other
`java.time` locals, a `Throwable`, a joda `DateTime` — is refused `:not-encodable` where
it is written, rather than stored and then refused on the way back off disk one restart
later. Write a date as a calendar term ([time.md](time.md)) or as a number; the types
nippy has an id for — `java.util.Date`, `java.time.Instant`, `java.time.Duration`,
`java.util.UUID`, `java.net.URI`, `java.math.BigDecimal`, every primitive array — are
unaffected.

### A file names no class

Every thaw the engine runs over a file goes through one door, and its allowlist of class
names is **empty**: a frame naming a class is refused `:disallowed-class` before the name
is resolved.

Nothing the engine writes states one. An export dump's frames are field maps by the
format's own rule ([api.md](api.md), `export!`); a log frame is a positional vector
(`vaelii.impl.disk.codec`); a whole-file blob holds counters and premise marks. So a
class name in a file came from somewhere else — and reading one is not a decode but a
**construction**: nippy's record id resolves the name and invokes the class's static
`create`, its deftype id invokes the first public constructor over the fields that
follow, and its `Serializable` id opens an `ObjectInputStream` over the bytes that
follow. A store directory and a dump are whatever an operator copied.
[why the allowlist is empty rather than curated](defenses.md#a-frame-naming-a-class-is-refused-never-resolved)

### A directory's sentinel

`records/format.edn` and `index/layout.edn` are read before anything else about a
directory is. A **missing** `format.edn` is stamped with the current version — a
pre-sentinel directory is by definition today's layout — but a **damaged** one is refused
(`:unreadable-store`), because a stamp cut mid-write is a directory whose records were
being written at the same moment. A damaged `layout.edn` reads as `:stale` instead and
the index is rebuilt from the records: it answers whether the entries can be *proved* to
match this build's key shape, and a torn stamp proves nothing.

## The canon gotcha

`LazySeq`, `PersistentList`, and vector can be `=` yet freeze to **different**
nippy bytes — and even two `=` `PersistentList`s (a reader literal vs one built
by `apply list`) differ. More basically, an in-memory map keys on `=`/`hash`, and a
`LazySeq` and a `PersistentList` that are `=` still must key identically. So every
sentence is canonicalized to a single `PersistentList` shape by `sentex/canon` (in
the `sentex` constructor), and `kv/term-key` canonicalizes lookup terms too (via
`sx/canon`). Anything that builds a sentence or a term for a key must go through
`canon` / `sentex/sentex`.

## Symbol interning

`canon` also **interns** every symbol it canonicalizes, through a process-wide pool
(`sentex/symbol-pool`, a `ConcurrentHashMap`), so a predicate, type, individual,
context, or variable name is a **single shared object** across every sentex that
mentions it, so the sharing it buys dwarfs its own footprint: a `parentOf` or `dog` in
millions of facts is one symbol, not one per fact. The trie key gets the sharing for
free, since `alpha-rename` passes constant symbols through unchanged, and the context is
interned by the constructor. Interning changes object identity, never equality, so a
pooled `?var0` still matches a fresh one as a binding key.

What bounds the pool is **not** the vocabulary. A KB that only names things holds one
entry per distinct name, but three writers mint a fresh symbol per *fact* — NAT
reification (`nat/fresh-constant`), head-existential skolemization
(`skolem/skolemize-conclusion`) and abduction's scratch contexts — and the pool is
static, process-wide and shared by every KB, so nothing hands an entry back. So it is
capped at `sentex/*symbol-pool-limit*` (1M, several times any real vocabulary: the
shipped ontology plus the whole of OpenCyc is ~188k constants) and cleared **wholesale**
when full, the shape the other bounded caches take. A clear costs the sharing for the
names minted before it and can change no answer, since identity was never what anything
read.

## Persistence & recovery

The record store, trie, term index, and rule index all persist — durably across a
restart on `:disk-log`, and within the JVM on `:memory` (the space-number
registry). The **taxonomy** and **JTMS graph** are in-memory, so a KB constructed
against an existing store has to rebuild them. `open-kb`'s `:recover? :auto` default
does it at construction (`true` is an alias for it); `:warn` leaves them empty and says
so, `false` leaves them empty in silence, and both leave the repair to a `core/recover`
call of the caller's own. Nothing else is a setting — a value `recover-modes` does not
name is refused (`:unknown-option`) rather than read as the warn branch, since a KB that
silently took `:warn` answers `[]` to everything and reads like an empty store. Either
way recovery is these two steps:

- **taxonomy** — re-integrate the special-predicate sentexes (`rebuild-taxonomy`
  queries `genl`/`genlCx`/`disjoint`/`disjointMetatype`/predicate-props/`inverse`).
- **JTMS** — the record store tracks live sentex ids, justification ids, and premise
  ids; each premise's assumption strength rides on its own sentex record (the
  `:strength` field, no side hash). `rebuild-tms` recreates a node per sentex, marks
  premises at their stored strength, adds each justification whose antecedents and
  conclusion the store still holds, and `relabel` recomputes belief. One naming a sentex
  the store does not hold is **left out** and counted, logged once at `:warn` under
  `::justifications-unrooted` with the count on `:data`: this is
  the one path whose justifications come off a store rather than out of a firing, so it
  is the only one that can reach `add-justification` with a datum that has no node, and
  a justification *concluding* the phantom would make it IN — a KB believing a handle it
  cannot show anyone. The informant is deliberately not checked; it is not a node
  reference. `recover` rebuilds the JTMS
  *before* the taxonomy (`rebuild-taxonomy` reads **stored**, not believed,
  sentexes, so `:support` / `:cache-support` record every asserting sentex —
  belief-filtering the replay would drop a disbelieved supporter, and clearing
  its defeat could never revive the entry), then narrows the replayed caches to
  belief with its own unconditional `refresh-beliefs` — inside the same depth
  deferral, and *before* the settle, so everything the settle reads answers
  through a taxonomy that already agrees with belief. The replay reads stored,
  the reconcile narrows to believed, and the contract is the composition: an edge
  supported by nothing was never in a region for the settle to reach, having been
  OUT from the moment its node was made, while the replay had already made it
  answer `genls`. Strengths, defeats, and reported conflicts are re-derived on
  restart and match either side of it.

Derivation depths reset to 0 on recovery (they only bound future chaining).

### Why the index persists and these two do not

All three are derived from the records, so "it can be rebuilt" does not separate them.
What separates them is **how** each is derived, and it decides the storage form each can
take.

An index entry is a **pure local function of one record**: `sentex/path`, `kv/root-keys`
and `kv/sentex-terms` read that record and nothing else. So a write touches ~6.2 entries
and no others, a log of write ops replays to exactly the map that produced it, and the
cost of persisting is proportional to the change. That is what makes `disk.kv`'s logical
op-logging work at all, and it is why the index is the half that persists.

A JTMS label is **not local** — it is a fixpoint over the justification graph, and one
assert can flip an unbounded region of it. Logging label changes would mean logging the
whole cascade per assert, which is precisely the cost `add-just*`'s
redundant-justification fast path exists to avoid. So the JTMS cannot be a write-ahead
log for the same reason the index can: the shape of its derivation is different.

That argues against *logging* it, not against *snapshotting* it — a snapshot is O(nodes),
written once and read once, and it is what the mapped index image already does for the
index. The write-once, validate-or-discard machinery that image carries is factored out of
it into a two-op **sink** seam (`vaelii.impl.io.snapshot` — a `SnapshotSink` streams a named
section and commits a manifest-last, a `SnapshotSource` reads them back; `decision` is the
validity check, one reason per mismatch class, any doubt discarding the whole image), so a
JTMS snapshot and a database image can share one format and one check with only the target —
a directory, a database, memory — varying. The export dump's index already reads and writes
through it, which is what keeps a dump's index and a standalone image the same bytes rather
than two serializations that drift. Two adapters implement the seam out of tree —
`vaelii-postgres`'s `pg-sink` / `pg-source` and `vaelii-sqlite`'s `sqlite-sink` /
`sqlite-source` — so its shape is published rather than private, and the in-repo
`file-sink` / `file-source` is the reference target an implementer reads. The taxonomy sits at the other end again: its adjacency is O(V+E) and each edge
insert is local and O(1), so it is a set-and-counter structure that `KvBackend` could hold
with no new ideas — the reason it is not held there is that nobody has needed it to be,
not that it resists it.

Two numbers to keep apart before acting on this. The Phase 0 "taxonomy ≈ 0" figure is
**residency** — 0.0 MB, 0 bytes/fact — and says nothing about rebuild *time*:
`rebuild-taxonomy` does a `sentexes-with-functor` per declaring functor plus a record
fetch per hit, and on a corpus where `genl` is a top predicate that is a great many
fetches. And `recover`'s ~8 s at 313k records is not decomposed, so how it splits
between the two is unmeasured.

**Atomicity.** All validation (naming, wff, arg/disjoint/functional/negation
checks) runs *before* any write, so a rejected assert leaves no trace (tested).
Cross-store atomicity is bounded by the two-store design: each side commits as a
single unit, and `reindex` rebuilds the index from the records to repair a torn
write.

## What a bulk load costs

`bulk-assert-facts!` is the write path with everything a *trusted* corpus does not need
already off — the definitional checks (the `arg` store query above all), the dedup
trie-walk, provenance, forward chaining, and N−1 settles. What remains is storing,
indexing and believing, and this is where that time goes.

`lein bench-loadphase [n] [repeats] [full|guard]` (`bench/vaelii/bench/loadphase.clj`) is
the instrument. It loads one corpus repeatedly through the same door, each run with one more
phase stubbed out from the outside in, so the difference between two consecutive runs is
that phase's cost and the deltas **sum to the baseline by construction** — there is no
unattributed residue. The peel order puts a phase before anything it reads: the
coincidence probe reads the index, so it is peeled before the index write, which is
peeled before the record write, which is peeled before canonicalization.

**1,000,000 distinct binary ground facts, `:memory` pair, one context, no rules.**

| phase | µs/fact | share |
|---|---:|---:|
| index write — key streams, postings, counts | 24.64 | 56.8% |
| JTMS node + the premise mark on the record store | 9.32 | 21.5% |
| the special-predicate suite + the violation ledger | 4.55 | 10.5% |
| the public `assert` prelude — shape checks, NAT gate, rule dispatch | 2.92 | 6.7% |
| record store `put-sentex` | 1.52 | 3.5% |
| the P/¬P coincidence set | 1.13 | 2.6% |
| canonicalization (`res/kb-sentex`) | 0.85 | 2.0% |
| the observation seams — alpha memories, change clock, handle cache | 0.63 | 1.4% |
| the one deferred settle | under the floor | — |
| **total** | **43.4** | **23,100 facts/s** |

Two things to read with it. The **settle** row measures at or below zero: one settle over
a million-fact positive corpus is free within the measurement, and because the baseline
runs first its rung also absorbs the run-to-run drift — which is why the rows above sum
to slightly more than the total. And a rung delta is a difference of two whole runs, so
**±1 µs/fact is the floor at 1M** (wider at 100k, where the runs are ten times shorter);
the rows under that are named rather than ranked.

**Across sizes the shape holds and the cost creeps.** The same ladder at 100,000 facts
reads 38.8 µs/fact against 43.4 at a million — a 10× corpus for a 1.12× per-fact cost —
and the index write is 56.5% of it at the small size against 56.8% at the large one. So
no phase changes character with N. What creeps is the depth of the structures being
written: a HAMT gains a level, and the roots' sets are ten times longer. The one row far
enough apart to be more than the floor is the **JTMS**, at 5.2 µs/fact against 9.3 — a
node into a map and a handle into a set, both of which the corpus size reaches.

**The index write is the load**, and splitting it says which part. Two `KvBackend`
decorators over the real one leave `index-sentex` computing every key and change only how
much of the batch it produced lands — one drops the `:increment` ops, the other drops the
batch entirely:

| component of the index write | µs/fact | of the load |
|---|---:|---:|
| postings — trie child edges and leaves, term index, secondary roots, roster, slots | 15.6–16.8 | 35–39% |
| key streams, the op list, and the pre-write roster/slot reads | 4.6–6.7 | 11–15% |
| count maintenance — one `:increment` per trie level per fact, plus the batch seal | 2.5–4.6 | 6–10% |

The ranges are two independent runs; the split arms are whole loads too, so their
difference carries the same ±1 µs/fact.

Postings dominate because two of them are `conj` into sets that grow with the corpus: the
functor root holds every fact with that predicate and the context root every fact in that
context, which is exactly what makes `count-with-functor` and `sentexes-in-context` O(1)
reads. **The load rate is the price of those roots plus the trie**, and it is not a
defect: the alternative to a write per family is a scan per read.

**Count maintenance is priced and it is not the lever.** Recomputing every prefix counter
once at the end instead of incrementing per level per fact can save 6–10% at most, and it
buys that by making `count-with-functor` answer a *stale* number for the length of a
load — a different contract from answering a slow one, and the query planner orders
conjuncts by those counts. The counts stay where they are.

**Two write-side tricks measured worse and are not on this path.** Accumulating the
in-memory index's map on a transient for the whole load
(`vaelii.impl.memory/with-bulk-writes`) ran **5–7% slower** than the plain path at 1M: it
removes the per-fact HAMT path copy of the *map*, which is not where the time is, and its
batch arm allocates an aligned reply vector per fact that the plain arm does not. Sorting
the corpus by trie key before inserting is unpriced here for a reason rather than an
oversight — its benefit is locality, and the in-memory trie is a hash map keyed by whole
path vectors, where there is no contiguity to hit.

**A facts/s figure is per writer thread.** This path is single-threaded, and by the
single-writer contract below it has to be. So a rate is only comparable against another
rate taken at the same writer count, and a wall-clock load comparison between two engines
is a comparison of thread counts until both are pinned to one.

### Why the coincidence post is guarded

One thing on the path is not a per-fact constant at all, and it is guarded rather than
paid. A store posts its sentence's body to the negation memo's `:dirty` set so the next
settle knows the body's pairing may have moved — but an unguarded post is one `conj` per
fact into a set that ends a load holding **one entry per fact of the corpus**, and on a
corpus with no negations the first settle then drops the whole thing. So `kb/note-opposed!`
writes the memo only for a body opposed before the store or after it, which is the only
case whose pairing can have changed. Both readers of `:dirty` filter it by `:opposed`
(`settle/moved-bodies` and `settle/note-supersession-flips!`), so a post for a body
opposed at neither end is written and dropped unread.

**What that buys is the set, not the clock.** Alternating the two arms inside one JVM in
**A-B-B-A order** — so the drift a JVM accumulates over a dozen loads lands on both arms
instead of on whichever runs second — measures **0.994× at 250,000 facts, five pairs
spread 0.95–1.04**: the guard does not move the wall clock at this size, and the spread
is the honest width of the answer. A fixed A-then-B order reports the same comparison as
a 20% win, which is the drift and not the guard, and is why the harness alternates. What
is really removed is a structure proportional to the corpus — a claim about a ten-million-
fact load's heap rather than about a quarter-million-fact one's seconds. `lein
bench-loadphase <n> <pairs> guard` re-checks it and prints every pair, because the spread
is what decides whether a median means anything.

## The single-writer contract

**One process, one writer.** The engine pairs a durable store with in-memory state
(the TMS, the taxonomy closures), and only the writing process's memory tracks its
writes:

- *Two threads, one process:* every TMS mutation applies atomically — the reference
  network through `jtms/swap-with-result!`/`swap!` on its atom, the dense one under a
  `StampedLock` write stamp — so concurrent operations **compose** and none is silently
  lost. That is a liveness floor, not a semantics: interleaved `assert`/`retract!`
  sequences are not serializable (find-or-create and the settle pipeline are
  check-then-act), so concurrent *writing* still needs a single writer. A reader thread
  beside a writer thread (the web browser over a REPL's KB) is the supported shape, and
  **both** TMS representations give that reader a consistent view — the reference out of
  its persistent-map snapshot, the dense one out of an optimistic read stamp validated
  against the writer's, so neither ever shows a partially-applied relabel
  (`jtms_concurrency_test`).

  **Two selectable index backends are narrower than that**, and it is the one place the
  floor does not reach. `:columnar` (`vaelii.impl.columnar`, and the `vaelii.impl.dense-roots`
  it builds on) and `:dense` (`vaelii.impl.dense-kv`, whose `IntPostings` is mutated in
  place) hold `^:unsynchronized-mutable` fields, so a write
  publishes through no barrier: a second thread may read an array reference, a
  capacity, the CSR-mode flag or a half-installed mapped section from before a growth,
  a compaction or a snapshot install, with no happens-before edge to stop it. The atom-
  and lock-based backends give the incidental reader a consistent view; these two do
  not, and keeping such a read on the writer's thread or behind a synchronizer is the
  caller's. The walk reads these fields at every frontier node, the index's hottest
  loop — [why unsynchronized
  there](defenses.md#the-columnar-and-dense-backends-use-unsynchronized-fields).
- *Two processes, one store:* not supported, and worse than stale — process B's
  belief filter hides A's facts, and B's retraction sweeps **delete records A
  still believes**. The `:disk` backend enforces this with an exclusive file lock
  that fails a second opener fast (`:type :disk-locked`), and there is no read-only
  open: `lock/acquire!` takes the whole file exclusively or throws, so the second
  process never reaches the records at all.

  **A server does not relax this, and it is the backend that most looks as though it
  would.** `:pg-memory` and `:pg-disk-log` put the records where several processes *can*
  reach them, and every clause above still holds: belief is in the writer's RAM, so a
  second process reasoning over the same database hides the first's facts and deletes
  records it still believes. What the `:disk` backend fails fast on, this one leaves to
  the operator — a database has no exclusive-open to take — so one writing process per
  database (or per `:schema`) is a rule that has to be kept rather than one that is
  enforced. A second process may read after its own `recover`, which is a snapshot
  reader and not a replica: [Postgres records](#postgres-records-pg-memory-pg-disk-log).

**What the contract does not cover is a second *batch*.** The in-memory index's bulk-write
path (`vaelii.impl.memory/with-bulk-writes`) accumulates on a transient taken off a state
atom held per **space**, which every index store over that space shares — so a bulk load
begun inside another over the same space is two accumulators over one atom on one thread,
which no rule about threads rules out. The install is therefore a compare-and-set against
the value the batch snapshotted, and a state that moved under it is refused
(`:stacked-batch`) rather than written over: [why compare-and-set rather than
overwrite](defenses.md#a-bulk-load-installs-by-compare-and-set-not-by-overwrite).

The contract is a property of the engine rather than of any backend: a shared record
store is not a shared KB, because belief lives in the writing process's RAM. So it holds
whatever the store underneath is, and no choice of backend relaxes it.
