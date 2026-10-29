# Storage

- **Covers:** the `RecordStore` / `IndexStore` protocols and the optional `Prefetching`,
  `Tallying`, `BulkLoading` and `BulkAnnotating` capabilities, what the three enumerations promise and what a
  handle set costs per handle, the sink an `import!` writes its records through, the eight legal record×index backend pairings and the optional `:sqlite` and
  `:pg` records adapters, nippy serialization, what one fact of a bulk load costs phase by
  phase, the two routes from a load to the chained closure and what each costs, loading a
  snapshot that changes over a fixed base, what an open reports of a record nothing
  supports, what a shutdown waits for, the reasoner set a store records, and the
  single-writer contract.
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

### The family methods

Seven `IndexStore` methods read and write every family `kv/index-families` names
([indexing.md](indexing.md), "The index-family registry"), by its tag `f` and a token
`path` from the family's root, so a store that implements the protocol answers every
family. One read reaches past the methods: a taxonomy probe forks the `KvBackend` the
families live in (`mount/fork-families`, below), found by `kv-backend-of` or under the
store's `:roots`. A probe runs at a `genl` assert while a stored rule carries a negative
edge (`checks/edge-negation-cycle`), and over an out-of-tree store keeping no `KvBackend`
that assert throws `:unforkable-index`. In a trie or count trie a **node** is the path
above the context and a **leaf** is the node plus the context; in a flat set the path is
the key's tail (`[:argument-slot pos term]` is `f` `:argument-slot`, path `[pos term]`).

| method | trie, count trie | flat set |
|---|---|---|
| `(family-count idx f path ctxs)` | `every-context`: the node's count; a set: the summed leaf sizes over its children in `ctxs` | the set's size; a set of contexts: the summed sizes of `(conj path c)` |
| `(family-children idx f path ctxs)` | the node's children, kept to `ctxs` on the smaller side; a set with `every-context`, else a vector | the members, kept to `ctxs`; a set with `every-context`, else a vector |
| `(family-child-count idx f path)` | how many children, no set built | the set's size |
| `(family-leaf idx f path)` | the leaf at exactly `path` | the set |
| `(family-member? idx f path x)` | membership in that leaf, no set built | membership |
| `(family-handles idx f node ctxs)` | the union of the leaves under `node` over its children in `ctxs`; one context answers its leaf as stored | the union of `(conj node c)` over a set of contexts |
| `(family-apply! idx ops)` | see below | see below |

`ctxs` is a set or `p/every-context`, and nil throws `:bad-args`, so a read past a
reader's ancestor set names the sentinel at its call site.

`family-apply!` takes `[:post f leaf-path h]` and `[:retire f leaf-path h]` and lands them
as one `kv-batch`. A count-trie post adds `h` to the leaf, the context to the node's
children and one to its count, and enters the root set (the family's `:root`) when
the node was empty; a retire undoes each of them where it empties. A flat-set op adds or
removes the member, and the root set follows the set's first and last member. A
count-trie retire's leaf path may end in `p/any-context`, which retires `h` from whichever
context's leaf holds it; a flat set keeps no list of its contexts, so its retire throws
`:bad-args` on one. The reply per op is the node's count (a set's size) after it, or nil when it
changed nothing. **The batch equals its ops applied one call at a time, in order**: each op
is decided against the store as the ops before it left it, so two posts of one handle are
one post and a retire after a post cancels it
(`index_test/a-family-batch-equals-its-ops-applied-one-at-a-time`). The trie is written
by `index-sentex` alone, and `family-apply!` refuses it.

A read or write that is one family method under another name is no method of its own.
`vaelii.impl.reads` answers the context root, the term index and its term-name set, the rule
indexes and the re-check index over `family-leaf`, `family-count`, `family-member?` and
`family-handles`. It composes the predicate-agnostic argument reads from the slot predicate set
(`:argument-slot`, or `:unary-slot` for the unary slice) and one `:argument-root` node per
predicate in it, and `rules/index-rule`, `rules/unindex-rule!`, `rules/index-exception`
and `rules/unindex-exception!` write the rule and re-check families through
`family-apply!`.

`KvIndexStore` answers the seven over the registry, dispatching on the tag with a `case`
the registry generates. `ColumnarIndexStore` answers `:trie` from its native trie and
hands every other tag to its embedded `KvIndexStore`. The methods tally nothing: the
`vaelii.impl.reads` entry point that calls one tallies the logical read it serves
([profile.md](profile.md)).

**The three record fetches are counted.** `get-sentex`, `get-justification` and
`get-provenance` each tally against their kind through `vaelii.impl.profile`'s
`:fetches` — the record-store twin of the `:reads` tally the index keeps, and its own
number because the two move independently. The worked case is `kb/find-sentex-handle`,
which asks the trie where one sentence is stored. Asked with `p/lookup`, a variable in the
path is a **wildcard**: the walk fans over every stored sentex of the same shape and the
caller reads the record behind each to find the one that is actually this sentence — one
index read by `:reads`, unimpeachable, and a few milliseconds per call at 800 candidates.
`p/leaf-at` is the exact read that answers the same question in one, at ~10 µs and one
record read per sentex at that one leaf (none for a ground sentence), and the `:reads` count is identical either way. On the durable store
each of those
fetches is a positional slot read, a positional frame read and a nippy thaw past the LRU —
orders above what any index read costs. `test/vaelii/record_fetch_cost_test.clj` is the
regression test: a non-ground `handle-of` must fetch **no** records, whatever the extent of the
pattern's shape.

The tally sits on the protocol method rather than inside a backend's own fetch, so it
counts what a caller asked for and not what a backend does to answer: the durable store
re-reads a record inside `mark-premise` where the RAM one reaches into its state map, and
a number covering both would be a reading of which backend is running. An overlay fetch
that consults the fork and then the base counts twice, which is what a fork costs.

A `KB` record bundles the two stores with eleven other slots the engine hangs off one
value — the prover registry, the solver, the naming policy, the feed, and a `Reasoning`
value whose own slots hold the contradiction and violation bookkeeping, the settle and
chain statistics, the resident qualitative networks and the match caches. **The engine programs against these protocols and never against a
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
exception is the `:disk-snapshot` image ("The image", below), which is off by default and
`mmap`s the leaf handles and the routed roots' postings rather than reading them onto the
heap.

One space number (`:space`, default 0) namespaces both stores so several KBs coexist in
one process; each backend uses it as it sees fit — the memory backend keys its registry
by number, the disk backend derives a directory from it. **One number, not one per
axis**: the index is a function of the records, so the two are shared or separate as one
thing, and each backend keys a registry of its own, so no KB can be given a private
index over records it shares.

**The space is a whole number 0 or more, or a keyword, a symbol or a vector**, and
`open-kb` refuses any other value (`:unknown-option`, `:mismatch :bad-value`). A keyword,
a symbol or a vector names a private space no number can name, and a test takes a
`gensym`. An ephemeral `fork` and a `kb-diff` side read from a path open on an **engine
space** (`mem/engine-space`), which no entry point hands to a caller, so `close!` of that
KB drops the space from every RAM registry. Every other RAM space stays in the registry
for the life of the JVM, because a second KB over the same space is how a store is
reopened; `clear!` empties it.
The refused values are the ones that name a store the caller did not spell. A string keys a
RAM store of its own but derives the directory of the number or symbol it prints as
(`"3"` and `3` are both `space-3`); a present `nil` is what `(:space cfg)` answers for a
missing key, and opens neither space 0 nor anything else anyone named. `:dir` is a
non-blank path string or a `java.io.File`: a blank path resolves against the JVM's working
directory. `:base-stores` is the `{:records :index}` pair of open stores `fork` hands over
from a live KB, and anything else is refused before a protocol call throws on it.

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
carrying `:axis`, `:kind` and a `:mismatch` that tells them apart
([troubleshooting.md](troubleshooting.md#open-kb-refuses-an-unknown-backend)) — but a
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
recovery walk does not make. `capabilities/recovery-hint-chunk` is the size. The
membership placement pass hints the same way, a chunk of terms at a time
([nmtms.md](nmtms.md#the-placement-pass)), and so does the settle's subsumed-mint
withdrawal, a chunk of candidate mints at a time
([argtypes.md](argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on)).

### The enumerations, and what a handle set costs

`sentex-ids`, `justification-ids` and `premise-ids` answer **a `java.util.Set` of
handles** — and the gap between that and *a Clojure set of handles* is the whole of what a
store may decide for itself. The protocol promises what the engine does to them:
`contains?`, `count`, `seq`, `sort`, and `=` against another set. `conj`, `disj` and
`clojure.set` are not on the list, so a caller wanting those converts with `(set …)` and
the copy is paid at the call site that asked for it — [why a Set, not a Clojure
set](defenses.md#the-enumerations-promise-a-set-not-a-clojure-set).

`vaelii.impl.handle-set` is the substitution that licence exists for: the same handles as a
`Roaring64Bitmap` behind a `java.util.Set`, at a fraction of a `PersistentHashSet<Long>`'s
residency. It is a `java.util.Set` precisely so that no caller can tell the difference,
and `enumeration_shape_test` is where core proves it: one session run
against a store answering handle sets and one answering Clojure sets, compared at the KB level
— beliefs, answers, `reindex`, `recover`, `export!` — rather than at the protocol call.

**The memory store answers Clojure sets**, because that is what its own state already
is — its key set and its premise set. What a store *holds* is a separate
question from what it answers, and the disk store's live-handle sets and premise set are
where the two come apart.

**The disk store holds its live handles as compressed bitmaps.** One per kind — sentexes,
justifications, provenance — resident for as long as the store is open, and the four
things they are asked are the four a bitmap answers directly: membership (`kill!`),
iteration (`sentex-ids`), cardinality (`sentex-tally`) and a first handle (`a-sentex-id`).
As a `PersistentHashSet<Long>` those sets retain **48–75 bytes a handle** (measured with
jol; the hash trie's fill varies with cardinality), which `lein bench-budget` carries to
**9.47 GB at 100M sentexes and j/n 1.1** — the second-largest resident row in the engine,
before a single record is fetched. The same handles as a `Roaring64Bitmap` measure
**33.0 MB**, still linear across both of the bench's steps
([density.md](density.md#the-budget-at-100m)). It is the form the allocation gives them:
`next-id` mints in assertion order, so a kind's live set is a strided run through the
handle space with holes where records were deleted.

`sentex-ids`, `justification-ids` and `premise-ids` hand back the snapshot itself, an
immutable `HandleSet`, so a call allocates the bitmap's size rather than the extent. A
caller that wants `conj`, `disj` or `clojure.set` converts with `(set …)` and pays the
extent at that call site.

The bitmap is mutated in place and is not thread-safe, so **a read of the live set takes
the kind lock**, which the boxed set did not need. That is the whole price: a tally and a
first handle are O(1) under a monitor the writer holds only for two file writes, and a
read that hands the set onward takes a snapshot inside the lock — a bitmap copy, costing
the handle set's size rather than the corpus's. Left unsynchronized the failure is real and
measured, not theoretical: an iterator over a bitmap being written throws
`ArrayIndexOutOfBoundsException` once the handle space is spread widely enough for the ART
trie to restructure under it, which a store whose handles interleave with two other kinds'
is (`disk_record_store_test`, the live handle set beside a writer).

The kind lock is a `ReentrantReadWriteLock`, not a bare monitor. The live-set read above,
and every write — `store!`, `kill!`, `mark-premise`, compaction, `close` — take it
exclusively (the *write* lock, the same mutual exclusion the monitor gave). A single-record
`fetch` (`get-sentex`/`get-justification`/`get-provenance`) takes the *read* lock instead:
two positional reads are safe against each other, so the lock only has to serialize a read
against a concurrent append + slot rewrite, never one read against another. Fetches from
two reader threads therefore run in parallel rather than funnelling through one monitor;
the engine's own bulk sweeps — `export!`, `reindex`, the `recover` read side — each fetch
on one thread. `fetch` never takes the write lock, so a
read cannot upgrade and deadlock against itself.

The premise set is a `LiveHandleSet` too, and still resident. A premise is a sentex handle,
so the set sits under the sentexes kind lock for reads and writes alike. A handle joins it
after its record lands, in a second acquisition, so a write that fails leaves no handle in
`premise-ids` whose `get-sentex` is nil.

### `Tallying` — the questions that do not need the handle set

`(count (sentex-ids store))` is how the engine asks *how many records is this*, and
`(first (sentex-ids store))` how it asks *does this store hold anything*. On a store whose
enumeration is a read of its own state, both added no work. On one whose enumeration is a
**query** they cost the whole table — every handle over the wire and a handle set built out of
it, to answer with one number — and `open-kb` asks them before the KB has answered
anything: the durable index's coverage check counts the records, and the recovery branch
asks whether there are any.

So a store that can answer without enumerating implements `Tallying` — `sentex-tally`,
`justification-tally`, and the three `a-…-id` samplers — and every caller goes through
`capabilities/count-sentexes`, `count-justifications`, `some-sentex-id`,
`some-justification-id` and `some-premise-id`, which **fall back to the enumeration**. A
store without the capability therefore reads exactly as it did before the capability
existed, which is what lets the engine call the helpers unconditionally.

Only the questions the engine actually asks are on the protocol — there is no premise tally and
no general sampler — so an implementer knows each op there is worth a statement. *Which*
handle a sampler returns is the store's own choice: every caller either tests it for nil or
reads the record to prove the build can read records at all, and none depends on which one
came back.

### `BulkLoading` — the protocol an import writes its records through

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
put](defenses.md#the-bulk-load-protocol-is-a-sink-not-a-batched-put).

The one restriction that buys this: **do not read a record back before the sink is
closed.** A sink may hold everything it was given until then. Neither import path does,
which is asserted rather than commented — the test wrapper's `get-sentex` throws on a
handle a sink still holds.

`capabilities/sentex-sink` and `justification-sink` are the callers' entry point, and they fall back
the way `Tallying`'s helpers do: a store with no capability gets a sink that is
`put-sentex` per record plus the premise mark, which is the loop the import paths ran
before. `{:premises? bool}` is the one option — whether a record carrying a `:strength`
joins the premise set by the write. The records-only pass marks inline and says true; the
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

`mark-premise-batch` and `put-provenance-batch` are the protocol, and
`capabilities/mark-premises` / `put-all-provenance` are the callers' entry point with the same
fallback: the loop, on a store that implements nothing. It is a **separate protocol from
`BulkLoading`** rather than two more ops in it, because a store may be able to load
records in bulk without being able to bulk-update rows that are already there, and a
half-implemented protocol fails at the call rather than at the `satisfies?`.

Neither op changes what the per-handle version does. A handle with no sentex is still not
marked — over Postgres the batch statement `RETURNING`s the ids it actually touched, since
an update count over a batch cannot say *which* rows matched and a strength cache filled
past that would answer for a handle `premise-ids` does not name.

The `:disk` store's `mark-premise-batch` decides each handle from its idx slot, and reads
the slots in handle order, so the reads walk the idx and the log forward. A slot whose
strength rank equals the wanted strength's is a mark already on disk, and the handle
joins the premise set without its record being paged. An import's sink writes each record carrying its
strength, so its marks page no record. A slot whose rank is unrecorded or different sends
the handle to its record, which is read without the hot-cache put and re-stored when its
`:strength` differs. `lein perf`'s `bulk-premise-mark-record-size` holds the cost per
handle flat in the size of the record.

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
the inline index build — and the store's sink, handed records directly, runs at 122.6k/s
against that. A server-backed load is now **faster than the local disk backend**, which is
the sentence that was not true before.

The belief path (`{:belief? :stored}`) is the same dump with the marks and the provenance
on top, and it is `BulkAnnotating` that carries those: **3,038 → 10,343 records/s** over
Postgres on the 10k corpus — 3.4×, one statement for every premise mark and one per 1,000
provenance maps in place of 20,000 round trips. The index rebuild remains there,
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
| `:pg-snapshot` | durable (Postgres) | native trie, **mapped from a local image** | `:disk-snapshot`'s two images, kept on the writer's host and fingerprinted by the adapter |
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
  `VAELII_TEST_BACKEND=disk-log lein test` (durability parity check: identical results).
  Detailed below.
- **SQLite records** (`com.vaelii/sqlite`, the `vaelii.sqlite.record-store` adapter) — an
  embedded-SQLite store in a single file (`<dir>/records.sqlite`) under `:dir`, durable
  across a restart with no server. It is **not built into the engine**: `record-store-for`
  resolves it lazily (`requiring-resolve`, the way `create-tms` reaches the dense TMS), so
  the SSPL engine carries no JDBC dependency, and the `:sqlite` backend works only when the
  Apache-2.0 adapter is on the classpath — selecting it without one is `:type
  :missing-adapter` naming the `:coordinate` to add, a missing dependency rather than an
  unknown backend. It pairs with a derived RAM index (the `:sqlite`
  sugar is `{:records :sqlite :index :memory}`), rebuilt on open; a `:disk-log` index
  over it is refused, the same rule RAM records meet. Outside the built-in grid below — not
  one of the eight pairings, and the adapter carries its own suite.
- **Postgres records** (`com.vaelii/postgres`, the `vaelii.postgres.record-store`
  adapter) — the records in a database an operator already runs, named by the `:pg` opt
  (a next.jdbc db-spec or a JDBC URL, with an optional `:schema` so one database holds
  several KBs). Resolved lazily exactly as `:sqlite` is, so the SSPL engine carries no
  JDBC dependency, and absent it refuses the same way with `:missing-adapter`. What a server buys and what it does not is
  [below](#postgres-records-pg-memory-pg-disk-log); the short version is that it buys `COPY`,
  an operator's existing backup and replication, and a store bigger than one disk — and
  it does **not** buy a shared KB. Outside the built-in grid below, as `:sqlite` is: the
  adapter carries its own suite, `VAELII_TEST_BACKEND` does not name it, and
  `backend_parity_test`'s "identical across every pair" is a claim about the pairs that
  run by default and not about this one — a backend whose tests need a server is covered
  by the adapter's own run against one, not by the matrix.
- **An adapter from this repository.** The `+with-sqlite` and `+with-postgres` profiles
  add the released adapter jar to any lein task, and the jar's pom brings its drivers:
  `lein with-profile +with-postgres browser`, or `lein with-profile
  +with-postgres,+with-sqlite uberjar` for a standalone jar that opens both. The default
  `lein uberjar` and the published pom carry neither. `scripts/link-checkouts.sh` links
  the adapters' live source, which shadows the jar's namespaces. A link without the
  profile has no drivers, and selecting the backend then refuses with `:missing-adapter`,
  naming the namespace that failed to load.
- **A derived index** — the RAM map, the dense postings, the columnar trie — holds
  nothing that is not recomputable, so it is never written. Over durable records that
  costs one `reindex` per open (below); in exchange, every density experiment can be run
  against a durable KB instead of only in RAM.

The two built-in axes admit ten pairings and **eight are legal**, each with a name:
RAM records under the durable index or under the image is refused — [why that pairing is
refused](defenses.md#ram-records-under-a-durable-index-is-refused). The rule the refusal
states is that **the `:disk-log` index needs durable records**, which is why `:pg`
may take it (`:pg-disk-log`) and `:sqlite` may not: `:sqlite` records already live in a
directory, so a durable index beside them is `:disk-log`'s pairing without its shared
lifecycle, and `:disk-log` is the name for that. So `:records` /
`:index` are for overriding *half* of a name, not for reaching a pair the table left out,
and `VAELII_TEST_BACKEND` takes a name. `./scripts/test-backends.sh` (`lein
test-backends`) runs the whole suite on all eight, one log and one ✔/✘ per run, plus a
ninth over the `overlay` decorator; `./scripts/test-matrix.sh` runs those nine and the
seven sweeps concurrently, which is the same coverage in a fraction of the wall
clock, since a durable run's store is `<vaelii.disk.dir>/space-<n>` and each gets its
own directory. A bare matrix run is the **routine** configuration set, which stands two of the
three durable-records-with-a-derived-index pairs down — one claim written three times,
and `mixed_backend_test` holds the protocol in an ordinary `lein test` — and `full` is all
sixteen. `./scripts/test-matrix.sh --owed` runs what the changed files owe and prints
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
TMS and taxonomy *by reading the index* (`special/rebuild-taxonomy` reads the supporter
families), so over an empty one it would recover an empty KB and report nothing wrong. The
repair is `reindex` — rebuild the index from the records, *then* recover — and
every recovering mode (`:trust`, the default, `:auto`, `:background`) runs it and logs how
long it took.

That log line is the point of interest: the rebuild is O(records) on **every** open, so
whether it is worth buying back — by persisting a snapshot of the derived index, which
is what `:disk-snapshot`'s image below does — is decided by that number at the corpus
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

- **No belief.** Every definitional check the assert entry point runs bottoms out in `jtms/in?`,
  so over an empty network they all match nothing and pass vacuously — and nothing
  re-runs them later, so the store keeps content its own constraints forbid. `recover` is
  the repair.
- **No index.** `assert` dedups through `p/leaf-at`. Over an index that opened empty every
  assert misses and mints a **second handle for a sentence already stored**, and
  `reindex` cannot merge the two afterwards because they are two records rather than two
  index entries. `reindex` is the repair, and `recover` alone is not — it reads the index
  rather than writing it, which is the same reason it is not the repair for a read.

So the write entry points — `assert`, `assert-inert`, `retract!`, `edit!`, `preview` — refuse
such a KB by name (`:unrecovered-kb`), reporting which of the two hold and naming the
call that clears them. The ex-data carries **`:hazards`**, a sorted vector of
`:no-belief` (the TMS is empty, so every definitional check passes vacuously) and
`:no-index` (the derived index opened empty, so dedup misses and every assert mints a
second handle for a sentence already stored), plus `:operation` and `:repair` — `recover`,
or `reindex` where the index is the empty one, which `recover` alone does not fix because
it reads the index rather than writing it. `check` and `check-edit` report the same
refusal as a problem, since they answer for the entry point.

`retract!` has two refusals of its own underneath that one, both about a handle the TMS
has no node for. A **stored premise** is not an inert sentex however alike they look to a
node test, and the dependency sweep a retraction owes cannot be computed over a network
that was never built (`:unrecovered-premise`). A **derived** record is the third case and
is told apart from neither: it carries no strength, so the premise set does not name
it, while the store holds the justifications that concluded it and any naming it as an
antecedent — and the store keeps no index from a handle to the justifications citing it,
so nothing per-handle can separate it from an inert one. Where belief was never built the
teardown is therefore refused for every record (`:unrecovered-kb`); where it was built, a
record with no node genuinely is inert. `vaelii.core/*write-unrecovered?*` accepts the
first kind of write anyway for a caller who has read what it costs; nothing accepts the
teardown of a handle whose dependents cannot be computed. `*bulk-load?*` deliberately is
not that opt — it skips the dedup walk that is already missing.

`preview` refuses where `edit!` does, which is the point of it. It implements a `:remove`
as a premise suspension conditional on `jtms/premise?`, false for every stored handle here, so
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

**It pairs with records whose store fingerprints its records for an image**
(`p/ImageFingerprinting`): `:disk`, whose fingerprint is a reading of its own slot files
taken under its own kind locks, and `:pg` (`:pg-snapshot`), whose adapter keeps one row a
trigger moves in the same transaction as every write. So `{:index :snapshot}` over
`:memory` or `:sqlite` records is refused with `:unknown-backend` (`:mismatch
:illegal-pair`), and a `:pg` adapter that predates the protocol is refused at open with
`:missing-adapter`.

**It is a representation, and it is not a promise that the image is valid.** Those are
two different things and the name carries only the first. What `{:backend
:disk-snapshot}` says is that this KB's index is meant to be read from bytes rather than
rebuilt — recorded in the opts map, where a reader of the KB's own configuration can see
it. What it does *not* say is that an image will be there: the fingerprint is checked on
every open, any doubt discards it, and the KB reindexes and answers correctly. The
difference a name makes is that such an open **warns**, naming the mismatch class, rather
than passing for a fast one that quietly took an hour.

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

**Only `assert` reaches the cadence.** The cadence check runs at the write entry point, so a store filled
by `reindex` or by the importer's inline bulk load — both of which post through
`reindex/index-one!` to `p/index-sentex` directly — never crosses it, and gets exactly one
image, at the close, whatever the threshold says. A batch build is therefore already on the
cadence it wants without asking for anything.

**A recover from the records defers it.** The settles of `recover` write sentexes, and an
image written part-way through them is stale before the recover ends. `kb/*defer-index-refresh?*`
is true while they run, `refresh-index-image!` writes nothing, and `recover` offers the
refresh once after them (the floor and the threshold still decide whether it writes). A
process killed during the recover reopens from the records. A background rebuild runs its
settles on a second KB that holds no image directory (`kb/rebuild-own`), so they write no
refresh; its install writes the reasoning image, and the index image waits for the next
write that crosses the cadence.

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
is written with the disk record store's slot fingerprint and checked on every open — never
behind a flag — and any doubt at all (format, `kv/index-layout-version`, byte order,
records that moved, a short section, a missing commit marker) discards it and runs the
same `reindex` above. That is what makes the backend safe to name: the index is
recomputable from the records, so a discarded image costs time and never an answer.

The slot fingerprint reads each slot's handle, offset and length, and no record content.
`clear!` truncates the logs, so a record written after it lands at an offset a removed
record held, and a record of the same byte length reproduces that record's slot exactly.
So `clear!` mints a random **epoch** into the store's `counters.nippy` blob, and the
fingerprint carries it (`record-store/clear-records!`). A store no `clear!` has emptied
carries none, and its fingerprint is the slots alone.

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

#### The reasoning image

The index image is one half of a `:disk-snapshot` cold open; `recover` is the other. A
`:disk-snapshot` KB on the dense network writes its whole reasoning state to `<dir>/reasoning/`,
and the next open installs it in place of the recover (`vaelii.impl.reasoning-image`):

- `network.bin` — the dense network: every node, justification column (the subsumptions
  column among them), label,
  defeat-class, block, forced set and supersession (`dense-jtms/write-image`), keys in sorted
  order so two images of one network are equal bytes;
- `state.nippy` — the taxonomy's relations and caches, less the slots the live KB owns
  (`reasoning-image/taxonomy-side-slots`), and the KB atoms recovery fills or the closing
  settle leaves (`reasoning-image/state-atoms`), the placed nogoods' handle sets among them;
- `manifest.edn` — what the image is valid against, written last, so a directory with no
  manifest holds no image.

**The manifest** holds the two layout numbers, the records'
`record-store/reasoning-fingerprint`, the **source identity** of the engine code that
derived the belief ([glossary.md](glossary.md)), and the three policies that move belief:
`VAELII_ASSERTIVE_ARG_TYPES`, the forced-monotonic declarations the store holds
(`reasoning-image/declared-forced`, [nmtms.md](nmtms.md#the-forced-monotonic-set)), and
the reasoner set the store records ([The reasoner set](#the-reasoner-set)). The
records fingerprint reads the justifications kind's slots beside the sentexes kind's,
where the index image's `slot-fingerprint` reads the sentexes alone: a justification
stored over sentexes that did not change moves belief and not the index. A premise mark
re-stores its sentex, so the sentex slots cover it. Both fingerprints carry the clear
epoch described above, so an image of records a `clear!` removed is declined.

**An open installs the image** only when every part of the manifest equals the KB's own, the
KB's provers are the defaults and the shipped reasoners its store records, its solver is the
default — a registered prover or evaluatable runs code the source identity does not cover —
and both sections read in full into a scratch network before anything moves into the KB's
own. Any mismatch, a registered prover, or a torn
section leaves the KB to the full recover, which then writes a fresh image. The install
thaws `state.nippy` and the network's object frames under `io.thaw/sharing`: each symbol is
the symbol pool's and each handle one `Long` per value in a section, so the installed KB
holds one object where the KB that wrote the image held one. A declined image
costs the recover and never an answer, because the recover it falls back to is the path an
open without an image runs. `lein cli upgrade --dir <path>` (and `scripts/upgrade-kb.sh`)
performs that open and a close for a store, so the recover a changed engine owes is paid
once, ahead of the next open ([operations.md](operations.md)). Its `--verify` recovers
anyway and compares the new image's believed sets with the old one's.

**A heap failure fails the open and declines nothing.** A `VirtualMachineError` while
either image is read, an `OutOfMemoryError` above all, is rethrown as itself, including
one nippy wrapped as a failed thaw (`io.thaw/vm-error`). The image may be sound, and the
recover or reindex a declined image starts needs more heap than the read that ran out. A
cache in `state.nippy` that runs out of heap fails the open the same way. An open that
throws closes the directories it opened without writing either image
(`disk.backend/close-dir!`'s `:images? false`), so the next open reads the images the
failed one found.

Nothing installs an image whose source digest differs from the running engine's, except
`:recover? :background` (below), which rebuilds belief behind the image it installs, and
`:recover? :trust` and a dump's import (both below), which keep it. A caller
that believes a particular source change moves no belief has no way to say so, by design:
the digest is the only check standing between an engine edit and belief computed under
the code before it, and the identity has been wrong in that direction before.

**An image is written** after a full recover, and when the directory closes if the records
moved since the image on disk was written. The records fingerprint is read before and after
the sections are written, and an image whose records moved during the write is abandoned.
The sections are written to temp files beside the image on disk and renamed over it only
once both are complete, so a write that throws or runs out of heap, at a close or a seal,
leaves the image the directory held installable. A
KB opened over an empty store registers the close-time write at open, since it builds its
belief assert by assert and never recovers. A KB holding a stored sentex that is no network
node and carries no `:inert` provenance mark (a loader filled it and skipped the recover)
writes none, and recovers at its next open. An `assert-inert` record has no node and carries
the mark, so a KB holding one writes an image. A recover makes no node for a record carrying
the mark either, so the image a build writes and the image a recover writes hold one node set
(`reasoning_image_test/an-inert-sentex-is-imaged-and-reopens-stored-and-not-believed`), and
`upgrade --verify` of a freshly built store reads `:labels :same`
(`cli_test/the-first-verify-of-a-freshly-built-store-reads-the-labels-the-build-wrote`).

**Rebuilding behind an image.** `open-kb` with `:recover? :background` installs an image
whose manifest differs from the KB's only in its source digest, which is the image an
earlier engine build wrote over the same records under the same policies. The open then
returns, and the KB answers from that image. Belief is rebuilt under the running build on
a daemon thread, over a second KB (`kb/rebuild-kb`). The second KB takes the records, the
index, the provers, the solver, the naming policy and the constraints from the open KB
(`kb/rebuild-shared`). It holds its own directory fields, operation log, change feed and
hazard record (`kb/rebuild-own`), and starts with an empty `Reasoning` value
(`kb/empty-reasoning`). A KB field named in none of the three is not copied, and
`background_rebuild_test` fails on one. When the rebuild finishes, its belief replaces the
installed belief: a KB holds its network, taxonomy and derived atoms as one `Reasoning`
value in a volatile (`vaelii.impl.types.reasoning`), and the install is one `vreset!` of
it. The image is then rewritten under the running source, and the change feed receives the
handles whose belief the replacement moved (`dense/moved-between`). Until then the KB
reports `{:stale-belief true}` from `write-hazards`, and every write entry point refuses
with `:unrecovered-kb`, `*write-unrecovered?*` included: a write would be checked against
the earlier build's belief, and the rebuild might not see its record. While the install is
pending, every public read entry point in `vaelii.core` runs against `kb/read-copy`, a
copy of the KB holding the belief the read began with. A read that begins before the
install reads the installed belief to its end, and a lazy sequence it returns reads that
belief when realized; no public read sees the network of one belief beside the taxonomy of
the other. A KB with no install pending is passed through unchanged after one atom read.

**Trusting an image.** `open-kb` with `:recover? :trust`, the default, installs the same image
`:background` would, and keeps it: no rebuild runs, the KB is writable at once, and
`write-hazards` reports no `:stale-belief`. Belief moves under the running build only where
a settle reaches, so a record no write touches keeps the label the earlier build gave it,
and `recover` re-derives all of it under this build on demand. An image whose candidate
index carries no argument family, written by a build without that family, installs
with the family adopted as read (`argument/installed!`): the first settle decides only the
declarations and terms its writes queue, and reads no declaration whole
(`reasoning_image_test/an-image-without-the-argument-family-installs-with-no-whole-argument-read`). The first settle after the
install draws no withheld mint a departure releases, as no settle `recover` runs does: the
image carries the owed releases, and `release-withheld!` draws them
([argtypes.md](argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on)). The close-time image write
records the source the image was read under, not the running one, so the image goes on
naming the source its belief was last derived under in full: a later `:auto` open still
declines it, and a later `:trust` open keeps it again. The open logs
`::reasoning-image-trusted` with that source. It is the default because the engine source
moves with every commit to belief-deriving code, and under `:auto` each one turns the next
open of every store into a full recover, an hour or more at millions of sentexes. A caller
that needs belief this build derived in full says so: it opens with `:auto`, calls
`recover`, or runs `lein cli upgrade`, which opens with `:auto` and writes the image the
next trusted open installs as current. An open with `:oplog?` and no `:recover?` takes
`:auto` ("The operation log").

**The rebuild writes no record.** The rebuild KB reads the open KB's record store through
`overlay.frozen/frozen-records`, which refuses every write with `:unrecovered-kb`, so no
record and no index posting is written from the rebuild's thread. The index
`:disk-snapshot` reads is the columnar one, whose fields are unsynchronized (see "The
single-writer contract"), and a caller's read walks it while the rebuild runs. A rebuild
whose closing settle, or whose re-fire of the rules that can refuse, places a conclusion
the image's records lack ends at that write as a rebuild that throws does (below), with a
message naming `recover`. The KB keeps answering from the image with writes refused, and
does not become writable until a caller runs `recover`, which rebuilds on the calling
thread and writes the conclusion there. `background_rebuild_test` asserts both. The rebuild
stops when `close!` closes the directory or `recover` is called; `recover` then runs the
rebuild on the calling thread. The rebuild reads a stop request during the network
replay, after it, before the closing settle and before the install. It reads none inside
the taxonomy replay or the settle, so a `close!` can wait out a whole step. `close-dir!`
waits before it takes the process-wide store registry's monitor, so the wait delays that
close alone and no other directory's open or close. An image declined for its records, its layout or its policies is not
installed, and the open recovers as `:auto` does. The browser, the daemon and the CLI open a
store with the default (docs/web.md).

`core/rebuild-progress` reports where a rebuild has got to: the step running, of nine
(the seven steps of a recover from the records, the install, and the image write), the
time since the rebuild began, and the source digests of the image and of the running
build. Each step
is logged at `:info` as it begins. A recover from the records records its step timings in
the KB, and the manifest carries them as `:recover`, which `decision` does not read; an
installed image hands them on to the next image the KB writes. Against an image's
`:recover`, `rebuild-progress` answers `:fraction`, the share of that recover the steps
done so far took. A recover with no rebuild around it logs its seven steps at `:info`
over a store of a million sentexes or more, and at `:debug` below that.

**A rebuild that throws** is logged at `:error`, and the KB keeps answering from the image
and refusing writes, since `:stale-belief` still holds. `rebuild-progress` keeps reporting
it with `:failed` added — `{:at :class :message}` — the step it was in, and its time
stopped at the throw, so a caller polling progress can tell a failure from a rebuild that
is not running. A `recover` clears the record and rebuilds belief on the calling thread;
`background_rebuild_test` injects the throw.

Measured on a large `:disk-snapshot` store by `lein bench-recoverphase beliefimage <dir>`:
the open that installed the image took under a tenth of the time of the open that ran a
full recover and wrote it, and writing the image took under 3% of that recover. The two
opens agreed on `in?` for every handle and held the same clash pairs.

**A dump carries one too.** `export!` writes the same three files under `<dump>/reasoning/`
by default (`:belief? false` omits them), and `import!` with `{:belief? true}` installs
them in place of the recover it would otherwise run. A dump image written under another
engine source is installed and trusted as `:recover? :trust` trusts a store's, and the
summary's `:reasoning-image` names that source under `:trusted`: a dump moves a KB between
stores, and a recover on landing would redo the derivation the dump carries. The records half of a dump image's
fingerprint is content rather than slots, because a dump lands in a different store: the
export folds `fingerprint/record-hash` over the sentex frames and
`fingerprint/justification-hash` over the justification frames it writes, and the import
folds the same two over the records it lands. The network is read after both walks, so the
export writes no image when the change clock moved during it: a write between the walks
and the network would put those records' fingerprints on labels the streamed records
never had. The import tries the image only when it kept every handle the dump gave, since
the network names its nodes by handle; the summary's `:reasoning-image` reports
`{:reasoning :installed}` (with `:trusted` when the image's source differs) or
`{:reasoning :recovered :reason r}`.

An installed image is the state of the KB that wrote it: its labels, which equal a recover's
because belief is order independent, and its derivation depths and settle readings, which a
recover rebuilds from the records instead of reading. Why an image is installed whole or
discarded whole, and never reconciled against the records:
[defenses.md](defenses.md#a-reasoning-image-is-installed-whole-or-not-at-all).

#### The operation log

`open-kb` with `:oplog?` attaches an **operation log** to a `:disk-snapshot` or
`:pg-snapshot` KB (`vaelii.impl.oplog`, `vaelii.impl.seal`). Each outermost public write
is appended to `<dir>/oplog/ops.log` as the call that made it, and a **seal** writes the index image and
the reasoning image and starts the log's next generation. An open after a crash installs
the images the last seal wrote and replays the operations logged since, in place of the
index rebuild and the recover the records would otherwise need.

| `:oplog?` | log | an operation's frame reaches the disk |
|---|---|---|
| `false` (the default) | none | — |
| `true`, `:each` | attached | fsynced before the operation runs |
| `:tick` | attached | on the durability daemon's tick (`vaelii.disk.sync-ms`), and before the operation writes a record the log's generation began with |

The log is read on `{:backend :disk-snapshot}` and `{:backend :pg-snapshot}` with
`:recover? :trust`, the default, or `:auto`. Another backend, a `:recover?` of
`:background`, `:warn` or `false`, and a value outside the table are refused with
`:unknown-option`: a restore installs the images only the `:snapshot` index keeps, and an
open with a log builds belief one way or the other. Under `:trust` a restore installs and
keeps a reasoning image written under other engine source, as an open without the log does
("Trusting an image"), and each seal's manifest names the source that belief was last
derived under in full. The browser opens a `:snapshot` store it recovers with `:oplog?
true`. Over `:pg-snapshot` the log, the seal and both images are files under
`:dir` on the writer's host, and the seal's fingerprints are the adapter's counter row.

**An open.** A directory holding a seal (`<dir>/oplog/seal.nippy`) is opened `{:recover? false}`
and restored (`seal/restore!`): both images install against the fingerprints the seal
records, and the frames of the current generation replay through the public write entry
points, each replayed write checked against the record stored at its handle. A clean close
seals, so the open after it replays no frame. The restore declines when the log is
unusable, the log holds no frame and the records' `belief-fingerprint` differs from the
seal's (`:records-moved`: a second `:pg` KB over the same schema wrote them), an image
does not install, a replayed write differs from the stored record, the store holds a
record no replayed frame accounts for, or after a replay the network and the records
disagree on a handle: a node or a justification with no record, or a premise mark one of
the two holds and the other does not (`:records-moved` as well). A replayed frame writes a
record it finds missing, so a second writer's deletion of a record a frame wrote is undone
rather than detected. The directory is then closed without writing an image, opened again
with the caller's `:recover?`, and sealed. A directory with no seal is opened and sealed
the same way. A write by a KB opened without `:oplog?`, under any disk backend over the
directory, renames the seal to `retired.nippy` and fsyncs the directory before the write
runs (`seal/retire-unlogged!`): the write reaches the records and no log, and the next
open with the log opens from the images or the records and seals again. The open
logs which path ran, at `:info` for a restore or a directory with no seal and at `:warn`
for a decline with its reason, and the log keeps the report (`oplog/opened`): `{:restored
true :frames n :ms t}` or `{:restored false :reason r :ms t}`.

**A seal** runs when `vaelii.core/seal` is called, when the directory closes, when the
index drifts past `vaelii.index.snapshot-drift`, and when a `:seal`-class operation
returns (`import!`, `clear!`, `recover`, `reindex`, `load-text!`). It writes both images,
then `seal.nippy` naming the generation, the records watermark and the two fingerprints,
then truncates the log to a header for the new generation. `vaelii.impl.seal`'s namespace
docstring lists what a crash between those writes leaves. A seal is declined, and the log
left as it is, inside an operation, inside `with-deferred-settle` and while a settle holds
the network; a declined drift or `:seal`-class seal runs after the next operation returns.

**A log becomes unusable**, and the next open rebuilds from the records, when a write ran
that its frames do not describe or a frame does not decode. The declined-restore table in
[operations.md](operations.md#after-a-crash) lists each reason the mark records. A
`:seal`-class operation's mark holds until its seal runs, and a configuration call's
(`set-solver`, `add-prover`, `add-evaluatable`, `add-reasoner`) until the next seal. The
mark is fsynced when it is appended, under `:tick` as under `:each`, so a write after it
runs only once the mark is on disk. A `VirtualMachineError` while a frame is
frozen, an `OutOfMemoryError` or a `StackOverflowError` on a deeply nested sentence, marks
nothing: it propagates as itself, no frame is written, and the write does not run. A KB
with a registered prover or solver other than a shipped reasoner cannot be sealed, so its
log stays unusable and the next open rebuilds.

**A log that cannot take a frame stops.** A failed append, fsync or truncation latches the
log's fault, as a record store's does ("A store that stops"): the operation is refused
with `:store-unusable` before it runs, and so is every later write and `seal`, until the
directory is opened again. Under `:each`, a frame whose fsync failed can be on disk
although its operation was refused, so the next restore can replay it.

**What it costs**, measured on a synthetic store of 600,300 sentexes (300,000 facts and the
conclusion a forward rule draws from each) on an APFS SSD, where one fsync takes 5.5–6 ms:

| | no log | `:tick` | `:each` |
|---|---|---|---|
| an assert of a new fact | 0.35–0.48 ms | 0.32–0.59 ms | 6.4–7.2 ms |
| a retraction of a fact older than the log's generation | 0.30–0.44 ms | 5.7–5.9 ms | 5.7–6.1 ms |

A seal took 3.0–4.7 s at that size. An open of a copy of the live directory, which holds
what a killed process leaves, restored in 5.5 s with 100
operations logged since the seal, 8.0 s with 10,000 and 34.9 s with 100,000, against 20.9 s
for the open without a log that rebuilt the index and belief from the records at 10,000.

### The index is written once — `KvBackend`

`KvIndexStore` (`vaelii.impl.kv`) is the **generic** `IndexStore`: the whole trie /
roots / rule / exception / term-index logic lives there, in terms of a small `KvBackend`
protocol — scalars, counters, sets, an N-key `kv-intersect`, a `kv-member?` probe, and a
`kv-batch` that lands one sentex's entire path (levels, term index, roots) as one unit. A
backend supplies only that adapter:

- `MemoryKvBackend` (`vaelii.impl.memory`) — one map keyed by the logical vectors, every
  family alike; `kv-intersect` is `clojure.set/intersection`, `kv-members` returns the
  stored set by reference.
- `DiskKvBackend` (`vaelii.impl.disk.kv`) — the same in-RAM map, durable behind a
  write-ahead log (below).

**No `KvBackend` op names an index family.** A scalar, a counter, a set and an
intersection are the whole vocabulary; which families a KB indexes, how their keys are
spelled and which reads descend them are `vaelii.impl.kv`'s, one layer up. The argument
roots are the family that tests this — they are hierarchical, and the reads a settle
leans on ask for subtrees of them — and `KvIndexStore` answers all of it over the generic
ops ([indexing.md](indexing.md), §2). A backend is free to hold any family in a
representation of its own and answer those ops off it — `dense-roots` packs its keys into
longs. That stays invisible above the backend, which is what makes it a representation.
The term reaching a
key is canonical — `vaelii.impl.kv` canonicalizes at both boundaries, because a lazy seq
and the `PersistentList` it is `=` to freeze to different nippy bytes.

`kv-member?` is there for a *cost* rather than an answer. `reads/watched-rule?` — the membership
check the firing path takes once per candidate rule per new datum — asks whether one handle
is in the posting of watched rules, and a backend that packs a posting
(`vaelii.impl.dense-kv`, `vaelii.impl.dense-roots`) has to answer by probing it, not by
materializing the posting and testing the result. On the two backends above the two roads read identically, which
is exactly why nothing behavioural catches the difference: `lein perf --only
watched-rule-membership` is what defends it, and `kv_membership_test` is what says every
adapter's probe agrees with its own `kv-members`.

So a new backend (SQL, overlay) is a new `KvBackend` rather than a second index,
contract-tested by `kv_backend_test` (every adapter satisfies one spec). The one
`IndexStore` that is *not* a `KvBackend` is `ColumnarIndexStore`
(`vaelii.impl.columnar`), which implements the trie natively over CSR arrays and
delegates the flat families — roots, term index — to an embedded `KvIndexStore` on the
same keys, so the two answer alike. Every family read and write goes through the family
methods above, so any `IndexStore` holds the taxonomy's supporters and the mints
(`index_test/an-index-store-reached-through-the-protocol-answers-the-families`, a
`reify` that delegates each method). The one structural reach below the protocol is a
taxonomy probe's fork (`mount/fork-families`, [overlay.md](overlay.md)), which refuses a
store keeping no `KvBackend` with `:unforkable-index`. The **record store** stays per-backend
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
  STDIN BINARY` loads at **95.8k records/s** where the per-record entry point manages **4.1k/s**,
  and where the `:disk` store's own per-record path manages 52.7k/s. It is a *load*
  rather than an upsert — `COPY` has no `ON CONFLICT`, so a handle the store already holds
  raises, so a bulk path never overwrites a record without saying so.
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
So the index directory records the database identity on first use, and an open over
a different one is refused (`:type :stale-index-records`) rather than answered. Give each
KB its own `:dir`, or delete the directory to rebuild against the records now behind it.

`close!` releases both halves: the pool the store built, and the index directory's
exclusive lock.

### `:pg-snapshot`: the two images over records on a server

`:pg-snapshot` is `:disk-snapshot` with the records in Postgres: the index image and the
reasoning image live under `:dir` on the writer's host, and an open installs both instead
of reindexing and recovering, as it does over `:disk` records. Each image is written with
the adapter's fingerprint row — a uuid minted with the store and a count a statement-level
trigger on the record table moves with every insert, update, delete, truncate and `COPY`,
in the same transaction — so one row read at open says whether the records moved since the
images were written, and the uuid says whether they are the same records at all. The
directory is held to one database as `:pg-disk-log`'s is, needs `:dir` for the same
reason, and takes the single-writer lock itself, since no component opens there.

**The directory names its server.** Both `:pg-*` backends write into `index/records.edn`
the host, port, database and schema the index was built against, so a reopen needs only
the directory: `{:backend (v/store-backend dir) :dir dir}` with no `:pg` connects to the
recorded server, as `PGUSER` (else the OS user) with `PGPASSWORD` when it is set. An
explicit `:pg` is used as given and still has to match the records identity. The browser's
catalog lists such a directory as a store and loads it this way.

Over `:disk-snapshot` it adds the server's `pg_dump`, PITR and replication of the
records. Each record fetch the LRU does not answer is a round trip, so a settle that
reaches widely, or a full recover, runs slower than over local records. A write that
reaches the records while the images do not (a crash, another writer) moves the
fingerprint, and the next open discards both images and rebuilds.

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
  tagged](defenses.md#frames-are-positional-not-tagged).  A literal frame is
  `[tag sentence context id strength]` and a rule frame `[tag context id antecedent
  consequent strength varmap engines defeasible effect]`, with no sentence and the
  engines as one bit per engine (tags 0–3, which also carry a polarity field after the
  id, still decode, and so do the rule tags that spell the wrappers as the three fields
  `direction` / `assumption` / `constraint`, read through `sentex/fielded-rule-slots`),
  a justification frame a bare vector (one
  shape needs no tag) `[id informant antecedents consequence bindings strength]` with the
  justification's subsumptions as a seventh element when it has some (a seven-element
  frame an earlier build wrote ends in an always-empty `:out` set, which decodes as
  none), and provenance — an open application map — passes through as it
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
  The same walk tombstones a record whose tokenized body holds a code this codec does
  not write (`:malformed-record`), and logs each count at `:warn` under its own
  message.  Both are read as crash damage.  A frame tag this build does not read
  (`:unknown-frame`) is not: the open rethrows it, because a build that cannot read a
  log must not delete it.  Only symbols and
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
  one `index-sentex`'s ops — is packed into one buffer and lands in **one write**, and
  the RAM map, published after the write, never disagrees with the log about which ops
  happened in the running process. One write is not an atomic one: a crash during it can
  leave a prefix of the batch's frames on disk, which replay applies. The batch-seal
  counter (below) is what detects that prefix.
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
*open* is the one that adds no work: the cache is empty, so there is nothing to
displace.)

What that displacement costs the queries after it is bounded, and the bound is why it
stays small.  Refilling costs at most one miss per entry the sweep displaced —
`capacity` misses, whatever the store's size — and where the sweep itself pays a read
per record, that is `capacity / records` of the sweep's own cost, a ratio the per-miss
cost cancels out of, so a store too large for the page cache does not change it.
Measured on an 800,000-record store at the 65,536 default: a skewed stream holding a
~84% hit rate at ~1 µs/query drops to ~69% over the 25,000 queries following a full sweep
and is back inside a point five 25,000-query spans later — **tens of milliseconds of added latency
in all, against a sweep that itself took seconds**.  At 200,000 records, three times the
cache and where that ratio is at its worst, the shape is the same and the sweep is the
larger cost by an order of magnitude.  A skewed stream's head is much smaller
than the cache, which is why the refill lands well inside one 25,000-query span: the sweep displaces
65,536 entries, of which a few thousand are ones anything asks for again.

**A closure sweep is the reader with no reuse inside it.**  A transitive-predicate walk
fetches one record per edge it crosses and visits each node once, so nothing it reads it
reads twice — the skew the cache is sized for is absent by construction.  Under the
capacity that adds no work (a walk over 20,000 records is 1% fetch, and the `:disk`
fetch beats the `:memory` one, a `LinkedHashMap` hit against a nested-map lookup); past
it the fetch is a real page-in at ~3 µs and rises to a fifth of the hop.  The other four
fifths are the retrieval and walk machinery both mounts pay alike, so the fetch is a
minority of the walk at every size measured — `lein bench-walk`, and
[taxonomy.md](taxonomy.md), "What one hop costs".

**Durability + crash-safety.**  A daemon (`disk.durability`) fsyncs every store on a
tick and a JVM shutdown hook closes them.  Logs are recovered on open: finish an
interrupted compaction, truncate a torn tail, tombstone any slot now past EOF.

Finding that torn tail reads the frame **lengths** and decodes nothing
(`files/log-tail-offset`): a prefix, a skip, repeat, through a positional read buffer,
since a `RandomAccessFile` is unbuffered and a `seek` per frame is syscall-bound —
[why lengths, not frames](defenses.md#torn-tail-recovery-reads-lengths-not-frames).
The length chain suffices because a frame is appended **before** the
slot that points at it, so a torn tail frame is one nothing references, and
`validate-idx-tail!` is what reconciles a slot against a log that lost its end.  A
**non-positive** length ends the walk: no frame payload is empty, so a zero is space
never written, and a filesystem that zero-fills past a tear would otherwise be walked to
EOF four bytes at a time and pronounced intact.

Three logs are read whole on open rather than through an idx: `tokens.log`, the index's
`kv.log` and the operation log.  Their decoding scan (`files/scan-log`) follows the
same length chain and stops where it ends.  A frame inside the chain whose payload does
not thaw is read by what follows it.  As the chain's **last** frame it is a torn tail:
its length landed and its payload did not, and the open truncates it with the rest of
the tail.  With frames **after** it, it is damage inside the log, and the scan throws
`:damaged-frame` naming the file, the byte offset and the frame.  Reading it as a tail
would drop every frame after it.  In the token dictionary that ended the dictionary
early, and the premise walk then tombstoned on disk every record citing a later token.
Each log answers the refusal by what it holds:

- `tokens.log` — the open refuses.  Frame *i* is id *i*, so no later frame can be read
  past the damaged one, and the records citing them are not crash skew.
- `kv.log` — the replay keeps the ops before the frame and flags the store
  `:damaged-frame`, and the coverage check below rebuilds the index from the records.
  The log is left as it is until that rebuild empties it.
- the operation log — truncated at the frame and marked unusable (`[:damaged-frame
  offset]`), so a restore declines and the open recovers from the records.

A `VirtualMachineError` inside a thaw, an `OutOfMemoryError` above all, is rethrown as
itself and fails the open: it says the JVM could not finish the thaw, not that the frame
is bad, and the next open reads the log whole.

A clean `close!` records each log's length in `clean.nippy` and the next open skips the
walk while the length still agrees; the marker is *consumed* on open, so it only ever
describes a store nobody holds, and any disagreement — stale, absent, unreadable, past
EOF — falls back to the walk.

The walk finds a frame boundary; it cannot say whether what remains is *everything*,
and a short index opens populated-looking and answers short forever — re-asserting a
fact it cannot find mints a second handle for a sentence already stored.  Two
instruments close that, each for the loss that defeats the other, and `open-kb`'s
coverage check reads both.  The **batch-seal counter** (`kv/sealed-prefix`) is
incremented as the *last* op of every `index-sentex` batch and decremented as the
last op of an unindex's cleanup, so it equals the indexed-sentex count exactly when
every batch landed whole: a torn append-mode tail keeps a batch's prefix — the root
count included, which is why the root count alone is the wrong instrument — and loses
the seal first.  The **length check** compares the file against the clean marker
before the marker is consumed: a compacted log is one flat `[:put]` per key in hash
order, so a tail lost at rest — a short restore, a partial copy — is arbitrary keys,
the seal possibly among the survivors, and only the length says the file is not the
one that was closed.  A frame inside `kv.log` that does not decode sets the same flag.
On any of these signs the coverage check rebuilds the index from the records.
A store whose seal reads zero — one written before the counter, or an index installed
whole by `import-dump`'s replay — is checked by the root count alone, as before.

The index WAL additionally **compacts on a clean close**
when its dead ratio has earned it (the same switch and threshold the background tick
uses), because opening it is a replay and so costs the frame count rather than the
live-key count.  Measured at 300k facts, that compaction is worth 4.5× on reopen (36.2s
uncompacted against 8.0s), and the index's own share of the open is where nearly all of
it sits (32.9s against 6.5s).

**The background trigger reads counters, not files.**  After each fsync tick the
durability daemon probes every registrant's dead ratio, at most once per
`vaelii.disk.compact-min-interval-ms`, and queues a rewrite of one that has reached
`vaelii.disk.compact-dead-ratio`.  The index WAL's ratio is `1 − live keys / frames
written`, and both numbers are resident.  The record store's is the largest across its
kinds of `1 − live frame bytes / log length`, where a live slot's frame is its 4-byte
prefix and its payload.  Each kind holds its live frame bytes as a counter under the kind
lock.  The open seeds the counter from the idx walk it already makes, and a store, a
batch and a kill move it by the frame each adds and the frame each supersedes, which
costs one 24-byte slot read when the handle was live.  A wipe zeroes the counter, and a
compaction install recounts it from the new idx.  A probe therefore reads the counter and
the log's length, and no idx byte
(`disk_record_store_test/a-probe-of-an-unchanged-store-reads-no-idx-bytes`), and the
counter equals a walk of the idx after every write path
(`the-maintained-dead-ratio-equals-a-scan-of-the-idx`).

Compaction never edits in place — it rewrites to a temp, fsyncs, drops a commit
marker, then replaces the original, so a crash mid-compaction recovers to the last
durable state.  The record store's compaction is **copy-on-write**: the O(live) record
rewrite (read + thaw + re-freeze + write every live frame) runs *without* the kind
lock, reading the log's immutable region through a private read handle, so reads and
writes of that kind do not stall for it.  Only two brief lock holds bracket it — a
snapshot of the live slots up front, and a delta reconcile + swap at the end that folds
in whatever was stored/killed during the rewrite.  A concurrent `clear-records!` — or a
`close!` of the directory — sets an abort flag: the copy loop stops at its next check
(every 256 frames) and the reconcile discards its temps rather than replaying them over
a wiped store or leaving them under a directory another process has just been handed.  A
rewrite already **past its commit marker** is deliberately out of the flag's reach: the
reconcile reads it under the kind lock and holds that lock until the install is done, and
a marker on disk is a rewrite the next open would finish off the marker anyway, so the
close lets this one finish now rather than hand over a half-installed directory.
`reindex` rebuilds the index from the records on disk unchanged.

The rewrite preserves every live record and its handle, with one exception: a slot whose
frame the log cannot give back — what a truncated tail leaves under a slot the truncation
did not reach — is **tombstoned rather than carried**, and the handle leaves the live set,
the premise set and the record cache once the install lands.  Re-freezing the `nil` would
put the handle back as a live record fetching to nothing, an id `sentex-ids` names and
`get-sentex` has no answer for; a record disappearing is logged at `:warn` per handle,
since it is something an operator has to be told rather than shown by a later count.

**Two monitors, because three threads touch this store.**  The writer is one; the
durability daemon is another (`fsync`, every `vaelii.disk.sync-ms`); a compaction runs on
a third.  So the store's *resident* state — the live-id set, the live frame bytes, the
hot-record cache, the compaction delta set, the failure flag, the handle counter and what the counters blob was
last left holding — is not the writer's alone, and a field written outside a monitor is
one another thread can catch mid-pair.

- The **kind lock** covers that kind's log and idx *and* the resident state derived from
  them — on the read side as well, since the live-handle set is a bitmap mutated in
  place and a read taken beside a concurrent add reads a structure mid-edit. A store, a
  kill, a batch and the compactor's reconcile each take it once and do both halves inside
  it, so no reader finds an id live whose slot says tombstone, or a cleared delta set
  under a writer folding an id into it. The cost is an `addLong` and a map put inside a
  monitor already held for two file writes.
- **A monitor of the store's own** covers the three that belong to no kind and move
  together: the handle counter, `counters.nippy`, and `synced-seq` saying what that blob
  holds. `fsync` reads and writes them on the daemon's thread and `clear-records!` on the
  writer's, and a tick that read the counter before a wipe and wrote the blob after it
  would leave a wiped store's blob holding the pre-wipe high-water mark. It is not a kind
  lock because a whole-file blob rewrite held inside one would put a record append behind
  it on every tick that minted a handle.

The premise set is a `LiveHandleSet` under the sentexes kind lock for every mutation, and
the pairing that would matter — a handle in `premise-ids` whose record is gone
— is a delete the writer makes, on the thread that reads it back. Its one mutation from
another thread is the compactor dropping a handle whose frame the log cannot give back,
which takes the kind lock beside the live-set drop it belongs with.

**The switches are checked.**  Every `vaelii.*` property the backend reads — the tick
(`vaelii.disk.sync-ms`), `vaelii.disk.fsync`, `vaelii.disk.auto-compact`,
`vaelii.disk.compact-dead-ratio`, `vaelii.disk.compact-min-interval-ms`,
`vaelii.disk.compress`, `vaelii.disk.cache`, `vaelii.disk.tokens`, `vaelii.disk.lock` —
has a domain in `vaelii.impl.config`, and a value outside it is refused with
`:unknown-option` naming the property, the value and the legal spellings.
`vaelii.index.snapshot` and `vaelii.belief.snapshot` have an empty domain and are refused at
every spelling, naming `{:backend :disk-snapshot}` instead: the mapped index image and the
reasoning image are what that backend reads on open, and a representation belongs in the opts
map where the KB's own configuration records it.
`open-kb` reads the lot before it opens anything (`config/check!`), which is the earliest
entry point: two of them are read per fsync tick, where a throw is a log line nobody can
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
- **This JVM, unable to let go** is a `.release` or `.close` that threw, at a close or
  while unwinding an acquire whose holder-tag write threw after the OS lock was taken.
  The directory stays marked held rather than being reported free while the descriptor
  and the OS lock are still ours, and re-acquiring it is refused with `:type
  :unreleased`. Only the process exiting drops what is still held.

Two refusals come **before** the lock is tried, because creating `.vaelii.lock` is the
first thing an open writes and java.io's refusal names that file rather than the
directory. `acquire!` catches it and names the directory, by the canonical path every
lock refusal uses:
`:type :not-a-directory` (with `:file`) when the directory, or the nearest part of its
path that exists, is a regular file, and `:type :not-writable` (with `:user` and the OS's
`:reason`) when the process cannot create files there. A read-only open is refused the
same way, since it takes the lock too.

The switch is read **at acquire time and by `held?`**: it decides whether an entry is
made, `release!` follows the entry alone, and `held?` answers true for an entry or for the
switch being off.  Toggling `vaelii.disk.lock` under a
directory this JVM already locked therefore cannot strand the OS lock, which is what a
`release!` re-reading the property would do.
`vaelii.core/close!` releases it without the JVM exiting, and **the order it does that
in is the contract**: deregister from the durability daemon, abort any compaction still
running, wait for the compactor to go quiet, write the index image, close each
component, drop the lock.  The lock goes last because it is the thing the other process
is waiting on, and everything above it is a file of this directory's still being
written.  The join is not belt-and-braces: the record store's rewrite phase holds no
lock on purpose, so it is still appending to `sentexes.log.compact` *by name* when a
close that skipped the wait would already have handed the directory over — and the next
owner's own compaction opens those same paths.  Two rewrites appending to one temp log,
one commit marker, and a replay installing frames from both is exactly the tearing the
lock exists to prevent.  An unclean close
still releases: every component gets its close attempt, the lock release and the
registry removal run even when one throws, and the first component failure is rethrown
*after* that cleanup — so a throw from `close!` means the directory is handed back but
the close was not clean.  Within one process, stores are shared per canonical
directory (`disk.backend`, a registry mirroring the memory backend's db registry), so
two KBs over one directory share the durable store — the restart contract the recovery
tests rely on — and the lock, file handles, and durability registration are taken once;
closing either KB closes both. `close!` also empties the process-wide memos the nogood
readers fill (`decide/drop-memos`), which hold the last KB read, so a closed KB's records
and index are collectable once its caller drops the KB value.

### A store that stops

**A sentex write is two stores, and a refusal from the second takes back the first.**
`kb/create-sentex` appends the record, which allocates the handle, and then writes the
index batch keyed on that handle.  An index that refuses the batch — `:compaction-failed`,
or any other throw — would otherwise leave a record no index names, reported to the
caller as a failed write.  The next open's coverage check indexes such a record, and
recovery then believes it as a premise whose forward rules never fired for it, since
`recover` rebuilds belief from the stored justifications and does not chain.  An index
can also refuse part-way through its write: the columnar index writes the trie posting
before the argument roots, and an argument-root scope past the argument-scope
ceiling refuses in the second step, so the posting would name a handle with no record.
So the postings the write landed are taken out (`unindex-sentex!`) and the record is
deleted before the throw travels, and the store holds what it held before the call.  A justification is one record and no index write, so the justification writers
have no second store to fall out of step with.  A crash after the record write and
before the premise mark or the justification that supports it leaves a record both stores
hold and nothing supports.  The coverage check indexes only a record no index names, so it
leaves that record as it is, and the open reports it
([A record no premise and no justification supports](#a-record-no-premise-and-no-justification-supports)).

**A disk store stops at its first fault, and says so on every call after it.**  Each
store — the record store, the index's `kv.log`, an overlay's metadata log, the operation
log — holds one fault latch, and five things set it, named by the refusal's `:reason`:

- `:interrupted` — a thread interrupt closed a channel the store was reading or writing.
  A `FileChannel` closes itself when the thread blocked in it is interrupted, and the
  closed channel closes the `RandomAccessFile` it belongs to, so the channel is gone for
  every later call on every thread, not only for the interrupted one.
- `:channel-closed` — a channel was found closed without the interrupt that closed it.
- `:write-failed` — an append, a slot write, a tombstone or a truncation threw an
  `IOException`: a full disk, an I/O error.
- `:fsync-failed` — the durability daemon's fsync, or the one `close!` runs, threw.  The
  kernel may already have dropped the dirty pages it was flushing, so a retry on the next
  tick could succeed over bytes that never reached the disk.  The fsync is not retried;
  the writer is told instead.
- `:closed` — `close!` released the store.

From then on every call on that store — reads, writes, enumerations, `clear!` — throws
`:store-unusable` with the first fault's `:reason`, its `:path`, and the exception that
latched it as the cause, where each call would otherwise have thrown whichever
`ClosedChannelException` or `IOException: Stream Closed` its own channel produced, with
no `:type`.  The first fault is logged once, at `:error`.  Only opening the directory
again clears the latch: the open walks a log that did not close cleanly and the
coverage check reads the index, which is the repair.  A read that fails with an
`IOException` on an open channel leaves nothing on disk changed and does not stop the
store.  `:compaction-failed`, a compaction that failed past its commit marker, is a
separate latch with its own refusal.

`close!` of a store that has already stopped releases every handle, logs at `:warn` and
does not throw.  It writes no clean marker, so the next open treats the directory as an
unclean shutdown.  A close whose own flush fails still throws, since that fault is the
close's to report.

**The steps `assert` takes after the write landed do not fail it.**  `assert` stores,
chains and settles the sentence, then records its provenance, re-homes a forced extent and
reconciles NATs.  A store that stops during those three steps is logged at `:error`
naming the handle, and `assert` returns the handle: the write took effect and a reopen
holds it with its consequences, and the store refuses the next call.  What a stop leaves
undone is the provenance or the maintenance, never the write.  A store that stops earlier,
while the sentence is being stored or chained, throws `:store-unusable` out of `assert`.
A premise stored before a fault inside the chaining keeps its record, and a reopen
believes it with only the consequences written before the fault: `recover` rebuilds
belief from stored justifications and does not chain.

### A record no premise and no justification supports

A stored record whose handle has no premise mark and no justification concluding it stays
OUT, counts in `count-sentexes`, and answers a belief-blind read.  A crash after the
record write and before the write that supports it leaves one, and so does a store closed
under a running write ([below](#a-shutdown-under-a-running-write)).

**The open reports such a record and changes nothing.**  After `recover` builds the
network, on the records path and the image path alike, `recovery/note-unsupported!` takes
the network's nodes less its premises and keeps each node no justification concludes.  On
the dense network the scan is one bitmap subtraction and one supports probe per
non-premise node: over a 1,000,000-node network of 300,000 premises and 700,000 derived
nodes with no unsupported one, the scan measured 70–276 ms per open (median 178 ms over
7 runs).  It reads the provenance of the nodes it keeps, and no record or index.
A node whose record carries the `:inert` mark drops out.  The open logs the handles at
`:warn` and holds them in the KB.  `(unsupported kb)` answers `{:n :handles}`, re-checked
against the network on each read, so a record premise-marked, concluded or retracted since
the open drops out.  The browser's catalog `:stats` carries the same map under
`:unsupported`, and the store card shows the count.  `write-hazards` does not name it, and
no write is refused over it.

**An `assert-inert` record carries an `:inert` mark.**  `assert-inert` stores a record with no
premise mark and no justification, and writes `:inert true` into a new record's
provenance, so the scan leaves the record out.  Two cases still read as unsupported:

- an `assert-inert` record an earlier build wrote, before `assert-inert` marked its
  records, until `mark-inert!` marks it;
- an `assert-inert` record whose mark did not land.  The mark is a second write after
  the record, so a crash between the two leaves the record unmarked, and the report is
  accurate: that write failed.

**A caller removes one on its own evidence.**  `(remove-unsupported! kb {:handles hs})`
retracts the unsupported records among `hs`, with their postings, and returns
`{:unsupported-removed n :handles [h …]}`.  The handles are the ones the caller's own
record of its writes marks failed; the engine keeps no outcome per write.  `{:force?
true}` removes every record `unsupported` reports, an earlier build's unmarked
`assert-inert` record included, so `{:handles hs}` is the form to use.  `(mark-inert! kb
{:handles hs})`, or `{:contexts cs}`, marks the unsupported records it names `:inert`.  Either call
with no evidence refuses `:unsupported-unattested`.

### A shutdown under a running write

Each public write entry point counts itself in flight while it runs, under its op name
(`dur/call-as-write`), and so does a `with-deferred-settle` batch's closing settle.  The
JVM shutdown hook waits up to **10 s** for no write to be in flight, and then closes the
stores (`dur/quiesce-writes!`).  Past that bound it logs `::shutdown-write-running` at
`:warn` and asks the running writes to stop.

**A clean stop always rolls back as a unit.**  Only the part of a write that the entry
point rolls back whole on a throw honours the stop request (`dur/as-unit`): an `assert`,
and an `edit!` batch's adds with its removals' refusal checks.  Such a write stops at its
next clean point, after a rule firing, at the start of a settle pass, or before each moved
type and each declaration an argument-hold refresh reads ([argtypes.md](argtypes.md)),
where every record it wrote has its premise mark or its justification, and throws
`:shutdown-abort`.  The
entry point then rolls the write back as it rolls back a refusal, with the stop request
off for the rollback, and an operation log marks itself unusable, since its frame
describes a write that did not complete as logged.  Every other write runs with the stop
request off and the hook waits for it: `edit!`'s removals and the settle after them, a
`retract!`, a `with-deferred-settle` batch's closing settle, and a write nested in another
public write.

**Past both bounds the case equals a crash.**  After the stop request the hook waits up to
`vaelii.disk.shutdown-unwind-ms` more (default `10000`).  Past that bound it logs
`::shutdown-write-unwound-late` at `:error`, naming the ops still running and the
setting, and closes the stores under them.  A store closed under a write is in the state a
crash at that moment leaves: it can hold an unsupported record, which the next open
reports and `remove-unsupported!` removes on the caller's evidence, and a batch past its
rollback point is applied in part.  A process that runs settles of many minutes, such as a
long import into a store of millions of records, sets the bound above its longest batch.

## The sentex records — `LiteralSentex` and `RuleSentex`

A sentex is stored as one of **two records**, split so a literal sentex does not carry
the six rule-only slots — there are 100M+ facts, and each dropped reference field is
~4 bytes across all of them (measured: the record shell falls from ~80 to ~48
bytes/instance, ~3.2 GB at 100M). Both share a scalar **core**; `RuleSentex` adds the rule
decomposition. The `sentex/sentex` constructor canonicalizes the structural connectives
and `set/*` wrappers into these fields rather than leaving them as sentence data, and
emits the right record.

The **core** (`LiteralSentex` and `RuleSentex` alike):

- `:context` — the context symbol it holds in.
- `:id` — the integer handle, `nil` until the record store assigns one.
- `:strength` — the assumption strength (`:monotonic` / `:default`) when the sentex is
  asserted as a premise; `nil` for a purely-derived sentex. The record store writes it
  on `mark-premise` and reads it back with `premise-strength`, so premise strength
  lives **on the record** — with the rank mirrored into the disk idx slot (above), so
  `premise-strength` answers off the slot rather than paging the record on every open.

**`LiteralSentex`** is a literal — a fact or its negation, a metadata declaration, or a
query pattern: one signed predicate application, ground or holding variables. The name is
the sentence's shape rather than its role, and the alternative that looks obvious
(`FactSentex`) is wrong for a reason recorded in
[defenses.md](defenses.md#the-two-records-are-named-for-the-sentences-shape-not-for-its-role). It adds
one field to the core:

- `:sentence` — the readable, normalized form (`(flies Tweety)`, `(not (flies Tweety))`),
  kept for display and matching. A negative literal's sentence is `(not S)` with **double
  negation eliminated** (`(not (not S))` ⇒ `S`, via `peel-not`), so the head is the whole
  sign: `sentex/negative?` reads it, and no field repeats it.

Reading any rule-only key off a `LiteralSentex` returns `nil`, so
`(some? (:antecedent sx))` is the literal-vs-rule discriminant everywhere — no consumer
needs to know which record it holds.

**`RuleSentex`** is an implication, and holds **no `:sentence`**. The decomposition below
is its one representation — the form the chainers, the indexers and the checks read — and
`sentex/sentence-of` builds the `(implies (and A B) C)` form from `:antecedent` and
`:consequent` for the trie key and for display. It adds:

- `:antecedent` — the antecedent patterns as a vector (a leading `and` unwrapped).
- `:consequent` — the consequent pattern.
- `:varmap` — `{?var0 ?x, …}` mapping each **canonical variable** back to the name the
  author wrote, so `sentex/originalize` can restore the original form for display.
- `:engines` — which engines run the rule, a subset of `#{:forward :backward :solve}`,
  set by the rule's `set/*Rule` wrapper: `#{:backward}` for a bare `implies`,
  `#{:forward :backward}` for `set/forwardRule` (and a bare generator), `#{:forward}` for
  `set/forwardOnlyRule`, `#{}` for `set/inertRule`, and `#{:solve}` for a choice or
  constraint rule. The wrapper canonicalizes into the record exactly like the connectives
  do, so a rule carries its own engines rather than them living in a side index. Not part
  of the rule's identity: a re-assert joins two spellings by union
  ([canonicalization.md](canonicalization.md#rule-wrappers-become-fields)).
- `:defeasible` — `true` for a `set/defaultRule` rule (its conclusions fire at
  `:default` strength and can be defeated); `nil` otherwise. Wrappers may nest, so a
  defeasible forward rule sets both fields.
- `:effect` — what the head is. `:derive` for a truth the rule concludes; `:choose` for a
  `set/assumptionRule`, whose head is a *choice* for a solve; `:forbid` for a
  `set/hardConstraint` and `:penalize` for a `set/softConstraint`, whose head is a
  contradiction the solver must avoid (excluded outright, or minimized). Part of the
  rule's **identity** — the trie key's two constant trailing slots spell it — so a choice
  or constraint rule and its bare twin are distinct sentexes; see
  [solving.md](solving.md).

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

`assert` records `{:creator :created}` on the sentex it creates — `:creator` from
`opts :creator` or the dynamic `*creator*`, `:created` from the dynamic `*clock*`
(epoch millis by default; both bindable, which is how tests fix them). Creation is
**first-writer-wins**: re-asserting an existing sentex keeps its original provenance,
while any `opts :provenance` map is merged in. `add-provenance` layers application
fields on later; `provenance` reads the map. It is torn down with the record — a
`retract!` (via `delete-sentex!` / `delete-justification!`) deletes the provenance entry
alongside the record, so it never leaks past the thing it annotates. The store methods
are keyed by any handle, so the protocol admits justification-level provenance (derivation
who/when); only asserted sentexes carry it.

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
(`encodable_test` and `check_test` assert the boundary).

**That thaw is the guarded one** (`vaelii.impl.io.thaw`), which is what makes the front
entry point and the file readers hold one opinion rather than two that agree today. A leaf whose
class round-trips only through Java serialization — `java.time.LocalDate` and the other
`java.time` locals, a `Throwable`, a joda `DateTime` — is refused `:not-encodable` where
it is written, rather than stored and then refused on the way back off disk one restart
later. Write a date as a calendar term ([time.md](time.md)) or as a number; the types
nippy has an id for — `java.util.Date`, `java.time.Instant`, `java.time.Duration`,
`java.util.UUID`, `java.net.URI`, `java.math.BigDecimal`, every primitive array — are
unaffected.

### A file names no class

Every thaw the engine runs over a file — a record stream, a log, a dump, the reasoning
image's `network.bin` and `state.nippy` — goes through one entry point, and its allowlist of class
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
directory is. A **missing** `format.edn` is written with the current version — a
pre-sentinel directory is by definition today's layout — but a **damaged** one is refused
(`:unreadable-store`), because a sentinel cut mid-write is a directory whose records were
being written at the same moment. A damaged `layout.edn` reads as `:stale` instead and
the index is rebuilt from the records: it answers whether the entries can be *proved* to
match this build's key shape, and a torn sentinel proves nothing.

Both are read under the manifest byte bound (`dfiles/read-edn-manifest`), as are an
index directory's `records.edn` and a belief image's `manifest.edn`. A `format.edn` past
the bound is `:manifest-too-large` at `open-kb`, as it is at the catalog; a `layout.edn`
past it reads as `:stale`, the answer a torn one gets.

The engine writes each of these EDN manifests, and `reasoners.edn`, to a temp file,
fsyncs it, renames it over the target and fsyncs the directory (`dfiles/write-atomic!`).
A crash mid-write leaves the previous manifest or the new one, never a torn file.

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
(`sentex/symbol-pool-generations`, two `ConcurrentHashMap`s), so a predicate, type, individual,
context, or variable name is a **single shared object** across every sentex that
mentions it, so the sharing it buys dwarfs its own footprint: a `parentOf` or `dog` in
millions of facts is one symbol, not one per fact. The trie key gets the sharing for
free, since `alpha-rename` passes constant symbols through unchanged, and the context is
interned by the constructor. Interning changes object identity, never equality, so a
pooled `?var0` still matches a fresh one as a binding key.

What bounds the pool is **not** the vocabulary. A KB that only names things holds one
entry per distinct name, but three writers mint a fresh symbol per *fact* — NAT
reification (`nat/constant-for`), head-existential skolemization
(`skolem/skolemize-conclusion`) and abduction's scratch contexts — and the pool is
static, process-wide and shared by every KB, so nothing hands an entry back. So the pool
is capped at `sentex/*symbol-pool-limit*` and held in two generations. A lookup reads the
current generation, then the previous one, and a name found in the previous one moves into
the current one. When the current generation reaches half the limit it becomes the
previous one, and the old previous generation is dropped. A name read at least once per
generation keeps one shared object; a name unread for two rotations leaves the pool. A
rotation can change no answer, since identity was never what anything read.

The limit starts at 1M, several times the shipped ontology plus the whole of OpenCyc
(~188k constants). A disk store's token dictionaries (the record store's `tokens.log` and
the index snapshot's) intern every token they hold at open, which on a large store is
millions of names. Each dictionary therefore first raises the limit to twice its entry
count (`sentex/size-symbol-pool`). One
generation then holds the whole dictionary, so the open rotates at most once and drops no
name it interned. A name minted per fact afterwards rotates the generations at the raised
limit. The limit never falls, so a second, smaller store leaves it where it is. A
store with no durable dictionary, such as the in-memory stores, keeps the 1M default.

## Persistence & recovery

The record store, trie, term index, and rule index all persist — durably across a
restart on `:disk-log`, and within the JVM on `:memory` (the space-number
registry). The **taxonomy** and **JTMS graph** are in-memory, so a KB constructed
against an existing store has to rebuild them. `open-kb`'s default, `:recover? :trust`,
does it at construction, and installs a reasoning image an earlier engine build wrote and
keeps it ("Trusting an image"). `:auto` does the same except over that image, which it
declines and recovers from the records under this build (`true` is an alias for it);
`:background` installs it and rebuilds behind it ("Rebuilding behind an image"); `:warn` leaves them empty and says
so, `false` leaves them empty in silence, and both leave the repair to a `core/recover`
call of the caller's own. Nothing else is a setting — a value `recover-modes` does not
name is refused (`:unknown-option`) rather than read as the warn branch, since a KB that
silently took `:warn` answers `[]` to everything and is indistinguishable from an empty store. Either
way recovery is these two steps:

- **taxonomy** — install the believed side of every key the index's supporter families
  hold (`rebuild-taxonomy`, [taxonomy.md](taxonomy.md#the-supporters-are-index-families-and-a-cache-holds-what-the-reconcile-reads)),
  and replay the stored equality declarations. The families are posted by the writers
  and by `reindex`, which reads each `genl`/`genlCx` sentex positionally for its two
  endpoints, so one an older or foreign writer left in either predicate's extent without a
  well-formed edge — a two-element sentence whose super reads nil — is **dropped** and
  counted, logged once at `:warn` under `::edges-malformed`. Posting it would activate a
  null closure node, which the `strong-components` condensation cannot walk; the drop is
  the taxonomy's twin of the JTMS's unrooted-justification skip below.
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
  *before* the taxonomy, since the taxonomy installs what the labels admit, then
  reconciles again with its own unconditional `refresh-beliefs` after the forced
  memberships go in — inside the same depth deferral, and *before* the settle, so
  everything the settle reads answers through a taxonomy that already agrees with
  belief. An edge supported by nothing was never in a region for the settle to reach,
  having been OUT from the moment its node was made. The supporters stay stored whatever
  their belief, so a disbelieved one revives its entry when it comes back IN.
  Strengths, verdicts, and reported conflicts are re-derived on restart and match either
  side of it.

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
log for the same reason the index can: the structure of its derivation is different.

That argues against *logging* it, not against *snapshotting* it — a snapshot is O(nodes),
written once and read once, and it is what the mapped index image already does for the
index. The write-once, validate-or-discard machinery that image carries is factored out of
it into a two-op **sink** protocol (`vaelii.impl.io.snapshot` — a `SnapshotSink` streams a named
section and commits a manifest-last, a `SnapshotSource` reads them back; `decision` is the
validity check, one reason per mismatch class, any doubt discarding the whole image), so a
JTMS snapshot and a database image can share one format and one check with only the target —
a directory, a database, memory — varying. The export dump's index already reads and writes
through it, which is what keeps a dump's index and a standalone image the same bytes rather
than two serializations that drift. Two adapters implement the protocol out of tree —
`vaelii-postgres`'s `pg-sink` / `pg-source` and `vaelii-sqlite`'s `sqlite-sink` /
`sqlite-source` — so its shape is published rather than private, and the in-repo
`file-sink` / `file-source` is the reference target an implementer reads. The taxonomy sits at the other end again: its adjacency is O(V+E) and each edge
insert is local and O(1), so it is a set-and-counter structure that `KvBackend` could hold
with no new ideas — the reason it is not held there is that nobody has needed it to be,
not that it resists it.

Two numbers to keep apart before acting on this. The Phase 0 "taxonomy ≈ 0" figure is
**residency** — 0.0 MB, 0 bytes/fact — and says nothing about rebuild *time*:
`rebuild-taxonomy` reads the predicate extent of each declaring functor and an
installed-key read per stored fact of one, with a supporter read per key, and on a corpus
where `genl` is a top predicate that is a great many reads. And `recover`'s ~8 s at 313k records is one number; `lein bench-recoverphase decomp`
splits a recover into its steps, the taxonomy rebuild among them.

**Atomicity.** All validation (naming, wff, arg/disjoint/functional/negation
checks) runs *before* any write, so a rejected assert leaves no trace (tested).
Cross-store atomicity is bounded by the two-store design: each side commits as a
single unit, and `reindex` rebuilds the index from the records to repair a torn
write.

### The reasoner set

A store records the names of the shipped reasoners its KB registers (`add-reasoner`, or
`open-kb`'s `:reasoners`). Two KBs over the same records derive different beliefs when
one registers `:allen` and the other does not: the second stores `(before A B)` and
`(before B C)` and finds `(before A C)` underivable. So the set is part of the store:

| store | where the set is recorded |
|---|---|
| a directory (`:disk`, a `:disk-log` or `:snapshot` index, a durable fork's own half) | `reasoners.edn` at the directory's root |
| records in RAM, a RAM fork's own half | the memory registry, keyed by the space, for the life of the JVM |
| records on a server with no `:dir` | nowhere: nothing is recorded or checked |

`open-kb` compares the set `:reasoners` names (none when the option is absent) with the
recorded one, and refuses a difference before recovery runs (`:reasoner-mismatch`, with
`:stored` and `:requested`). `:reasoners :stored` takes the recorded set instead. A fork
mounted by `:base` opts with nothing recorded in its own half is held to the set its base
records, and `fork` registers the reasoners of the KB it forks. A store that records no
set accepts any, and records the set the open names. Either way the provers are
registered once recovery has run, which is where a caller's own `add-reasoner` after
`open-kb` lands, and `add-reasoner` adds its names to the record. `clear!` keeps the
record, as it keeps `format.edn`. No entry point removes a name from it; deleting
`reasoners.edn` forgets it.

`export!` writes the set into `meta.edn` as `:reasoners`, and `import!` refuses a
destination registering another set before the first write. `{:reasoners :stored}`
registers the dump's set once the import has recovered, when the destination registers
no name outside it; `koinii.deref/pull!` passes its opts through. A dump with no
`:reasoners` key, from an earlier build or another dialect, is not checked.

The record holds names only. A prover `add-prover` registers is code no record can carry,
so neither the store nor a dump names one. The CLI, the daemon and the browser's attach
open an existing directory with `:reasoners :stored`.

### Editing the records of a KB without belief

A removal through `edit!` or `retract!` keeps belief current at the write: it sweeps the
dependents of what it removes, re-checks what the removal released, and settles, and a
batch pays that over its whole reach. A repair of many records can apply its batches to
the records instead and pay one rebuild after them.

```clojure
(def kb (open-kb {:backend :disk-log :dir d :recover? false}))
(def r  (edit-records! kb {:remove hs :direction {rule-h :backward}}))
;; => {:removed n :unpremised n :absent n :redirected n :justifications-removed n :seeds [h …]}
(settle-record-edits! kb {:seeds (:seeds r)})
;; => {:rebuilt :recover :unrooted n :removed-sentexes n :removed-justifications n
;;     :rules-chained n :rechained n :arg-types {…}}
```

**`edit-records!` writes records and nothing else.** It runs no check, no dependency sweep
and no settle, so it refuses a KB with belief or one answering from an installed image
(`:belief-built`): open the store with `{:recover? false}`. A batch takes `:remove`, a
seq of handles, and `:direction`, `{handle direction}` over stored derive rules
([inference.md](inference.md#rule-direction-virtual-predicates)). It takes no additions:
canonicalizing a symmetric or commutative argument, homing a forced-decontextualized
predicate and deduplicating on a derived index each read belief. An addition goes through
`edit!` after the settle. The handles come from a read of an index: `:disk-log` keeps its
index on disk, so `handle-of` answers on it opened `{:recover? false}`. `:disk-memory`,
`:disk-dense`, `:disk-columnar` and `:disk-snapshot` open `{:recover? false}` with
`:no-index` among their `write-hazards`, and there `handle-of` reads an empty index and
answers nil, so read the handles before closing the KB that built the index. Per batch:

- A removed record is deleted with its index postings, rule-index and taxonomy-supporter
  postings among them, unless a justification that survives the batch concludes it. Such
  a record only loses its premise mark and stays, derived.
- A rule's direction is written into its record and its postings moved.
- Every stored justification resting on a deleted record, and every firing of a rule
  the batch takes off `:forward`, is deleted. The records those firings concluded stay
  until the sweep. A rule firing that rests on a deleted `genl` or `genlCx` edge stays
  stored too: the edge was the one route the firing named, and the settle reads the
  firing's antecedents before it deletes it.
- A removal naming no stored record, a nil one included, counts under `:absent`.
- An `except`, `defeat` or `exceptWhen` removal is refused (`:record-edit-unsupported`):
  its departure re-posts what the remaining ones name, which only `edit!` computes. A
  direction on a fact, a choice rule or an absent handle is refused too. Every refusal
  comes before the first write.

**`settle-record-edits!` rebuilds once and sweeps.** It runs `reindex` when the index is
missing and `recover` when belief is, then the sweep: it deletes the justifications the
recover left out because a record they name is gone (`:unrooted`, [above](#persistence--recovery)),
and sweeps the consequence closure of their conclusions and of `:seeds` as a retraction
does — every record there that is no premise and is OUT goes, with its justifications —
then settles. A rule a batch put on `:forward` is among the seeds and is chained over the
stored facts. The antecedents of each unrooted rule firing, less the deleted records, are
re-chained (`:rechained`), as `edit!` re-chains the antecedents of a firing that named a
removed edge ([contexts.md](contexts.md)): where a second route still licenses the firing,
it comes back at a fresh handle. The recover logs each such firing among the
justifications it leaves out. Last, `record-arg-types` re-asks every fact an argument
declaration reaches, which releases a general type mint a removed membership or `genl`
edge withheld ([argtypes.md](argtypes.md)).

**`{:arg-types? false}` leaves that pass to its own call.** The settle then returns a KB
that is settled and forced to disk, so a copy taken right after it is a consistent one,
and the pass is owed (`arg-types-owed`): `edit-records!` records it when a batch removes
anything, and the settle when its sweep removed anything and nothing was owed yet.
`record-arg-types!` runs it with a budget per fact, stops at a fact boundary and resumes
from what the store records, under this engine or a later one
([argtypes.md](argtypes.md#the-pass-over-a-stored-kb)). `:on-progress` reports each phase
as `{:phase :done :total}`: `:reindex`, `:recover` with the recover's seven steps, and
`:sweep` with its six, the chain's `:derived` and `:pending` beside; a throw from it lands
at the next phase boundary.

The believed sentences then equal those the same batches through `edit!` leave, handle
numbers aside: `edit_test/edit-records-then-settle-believes-what-edit-believes` runs each
case both ways. A record OUT after the rebuild that no seed reaches stays stored and
unbelieved; `unsupported` reports one no justification concludes.

**A crash loses nothing the rebuild needs.** A KB without belief carries no operation
log, so neither call is logged; a batch is idempotent instead. It writes the directions
and premise marks first, then each deleted record with its postings, then the dead
justifications, which the recover leaves out while their records are gone. The same batch
run again completes it, counting what is already deleted under `:absent`. Its `:seeds`
are computed from the justifications it deletes, so a caller keeps them with its own
record of the batch: a re-run after a crash past those deletes returns fewer, and the
records the lost seeds reached stay stored and OUT, which `unsupported` reports. A crash
inside `settle-record-edits!` leaves the records and the rebuild repeats. A crash inside
`record-arg-types!` needs no restore either: the records it wrote are durable as written
(a `:pg` store commits each one; a `:disk` index is forced every few seconds and its open
repairs a short one), and after the rebuild the next call redraws from its last commit, at
most `:commit-every-ms` of drawing. A mint torn between its record and its justification
is stored OUT until that redraw justifies it.

## What a bulk load costs

`bulk-assert-facts!` is the write path with everything a *trusted* corpus does not need
already off — the definitional checks (the `arg` store query above all), the dedup
trie-walk, provenance, forward chaining, and N−1 settles. What remains is storing,
indexing and believing, and this is where that time goes.

`lein bench-loadphase [n] [repeats]` (`bench/vaelii/bench/loadphase.clj`) is
the instrument. It loads one corpus repeatedly through the same entry point, each run with one more
phase stubbed out from the outside in, so the difference between two consecutive runs is
that phase's cost and the deltas **sum to the baseline by construction** — there is no
unattributed residue. The peel order puts a phase before anything it reads: the nogood
candidate note reads the index, so it is peeled before the index write, which is
peeled before the record write, which is peeled before canonicalization.

**1,000,000 distinct binary ground facts, `:memory` pair, one context, no rules.**

| phase | µs/fact | share |
|---|---:|---:|
| index write — key streams, postings, counts | 24.64 | 56.8% |
| JTMS node + the premise mark on the record store | 9.32 | 21.5% |
| the special-predicate suite + the violation ledger | 4.55 | 10.5% |
| the public `assert` prelude — shape checks, NAT presence check, rule dispatch | 2.92 | 6.7% |
| record store `put-sentex` | 1.52 | 3.5% |
| the P/¬P coincidence set | 1.13 | 2.6% |
| canonicalization (`res/kb-sentex`) | 0.85 | 2.0% |
| the observation call sites — alpha memories, change clock, handle cache | 0.63 | 1.4% |
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
no phase changes character with N. The structures being written creep deeper: a HAMT gains
a level, and the roots' sets are ten times longer. The one row far enough apart to be more
than the floor is the **JTMS**, at 5.2 µs/fact against 9.3 — a
node into a map and a handle into a set, both of which the corpus size reaches.

**The index write is the load**, and splitting it says which part. Two `KvBackend`
decorators over the real one leave `index-sentex` computing every key and change only how
much of the batch it produced lands — one drops the `:increment` ops, the other drops the
batch entirely:

| component of the index write | µs/fact | of the load |
|---|---:|---:|
| postings — trie child edges and leaves, term index, secondary roots, term-name set, slots | 15.6–16.8 | 35–39% |
| key streams, the op list, and the pre-write name-set/slot reads | 4.6–6.7 | 11–15% |
| count maintenance — one `:increment` per trie level per fact, plus the batch seal | 2.5–4.6 | 6–10% |

The ranges are two independent runs; the split arms are whole loads too, so their
difference carries the same ±1 µs/fact.

Postings dominate because two of them are `conj` into sets that grow with the corpus: the
predicate extent holds every fact with that predicate and the context root every fact in that
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
removes the per-fact HAMT path copy of the *map*, which is not where the time is. Sorting
the corpus by trie key before inserting is unpriced here for a reason rather than an
oversight — its benefit is locality, and the in-memory trie is a hash map keyed by whole
path vectors, where there is no contiguity to hit.

**A facts/s figure is per writer thread.** This path is single-threaded, and by the
single-writer contract below it has to be. So a rate is only comparable against another
rate taken at the same writer count, and a wall-clock load comparison between two engines
is a comparison of thread counts until both are fixed to one.

### What a recover spends its time and heap on

`:last-recover`'s `:steps` split a recover's wall time by phase. A converted ontology
store carried through `import!`, `reindex`, `export!` and a reimport on `:disk-columnar`
(`{:records :disk :index :columnar}`) splits its recover as follows:

| step | share of the recover |
|---|---:|
| `:settle` | about 50% |
| `:derived-sets` | about 25% |
| `:taxonomy` | about 15% |
| `:network` | about 6% |
| `:depths` | about 4% |
| `:refusals` | under 1% |

`:refusals` holds the re-fire of the rules that can refuse and the settle a re-fire owes.
`:placement` holds the settle that places the nogoods the rebuilt candidate index queued
(`chain/placement-queued?`). The table's measurement counts that settle under `:refusals`.

The recover's heap peak is about twice the import's, so the recover sets the heap a store
needs (`VAELII_HEAP`). A `:disk-snapshot` open that installs the reasoning image takes
about a twentieth of the recover's wall time. An open declines the image when the engine
source has changed, and then pays the full recover
([The reasoning image](#the-reasoning-image)). `scripts/upgrade-kb.sh` pays the recover
once, ahead of the next open.

## Loading a changing snapshot over a fixed base

A process that reasons over live data loads a snapshot of ground facts, reads an answer,
and loads the next snapshot. The KB beside the snapshot (vocabulary, rules, the facts
every snapshot shares) does not change between reads. Each read's cost depends on which
write route loads the snapshot.

### Two routes to the chained closure

A **chained write** (`assert`, `assert-many`, `edit!`) chains each fact from a seed list
it builds for that fact (`vaelii.impl.assert-entry`):

- the fact's own handle;
- the argument-type memberships the fact entails ([argtypes.md](argtypes.md));
- the stored facts below a `genl` edge the fact adds (`special/subsumption-seeds`);
- the rule triggers behind a link the fact adds to a declared-transitive predicate
  (`special/transitive-seeds`);
- the facts a `genlCx` edge the fact adds brings into a context's view, which the write's
  settle seeds.

A chained write's cost therefore grows with what the new facts reach.

**`bulk-assert-facts!` builds none of that list.** It stores, indexes and believes the
facts, and leaves three passes to the caller:

1. `record-arg-types` records the argument-type memberships. It draws every fact of
   every declared functor, including facts stored before the load. It runs no forward
   chaining from what it records.
2. `release-withheld!`, when `owed-releases` is non-zero.
3. `forward-chain` fires the stored rules over the loaded facts and the recorded
   memberships. It seeds every believed datum, including the rest of the KB.

After the three passes the KB holds what a chained per-fact load holds. Both
`record-arg-types` and `forward-chain` read the whole KB, so the bulk route's cost grows
with the KB and not with the load. The bulk route fits a store whose whole content is
new: a corpus import, or building the fixed base once. A snapshot loaded over a larger
KB takes a chained write.

No public entry point chains from a given set of handles. A run seeded with the loaded
handles alone omits every seed in the list above except the first. A snapshot holding a
`genl` edge, a `genlCx` edge, a transitive link or an argument-type entailment then
derives fewer conclusions than the chained write derives.

### Writing the difference between two snapshots

- **Close the base once.** Load the content every read shares, rules included, and
  bring it to its chained closure before the first snapshot.
- **Keep one KB across reads.** Hold the snapshot's facts in a context of their own.
  Write each new snapshot as one `edit!`: `:add` holds the facts that arrived, and
  `:remove` holds the handles (`handle-of`) of the facts that left. The adds land before
  the removes and one settle closes the batch, so a conclusion both snapshots support
  stays IN throughout ([api.md](api.md)). Every add is a chained write, so no pass
  follows the `edit!`. The batch's cost follows the size of the difference.
- **An aggregate rule can stay in the base.** One `edit!` against a stored aggregate
  rule costs 5.1 ms at 10 nodes, against 4.4 ms for the rule asserted after the facts
  and 21.3 ms for one assert per fact (`lein bench-aggchain`,
  [aggregate.md](aggregate.md#what-it-costs)).
- **A fork per read pays a recover per read.** `fork` rebuilds the fork's belief with
  one `recover` over the base's contents ([overlay.md](overlay.md)), and every read in
  a fork merges the overlay half with the base. A fork that several hypotheses need is
  kept open across reads. A process that owns its KB does not need a fork.

`chain-report` gives each forward rule's placed and refused firings, and `chain-stats`
gives the last run's `:derived`. Forward chaining keeps no beta network
([inference.md](inference.md)), so each firing re-joins the rule's other antecedents.
The two reads name the rules a snapshot's chaining time goes to.

## The single-writer contract

**One process, one writer.** The engine pairs a durable store with in-memory state
(the TMS, the taxonomy closures), and only the writing process's memory tracks its
writes:

- *Two threads, one process:* every TMS mutation applies atomically — the reference
  network through `jtms/swap-with-result!`/`swap!` on its atom, the dense one under a
  `StampedLock` write lock — so concurrent operations **compose** and none is silently
  lost. That is a liveness floor, not a semantics: interleaved `assert`/`retract!`
  sequences are not serializable (find-or-create and the settle pipeline are
  check-then-act), so concurrent *writing* still needs a single writer: two threads
  asserting one sentence can store it at two handles, both believed, and the store keeps
  both across `recover`. A reader thread
  beside a writer thread (the web browser over a REPL's KB) is the supported shape, and
  **both** TMS representations give that reader a consistent snapshot — the reference out of
  its persistent-map snapshot, the dense one out of an optimistic read validated
  against the writer's, so neither ever shows a partially-applied relabel
  (`jtms_concurrency_test`).

  **A settle is published once.** A settle is a run of TMS calls: it empties the standing
  nogoods before it finds them again, so between its first call and its last a reader
  could read a standing loser believed, on every settle, including one for an unrelated
  fact. While a settle runs it **holds**
  the belief it began from (`vaelii.impl.settle/settle`): the network records each label
  a relabel moves as it was when the settle began, the standing nogoods keep their
  value, and a thread other than the writer reads those — belief, a defeat class, the
  blocked and superseded sets, and the placed nogoods. When the
  settle ends it publishes what it decided in one step, which is one swap of the open
  holds (`vaelii.impl.observe`). A reader beside the writer therefore reads, for every
  settle, the belief before it and then the belief after it, and never one in between
  (`kb_concurrency_test`). Three things keep that exact:
  - **The caches.** A thread reading a hold's belief reads the change clock as
    `-1 - clock` (`observe/change-clock`), so no clock-keyed cache hands it an entry the
    writer derived from the network it is deciding, and none hands the writer one derived
    from the belief the reader holds.
  - **The taxonomy is read live.** Its closures are memoized where the writer reads them,
    so the two visibility callbacks read what the writer holds now (`observe/live`), and
    `genl?`, `isa?` and the scoped closures answer a reader beside a settle from the
    closures as the settle moves them. The hold covers belief, not the closures.
  - **The reasoning image.** Its manifest covers the records, and a settle moves belief
    without writing one, so `reasoning-image/save!` declines while a settle holds the
    network, or when the change clock moved while it wrote.

  **A read is not one state's, and the engine does not make it one.** `sentexes-matching`
  and `query` read the index postings and then belief per candidate, and nothing ties the
  two reads to one state. A match stored after the postings are read is missing from the
  answer, and so is a match that leaves belief before its check. A writer that moves a
  counter with `assert (cnt N+1)` and then `retract! (cnt N)` holds one or two believed
  counters in every state, and a reader's one `sentexes-matching` for `(cnt ?n)` can
  still answer none. Both reads are lazy over live state, so a caller bounds an open read
  by taking from its seq and pays for the records it takes
  ([api.md](api.md#choosing-a-query-function)). One state per read would need every answer
  realized whole and re-run whenever a write lands inside it, or a versioned store, and
  the engine has neither. A caller that needs one state per read reads on the writer's
  thread, or between writes it orders itself. An assert or a retraction publishes the TMS
  calls it makes before its settle one at a time, and an `edit!` is visible to that reader
  add by add; its effect as one change is its one `watch` event.

  **A cache entry is one state's.** Every TMS entry point moves the change clock before
  and after its mutation (`vaelii.impl.jtms`, `moving`). The literal-match cache and the
  closure cache install an entry only when the clock reads the same before and after
  computing it (`literal-cache/lookup`, `provers/cached-reach`). A reader thread that
  computes across a TMS call therefore installs nothing in either, and neither the writer
  nor a later read is served an answer about the network before the call.

  **Two selectable index backends are narrower than that**, and it is the one place the
  floor does not reach. `:columnar` (`vaelii.impl.columnar`, and the `vaelii.impl.dense-roots`
  it builds on) and `:dense` (`vaelii.impl.dense-kv`, whose `IntPostings` is mutated in
  place) hold `^:unsynchronized-mutable` fields, so a write
  publishes through no barrier: a second thread may read an array reference, a
  capacity, the CSR-mode flag or a half-installed mapped section from before a growth,
  a compaction or a snapshot install, with no happens-before edge to stop it. The atom-
  and lock-based backends give the incidental reader a consistent snapshot; these two do
  not, and keeping such a read on the writer's thread or behind a synchronizer is the
  caller's. Two writer threads on them do worse than tear: they can leave an
  open-addressing map with no empty slot, and both threads then probe it without end. The walk reads these fields at every frontier node, the index's hottest
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
