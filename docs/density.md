# Density — the dense backends

- **Covers:** the dense int-postings, columnar trie, and packed-root backends that replace
  the default map-based index structures, what each is measured to cost or save in
  resident bytes, and what a lookup on either trie layout allocates.
- **Not here:** the index's logical key layout these backends implement →
  [indexing.md](indexing.md); how `open-kb` selects a record/index backend pairing →
  [storage.md](storage.md).
- **Assumes:** sentex, handle, index, canonical form → [glossary.md](glossary.md).

`vaelii.impl.dense-kv`, `vaelii.impl.columnar`, `vaelii.impl.dense-roots`,
`vaelii.impl.tokens`, `vaelii.impl.dense-jtms`, and the record-side work in
`vaelii.impl.disk.*`.

These exist because of a gap between the engine's *seams* and its data structures at
corpus scale. The seams carry a large KB — the `LiteralSentex`/`RuleSentex` split, symbol interning,
an index derived from the records and rebuildable by `reindex` — while the default
structures are persistent Clojure collections holding boxed values, which measure
~1,973 B/fact of index (591.9 MB over 300k real facts, measured below). Each backend
here is a dense replacement for one of them.
**Every one is off by default**, selected per KB, and each is gated by a differential
oracle proving it answers the protocol identically to the structure it replaces.

Nothing here changes what the engine computes. If a dense backend ever returns a
different answer, that is a bug in the backend, not a feature of it — which is why the
oracles compare *sets*, not summaries.

## Selecting one

The records and the index are chosen on **separate axes** — `open-kb`'s `:records`
(`:memory` / `:disk`) and `:index` (`:memory` / `:dense` / `:columnar` / `:disk-log`), with
`:backend` as sugar naming a pair (see [storage.md](storage.md)). That split is what
lets the density work run durably: a dense index is *derived* state, so pairing one with
durable records costs only a rebuild on open.

| `:backend` | records | index | what it is for |
|---|---|---|---|
| `:memory` | RAM | `KvIndexStore` over a map | the default; no external dependency |
| `:memory-dense` | RAM | int-postings values | Phase 1 — the 31% of the index that is posting *values* |
| `:memory-columnar` | RAM | native int-token trie + int-keyed roots | Phase 2 — the 69% that is *keys and nodes* |
| `:disk-memory` | paged from disk | `KvIndexStore` over a map, rebuilt on open | durable records, nothing written for the index |
| `:disk-dense` | paged from disk | int-postings values, rebuilt on open | Phase 1's index, measured at durable scale |
| `:disk-columnar` | paged from disk | native int-token trie, rebuilt on open | Phase 2's index, measured at durable scale |
| `:disk-log` | paged from disk | `KvIndexStore` over a WAL-backed map | durability; the record side of the density work |
| `:overlay` | a decorator | a decorator | a fork over a frozen base — [overlay.md](overlay.md) |

The whole test suite runs on any of them: `VAELII_TEST_BACKEND=memory-columnar lein
test`. `backend_parity_test` runs a scripted KB session across all eight configurations
the engine carries alone — the seven record×index pairs above plus the overlay decorator
— in an ordinary `lein test`, so a divergence fails without anyone remembering to. The
`:sqlite` and `:pg` record axes are legal too and are not here: they live in sibling
adapters that core does not depend on, so their parity is each adapter's own suite
([storage.md](storage.md)).

`:backend` names the *storage*. The third resident structure, the truth-maintenance
network, is orthogonal to it and is selected separately by `:tms` — `:dense`
(default, Phase 3 below) or `:reference`, either of which works with any backend.
Plain `lein test` runs the suite through the default dense one;
`VAELII_TEST_TMS=reference lein test` runs the baseline.

## The measurement that shaped it

The index's cost is **keys, everywhere** — not the handle sets everyone assumes. On
300k real facts (`lein bench-densetrie`):

```
── index decomposition ──            MB    keys    values
  trie-counters                     137.6  137.6     0.0    ← pure key overhead
  trie-childsets                    202.2  105.2    97.0
  trie-leaves                       131.7   90.1    41.6
  root-arg                           98.7   52.6    46.1
  term-index                        196.8  101.3    95.5
  root-context / root-functor        31.7    0.6    31.1
  TOTAL                             591.9   (the whole index map, deduped)
```

The rows sum higher than the TOTAL, and that is not an error: a row is measured on its
own entries, so an object two subsystems share is counted twice across the rows and once
in the total. Read the rows against each other and the TOTAL as the retained size. About
487 MB of it is boxed structured-vector **keys**.

A trie node is three map entries (`[:trie :count prefix]`, `[:trie :children prefix]`,
`[:trie :handles prefix]`), and a path's every prefix is a separate vector object.

**The finding that had to drive the build: the win is the *layout*, not the interning.**
Interning tokens while keeping an object-per-node map (a fastutil
`Int2ObjectOpenHashMap` per node) recovers **1.28×** — per-node map overhead swamps it.
A columnar layout — parallel `int` arrays, zero per-node objects — gets **15–20×**. A
plausible design and a good one differ by an order of magnitude here, which is why the
bake-off ran before the build.

**Read that 15–20× as what it is: the trie *nodes*, measured against the structure they
replace.** It is not what a KB weighs. A whole KB is the index plus the records plus the
TMS, and only the first is what a dense index addresses — so end to end, on 200k ground
binary facts, `:memory-columnar` holds **1,631 B/fact against `:memory`'s 2,668**, a
**1.6×**, and loads at 31.8k facts/s against 22.5k. The trie figure is the right one for
choosing a layout and the wrong one for sizing a machine; the records and the TMS are
what is left standing once the index is dense, and they are the floor the whole-KB
number sits on.

## Phase 1 — tiered int postings (`:memory-dense`)

`vaelii.impl.dense-kv` replaces each `PersistentHashSet` of boxed `Long` handles with
`IntPostings`: a sorted `int[]`, promoted to a `RoaringBitmap` past 128 members.

The tiering is measured, not assumed. Sorted `int[]` beats the boxed baseline
**5.6–6.3×**; **RoaringBitmap only 1.07–1.45×**, because the index's mass is in a very
large number of *tiny* postings where a bitmap's per-container overhead dominates. So
the answer was a size-tiered hybrid, not blanket Roaring — the opposite of the obvious
choice. Oracle: `dense_kv_oracle_test`. Measured 591.9 → 464.5 MB (**1.27×**).

**The tiering pays a second time on reads.** `kv-intersect` — what `sentexes-with-args`
and `sentexes-with-terms` bottom out in — narrows in the representation the postings are
already in rather than in the sets they would make: `RoaringBitmap/and` where both sides
are hot, a sorted two-pointer merge where both are cold and comparable, a probe of the cold
side's entries into the bitmap where the tiers differ, and — where neither side is a bitmap
and one is 32× the other — a binary search of the short run into the long one, which is
what a **mapped** root run needs, having no hot tier to probe at all (`dense-roots` reads a
snapshot's postings as plain sorted runs). Smallest posting first, so the accumulator
starts as narrow as any column can make it and only shrinks, and the one Clojure set is
built at the end at the size of the *answer*. Measured against folding
`clojure.set/intersection` over materialized postings, on one hot root and one rare
argument root:

```
  rare(4) ∩ hot(1000)      0.120 ms → 0.0015     80×
  rare(4) ∩ hot(32000)     4.734 ms → 0.0015   3234×    ← flat where it was linear
  hot(1000) ∩ hot(1000)    0.628 ms → 0.0149     42×
  hot(32000) ∩ hot(32000)  29.24 ms → 0.563      52×
```

Read down the column and the four rows say one thing: **the cost tracks the answer, not the
columns it came from.** The rare rows hold their answer at 4 handles while the hot side
grows 32× and the cost does not move; the hot ∩ hot rows grow their answer 143 → 4,572 and
the cost grows with it. That is the boundary contract showing through — the narrowing is
native, and what is left is `|answer|` handles boxed into `Long`s for a caller who was
promised a Clojure set. `lein perf --only intersect-selectivity` gates the first half of
it.

Every arm allocates its result, so a read can never shrink a posting it narrowed against.
The mutating `RoaringBitmap.and` instance method would, and would stay invisible until some
later query came back short — which is why `dense_kv_oracle_test` snapshots every posting
across a run of intersections and compares.

**Which families get packed is a decision, and it is checked.** A handle family is one
whose value is a set of handles: the trie leaves `[:trie :handles …]`, the three roots
`[:context-root …]` `[:functor-root …]` `[:argument-root pred pos …]`, the term index
`[:term-index …]`, both halves of the rule index `[:rule-index :antecedent|:consequent
…]`, and both halves of the exception index `[:exception-index <pred>|:rules]`. The rest
must *not* be packed: `[:trie :count …]` is an integer, `[:trie :children …]` holds path
tokens (numbers among them), and `[:term-roster]` and `[:argument-slot …]` hold term and
predicate *names*. **Every handle family packs**, the argument roots included, and they
are the one family that has to earn it: `[:argument-root pred pos term]` carries two names
where every other key carries one, and the packed long has a single term field. The room
is in `pos` — 24 bits reserved for an argument position, which every other family passes
0 in — so `dense-roots` interns the `(pred, pos)` scope to a dense id of its own and rides
those bits. `dense_routing_test` records that no handle family is left in the fallback.

Both dense backends keep a fallback for keys they don't route, which makes a routing
mistake behaviourally invisible — a misrouted family is stored as an ordinary boxed set,
answers every read identically, and passes both oracles and the `index-entries`
projection while buying nothing. So routing has its own test that reads the stored
*representation* rather than the answers, over keys taken from a real load rather than
spelled by hand: `dense_routing_test`. It also fails on a family nobody has classified,
so adding an index family forces a routing decision instead of silently taking the
fallback.

## Phase 2 — the columnar trie (`:memory-columnar`)

`vaelii.impl.columnar` is a native trie rather than a map of path keys: `int` node ids,
grow-on-demand parallel arrays (`counts` `int[]`, per-node child edges — sorted `int[]`
tokens and targets while narrow, one `Int2IntOpenHashMap` once wide — and `IntPostings`
leaves, so Phase 1 and Phase 2 are the same structure), and edges labelled with interned
`int` tokens from `vaelii.impl.tokens`.

It is **mutable, not a static CSR**, because the index mutates: a per-node child
structure plus a free list supports incremental add and remove, which a CSR cannot do
live. The
CSR is available as a *read optimization* instead — `columnar/compact!` freezes the node
graph into flat parallel `int` arrays (DFS-preorder renumber, which also reclaims the id
holes a churny load leaves), the read primitives dispatch on a `frozen?` flag, and a
write thaws back to mutable. That is the bulk-load-then-query move, and the record
store's own mutable-head/compacted-tail pattern.

**A node's child structure is tiered on its width**, for the reason that recurs across
these backends: a representation chosen for how it *holds* data has to be re-checked
against how the code *writes* it. Minting an edge in the sorted pair splices both arrays,
so it costs O(children already there) — and nothing bounds a node's width. The level-2 node
holds one child per distinct first argument of a predicate, so an array-only node
structure loads one broad relation — `(genl S T)`, any hot relation in a
real ontology — in time quadratic in *that relation's own extent*. The cost tracks the
node, not the corpus. Holding 200k facts fixed and varying only the widest node's
fan-out:

```
  widest node   2,000 children    4,188 ms
  widest node  20,000 children    9,045 ms
  widest node 200,000 children   18,193 ms
```

So past `columnar/promote-at` (64) children a node's edges become one primitive
`Int2IntOpenHashMap` — O(1) insert, no splice — and drop back to the array pair below
half of it, the hysteresis keeping a node on the boundary from rebuilding on every
add/remove pair. Blanket maps are the wrong answer in the other direction: the bake-off
above put a fastutil map per node at 1.28× against the columnar layout's ~15–20×. The
tier takes both, because nearly every node is narrow and never leaves the dense pair.
Child order is not part of `p/children`'s contract — the flat-map index answers it out of
an unordered set — so a wide node's edges come off the map as they lie, and only
`compact!` pays to sort them, which the frozen CSR's binary search needs.

`lein perf --only columnar-fanout` is the gate: n sentexes on one predicate with n
distinct first arguments, so the only thing that grows between 4,000 and 64,000 is the
fan-out of the single node every insert passes through. The tiered node reads **1.07×**
growth against a bound of 2.00×; the array-only node reads 3.14×, and costs 4.3× as much
per insert at the larger size.

`vaelii.impl.dense-roots` is a key-interning `KvBackend`: the secondary roots, the rule
and exception indexes, and the inverted term index route into one
`Long2ObjectOpenHashMap` keyed by a packed `family | pos | term-id`, with the term
interned through the *same* dictionary the trie uses. Unrecognized keys fall back to a
plain backend, so it stays a full `KvBackend` and the composition above it is unchanged —
which here is two families: `[:term-roster]` and `[:argument-slot pos term]`, whose
members are term and predicate names rather than handles. Both are vocabulary-scaled, so
nothing fact-scaled is left outside the packed map — the argument roots reach it through
the interned `(pred, pos)` scope described above. The columnar trie is native, so no
`[:trie …]` key reaches this backend at all.

`vaelii.impl.tokens` is the `path-token ↔ int` dictionary. It interns a path level
**as-is** — a symbol, a number, `:false`/`:rule`, `nil`, a `[::subterm k]` arity marker,
or a whole literal list — because re-canonicalizing would turn a marker vector into a
list and break `sentex/subterm-mark?`. Content-keyed and first-writer-wins, so ids are
stable; the id *value* depends on encounter order, which nothing above it reads, so a
rebuild that interns in a different order yields an equal index.

It keys tokens by **Clojure** equality, and that is load-bearing rather than tidy. The flat
map it replaces keys its trie on a `PersistentHashMap`, where `(= 2 (int 2))` is true and a
path carrying an `Integer` reaches a node stored under a `Long`; a `java.util.HashMap` keyed
on the token says false, and the node is simply not found — one fewer answer, no error. The
two boxings meet in ordinary use, since `agg/count` concludes with an `Integer` and the same
sentence asked as a question carries a `Long`, and a whole literal list is a token too, so
the disagreement nests. A `Key` wrapper defers to `hasheq`/`equiv`, the same two the flat map
uses.

Oracles: `columnar_index_oracle_test` (including a compaction arm that freezes, re-checks
every read against the never-compacted reference, churns, re-freezes, and inserts after
freezing, and a width arm that drives one node across `promote-at` in both directions
with the threshold turned down — asserting the *representation* as well as the answers,
since no comparison of reads can tell a promotion that happened from one that did not),
`dense_roots_oracle_test`, `tokens_test`.

```
  whole index, 300k real facts   591.9 MB → 223.0 MB   2.65×   resident
                                          → 185.9 MB   3.18×   after compact!
  ├─ native trie                  52.4 → 15.4 MB (3.4× compacted)
  ├─ int-keyed roots + term index 69.1 MB  (was ~208 boxed)
  └─ shared token dictionary     101.4 MB
```

The dictionary is the largest part above, and every term-index key interns through it — so
what the term index keys on is what the dictionary is bounded by. A sentence's own body is a
subterm of itself, so keying each literal for *itself* mints one token per record, holding
exactly one handle: at that setting 4,754 records over 511 distinct terms produce 5,336
tokens, 4,750 of them whole lists. A dictionary of facts, over a vocabulary of hundreds.

**`sentex/*min-indexed-depth*` is the floor that refuses them**, and the bound is the
vocabulary. It drops a content literal's key for itself and keeps every compound nested inside
one, so nothing a probe is actually *for* loses its key (`(sentexHandle H)`, the sentence
inside an `(ist Ctx S)`), and a compound with no key is still found — from the atoms it
contains, verified against the record ([indexing.md](indexing.md), "Which compounds are
keys"). Measured on the same corpus at the same two sizes, 17,267 → 51,071 records over a
fixed 511 names:

```
                            keys for itself      the default
  mapped index, resident      13.0 MB              1.8 MB
  ├─ dictionary                9.8 MB (75%)        0.1 MB (6%)
  ├─ trie                      1.6 MB              1.6 MB
  └─ roots + term index        1.6 MB              0.1 MB

  growth over 2.96× the records
    dictionary                 2.94×               1.00×
    roots + term index         3.59×               1.00×
    whole mapped index         2.99×               2.35×
```

The dictionary and the roots are flat in the corpus and bound by the vocabulary. What
grows is the CSR skeleton, which is path-scaled and deliberately resident.

## What a lookup allocates

Retained heap is what the index *holds*; **allocation** is what a read *writes*, and it is
structural for the same reason retained heap is — a count of what the code builds, not a
measurement of how fast the box ran it. So it is the read-path quantity that survives the
caveat at the bottom of this page, and `lein bench-alloc` is the harness. The instrument is
`getCurrentThreadAllocatedBytes` on `com.sun.management.ThreadMXBean`, differenced across a
region bounded by two reads on one thread: no agent, no profiler, and no seam in the
engine. 20,000 Zipf-skewed binary facts, both layouts over one corpus, every answer set
compared across the layouts before anything is measured — a walk that quietly found nothing
allocates almost nothing and would otherwise report as a win.

```
  pattern shape             probes    B/lookup   B/probe
  exact       :memory          5.0       4,358       872
              :columnar                  3,733       747   1.17×
  after-var   :memory        304.8     247,664       813
              :columnar                165,339       543   1.50×
  lead-open   :memory      2,931.4   2,268,179       774
              :columnar              1,895,732       647   1.20×
```

`probes` is node probes per walk, off `vaelii.impl.profile`'s `:fan` tally, which counts
one per frontier node per level. The tally fires on `KvIndexStore` only
([profile.md](profile.md)), and a probe count is a property of the trie and the pattern
rather than of the layout, so the flat map's is the denominator for both.

**The layouts separate by 1.2 to 1.5× on a read, against the 15–20× they separate by in
resident bytes.** Most of a lookup belongs to neither of them: both walks rebuild the
frontier as one `(into [] (mapcat f) frontier)` per pattern level, measured at **648 B**
per level over a one-node frontier, and on a narrowing walk that is the largest single
term in the whole lookup.

What is left is the layout, and it reads as a **marginal** rather than as a ratio. A ratio
over `B/lookup` divides the shared frontier cost into both arms and reports a difference
smaller than the one that exists — the trap `bench/vaelii/bench/perf.clj` names as a
baseline already carrying the cost being measured, arriving here as a denominator instead
of as a size. The bytes one extra frontier node costs:

```
  ground probe at width     :memory 812 B    :columnar 539 B    1.51×
  fanned child edge         :memory 774 B    :columnar 647 B    1.20×
```

**The columnar advantage is a narrowing step's, and a fan nearly erases it.** A
`KvIndexStore` ground probe names eight objects: the query token conjed onto the prefix
twice (the expression is written twice and evaluated twice — once for the count probe, once
for the surviving frontier entry), a `[:trie :count prefix]` key vector around one of them,
and a one-element result vector — and two of those arrays are prefix-sized. The columnar
probe names six, every one of them small: a `Key` wrapper for the token intern, three boxed
ints (token id, child id, subtree count) and the same one-element result vector. A *fanned*
step swaps the shapes over, because `-edges` decodes every child edge into a boxed `[token
child]` pair before `skip-one` throws the token away, which costs about what the flat map's
conj of the child onto the prefix costs.

The accounting closes on itself, which is what says the derivation is the right one.
Derived probe bytes plus the measured frontier container account for 84% of a narrowing
lookup on the flat map and 83% on the columnar trie, the remainder being the seq cells
`mapcat` builds and the answer set at the terminus. Per *extra* path level the same two
terms predict 944 B against 930 measured on the flat map, and 976 against 960:

```
  arity   levels   :memory B/lookup   :columnar B/lookup
      2        4              4,364                3,710
      4        6              6,224                5,147
      8       10             10,064                8,096
  per extra level          930 → 960            719 → 737
```

That growth is the prefix showing through. A flat-map probe carries the depth it sits at,
since it conjes a prefix-sized array twice per level and the fresh vector's `hasheq` cache
is empty every time, so each level re-hashes what the level above it just hashed; a
columnar probe is an int intern and a binary search into an edge array, and does not.

Two limits, both in the harness's own docstring. The instrument counts **bytes and not
objects** — nothing on this JVM counts objects exactly without an agent — so every object
figure above is derived from the source and is a lower bound on what the walk builds. And
an allocation the JIT proves non-escaping never reaches a thread's TLAB and is invisible
here; cold and warm readings differ by under 1% on both layouts, so escape analysis removes
almost none of this walk.

## Phase 4 — the record side (`:disk`)

Records already leave the heap on `:disk`; what was unmeasured was what reaching them
costs, and what a frame spends its bytes on. Both answers were surprising, and both are
in [storage.md](storage.md#the-on-disk-backend-disk):

- **A warm fetch was 52% slot read.** Not seek distance — *syscall count*: an unbuffered
  `RandomAccessFile` charged six syscalls to move 24 bytes. One positional
  `FileChannel` read each for the slot and the payload took a fetch 7.12 → 3.08 µs. The
  batched `get-many` the plan called for measured **0.91–0.95× — slower** — and was not
  built, because sorting a batch by offset removes no syscall.
- **56% of a frame was scaffolding.** nippy writes the record's type tag and every field
  name into every frame. A **positional** frame is 1.72× smaller and needs no dictionary;
  the `int[]` int-id body the plan called for measured **0.89× — worse than symbols** —
  because four bytes per token only beats nippy's symbol encoding where names are long.
- A bounded **hot-record LRU** serves 64–81% of a skewed stream (5.6× on a zipfian
  stream), and **tokenized bodies** (opt-in) take the log 92.3 → 45.8 B/record.

## Phase 3 — the dense truth-maintenance network (`{:tms :dense}`)

The index and the records are only two of the three resident structures. The **JTMS is
always in RAM in every backend**, and the reference network — an atom over one persistent
map — costs ~467 B/node (`lein bench-jtms`), ~43 GB at 100M, on par with the whole record
store. That is why `vaelii.impl.dense-jtms`, the bitmap/primitive-map representation, is
**the default** as of 0.9.0 (`open-kb`'s `:tms`, orthogonal to storage — any backend may
use either network); `:reference` is the baseline a caller pins:

```
  109,055 nodes, a fact corpus         total    graph    justs
  :reference (atom + persistent map)    26.8     24.1      2.7
  :dense (bitmaps + primitive maps)      4.9      3.8      1.1   5.52×  (258 → 47 B/node)

  16,889 nodes, 60,486 justifications — a rules-heavy corpus (3.6 per node)
  :reference                            22.3     11.3     11.0
  :dense                                 6.8      2.0      4.9   3.26×
```

The decomposition (`lein bench-jtms`) refuted the plan the same way the index's did.
**The per-node scalars are already free** — stripping `:depth`, `:premise?` or `:datum`
releases *nothing*, because they are shared cached objects (small `Long`s, keywords,
booleans). 310 of the 467 B/node is the per-node **map object and its HAMT slot**, so
the lever is not "shrink the fields" but "stop having a map per node".

**Belief sets are the opposite regime from the index's postings.** `bench-postings` found
RoaringBitmap a *loss* (1.07–1.45×) on millions of tiny postings; `:in` holds nearly every
node and compresses **384×**. Both measurements are right — density is the variable, and
a single blanket answer would have been wrong in one direction or the other. Two more
consequences fall out of the same reading: with exactly two defeat-classes and only the
non-bottom stored, **the class map is one bitmap**; and adjacency reuses Phase 1's
`IntPostings` rather than a bare `int[]`, because a much-used premise's consequences grow
without bound and an array-copy insert would make loading such a rule quadratic.

**The compression that makes the belief sets cheap to hold made them expensive to
write, and the locality invariant is what noticed.** A `RoaringBitmap` is a sorted list
of 65,536-value containers, so any operation that rebuilds the whole bitmap costs one
pass over every container — invisible below 65,536 nodes, where there is exactly one.
`relabel-region!` did six such passes per call: it built each fixpoint's boundary with
the *static* `RoaringBitmap/andNot` (which copies every container), cloned that again
inside the fixpoint, and installed the answer with `.clear` + `.or`. So a **singleton
region cost O(believed)** — the opposite of what [nmtms.md](nmtms.md)'s locality
invariant claims, and undetectable in the table there, whose largest graph is 16,000
nodes.

It shows up when a rebuild adds a premise per stored premise. Adding premises in
batches of 250,000, and measuring the copying implementation against the in-place one:

```
  copying     15.6 µs/premise rising to 232.1   ×14.9 across 3M — quadratic
  in place     2.4 µs/premise steady at   2.5   ×1.04 across 3M — flat
  reference   11.6 µs/premise steady at  14.3  (persistent maps never have the problem)
```

What holds the invariant is not copying: `relabel-region!` clears the region out of each
live bitmap **in place** — the mutating `andNot` is a merge over the container lists and
touches only the region's own — and each fixpoint accumulates straight back into it.
That is worth ~56× over 3M premises (~388s against ~6.9s) and 6.5× even in the first
batch, because a clone is never cheap; it is also what puts the dense network 5× ahead
of the reference rather than behind it. **Do not reintroduce a whole-bitmap rebuild in
that path**, however local the code looks. The general lesson is the one this whole
document keeps finding: a
representation chosen for how it *holds* data has to be re-checked against how the code
*writes* it, and the two answers need not agree.

This one is a **parallel implementation** rather than a swap, and the reason is
atomicity, not caution: `RoaringBitmap` is mutable while the reference is an atom over a
persistent map whose all-or-nothing mutation `jtms_atomicity_test` pins. So both sit
behind a `vaelii.impl.jtms-protocol/Tms` protocol, and the dense one coordinates through a
`StampedLock`: writers take the exclusive stamp — serializing exactly as the reference's
`swap!` retry does — while point reads (`in?`, one per candidate on the match path) run
**optimistically**, lock-free in the steady state and validated after the fact, and the
O(nodes) iterating reads take a shared stamp. That gives the incidental reader — the web
browser beside a REPL's writer, the shape the single-writer contract calls supported
(docs/storage.md) — the consistent view the reference's persistent map gives for free: a
reader never observes a partially-applied relabel. The lock is not the trade the earlier
unlocked design feared, either, because a bitmap probe under an optimistic stamp still
beats a boxed-`Long` hash-set lookup by an order of magnitude — measured ≈19 ns against
the reference's ≈180 ns per `in?`. Plain `lein test` runs the whole suite through the
dense network (it is the default), `VAELII_TEST_TMS=reference lein test` the persistent-map
baseline; `jtms_dense_oracle_test` compares the two in full after every step of randomized
operation streams, and `jtms_concurrency_test` holds the consistent-view guarantee under a
reader-beside-writer stress on both.

**A justification is not an object either.** A fact corpus derives about a tenth of a
justification per node and cannot say what one costs, so the decomposition was taken on a
rules-heavy corpus — a dense relation with a join rule over it, where every 2-path is a
separate witness:

```
  structure     118 B  43%   the record object + its map slot
  bindings       80 B  29%   the firing's variable map — belief never reads it
  antecedents    73 B  26%   a vector of boxed handles
  consequence     6 B   2%
  id / informant / strength / out    0 B   already shared objects
```

Two answers fall out. The belief-relevant fields become **columns keyed by justification
id** — an int column for the consequence, one `int[]` per antecedent list, a bitmap for
the strength (two classes again) — and a record is rebuilt only when a caller asks for
one, which no relabel does. And the **bindings leave the network entirely**: they are read
only to re-evaluate an `exceptWhen` query or a NAF antecedent per firing, both readers
hold the KB, and the record store has the record durably. `jtms/graph-just` is the
projection, applied by both representations, so neither keeps a second copy of a
justification and the two still store equal values. **277 → 85 B each**, and the dense
network's advantage on a rules-heavy corpus goes 1.61× → 3.26×.

### At corpus scale, and why it is the default (item 09)

The tables above top out at 109k nodes. `lein bench-scale [n] [rn] [reference|dense]`
takes the per-node resident cost out to 1M under the real `assert` path, both networks,
and it is **flat**: reference holds at ~210–260 B/node and dense at ~18–22 B/node on pure
premises across a 50× range (20k → 1M), so the linear interpolation the whole estimate
rests on is confirmed, not assumed. Because it is linear, the cost **decomposes** —
`jtms_bytes = node_cost·N + just_cost·J` — and the two anchors (premises-only and one
rule firing per fact) solve it:

```
              per node   per justification
  reference    263 B          460 B
  dense         18 B          166 B
```

Applied to a real corpus — 11.5M stored sentexes, 13.0M justifications (j/n ≈ 1.1), the
shape a common-sense KB actually takes — that is **~9.1 GB reference against ~2.35 GB
dense, 3.8×**: the JTMS falls from ~30% of a whole-KB footprint to under 10%, a ~21%
whole-KB RAM cut, on the largest stores the engine is built for. The single 467 B/node
coefficient is a j/n ≈ 0.5 reading and undercounts a justification-heavy corpus (~730
B/node at j/n ≈ 1); the node+just pair above is the honest model.

**The win is memory, not wall.** Across every cell dense loaded and recovered as fast as
the reference or slightly faster, and at 10.19M the two walled identically because the
open-time bottleneck is the `content-order` sort, above the network entirely — so dense
makes a large KB *fit*, never *open faster*. Given an engine whose target is one large
node holding 100M, the default is the network that scales, and this is it. `:reference`
remains a one-keyword pin for the simpler baseline.

**One ceiling the reference does not share.** The dense bitmaps and fastutil maps are
`int`-keyed, so a handle or justification id must fit a 32-bit int — 2^31-1 ≈ 2.1B.
Handles allocate in assertion order and never reuse, so that bounds a KB's *cumulative*
allocations, not its live nodes: 21× the 100M target, but a long-lived writer churning
assert/retract can climb to it. Crossing it throws `:type :handle-ceiling`, an actionable
error naming the ceiling and carrying `:remedy {:tms :reference}` — checked where a new id
first enters, so an operator sees that rather than the cast's bare "integer overflow", and
a supervisor discriminates on the type as it does on every other refusal — and never a
silent truncation
that would collide two handles and corrupt belief. A KB that expects to churn past 2^31
pins `{:tms :reference}`, whose `Long`-keyed maps have no ceiling. The reference costs the
RAM this page measures; that is the trade.

## The budget at 100M

Every section above prices one structure. This one adds them up, because the question the
dense backends exist to answer is not *"what does the trie cost"* but **"what does a
100M-sentex KB hold in heap, and where does it go?"** `lein bench-budget` is the report,
and it re-runs: four geometric corpus sizes per backend at two justification ratios, one
row per resident structure, each row carried to the target only on a shape it passes on
every step. Four sizes rather than three — the third size alone left one row's shape
[unresolved](#what-the-mapped-image-does-and-does-not-take-off-the-heap) and left the
record store's own residue [unattributed](#the-premise-set-is-the-row-that-was-hiding);
a fourth sample settles both. What follows is its output at the default size, extrapolated
to 100,000,000 facts against a 40 GB heap.

`:disk-log`, at j/n 1.1 — the ratio [below](#at-corpus-scale-and-why-it-is-the-default-item-09)
calls the shape a common-sense KB actually takes:

| Structure | At 100M | Shape |
|---|---|---|
| flat KV index (resident, whole map) | **293.73 GB** | linear |
| dense JTMS | **16.56 GB** | linear |
| record premises (boxed set) | **4.12 GB** | linear |
| hot-record cache | 41.2 MB | capped at 65,536 records/kind |
| record live-id rosters | tens of KB | refused — too small for four points to resolve |
| record store, rest | 1.6 KB | flat in the extent |
| naming / match / feed / qcn | tens of KB | refused — same reason as the rosters |
| taxonomy `:up`/`:down` | 0.2 MB | flat in the extent |
| **total** | **314.45 GB** | **7.86× the budget** |

At j/n 0.5 the justification-sensitive rows fall — the JTMS to 11.07 GB, the premise set to
4.22 GB — and the total to 306.21 GB. The index does not move with j/n.

**The roster row is a bitmap, and reading it beside the premise row is the only honest way
to read either.** The live-handle sets are `Roaring64Bitmap`s over the strided runs
`next-id` mints (`vaelii.impl.roster`, [storage.md](storage.md#the-enumerations-and-what-a-roster-costs)),
which is what put a row that carried **9.47 GB** as a `PersistentHashSet<Long>` under 100
KB at every corpus size this run tried. Four points cannot resolve a row that small —
26.3 → 68.0 KB across the run, inside noise — which is a property of the row's new size,
not a gap in the method. What matters is where the weight this row once carried sits now.

### The premise set is the row that was hiding

`cumulative` attributes shared structure to whichever row it reaches first, and the
rosters are measured before the rest of the record store — so a hash-set roster's boxed
`Long`s are the premise set's `PersistentHashSet<Long>` as well, and taking them out of
the roster row only moves the charge: it does not take them out of the KB. With no row
of its own that charge lands on one undifferentiated row, where *"record store, rest"*
reads 4.07 GB against the 2.00 GB it reads when the rosters absorb the boxing.
`bench-budget` gives the premise set the same row the rosters have: `record-premises`,
attributed before the leftover fields rather than folded into them.

**The result is that `record store, rest` is now exactly what its name says.** With
`premises` measured on its own, the leftover — the `DiskRecordStore`'s own fields net of
every row that has a name — reads **1.6 KB, flat, across all four corpus sizes**. It was
never a distributed cost across the store's bookkeeping; it was one boxed set the whole
time, and `record premises` carries it now: **4.12 GB at j/n 1.1**, linear on every one of
the three steps between the four points, and **4.22 GB at j/n 0.5** — slightly higher,
because the target is a fixed sentex count and fewer justifications means fewer of those
sentexes are non-premise rule conclusions, so more of the same 100M are premise-bearing.
Either way it is the size a boxed `PersistentHashSet<Long>` gives at this cardinality,
because that is still the representation. `premises` still needs no monitor on its write
path today ([storage.md](storage.md#tallying--the-questions-that-do-not-need-the-roster)):
that argument does not change by measuring the set more precisely, only the case for
converting its representation does.

**The engine-wide saving from the roster conversion is the pair, not the roster row
alone.** Before: 9.47 GB of boxed rosters plus 4.07 GB of (then-unattributed) premises,
13.54 GB. After: under 100 KB of bitmap roster plus 4.12 GB of (now-named) boxed premises,
4.12 GB. The roster's own multiple is real, but reading it alone credits the conversion
with more than it delivered — the honest saving is what the pair actually gave back,
**9.4 GB**, and the premise set is what is left to convert to close the rest of it.

**The index is the whole problem, and it is worse than its coefficient suggests.** 294 GB
is 7.3× the entire budget on one row. Nothing that compresses what the map holds closes a
gap that size; only taking it off the heap does.

**Everything else fits, with room.** The non-index rows sum to about 21 GB at j/n 1.1 —
half the budget. So an index that goes fully off-heap is sufficient on its own, and the
JTMS work is headroom rather than a precondition.

### What the mapped image does and does not take off the heap

`:disk-snapshot` maps its image, and the index row falls from 293.73 GB to **6.41 GB** —
a total of **27.14 GB, 0.68× the budget**. The image is not one structure, though, and its
sections do not share a shape. `bench-budget` reports each on its own, as a decomposition
of the index row:

| Section | At 100M | Shape |
|---|---|---|
| CSR skeleton | **3.26 GB** | linear |
| roots routed map | *refused, but bounded — see below* | flat, then a 10.9× step, then flat again |
| roots fallback blob ← term + slot rosters | 19.0 MB | flat in the extent |
| token dictionary | 1.3 MB | flat in the extent |
| argument-root scope table | 0.0 MB | flat in the extent |
| roots handle column *(mapped)* | 2.95 GB | linear |
| CSR leaves *(mapped)* | 1.19 GB | linear |
| roots key + offset columns *(mapped)* | 310.1 MB | affine, 0.6 MB + 3 B/fact |

**The fallback blob is the row an earlier measurement was taken to find, and it is still
flat.** At `format-version` 1 it carried the predicate-scoped argument roots — `[:argument-root
pred pos term]` had no packed spelling, so the family rode the resident blob and was read
whole on open. That row once measured **34.10 GB, linear**, 90% of the image's remaining heap
and the difference between this backend being over budget and under it. The interned
`(pred, pos)` scope gave it a packed spelling; the argument roots now ride the mapped
handle column with every other family, and the blob keeps the term and slot rosters alone.
No resident section of the image tracks the fact count except the CSR skeleton.

**The routed map's jump is a threshold, not a slope, and the fourth point is what tells
the two apart.** At 201,096 facts the heap sections summed to 25.9 MB against an index
row of 26.6 MB; a fixed-baseline affine fit through three points (10.1 MB + 86 B/fact)
carried the difference anyway, because a row that sits flat for one step and then jumps
10.9× on the next fits neither "flat" nor "linear" and a two-point affine fit cannot tell
a one-time threshold from an under-sampled slope. The fourth point resolves it directly:
the routed map holds at 154.8 KB across the first two sizes, jumps to 1.7 MB at the third,
and **stays at 1.7 MB at the fourth** — 0% growth on the step that would have shown a
slope if there were one. That is a representation threshold firing once, not a row that
tracks the extent. The likeliest candidate, from `dense_roots.clj`'s own account of
`:routed` — the handful of routed families that still ride the mutable map rather than
the mapped columns — is one or more of their `IntPostings` promoting from a sorted
`int[]` to a `RoaringBitmap` past 128 entries (`dense_kv.clj`'s `promote`): a jump in
per-entry overhead on the entry that crosses it, followed by the bitmap's own compression
absorbing further growth. That is what the shape is consistent with, not something this
run measured directly — a `Long2ObjectOpenHashMap` resize is not ruled out by these four
points alone, and either way the operative fact for the budget is the plateau, not which
of the two produced it. Refitting the index row's affine coefficient over the widened range drops it from
86 B/fact to **69 B/fact** (66 B/fact at j/n 0.5) — the 20% the old fit was carrying on
the routed map's behalf. **The section is still refused a shape of its own — a
flat/jump/flat step matches none of the three the gate tests for — but it is no longer an
unattributed 4.6 GB: it is a measured, bounded 1.7 MB, and the affine fit for the row that
contains it no longer needs to guess.**

The move off the boxed blob is not free on the mapped side, and the two figures are not
each other's complement. The blob shed 34.10 GB of heap; the mapped columns took on far
less than that — the roots' key and offset columns went from flat and small to 310.1 MB
affine, and the handle column to 2.95 GB — because a nippy-thawed posting set on the heap
and a flat `int` run in a mapped file are not the same bytes. So the packing is worth
roughly **30 GB** of the backend's total rather than the 34.10 GB the row itself named.

### What these numbers are not

The corpus holds its vocabulary fixed at every size, so only the extent grows. That is
what makes a growth ratio mean anything, and it is also why the total is a **floor**: every
row that measures flat is carried to 100M at the value 8,000 individuals and 40 types gave
it, and a KB of 100M facts has neither. The taxonomy row, the token dictionary, the
fallback blob and the argument-root scope table are all flat for exactly that reason. Read
the total as the extent's price, not as a KB of that size.

### What a real vocabulary adds, and where

Two of those rows can be bounded rather than left as a caveat, and the answers go opposite
ways.

**The taxonomy row is small because the closure is not stored**, not because the corpus is
small. Only the O(V+E) direct adjacency is resident; `genls`/`specs` walk it and memoize
per node against the relation's `:gen` ([taxonomy.md](taxonomy.md)). So the row scales with
*edges*, never with the Θ(V²) closure a materialized one would hold. Measured with
`bench-budget`'s own `kb-structures`, on `:memory` (the row is backend-independent), a
branching-4 tree over 2,000 individuals and no ground facts:

| Types | Cold | Warm (`genls` + `specs`) | B/type warm | Closure pairs |
|---|---|---|---|---|
| 40 | 0.19 MB | 0.21 MB | 5,374 | 261 |
| 400 | 0.66 MB | 0.69 MB | 1,819 | 2,435 |
| 4,000 | 5.14 MB | 6.06 MB | 1,590 | 30,270 |
| 40,000 | **43.11 MB** | **69.18 MB** | 1,813 | 370,964 |

The 40-type reading reproduces the budget's 0.2 MB, which is also the cross-check that
individuals do not enter this row — the budget corpus has four times as many. The last
decade of types costs 8.4× cold and 11.4× warm against 10× the types, so the row is linear
with a mild excess from ancestor-set size tracking depth as log_b V. Depth is the axis
that could have broken it and does not: 40,000 types at branching 2, 4 and 16 (depths 17,
10 and 6) measure 44.66 / 43.11 / 42.48 MB cold and 83.90 / 69.18 / 61.50 MB warm — the
adjacency is flat in shape, and only the memo tracks depth, over 1.4× across a 3× range.
At ~1,800 B/type a 400,000-type ontology is **~0.7 GB**, 2% of the total. The row stays
small at any vocabulary a KB actually has.

**The taxonomy's sentexes are not in that row**, which is the other half of the answer. A
`genl` edge is an ordinary sentex — a record, index postings, a TMS node — so 400,000 of
them cost 400,000 sentexes of the rows above, 0.4% of a 100M extent, and memberships the
same. Widening the ontology moves the total twice and both moves are small.

**The fallback blob is the row that does not have this defence.** It holds the term and
slot rosters, it is vocabulary-scaled rather than closure-bounded, and 8,070 terms is a
very small vocabulary. It measures flat here only inside the 0.25 tolerance — 11.0 → 13.3
→ 16.0 MB is 1.20× then 1.20× against facts at 1.68× then 1.73× — so it is *not tracking
the extent*, which is the finding, but it is not constant either. Sizing it wants a sweep
that holds the facts fixed and grows the vocabulary, which no bench here runs.

## Reading these numbers honestly

Two caveats the measurements carry, both easy to drop and both load-bearing:

- **A uniform sample of a corpus breaks locality.** Sample thinly enough and each term is
  seen about once, so a dictionary measured against the sample is corpus-sized while the
  store is sample-sized. That is why tokenized bodies read 2.02× on the log but only
  1.13× all-in: the dictionary row does not carry over, the log row does.
- **Retained heap (jol) is structural, so it is trusted under contention; wall-clock is
  not.** Every RAM figure here is jol; every timing was taken on an otherwise-quiet box
  and is indicative. **Allocated bytes are structural too** — a thread's allocation
  counter records what the code built, not how long it took — which is what makes the
  read-path comparison above a trusted reading rather than an indicative one.

## Traps in measuring and writing one

Four that cost real time here, and that a fifth dense representation would meet again:

- **A fact corpus cannot size a rule structure.** At 0.12 justifications per node the
  justification columns are invisible; the rules-heavy corpus — a dense binary relation
  plus a join rule, so every 2-path is a witness — puts it at 3.6 per node and the
  numbers change shape. Size a structure against the corpus that exercises *it*.
- **Strip-and-remeasure needs a rebuilt baseline.** Stripping a field rebuilds the map,
  and an `into`-grown `PersistentHashMap` differs from an `assoc`-grown one by a few
  bytes per entry. That constant lands on every row and reads as *negative* cost for the
  shared-object fields until the baseline is itself a rebuild.
- **Columns are set, never merged.** A map entry is replaced wholesale, so every one of
  the parallel columns standing in for it has to be told; a column left alone on a re-add
  still answers for whatever held that id before.
- **A dense read must be total where the map it replaces was.** `handle-of` returns nil
  for an unstored sentence and `core/defeat-class` is called with it, so a bitmap read
  has to guard for a non-handle rather than `(int nil)` — a persistent map is total for
  free and a primitive column is not.

One language trap worth naming: `doto` clears its target *before* the argument
expression is evaluated, so `(doto mono (.clear) (.or (region-classes …)))` wipes the
boundary classes `region-classes` is about to read.

Harnesses: `lein bench-postings` (the Phase 1 bake-off), `bench-densetrie` (the index
decomposition and the trie bake-off), `bench-alloc` (what a lookup allocates on each trie
layout), `bench-records` (the record side), `bench-jtms` (the truth-maintenance
decomposition and the two representations), `bench-scale` (the Phase 0 per-component
sizing).
