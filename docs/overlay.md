# Forks: an overlay over a frozen base

- **Covers:** what a fork is — a private, writable KB layered over a frozen, read-only base
  — how reads, writes, counts and tombstones route between the two, how a newer dump
  replaces a fork's base while the fork keeps its writes, and how a fork's writes travel
  to another KB as a delta.
- **Not here:** the record/index store protocols and the single-writer lock a base is opened
  through → [storage.md](storage.md); the dense backend internals (postings, the columnar
  trie) a KV decorator wraps → [density.md](density.md).
- **Assumes:** sentex, context, handle, JTMS → [glossary.md](glossary.md).

`vaelii.impl.overlay.kv`, `vaelii.impl.overlay.store`,
`vaelii.impl.overlay.frozen`, `vaelii.impl.overlay.mount`, `vaelii.impl.overlay.rebase`;
`core/fork`.

A **fork** is a private, writable KB layered over a shared, read-only **base**. Reads
resolve fork-first and fall through to the base; writes land only in the fork; **the base
is never mutated**. So N forks can hang off one base and each keep its own divergent
copy, and the sharing adds no work — no copy, no protocol between them, no coordinator.

The sharing is **within one process**. A `:disk` base is opened through the ordinary
durable store registry, which takes the directory's exclusive single-writer lock
(storage.md, "The single-writer contract"), so a second JVM mounting the same base
directory is refused with `:type :disk-locked` — base immutability is a property of the
decorator, not a licence to open the bytes twice.

A base mounted from **`:base` opts** (rather than the `fork` call's `:base-stores`)
holds that lock for the JVM's life: the fork's `close!` releases only the fork's own
directory, and no KB value names the base's, since the registry shares it with every
fork over it and counts no openers. To keep the base's release in hand, open it as
its own KB and fork *that* — closing the base KB is then what frees the directory
for another process.  A fork's own half also never writes into its base's directory:
both halves naming one store is refused outright (`:type :base-is-overlay`), and when
both arrive as opts the refusal comes before either store opens.

```clojure
(def base (v/open-kb {:backend :disk-log :dir "/kb/frozen" :recover? :auto}))
(def f    (v/fork base))                             ; ephemeral: an in-RAM overlay
(def g    (v/fork base {:backend :disk-log :dir "/kb/g"})) ; durable: remountable later

(v/assert f '(penguin Pingu) 'CxBird)   ; f believes it; base and g do not
```

`opts` names the fork's *own* storage, as an ordinary opts map — so the two variants are
spelled with the backends that already exist rather than with names of their own: an
in-RAM overlay is the ephemeral hypothesis, a disk one is durable and remountable. An
ephemeral fork's own half opens on an engine space no caller can name, so its `close!`
drops that space ([storage.md](storage.md)); naming a `:space` keeps it for a remount.

A fork assembled from opts alone spells it out instead — which is how a durable fork is
remounted, in a later process, over the base it was taken against:

```clojure
(v/open-kb {:backend :overlay
            :base    {:backend :disk-log :dir "/kb/frozen"}
            :overlay {:backend :disk-log :dir "/kb/g"}
            :recover? :auto})
```

`:backend :overlay` sets both axes. `:records :overlay` or `:index :overlay` alone is
refused (`:type :unknown-backend`, `:mismatch :illegal-pair`, `:axis` naming the half to
change): the records and the index decorate one base together, and one half alone reads
the base through one store and not the other.

A base opened this way is held to the index key-layout sentinel `open-kb` holds its own
half to ([indexing.md](indexing.md), §7) — and refused (`:type :stale-index-layout`)
rather than rebuilt, since rebuilding is a write and a base is mounted read-only. Open
that directory as a KB once, which clears and rebuilds it, then mount the fork over it.

The fork's own durable half is held to the same sentinel and, under `:recover? :auto`,
to the coverage check ([storage.md](storage.md)) — both read **through the merged
mount**. The own half is the fork's delta, not an index of its own records: its
counters hold base+net and its removal records say which inherited postings the fork
took out, so its seal compared against the fork's own record count disagrees on every
healthy fork that has written anything. Read through the mount, the seal and the root
count are the merged index's and compare against the merged records, so a remount of a
healthy fork rebuilds nothing. When either check does trip, the repair is the one
`reindex` makes on any fork (below): clear the merged index, which hides the base, and
rebuild it from the merged records into the own half.

## Why one decorator forks the whole index

`KvIndexStore` (`vaelii.impl.kv`) implements every index family over one substrate — the
count-aware trie, the context / functor / argument roots, the rule index, the exception
re-check index, the inverted term index and the term-name set — and it holds no state of
its own: every read bottoms out in `kv-members`, `kv-count`, `kv-intersect` or
`kv-get`, and every write in `kv-batch`. So a single `KvBackend` decorator merges the
entire index, and the trie walker, the matcher, the planner, the TMS and the query layers
need no part in it. That is what the `KvBackend` protocol buys.

Two things follow, and they bound the feature.

**The columnar index is not forkable this way.** `vaelii.impl.columnar` is a *native*
`IndexStore`: its trie is int-id nodes in parallel arrays, with no keys and no backend
underneath, and only its roots / term / rule / exception families delegate to an embedded
backend. A KV decorator over it would fork those and silently leave the trie behind, so
`fork` refuses it by name. The forkable index axes are `:memory`, `:dense` and `:disk-log`.

**A taxonomy probe forks the families alone.** `tax/detached-copy` posts a probe's
supporters into `mount/fork-families`: a `KvIndexStore` whose writes land in a private
in-memory layer over the index's family backend, read through the frozen mount. That
backend is the one `kv-backend-of` names, or a columnar index's `:roots`, which holds
every family but the trie. An index with neither refuses with `:unforkable-index`.

**The TMS is not storage.** Belief lives behind its own protocol (`vaelii.impl.jtms`,
with `dense-jtms` as a second implementation) over state derived from the records. A fork
therefore gets its *own* network, and the engine already has the operation that computes one
from records: `recover`. So `fork` recovers over the merged contents rather than layering one
truth-maintenance graph over another. One pass over the merged records, which is what
`recover` costs anywhere.

## The merge model — index half

`OverlayKv` is a composite `KvBackend` `{overlay base}`, per key:

| shape | rule |
|-------|------|
| set | `members(K) = (base(K) ∪ overlay(K)) − removed(K)`; `base(K)` is empty if `K` is tombstoned |
| scalar | the overlay's value shadows the base's |
| counter | **copy-on-write** — the first `kv-increment`/`kv-decrement` seeds the overlay from the base value, so afterwards it holds base+net |
| whole-key delete | a **sticky** tombstone shadows the base for that key; a later `kv-add-to-set` repopulates it from the overlay *only* — "deleted, then re-added fresh" |
| whole-store clear | one `::cleared` flag, after which every base key reads absent |

A base set cannot be edited, so removing an inherited member is *recorded* rather than
applied: `[::removed K]` holds the base members this fork took out of `K`. All the
bookkeeping — `::cleared`, `::deleted-keys`, `[::removed K]` — lives in the overlay under
reserved namespaced keys that no index key can collide with, which means it is exactly as
durable as the fork is and a remount needs no separate recovery step.

**`kv-count` answers the merged cardinality**, never the overlay's. The count-aware trie
is a selectivity structure — `plan/order` costs every conjunct off `count-at`, divides by
the fan-out at a position off `reads/stored-count-children`, and `prover-types/est-bindings` reads the
predicate extent's count — so a base-blind count would not be a wrong answer, it would be a silently
wrong *plan* for every query touching inherited content. `kv-intersect` merges for the
same reason: `sentexes-with-args` intersects the predicate-scoped argument roots, and it
has to see the base's postings.

**Merging is not the same as building the merged set**, and on a fork the difference is
what every query plan costs. Read the rule backwards: `(base ∪ overlay) − removed`
collapses to `base` exactly when the base is visible and the overlay holds neither members
of its own at that key nor a record of a removal there — which is the structure of nearly
every key a fork reads, since the whole point is that N processes share one base and each
writes a little. `kv-count` and `kv-members` recognize that case and hand the base's own
answer straight back, and `kv-intersect` recognizes it across *all* of its keys at once —
when every one is inherited the whole narrowing goes to the base, which then does it in
whatever representation it holds rather than in sets the merge would have flattened it
into first ([density.md](density.md)). Over a flat-map base the two roads read the same, because its
`kv-members` is a reference return; over a `:dense` base, where the posting has to be
materialized into a Clojure set first, counting through the merge cost ~13 ms per call on
a 100,000-handle root — a selectivity read, per conjunct, on a key the fork had never
written to. `lein perf --only overlay-selectivity` is the perf check. `kv-member?` is the same
observation at member granularity: it probes both sides rather than merging them, which is
what keeps the `reads/watched-rule?` membership check O(1) across the `KvBackend` protocol.

So the two roads cost differently and must answer alike, and that is what
`overlay_test`'s `count-children-answers-the-same-on-both-roads-through-the-merge` holds:
a prefix the fork has added a child under, removed one from, or both, is counted off the
merged set and reads what the child set there reads — including at the depths the merge is
most likely to confuse, a whole sentence (whose children are the contexts it is stored in)
and the leaf below it. A fork that counted a fan-out its own matcher does not see would
plan every query touching its own writes against the wrong number.

`kv-get` is the scalar/counter read and does **not** merge set values. No key in the index
is read both ways (the trie's counters go through `kv-get`, its handle sets through
`kv-members`), and a backend is free to hold a posting privately — `vaelii.impl.dense-kv`
hands back an `IntPostings` here — so merging at that op would mean type-testing another
backend's internals. `kv-entries`, whose contract *is* Clojure sets, merges properly, and
it is what an export of a fork writes.

**`kv-clear!` is O(1), and it is what makes `reindex` work on a fork:** the flag hides the
base wholesale, so clearing the merged index and rebuilding it from the merged records
means what it says. The rebuilt index is then wholly the fork's — the sharing is spent,
deliberately, because that is what the caller asked for.

## The merge model — record half

`OverlayRecordStore` is a composite `RecordStore` `{overlay base}`.

- **The id boundary.** The fork's handle counter is seeded above every handle the base holds,
  so a minted handle can never collide with a base one. A record written at a handle the
  base *already* uses is therefore an **override** — same handle, different record — and
  the overlay's copy wins every read. That is how a base record is edited without editing
  the base: `mark-premise` materializes an override before it writes, since the assumption
  strength lives on the record.
- **A base that changed between mounts.** The boundary holds over the base the handles
  were minted against, and so do the fork's removals and copy-on-write counters: a key
  the fork emptied stays deleted, so it would hide what a grown base has since added under
  it. Each mount records the base's `next-id` in the bookkeeping, and the next mount
  looks for a base record at or above it. A base that holds one has grown, and a fork
  that has written anything (a record, a tombstone, a released mark, a `reindex`) is
  refused (`:type :fork-base-overlap`, `:handles` naming the fork's own handles the base
  now also holds) rather than served over it, and the refused mount releases the fork's
  directory lock. A fork that has written nothing mounts.
  A base rebuilt in another order grows nothing, so before the fork writes a tombstone,
  an override or a released mark at a base handle it **records the base digest** there —
  the content digest of the base record, in the bookkeeping — and a mount over a base
  holding another record at a digested handle is refused the same way, naming it. A write
  at a handle the fork minted records no digest. A fork whose bookkeeping holds no watermark, mounted before it was
  recorded, is checked once by content instead: each of its own records at a handle the
  base holds must match the base's record except in its strength, as an override does.
  What none of this sees is a fork justification or except naming a base handle the fork
  wrote no state at: over a reordered base, that names the record now there.
  To carry a refused fork onto the grown base, mount it over the base it was taken
  against and import the grown base's dump with `:rebase? true` (below), which
  re-asserts the fork's premises by content and re-points each `except` at the new
  handle of its target.
- **Tombstones.** Deleting an inherited record cannot touch the base, so it is recorded
  and the read path filters it. They are sticky: an inherited record cannot come back
  through fall-through, only by being written into the overlay again (a revival, at the
  same handle).
- **Handle sets.** `sentex-ids` / `justification-ids` / `premise-ids` are
  `base ∪ overlay − tombstoned`, with released premise marks subtracted from the last.
- **Durable bookkeeping.** The tombstone sets, the released marks and the cleared flag
  live in a small `KvBackend` beside the overlay, mirrored in atoms for the read path.
  Every mutation writes through and a mount rebuilds the atoms from it, so remounting a
  durable fork over the same base serves the merged contents it was left in. An in-RAM fork
  gets an in-RAM one and pays nothing for the machinery. That one is keyed on the fork's
  `:space` and lives as long as the process, so a fork cleared and then reopened on the
  same `:space` still hides its base, as a cleared durable fork does after a remount.
  `fork` with no `:space` takes a space nothing else names.
- **A read beside the fork's writer.** Every write is ordered so that a record read on
  another thread answers the record the fork held before the write or the one it holds
  after it, and never the base's record behind an override. A deletion writes the
  tombstone before it deletes the overlay's copy, a write or a revival stores the
  overlay's record before it releases the tombstone, and `clear-records!` sets the cleared
  flag before it empties the overlay. Nothing makes the several writes of one call a
  single step: a handle set read during a deletion can already lack the handle while
  `get-sentex` still answers it, which is the per-read gap
  [storage.md](storage.md#the-single-writer-contract) states for every backend.

- **The optional capabilities cross the protocol.** A base may carry `Tallying` and
  `Prefetching` ([storage.md](storage.md)), and both are answered *through* the fork
  rather than lost at it. The three samplers ask each half for one handle instead of
  building the merged handle set, falling back to that set only when the handle sampled is
  one this fork tombstoned or released — so `nil` still means *empty*. The two tallies are
  the merged count and nothing cheaper, since `|base| + |own \ base| − |tombstoned|` needs
  both sets. The prefetch hint is forwarded to both halves; a fork's own records never
  prefetch, so it is the base's that matters — a fork `recover`s over the merged contents, and
  a base whose fetch is a round trip is exactly what the hint is for.

**Counts need no delta bookkeeping.** A `RecordStore` exposes handle *sets*, not
counts, and everything counted — `sentex-count`, `count-in-context`, `count-with-functor` —
is read off the *index*, where the merge is the trie's copy-on-write counters and the
merged root sets. So a fork's counts are exact by construction rather than by a second,
parallel accounting that could drift from the records.

## The frozen mount

A base is any `RecordStore` + `KvBackend` wrapped by `vaelii.impl.overlay.frozen`, which
answers every read and **throws on every write**. Base immutability is thus structural: a
write path that forgot to divert fails loudly at the boundary instead of silently mutating
what every other fork is reading. It is a decorator, not a file mode, so it says nothing
about how the underlying store was opened — which is what makes the composition safe
whatever the base is.

One call is deliberately not a refusal: `next-id` on the frozen record store. It hands out
a handle nobody holds and touches no stored record, and it is what the fork's id watermark
is seeded from; the alternative is a `max` over the base's whole live-id set at every
mount.

**It is the one thing a mount changes about the base**, and over a durable base the change
outlives the process. `next-id` advances the base store's monotonic counter, and the disk
record store persists that counter to `counters.nippy` on its next flush — so mounting a
fork over a `:disk` base bumps the base's stored sequence by one, permanently. The bump
allocates: it can only skip a handle, never reuse one, and recovery takes
`max(the counters blob, 1 + the highest slot id)`, so a skipped number adds no work and
loses nothing. There is no read-only way to seed a watermark, and no arrangement under
which the counter both seeds a fork and stays where it was.

## Replacing the base

`(import! fork dir {:rebase? true})` installs the export dump at `dir` as the fork's base and
keeps what the fork wrote; `koinii.deref/pull!` passes `:rebase? true`
([koinii.md](koinii.md#the-other-deployment-shape-independent-seats)). The base must be the
fork's own, one mounted from `:base` opts. A fork `fork` took over a live KB reads that KB's
stores and is refused (`:frozen-base`); import into the KB it was forked from instead. A KB
that is no fork is imported into as without the option: an empty one takes the dump, and a
non-empty one is refused `:not-empty`.

The rebase is five steps on the writer's thread:

1. **The fork's writes are read by content.** Its premises and inert sentexes become the
   forms a text KB file writes (`text/premise-entries`), each with its provenance, and a
   handle at a reference position is written as `(ist Cx S)`, with the named record's
   digest ([storage.md](storage.md#content-digests)). A base premise the merged KB holds as no
   premise is kept as its sentence and context, since the fork retracted it. An override
   equal to the base record it copies, strength included, is the base's and is not kept.
   A durable fork writes these to its directory before step 2: the forms as a delta text
   KB under `rebase-delta/` (what `export-text! {:delta? true}` writes), each file fsynced,
   then the marker `rebase-pending.nippy`, which holds the retracted premises' content keys,
   each form's provenance and captured record, and the forms an earlier marker kept (below).
2. **The own half is emptied**: its records, its bookkeeping and its index.
3. **The dump is imported into the base's stores** through a second KB opened from the
   base's opts, under `:belief? :stored`: records, justifications, premise marks and index,
   with no recover. The base records the dump's reasoner set. The fork's handle counter
   and watermark are then seeded from the new base's `next-id`, as a mount seeds them.
4. **Belief is rebuilt** over the merged contents on a second KB and installed as a
   background rebuild installs it, so the change feed receives the handles that moved.
5. **The fork's writes are asserted again** through `assert`. The forms go through
   `load-text!`'s order-insensitive rounds, each reference resolved against the merged KB
   and its digest compared. Each retracted base premise the new base also holds is
   retracted again. Last, `import!`'s `:on-replayed`, when given, is called with the
   record each premise of one record was captured from and the handle it is stored at
   again; `identity/rebase!` passes one that seals a koinii attestation again
   ([koinii.md](koinii.md#identity-and-the-write-boundary)). An exception it throws
   propagates from `import!`, and a durable fork keeps the marker for the next open or
   rebase to finish.

`assert` stores a clash and settles it, so a write the new base contradicts is kept and
belief decides between the two. The summary's `:rebase` is `{:asserted n :refused [..]
:unresolved [..] :retracted n :elapsed-ms n}`. `:refused` lists the forms `assert` still
refused after a round that asserted nothing more, with the refusal's `:type`, and
`:unresolved` the forms holding a reference no record of the merged KB answers. The
rebase logs one line (`::rebased`), at `:warn` when either list is non-empty. Each record
the fork wrote takes a new handle above the new base's range.

Step 5 ends by deleting the marker and the delta. An `open-kb` of a durable fork whose
directory holds the marker asserts the delta's forms again with their provenance and
retracts the recorded base premises again, through step 5's code
(`rebase/finish-pending!`). The marker then keeps the forms still refused, a form naming a
record the base lacks included, and the retractions of a sentence the KB holds no premise
of, a sentence a fork rule derived during the replay included; the open deletes the delta,
and deletes the marker when it keeps nothing. A crash between step
2 and the end of step 5 therefore loses none of the fork's writes. After a crash inside
step 3 the base is partly imported, and the writes it cannot hold stay in the marker. The
open logs `::pending-replayed` at `:warn`, counting the kept forms under `:refused` and
`:unresolved` and naming the kept retractions under `:kept`. The next rebase adds what the
marker keeps to step 1's capture, less a form the fork has since written again and a
retraction of a sentence the fork's own records hold, and asserts it in step 5 against the
complete base. An open whose KB refuses writes (`:recover? false`) keeps the marker, and
the next rebase finishes it before step 1, calling that rebase's `:on-replayed` with each
record the marker holds. A fork in RAM writes no delta and has nothing to recover after a
crash.

A read on another thread during a rebase answers from the fork before the rebase or after
it. The rebase holds the write side of the fork's rebase lock from the replay of a marker
an earlier rebase left, or from step 1, to the end of step 5 (`ostore/excluding-readers`).
Every public read entry point holds the read side for its call (`kb/reading`). Step 1
therefore waits for every read already running to return, and a read called during the
rebase waits for step 5 to end. The writer's thread re-enters the lock, so the rebase's own
reads and writes do not wait. A lazy seq a read returned is realized against the stores as
they stand when it is realized, as it is beside any write
([storage.md](storage.md#the-single-writer-contract)), so a seq realized during a rebase
reads the fork partway through it; `vec` the seq before the rebase to fix the answer. A
read does not realize its seq before it returns, because an extent reader's `(take n …)`
fetches n records ([api.md](api.md)). The lock covers reads of this fork only: another fork
mounted over the same base store reads the new base from step 3 on, which is the base
changing under a mounted fork (below). `overlay_test` starts a reader at the end of step 2,
at the end of step 3 and before a marker's writes are replayed, and asserts it answers as
the fork did before the rebase or after it.

**A read that starts a rebase, or waits on another thread's read, deadlocks.** The read
side does not upgrade to the write side, so a read whose callback rebases the same fork
waits for its own read to end. The lock is a non-fair `ReentrantReadWriteLock`, which parks
a new reader behind a queued writer. A read that waits on a second thread's public read of
the fork therefore deadlocks against a rebase queued between the two. A `prove` with
`:portfolio?` holds the read side while its racers run on other threads, so a prover
registered with `add-prover` that calls `vaelii.core` from a racer parks behind the queued
rebase, which waits for the `prove` to return. An `:on-replayed` fn runs while the rebase
holds the write side, so one that waits on another thread's public read of the fork
deadlocks: that read waits for the rebase to end.

## A delta

`(export-text! fork dir {:delta? true})` writes a text KB holding the fork's own writes:
the records step 1 above reads, as the forms it reads them as, and `digests.edn`, the
digest of each reference they hold ([storage.md](storage.md#content-digests)). A copy of a base record that changed nothing is not written,
and neither is anything the fork concluded, which a KB loading the delta concludes again.
A text KB has no form for a retraction, so a base premise the fork retracted is counted in
the summary's `:retractions` and not written. On a KB that is no fork, `:delta?` is
refused (`:unknown-option`).

`(load-text! kb dir {:merge? true})` reads a delta into a KB that holds content of its own:
another fork over the same base, or a KB that built the same base at other handles, since
each reference resolves against the loading KB's records. Each form goes through `assert`, so
a form the KB's content contradicts is stored and the clash is settled by belief: a
monotonic observation in the delta defeats the default it contradicts in the loading KB as
it does in the fork it came from. A form `assert` still refuses after a round that stores
nothing more, is reported under `:refused` as `{:form :context :type}`, and the rest of the
delta stays stored. A reference no record answers is `:unresolved-reference`, and one
answered by a sentex whose digest differs from the recorded one is `:canonical-mismatch`:
the two KBs canonicalize the sentence differently, as when only the loading KB declares a
predicate `symmetric`.

## A handle stays in its KB

A handle is allocated in arrival order by one KB, so two forks over one base allocate
different handles from their first own write, and a handle one seat sends names another
sentex, or none, on the next. Every exchange between seats names a sentex by its stored
content, `(ist Cx S)`, with its content digest as a checksum: a delta writes each reference
so (above), `koinii.deref` finds a marker's record by its sentence and context, and a
dispute id is a vector of digests ([koinii.md](koinii.md#disputes-and-adjudication)). A
daemon reply names a sentex as a map holding its handle, sentence and context, and its
`:digest` on request ([operations.md](operations.md#daemon--vaeliiserve)). The handle stays
the identity inside a KB: a justification, a JTMS node and an index posting hold it as a
long, and a handle survives a respelling where the content and its digest do not.

A bare handle in a reply (`assert`'s answer, a justification's antecedents, a clash
report's `:handles`) carries no content beside it, and a sentence a reply holds keeps each
`(sentexHandle n)` as stored, so both name the daemon's sentex; the sentence's `:digest`
digests each target by its content. Two seats whose equality facts differ (`rewriteOf`,
`sameAs`) canonicalize one fact into two spellings, so the content finds nothing on the
other seat or the digest check refuses it (`:canonical-mismatch`).

## Invariants

1. **Base immutability.** No overlay operation writes the base. `overlay_test` compares
   the base's records, premise marks and whole index before and after a fork asserts,
   derives, retracts and clears — byte-identical, including handles. The **id counter**
   is outside that comparison and is the one exception, above: mounting advances it by
   one, and on a durable base that lands in `counters.nippy`. No record, key, mark or
   handle assignment moves.
2. **A fork of nothing is the thing it forked.** The overlay `KvBackend` passes
   `kv_backend_test`'s adapter contract over an empty base, and
   `VAELII_TEST_BACKEND=overlay` runs the *whole suite* that way
   (`scripts/test-backends.sh`). Each `tu/fresh` there opens its fork on a new space and
   drops the one before, since a cleared fork hides its base, so every read in the run
   merges the fork with its base.
3. **Tombstones are sticky and durable.** A deleted inherited record or key stays deleted
   across a remount, rebuilt from the bookkeeping.
4. **Counts stay exact** under the frozen-base + copy-on-write-counter scheme, after adds,
   deletes and overrides alike.
5. **`reindex` and belief are unchanged** — the overlay is transparent to the index, TMS
   and query layers. That is the point.

## What this is not

This is the *storage substrate* for hypothetical reasoning, not the belief logic: an ATMS
tracks several environments inside one network, and nothing here does. It is also not a
distributed system, and not a way around the single writer: a durable base is locked by
the process that mounts it, and the forks that share it are the ones in that process's
heap. There is no coherence protocol either — a base that changes under a mounted fork is
outside the contract, except under the fork that replaced it (`:rebase?`, above). Multi-level stacks (base → fork → fork) are refused rather than
half-supported, on both roads in: an `:overlay` half declared `:overlay` is an error
naming itself, and `core/fork`'s own `:base-stores` — which names no backend to catch —
is asked directly (`mount/forked?`), so `(fork (fork base))` throws `:stacked-fork`.

See also [storage.md](storage.md), [indexing.md](indexing.md),
[density.md](density.md).
