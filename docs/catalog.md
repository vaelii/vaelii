# The KB catalog

- **Covers:** what a KB source is (six kinds), how loading, unloading and exporting run
  in the background with progress and cancellation, and what holding one costs in memory.
- **Not here:** the sequence for getting each shipped, plugin or supplied KB to a first
  load → [kbs.md](kbs.md); the reader map a corpus plugin declares itself with →
  [foreign.md](foreign.md); the registry a load runs in, and the screen that watches it →
  [web.md](web.md), "Long work as jobs".
- **Assumes:** sentex, context, `genl` / `genlCx` → [glossary.md](glossary.md).

`vaelii.browser.catalog`. Everything else in this repo assumes it is holding *the* KB. The
catalog is what makes that a choice: it lists the knowledge bases this process could
load, loads one in the background while the pages keep answering, and says which of the
loaded ones every other page is about.

Three parts, in the order a KB moves through them:

    a source          a KB you could load, as data      catalog/sources
      │  load-source  as a job: watchable, cancellable
      ▼
    an entry          a KB you have loaded              catalog/entries
      │  activate
      ▼
    the active KB     what every page reads             catalog/holder

## Sources

A source is a description, not a KB. Six kinds:

| kind | content | loader |
|------|---------|--------|
| `:core` | the CxCore vocabulary head alone | `vaelii.host.core-context` |
| `:starter` | the shipped schema-only ontology | `vaelii.host.starter` |
| `:generated` | synthesized from numbers — see [generating one](#generating-a-kb) | `vaelii.host.io.generate` |
| `:corpus` | a translated sentence corpus (OpenCyc) | a plugin's reader — [foreign.md](foreign.md) |
| `:dump` | a vaelii export dump, with or without its index | `vaelii.impl.io.import` |
| `:store` | an on-disk KB already in vaelii's own format | opened in place |

The first three ship here and are always offered. The last three are **found**, never
hardcoded: every directory on the search path is probed, and the marker its writer left
decides what it is — a corpus `meta.edn` carries the context order it was written in, a
dump's carries a `:format-version`, and a vaelii store is a `records/` directory the
record writer has stamped with its own `format.edn`. Anything else is not a KB and is
passed over, including a directory whose `meta.edn` does not read as EDN.

**The records half is the whole marker.** Requiring an `index/` beside it hid exactly the
stores worth finding: only `:disk-log` keeps a durable index on disk, while `:disk-columnar`,
`:disk-dense` and `:disk-memory` derive theirs and write no `index/` at all — so a
large store classified as nothing and could not be offered. Those are
the backends a corpus past a few million records is loaded into, `:disk-log`'s index being a
map held in RAM whatever else is on disk ([storage.md](storage.md)).

What it takes to *have* each of these — which ship here, which needs a plugin, which you
supply, and what each costs to get to a first load — is [kbs.md](kbs.md).

```
VAELII_KB_PATH=/kbs:/data/corpora    # colon-separated; each entry is a KB directory or
                                      # a directory of them, probed one level down
```

With no `VAELII_KB_PATH`, the `vaelii.kb.path` system property is consulted (the same
shape, and what a test sets — a JVM cannot change its own environment), and failing that
`./kbs` and `~/.vaelii/kbs`.

A KB **outside** the search path is named in a catalog file — `VAELII_KB_CATALOG`, the
`vaelii.kb.catalog` property, or `~/.vaelii/catalog.edn` — a vector of maps, each with a
`:path` and whatever it wants to override about what is found there:

```clojure
[{:id "archive" :name "Last quarter's export" :path "/kbs/2026-Q1-export"}
 {:id "cyc"     :name "OpenCyc 4.0"           :path "/kbs/opencyc-4.0"}]
```

That file is the **only** place a machine's own paths live. Nothing about them is in the
repo, and `sources` is recomputed per call — dropping a corpus into a search-path
directory makes it appear on the next page load, with no restart.

Recomputed per call is what makes that immediacy true, and it is also the cost: every
candidate under a search-path entry is `classify`d — a `meta.edn` read, plus a size
estimate for a `:store` — on **every** `/kbs` request. So a search-path entry is probed
for the first `max-discovered` (200) children by name, which is the number that makes
this list no exception to [web.md](web.md)'s "every list caps". A directory of converted
corpora is exactly what grows past that over time, so the cut is **named** rather than
taken quietly — on the page, and in the log — because a list that silently ends early
reads as "this machine has no other KBs". A KB below the cut is listed regardless if the
catalog file names it: an entry written down by hand is never capped, and neither are the
built-ins.

Every source carries its own `:options`: the form controls it accepts, as data. The
generator's sliders are `vaelii.host.io.generate/knobs` rendered directly, so the page
and the generator cannot disagree about a parameter's range or its default.

One of those options is worth naming here because its cost is easy to under-read. A dump's
`:belief?` (and a store's `:recover?`) governs **two** derived structures, not one: the
JTMS *and* the cached `genl` / `genlCx` closures. Left off, the KB is findable by
term and countable but has no type hierarchy at all — `types` and `contexts` come back
empty and the ontology page has nothing to draw. On the OpenCyc import
[kbs.md](kbs.md) is the route to, that is the difference between 0 types and roughly a
hundred thousand. (The figure to read is 0 versus six figures; the count itself moves with
the import profile and the plugin version, which is why it is cited rather than
restated.) Off is still the right default for a corpus
past what `recover` can do in reasonable time, which is why it is a switch rather than a
decision the catalog makes.

It is a **three-way choice** rather than a checkbox, and the catalog carries it as one
(`{:type :choice :choices [:rebuild :stored :skip]}`):

| | what lands | what it costs |
|---|---|---|
| `:rebuild` (`:belief? true`) | every justification, premise mark and provenance entry, then the `recover` | the recover, which is what a large corpus cannot afford |
| `:stored` (`:belief? :stored`) | all of the above **except** the recover — the network is left empty for one somebody schedules later | nothing now; the KB refuses writes until `recover` runs ([storage.md](storage.md)) |
| `:skip` (`:belief? false`) | records only — no justifications, no premise marks | the deductions, permanently: a later `recover` over that store believes nothing |

`:stored` is the mode that exists because the option had two ends and a corpus that could
not afford `recover` had to discard its justifications forever to say so. For a **foreign**
dialect it is the only mode that keeps them at all. An unrecognised value is refused by
name (`:unknown-option`), since anything truthy would otherwise mean `:rebuild` and run
the recover the caller asked to defer.

### A remapped load reports what its own deletions cost

A remapped load rewrites the handles embedded in stored content and **drops** the
meta-sentexes whose `(sentexHandle H)` will not resolve. The dump-id map is built before
that pass, so a deleted record's id went on resolving afterwards and both deduction
readers stored justifications, premise marks and provenance pointing at records that were
no longer there. `forget-deleted` takes those ids out of the id map **and** out of the
sentex metadata the premise marks are read off, so the reference comes back `nil` and the
readers drop it through the path they already had.

Two summary keys, and they are apart because they are different facts:

| | |
|---|---|
| **`:orphaned-ids`** | dump ids the load's own deletion left naming nothing |
| **`:dropped-justifications-orphaned`** | the deductions that went with them |

A dump also hangs deductions off sentexes it never carried, which is what the dump is like
rather than what the load did to it — so a frame is attributed to the load only when
*every* id that failed to resolve is one the load orphaned, exactly the frame that would
otherwise have resolved whole.

Three things come back with it. The store holds no dangling justification; the premise
count agrees with the roster, where before it over-counted by however many marks named a
deleted handle (`mark-premise` silently declines a handle with no record); and no
provenance entry is written against a missing handle. A store already carrying them is
repairable in place — delete every justification naming a handle `sentex-ids` does not
yield — and differs from a corrected load only in justification numbering, since a
justification never written mints no handle.

## Loading

`load-source` registers the entry, submits a **job**, and returns immediately. **One load
runs at a time** — they are minutes long and memory-hungry, and two at once would make
each other's timings meaningless and each other's memory unpredictable.

The running half is not here. A load is a job like the export beside it and the chaining
run on `/stats` (`vaelii.browser.jobs`, [web.md](web.md)), which is what gives it the thread,
the progress reading, the cancel flag and the report — so an entry carries its job's id and
**reads its status** rather than keeping one of its own, and the panel and the loader cannot
tell two stories. The status vocabulary is the registry's, whatever the job is doing:

    :running → :cancelling → :done | :cancelled | :failed

"One load at a time" is a consequence rather than a rule of its own: a load claims the
process's one writer, and the registry refuses a second job that wants it — naming the job
that holds it. An `:already-loaded` refusal is still the catalog's, since that is a
question about the entries rather than about the writer.

**The entry outlives the report, so it files the terminal status onto itself.** A settled
job ages out of the registry after an hour and its entry stays, which makes "reads its
status" a claim with an end: from that point the entry answers from its own fields, so a
load writes `:done` / `:cancelled` / `:failed` there as it finishes, from both of its ends.
Two readers make that required rather than tidy — `write-blocked?` refuses a write to a
KB whose entry says `:running`, and `unload!` refuses `:still-stopping` — so an entry left
holding the placeholder it registered with is a finished KB that is permanently unwritable
and cannot be taken down, with nothing running and no job to point at.

Progress comes back through the loaders' own `:on-progress` callback, which each of the three
long loaders takes:

| loader | phases | total |
|--------|--------|-------|
| `io.generate/load-into` | vocabulary → contexts → types → individuals → rules → facts → chaining | exact, except chaining |
| a corpus reader's `load-dir!` | topology → hierarchy → schema → memberships → facts | from the corpus's `report.edn` |
| `io.import/import-dump` | sentexes → justifications → index-entries *or* reindex | from the dump's `meta.edn` |

A load with a total gets a real percentage; one without gets a count and an indeterminate
bar, which is the honest rendering of not knowing how far there is to go. **Chaining is a
phase of the second kind even in a load whose assert phases are counted exactly**: a
fixpoint's agenda grows as it derives, so there is no total to count towards, and what it
reports instead is what it has concluded and how much agenda is left.

**Cancelling is that same callback throwing.** A loader is a tight assert loop with no
other point at which stopping is safe, so `cancel!` flags the job and the next progress
report reads that flag and throws on it. It is never a thread interrupt: one landing
mid-cascade on a durable store tears the write it lands in, which is why a KB-writing job
is left to notice however long that takes. What had already landed stays landed — none of
the loaders is a transaction — and the entry keeps its KB so `unload!` can still release
it.

That also means a phase reporting **no** progress cannot be cancelled while it runs, and
one still does: opening a large on-disk store, whose record log is scanned before anything
is said. Nothing is released while a loader is still running — `unload!` says the entry is
*still stopping* rather than clearing stores out from under a live writer.

**Forward chaining reports through the same callback** (`chain`'s own `:on-progress`), which
took a second reporting point to be worth anything: the agenda loop sees a run only
*between* datums, and the rule datum that joins over a whole corpus is one datum that can
hold the loop for a minute. So a firing reports too, and the
interval is wall-clock — about four reports a second — rather than a datum count, since
datum cost spans microseconds to minutes. A single *unproductive* join is the stretch that
still says nothing, bounded by the extent it scans. An aborted fixpoint leaves the
conclusions it had already placed, like every other cancelled phase.

Bounds are still what keep a chained load finite rather than merely interruptible: the
generator bounds cascade depth at its own layer count and passes the engine's
`:max-derivations` backstop, which the UI exposes as the derivation cap (a run overshoots
it by the last datum's fan-out, since the bound is checked between datums). A corpus has
no layer count to bound a cascade by, so there the cap is the *whole* bound — which is
why the corpus card carries one of its own.

**A chained load chains once, at the end.** Every loader asserts with `:chain? false` and
the pass runs after it, which is what the option says and the only shape that pays: firing
rules against a KB whose rules are half loaded costs more and reaches the same fixpoint.
It is also the only arrangement that can be *reported*, since a pass has a phase and a
per-assertion cascade has nowhere to say anything. Chaining is off by default, and the
cards that offer it are the two shipped ontologies, the generator and a corpus — a dump
and a store rebuild belief instead (`:belief?` / `:recover?`), which is a different
question from deriving what the rules conclude.

The KB an entry loads into is in memory by default, over a space the catalog claims
(from 100 up, clear of the block the test suite owns). Name a `:dir` and it is a durable
`:disk-log` KB there instead — which is what a corpus far past what RAM holds wants.

## Unloading never deletes an on-disk KB

This is the property to keep:

* a **memory-backed** entry has its stores cleared. They are keyed by space number and
  would otherwise hold the corpus for the life of the JVM.
* a **disk-backed** one is *closed*: the file lock released, the directory left exactly
  as it was. The same directory can then be loaded again, or opened by another process.

So the `!` in `unload!` is about the memory case, which does destroy something. Unloading
an attached daemon, or a KB registered by a caller that owns it, releases nothing at all.

Unloading the active entry falls back to the most recent one still loaded, so the browser
is never left pointing at nothing while a KB is sitting right there. It falls to a `:done`
entry and not merely to one holding a KB, which matters because of the third refusal below.

**Three things stop an unload, and each is something else still holding the KB.** Releasing
is the one operation here with no half state worth having, so it gives way rather than
racing:

| refusal | who is holding it |
|---------|-------------------|
| `:still-stopping` | its own loader — cancellation is cooperative, so the stores are the loader's until its thread returns |
| `:still-exporting` | a dump walking it record by record, with no snapshot to walk instead ([`exporting-kb?`](#and-back-out-again)) |
| `:unreleased` | nothing: the release itself threw |

**The `:still-exporting` test and the release are one step**, under the same monitor
`export-entry!` checks and submits under. They read different registries — the unload asks
the job registry whether a walk is running, the export asks the catalog whether a loader
is — so nothing but that shared monitor orders them, and outside it an unload and an
export arriving together each pass their own check. If the release lands first the walk
then dumps a KB that was emptied under it, and reports `{:ok true}` over a summary that
reads exactly like a clean export. The entry is dropped inside the monitor too, so an
export held at the entry point finds it gone rather than finding it released.

The first two are retried after the thing holding the KB lets go. The third is the
truth-telling one. A release can fail — an index that will not fsync, a component that
throws on close — and logging that and dropping the entry would tell the operator it had
released a KB it had not. So the entry keeps its place with status `:unreleased` and the
reason on it, stops being active (a KB whose stores half-closed is the one thing here
nobody can vouch for, so the fallback above steps over it), and the throw is what stops
the caller reporting a clean unload over a directory that did not close. Unloading again
retries the release.

`unload!` takes `:run-in` for the same reason `export-entry!` does: the browser hands its
write monitor, so a synchronous write already past the write entry points drains before the stores
go rather than interleaving with the clear.

## And back out again

`export-entry!` writes a loaded KB out as an export dump, as a job on the same discipline a
load runs on: progress recorded where the page already looks for it, and cancellation by
the progress callback throwing — which `export!` calls at each chunk boundary, the only
point at which stopping leaves a directory rather than a file half-written. It claims **no
writer**, because a dump is bytes on the filesystem rather than a KB, so a load may run
beside it.

It is deliberately **not** an entry. An export produces no KB, and filing it as one would
put a second handle on a KB somebody could then unload out from under the writer. The
newest export job in the registry is the panel's report — which is what lets it say where
the dump went after the job has finished.

That report is the newest export of **any** status, which is why `cancel-export!` does not
read it: cancelling the newest would ask about a dump that finished an hour ago and is
already written. It asks the *running* set instead, and answers false when nothing is
running — as `jobs/cancel!` itself does for a job that has already settled.

That closes the loop. `classify` keys on `meta.edn` and `export!` writes it **last**, so
the moment a dump lands under the search path it is a `:dump` source, and export-then-reload
is two clicks that never leave the browser. The same ordering is what keeps a **partial**
dump out: a cancelled or failed export leaves a directory with no `meta.edn`, which
`classify` does not recognise and `sources` does not offer.

Three refusals, each about something an export cannot be correct in the face of:

* **another export is running.** One at a time. A *load* is not refused and does not
  refuse this — a load fills some other KB, and blocking on one would be a rule about
  this process's busyness rather than about the dump.
* **the entry is not an in-process KB.** A daemon serves its KB from another host, and
  that is where its dump would be written — so the export belongs to the daemon's own
  surface, not to a form here naming a path on the wrong machine.
* **the KB is still loading** (`write-blocked?`). `export!` walks it record by record
  with no snapshot to walk instead, so a dump of a KB something is still writing is a
  dump of no single state.

The `!` in `export-entry!` / `cancel-export!` is for what a stopped one leaves behind: a
directory holding part of a dump. Not a *loadable* dump — but bytes on disk that nothing
here will clean up.

## What it costs to hold

Loading a corpus is mostly a memory decision, so the catalog answers two questions of
different kinds and keeps them visibly apart.

`heap` is a **measurement** — `{:used :committed :max}` off the memory MX bean — and it
belongs to the whole JVM: every loaded KB, the browser itself, and whatever garbage has
not been collected yet, in one figure that cannot be attributed to anybody. `:used` drifts
up between collections and drops without anything being freed, so it is the structure of a
curve rather than a number to subtract KBs from.

`footprint` is an **estimate** for one KB, and the only per-KB answer there is: the
alternative is to unload it and diff the heap, which is not something a page may do to a
KB somebody is reading. It multiplies the stored sentex count — one O(1) trie read, so
this is inexpensive enough to run on a page that polls — by what a sentex measured per resident
component (`resident-bytes-per-sentex`, from the `lein bench-scale` sizing runs):
~1,549 B of index, ~279 B of records, ~101 B of truth-maintenance network (the dense
default — 18 B/node + 166 B/justification; the reference map is ~467 B/sentex, ~3.8×
more — see [density.md](density.md)). Two adjustments make it about *this* KB: a `:disk` KB
pages its records, so that term drops (what stays resident is the bounded hot-record LRU,
which does not grow with the corpus), and a KB loaded without belief — an import with
`:belief? false`, a store opened without `:recover?` — has no network, so that term drops
too.

The error term is **sentence shape**: a lean arity-2 fact indexes at the coefficient
above, a rich one with compound arguments measured ~2,158 B. The leaner figure is used, so
a corpus of fat sentences reads low. `predicted-footprint` puts a source's own count of
what it holds through the same coefficients — what loading it *would* cost, which is the
number that decides whether to load it at all.

## The switch

`holder` is a deref-able that yields the active KB (or a fallback when nothing is
loaded). `vaelii.browser.web/app` takes one of those in place of a KB and resolves it **per
request**, so activating another entry re-points every page at once with no restart and
no handler rebuild. A KB or an access value still works — `app` takes any of the three.

Anything **holding a KB** can be activated, a load still running included. The only
refusal is an entry with no KB yet, and that is a statement about there being nothing to
read rather than about the load.

A half-loaded KB answers about what has landed, which is a *prefix* and not a wrong
answer — the ordinary open-world condition this engine is built on, where an absent fact
never means a false one. Reading beside the loader is sound for the same reason a reader
thread beside the writer is: one writer, and every store mutation lands atomically
([storage.md](storage.md), the single-writer contract). So what a reader is owed is being
*told*, not being refused.

`active-caveat` is what tells them — nil when the active KB is finished and believed,
otherwise the two things that can be less than the whole truth, reported separately
because they are independent:

* the load is **still running** (or stopped part-way), so what is stored is a prefix of
  what was asked for;
* **belief and the taxonomy are not built** — `recover` builds them together, and both
  `:belief? false` and `:belief? :stored` leave them for later. That empties more than
  queries: with no JTMS every believed answer is empty, and with no genl/genlCx closures
  there is no type hierarchy either, so a fully stored KB renders as one holding no types
  and no contexts at all.

The second is the one that matters most, because it **outlives** the first. A store
opened without `:recover?` finishes its job `:done` and stays that way, and so does a
dump imported without belief — the dangerous case is the one that looks finished. The browser puts both
at the top of every page ([web.md](web.md)).

**And it says which of two repairs applies**, because they are not the same size. A KB
whose store holds justifications or premise marks has everything `recover` reads, and
recovering it is one pass over what is already there — that is what `:belief? :stored`
loads. A KB holding neither cannot be recovered into belief at all and has to be loaded
again; for a **foreign** dialect `:belief? false` always leaves it in that state, since
that path rosters no premise. `active-caveat` probes the store and reports
`:recoverable?`, and prescribing the reload to the first case would send it back through
hours of work for nothing.

What activating a half-loaded KB costs is exactly one thing: **the right to change it.**
`write-blocked?` says so — the loader is already this process's writer, and two
interleaved writers are not serializable, so the reads stay open and the writes wait. It
is asked of a *KB*, by identity, rather than of whichever entry is active: a second KB
loading in the background is no reason to stop writing to the one on screen, and a caller
holding a KB the catalog never heard of is nobody's loader's business.

This is what makes fast open worth having twice over. A `:store` that opens in seconds is
browsable while `recover` rebuilds belief behind it, and a corpus is browsable from its
first thousand sentexes — the wait stops being a wait.

## Generating a KB

`vaelii.host.io.generate` synthesizes a KB from a handful of numbers — types,
individuals, predicates, facts, rules, the forward/backward mix, how many are defeasible,
how deep the type tree branches, how many contexts the facts spread over, and the seed.

Two properties make it a measurement rather than noise:

* **Deterministic.** Each of `plan`'s three draw streams — memberships, rules, facts —
  owns a `java.util.Random` seeded from the plan seed and the stream's own constant, so
  the same parameters give the same KB whichever order a reader realizes the streams
  in. `plan` is pure — the whole KB as data, nothing asserted — and `load-into` asserts
  it.
* **Stratified.** Predicates are split into layers; facts populate layer 0, and a rule
  concluding a layer-*k* predicate draws its antecedents only from below *k*. The rule set
  is acyclic, so forward chaining cascades base → derived → further-derived and
  terminates. The chain is additionally bounded at `layers + 1`, since a derivation over
  this rule set cannot legitimately go deeper: anything that does is a join fanning out
  over itself, and the bound turns that into a *truncated* run rather than one that does
  not come back.

Individuals and predicates are Zipf-sampled, so the corpus has hot terms and a long tail
like a real one. Generated names carry their role in their spelling, as the naming
invariants require: `gen_type_7`, `GenInd42`, `genRel3`, `CxGenBand0`.

A rule's **direction and its defeasibility are two independent draws**, each a percentage
against the rule stream's own generator, so the four combinations all occur and the mix is
a share rather than an exact count. Read off one rule index they would be perfectly
correlated — at any settings where `defeasible` ≤ `forward`, every defeasible rule would
also be a forward one, and no settings at all would produce a defeasible *backward* rule.

The fact contexts are a **chain**, not a fan of siblings. Two incomparable contexts
have no common descendant, so a rule joining a fact from each would complete with nowhere
to put its conclusion (`:no-placement`, in `violations`). Down a chain every pair is
comparable and the conclusion lands in the deeper of the two.

## What this is not

The catalog is **process-local**: it is the browser's own state, not a KB's, so nothing
about it is stored, nothing survives a restart, and the daemon (`vaelii.host.serve`) does
not serve it. A browser started with `--attach` registers the daemon as an entry it reads
and can load local KBs beside it, but it cannot make the daemon load anything.
