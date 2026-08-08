# The change feed

- **Covers:** what `watch` delivers to a listener when belief moves — every change for a
  plain listener, or a standing query's filtered subset, one event per settle.
- **Not here:** the operational surface a daemon serves, which has no way to push a feed
  across the wire → [operations.md](operations.md); the one-shot before/after diff for a
  batch not yet committed → [preview.md](preview.md).
- **Assumes:** sentex, context, settle, justification → [glossary.md](glossary.md).

`core/watch` — be told when belief moved, instead of asking again.

```clojure
(watch kb f)                      ; every belief change      => token
(watch kb goal context f)         ; a standing query         => token
(unwatch kb token)                ; => bool
(watchers kb)                     ; => [{:token t} {:token t :goal S :context C} …]
```

`f` is called with one argument, in [preview.md](preview.md)'s entry shapes, so an
application renders a preview and a feed with one renderer:

```clojure
{:believed-added   [{:sentence S :context C :handle h :premise? bool
                     :justification {:informant i :rule S :antecedents [S …]}} …]
 :believed-removed [{:sentence S :context C :handle h :reason kw :detail {…}} …]}
```

A standing query's entries carry `:bindings` as well — which solution moved.

## Why this exists

Without it every application built on this engine polls: re-run the query, diff it
yourself, guess an interval. That is wrong in the two directions polling is always wrong
in — it misses changes between polls, and it costs the most on the KBs where the least is
moving.

Nothing here computes anything new to fix that. A settle already knows the **region** it
relabelled and which of that region was believed when it first touched it; `preview` and
`edit-with-consequences!` already turn that pair into a belief diff and render it. The
information a feed needs was being computed on every mutation and then thrown away.

This is not a cache and not a materialized view. The three are easily conflated under
one heading, and they are three different features; this is the one that exists.

## Belief, not storage

Delivery hangs off the **settle** — `settle/settle`'s tail, through
`feed/deliver!` — and never off the store choke points. The difference is not cosmetic.
An `assert` stores a sentex whose label several later justifications settle, so a
store-time event would announce content the KB does not believe, and then stay silent
when it comes to believe it. Forward chaining makes that routine: one `assert` stores
dozens of conclusions before the settle that decides any of them.

`vaelii.impl.observe`'s two observers *do* fire at `kb/create-sentex` and
`integrate/sentex-removed!`, and correctly — an incremental matcher's alpha memories
mirror the stored fact set, which is a storage question. Belief is not, so the feed reuses
`observe`'s *shape* (a leaf indirection both layers can see) at a different altitude.

**Only a stored sentex can be reported.** A TMS datum is a stored sentex, so only a
stored sentex enters or leaves belief. An answer that exists solely while a prover is
computing it — an evaluable, an aggregate, `unknown`, an `argIsa` type inference, a
`set/backwardRule`'s conclusion — is nobody's belief and no relabel carries it. That is
the same limit `preview` and `edit-with-consequences!` have, and it is why `watch` refuses
a goal of that shape rather than watching it silently for nothing (below).

## The event is a region diff

`settle-finish` decides, once, what the settle moved: the relabelled regions
(`jtms/touched`) plus the flips no relabel records, and which of that set was believed
before (`jtms/touched-in`). Three destinations then read the same answer — the caller's
`*touched-sink*` / `*touched-in-sink*` (which is what `preview` and
`edit-with-consequences!` bind) and the feed's own accumulator. One place decides, so
three mechanisms cannot disagree about what a batch meant.

`core/moved-handles` turns region + before-labels + belief-now into `[added removed]`, and
both the consequence report and a feed event call it. An application that got different
answers from the two would have no way to tell which was the KB's.

The alternative — snapshot the believed set, mutate, diff — is O(KB) per write and is
what [preview.md](preview.md) measures at 4.4 ms / 41.6 ms / 401 ms over 2.7k / 23k / 224k
sentexes. `lein perf`'s `feed-listener-scaling` is the gate that says the feed does not do
that; wired to diff the believed set it reads 7.2× growth against a 2.0× bound, and 0.7×
as built.

## One settle is one event

A batch under `with-deferred-settle` / `assert-many` / `edit!` settles **once**, so it is
one event whose halves are exactly what `edit-with-consequences!` reports for the same
batch. A conclusion derived and then defeated inside the batch appears in neither: a feed
reports what *changed*, not what happened on the way.

A teardown is the one operation that settles more than once — revive, re-derive what the
removal released, settle again — and `core/retract!` and `core/edit!` therefore **hold**
the feed for their duration (`feed/with-one-event`). The regions union and one event is
delivered. Delivered per settle instead, a datum that went OUT in the first pass and
revived in the second would arrive as a removal followed by an addition when the
operation's net effect on it was nothing; that flicker is the same failure a preview
would send, and the reason for both suppressions is the same. Holds nest, so the orphan
sweep's retractions inside a retraction stay inside one event.

## A standing query is a filter, not a re-run

`(watch kb goal context f)` matches the region's entries against `goal` with
`res/match1` — the same subsumption a rule antecedent gets, so `(animal ?x)` is answered
by a stored `(dog Muffet)` through the `genl` closure and `(parentOf ?x ?y)` by a stored
`(fatherOf Tom Bob)` through the predicate hierarchy. One cached closure lookup per
candidate.

It does **not** re-run the goal, and that is the point: a listener that re-queried would
make every mutation cost a query per listener, which is the cost polling already had.

Context-scoped like every other read — the sentex must sit in a context the watch's own
can see, up the `genlContext` cone. A **variable** context (`'?ctx`) watches every context
and binds to the one that answered, the convention `ask` already takes.

`f` is not called at all when nothing the goal answers moved, so an unrelated write is
silence rather than an empty event. And the expensive half of an event — a supporting
justification and a `why-not` apiece — is a `delay`: a KB whose listeners are all standing
queries filters to its own matches first and never builds the full set.

## What is refused

Being incomplete is one thing; being quietly wrong is the thing a feed must not be. A
goal whose truth is a function of something the region does not hold is refused
(`:type :not-watchable`) rather than watched for nothing:

| refused | because |
|---|---|
| a **vector** conjunction | it joins against facts the batch never touched |
| an **aggregate** (`agg/count` …) | its value is a property of a whole answer set |
| **`unknown`** | a fact *leaving* belief can flip it, with nothing about the flip in the region |
| **`thereExists`** | the same — existence over the KB, not a property of one entry |
| an **evaluable** (`evaluate`, `lessThan`, `different`, the quantity comparisons) | computed and never stored, so no relabel carries it |
| **`ist`** | a watch already takes its context as an argument, and no stored sentence has that functor |

Reach for those with `query` on a plain listener: the event says belief moved, and the
query says what it is now.

A **negated** goal needs no special handling — a `:truth :false` sentex stores the `not`
in its sentence, so `(not (dog ?x))` and `(dog ?x)` separate on the ordinary unification,
and a positive watch does not fire for a believed negation.

Two more refusals are about the *call* rather than the goal, and both catch a silent
nothing:

- **A goal with no context to scope it.** A context naming nothing sees nothing, so the
  watch would match forever and report never. Pass a context symbol, or a variable for
  every context.
- **A listener that is not a function.** `fn?` (or a var naming one), deliberately not
  `ifn?`: a *symbol* is `ifn?`, so `(watch kb 'someGoal)` — the three-argument form
  written with two — would register the goal as the listener under `ifn?` and fail much
  later, at the first delivery, having said nothing at the call that was wrong.

## Ordering and reentrancy

**Listeners run after the settle, never inside it.** By the time `feed/deliver!` runs, the
fixpoint is reached, the taxonomy caches are reconciled, the readings are recorded and the
touched set is cleared. So a listener may read the KB freely, and may **write**: an
`assert` from a listener is an ordinary assert that settles and files a region of its own,
which the delivery loop picks up in the next round. The listener sees its own writes as a
second event.

Listeners never **nest** — the writing listener's own `deliver!` declines the claim
another frame holds — so no listener ever sees a half-relabelled KB. A listener that
writes on *every* event it receives is an infinite loop, and it is the listener's bug;
the loop gives up after 64 rounds with a `:warn` rather than hanging the writer.

A listener's writes are also fenced off from the caller's diff: `*touched-sink*` and
`*touched-in-sink*` are unbound for the duration of delivery, so an
`edit-with-consequences!` never reports a listener's assertions as consequences of the
batch.

**Delivery order is registration order**, and the *content* of a batch does not depend on
it: the diff is computed once, before any listener runs, so a listener that writes cannot
change what its neighbours are told about this event — only produce a further one.

A listener that **throws** loses its own event and nothing else. It is logged at `:warn`
with its token, the remaining listeners still run, and the settle it was hearing about is
already committed — aborting there would leave the KB settled and every other listener
uninformed, which punishes the wrong party.

`unwatch` takes the token and is idempotent; a token is monotone per KB and never
reissued, so dropping a stale one removes nothing and says so. A listener may drop
itself mid-delivery: the registry is read once per event, so editing it cannot make the
loop skip or repeat a neighbour.

**`f` runs on the writing thread**, synchronously, inside the `assert` that caused it.
That is what makes a listener's own write an ordinary write and lets it read a settled
KB — but it also means a slow listener slows the writer, and this engine has one
([storage.md](storage.md), "The single-writer contract"). A listener that does real work
should hand the event to a queue and return.

## What does not arrive

- **A mutation that moved no belief.** Re-asserting a stored sentex relabels its region
  and changes no label, so both halves are empty and nothing is delivered.
- **Anything during a `preview`.** It stores, settles, reads the diff and takes every
  write back; a feed through one would send a change and then its exact reverse, and an
  application told that learned nothing and has probably already acted.
  `feed/*enabled?*` is off for the whole preview, **rollback included** — the rollback is
  the half that would send the retraction.
- **Anything during `recover` / `reindex`.** They relabel everything, so a feed running
  through one would hand a reconnecting application the whole KB as newly believed. Off
  under `settle/*rebuilding?*`, the same gate the disjointness exposure pass takes and for
  the same reason: the entry means *newly*, and on a rebuild there is no newly.
- **A datum the dependency-directed sweep deleted.** It is in the region with no record
  left to describe, so it is dropped rather than guessed at.
  `edit-with-consequences!` has the same gap; `preview` is what answers "what would this
  removal take with it", since it suspends instead of retracting and can still name every
  casualty.
- **A spelling an equality merge displaced.** A merge supersedes the displaced sentex on
  the **assert** path, and the before-labels hand-off covers only what a *settle*
  supersedes — so the displaced spelling loses belief with nothing in the region saying
  it did. `edit-with-consequences!` misses it identically (the two agree, which is the
  contract, and a test pins that they do); `preview` reports it as `:superseded`, because
  its rollback lets it read belief-before off the restored KB instead. Closing it means
  the equality path posting the displaced handle where a settle can see it, which would
  move `edit-with-consequences!`' answer too — a change to that mechanism, not to this
  one.
- **A batch that threw.** `edit!` is not a transaction: a throw mid-batch leaves what was
  already stored in place with the settle not run, so there is nothing to deliver *yet*.
  Nothing is lost — the region is still uncleared, so the next settle reports it.

## Cost

A KB with **no** listener pays one deref per settle (`feed/watched?`) and accumulates
nothing. A KB **with** one pays per relabelled region — never per stored sentex, and never
a re-run of a goal.

Mean µs per `assert` of a two-argument fact, best of five runs over the last fifth of each
load, by what is attached:

| listeners | 250 facts | 2 000 | 8 000 |
|---|---|---|---|
| none | 126.7 | 143.2 | 142.6 |
| one plain | 138.8 | 147.2 | 152.1 |
| one standing query | 141.6 | 157.4 | 156.9 |
| both | 151.3 | 160.2 | 164.4 |

Flat in the stored set in every row, which is the claim. The ~10 µs a listener adds is one
event's worth of work: a `moved-handles` walk over a one-handle region and, for a plain
listener, one supporting-justification lookup to render it.

A batch whose conclusions **cascade** produces a proportionally larger event, because the
region is larger — that is the answer being asked for, and `:max-derivations` on the write
is what bounds it. An event is built once per settle and shared by every listener.

## Tests

`test/vaelii/feed_test.clj` — 35 tests over four themes:

- **Altitude**: a defeat and its revival arrive as two events in opposite directions; a
  derived conclusion arrives with the rule that derived it; a re-asserted sentex is not
  news; a `preview`, a `recover` and a `reindex` are silent; an `assert-inert` arrives
  nowhere in either direction (it is never a TMS datum, so there is no label to move);
  `forward-chain` delivers what it derived; registering a listener moves no belief.
- **Granularity**: a three-fact batch is one event; a teardown that releases an exception
  and re-derives what it swept is one event; a batch that threw reports nothing and the
  next settle reports what it left; the feed and `edit-with-consequences!` are the same
  answer on the same batch — two mechanisms sharing their entry shapes and nothing else,
  so agreement is evidence rather than tautology, and an equality merge is pinned
  separately because it is where they agree about a *gap*.
- **Reentrancy**: delivery is registration order; a thrower loses its own event and its
  neighbour still runs and the write stands; a listener that asserts is delivered its own
  event in a second round, and one that asserts on *every* event stops at the bound
  instead of spinning; a listener may `unwatch` itself mid-delivery without disturbing
  its neighbours; **a listener's own writes are not reported as the batch's
  consequences** — the sinks are closed for the duration, or an
  `edit-with-consequences!` would attribute them to the caller.
- **Honesty**: a standing query fires only on what answers it, through a subtype and a
  sub-predicate, up the `genlContext` cone and no further; eight unanswerable goal shapes
  are refused and register nothing, as are a goal with no context and a listener that is
  `ifn?` but not a function; two live KBs never hear each other and a fork inherits no
  listeners.

Two cost claims are tested rather than asserted. `lein perf`'s
`feed-listener-scaling` is the scaling gate, over both listener shapes at once because
the standing query is the one that would re-run something. And the `delay` over the
entries is pinned by counting calls at the renderer: a standing query whose goal matches
nothing must render **zero** entries, where a plain listener renders the diff.
