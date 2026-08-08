# The lookup-to-query stack

- **Covers:** the eight-level stack from a raw index read to full backward chaining, and
  `escalate`/`explain-levels` for naming which level a goal needs.
- **Not here:** the forward/backward chaining machinery levels 6–7 wrap →
  [inference.md](inference.md); the retired-spelling filter levels 3–4 apply but do not own →
  [equality.md](equality.md).
- **Assumes:** sentex, context, `genl`, prover → [glossary.md](glossary.md).

`vaelii.impl.levels`, surfaced as `core/lookup`, `core/escalate`, `core/explain-levels`,
`core/levels`.

Retrieval in this engine is not one thing. The trie knows nothing but paths;
`raw-match` adds unification; `matches-visible` adds context inheritance; the
prover engine adds closures and rules. Those layers already existed — the stack
just **names them and gives them one call shape**, so the cost of an answer is
legible instead of implicit.

```clojure
(v/lookup kb 4 '(animal ?x) 'MantleContext)
;=> ({:level 4 :handle 41 :sentence (dog Muffet) :context MantleContext :bindings {?x Muffet}})
```

## The eight levels

Each level adds **exactly one** mechanism to the one below it. That is the whole
point: a result that appears at level *n* and not at *n-1* is attributable to that
mechanism and nothing else.

| L | name | adds | built on |
|---|------|------|----------|
| 0 | `:raw` | nothing — handles at an index location | `p/lookup` |
| 1 | `:extent` | one literal context, narrowed by functor | the context + functor roots |
| 2 | `:local` | unification + the symmetric mirror | `res/raw-match` |
| 3 | `:visible` | context inheritance (`genlContext` up-closure) | `res/raw-match` per context |
| 4 | `:typed` | predicate inheritance (the `genl` spec walk) | `res/matches-visible` |
| 5 | `:closed` | transitive closure for transitive predicates | + the transitive provers |
| 6 | `:solved` | the whole prover registry, no member of which expands a rule | `provers/solve-goal-with` — what `ask` runs |
| 7 | `:proved` | rule expansion (backward chaining) | `res/prove-seq`, with the registry as its leaf |

Level 0 is the only one that addresses the index directly: a **vector** goal is
taken as an index path, a sentence is turned into one through `kb-sentex`. It
interprets nothing — not belief, not polarity, not the goal's arguments beyond what
the path encodes.

Level 1 is candidate retrieval, not matching: it intersects the context root with
the functor root and does **not** look at arguments. Both roots carry O(1)
cardinality, so it drives from whichever is smaller.

Level 3's fan-out up the `genlContext` cone is also what *creates* a retired spelling,
so the reader-scoped filter that drops one belongs to it: a fact stated above an
equality merge is believed where it lives — its own context was told nothing — while a
context below the merge sees both it and the twin migration placed there. Reading up
the cone without `res/without-retired` would hand one fact back twice, under two names
the reader knows denote one thing ([equality.md](equality.md)). That is an artifact of
the fan-out rather than something the fan-out found.

Levels 6 and 7 differ by exactly one mechanism: level 6 is the registry, none of whose
members expands a rule, and level 7 wraps it in the recursive chainer with the registry
as that chainer's *leaf*. So level 7 adds rule expansion and nothing else.

Both of them **prepare the goal the way `ask` does** — a ground reifiable NAT reified
to the constant it denotes ([nat.md](nat.md)), a term an equality merge retired
rewritten to its class representative. That is what makes level 6 the same question
`ask` asks rather than a near-miss of it, and it is a truth question rather than a
storage one, which is why levels 2–5 match the goal as written.

## `sentexes-matching` is level 2

`core/sentexes-matching` — the public believed-literal match — **is** level 2. It calls the same
`res/raw-match`: one literal context, no subtype fan-out, unification, the symmetric
mirror, belief-filtered. So a `sentexes-matching` pinning an argument *after* a variable
(`(parentOf ?x Tom)`) shares `match-one`'s argument-root divert — it reads the
predicate-scoped argument root (`[:argument-root parentOf 2 Tom]`) instead of fanning
the whole first-argument column — while a fully-ground or left-prefixed query keeps the trie,
none of which `sentexes-matching` has to know about.

It adds exactly three things level 2 does not, all **questions about truth** rather than
about storage:

- the **`except` visibility filter** (`res/without-excepted`) — a believed
  `(except (sentexHandle H))` visible from the query context hides `H` there and in
  every context that sees it ([contexts.md](contexts.md));
- the **retired-spelling filter** (`res/without-retired`) — the reader-scoped half of
  supersession. A fact stated above a merge is believed where it lives, while a context
  below the merge sees both it and the twin migration placed there; this drops the
  spelling that reader has retired, so a count over an answer set means something
  ([equality.md](equality.md)). Seeing both is a *cross-context* read, so this one also
  belongs to level 3 and is applied there — level 2 stands in one literal context,
  where there is no second name for the fact to arrive under;
- the **equality goal-rewrite** (`kb/rewrite-goal`) — a goal naming a term an equality
  merge retired is rewritten to the class representative first, so the old spelling
  stays a usable question even though it is no longer a usable answer
  ([equality.md](equality.md)).

`sentexes-matching` returns the stored sentex records; level 2 wraps each in the uniform result
map. Everything else is shared, so the two cannot drift — `levels_test` pins it: the
`sentexes-matching` core equals level 2 over a spread of goal shapes, and the `except` filter and
goal-rewrite are exactly what distinguishes them.

## Uniform results

Every level yields the same map, with `nil` where a level cannot supply a field:

```clojure
{:level 4 :handle 41 :sentence (dog Muffet) :context MantleContext :bindings {?x Muffet}}
```

Levels 0–4 answer from a stored sentex and carry its `:handle`. Levels 5–7 answer
through provers that return bindings only, so `:handle` is nil and `:sentence` is
the goal seen through those bindings — the answer is *derived*, not stored.

Level 5 is the one level whose results are a mixture of the two, and the fields the
two halves fill do not line up: a stored match carries the sentence it was stored
**as** and the context it was stored **in**, while a derived one carries the goal under
its bindings and the context it was **asked** in. So for any fact inherited from a
general context — every taxonomy fact a story context reads — the closure's re-derived
copy agrees with the stored match on neither field, and a dedup keyed on either would
call one answer two. What identifies an answer is the **goal seen through the
bindings**, and that is what the fold keys on: a derived answer a stored result already
carries is dropped, so the surviving result is the one with provenance. The fold is
**one-way** — two stored matches carrying one answer are two *facts*, and level 5 is
level 4 plus a mechanism, never level 4 minus a duplicate.

`:level` is the level of the *lookup*, not a claim about where an answer first
became reachable. `explain-levels` is what answers that question.

## Monotonicity, and the two joints where it is not free

Climbing must never *lose* an answer, or a level's contribution is the net of two
effects and reads as neither. Levels 3–5 are wider calls to the same matcher and level
5 is literally `level 4 ∪ the closure`, so across those an answer reachable at one rung
is reachable at the next. Two joints are not like that, and naming them is half of what
naming the levels is for.

**1 → 2 narrows.** Level 1 is candidate retrieval and never looks at the goal's
arguments; level 2 unifies. So for any goal that pins an argument, level 2 is a
*subset* of level 1 — which is one of the two reasons `escalate` floors at 2.

**3 → 4 can drop an answer.** Level 4 is `res/matches-visible`, which reads the
`except` visibility filter that `res/raw-match` does not. A sentex a believed
`(except (sentexHandle H))` hides from the view context is therefore matched at levels
2 and 3 and gone from level 4 up. Level 4 is right and the engine agrees — `ask` denies
that goal too. What it costs is `escalate`, which will name level 2 as the machinery
sufficient for a goal the engine refuses. **No floor rules that out**: whether a level
over-reports is a property of the KB, not of the level, so the way to see it is
`explain-levels`, where the drop at level 4 is on the page.

From level 4 up the content holds. Levels 6 and 7 delegate to the real engine and
inherit its behaviour — including the short-circuit where a prover claiming
`completeness` 100 runs **alone**. For a `genl` goal, level 6 returns the taxonomy
closure rather than the union of closure and stored facts, so an answer that carried a
handle at level 4 may arrive without one at level 6.

The **content** does not bend, only the provenance, and that is what `completeness`
100 claims: *my answers are a superset of what every other applicable prover whose
sources I read would answer for this goal*. The closure is built from the very edges
level 4 reads, so it contains them; it hands back a derived answer rather than a stored
one.

What stops that claim from over-reaching is not the prover but the **engine**.
`provers/sole-prover` asks `provers/shadowing-channels` whether this KB could reach the
goal by a route no computed prover reads — an `(argPreserving P n R)` declaration
(`:preserving`), a rule concluding the goal's predicate or a spec of it (`:rules`), or a
declared `(inverse P Q)` (`:inverse`) — and if any of the three bears, nobody runs alone
and the union runs instead, whatever was claimed. So above level 4 a result never
*disappears* going up the stack; it can only lose its handle.

That is the engine being honest about its own dispatch rather than the stack
papering over it. If you want the stored sentex behind an answer, ask at the level
that reads the store.

## Operators

**`escalate`** climbs from a floor and stops at the first level that answers —
the cheapest machinery sufficient for a goal:

```clojure
(v/escalate kb '(animal ?x) 'MantleContext)
;=> {:level 4 :name :typed :results (...) :tried [2 3 4]}
```

Because every level is lazy, the climb costs *one result* per level tried, not a
full answer set per level.

The floor defaults to **2**, not 0. Levels 0 and 1 answer questions about
*storage*, not truth: level 1 ignores the goal's arguments (that is what level 2
adds) and level 0 ignores belief (a defeated sentex still has a handle in the
trie). Either will report a hit for a goal it cannot verify — `(genl dog thing)`
gets an "answer" at level 1 from some *other* stored `genl` fact in the same
context, when the real answer is the closure at level 5. Escalating from 0 would
name the wrong mechanism, which is the one thing escalate exists to get right.
Pass an explicit floor of 0 when you want the retrieval levels included.

A floor is the coarse half of that guard and the only half a constant can supply. The
`except` filter enters at level 4, so a goal whose only stored answer is excepted is
reported here at level 2 while `ask` denies it — see the monotonicity section above.
That depends on the KB rather than on the level, so no floor rules it out.

**`explain-levels`** runs all eight and reports what each yields. The level at which the
count first rises is the mechanism the answer depends on:

```clojure
(v/explain-levels kb '(animal ?x) 'MantleContext)
;=> ({:level 3 :name :visible :count 0}
;    {:level 4 :name :typed   :count 3}   ; <- the genl spec walk is what answers this
;    ...)
```

It counts, so unlike `lookup` it realizes every level fully. It is a diagnostic.

**`levels`** returns the table as data (`:level :name :below :adds`).

## Laziness

Every level returns a lazy seq, and **taking one result costs strictly less than
taking all of them**. Concretely: a record fetch, an expensive prover's `solve`,
and a rule expansion are each paid per result *consumed*.

Three things make that true:

- **`match-one` yields `[handle bindings stored-sentex]`.** The record was already
  fetched to unify against, so it rides along instead of making a caller that wants
  the matched sentence pay for a second round trip. Callers wanting only bindings
  destructure `[_ b]` and ignore it.

- **`res/lazy-mapcat` replaces `mapcat` on every fan-out** — over contexts, over
  subtypes, over provers. `clojure.core/mapcat` is `(apply concat (map f coll))`,
  and `map` realizes a whole 32-element chunk at once, so an ordinary `mapcat` over
  a handful of contexts expands *every* one (each its own trie walk) before yielding
  the first result. That defeats the cheapest-first prover ordering entirely: every
  applicable prover's `solve` would run before the first solution came back.

- **Level 7 streams a search that has no bound.** The recursive chainer is a
  `loop`/`recur` that runs to completion, so it cannot itself be lazy: it holds a search
  scope open for its length (`observe/with-search-scope`), and a lazy seq escaping that
  scope would realize later with the pin and the closure memo gone. `res/prove-seq`
  resolves that without a second engine — the chainer is already *resumable*, so it runs
  capped at one result, yields it, and resumes from the stack it left when the consumer
  asks again. Each pull is one eager segment inside its own scope, which is sound because
  a query mutates no belief for a pin to hold still against.

  This matters most at the level where it is least affordable. Level 7 is unbounded — it
  terminates on the data, not on a depth — so it is the level whose full answer set costs
  the most, *and* the one `escalate` reaches last and the browser is most likely to be
  paging. A level 7 that realized everything before returning would make merely asking
  whether it answers cost the whole search.

Some costs are inherent rather than missed. Reading a stored set is one operation
whether you take one member or all of them, and a transitive closure has no partial
answer — computing one link computes the fixpoint. Those are noted at the site.
