# Resource-bounded / anytime inference

- **Covers:** the budget a query runs under
  (`:max-ms`/`:max-results`/`:max-cost`/`:max-depth`/`:max-term-growth`),
  the partial-result contract `ask-within`/`prove-within` return, and what `resume` continues.
- **Not here:** the chainers and prover registry a budget bounds → [inference.md](inference.md);
  the lookup-to-query stack whose laziness the budget spends → [levels.md](levels.md).
- **Assumes:** sentex, prover, backward chaining → [glossary.md](glossary.md).

`vaelii.impl.budget`, surfaced as `core/ask-within`, `core/prove-within`, and
`core/resume`.

A large KB has queries that do not terminate usefully: the transitive closure is
huge, a backward search fans out, an existence check would scan an extent. The
engine's answer is not a faster search — it is a **bounded** one that returns what
it found, says whether it ran dry or was cut short, and can be continued. That is
the *anytime* contract: an answer available at any moment, improving with more
time.

## The one idea: bound a lazy stream, keep the tail

Every query path in this engine is **lazy** — `ask`, `query`, the level stack
all yield one solution at a time, paying per result consumed (see
[levels.md](levels.md), [inference.md](inference.md)). So resource-bounding is not
new machinery threaded through every prover; it is the **consumer-side** discipline
of realizing a lazy answer stream under a bound. And resumption falls out for free:
the *unrealized tail is the continuation*. Hold it, and continuing is realizing
more of it.

`prove` is the one eager engine (a DFS returning a vector). It is made bounded and
resumable the same way, with the same contract — there the **goal stack is the
continuation** rather than a lazy tail.

**The node engine's state is a value.** Routed to by `core/*query-engine*`
([inference.md](inference.md)), it stops between two node expansions and what it leaves
behind is an **agenda** — a frontier, a node registry, a claimed-key set — rather than a
continuation closure. `inference/search-within` drives it under a budget and checks the
bounds **before every node expansion**, not between yielded results: one pull of its
lazy result stream (`search-seq`) steps until a node yields, so a wide unproductive
frontier — a converging rule graph under a generous depth — would otherwise run whole
before a deadline held between results was seen. The session is the continuation, and
`:resume` drives the same session further; solutions an expansion completed past a
`:max-results` cap head the next step rather than being dropped, so a cap of *n* returns
exactly *n*.

Which node it stops *on* is the one thing a bound makes visible. An exhaustive run
expands the same nodes under every ordering, so the node engine's tacticians
([inference.md](inference.md)) can only pay here — time to the first *k* answers, or
answers before a deadline. Two of its modes are outside this contract and say so:
`:first-result?` reduces the answer set rather than reordering it, and a **portfolio** is
driven to completion before its racers can be unioned, so it has no partial answer to
hand back. `prove-within` drives the ordinary stream.

**A cap keeps *some* *k* answers, and arrival order decides which.** Under a
`:max-results` smaller than the answer set, four things are the same in every arrival
order: each capped answer is an answer of the uncapped read, the step's `:status`, its
`:count`, and the answers the `resume` steps hand back, which hold every answer exactly
once. The membership of the capped prefix is not among them. A stored literal's matches
stream in the order the index holds their handles, and handles are allocated in
assertion order, so three facts `(awp AwA)`, `(awp AwB)`, `(awp AwC)` asserted in six
orders give different first answers under `{:max-results 1}` on `ask-within` and on both
of `prove-within`'s executors. Sorting a literal's matches by content before the cap would
realize the literal's whole extent, which is the cost `:max-results` bounds. The same
argument holds one level up: putting the answers of a join or a rule chain in content
order means running the search to completion. Two short lists are content-ordered,
because each holds a handful of entries: the rules that conclude a goal
(`provers/candidate-rules`, by `[sentence context]`) and the node frontier's cost ties
(`inference/frontier-key`). So a capped proof whose rules each have one witness answers
the same in any order, and a capped read that chooses among stored facts does not.
`order_independence_test` asserts both halves. A `:max-ms` deadline cuts at a moment rather
than at a count, so its prefix depends on the machine as well as on arrival order.

`take` over the lazy stream `ask` and `query` return has the same contract. Those streams
read a literal's matches from the same index, so `(take k …)` holds *k* answers of the
uncapped read, and arrival order decides which *k*. `find-terms :limit` sorts by name
before it keeps the first *n*, so its prefix is chosen by content.

**A bounded run does not poison the literal cache.** `matches-visible` answers are
cached ([inference.md](inference.md)), and a cached stream accumulates as its consumer
pulls but stores only at the moment the *source* runs dry — never when the consumer
stops. So a run cut short by `:max-results`, a deadline, or a bare `take` stores
nothing, and a later unbounded ask for the same literal cannot be served that run's
prefix as though it were the whole extent. Realize-and-store is a decision the source
makes by ending, not one the consumer makes by leaving.

## The budget

A budget is a map of optional bounds; any subset, and `nil` / `{}` means unbounded.

| key | meaning | honored by |
|-----|---------|-----------|
| `:max-ms` | wall-clock milliseconds — a soft deadline | `ask-within`, `prove-within` |
| `:max-results` | stop after this many solutions | both |
| `:max-cost` | a qualitative prover-cost ceiling (a tier keyword) | `ask-within` |
| `:max-depth` | transformation (rule-expansion) depth | `prove-within` |
| `:max-term-growth` | how far a rule may grow a subgoal's nesting | `prove-within` |

`:max-ms` is checked **between** yielded solutions — the granularity is one
solution, so a single blocking pull (a closure fixpoint, one deep proof) is not
interrupted mid-flight. This matches the engine's existing candor that "a closure
has no partial answer"; it is a real limit, stated rather than hidden. `:max-cost`
is the complement that keeps *per-solution* latency bounded — see below.

One pull is interrupted: the argument-preservation prover's claim walk, which reads a
predicate's extent or the product of the goal's reaches to answer one closed goal
([inherit.md](inherit.md#what-one-question-costs)). Under `ask`, `ask?` and `ask-within`
the walk checks the deadline per row it reads, so the step stops at the deadline and
answers `:timeout` (`:budget-exhausted` at `ask` / `ask?`) at every extent
(`inherit_test/an-ask-deadline-stops-the-claim-walk-at-the-row-it-passes-on`). An
interrupted lazy stream cannot be pulled again, so the `ask-within` continuation rebuilds
the stream, drops the answers already returned, and runs its first pull without the
deadline: a resume gets past the interrupted walk, and a resume loop under a fixed budget
terminates.

`prove`, `provable?` and `prove-within` with a `:max-ms` carry the same deadline into the
walk when it answers a leaf of the backward search, on both engines: the DFS stops at the
deadline and answers `:timeout` (`:budget-exhausted` at `prove` / `provable?`)
(`inherit_test/a-prove-deadline-stops-the-claim-walk-at-the-row-it-passes-on`). The
stopped leaf, or the node engine's stopped node, stays where it was, a goal-stack frame
or a frontier entry, and the continuation runs that one leaf without the deadline, so a
resume loop under a fixed budget terminates here too. The other readers of the same walk
— the asymmetry check at `assert`, settle, forward chaining — run under no deadline.

## The partial-result contract

`collect` (and `prove-within`) return one shape:

```clojure
{:results    [ … ]        ; the solutions realized in THIS step (a vector)
 :status     :complete    ; the source ran dry — the answer is exhaustive
             ;; | :incomplete the source ran dry, :unenumerated is non-empty
             ;; | :timeout    :max-ms elapsed, the source not yet dry
             ;; | :capped     :max-results reached, the source not yet dry
 :count      n            ; (count :results)
 :elapsed-ms ms           ; wall-clock spent in this step
 :resume     <fn | nil>   ; nil iff :complete or :incomplete; else (budget -> partial result)
 :unenumerated [P …]      ; ask-within / prove-within: transitive predicates whose closure
                          ; a both-open goal did not enumerate, cumulative over the steps
 :unenumerated-in-guards [P …]}  ; the subset recorded inside unknown / exceptWhen
```

`:complete` is the required one and it is exact: it is reported only when the
source was pulled and ended, and no goal `(P ?x ?y)` over a `transitive` `P` was
answered from `P`'s extent. Such a goal is answered from the stored pairs and not the
closure ([taxonomy.md](taxonomy.md#predicate-metadata)), so a run whose source ended
after one reads `:incomplete`: the answers may lack a derived pair, and `:unenumerated`
names each `P`. A predicate recorded in one step bounds the union of every step's
`:results`, so a step's `:unenumerated` holds every predicate the steps before it
recorded. `:timeout` and `:capped` keep their meaning and carry the set too. The other two are the negation of `:complete` rather than
a claim that work remains — `collect` stops *before* pulling past its bound, since
deciding whether a tail exists means realizing one more element than the cap allows.
So `{:max-results 3}` over a source of exactly three answers reports `:capped` with a
continuation, and driving that continuation yields `:complete` with no results. That
is one extra step, never a wrong answer, and it is the price of a cap that reads
exactly *n*.

**The plain entry points take a bound too, and answer differently.** `ask`, `ask?`, `prove` and
`provable?` each take a trailing option map — `{:max-ms n}` at the first two,
`{:max-ms n :max-depth n}` at the last two ([api.md](api.md)) — and what a reached
`:max-ms` gets there is a refusal, `:type :budget-exhausted`, rather than the prefix. A
solution vector and a boolean have no `:status` slot, so a prefix returned in either shape
is a wrong answer wearing a right one's face; the contract below is what a caller asks
through when the prefix is what they want
[why refuse there](defenses.md#a-deadline-on-ask--prove-refuses-a-depth-does-not).
`:max-depth` at `prove` / `provable?` prunes rather than suspends, so it never refuses —
the run is `:complete` for the depth it was given.

`:results` are **per step, not cumulative** — concatenate across steps for the
whole answer. `:resume` is a one-argument function taking a fresh budget, so each
continuation is independently budgeted; `core/resume` calls it (and returns a
`:complete` result unchanged, so a drive loop terminates cleanly):

```clojure
(loop [r (v/ask-within kb goal ctx {:max-results 20})]
  (handle (:results r))
  (when (:resume r) (recur (v/resume r {:max-results 20}))))
```

A bounded run is a **strict prefix** of the unbounded stream, so concatenating
`:results` across `resume` reconstructs exactly what `ask` / `prove` would have
returned (`budget_test` asserts this, dedup included).

The continuation captures an in-memory lazy tail (or the DFS goal stack), so
resumption is **in-process only** — it does not survive a restart, and holding a
partial keeps its captured state reachable in the heap. This sits under the single-writer
contract (see [storage.md](storage.md)); a cross-restart resume would need the
search state serialized, which it is not.

## Where the collector lives

`TransitivePredicateProver` adds `P` to the dynamic `provers/*unenumerated*` when it
declines a both-open goal, and a read reports the set only where a binding of the
collector covers the call that runs the prover. Each read binds it around the stretch of
its search that runs eagerly:

| read | binding |
|---|---|
| the node engine (`search-report`, `search-tree`, `compare-tacticians`, `prove-within` at a depth, its `resume`) | the session's `:unenumerated` collector, bound around each expansion's solve in `step!`; the session is the continuation, so a resume adds to the same set |
| the DFS arm of `prove-within` and its `resume` | one collector the continuation closure carries, bound around each `res/prove-from` step |
| `ask-within` and its `resume` | one collector bound around each pull of the lazy stream (`provers/collecting-seq`), including the stream a `:timeout` continuation rebuilds |
| `query-status` without a depth, `explain-levels`, `escalate` | `provers/with-unenumerated` around a realized read: per level for `explain-levels`, the stopping level's probe for `escalate` |
| `do/label` | `provers/with-unenumerated` around the grounding (`solve-context/build`), which is eager ([solving.md](solving.md#dolabel-base-into-mode)) |

`compare-tacticians` reads a row `:incomplete` under the same rule. Every tactician runs
the same goals, so the rows' `:unenumerated` sets are equal, as their answer sets are.
`escalate` returns the stopping level's results lazily, and its set covers the probe that
pulled the first result; a later pull of `:results` records nothing. `query`, `prove` and
`ask` return a vector or a seq with no status slot and report nothing. The `unknown` and
`exceptWhen` evaluations record into `:unenumerated-in-guards` as well
([inference.md](inference.md#truncation-is-observable-corequery-status)).

## `:max-cost` — the qualitative bound

The prover cost model is **qualitative**, not a per-prover time estimate
[why qualitative](defenses.md#qualitative-cost-tiers-over-time-estimates) — a `cost`
tier answering one question, *is the answer something you look up, compute, or search
for?* (`vaelii.impl.provers/cost-tiers`):

```
:lookup  <  :compute  <  :search
```

- `:lookup` — a bounded single-step retrieval: an O(1) ground test (reflexive,
  `evaluate`, `different`, the evaluable and quantity comparisons, the arity-position
  query `admitsArgnum`), a cached closure /
  metadata read (genl/genlCx transitivity, disjointness, arg-type), or one index hit
  (facts, symmetric, inverse). All three are one bounded
  step, lazy to the first result, and no decision turns on which of the three it is, so
  they fold into one tier. Nineteen of the shipped provers sit here.
- `:compute` — work over stored facts before the first answer, and thirteen provers claim
  it: a declared-`transitive` predicate walking its closure, `transitiveInArg`, `unknown`,
  `thereExists`, `forall`, a declared-complete extent's negation, the two
  definitional-membership provers (`defnSufficient` and the `defnNecessary` negation), the
  aggregates, a modal belief projection, and the argument-type meta-predicates read up
  `genl`. `thereExists`
  and the aggregates are the ones `{:max-cost :lookup}` is really about, since a `count`
  is a census of a whole extent.
- `:search` — recursive backward chaining, open-ended proof search. **Unoccupied**, and
  by construction: no member of the registry expands a rule, so nothing `ask` dispatches
  opens a proof search — an application prover added through `add-prover` can claim it
  [why the tier stays](defenses.md#qualitative-cost-tiers-over-time-estimates). Rule
  expansion itself is priced by the engine that does it, as `:max-depth` below, which is
  a bound rather than a tier.

The union path already orders applicable provers by this tier (cheapest first, so a
consumer taking one answer never pays for a closure when a lookup answers).
`:max-cost` turns the tier into a **ceiling**: `ask-within` drops every prover above it
*before* the stream is built. So `{:max-cost :lookup}` runs bounded retrieval only — no
closure fixpoint, no `thereExists`, no aggregate — and, `:search` being empty, `:compute`
and `:search` both keep the whole registry. A goal answerable only by a dropped tier
simply yields nothing (an empty result, not a hang). Combined with `:max-ms` it is a
genuine anytime strategy: *cheap tiers only, and stop at N milliseconds*.

**`unknown` is the one prover no ceiling drops**, and the asymmetry is what the meaning of
an empty result rests on. Dropping a `:compute` prover makes a run *under-report*, which
is the trade a ceiling is asking for; dropping the closed-world one **inverts** it — an
empty result for `(unknown S)` reads as *S is derivable*, and the run reports `:complete`
while saying it. So `cost-capped-provers` retains `UnknownProver` at every ceiling. It is
applicable only to `unknown` goals, so keeping it narrows nothing else, and a wrong answer
outranks a best-effort cost bound. `thereExists` and the aggregates under-report rather
than invert, so they stay droppable.

A value that is not one of the three tiers is **refused** (`:type :unknown-option`), not
read as no ceiling
[why refuse](defenses.md#refusing-an-unrecognized-cost-ceiling).

`:max-cost` bounds `ask`'s prover tiers rather than a search, so `prove-within` ignores
it and uses `:max-depth` to bound the search instead.

## `:max-depth` — bounding transformation, not the stack

`prove-within`'s `:max-depth` bounds **rule-expansion** depth: each DFS frame
carries the number of rule expansions taken to reach it, a fact match keeps that
depth, a rule expansion increments it. `{:max-depth 0}` permits no rule expansion
at all (facts only); `{:max-depth 1}` allows a single-hop rule like grandparentOf
but no recursion. Unlike `:max-ms` / `:max-results` it is a **pruning** bound, not
a suspending one: the depth-bounded search still runs to `:complete` (its space is
genuinely exhausted under the bound), so you widen it by re-running with a larger
depth rather than by `resume`. It is the analogue of Cyc's
`:max-transformation-depth`, distinct from forward chaining's `:max-depth`
(recursion-detection cap) though named alike.

## `:max-term-growth` — the other termination guard

The DFS's second guard is a ceiling on how far a **rule** may grow a subgoal's
compound nesting past what its own derivation path has already met
(`res/default-max-term-growth`, 8 — the mechanism is
[inference.md](inference.md), "Backward chaining"). It is a pruning bound like
`:max-depth`, and it is on whether the caller names one or not: a rule that wraps a
function around a head variable asks a fresh goal per expansion, so without a ceiling
the search does not return at all. What the budget key buys is **raising** it, for a KB
whose derivations legitimately build terms deeper than the allowance —
`{:max-term-growth 40}`. The node-engine arm ignores it, terminating on `:max-depth`
instead.

## What it is not

- **No mid-solution interruption** outside the argument-preservation claim walk. The
  deadline is checked between yielded solutions (between DFS steps and node expansions
  under `prove-within`); any other single expensive `solve` (a
  large closure) runs to its own completion. `:max-cost` is the lever for that case —
  exclude the expensive tier rather than interrupt it.
- **No estimate-based admission control.** The budget spends *real* time, never a
  per-prover estimate
  [why qualitative](defenses.md#qualitative-cost-tiers-over-time-estimates);
  `:max-cost` is the tier-based version, and there is no finer check reading a
  prover's `est-bindings` against the remaining budget.
- **No cross-process / cross-restart resume.** The continuation is heap state.
- **No resume over the wire.** The daemon serves `:ask-within` and `:prove-within`
  ([operations.md](operations.md)) and answers `:results`, `:status`, `:count` and
  `:elapsed-ms` as ever — but `:resume` is a function over that heap state, so it is
  replaced by **`:resumable`**, a boolean saying the search had more to give. `core/resume`
  is in-process only. A remote caller continues by asking again under a larger budget: a
  bounded run is a strict prefix of the unbounded one, so the larger call is a superset of
  the smaller rather than a second, unrelated answer.

## Where it plugs in

The budget layer adds no engine of its own. `ask-within` runs `ask` over a possibly
cost-filtered registry and `collect`s the lazy result; `prove-within` runs the same DFS
through `res/prove-from`, which is the resumable core `prove` itself delegates to, and
wraps its batch in the same contract — or, routed to the node engine, drives a session
through `inference/search-within`, which builds the same contract per expansion. Both
normalize their goal through
`prepare-goal-for-read`, the same step `ask` / `prove` / `sentexes-matching` take — a
reifiable NAT reified to the constant it denotes, a merge-retired term rewritten to
its representative. That is what "same answers as `ask`" rests on, and a read path
that skipped it would not answer *wrongly*, it would answer **emptily**, which reads
exactly like a KB that was never told.

The budget is a thin, testable layer over machinery that is lazy underneath it — which
is why it is small.

A budget bounds the *search*: how long it runs, how many results it collects,
how deep it goes. It does not allocate effort **between** proof branches — no estimate
decides which branch deserves the remaining time — so a budget spent on an unproductive
branch is spent.
