# Abduction: what would have to be true

- **Covers:** `abduce` — mint the minimal set of hypotheses a goal needs to become provable, each
  admitted by the abducibility check, isolated in a scratch context.
- **Not here:** the DFS backward chainer (`prove`) whose dead-end hook abduction listens on →
  [inference.md](inference.md); open, non-ground hypotheses → [skolem.md](skolem.md).
- **Assumes:** context, premise, strength, justification → [glossary.md](glossary.md).

Backward chaining answers *is this provable?*  Abduction answers the complementary
question — *what would have to be true for it to be provable?* — and mints the answer as
a **hypothesis**.

```clojure
(v/assert kb '(abducible_predicate was_washed) 'CxLaundry)
(v/assert kb '(set/forwardRule (implies (and (was_washed ?x)) (clean ?x))) 'CxLaundry)

(v/abduce kb '(clean Shirt) 'CxLaundry)
;; {:solutions   [{} {}]
;;  :hypotheses  [{:sentence (was_washed Shirt) :context CxAbduction3a9d… :handle nil}]
;;  :refused     []
;;  :context     CxAbduction3a9d…
;;  :status      :complete}
```

The goal is answerable **given** `(was_washed Shirt)`, which nobody said, so the solutions
and the hypotheses always come back together.  The solutions are `prove`'s, unprojected: a
ground goal binds none of the rule's variables, so both maps are empty.  There are two
because a hypothesis is minted through the whole `assert` pipeline, chaining included, so
by the time the proof is re-run `(clean Shirt)` is also a stored fact in the scratch
context: one solution is that fact, one is the rule expanded over the hypothesis.

`vaelii.core/abduce` and `abduce-discard!` state the call's contract: the result keys, the
options and the refusals.

## Where it lives

- `vaelii.impl.abduce` — the scratch-context lifecycle, the abducibility check (`abducible?`) and the
  mint/re-prove loop (`run`).
- `vaelii.impl.resolution` — `*dead-end*`, the observer `prove` reports dead ends to.
- `vaelii.impl.special` — the `abducible_predicate` entry, a scoped taxonomy prop.

## Why this is small here

Abduction needs containment (a hypothesis must not corrupt what you already believe),
arbitration (a hypothesis must lose to real knowledge) and cleanup.  The engine provides
all three through mechanisms built for other reasons:

| | |
|---|---|
| **containment** | the context lattice.  A hypothesis goes into a fresh context hung *below* the asking context, so it sees everything the question could see and nothing that existed before can see it |
| **arbitration** | strengths.  A hypothesis is a `:default` premise, so a `:monotonic` fact that contradicts it defeats it through the ordinary path |
| **cleanup** | retraction.  A hypothesis is an ordinary premise, so `retract!` and the dependency-directed sweep take it and everything it supported |

The scratch context therefore needs no machinery of its own.  A rule firing over a
hypothesis places its conclusion **in** the abduction context, because placement is the
maximal common descendant ([contexts.md](contexts.md)) and the scratch context is the only
one below both the rule and the hypothesis.  The consequences land in the context that
gets discarded.  The sandbox (`vaelii.browser.sandbox`) uses the same placement for the
same reason.

The code specific to abduction is the **search**: finding the dead end, and deciding what
may be assumed.

## The dead end

A **dead end** is a subgoal `res/prove` could neither match nor expand.  `res/*dead-end*`
receives each one; its docstring states the contract.

The observer is a sink, not a filter: its return value is ignored, so an observed run
takes the same path as an unobserved one, and abduction searches exactly as `prove` does.

A branch cut short by the per-path loop guard, by `:max-depth` or by the term-growth
ceiling is not reported.  A truncated branch is a search that ran out of **budget**; a
dead end is a search that ran out of **knowledge**, and only the second names something
the KB could be told.  Reporting truncated branches would let a depth cap produce
hypotheses.

Only the DFS reports.  `query` is lazy: its dead ends would be found whenever a consumer
realized the seq, after the thread binding is gone.  `prove` is a loop, so the binding is
in place for the whole search.

## The abducibility check

Without the abducibility check every dead end would be assumed and every goal would be
answerable.
`abduce/abducible?` checks four conditions, cheapest first:

1. **A ground positive literal.**  An open hypothesis is a skolemization question
   ([skolem.md](skolem.md)), so `(was_washed ?x)` is refused rather than given an invented
   name.  A negation has functor `not`, which nothing grants, so negative hypotheses are
   excluded with no rule of their own.
2. **Declared abducible.**  `(abducible_predicate P)` makes a `(P …)` assumable, and
   nothing else does.  It is a predicate property like `transitive` / `symmetric` —
   cached in the taxonomy, belief-following, retractable — except that it is **not**
   decontextualized.  Those properties hold wherever the predicate is mentioned; this one
   is a **policy** of the context that grants it, read from the asking context's `genlCx`
   ancestor set, so one theory may assume a predicate that another, reading the same
   vocabulary, will not.  The shipped schema grants one: `CxBiology` declares
   `(abducible_predicate asleep)`, so *why is this animal not awake* is answerable and
   *why does it not fly* comes back with `(bird …)` in `:refused`.
3. **Legally assertible.**  The same four checks every minted sentence passes
   (`special/inadmissible`): naming, the definitional constraints, well-formedness and
   edge stratification.  A sentence `assert` would refuse is not assumed, so abduction is
   not a way around the checks.
4. **Not already contradicted**: no `(not S)` believed where it would land.  A
   clash found *later* is arbitrated, because the hypothesis is `:default`; a clash visible
   at mint time refuses the hypothesis.  The read is `matches-visible`, so a negation
   stated in a context the asker cannot see does not block, as it would not block an
   assertion.  The belief filter changes nothing here: defeating `(not S)` means believing
   `S`, and a believed `S` is not a dead end.

`abducible?` reads nothing but its arguments, so what may be assumed is decidable without
running a search.

## The loop

Prove, gather the dead ends, mint what the abducibility check allows within `:max-depth`, prove
again.

A hypothesis satisfies the antecedent that dead-ended, so the next round reaches one rule
further and exposes the next missing subgoal.  A conjunction is solved left to right: with
`(implies (and (p ?x) (q ?x)) (goal ?x))` and nothing stored, the first round never reaches
`q`, since `p` produced no frames.  Assuming `p` exposes `q`.

Each round mints at least one hypothesis or stops, and the minted set is capped, so there
are at most `:max-hypotheses` rounds.  A nil `:max-hypotheses` is no bound, as for every
optional bound ([api.md](api.md)): the rounds then end when no dead end yields a candidate
not already minted.

Candidates are taken in **content order**, because the cap decides which survive, and a
cap resolved in DFS arrival order would make the answer depend on traversal — the reason
belief never tie-breaks on a handle ([nmtms.md](nmtms.md)).

## Minimal, in the irredundant sense

Once the goal follows, each hypothesis is dropped in turn, in content order, and the proof
re-run; it goes back only if the goal stopped following.  The result is **irredundant** —
no single member can be removed — and not *minimum*.  A smaller set reachable only by
swapping two members out for a third is an ATMS question, not asked here.

With two rules concluding one goal, each with its own abducible antecedent, both
antecedents dead-end in the first round and both are assumed; the first in content order
is then dropped.  The solutions are read after minimizing, so they are the ones the
returned hypotheses license.

## The caps

`:max-hypotheses` (default 8) bounds how much may be assumed; `:max-depth` (8) bounds the
rule depth past which a dead end is left alone.  A hypothesis minted twelve rules deep
explains the goal only in the sense that anything explains anything.

Neither narrows silently.  A check that did would read as *there was nothing to find* when
a predicate was never granted:

* `:status :capped` says the hypothesis cap left candidates unminted, in any round, even
  when a later round proved the goal;
* `:refused` lists the dead ends the abducibility check would not assume, and is reported only when
  nothing was proved, which is when a caller asks *why nothing*.

## Isolation

**An `abduce` call whose result you ignore leaves the KB as it found it.**  The scratch
context is torn down before returning, and on the way out of an exception.

`{:keep? true}` leaves the context standing and the caller owns it: the handles are real,
the hypotheses are inspectable, `why` works on what they licensed, and `abduce-discard!`
ends it.  Without `:keep?` the reported `:handle` is **nil**, because after the teardown
there is no such sentex (`preview` reports its handles the same way).

**A KB holds at most 64 kept contexts** (`vaelii.impl.abduce/max-kept`).  A `:keep?` call
past that is refused with `:too-many-kept` before it searches, and the refusal lists the
standing contexts under `:contexts`.  Nothing is evicted: the caller holds each context,
so a context discarded unasked would make that caller's later read or `abduce-discard!`
fail without a reason.  A call without `:keep?` is not counted and still runs at the cap.

**Committing is the caller's.**  To keep a hypothesis, assert it in a context that
outlives the scratch.  There is no promotion path, for the sandbox's reason: a scratch
context with no exit path cannot be half-committed.

## What a hypothesis is, in the record

An ordinary premise:

| | |
|---|---|
| strength | `:default`.  A `:monotonic` fact that contradicts it defeats it, and what it licensed goes OUT with it — through the ordinary path, with no abduction-specific rule anywhere.  Retract the fact and the assumption revives |
| context | the scratch context, so nothing that existed before the call can see it |
| provenance | `{:abduced true :abduced-for <goal>}`, asserted with `:creator :vaelii.impl.abduce/hypothesis`, so a reader of the record can tell an assumption from something a person asserted, and what it was assumed *for* |
| justification | none.  It is assumed, not derived; `premise?` is true and `why` reports it as one |

The `genlCx` edge that makes the scratch context is `:monotonic`: which context sees which
is a fact about the scratch space, and a defeasible edge would let a contradiction among
the hypotheses unhook the context holding them.

## Scope

**In:** `core/abduce` / `core/abduce-discard!`, the context lifecycle, the dead-end
observer, the abducibility check, `abducible_predicate`, provenance, the caps, the irredundancy check.

**Out:**

* **Best-explanation ranking.**  Returning the candidate set is in; scoring it by
  likelihood needs a cost model this KB has no source for.
* **Full ATMS minimality** over environments.
* **Open (non-ground) hypotheses** — skolemization's territory ([skolem.md](skolem.md)).
* **Committing to base belief automatically.**  The caller decides.

**Isolation is exact.**  Two mechanisms could in principle move a base handle, and neither
does:

* **Defeat** does not sweep.  A hypothesis, or a conclusion drawn from one, that
  contradicts a base default is arbitrated by label; the base record keeps its support and
  its handle, and the teardown removes the side that contradicted it.
* **Blocking** does sweep: an `exceptWhen` that holds makes a justification invalid, and
  the dependency-directed sweep *deletes* the conclusion, so a revival is a re-derivation
  at a new handle.  A hypothesis cannot reach one.  A rule's exception is evaluated in
  **the conclusion's placement context**, and a base conclusion is placed at or above the
  asking context, which is strictly above the scratch one and cannot see into it.  A firing
  whose placement *is* the scratch context concludes there and is discarded with it.

The tests hold the strong claim: the same records, the same justifications, the same
beliefs, at the same handles.
