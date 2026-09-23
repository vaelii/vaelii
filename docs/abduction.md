# Abduction: what would have to be true

- **Covers:** `abduce` — mint the minimal, gated set of hypotheses a goal needs to become
  provable, isolated in a scratch context.
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

The goal is answerable — **given** `(was_washed Shirt)`, which nobody said.  The two travel
together, and there is no arity that returns the solutions alone.

`:solutions` are `prove`'s, unprojected, so they carry the rule's canonical variables —
a ground goal like this one binds none of them, which is why both maps read empty. There
are two of them here for one reason worth spelling out: a hypothesis is minted
through the **whole** `assert` pipeline, chaining and settle included, so by the time the
proof is re-run the rule has already fired and `(clean Shirt)` is a stored fact in the
scratch context.  One solution is that fact, one is the rule expanded over the
hypothesis.

## Why this is small here

The hard parts of abduction are containment (a hypothesis must not corrupt what you
already believe), arbitration (a hypothesis must lose to real knowledge) and cleanup.
The engine already had all three, built for other reasons:

| | |
|---|---|
| **containment** | the context lattice.  A hypothesis goes into a fresh context hung *below* the asking context, so it sees everything the question could see and nothing that existed before can see it |
| **arbitration** | strengths.  A hypothesis is a `:default` premise, so a `:monotonic` fact that contradicts it defeats it through the ordinary path |
| **cleanup** | retraction.  A hypothesis is an ordinary premise, so `retract!` and the dependency-directed sweep take it and everything it supported |

That last one is why the scratch context needs no machinery of its own.  A shipped rule
firing over a hypothesis places its conclusion **in** the abduction context, because
placement is the maximal common descendant (docs/contexts.md) and the scratch context is
the only one below both the rule and the hypothesis.  So the consequences land inside the
thing that gets discarded, with nothing arranging for it — the same asymmetry the sandbox
(`vaelii.browser.sandbox`) is built out of, for the same reason.

So the new code is the **search**: finding the dead end, and deciding what may be
assumed.

## The dead end

`res/prove` is the DFS backward chainer.  A **dead end** is a subgoal it could neither
match nor expand: no visible believed fact unified with it, and no rule concluding it
unified either.  `res/*dead-end*` is an optional observer of exactly those —
`(fn [goal depth])`, nil by default, one var deref per expanded goal when unbound.

It is a **sink, not a filter**.  An observed run and an unobserved one take byte-identical
paths, so abduction gets the very search `prove` runs rather than a variant of it, and
nothing about `prove` changes to make abduction possible.

Three branches deliberately do *not* report:

* the per-path loop guard cut the expansion (the goal is re-entering its own derivation
  path),
* `:max-depth` bit, and
* the term-growth ceiling (`res/default-max-term-growth`) refused the expansion, the
  subgoal's arguments having nested deeper than its own path had already met.

A truncated branch is a search that ran out of **budget**; a dead end is a search that ran
out of **knowledge**, and only the second names something the KB could be told.  Without
that distinction a depth cap would manufacture hypotheses.

Only the DFS reports.  `query` is lazy: its dead ends would be discovered whenever a
consumer happened to realize the seq, by which time the thread binding would be gone.  So
abduction rides `prove`, which is a loop.

### What the hook costs `prove`

A workload built to saturate it — 60 rules concluding one goal, every one of them
bottoming out, so 12,000 dead ends are reported per run:

| | median |
|---|---|
| unbound (nobody listening) | 120.4–120.6 ms |
| observed (deref, call, `vswap!`, `conj` per dead end) | 122.8–125.6 ms |

So the *whole* observing path is 3–4% of a run made of nothing but dead ends, and the
unbound path — a nil deref, first in the `and`, in a branch that has already done two
index reads — is a fraction of that and does not resolve.  On anything with a normal
ratio of matches to dead ends it is not there at all.

## The gate

**An ungated abducer hypothesizes anything and is worth nothing.**  Four conditions, in
`abduce/abducible?`, cheapest first:

1. **A ground positive literal.**  An open hypothesis is a skolemization question
   (docs/skolem.md) and not this one, so `(was_washed ?x)` refuses rather than inventing a
   name.  A negation has functor `not`, which nothing grants, so negative hypotheses are
   excluded with no rule of their own.
2. **Declared abducible.**  `(abducible_predicate P)` is what makes a `(P …)` assumable and
   the *only* thing that does.  It is a predicate property like `transitive` / `symmetric`
   — cached in the taxonomy, belief-following, retractable — with one deliberate
   difference: it is **not** decontextualized.  Those are claims about a predicate that
   hold wherever it is mentioned; this is a **policy** of the context that grants it,
   so it is read from the asking context's `genlCx` ancestor set and one theory may be
   willing to assume a predicate that another, reading the same vocabulary, will not.
   The shipped schema grants exactly one: `CxBiology` declares `(abducible_predicate
   asleep)`, so *why is this animal not awake* is answerable and *why does it not fly*
   comes back with `(bird …)` named as the dead end it refused to assume.
3. **Legally assertible.**  The same four checks every minted sentence passes
   (`special/inadmissible`) — naming, the definitional constraints, well-formedness, edge
   stratification.  A sentence `assert` would refuse must not be one the search assumes,
   or abduction is a way around the checks.
4. **Not already contradicted** where it would land — a visible, believed `(not S)`.  A
   clash discovered *later* resolves itself, because the hypothesis is `:default`; a clash
   visible at mint time is not an arbitration to run, it is a hypothesis with no business
   existing.  The read is `matches-visible`, so **visibility** is what narrows: a negation
   stated in a context the asker cannot see does not block, exactly as it would not block
   an assertion.  Its belief filter is vacuous here rather than useful, and pleasingly so
   — defeating `(not S)` means believing `S`, and a believed `S` is not a dead end for the
   search to have reached.

`abducible?` is a pure predicate over a sentence and `maybe-abduce` adds the depth bound.
Both are deliberately separate from the search, so what may be assumed is decidable
without running one.

## The loop

Prove, gather the dead ends, mint what the gate allows, prove again.

Minting is what makes progress possible: a hypothesis satisfies the antecedent that
dead-ended, and the search reaches one rule further, exposing the next thing it lacks.
That matters more than it sounds, because **a conjunction is solved left to right** — with
`(implies (and (p ?x) (q ?x)) (goal ?x))` and nothing stored, the first round never
reaches `q` at all, since `p` produced no frames to carry it.  Assuming `p` is what
exposes `q`.

Termination is structural: each round mints at least one hypothesis or stops, and the
minted set is capped, so there are at most `:max-hypotheses` rounds.

Candidates are taken in **content order**, because the cap decides which of them survive
and a cap resolved by whatever order the DFS happened to reach them would make the answer
depend on traversal — the same reason belief never tie-breaks on a handle
(docs/nmtms.md).

## Minimal, in the cheap sense

Once the goal follows, each hypothesis is dropped in turn and the proof re-run; it goes
back only if the goal stopped following.  What that yields is an **irredundant** set — no
single member can be removed — and not a *minimum* one.  A smaller set reachable only by
swapping two members out for a third is an ATMS question and deliberately not asked here.

Two rules concluding one goal, each with its own abducible antecedent, is the shape:
both dead-end in the first round so both are assumed, and the one the answer does not need
is then dropped.  Which of two mutually-redundant hypotheses survives is decided by
content order, not by which was minted first.

The set is minimized before the solutions are read back, so what the caller gets are the
solutions the hypotheses they are handed actually license — not the ones a larger set did.

## The caps, said out loud

`:max-hypotheses` (default 8) bounds how much may be assumed; `:max-depth` (8) bounds the
rule depth past which a dead end is left alone.  A hypothesis minted twelve rules deep
explains the goal in the sense that anything explains anything.

Neither narrows silently, because a gate that does reads as *there was nothing to find*
when the truth may be that a predicate was never granted:

* `:status :capped` says the hypothesis cap ran out with candidates remaining;
* `:refused` lists the dead ends the gate would not assume — reported when nothing was
  proved, which is when a caller asks *why nothing*.

## Isolation, which is the contract

**An `abduce` call whose result you ignore leaves the KB as it found it.**  The scratch
context is torn down before returning — the extent in one `edit!`, so it is one settle and
the sweep takes the derived content with the premises it rested on, then the `genlCx`
edge, which was never *in* the extent (`genlCx` is forced-decontextualized, so it
lives in CxUniverse).  The teardown also runs on the way out of an exception, which
is when isolation is easiest to lose.

`{:keep? true}` leaves the context standing and the caller owns it: the handles are real,
the hypotheses are inspectable, `why` works on what they licensed, and
`abduce-discard!` ends it.  Without `:keep?` the reported `:handle` is **nil** — after the
teardown there is no such sentex, and a dangling integer would be worse than an honest nil
(`preview` says the same thing the same way).

**Committing is deliberately the caller's.**  Abduction proposes: to keep a hypothesis,
assert it in a context that outlives the scratch.  There is no promotion path, for the
same reason the sandbox has none — a dead end that cannot be half-escaped is easier to
reason about than one with an entry point in it.

## What a hypothesis is, in the record

An ordinary premise, and every part of that is required:

| | |
|---|---|
| strength | `:default`.  A `:monotonic` fact that contradicts it defeats it, and what it licensed goes OUT with it — through the ordinary path, with no abduction-specific rule anywhere.  Retract the fact and the assumption revives |
| context | the scratch context, so nothing that existed before the call can see it |
| provenance | `{:abduced true :abduced-for <goal>}`, asserted with `:creator :vaelii.impl.abduce/hypothesis` beside it — a reader of the record can tell an assumption from something a person asserted, and can see what it was assumed *for* |
| justification | none.  It is assumed, not derived; `premise?` is true and `why` reports it as one |

The `genlCx` edge that makes the scratch context is `:monotonic`, and that is not an
inconsistency: which context sees which is a fact about the scratch space, and a
defeasible one would let a contradiction among the hypotheses quietly unhook the
context holding them.

## Scope

**In:** `core/abduce` / `core/abduce-discard!`, the context lifecycle, the dead-end
observer, the gate, `abducible_predicate`, provenance, the caps, the irredundancy check.

**Out:**

* **Best-explanation ranking.**  Returning the candidate set is in; scoring it by
  likelihood needs a cost model this KB has no source for.
* **Full ATMS minimality** over environments — the subset check here is deliberately
  cheaper.
* **Open (non-ground) hypotheses** — skolemization's territory (docs/skolem.md).
* **Committing to base belief automatically.**  The caller decides.

**Isolation is exact, not nearly so**, and note why rather than only that.
Two things could in principle move a base handle, and neither can:

* **Defeat** does not sweep.  A hypothesis contradicting a base default leaves it
  *defeated* — support intact, retained for revival — so the record stays put and the
  teardown flips the label back.
* **Blocking** does sweep: an `exceptWhen` that holds makes a justification invalid,
  suppresses groundability, and the dependency-directed sweep *deletes* the conclusion, so
  a revival is a re-derivation at a handle that never existed.  But a hypothesis cannot
  reach one.  A rule's exception is evaluated in **the conclusion's placement context**,
  and a base conclusion is placed at or above the asking context — which is strictly above
  the scratch one and cannot see into it.  A hypothesis on the exception's very predicate
  leaves a base firing untouched; a firing whose placement *is* the scratch context
  concludes there and is discarded with everything else.

So the tested claim is the strong one: the same records, the same justifications, the same
beliefs, at the same handles.
