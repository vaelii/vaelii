# Exceptions: `exceptWhen`

- **Covers:** how a rule states its own exception (`exceptWhen`) — blocking evaluation, the
  re-check index, and the stratification check over the rule dependency graph.
- **Not here:** the same undercutting block inlined per antecedent literal →
  [naf.md](naf.md); defeat classes, order independence and contradiction reporting →
  [nmtms.md](nmtms.md).
- **Assumes:** justification, defeasible, belief, `genl` → [glossary.md](glossary.md).

How a rule states its own exception: a belief-following meta-sentex that names the
rule by handle, re-evaluated per firing rather than materialized per instance.

## The problem it solves

Without it, a defeasible generality and its exception are two unrelated rules
concluding opposite literals:

```clojure
(set/defaultRule (implies (bird ?x) (flies ?x)))
(set/defaultRule (implies (penguin ?x) (not (flies ?x))))
```

Nothing connects them. Both conclusions are derived, and the connection has to be
*rediscovered* syntactically at settle time by matching `S` against `(not S)` — which
puts every hard question in the rediscovery rather than in the knowledge: which
contexts make the pair a real clash, what breaks a tie between two defaults, and how
to recover an ordering the ontology already implies without reading it back off the
genl hierarchy ([nmtms.md](nmtms.md), *There is no second axis*).

The deeper cost is that no argument survives. `why (flies Opus)` and
`why (not (flies Opus))` are two disjoint trees, and nothing records which won or
why — so an application cannot argue for or against a proposition, which is the
whole point of keeping justifications.

An exception belongs on the rule it excepts:

```clojure
(exceptWhen (flightlessBird ?b)
  (set/defaultRule (implies (bird ?b) (hasAbility ?b flying))))
```

## Semantics

`exceptWhen` **blocks**. When the exception holds for a binding, the rule does not
conclude for that binding — there is no conclusion to defeat and nothing to
arbitrate. Under forward chaining the conclusion is never created; under backward
chaining the argument is constructed and then reported as excepted, so `why-not`
can say *"rule R applies via `(bird Opus)`, but its exception `(flightlessBird
Opus)` holds"* instead of recomputing a contradiction it never recorded.

`why-not` therefore needs an arity that takes a **sentence and a context**, not
just a handle. A blocked conclusion is never created, so it has no handle to ask
about — the question is only askable of a proposition. It answers `{:reason
:excepted :rule <handle> :exception <ground sentence> :via <antecedent handles>}`,
which is the argument the backward chainer built before discarding it.

This is undercutting defeat. It is not the same as rebutting, and vaelii keeps
both: two rules concluding `P` and `¬P` with neither naming the other's case is a
genuine dilemma (the Nixon diamond), and the engine represents it rather than
deciding it. Coexisting `P`/`¬P` at `:default` is therefore the signature of a real
dilemma, not of a badly-written exception.

An `(unknown S)` **antecedent** is the same mechanism inlined per-literal — the rule
does not conclude for a binding under which `S` is derivable — and it reuses
everything below (the level-6 evaluation, the re-check index, block / sweep / revive,
the stratification graph), differing only in that each `unknown` is an independent
block condition rather than a conjunction. See [naf.md](naf.md).

### The exception is a query, not a literal

The exception is **any closed level-6 query** once the rule's bindings are
substituted in — see [levels.md](levels.md). Level 6 (`:solved`) is the full prover
stack *minus* rule backchaining, so an exception may reach through genl
specificity, the genlContext visibility closure, transitive/symmetric/inverse
metadata, disjointness, and evaluable arithmetic.

Two properties make this affordable:

- **Closed.** Every variable is bound by the rule's antecedents before the
  exception runs, so it is a ground question, never a search for bindings.
- **One answer suffices.** It is an existence check. The levels stack is lazy
  throughout, so the query stops at the first result.

**A conjunction is a vector**, spelled the way `core/prove` spells one:

```clojure
(exceptWhen [(flightlessBird ?b) (adult ?b)] (implies (bird ?b) …))
```

Closure is what makes this cheap: with every variable already bound, the conjuncts
share nothing, so each is an independent ground existence check and *all* must
hold. There is no join, and level 6 needs no conjunctive goal form — the evaluator
runs each conjunct separately. A single literal may be written bare.

**Closure is enforced, not assumed.** A variable in the exception that no
antecedent binds is rejected at assert time, like a range-restriction failure on a
consequent. That forbids an existential exception — "birds fly unless they have a
sick child" is not expressible, because `?child` would be unbound. This is a real
limit and the price of the exception being a ground check rather than a search;
the workaround is an antecedent that binds the witness.

**No backchaining.** An exception that is only derivable by running rules (level 7)
does not hold. This bounds the cost and keeps an exception from silently invoking
an unbounded proof search inside the relabel loop.

**An unanswerable exception does not hold**, and the rule fires. This is the
open-world reading, and it matches `argIsa`, where an argument whose type is
unknown cannot violate a constraint. Blocking on "cannot tell" would let a
missing fact silently suppress knowledge.

**The exception is evaluated in the conclusion's placement context**, not the
rule's. The conclusion is what the exception is about, and an exception invisible
from where the conclusion would live has no business blocking it. Backward chaining
places nothing, so it has no placement context; there the exception is evaluated in
the query's context instead, the backward analogue of the same rule.

## The exception is a meta-sentex, not a materialized extent

The exception is stored **once**, as a belief-following meta-sentex
`(exceptWhen <query> (sentexHandle H))` naming the rule `H` it qualifies
(`sentex/exceptWhen-meta`), its query aligned to the rule's canonical variables. It is
*not* materialized per instance, and the obvious per-instance implementation —
materialize the ground exception as an unbelieved node and put its handle in the
justification's `out` set — is wrong twice over.

**It would store the negative space.** `(exceptWhen (flightlessBird ?b) ...)` over ten
thousand birds would materialize a probe for every bird that *is not* flightless, which
is nearly all of them. The store would grow with the exceptions that do not apply. The
one meta-sentex says the same thing without the extent.

**An arbitrary query has no handle.** `out` is a set of handles and can only say
"these specific propositions are not believed". An exception answered through
transitivity or arithmetic has no single node whose OUT-ness stands for it. The
`out` slot is the wrong shape for this, independently of materialization.

So the exception's *query* is not materialized: the one meta-sentex holds it, the
engine reads a rule's exceptions with `provers/rule-exceptions` (the term index on the
handle, belief-filtered), and **re-evaluates** them per firing. An index exists only to
decide *when* re-evaluation is needed. Because the exception is an ordinary
belief-following fact, a rule and its unexcepted twin share one handle — asserting or
retracting an exception amends the rule in place — and retracting or defeating the
exception lifts the block.

### The re-check index

The key structural fact is one the engine already maintains: **a rule handle is an
antecedent of every justification it licenses**. So every conclusion a rule
produced is reachable from the rule through the existing consequence links, and no
per-firing bookkeeping is required.

That allows an index at *rule* granularity:

```
[:exception-index <predicate>] -> #{rule handles whose exception mentions that predicate}
[:exception-index :rules]      -> #{every rule handle carrying an exception}
```

Rules are few, so this is the scale of the existing rule index — tens of entries,
never millions.

**"Mentions" means a symbol in functor position at any nesting depth**, not just
the top-level functor of each conjunct, since a level-6 query can reach a predicate
through a subterm. When in doubt, **over-approximate**: a spurious re-check costs
one query, while a missed one is a correctness bug that shows up as a conclusion
that should have been swept and wasn't.

Two consequences worth stating:

- The **`:rules` roster is written unconditionally**, even for an exception that
  mentions no indexable predicate. The taxonomy trigger enumerates that set, and a
  rule missing from it would be invisible to `genl` edge changes.
- **Retraction recomputes the predicates from the stored sentex** rather than
  trusting what a caller has in hand. The index holds no derived state, so a
  mismatched deregistration leaks a stale posting — harmless (a wasted re-check)
  but avoidable, and recomputing is the rule that cannot drift.

When a fact with predicate `P` is asserted or retracted, the rules whose exception
mentions `P` are looked up, their justifications reached through the rule handle's
consequences, and those conclusions joined to the affected region.

### Narrowing the re-check to the firings a trigger can reach

Rule granularity is right for deciding *whether* to look at a rule and far too coarse
for deciding *which of its firings* to re-evaluate. Re-running the exception query for
every justification the queued rule ever licensed is quadratic in that rule's firing
count, and was measured so (see "The cost is in re-checking" below).

So the queue carries the **triggering sentences** alongside each rule handle, and the
firings are filtered before a single query is paid for:

- Substituting the firing's bindings into the rule's exception conjuncts yields ground
  literals. Closure guarantees they are ground, and this is pure structure manipulation
  — **no store access at all**, which is what makes the filter worth running.
- A triggering fact can only answer a ground exception literal when their argument
  lists agree **and** the fact's predicate lies in the exception predicate's `specs`
  closure. That closure is the in-memory taxonomy, not the stored index. The `specs` half is
  load-bearing rather than defensive: an exception on `flightless` is satisfied by a
  stored `(penguin Opus)` when `(genl penguin flightless)`, so comparing the two
  predicates for equality would miss the case the taxonomy exists for. It is also
  exactly the test the index itself is keyed on, read in the other direction, so the
  filter narrows *within* what the index selected and never past it.
- Arguments are compared as a **multiset**, so a symmetric predicate's mirrored fact
  still matches — level 6 probes both orders, and so must this.
- Only the survivors run the level-6 query.

**Every "cannot tell" answers keep.** A literal that is not flat and ground, a nested
subterm, a predicate whose truth a level-6 prover can derive from *different* arguments
(the `genl`/`genlContext` closures, disjointness, anything declared transitive or
reflexive or holding an inverse, anything with a **preserved argument position**, the
evaluables) — each of those skips the filter and keeps every candidate. A spurious
re-check costs one query; a missed one is a conclusion that should have been swept and
wasn't.

Preservation is the one of those that cannot be listed in the code, and the one where
argument agreement is at its most misleading: `(argPreserving bigger n genl)` makes a
stored `(bigger dog cat)` answer `(bigger poodle siamese)`, so the trigger and the
conjunct agree on **no argument at all** while naming the same predicate — which reads
to the filter exactly like an unrelated fact. Which predicates those are is a property
of the content, so the question asked is `inherit/declared-about?`, the same O(1) gate
`ArgPreservingProver` takes before its own read, and it is asked once per pass rather
than once per firing: substituting a firing's bindings never moves a functor, and one
arm of the answer is an index read that the filter's whole claim — that deciding it
touches nothing but memory — does not allow inside the per-firing loop.

**Four paths have no triggering sentence to narrow by**, and all four queue `:all`
rather than a set of sentences: a `genl`/`genlContext` edge change (the next section), a
**declaration** whose subject is the exception's predicate ("Four channels" below), an
**equality** moving the closure (same section), and a rule that has just been indexed. In
each the sentence that moved — an edge, a `(symmetric P)`, a `(sameAs A B)`, nothing at
all — shares no argument with the exception conjunct, so reading it would narrow the
firings away rather than down.

### Re-chaining what was released, not what was touched

The settle loop has a second cost of the same shape one layer down. When a pass blocks
a justification, the conclusion is swept, and a *released* exception then has to be
re-derived — which is forward chaining, not relabelling. Seeding `chain` with a rule
handle joins that rule over the **whole fact extent**, so handing it every rule the
pass touched costs one firing, and one level-6 query, per fact the rule has ever
matched: quadratic again, and independently of the re-check above.

What actually needs re-deriving is what the pass **released** — the informants of the
justifications that were blocked and are not any more. A newly *blocked* justification
has nothing to revive; its conclusion is what the sweep is about to collect. Three
things are re-chained: those released rules, the rules queued with `:all` (no sentence
to say whether the move blocked or released), and whatever the sweep itself queued —
deleting a fact can release some other rule's exception at derive time, where no block
ever existed to lift.

A pass is **productive** when the blocked set moved. Two things force one that did not.
An **aggregate** antecedent binds a *value*, so a count going 1 ⇒ 2 licenses a firing no
block ever suppressed. And a released **refusal** — the next section — is a firing that
never held a justification for the blocked set to have said anything about.

**Nothing caches the exception's truth**, so nothing can drift from belief. The
index is a hint about what to re-check and never an answer — which is what
distinguishes it from the cached closures, which are answers and are therefore
belief-following ([taxonomy.md](taxonomy.md)).

### A refused firing is remembered as bindings

`place-conseq` does not place a firing whose block condition already holds. That is the
right call for the placement — the conclusion would be swept on the same pass — but such
a firing otherwise leaves **no trace at all**: no justification, no node, nothing in
`jtms/blocked`. A pivot on the blocked set is therefore blind to it, and the conclusion
stays suppressed after the condition releases, while the same knowledge in the other
order concludes. Belief would depend on whether the block arrived before or after the
facts, which is the invariant [nmtms.md](nmtms.md) opens with.

So the refusal is recorded, one level earlier and in the same shape. Where the blocked
set holds justification ids, `(:refused kb)` holds `{rule-handle -> #{refusal}}`, and a
refusal is the firing's conclusion, its placement context, its antecedent handles and
the bindings the condition was asked under — enough to re-ask the same level-6 question,
and enough to place the conclusion from when the answer moves. A release is then found
by **re-evaluating the record**: one query per recorded refusal, in place of a join over
the fact extent.

**Two of the four refusal reasons are recorded**, and the other two are covered
elsewhere rather than forgotten:

| reason | recorded | why |
|---|---|---|
| the rule's exception holds | yes | re-askable from the bindings alone |
| an `(unknown S)` antecedent blocks | yes | likewise, and the same evaluator |
| a post-join literal had no answer | no | an aggregate is a *value* that moved, and a queued aggregate rule is re-joined whatever the blocked set did (`settle/aggregate-recheck-rules`) |
| a visibility `except` hides an antecedent | no | an `except` arriving or leaving queues every rule that could fire on the hidden fact (`special/recheck-except`), and queues it with **`:all`** — so it takes the coarse re-join and the refusal is re-derived there. An entry would be one nothing reads |

Both unrecorded reasons are covered by a **coarse re-join** rather than by nothing, and
that is what makes the record an efficiency structure rather than a completeness one.
The same holds past the cap below. A reader tempted to narrow `recheck-except`'s
fire-on-H rule set should note that it is what covers the fourth row: narrowing it to a
sentence-specific trigger would turn this table's last line into a real gap.

Four properties hold of the record, and each is the shape a work list has rather than
the shape an answer has:

- **It never decides belief.** It says which firings to re-ask, never what the answer
  is. Every entry is re-decided from scratch when it is read (`chain/refusal-state`),
  by the same judgement a blocked justification is re-decided by
  (`chain/rule-firing-blocked?`), so blocking cannot drift from belief and the two
  paths cannot drift from each other.
- **Nothing in it is a nogood**, and nothing in it reaches `contradictions`. Nothing was
  believed and nothing conflicts; the rule simply did not fire.
- **It is keyed on content.** Two refusals of the same rule at the same bindings from
  different passes are one entry, so arrival order cannot be read back out of it.
- **A refusal that fires is re-derived from what it recorded** — `place-conclusion` with
  the recorded conclusion, placement and antecedents, and the depth recomputed from the
  antecedent facts. Never a fresh join: re-joining is the cost the record exists to
  avoid.

An entry is retired when it fires, when its rule goes, or when an antecedent handle
behind its bindings is no longer stored and believed. The bindings are a snapshot, so
that last one is what stops a refusal resurrecting a firing whose support left; it is
checked whenever the record is walked, which is also when dead entries are dropped.

The record is **derived state**, and no store holds it — a refused firing left no
justification for `recover` to replay. So `recover` rebuilds it the way it rebuilds
blocking, by re-deciding rather than by reading: `chain/rerecord-refusals!` re-fires
every rule that can refuse, after the settle that establishes belief, and the refusals
re-record. A firing that is placeable is placed and deduped by `has-justification?`.

**The record is capped at `chain/max-refusals-per-rule` = 4096 entries per rule**, and
the cap is real rather than defensive. Blocking is bounded by what a rule *derived*;
this is bounded by what it did **not**, and a rule excepted on a common condition can
refuse far more than it places. On either side of the line:

- **under the cap**, a queued rule's refusals are re-evaluated individually and a
  released one is re-derived from its bindings;
- **at the cap**, the rule's record collapses to `:overflow`, it keeps no entries, and a
  queued overflowed rule forces a productive pass and is **re-joined over its extent**
  instead. That finds the same releases at the cost the record exists to avoid, and it
  is what the whole record buys its way out of for the rules under the line.

Neither side is silent: an overflowed rule is still reached by every trigger, and the
two edge triggers that narrow on a rule's firings wave it through for exactly the reason
they wave an aggregate through — a rule with no entries to test is one no test can
clear.

#### How big it gets

Measured on a join shape — `(pseen ?x ?y) ← (pb1 ?x ?z) (pb2 ?z ?y)` excepted on a
condition that holds for every binding, so all n² firings are refused — the record holds
**one entry per refused firing** and retains **≈766 bytes** apiece, flat across sizes:

| n | firings | entries | record |
|---|---|---|---|
| 20 | 400 | 400 | 0.3 MB |
| 40 | 1 600 | 1 600 | 1.2 MB |
| 80 | 6 400 | 6 400 | 4.5 MB |
| 160 | 25 600 | 25 600 | 18.7 MB |

That is the growth the cap is for: the entry count follows the *join*, not the store, so
one rule can outgrow the KB it is reasoning over. 4096 entries is about 3 MB per rule,
which is where the record stops being cheaper than the re-join it replaces.

#### What it costs

The workload is a taxonomy load under an excepted predicate: 800 firings of one excepted
rule, then 50 `genl` edges whose supertype is at or below the exception's own predicate,
so the rule is queued on every edge. Both halves matter and they pull in opposite
directions, so both are here:

| 800 firings, then 50 edges | building the firings | the 50 edges | total |
|---|---|---|---|
| the rule fires, nothing blocks | 334 ms | 2361 ms | **2695 ms** |
| every firing refused, no record | 300 ms | 19 ms | **319 ms** |
| every firing refused, recorded | 982 ms | 1381 ms | **2363 ms** |
| every firing refused, coarse re-join | 10 082 ms | 1598 ms | **11 680 ms** |

Read the second row first: it is cheap because it does **nothing**, which is the defect.
The first row is the price of a correct answer, and the engine has always paid it — a
rule whose firings *were* placed pays edges × firings through `exception-candidates` over
`jtms/dependents`. So the derive-time case is not a new asymptotic; it is the same one,
and it was free only while it was wrong.

Against that, the record costs **less than the engine already pays for the placed case**
(2363 against 2695: a refusal carries its bindings inline where a justification is a
record fetch away), and **4.9× less than the coarse re-join** it replaces. The re-join's
damage is concentrated where a record cannot be: in the *build*, where every arriving
fact forces a productive pass and joins the rule over everything asserted so far.

The record is not free either, and the third row says where it is paid: building those
800 refused firings goes from 300 ms to 982 ms, because a fact on the exception's own
predicate now narrows against the record as well as against the placed firings. That is
the shape `exception-candidates` has had all along — memory-only work per firing per
trigger, no query — and it is what a firing costs once it is remembered.

The edge half is linear in the firing count, on both sides of the fix: 104 / 341 /
1381 ms at 50 / 200 / 800 firings recorded, against 223 / 623 / 2384 ms for the same
firings placed.

### Taxonomy changes are keyed on what the closure moved

An exception like `(flightlessBird ?b)` can flip because someone asserted
`(genl penguin flightlessBird)` — no fact with a matching predicate ever arrives, so
there is no *sentence* to narrow by and the queueing is `:all`. What is narrowed is
**which rules**, and the two edge kinds key it differently because their closures reach
an answer differently.

- A **`genl`** edge `[sub super]` moves reachability only along paths through it, so the
  spec closure of an exception predicate `pe` changes iff `pe` is `super` or above it:
  `genls(super)` is the roster, plus the handful of functors a `genl` edge can flip
  without either endpoint appearing near the registered predicate (`genl` itself, whose
  conjunct the transitivity prover answers from the very closure that moved; `disjoint`,
  which is closed under `genl` on both sides; and `not`).
- A **`genlContext`** edge `[sub super]` moves what contexts *see*, and an exception is
  evaluated in its conclusion's placement context — so an exception is affected iff one
  of its rule's firings is placed in `context-down(sub)`. Each excepted rule's firings
  are checked for one, a context lookup apiece and no query. Keyed on where a firing
  was *placed*, so the same cone test is asked of the rule's **recorded refusals**,
  whose entries name the placement context the refused conclusion would have had — a
  rule blocked every time it fired has no placed firing to read a context off, and a
  widened cone that releases it would otherwise reach nothing.

  **A rule carrying an aggregate is waved through that narrowing**, because for it the
  absence is not a gap but a wrong answer. Every other re-check condition is a block, so
  whatever a widened cone can change always left a firing to find; an aggregate binds a
  **value**, and a census that rises licenses a firing that never existed — no placed
  conclusion, no context to read, nothing for the cone test to match. A count taken in
  `SubContext` before it inherited `UpContext` would simply stay taken. It is the same
  asymmetry the settle loop re-joins a queued aggregate rule for, met the same way, and
  costs one record fetch per excepted rule on a `genlContext` edge.

Both are gated on the `[:exception-index :rules]` roster being non-empty, so a KB using
no `exceptWhen` pays one set read per edge and stops — which matters, because that guard
is what keeps a deep taxonomy load from going quadratic on the up-closure alone.

### Four channels a declaration or a fact reaches an exception through sideways

The index's keying is *the exception's predicate and every supertype of it*, which is
sound for every level-6 prover that answers an exception from content on that predicate
(or a spec of it) — the fact fan-out, the transitive closures, the symmetric mirror.
Four things do not, and each arrives with no predicate relationship to the exception
at all for the genls walk to follow. All four queue `:all`, for the same reason the
taxonomy path does: what moved is about one predicate and the exception is about
another, so the sentence could not narrow the right firings anyway.

- **Argument preservation, from the relation's side.** `ArgPreservingProver` answers by
  walking the *arguments'* reach, so `(genl chihuahua dog)` flips an exception on
  `largerThan` with neither endpoint anywhere near it.
  `special/recheck-preserving-along` queues every rule whose exception mentions a
  predicate declared `(argPreserving P n R)` whenever `R`'s extent moves.
  [inherit.md](inherit.md) has the whole argument. (From `P`'s *own* side the index is
  already right — the fact is on the exception's predicate — and what has to give way
  there is the argument-agreement filter above.)
- **`argIsa` read as an inference.** A believed `(motherOf X …)` beside
  `(argIsa motherOf 1 mammal)` makes `X` a `mammal` and every supertype of it
  (`ArgTypeProver`, [inference.md](inference.md)), so a fact on `motherOf` satisfies an
  exception on `mammal` with nothing on `mammal` ever written and no genl path between
  the two predicates. `special/recheck-argisa-inferred` closes it, from both arrival
  orders — a fact of a declared predicate, and the declaration itself arriving over
  facts already stored.
- **A declaration, where no fact moved at all.** The extent of every predicate is
  exactly what it was, and what changed is what may be concluded from it:
  `(symmetric sibOf)` makes a stored `(sibOf Ann Bob)` answer `(sibOf Bob Ann)`,
  `(transitive partOf)` closes a chain, `(inverse childOf parentOf)` answers a goal from
  the partner predicate's facts, `(argPreserving P n R)` opens the inheritance over
  claims already stored, and `(asymmetric P)` is what gives a converse the standing to
  close one again. The sentence's functor is the declaration's, never the exception's,
  so the genls walk misses every one. `special/recheck-declaration` reads the subject
  predicate off argument 1 — two of them for `inverse`, since either one's goals are
  answered from the other's facts — and queues on `genls(subject)`. `transitive` gets a
  second posting through `recheck-preserving-along`, because it is also the **licence**
  `inherit/usable-relation?` reads at use: withdrawing it withdraws the inheritance for
  a `P` the sentence never names. `functional`, `arity` and the decontextualization
  marks are not in the roster — they are read by the definitional checks and by
  placement, and answer no goal.
- **An equality, which moves no extent and answers no goal.** A merge is not a fact
  arriving or leaving, and it reaches an exception twice over. It **retires a
  spelling** rather than removing a fact — the superseded sentex is still stored and
  still holds its handle, so no arm reports anything moving on its predicate, while it
  is gone from every belief-filtered read. And it **rewrites the question**: an
  exception conjunct spelled with a retired term is answered under the class
  representative, so `(penguin Tweety)` can start holding with nothing on `penguin`
  having moved at all. That second half is what rules out keying on a predicate the
  way the taxonomy path does, and the first rules out keying on the terms a firing
  names. `special/recheck-equality-edge` covers both, for an asserted `sameAs` /
  `rewriteOf` / `equals`, the equality a `functional` declaration derives, and a
  schematic rewrite rule — and both directions, since splitting a class gives the
  retired spellings back.

  It keys on the **merged class**, and on the firings rather than the rules: a firing is
  reached when it *binds* a term of the class, which is a set membership apiece and no
  query — the twin of the `genlContext` trigger's placement test, and asked of the
  rule's recorded refusals as well as of its justifications, since a refused firing's
  bindings are recorded too. Three things take the blanket instead. An **aggregate**
  rule, because a census can move with no term the firing names appearing in the merge
  at all — `(childOf Ann C3)` counted, `Ann` bound, `{C2 C3}` merged — and a census that
  rises licenses a firing there is no justification for yet. A **schematic rewrite**,
  which normalizes terms rather than merging symbols, so there is no class to test
  against. And the whole **removal** side, where the narrowing is not imprecise but
  blind: what a released condition owes a re-derivation to includes the firings the
  block already swept, and a swept firing holds no bindings to test.

All four are free for a KB not using the feature: the declarations are read off the
functor roots behind an O(1) cardinality gate, the declaration roster is a map lookup on
the functor, and the whole path sits behind the `[:exception-index :rules]` roster being
non-empty — which is what a KB that merges but carries no re-check condition pays, once
per merge. All four are read **globally** rather than per context, deliberately: a
declaration this context cannot see still qualifies a rule in one that can, and a
trigger has to be conservative in the direction the answer is.

A firing's **stored bindings** are the other half of that last channel, and they are the
half a trigger cannot fix. A justification records what matched when it fired, and a
merge does not go back and edit it — so a re-check substituting them asks about a term
the KB no longer answers under, and gets the honest empty that reads as *not excepted*.
`chain/settled-bindings` rewrites them to the representatives the conclusion's context
now elects, in that context, before any condition is evaluated: the same scoping every
other read of the partition takes, since a merge the conclusion cannot see must not
rename what its own re-check asks about.

The general rule these four are instances of: **a re-check trigger is sound only for the
provers whose answer is addressed by the key it uses.** Keying on the exception's
predicate covers every prover that reads content *at* that predicate; a prover that
reads the arguments, or reads one predicate to answer another, needs its own channel or
belief depends on arrival order. When a new prover joins the registry, the question to
ask of it is which content can move its answer, and the answer to a doubt is to queue.

## Blocking and the TMS

`vaelii.impl.jtms` is pure and in-memory: it has no KB and cannot run a level-6
query. So the exception is evaluated *outside* the TMS and the result handed in.

TMS state carries `:blocked`, a set of justification ids currently blocked by their
exception, and `valid?` reads it:

```clojure
(and (every? #(contains? in %) (:antecedents j))
     (not (contains? blocked (:id j))))
```

Belief and blocking are mutually dependent — a level-6 query reads believed facts,
and belief depends on which justifications are blocked — so `settle` iterates:
relabel, re-evaluate the exceptions in the region, relabel again if the blocked set
moved. `jtms/set-blocked` **replaces** the blocked set rather than adding to it, so
the fixpoint test is set equality and the loop iterates only while the blocked set
keeps moving. **Stratification is what makes that terminate** (see below); the loop
is bounded at **16 passes** regardless, so a bug cannot hang the engine.

## Garbage collection, not defeat

Blocking has no defeated state to keep a datum stored for. A defeated datum keeps its
support and stays stored so it can revive; a blocked justification is simply invalid,
the conclusion is unsupported, and the dependency-directed sweep **deletes** it along
with everything solely resting on it. That is the garbage collection, and it is the
retraction path that already exists.

The trade is deliberate. Reviving costs a re-derivation rather than flipping a bit:
retract the exception and the conclusion is chained again, not restored. Recompute
is cheaper than an unbounded store.

That has a consequence for `retract!`. A relabel and a sweep cannot revive what a
retraction released: when a retraction causes an exception to stop holding, the
conclusions it was blocking must be **re-derived**, which is forward chaining. So
`settle-after-teardown!` settles, re-chains from the rules whose exceptions were
released, and settles again — the revival is visible by the time `retract!` returns
rather than on the next unrelated assert.

## What surfaces where

Blocking produces no nogood at all: an excepted conclusion does not exist, so
nothing is contradictory and nothing is arbitrated. `conflicts` is empty for it.

`conflicts` narrows to what it always meant — irreducible clashes among known-true
content. A coexisting `P`/`¬P` pair at `:default` is not a conflict; it is a
represented dilemma, and it is what an application ranks. That needs its own
reader, `contradictions`, listing each coexisting pair with both handles and both
justifications. Reporting a dilemma as a "conflict" would say the engine failed at
something it deliberately declines to do.

## Stratification

If one rule's exception depends on what another rule concludes and vice versa, the
program has a cycle through negation, which admits zero or several stable models.
"Which one" would depend on arrival order, breaking the order-independence
invariant that [nmtms.md](nmtms.md) makes non-negotiable.

Level 6 helps but does not eliminate this — an exception cannot recurse through
rules *at query time*, but it can read a forward-derived stored fact, so a cycle
across two rules remains constructible.

So a rule set with a cycle through negation is **rejected at assert time**, as a
well-formedness check over the rule dependency graph alongside the `genl` cycle
check in [wff](../src/vaelii/impl/wff.clj). Rules are few, so the graph is small.
Common-sense rule sets are almost always stratified; this is a guard, not a tax.

### The graph

Two kinds of node — rules and predicates — and two kinds of edge:

```
rule R --depends-on--> P     P appears in R's antecedents        (positive)
rule R --excepts-on--> P     R's exception mentions P            (negative)
P --concluded-by--> rule R   R concludes P                       (positive)
```

A cycle crossing **at least one** negative edge is refused. A purely positive cycle
is ordinary recursion, which the engine supports and bounds by depth, and is
deliberately left alone — `stratification_test` pins both directions, because a
check that rejected recursion would be worse than no check at all.

**Predicate dependence is not literal.** An antecedent `(animal ?x)` is satisfied by
a stored `(dog Muffet)`, and an exception on `flightless` by a stored `(penguin Opus)`
when `(genl penguin flightless)` — so both kinds of outgoing edge fan out over the
genl **spec** closure, which is the fan-out matching does and the one
`special/recheck-on-predicate` keys the exception trigger on, read in the same
direction. A cycle that exists only through a subtype is caught. Expanding the
*consuming* side downwards is equivalent to expanding the producing side upwards, so
the consequent is looked up literally and the fan-out is paid once. Where the two
readings differ, **over-approximate**: refusing a stratified program is annoying,
accepting an order-dependent one is a correctness hole.

### The search

`wff/negation-cycle` is a plain DFS from the rule being asserted, and looks only for
cycles **through that rule**. Every rule assert runs the check, so the stored graph
is already free of them and adding one rule can only close a cycle passing through
it. The search state is `[rule negative?]` rather than the rule alone: a node reached
with and without a negative edge behind it are different states, and only the
negative one closes a bad cycle — which is exactly what lets positive recursion
reach the start node, find the flag false, and stop.

The rule being asserted **is not stored yet**, so `checks/stratification-concluders`
adds it to the graph by hand under its own consequent predicate. Without that, a
rule whose exception mentions what it concludes — a one-rule cycle, and the easiest
one to write by accident — would look stratified. Everything else is reached through
the rule index (`rules-by-consequent`, complete whatever a rule's direction), so
nothing scans.

The check runs **before anything is written**, so a refused rule leaves no partial
state: no sentex, no justification, and no posting in the rule or exception indexes. It
throws `ex-info` with `:type :not-stratified` and a `:cycle` naming the nodes and
edges around the loop.

**Fast path:** with no exception on the rule being added and none on any stored rule,
the graph has no negative edge at all and the walk is skipped. That is every rule in an
ontology that uses no exceptions, which is most of them. The guard is the KB's whole
exception index rather than the rule at hand, so **one** exception anywhere ends the
fast path for everything asserted after it: the bundled starter takes it until
`BiologyContext`'s `dead` exception loads, and pays the walk from there on. The walk is
cheap and the ordering is alphabetical, so this is a cost note, not a limit.

### A taxonomy edge closes a cycle too

Both kinds of outgoing edge fan out over the genl spec closure, so a rule is not the
only thing that can close a cycle: an exception on `flightless` reaches a rule
concluding `penguin` the moment `(genl penguin flightless)` holds, and it does not
matter which of the three arrived last. Walking on rule assert alone would accept an
unstratified program silently whenever the **edge** is the newcomer.

So the walk runs on `genl` / `genlContext` assert as well. `checks/edge-negation-cycle`
takes the coarse route this document already proposed for the re-check trigger, and
for the same reason — an edge change has no rule and no fact to narrow by:

- Every cycle through negation crosses a negative edge, and negative edges leave
  **excepted rules only**. So starting the walk at each excepted rule is complete,
  and `exception-rules` — the `[:exception-index :rules]` roster, which exists for the re-check
  trigger — is that set in one lookup.
- The edge is added to a **detached copy** of the taxonomy, so the question is asked
  of the graph-as-it-would-be without the real closures learning anything.
- Only *additions* need checking. `specs` grows monotonically with the edge set, so
  removing an edge only removes graph edges; a retraction can never close a cycle.

**The edge is refused.** The `genl` assert is the operation at fault, so refusing it
is the consistent answer: it is what `wff` already does to an edge that would make
the taxonomy cyclic, and it keeps the invariant that stored state is *always*
stratified — which is what lets the rule-side walk look only for cycles through the
rule being added. As on the rule path, the check runs before anything is written and
before the taxonomy is touched, so a refusal leaves no sentex, no justification, and no
closure that learned the edge.

**Fast path, again:** no stored rule carries an exception, so the graph has no
negative edge and nothing is walked. An ordinary `genl` assert pays one set read
and stops — which is every `genl` assert in the bundled starter.
`stratification_edge_test` pins that by *counting* the walks rather than timing them.

The trigger sits on both transitive relations, so the two edge kinds cannot drift
apart. Today only `genl` can actually move the graph: the dependency graph is over
**predicates** and mentions no context at all, so a `genlContext` edge adds no graph
edge and the walk finds nothing. That is a fact about the current graph rather than a
missing hook, and the test asserts both halves of it — the check runs, and it accepts.

### A derived edge is dropped, not thrown

`integrate-transitive` reaches the taxonomy from forward chaining as well as from
`assert`, so a rule concluding `(genl ?t flightless)` can close a cycle with no caller
asserting an edge. Throwing there is the wrong shape — chaining is a fixpoint and an
exception escaping one firing would make the resulting belief set depend on which
rule fired first.

So this joins the **`violations`** mechanism, which exists for exactly the same
situation one layer over: a derived conclusion that breaks a definitional constraint.
`chain/place-conclusion` asks `edge-stratification-violation` alongside
`constraint-violation`, and a bad edge is **dropped** — no sentex, no justification,
nothing in the closures — and reported in `(violations kb)` as
`{:violation :not-stratified :detail {:cycle …}}`. Dropping rather than merely
reporting is what keeps the invariant: an unstratified edge that was only reported
would still be in the taxonomy.

One consequence to state plainly: with stratified negation the **settled** state is
unique and order-independent, but intermediate states during a load are not. A rule
may fire, have its exception arrive, and be swept. Only the fixpoint is guaranteed.

## Storage and identity

`exceptWhen` is split at the assert layer (`rules/split-exceptWhen`): the rule stores
normally and the exception is stored **separately** as a meta-sentex
`(exceptWhen <query> (sentexHandle H))` naming the rule `H` it qualifies. The wrapper
never reaches the rule record — the pure `sentex` constructor drops a surface
`exceptWhen` wrapper onto the bare rule, and `core/assert-exceptWhen-meta!` builds and
stores the meta.

**The exception amends the rule in place.** Because it is a separate assertion, `bird ⇒
flies` and `bird ⇒ flies exceptWhen penguin` name the **same** rule handle: adding an
exception does not fork a second rule, it amends the one rule, and retracting the
exception restores it. A rule can carry several independent exceptions (block-if-any).
**The exception is deliberately not part of the rule's identity** — it is not in the trie
key ([indexing.md](indexing.md)) — because a rule that forked on acquiring one would leave
every justification the original licensed hanging off a handle nothing concludes.

**The query is aligned to the rule's canonical variables.** The exception is written in
the author's variable names beside the rule; `assert-exceptWhen-meta!` maps them to the
rule's canonical `?varN` through the rule-as-written's `:varmap`, so a firing's bindings
substitute straight in. A re-reference of the same rule under new variable names aligns
correctly, because the varmap is read from the rule as written *in this assert*, not
from whatever names the rule was first stored with.

**Conjunct order and repetition are not part of identity.** Conjuncts are sorted and
deduplicated (`sentex/sort-conjuncts`), so two spellings of one exception dedup to the
same meta-sentex.

**The meta-sentex is the first non-ground stored Atomic.** It carries the rule's
variables, so it is exempt from the ground-fact check, and it is excluded from ordinary
fact matching (`match-one`, `matches-hierarchical`, `sentexes-matching`) so it never surfaces as a
domain fact. It *is* findable by the handle it names — `(sentexHandle H)` is a ground
compound the term index keeps — which is how `provers/rule-exceptions` reads a rule's
exceptions.

**Closure is checked at the assert layer** (`sentex/check-exception-closed`, run atomically
on the wrapped form before the bare rule is stored): a variable no antecedent binds has
no canonical number to align to. It throws `ex-info` with `:type :exception-not-closed`.
The anonymous wildcard `_` is refused for the same reason range restriction refuses it —
two occurrences are two different variables, so no antecedent can ever bind one.

**Degenerate wrappers.** `exceptWhen` around a non-rule is stripped and ignored, as the
other wrappers are. Two `exceptWhen`s written together conjoin into one meta-sentex
(block-if-all); two asserted separately are independent exceptions (block-if-any).

## The parts

- **Evaluation.** `provers/exception-holds?` substitutes the firing's bindings into a
  conjunction (from `provers/rule-exceptions`) and runs each conjunct as an independent
  ground existence check over the registry — level 6 of the lookup stack, reached here
  without depending on `levels`. Nothing in the registry expands a rule, which is what
  keeps the check bounded. `exceptions-block?` ORs this over a rule's exceptions.
- **Blocking, in every chainer.** Forward chaining checks before placing
  (`derive-conclusion`), and `res/prove` and the node engine each
  carry a `:guards` entry on the parsed rule and drop the argument once it is complete. An
  exception that blocked forward but not backward would make `sentexes-matching` and `ask`
  disagree about one rule, which is the one thing it must never do. `prove` reduces
  a rule by *pushing* its antecedents, so its guard rides the goal stack as a marker
  behind them — that is the only point at which "the argument is now complete" is
  observable.
- **Triggers.** A fact arriving or leaving queues the rules whose exception mentions
  its predicate **or any supertype of it**; a `genl`/`genlContext` edge change queues
  the rules its own closure reaches; a declaration queues the rules whose exception
  mentions its subject predicate. The genl fan-out is not over-caution: an exception
  `(flightless ?b)` is satisfied by a stored `(penguin Opus)` through the spec walk,
  so keying the trigger on the literal predicate alone misses every exception stated
  at a more general type than the fact that satisfies it.
- **Narrowing.** The queue carries the triggering sentences, not just the rule handles,
  and the firings a trigger cannot reach are filtered out from memory alone before any
  query runs; the re-chain after a productive pass is seeded from what the pass
  *released*, plus the rules queued with no sentence to read, rather than from every
  rule it touched. Both quadratics above, gone.
- **The refusal record.** A firing refused before it could become a justification is
  remembered as `[rule handle, bindings]` in `(:refused kb)`, so a release reaches it
  too; `settle/released-refusals` re-evaluates the queued rules' entries under the same
  narrowing, and `chain/release-refusal!` re-derives the ones that no longer block from
  the bindings they recorded. Capped per rule, `recover` rebuilds it by re-firing.
- **Sweeping.** `jtms/sweep!` is `retract!`'s sweep without the retraction, and
  `settle` runs it over the newly-blocked justifications' conclusions.
- **Revival.** `retract!` captures the released rules before settling and re-chains
  them, so the re-derivation is visible by the time it returns.
- **`why-not`** carries a `(kb sentence context)` arity and the `:excepted` reason, which
  is the only route to a blocked conclusion: it is never stored, so there is no handle.
- **Stratification.** `wff/negation-cycle` walks the rule dependency graph on every
  rule assert and refuses one that closes a cycle through negation, before anything
  is stored. Per the measurement below it is a *correctness* guard, not an
  evaluation-ordering mechanism, so it sits beside the fixpoint loop rather than in
  place of it. `stratification_test` covers the two-, three- and one-rule cycles, the
  cycle that closes only through a genl subtype (with the no-genl control), direct
  and mutual positive recursion staying accepted, and the empty teardown.
- **Stratification on a taxonomy edge.** The same walk runs on `genl` / `genlContext`
  assert, started at each excepted rule, because the edge is as capable of closing a
  cycle as the rule is. An asserted edge that closes one is **refused** like a cyclic
  `genl`; a *derived* one is dropped and reported in `violations`, since chaining
  cannot throw. `stratification_edge_test` covers both, the two controls that make the
  refusal attributable to the cycle, the empty teardown of store *and* closures, and
  the fast path by walk count.

### The fixpoint question, measured

The open question was whether evaluation needs the iterate-to-fixpoint loop or whether
strata should be computed first so one pass suffices. `settle` is instrumented
(`core/settle-stats`): `:iterations` counts the passes in which the blocked set
actually **moved**.

| Case | `:iterations` |
|------|---------------|
| starter + stories load (462 settles) | **0** — every settle |
| every `except_test` scenario | **1** — max, in all of them |
| cried-wolf shape, all 120 permutations | **0** in 60, **1** in 60; never 2 |
| synthetic chain of N (each exception on the previous conclusion) | 0, 0, 0, **1**, **1**, **2**, **3** for N = 1,2,3,4,5,6,8 |

The synthetic chain is the control: the counter *does* rise, so a flat reading on real
content is a fact about the content and not a broken instrument.

**One pass suffices for realistic content.** The count never reaches 2 outside the
synthetic chain, so the loop never actually iterates on anything the bundled ontology
contains. The bounded loop stays, and stratification stays a pure correctness guard
against cycles rather than an evaluation-ordering mechanism.

The evidence is not perfectly clean and the caveat is worth stating: the count is not
*constant*, it varies 0/1 with permutation order. But that variation is between "the
derive-time check in `derive-conclusion` already caught it" and "the rule fired first,
so settle had to block and sweep once" — not between one pass and two. Both converge
to the same settled state (all 120 permutations of the cried-wolf shape agree), which
is the invariant that matters. Stratum order would move *when* the single evaluation
happens; it would not reduce the number of evaluations below one.

### The cost is in re-checking, not in evaluating

The more useful finding is about cost, and it is not the one the question asked about.
An exception that never holds is free; one that holds is flat in its rule's firing count,
and **the narrowing is what makes it flat** — without it, both call sites below are
quadratic. Measured as total elapsed time over n asserts against one excepted rule, the
narrowed run against an unnarrowed one:

| | n=25 | n=50 | n=100 | n=200 | scaling |
|---|---|---|---|---|---|
| no exception | 70 ms | 106 ms | 181 ms | 358 ms | flat, ≈1.8 ms/assert |
| exception present, never holds | 49 ms | 96 ms | 187 ms | 372 ms | flat (≈4%, within noise) |
| exception holds on every firing, unnarrowed | 452 ms | 1085 ms | 3102 ms | 11 698 ms | **quadratic** |
| exception holds on every firing, as it runs | 102 ms | 224 ms | 452 ms | 844 ms | flat, ≈4.2 ms/assert |

13.9× at n=200, and the row does not bend.

Timing measures the machine as much as the algorithm, so the load-bearing number is
the count of level-6 exception evaluations, which is exact:

| level-6 evaluations per assert | n=25 | n=50 | n=100 | n=200 |
|---|---|---|---|---|
| unnarrowed | 16.0 | 28.5 | 53.5 | 103.5 |
| as it runs | 3.0 | 3.0 | 3.0 | 3.0 |

**There are two quadratics to avoid here, and the benchmark above only ever exercises
one of them.** Separating them by call site is the whole of the diagnosis, and either
one reintroduced puts the curve back:

- `exception-blocked-set` re-evaluating **every** justification the queued rule
  licensed. Exactly n² — 625 / 2 500 / 10 000 evaluations at n = 25/50/100 — but it
  needs a rule with many *live* firings to show, so the benchmark above, whose firings
  are blocked and swept as fast as they are made, never pays it. It reads **0**: the
  narrowing filters every unreachable candidate out before a query is run.
- `rechain-exception-rules` re-joining the blocked rule over the whole fact extent
  after every productive settle pass. This is what the benchmark above actually pays,
  through `derive-conclusion` rather than through the re-check at all. Unnarrowed that
  is 375 / 1 375 / 5 250 evaluations at n = 25/50/100; as it runs, 50 / 100 / 200.

The lesson is the ordinary one about attributing a measurement: the shape of the curve
says "quadratic in the firing count" and the first plausible mechanism fits it, but the
call sites tell a different story, and only one of the two candidates is on the
benchmark's path. `except_recheck_test` pins both, by count rather than by clock.

## Two mechanisms this makes unnecessary, and why neither belongs here

`exceptWhen` makes `penguin ⇒ ¬flies` beat `bird ⇒ flies` **structurally**. Two other
mechanisms would do the same job, and neither belongs in the engine — **do not add
either**:

- **A specificity heuristic**, ranking colliding defaults by the genl up-closure size
  of their rules' antecedent predicates. It guesses at what a block states outright,
  and its answer moves with how densely the taxonomy above each predicate happens to
  be populated.
- **A third defeat class**, letting a non-defeasible rule outrank a defeasible
  generality. The lattice is `:monotonic > :default` and holds exactly two: a bare rule
  confers `:monotonic`, capped at its weakest antecedent, and a `set/defaultRule`
  confers `:default`. A third class is a second ordering that has to be kept consistent
  with the first.

`why-not` recomputes the excepted argument with `excepted-argument` rather than reading
the one the backward chainer built.
