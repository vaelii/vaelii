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

Nothing connects them, and nothing records which one wins.
[why](defenses.md#the-exception-belongs-on-the-rule-it-excepts)

An exception belongs on the rule it excepts:

```clojure
(exceptWhen (flightless_bird ?b)
  (set/defaultRule (implies (bird ?b) (hasAbility ?b flying))))
```

## Semantics

`exceptWhen` **blocks**. When the exception holds for a binding, the rule does not
conclude for that binding — there is no conclusion to defeat and nothing to
arbitrate. Under forward chaining the conclusion is never created; under backward
chaining the argument is constructed and then reported as excepted, so `why-not`
can say *"rule R applies via `(bird Opus)`, but its exception `(flightless_bird
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
the stratification graph), including the conjunction: `S` may be an `(and …)`, read
block-if-all-hold by this same evaluator, which joins the conjuncts so a quantified one
takes a single witness for all of them ([naf.md](naf.md)). What differs is that each `unknown`
antecedent is an independent block condition, where a rule's exceptions are one.
See [naf.md](naf.md).

### The exception is a query, not a literal

The exception is **any closed level-6 query** once the rule's bindings are
substituted in — see [levels.md](levels.md). Level 6 (`:solved`) is the full prover
stack *minus* rule backchaining, so an exception may reach through genl
specificity, the genlCx visibility closure, transitive/symmetric/inverse
metadata, disjointness, and evaluable arithmetic.

Two properties make this affordable:

- **Closed.** Every variable is bound by the rule's antecedents before the
  exception runs, so it is a ground question, never a search for bindings.
- **One answer suffices.** It is an existence check. The levels stack is lazy
  throughout, so the query stops at the first result.

**A conjunction is a vector**, spelled the way `core/prove` spells one:

```clojure
(exceptWhen [(flightless_bird ?b) (adult ?b)] (implies (bird ?b) …))
```

Closure is what makes this cheap: with every variable already bound, the conjuncts
share nothing, so each is an independent ground existence check and *all* must
hold. Level 6 needs no conjunctive goal form: the conjuncts go through
`provers/conjunction-solutions`, the joined evaluator `unknown` and `thereExists` share
([naf.md](naf.md)), of which a ground conjunction is the degenerate case — each conjunct
contributes one solution or none, and the join *is* the independent existence check. A
single literal may be written bare.

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
open-world reading, and it matches `arg`, where an argument whose type is
unknown cannot violate a constraint. Blocking on "cannot tell" would let a
missing fact silently suppress knowledge.

**The exception is evaluated in the conclusion's placement context**, not the
rule's. The conclusion is what the exception is about, and an exception invisible
from where the conclusion would live has no business blocking it. Backward chaining
places nothing, so it has no placement context; there the exception is evaluated in
the query's context instead, the backward analogue of the same rule.

**The exception's own context is scoped the same way.** An `exceptWhen` meta-sentex is
a sentex, so a context reads the exceptions its `genlCx` ancestor set holds and no
others, as it reads the rules (`provers/exception-visible-from?`). An exception stated
in a context below the conclusion's blocks nothing in the conclusion's context, even
when its query holds there. A `genlCx` edge that brings the exception into the ancestor
set re-checks the firings placed below the edge, the same re-check any `genlCx` edge
queues (the re-check index, below).

## The exception is a meta-sentex, not a materialized extent

The exception is stored **once**, as a belief-following meta-sentex
`(exceptWhen <query> (sentexHandle H))` naming the rule `H` it qualifies
(`sentex/exceptWhen-meta`), its query aligned to the rule's canonical variables. It is
*not* materialized per instance.
[why](defenses.md#the-exception-is-not-materialized-per-instance)

So the exception's *query* is not materialized: the one meta-sentex holds it, the
engine reads a rule's exceptions with `provers/rule-exceptions` (the term index on the
handle, belief-filtered), and **re-evaluates** them per firing. An index exists only to
decide *when* re-evaluation is needed. Because the exception is an ordinary
belief-following fact, a rule and its unexcepted twin share one handle — asserting or
retracting an exception amends the rule in place — and retracting or defeating the
exception lifts the block.

### The re-check index

The key structural fact is one the engine already maintains: **the TMS lists every
justification a rule licenses under the rule's node** — the rule is the justification's
informant, and `valid?` needs it believed. So every conclusion a rule produced is
reachable from the rule through the existing consequence links, and no per-firing
bookkeeping is required.

That allows an index at *rule* granularity:

```
[:exception-index <predicate>] -> #{rule handles whose re-check condition mentions it}
[:exception-index :rules]      -> #{every rule handle carrying a re-check condition}
```

Rules are few, so this is the scale of the existing rule index — tens of entries,
never millions.

**"Mentions" means the predicate each conjunct *reads*, with the query frames peeled**
(`rules/watched-predicates`). A conjunct may itself be a query operator — the exception
is any closed level-6 goal, so `(unknown S)`, a `thereExists` and an aggregate all
stand there — and none of those functors is one a sentex is ever stored under. Keyed on
the operator, the rule sits in the index under a predicate nothing arrives on: the
exception is evaluated correctly once and re-evaluated never, which from the outside is
a guard that answers whatever happened first. So an `unknown` yields its conjuncts'
predicates, a `thereExists` its body's, an aggregate its census body's, and an `(and …)`
its conjuncts' — the last of which is how a **joined** NAF query under a quantifier gets
every one of its conjuncts watched ([naf.md](naf.md)), since any of them can be the
arrival that completes it.

`not` is the one frame left alone, because the *trigger* side keys an arriving `(not S)`
under `not` as well — one coarse bucket for every negated condition, but the two agree,
and peeling one side alone is what would break it.

A `different` antecedent is the one condition whose trigger predicates are named rather
than read off the sentence. It is negation as failure over the equality closure and over
the `indeterminate_term` category, so what flips it is a merge or an indeterminacy
arriving, and neither of those appears anywhere in the antecedent. The rule is registered
under the fixed set `rules/different-flip-predicates`, and `chain/different-blocks?`
re-decides the firing against its settled bindings
([predall.md](predall.md#a-different-guard-is-re-checked-not-supported)).

When in doubt, **over-approximate**: a spurious re-check costs one query, while a
missed one is a correctness bug that shows up as a conclusion that should have been
swept and wasn't. A predicate reachable only through a *subterm* is not indexed, and
the `genl` and equality edge triggers are what cover the conditions that move without
one.

Two consequences follow:

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
- The conjuncts are read through their **query frames** first
  (`rules/watched-literals`, the same peel the index keys on), because a shape test
  needs a literal a *fact* could carry. An exception that is itself a query operator has
  no shape however ground it is — `(unknown (qskip PX7))` is unreadable to the filter —
  so unpeeled it answers "cannot tell" every time and keeps the rule's whole history.
  That is where the shape is commonest, too: `(unknown S)` holds exactly while `S` is
  absent, which is the state a firing is *refused* in, so such a rule accumulates its
  history in the refusal record rather than as justifications. Both populations are
  filtered the same way and both peel.
- A triggering fact can only answer a ground exception literal when their argument
  lists agree **and** the fact's predicate lies in the closure that literal's polarity
  names. That closure is the in-memory taxonomy, not the stored index, and for a
  **positive** conjunct it is `specs`. That half is required rather than defensive:
  an exception on `flightless` is satisfied by a stored `(penguin Opus)` when
  `(genl penguin flightless)`, so comparing the two predicates for equality would miss
  the case the taxonomy exists for. It is also exactly the test the index itself is
  keyed on, read in the other direction, so the filter narrows *within* what the index
  selected and never past it.
- A **negated** conjunct takes `specs` **and** `genls`, because two different things
  move it and they run in opposite directions. A negative trigger answers it directly,
  and matching under a negation is contravariant — `(not (flightless Opus))` is answered
  by a stored `(not (animal Opus))` when `flightless ⊑ animal`
  ([inference.md](inference.md), "Under a negation the fan reverses") — which is the
  `genls` half. A positive trigger moves it the other way, by contradicting the negative
  sentex the conjunct reads and flipping its belief, and a positive fact on a spec is
  what does that. The shape test drops polarity, so a trigger of either kind arrives
  under one shape and the union is what covers both; over-approximating is the safe
  direction here as it is everywhere in this filter, an extra candidate being a re-check
  that changes nothing and a missing one a lost withdrawal.
- Arguments are compared as a **multiset**, so a symmetric predicate's mirrored fact
  still matches — level 6 probes both orders, and so must this.
- Both sides are read under the **equality-class representative** when the KB has merged
  anything (`settle/merge-normalizer`). A justification records what matched when it
  fired and a merge does not go back and edit it, while a rule's condition keeps the
  constants it was written with — so the same content reaches the test under two
  spellings and agrees on no argument at all. Collapsing both sides puts one class under
  one symbol, which is the only reading on which argument agreement means what the test
  takes it to mean. Read **unscoped**, like the `specs` closure beside it: the two sides
  go through the same function, so a class the reader cannot see collapses on both or on
  neither and the answer can only broaden. A KB that has merged nothing skips the
  rewrite outright, one deref at the top of the pass.
- Only the survivors run the level-6 query.

**Every "cannot tell" answers keep.** A literal that is not flat and ground, a nested
subterm, a predicate whose truth a level-6 prover can derive from *different* arguments
(the `genl`/`genlCx` closures, disjointness, anything declared transitive or
reflexive or holding an inverse, anything with a **preserved argument position**, the
evaluables) — each of those skips the filter and keeps every candidate. A spurious
re-check costs one query; a missed one is a conclusion that should have been swept and
wasn't.

Preservation is the one of those that cannot be listed in the code, and the one where
argument agreement is at its most misleading: `(transitiveInArg bigger n genl)` makes a
stored `(bigger dog cat)` answer `(bigger poodle siamese)`, so the trigger and the
conjunct agree on **no argument at all** while naming the same predicate — which reads
to the filter exactly like an unrelated fact. Which predicates those are is a property
of the content, so the question asked is `inherit/declared-about?`, the same O(1) gate
`TransitiveInArgProver` takes before its own read, and it is asked once per pass rather
than once per firing: substituting a firing's bindings never moves a functor, and one
arm of the answer is an index read that the filter's whole claim — that deciding it
touches nothing but memory — does not allow inside the per-firing loop.

**Several paths have no sentence that could narrow the firings**, and each queues `:all`
rather than a set of sentences: a `genl`/`genlCx` edge change (the next section), the two
argument-side channels — preservation and `arg`-inference — a **declaration** whose
subject is the exception's predicate, an **equality** moving the closure (all four under
"Four channels" below), and a rule that has just been indexed. In
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

Re-derivation is needed for what the pass **released** — the informants of the
justifications that were blocked and are not any more. A newly *blocked* justification
has nothing to revive; its conclusion is what the sweep is about to collect. Three
things are re-chained: those released rules, the rules queued with `:all` (no sentence
to say whether the move blocked or released), and whatever the sweep itself queued —
deleting a fact can release some other rule's exception at derive time, where no block
ever existed to lift.

A pass is **productive** when the blocked set moved. Three things force one that did not.
An **aggregate** antecedent binds a *value*, so a count going 1 ⇒ 2 licenses a firing no
block ever suppressed — and a **nested** NAF joins it there, since an arriving fact can
remove the witness its inner query found ([naf.md](naf.md)). A released **refusal** — the next section — is a firing that never
held a justification for the blocked set to have said anything about. And a **revived**
datum is one whose firing was never attempted, because the join ran while it was OUT and
the matcher is belief filtered; that one is not an exception mechanism at all, and it is
[nmtms.md](nmtms.md#a-revived-datum-is-a-datum-the-agenda-has-not-seen)'s to explain.

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
set holds justification ids, `(reasoning/refused kb)` holds `{rule-handle -> #{refusal}}`, and a
refusal is the firing's conclusion, its placement context, its antecedent handles, the
bindings the condition was asked under, and the **depth bound the refusing run was
configured with** (so a release honours that bound, not the default, in a settle with no
run config in scope) — enough to re-ask the same level-6 question,
and enough to place the conclusion from when the answer moves. A release is then found
by **re-evaluating the record**: one query per recorded refusal, in place of a join over
the fact extent.

**Two of the four refusal reasons are recorded**, and the other two are covered
elsewhere rather than forgotten:

| reason | recorded | why |
|---|---|---|
| the rule's exception holds | yes | re-askable from the bindings alone |
| an `(unknown S)` antecedent — or a closed-extent negative one — blocks | yes | likewise, and the same evaluator |
| a post-join literal had no answer | no | an aggregate is a *value* that moved, and a queued aggregate rule is re-joined whatever the blocked set did (`settle/rejoin-on-arrival-rules`) |
| a visibility `except` hides an antecedent | no | an `except` arriving or leaving queues every rule that could fire on the hidden fact (`special/recheck-except`), and queues it with **`:all`** — so it takes the coarse re-join and the refusal is re-derived there. An entry would be one nothing reads |

The record holds four more kinds of entry, none of them a refusal by an exception. Three
are kept because the thing that refused them was an **absence** that later content can
fill; the fourth is the opposite, a derivation withheld for something the KB has:

| entry | kept under | refused because | re-asked when |
|---|---|---|---|
| `:constraint` | the rule | `place-fact-conclusion` dropped the conclusion on an `arg` / `genlArg` / `interArg` / `interArgs` / `interArgAndRest` / `quotedArg` conviction: the argument's types had no path to the declared one | a `genl` or `genlCx` generation moved since the entry was decided, or a settle relabelled a sentex naming the convicted term |
| `:lift` | the source fact | a `decontextualized_predicate` copy from a context that does not see CxUniverse failed the same argument check there | the same two |
| `:mint` | the declaration | the declared type did not yet reach `thing` (`checks/mintable-type?`), so the declaration minted nothing over its facts | a `genl` or `genlCx` generation moved |
| `:subsumed` | each antecedent that entails it | the minted type is one a believed membership says more specifically (`checks/subsumed-mint`), so no record was written — or the one written was blocked and swept | the membership it gave way to stops being believed, or a `genl` generation moved |

`settle` re-asks them each pass (`released-constraint-refusals`, `released-lifts`,
`released-mints`, `released-subsumed`): a conclusion now admissible is placed from the entry, a copy lifted, a
declaration's whole sweep run again (`special/entail-existing`), and what each creates goes
on the agenda. A `:constraint` or `:lift` entry re-asked and still convicted is stamped with
the current generations and with the term the conviction names **now**
(`checks/conviction-watch`). An application can be convicted on more than one argument,
and the conviction names the first; once that argument is typed it names the next, so an
entry that kept its first term would never be re-asked when the last one is typed, and the
order the arguments were typed in would decide whether the conclusion is placed. Placed, a
`:constraint` or `:lift` entry withdraws the ledger entry its drop
filed (`violations/withdraw!`), since the order that brought the type first filed none.
A `:subsumed` entry is re-derived rather than re-inserted — `checks/constraint-entailments`
over the antecedent's own sentence, narrowed to the sentence that was withheld — so the
record comes back justified exactly as the arrival order that never withheld it justifies
it (docs/argtypes.md). Its two gates are O(1) per entry, which is what lets a KB holding a
thousand withheld mints re-ask them all on every settle.

`recover` rebuilds the `:mint` and `:lift` entries (`special/rebuild-pending!`); the
`:constraint` ones are not rebuilt, since that would mean re-firing every forward rule
over the store, so a KB restarted with a standing constraint drop re-derives it only when
its rule next fires. The `:subsumed` ones are not rebuilt either, and for the same kind of
reason: rebuilding them would mean running every declaration's sweep over the store to
find the mints it withholds. A KB restarted with a withheld mint keeps withholding it —
which is what the store says — and draws it again when the fact, the declaration or an
edge under them next moves.

Both unrecorded reasons are covered by a **coarse re-join** rather than by nothing, and
that is what makes the record an efficiency structure rather than a completeness one.
The same holds past the cap below. A reader tempted to narrow `recheck-except`'s
fire-on-H rule set should note that it is what covers the fourth row: narrowing it to a
sentence-specific trigger would turn this table's last line into a real gap.

Four properties hold of the record, and each is the form a work list has rather than
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

The record is also what the **chaining funnel** reads. `core/chain-report` walks every
forward rule (enumerated `O(rules)` off the antecedent roster, never the fact extent) and
for each reports what it placed — `jtms/dependents` on the rule handle is its firings —
against what this record says it refused and why, re-deciding each entry through
`refusal-state` so a reason shown is one that still holds. A rule that placed nothing and
refused nothing never completed an antecedent set. That is the per-rule breakdown the
browser draws at `/funnel` ([web.md](web.md)), and it needs no per-run counter: the ledger
and the justification graph already hold the answer.

The record is **derived state**, and no store holds it — a refused firing left no
justification for `recover` to replay. So `recover` rebuilds it the way it rebuilds
blocking, by re-deciding rather than by reading: `chain/rerecord-refusals!` re-fires
every rule that can refuse, after the settle that establishes belief, and the refusals
re-record. A firing that is placeable is placed and deduped by `has-justification?`.

That re-fire runs at the **default** depth bound, not whatever bound each original run
set. A run's `:max-depth` is transient live-session config that no store holds — exactly
as `recover`'s derivation depths reset to 0, since a bound only ever governs *future*
chaining. So a KB chained under a non-default bound and then recovered rebuilds its
refusals, and releases them, at the default; that matches the live session everywhere the
default was used, and can differ from it only in the narrow case where a refusal's
re-derivation depth had risen above a smaller live bound. The bound on an entry is a
live-session refinement of *that* session's releases; the recovered KB is internally
consistent at the default it rebuilt over, which is the same default its reset depths now
bound future chaining against.

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
**one entry per refused firing** and retains **roughly 750 bytes** apiece, flat across
sizes:

| n | firings | entries | record |
|---|---|---|---|
| 20 | 400 | 400 | ~0.3 MB |
| 40 | 1 600 | 1 600 | ~1.2 MB |
| 80 | 6 400 | 6 400 | ~4.5 MB |
| 160 | 25 600 | 25 600 | ~19 MB |

That is the growth the cap is for: the entry count follows the *join*, not the store, so
one rule can outgrow the KB it is reasoning over. 4096 entries is about 3 MB per rule,
which is where the record stops being cheaper than the re-join it replaces.

#### What it costs

The workload is a taxonomy load under an excepted predicate: 800 firings of one excepted
rule, then 50 `genl` edges whose supertype is at or below the exception's own predicate,
so the rule is queued on every edge. Both halves matter and they pull in opposite
directions, so both are here. The times are one run's wall clock on one box, rounded —
what they are for is the ratio between the rows, which is the structure of the argument:

| 800 firings, then 50 edges | building the firings | the 50 edges | total |
|---|---|---|---|
| the rule fires, nothing blocks | ~0.3 s | ~2.4 s | **~2.7 s** |
| every firing refused, no record | ~0.3 s | ~0.02 s | **~0.3 s** |
| every firing refused, recorded | ~1.0 s | ~1.4 s | **~2.4 s** |
| every firing refused, coarse re-join | ~10 s | ~1.6 s | **~12 s** |

Read the second row first: it is cheap because it does **nothing**, which is the defect.
The first row is the price of a correct answer, and the engine pays it either way — a
rule whose firings *are* placed pays edges × firings through `exception-candidates` over
`jtms/dependents`. So the derive-time case is not a second asymptotic; it is the one the
placed case already has, paid in the cheaper of the two shapes.

Against that, the record costs **less than the engine already pays for the placed case**
(~2.4 s against ~2.7 s: a refusal carries its bindings inline where a justification is a
record fetch away), and **roughly 5× less than the coarse re-join** it replaces. The
re-join's damage is concentrated where a record cannot be: in the *build*, where every
arriving fact forces a productive pass and joins the rule over everything asserted so far.

The record is not free either, and the third row says where it is paid: building those
800 refused firings roughly triples, because a fact on the exception's own predicate now
narrows against the record as well as against the placed firings. That is
`exception-candidates`'s own shape — memory-only work per firing per trigger, no
query — and it is what a firing costs once it is remembered.

The edge half is linear in the firing count, on both sides of the fix: on the same
workload it reads roughly 0.1 / 0.34 / 1.4 s at 50 / 200 / 800 firings recorded, against
roughly 0.2 / 0.6 / 2.4 s for the same firings placed — whose 800-firing figure is the
edge column of the table above.

### Taxonomy changes are keyed on what the closure moved

An exception like `(flightless_bird ?b)` can flip because someone asserted
`(genl penguin flightless_bird)` — no fact with a matching predicate ever arrives, so
there is no *sentence* to narrow by and the queueing is `:all`. What is narrowed is
**which rules**, and the two edge kinds key it differently because their closures reach
an answer differently.

- A **`genl`** edge `[sub super]` moves reachability only along paths through it, so the
  spec closure of an exception predicate `pe` changes iff `pe` is `super` or above it:
  `genls(super)` is the roster, plus the two functors a `genl` edge can flip without
  either endpoint appearing near the registered predicate — `genl` itself, whose conjunct
  the transitivity prover answers from the very closure that moved, and `disjoint`, which
  is closed under `genl` on both sides. Both are answered *across arguments*, so neither
  can be keyed on a predicate and both take `:all`.

  A **negated** conjunct is the third case, and it is keyed at the edge's other end. It
  registers under the functor `not` — that is what `(exceptWhen (not (has_wings ?x)) …)`
  puts in the index — so the registration hides the predicate the conjunct is about and
  the `genls(super)` walk has nothing to decide it with. What decides it is that a
  negative match is **contravariant**: `(not (dog X))` is read off a stored
  `(not (animal X))` by walking the **up**-closure of the conjunct's own predicate
  ([inference.md](inference.md), "Under a negation the fan reverses"). An edge
  `[sub super]` moves that closure for exactly the predicates at or below `sub`, so
  `specs(sub)` is the keying — the contravariant twin of the covariant walk above it, on
  the one functor whose registration says nothing about its subject. Reading the conjunct costs one record fetch per rule carrying a negated
  condition and nothing at all for a KB carrying none, and anything it cannot read — a
  body whose functor is a variable, a compound, or a connective frame — answers keep.
  What the keying is worth is the alternative: queued on the functor alone, such a rule
  takes `:all`, which is one level-6 query per firing it ever made, on every `genl` edge
  written anywhere in the KB.
- A **`genlCx`** edge `[sub super]` moves what contexts *see*, and an exception is
  evaluated in its conclusion's placement context — so an exception is affected iff one
  of its rule's firings is placed in `context-down(sub)`. Each excepted rule's firings
  are checked for one, a context lookup apiece and no query. Keyed on where a firing
  was *placed*, so the same ancestor set test is asked of the rule's **recorded refusals**,
  whose entries name the placement context the refused conclusion would have had — a
  rule blocked every time it fired has no placed firing to read a context off, and a
  widened ancestor set that releases it would otherwise reach nothing.

  **A rule an arrival can release is waved through that narrowing**
  (`rules/arrival-releasable?`), because for it the absence is not a gap but a wrong
  answer. Most re-check conditions are a block, so whatever a widened ancestor set can change
  always left a firing to find. Two are not. An aggregate binds a **value**, and a census
  that rises licenses a firing that never existed — no placed conclusion, no context to
  read, nothing for the ancestor set test to match; a count taken in `CxSub` before it inherited
  `CxUp` would simply stay taken. A **nested** NAF is the same shape one level in: an
  arriving fact removes the witness the inner query found ([naf.md](naf.md), `forall`),
  and again there was never a blocked justification to unblock. It is the same asymmetry
  the settle loop re-joins such a rule for, met the same way.

  The narrowing is what that exemption is measured against, and it is not free: one
  record fetch per excepted rule to ask the exemption, and then one per **firing** for
  the ancestor set test. `some` short-circuits on a hit, so a rule the edge reaches costs the
  firings up to the first one in the ancestor set, and a rule it reaches through none costs every
  firing that rule ever made. That is the price of narrowing on placement rather than
  queueing wholesale, and a `genlCx` edge is the only thing that pays it.

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

- **Argument preservation, from the relation's side.** `TransitiveInArgProver` answers by
  walking the *arguments'* reach, so `(genl chihuahua dog)` flips an exception on
  `largerThan` with neither endpoint anywhere near it.
  `special/recheck-preserving-along` queues every rule whose exception mentions a
  predicate declared `(transitiveInArg P n R)` whenever `R`'s extent moves.
  [inherit.md](inherit.md) has the whole argument. (From `P`'s *own* side the index is
  already right — the fact is on the exception's predicate — and what has to give way
  there is the argument-agreement filter above.)
- **`arg` read as an inference.** A believed `(motherOf X …)` beside
  `(arg motherOf 1 mammal)` makes `X` a `mammal` and every supertype of it
  (`ArgTypeProver`, [inference.md](inference.md)), so a fact on `motherOf` satisfies an
  exception on `mammal` with nothing on `mammal` ever written and no genl path between
  the two predicates. `special/recheck-arg-inferred` closes it, from both arrival
  orders — a fact of a declared predicate, and the declaration itself arriving over
  facts already stored.
- **A declaration, where no fact moved at all.** The extent of every predicate is
  exactly what it was, and what changed is what may be concluded from it:
  `(symmetric sibOf)` makes a stored `(sibOf Ann Bob)` answer `(sibOf Bob Ann)`,
  `(transitive partOf)` closes a chain, `(inverse childOf parentOf)` answers a goal from
  the partner predicate's facts, `(transitiveInArg P n R)` opens the inheritance over
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
  query — the twin of the `genlCx` trigger's placement test, and asked of the
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
The condition's own **written-in constants** are the same problem from the other side: a
rule is held back from an individual-only rewrite migration, so `(exceptWhen (mskip
MOne) …)` goes on naming `MOne` after the merge has retired it.

The **question** carries the rewrite for both, and once: `provers/exception-holds?` puts
each substituted conjunct in its context's normal form before evaluating it, which
settles the firing's bindings and the condition's constants in one walk — so the
derive-time check and the re-check ask one question of one firing however the merge is
ordered against them. `chain/settled-bindings` rewrites the binding map itself, for the
conditions that read a binding rather than a goal: an aggregate's recount and an
inheritance re-check. Both scope to the conclusion's context, the scoping every other
read of the partition takes, since a merge the conclusion cannot see must not rename
what its own re-check asks about.

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
(let [inf (:informant j)]
  (and (every? #(contains? in %) (:antecedents j))
       (or (not (integer? inf)) (contains? in inf))   ; the rule, when it is a handle
       (not (contains? blocked (:id j)))))
```

Belief and blocking are mutually dependent — a level-6 query reads believed facts,
and belief depends on which justifications are blocked — so `settle` iterates:
relabel, re-evaluate the exceptions in the region, relabel again if the blocked set
moved. `jtms/set-blocked` **replaces** the blocked set rather than adding to it, so
the fixpoint test is set equality and the loop iterates only while the blocked set
keeps moving. **Stratification is what makes that terminate** (see below); the loop
is bounded at **16 passes** regardless, so a bug cannot hang the engine.

`core/blocked-justifications` is that set, read: the ids blocked as of the last settle.
It is the one property of a justification that **belief alone does not report** — a
blocked justification's antecedents can all be IN, so a reader judging support from belief
calls it supporting when it supports nothing. Hence a whole-set read rather than a
per-id question: the reader asking is usually rendering a proof tree, and wants one read
per page rather than one per justification. It is served (`:blocked-justifications`) and
reachable from `vaelii.client` and the access facade, so an **attached** browser draws the
same pills as an in-process one; the network is not a record, and without the op there is
nothing over the wire to ask.

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

A rule whose exception depends on what another rule concludes, and vice versa, is a
cycle through negation. Level 6 cannot recurse through rules *at query time*, but an
exception can read a forward-derived stored fact, so a cycle across two rules remains
constructible even though the exception evaluator itself never expands a rule.
[why](defenses.md#a-cycle-through-negation-is-rejected-not-resolved)

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

**Fast path:** with no negative dependency on the rule being added — no exception, no
`unknown`, no aggregate, no closed-extent negative and no `different` — and no exception
on any stored rule, the graph has no negative edge at all and the walk is skipped. That
is every rule in an ontology that uses none of them, which is most of them. The second
half of the guard is the KB's whole exception index, so **one** exception anywhere ends
the fast path for everything asserted after it: the bundled starter takes it until
`CxBiology`'s `dead` exception loads, and pays the walk from there on. The walk is
cheap and the ordering is alphabetical, so this is a cost note, not a limit.

### A taxonomy edge closes a cycle too

Both kinds of outgoing edge fan out over the genl spec closure, so a rule is not the
only thing that can close a cycle: an exception on `flightless` reaches a rule
concluding `penguin` the moment `(genl penguin flightless)` holds, and it does not
matter which of the three arrived last. Walking on rule assert alone would accept an
unstratified program silently whenever the **edge** is the newcomer.

So the walk runs on `genl` / `genlCx` assert as well. `checks/edge-negation-cycle`
takes the same coarse route the re-check trigger takes on an edge, and for the same
reason — an edge change has no rule and no fact to narrow by:

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
**predicates** and mentions no context at all, so a `genlCx` edge adds no graph
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
`checks/constraint-admission` and `special/wff-violation`, and a bad edge is **dropped** — no sentex, no justification,
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
`exceptWhen` wrapper onto the bare rule, and `assert-entry/assert-exceptWhen-meta!` builds and
stores the meta.

**The exception amends the rule in place.** Because it is a separate assertion, `bird ⇒
flies` and `bird ⇒ flies exceptWhen penguin` name the **same** rule handle: adding an
exception does not fork a second rule, it amends the one rule, and retracting the
exception restores it. A rule can carry several independent exceptions (block-if-any).
**The exception is deliberately not part of the rule's identity** — it is not in the trie
key ([indexing.md](indexing.md)) — because a rule that forked on acquiring one would leave
every justification the original licensed hanging off a handle nothing concludes.

**A polycanonicalized rule gets one exception per expansion.** The `exceptWhen` is split
off *before* the expansion runs, so a rule whose consequent conjoins or whose antecedent
disjoins is stored as several — and the exception is re-attached once per stored rule,
against that rule's own handle. It has to be per-handle because the meta-sentex names a
handle, and per-*varmap* because each expansion is canonicalized on its own: a self-join
tie group can be numbered differently by two conjuncts (the consequent breaks the tie),
so one shared alignment would misalign the exception on whichever expansion numbered
differently. `assert` returns the vector of exception handles in that case, exactly as
the bare rule returns the vector of rule handles
([canonicalization.md](canonicalization.md)).

An `or` **inside** the exception query is refused instead of expanded, and the reason is
one paragraph up: the conjuncts of one exception all have to hold, while a rule's
exceptions block if **any** holds. So a disjunctive exception is already two exceptions —
assert `(exceptWhen <alternative> (sentexHandle H))` once per alternative, and each is
separately assertable, retractable and believable, which one `or` inside a single query
would not be.

**The query is aligned to the rule's canonical variables.** The exception is written in
the author's variable names beside the rule; `assert-exceptWhen-meta!` maps them to the
rule's canonical `?varN` through the rule-as-written's `:varmap`, so a firing's bindings
substitute straight in. A re-reference of the same rule under new variable names aligns
correctly, because the varmap is read from the rule as written *in this assert*, not
from whatever names the rule was first stored with.

**Conjunct order and repetition are not part of identity.** Conjuncts are sorted and
deduplicated (`sentex/sort-conjuncts`), so two spellings of one exception dedup to the
same meta-sentex.

**The exception has a defeat class of its own, and a spelling for it.** The meta-sentex
is a premise like any other, so it stands at a strength — and `assert` takes one `opts`
for what is really *two* assertions, the rule and the exception qualifying it. That one
option reaches both halves, which says three of the four rule × exception pairings and
cannot say the fourth: a **known-true exception on a default rule**. That one is stated
on the query, `(exceptWhen (set/monotonic Q) R)`. The wrapper is peeled at the entry point
(`sentex/peel-exception-strength`) and never reaches the store, so the meta-sentex is the
sentence it always was; what it changes is the class the premise is marked at. `check`
reports the same `:shape` refusal `assert` throws for a wrapper written round the wrong
number of queries, and two `exceptWhen`s written together conjoin into one meta-sentex,
so a wrapper on either query says the whole exception is known-true. This is the spelling
the text KB format writes and reads back ([kbs.md](kbs.md)).

**The meta-sentex is the one non-ground stored Atomic.** It carries the rule's
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
  conjunction (from `provers/rule-exceptions`) and runs the conjuncts through
  `provers/conjunction-solutions` — one evaluator with `unknown`, and on a ground
  conjunction exactly the independent existence checks it has always been — over the
  registry, level 6 of the lookup stack, reached here
  without depending on `levels`. Each substituted conjunct is first put in the **normal
  form its context answers under** (`condition-normalizer`), the preparation
  `levels/engine-goal` gives a level-6 read and `kb/rewrite-goal` a query: a bound term
  and a written-in constant alike may be a spelling an equality merge has retired, and a
  conjunct asked as written gets the honest empty that reads as *not excepted*. Nothing
  in the registry expands a rule, which is what keeps the check bounded.
  `exceptions-block?` ORs this over a rule's exceptions.
- **Blocking, in every chainer.** Forward chaining checks before placing
  (`derive-conclusion`), while `res/prove` carries a `:guard` on the parsed rule and the
  node engine a `:guards` list, each dropping the argument once it is complete. An
  exception that blocked forward but not backward would make `sentexes-matching` and `ask`
  disagree about one rule, which is the one thing it must never do. `prove` reduces
  a rule by *pushing* its antecedents, so its guard rides the goal stack as a marker
  behind them — that is the only point at which "the argument is now complete" is
  observable.
- **Triggers.** A fact arriving or leaving queues the rules whose exception mentions
  its predicate **or any supertype of it**; a `genl`/`genlCx` edge change queues
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
  remembered as `[rule handle, bindings]` in `(reasoning/refused kb)`, so a release reaches it
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
- **Stratification on a taxonomy edge.** The same walk runs on `genl` / `genlCx`
  assert, started at each excepted rule, because the edge is as capable of closing a
  cycle as the rule is. An asserted edge that closes one is **refused** like a cyclic
  `genl`; a *derived* one is dropped and reported in `violations`, since chaining
  cannot throw. `stratification_edge_test` covers both, the two controls that make the
  refusal attributable to the cycle, the empty teardown of store *and* closures, and
  the fast path by walk count.

### The fixpoint question, measured

Whether evaluation needs the iterate-to-fixpoint loop, or whether strata computed first
would let one pass suffice, is answered by measurement. `settle` is instrumented
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

The evidence is not perfectly clean and the caveat matters: the count is not
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
| no exception | ~70 ms | ~110 ms | ~180 ms | ~360 ms | flat, ≈1.8 ms/assert |
| exception present, never holds | ~50 ms | ~100 ms | ~190 ms | ~370 ms | flat (≈4%, within noise) |
| exception holds on every firing, unnarrowed | ~450 ms | ~1.1 s | ~3.1 s | ~12 s | **quadratic** |
| exception holds on every firing, as it runs | ~100 ms | ~220 ms | ~450 ms | ~840 ms | flat, ≈4 ms/assert |

Roughly 14× at n=200, and the row does not bend.

Timing measures the machine as much as the algorithm, so the required number is
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

The lesson is the ordinary one about attributing a measurement: the structure of the curve
says "quadratic in the firing count" and the first plausible mechanism fits it, but the
call sites tell a different story, and only one of the two candidates is on the
benchmark's path. `except_recheck_test` pins both, by count rather than by clock.

## Two mechanisms this makes unnecessary, and why neither belongs here

`exceptWhen` makes `penguin ⇒ ¬flies` beat `bird ⇒ flies` **structurally**, without
either of two mechanisms that would do the same job: a specificity heuristic ranking
colliding defaults by genl up-closure size
([why](defenses.md#there-is-no-second-axis)), or a third defeat class ranking a
non-defeasible rule above a defeasible generality
([why](defenses.md#two-strength-classes-not-three)). The lattice stays
`:monotonic > :default`, exactly two classes: a bare rule confers `:monotonic`,
capped at its weakest antecedent, and a `set/defaultRule` confers `:default`.

`why-not` recomputes the excepted argument with `excepted-argument` rather than reading
the one the backward chainer built.
