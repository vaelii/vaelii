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

`exceptWhen` **blocks**. When the exception holds for a binding, the firing at that
binding supports nothing, and no nogood arbitrates it. Under forward chaining the
conclusion is stored with a guard defeat resting on the facts the exception holds
through, whether those facts are `:default` or `:monotonic`, and a reader that does not
believe them believes the conclusion (design rulings 25 and 30,
[naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)). An exception that holds
through no stored fact (a prover answer, such as an `argIsa` or a symmetric reading)
places the defeat on the exception's own handle.
Under backward chaining the argument is constructed and then reported as excepted, so
`why-not` can say *"rule R applies via `(bird Opus)`, but its exception
`(flightless_bird Opus)` holds"* instead of recomputing a contradiction it never
recorded.

`why-not` therefore needs an arity that takes a **sentence and a context**, not
just a handle: the backward chainer stores nothing, so the conclusion it discards has no
handle to ask about. It answers `{:reason
:excepted :rule <handle> :exception <ground sentence> :via <antecedent handles>}`,
which is the argument the backward chainer built before discarding it.

This is undercutting defeat. It is not the same as rebutting, and vaelii keeps
both: two rules concluding `P` and `¬P` with neither naming the other's case is a
genuine dilemma (the Nixon diamond), and the engine represents it rather than
deciding it. Coexisting `P`/`¬P` at `:default` is therefore the signature of a real
dilemma, not of a badly-written exception.

A conclusion the exception does not block is `:default`, whatever the rule's
defeasibility and its antecedents' classes, because a later fact can block it
([nmtms.md](nmtms.md#strength-propagates-from-the-antecedents)).

An `(unknown S)` **antecedent** is the same mechanism inlined per-literal — the rule
does not conclude for a binding under which `S` is derivable — and it reuses
everything below (the level-6 evaluation, the re-check index, the guard defeat,
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

- **Closed.** Every free variable is bound by the rule's antecedents before the
  exception runs, so it never searches for the rule's bindings. A `thereExists` inside
  it searches for its own witness, and stops at the first.
- **One answer suffices.** It is an existence check. The levels stack is lazy
  throughout, so the query stops at the first result.

**A conjunction is a vector**, spelled the way `core/prove` spells one:

```clojure
(exceptWhen [(flightless_bird ?b) (adult ?b)] (implies (bird ?b) …))
```

With every free variable bound, the conjuncts share nothing, so each is an independent
existence check and *all* must hold. The conjuncts go through
`provers/conjunction-solutions`, the joined evaluator `unknown` and `thereExists` share
([naf.md](naf.md)); on a ground conjunction each conjunct contributes one solution or
none. A single literal may be written bare.

**Closure is enforced, not assumed.** A free variable in the exception that no
antecedent binds is rejected at assert time (`:exception-not-closed`), like a
range-restriction failure on a consequent. A variable a `thereExists` binds is not
free, so an existential exception is written with one:

```clojure
(exceptWhen (thereExists ?c (and (childOf ?b ?c) (sick ?c)))   ; "unless it has a sick child"
            (implies (bird ?b) (flies ?b)))
```

The `(and …)` under the quantifier is joined, so one `?c` must satisfy both conjuncts
([naf.md](naf.md)). The binder must be **local**: one the antecedents also name is
refused `:quantifier-not-local`, because the rule's binding would replace it before the
query runs. Binders are numbered past the rule's variables when the exception is
stored, so two exceptions that differ only in a binder's name are one meta-sentex.

A `forall` conjunct is stored as the nested NAF it is, as a `forall` antecedent is
([naf.md](naf.md)), so it and its `(unknown (thereExists …))` spelling are one
meta-sentex. A count is compared inside a quantifier that binds it, since the conjuncts
of a vector share no variable:

```clojure
(exceptWhen (thereExists ?n (and (agg/count ?n ?c (childOf ?b ?c)) (lessThan 1 ?n)))
            (implies (bird ?b) (flies ?b)))
```

**No backchaining.** An exception that is only derivable by running rules (level 7)
does not hold. This bounds the cost and keeps an exception from silently invoking
an unbounded proof search inside the relabel loop.

**An unanswerable exception does not hold**, and the rule fires. This is the
open-world reading, and it matches `arg`, where an argument whose type is
unknown cannot violate a constraint. Blocking on "cannot tell" would let a
missing fact silently suppress knowledge.

**The exception is evaluated in the conclusion's placement context**, not the
rule's. The conclusion is what the exception is about, and an exception invisible
from where the conclusion would live has no business blocking it. Where the exception
holds below the placement and not at it, the firing stores a guard `defeat` of its
conclusion there, as an `unknown` antecedent does, and a reader that sees the defeat does
not believe the conclusion through that firing
([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)). The defeat is placed
at the contexts that see the placement, the blockers and the `genl` edges the query
climbed, and at the context of each `except` that takes a blocker's own defeat out of
force there. Backward chaining
places nothing, so it has no placement context; there the exception is evaluated in
the query's context instead, the backward analogue of the same rule.

**The exception's own context is scoped the same way.** An `exceptWhen` meta-sentex is
a sentex, so a context reads the exceptions its `genlCx` ancestor set holds and no
others, as it reads the rules (`provers/exception-visible-from?`). An exception stated
in a context below the conclusion's blocks nothing in the conclusion's context, even
when its query holds there. The firing stores a guard `defeat` at the contexts that see
its placement, the exception and the blockers, where the query holds, as for a blocker
below the placement (`chain/place-guard-defeats!`). A `genlCx` edge that brings the exception into the ancestor
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

The TMS lists every justification a rule licenses under the rule's node, since the rule
is the justification's informant. Every conclusion a rule produced is therefore
reachable from the rule through the consequence links, and the index works at *rule*
granularity with no per-firing bookkeeping:

```
[:exception-index <predicate>] -> #{rule handles whose re-check condition mentions it}
[:exception-index :rules]      -> #{every rule handle carrying a re-check condition}
```

**"Mentions" means the predicate each conjunct *reads*, with the query frames peeled**
(`rules/watched-predicates`). A conjunct may itself be a query operator (`(unknown S)`,
a `thereExists`, an aggregate), and no sentex is stored under those functors, so a rule
keyed on the operator would be re-evaluated never. An `unknown` yields its conjuncts'
predicates, a `thereExists` its body's, an aggregate its census body's, and an `(and …)`
its conjuncts', so every conjunct of a **joined** NAF query under a quantifier is watched
([naf.md](naf.md)).

`not` is the one frame left alone, because the trigger side keys an arriving `(not S)`
under `not` as well. Three kinds of extra key cover the negated conjuncts a positive
arrival moves (`special/exception-recheck-predicates`):

- every type a separation holds apart from the `T` of a unary `(not (T …))`
  (`rules/separation-denial-predicates`), since `DisjointnessNegationProver` answers the
  denial from a membership of such a type;
- every predicate a `negates` declaration says negates the `P` of a `(not (P …))` or a
  supertype of it (`rules/negates-denial-predicates`), since `NegatesProver` answers the
  denial from a tuple of such a predicate. A `negates` arriving after the rule, or a
  `genl` edge under a predicate one reaches, posts the rule again
  (`special/repost-negates-denial-rules`);
- the `P` of a `(not (P …))` on which a closed extent is declared
  (`rules/closed-extent-query-predicates`), since a `(P …)` arriving or leaving moves it.

A `different` antecedent is the one condition whose trigger predicates are named rather
than read off the sentence. It is negation as failure over the equality closure and over
the `indeterminate_term` category, so what flips it is a merge or an indeterminacy
arriving, and neither of those appears anywhere in the antecedent. The rule is registered
under the fixed set `rules/different-flip-predicates`, and `chain/different-blocks?`
re-decides the firing against its settled bindings in the conclusion's context
([predall.md](predall.md#a-different-guard-is-re-checked-not-supported)).

The index **over-approximates**: a spurious re-check costs one query, and a missed one
leaves a conclusion believed that the exception blocks. A predicate reachable only
through a *subterm* is not indexed; the `genl` and equality edge triggers cover the
conditions that move without one.

- The **`:rules` set is written unconditionally**, even for an exception that mentions
  no indexable predicate, because the taxonomy trigger enumerates that set.
- **Retraction recomputes the keys from the stored sentex**, not from what the caller
  holds, so a deregistration removes exactly the postings the registration wrote.

When a fact with predicate `P` is asserted or retracted, the rules whose exception
mentions `P` are looked up, their justifications reached through the rule handle's
consequences, and those conclusions joined to the affected region.

### Narrowing the re-check to the firings a trigger can reach

Rule granularity decides *whether* to look at a rule, not *which of its firings* to
re-evaluate, and re-running the exception query for every justification the queued rule
licensed is quadratic in its firing count
([measured](defenses.md#the-exception-re-check-narrows-to-firings-not-rules)). The queue
therefore carries the **triggering sentences** beside each rule handle, and
`recheck/exception-candidates` filters the firings before any query runs:

- Substituting the firing's bindings into the exception conjuncts yields ground
  literals, with no store access.
- The conjuncts are read through their **query frames** first (`rules/watched-literals`,
  the peel the index keys on), because a shape test needs a literal a fact could carry:
  `(unknown (qskip PX7))` has no shape, and unpeeled it would keep the rule's whole
  history.
- A triggering fact can answer a ground exception literal only when their argument lists
  agree **and** the fact's predicate lies in the closure the literal's polarity names,
  read off the in-memory taxonomy. A **positive** conjunct takes `specs`: an exception on
  `flightless` is satisfied by a stored `(penguin Opus)` when `(genl penguin flightless)`.
  This is the index's own keying read in the other direction, so the filter narrows
  within what the index selected.
- A **negated** conjunct takes `specs` **and** `genls`. A negative trigger answers it
  contravariantly — `(not (flightless Opus))` is answered by a stored
  `(not (animal Opus))` when `flightless ⊑ animal` ([inference.md](inference.md), "Under a
  negation the fan reverses") — and a positive fact on a spec moves it by contradicting
  the negative sentex it reads. The shape test drops polarity, so the union covers both.
  A negated conjunct is also reached by a tuple of a predicate a `negates` declaration
  says negates its own (`recheck/negates-reaches?`).
- Both closures cross `genlInverse` edges (`special/signed-all`).
- Arguments are compared as a **multiset**, so a symmetric predicate's mirrored fact
  matches, as level 6 probes both orders, and so does a fact a `genlInverse` edge swaps.
- Both sides are read under the **equality-class representative** when the KB has merged
  anything (`recheck/merge-normalizer`). A justification keeps the terms it matched and a
  rule keeps the constants it was written with, so without the rewrite one content
  reaches the test under two spellings. The rewrite is unscoped, as the `specs` closure
  is, and goes through one function on both sides, so it can only broaden the answer. A
  KB that has merged nothing skips it.
- With no merge, and every conjunct flat over a named predicate the filter does not wave
  through, with a variable argument, a conjunct agrees with a trigger only when one of
  its variables is bound to a trigger argument. The filter looks the variables up in the
  firing's bindings first and drops a firing that binds none of them to one
  (`recheck/firing-test`), so a firing the trigger does not name costs a lookup per
  variable and no substitution. `lein perf`'s `except-of-a-guard-blocker` holds the
  re-check flat in the rule's firings the trigger does not name.
- Only the survivors run the level-6 query.

**Every "cannot tell" answers keep.** A literal that is not flat and ground, a nested
subterm, a predicate whose truth a level-6 prover can derive from *different* arguments
(the `genl`/`genlCx` closures, disjointness, anything declared transitive or
reflexive or holding an inverse, anything with a **preserved argument position**, the
evaluables) — each of those skips the filter and keeps every candidate.

Preservation is the one of those the code cannot list, because it is a property of the
content: `(transitiveInArgInverse bigger n genl)` makes a stored `(bigger dog cat)` answer
`(bigger poodle siamese)`, and the two agree on no argument. The filter asks
`inherit/declared-about?`, the O(1) presence check `TransitiveInArgProver` takes before
its own read, once per pass rather than once per firing, since a substitution never moves
a functor.

**Several paths have no sentence that could narrow the firings**, and each queues `:all`
rather than a set of sentences: a `genl`/`genlCx` edge change (the next section), the two
argument-side channels — preservation and `arg`-inference — a **declaration** whose
subject is the exception's predicate, an **equality** moving the closure (all four under
"Five channels" below), and a rule that has just been indexed. In each the sentence that
moved shares no argument with the exception conjunct. Two more paths have no such
sentence either, and narrow by what the firing's withdrawal reads instead (the next
section).

### Two withdrawals a firing carries

Two withdrawals belong to a rule's firings rather than to its exception, and each is
posted on ordinary fact arrival: an **unsatisfiable network** (`chain/entailment-withdrawn?`,
posted by `special/recheck-on-qualitative` for every rule joining on a calculus the
sentence moves, [qcn.md](qcn.md), and by `special/composed-exception-rules` for every
rule whose block literal the calculus answers, "Five channels" below) and a **more
specific `:monotonic` contrary claim** (`chain/inheritance-withdrawn?`, posted by
`special/recheck-preserving-firings` for every
rule with an antecedent on a preserved predicate the sentence moves,
[inherit.md](inherit.md); a `:default` one places a defeat instead). The sentence is no
narrowing trigger for either: a constraint
moves entailments network-wide, and a claim or a reach edge shares no argument with the
goals it moves, and `:all` would re-decide every firing the rule has made on every
arrival, quadratic over a load. Each posts a **marker** instead, with its own test
(`recheck/exception-candidates`):

- **`::entailment`.** A firing is withdrawn only while a network its rule joins on is
  unsatisfiable at the firing's placement context. The *governing* contexts are those
  holding a fact the network reads, or a `genl` edge into a sub-predicate it reads,
  closed under meets; every context sees the sentences one of them at or above it sees,
  less what a defeat or an `except` withdraws below it, and a network over fewer facts is
  never tighter. So while every governing network is satisfiable
  (`qcn-kb/unsatisfiable-somewhere?`), the candidates are the rule's **blocked** firings,
  which a network turned satisfiable releases, and no other; otherwise every firing. A
  rule whose block literals name a predicate a calculus answers keeps every firing, since
  that answer moves with the network as a whole: every arrival that moves the calculus
  re-decides every firing of such a rule
  ([why not a baseline](defenses.md#a-composed-exception-keeps-every-firing-not-a-network-baseline)).
  `lein perf`'s `qcn-arrival-over-composed-exceptions` bounds the cost.
- **`{::preserving s}`.** A claim moves only a goal whose product holds its tuple, so every
  argument of such a goal is an argument of the claim or a term one of them licenses. A
  fact on a relation moves only a goal whose reach crosses it, and a walk from the goal's
  term reaches the fact's first end whether or not the fact stands, so some argument of
  the goal is an end of the fact or a term one licenses along it
  (`inherit/moved-goal-test`, read at `'?ctx`). A membership moves a goal on a predicate a
  separation holds apart from its type, at the membership's own argument, and a separation
  or a `genl` edge under a separated type moves every goal of a predicate whose
  separations it moves (`inherit/separation-moved`). A firing is a candidate when a goal it
  bound on a declared predicate passes, read under both spellings when the KB has merged
  anything. A declaration, `transitive`, `asymmetric`, a permuting mark and a `genl` edge
  into a declared predicate have no test and keep every firing.

Neither marker narrows what the pass re-chains or which refusals it re-asks: a marked rule
takes both as an `:all` one does. The entailment test costs the governing networks'
satisfiability per settle, with nothing per firing, and `lein perf`'s
`qcn-arrival-over-standing-firings` bounds an arrival over standing firings. The
preservation test still reads one record per firing, and the chainer's full re-join of the
same rules (`inherit/rejoin-rules`) is linear in the claims beside it.

### Re-chaining what was released, not what was touched

When a pass blocks a justification on a condition its rule carries (a closed extent, an
aggregate, a withdrawn `different`; `chain/rule-firing-blocked?`), the conclusion is
swept, and a *released* block has to be re-derived by forward chaining. Seeding `chain`
with a rule handle joins that rule over the **whole fact extent**, so seeding it with
every rule the pass touched is a second quadratic, independent of the re-check above.

Re-derivation is needed for what the pass **released**: the informants of the
justifications that were blocked and are not any more. Three things are re-chained:
those released rules, the rules queued with `:all` or a
withdrawal marker (no sentence to say whether the move blocked or released), and whatever
the sweep itself queued —
deleting a fact can release some other rule's block at derive time, where no block
ever existed to lift. The queue is read right after the sweep, so a rule the pass's own
re-chains queue is left to the next pass, which re-decides its firings against the queued
sentences; `lein perf`'s `released-refusal-beside-guarded-firings` bounds a retraction
whose released firing queues a rule beside that rule's firings.

A pass is **productive** when the blocked set moved. Three things force one that did not.
An **aggregate** antecedent binds a *value*, so a count going 1 ⇒ 2 licenses a firing no
block ever suppressed — and a **nested** NAF joins it there, since an arriving fact can
remove the witness its inner query found ([naf.md](naf.md)). An exception an arrival
can move both ways joins them too — an aggregate, or a literal under an odd number of
`unknown`s beside one under an even number, as in "a child not vaccinated": one arrival
imposes the block and a later one lifts it with no refusal to record it (`rules/exception-arrival-releasable?`). A released **refusal** — the next section — is a firing that never
held a justification for the blocked set to have said anything about. And a **revived**
datum is one whose firing was never attempted, because the join ran while it was OUT and
the matcher is belief filtered; that one is not an exception mechanism at all, and it is
[nmtms.md](nmtms.md#a-revived-datum-is-a-datum-the-agenda-has-not-seen)'s to explain.

**Nothing caches the exception's truth**, so nothing can drift from belief. The
index is a hint about what to re-check and never an answer — which is what
distinguishes it from the cached closures, which are answers and are therefore
belief-following ([taxonomy.md](taxonomy.md)).

### A refused firing is remembered as bindings

`place-conseq` does not place a firing a closed-extent negative antecedent or a
separation already rules out. Such a block has no defeat form: a closed extent blocks on
an absence, and the absence of a visible grant is not a sentex a defeat can rest on. Such
a firing leaves no justification, no node and nothing in `jtms/blocked`, so without a
record its conclusion would stay suppressed after the condition releases while the other
arrival order concludes ([nmtms.md](nmtms.md)'s order independence).

The refusal is therefore recorded, one level earlier and in the same shape. Where the blocked
set holds justification ids, `(reasoning/refused kb)` holds `{rule-handle -> #{refusal}}`, and a
refusal is the firing's conclusion, its placement context, its antecedent handles, the
bindings the condition was asked under, and the **depth bound the refusing run was
configured with** (so a release honours that bound, not the default, in a settle with no
run config in scope) — enough to re-ask the same level-6 question,
and enough to place the conclusion from when the answer moves. A release is then found
by **re-evaluating the record**: one query per recorded refusal, in place of a join over
the fact extent.

**Three of the five reasons are recorded**, and the other two are covered
elsewhere rather than forgotten. An `exceptWhen` exception or an `(unknown S)` antecedent
that holds is not among them: its firing is placed with a guard defeat, and the JTMS
withdraws the defeat when the blocker goes OUT.

| reason | recorded | why |
|---|---|---|
| a closed-extent negative antecedent blocks | yes | re-askable from the bindings alone |
| a `disjoint` antecedent the placement context does not read separated | yes | likewise, and the same evaluator |
| a post-join literal had no answer | no | an aggregate is a *value* that moved, and a queued aggregate rule is re-joined whatever the blocked set did (`settle/rejoin-on-arrival-rules`) |
| the settle blocks a placed firing, and the sweep deletes it | yes, by `chain/record-swept-firing!` | the conclusion is gone from the store, so the record is what a trigger lifting the block re-derives it from, as for a firing refused at its placement |
| a visibility `except` hides an antecedent | no | an `except` arriving or leaving, or a `genlCx` edge moving which contexts see it, re-joins from its target's consequence closure and the antecedents of the justifications resting on it (`special/drain-except-moves!`), and the refusal is re-derived there. An entry would be one nothing reads |

The record holds two more kinds of entry, neither of them a refusal by an exception. Each
is kept because later content can lift what refused it:

| entry | kept under | refused because | re-asked when |
|---|---|---|---|
| `:constraint` | the rule | `place-fact-conclusion` dropped the conclusion on an `arg` / `genlArg` / `interArg` / `interArgs` / `interArgAndRest` / `quotedArg` conviction: the argument holds a type the taxonomy separates from the declared one, or for `quotedArg` its kind has no path to it | a `genl` or `genlCx` generation or a separation (`tax/separation-inputs`) moved since the entry was decided, or a settle relabelled or removed a sentex naming the convicted term (`integrate/*removed-sink*`) |
| `:lift` | the source fact | a `decontextualized_predicate` copy from a context that does not see CxUniverse failed the same argument check there | the same two |

The generations an entry is decided under (`:read-under`) carry the taxonomy's rebuild epoch
(`special/taxonomy-generations`; `special/conviction-generations` adds the separations for
a `:constraint` or `:lift` entry). A `recover` restarts each generation at 0 and replays
the stored edges, so a generation can return to a number it held under another hierarchy.
The recover moves the epoch, so generations read before the recover never compare equal
after it.

`settle` re-asks them each pass (`released-constraint-refusals`, `released-lifts`). A
re-ask releases what the moved generations admit: a conclusion now admissible is placed
from the entry, a copy lifted, and what each creates goes on the agenda. A `:constraint` or `:lift` entry re-asked and still convicted is
re-recorded under the current generations and with the term the conviction names **now**
(`checks/conviction-watch`). An application can be convicted on more than one argument,
and the conviction names the first; once that argument is lifted it names the next, so an
entry that kept its first term would never be re-asked when the last one is lifted, and
the order the arguments were lifted in would decide whether the conclusion is placed.
Placed, a `:constraint` or `:lift` entry withdraws the ledger entry its drop filed
(`violations/withdraw!`), since the order that brought the type first filed none. A mint
withheld because the KB says it more specifically is the opposite case, a derivation
withheld for something the KB has, and it has no entry: the settle re-derives it when that
something leaves (docs/argtypes.md). A declaration whose type an arity statement binds to
another length has no entry either: the stored declaration is the record, and the settle
reads the declarations naming a type when that type's own bindings move
(`special/mints-on-lengths`, [argtypes.md](argtypes.md)). A write beside n such
declarations does not grow with n (perf checks `write-after-rolled-back-preview` and
`genl-write-beside-waiting-declarations`).

A pass finds the two kinds through the record's **kind index**: its `:kinds` key names,
per kind, the handles holding at least one entry of that kind, and every writer of such an
entry keeps it (`special/note-kind`, `drop-kinds`, `forget-kinds`). The pass reads only
those handles' sets (`special/kind-entries`), so the rules' own refusals, up to 4096 per
rule, are read only when a trigger queues their rule. The kind index sits in the record's own
map, so the batch rollback's snapshot, the reasoning image and a wipe carry it with the
entries. `lein perf`'s `assert-beside-naf-refusals` bounds an unrelated assert beside
32,000 `unknown` refusals.

`recover` rebuilds the `:lift` entries (`special/rebuild-pending!`); the `:constraint`
ones are not rebuilt, since that would mean re-firing every forward rule over the store,
so a KB restarted with a standing constraint drop re-derives it only when its rule next
fires.

Both unrecorded reasons are covered by a **re-join** rather than by nothing, and that is
what makes the record an efficiency structure rather than a completeness one. The same
holds past the cap below. The `except` row's re-join starts from the target's consequence
closure and the antecedents resting on it; a re-join from less than that turns the
table's last line into a real gap.

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
forward rule (enumerated `O(rules)` off the antecedent index, never the fact extent) and
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

That re-fire runs at the **default** depth bound, not the bound each original run set: a
run's `:max-depth` is session config no store holds, and `recover` resets derivation
depths to 0 as well. A KB chained under a smaller bound and then recovered can therefore
release a refusal whose re-derivation depth exceeded that bound.

**The record is capped at `chain/max-refusals-per-rule` = 4096 entries per rule.** The
blocked set is bounded by what a rule derived; the record holds one entry per refused
firing, so its size follows the rule's join rather than the store, and a rule refused on
a common condition can refuse far more than it places. On either side of the cap:

- **under the cap**, a queued rule's refusals are re-evaluated individually and a
  released one is re-derived from its bindings;
- **at the cap**, the rule's record collapses to `:overflow`, it keeps no entries, and a
  queued overflowed rule forces a productive pass and is **re-joined over its extent**
  instead, which finds the same releases.

An overflowed rule is still reached by every trigger, and the two edge triggers that
narrow on a rule's firings wave it through, as they wave an aggregate through: a rule
with no entries has nothing to test.

### Taxonomy changes are keyed on what the closure moved

An exception like `(flightless_bird ?b)` can flip because someone asserted
`(genl penguin flightless_bird)` — no fact with a matching predicate ever arrives, so
there is no *sentence* to narrow by and the queueing is `:all`. What is narrowed is
**which rules**, and the two edge kinds key it differently because their closures reach
an answer differently.

- A **`genl`** edge `[sub super]` moves reachability only along paths through it, so the
  spec closure of an exception predicate `pe` changes iff `pe` is `super` or above it, or
  above an `inverse` of such a predicate: the predicates a fact on `super` answers
  (`special/answered-predicates`, below) are the set queued on, plus the two functors a
  `genl` edge can flip without either endpoint appearing near the registered predicate —
  `genl` itself, whose conjunct the transitivity prover answers from the very closure
  that moved, and `disjoint`, which is closed under `genl` on both sides. Both are answered *across arguments*, so neither
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
  the one functor whose registration says nothing about its subject. Reading the
  conjunct costs one record fetch per rule carrying a negated condition, and a body it
  cannot read (a variable functor, a compound, a connective or quantifier frame such as
  `forall`) answers keep. Queued on the functor alone, such a rule would take one level-6
  query per firing on every `genl` edge in the KB.
- A **`genlCx`** edge `[sub super]` moves what contexts *see*, and an exception is
  evaluated in its conclusion's placement context — so an exception is affected iff one
  of its rule's firings is placed in `context-down(sub)`. Each excepted rule's firings
  are checked for one, a context lookup apiece and no query, and the same test is asked
  of the rule's **recorded refusals**, whose entries name the placement context the
  refused conclusion would have had.

  **A rule an arrival can release is waved through that narrowing**
  (`special/arrival-releasable-rule?`). An aggregate binds a **value**, so a census that
  rises licenses a firing that has no placed conclusion and no context to test; a
  **nested** NAF is the same one level in, since an arriving fact removes the witness the
  inner query found ([naf.md](naf.md), `forall`). The settle loop re-joins such a rule
  for the same reason.

  The test costs a record fetch and an exception read per excepted rule, then one context
  lookup per firing up to the first one in `context-down(sub)`, so a rule the edge reaches
  through no firing costs every firing it made.

Both run only while the `[:exception-index :rules]` set is non-empty, so a KB using no
`exceptWhen` pays one set read per edge.

### Five channels a declaration or a fact reaches an exception through sideways

The index's keying is *the exception's predicate and every supertype of it*, which is
sound for every level-6 prover that answers an exception from content on that predicate
(or a spec of it) — the fact fan-out, the transitive closures, the symmetric mirror. A
fact's trigger fans over `special/answered-predicates`: its predicate's supertypes across
`genl` and `genlInverse` edges, and those of every `inverse` partner of one, since
`(inverse childOf parentOf)` answers `(parentOf Ann Opus)` from `(childOf Opus Ann)`.
Five things do not, and each arrives with no predicate relationship to the exception
at all for the genls walk to follow. None of the five narrows by the moved sentence, as
the taxonomy path does not: what moved is about one predicate and the exception is about
another.

- **Argument preservation, from the relation's side.** `TransitiveInArgProver` answers by
  walking the arguments' reach, so `(genl chihuahua dog)` flips an exception on
  `typeLargerThan`. `special/recheck-preserving-along` and
  `special/recheck-separated-exceptions` queue the rules it reaches
  ([inherit.md](inherit.md#four-things-that-follow-from-reading-claims-out-of-belief)).
  From `P`'s own side the index already keys the fact, and the argument-agreement filter
  above waves `P` through.
- **`arg` read as an inference.** A believed `(motherOf X …)` beside
  `(arg motherOf 1 mammal)` makes `X` a `mammal` and every supertype of it
  (`ArgTypeProver`, [inference.md](inference.md)), so a fact on `motherOf` satisfies an
  exception on `mammal` with nothing on `mammal` ever written and no genl path between
  the two predicates. `special/recheck-arg-inferred` closes it, from both arrival
  orders — a fact of a declared predicate, and the declaration itself arriving over
  facts already stored.
- **A declaration, where no fact moved at all.** `(symmetric sibOf)` makes a stored
  `(sibOf Ann Bob)` answer `(sibOf Bob Ann)`, a commutativity mark does the same at any
  arity, `(transitive tangiblePartOf)` closes a chain, `(inverse childOf parentOf)` and
  `(negates likes dislikes)` answer a goal from the partner predicate's facts,
  `(reflexive P)` answers `(P a a)`, `(transitiveInArg P n R)` opens the inheritance over
  claims already stored, and `(asymmetric P)` gives a converse the standing to deny one.
  `special/recheck-declaration` reads the subject off argument 1 (both arguments for
  `inverse` and `negates`, argument 2 for `genlInverse`) and queues on the predicates a
  fact on the subject answers (`special/answered-predicates`), and the rules with a
  negated condition on the subject or a spec of it, which are posted under `not`; a
  `negates` side queues on the side and its specs, the keys of the denials it answers.
  `transitive` takes a second posting through `recheck-preserving-along`, because it is
  also the licence `inherit/usable-relation?` reads at use. `recheck-preserving-along`
  queues the negated conditions on each predicate declared along the relation that moved
  too, since a denial reached along it answers them.
  `special/declaration-subjects` names which declarations post here, and
  `predicates/check-facets` refuses at load a declaration that answers goals and posts
  by no route.
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
  block already swept, and the refusal record holds those only where no except hid an
  antecedent (`chain/record-swept-firing!`).

- **Composition, where a calculus answers the exception.** A registered calculus answers
  `(spatiallyDisconnected Canary Room)` from `(spatiallyDisconnected Cage Room)` and
  `(nonTangentialProperPart Canary Cage)`: the network reads one predicate to answer
  another, and neither fact names the canary and the room together. The genls walk from
  `nonTangentialProperPart` never reaches `spatiallyDisconnected`, and the `dc` fact's
  arguments agree with the firing's literal on nothing. `special/composed-exception-rules`
  closes it: a sentence that moves a calculus (`qkb/calculi-triggered-by`, which counts a
  sub-predicate's fact and a metric narrowing's source, [qcn.md](qcn.md#what-a-registered-prover-is-reachable-from))
  queues every rule with a block literal on a predicate the calculus claims or on a
  super-predicate of one, with the `::entailment` marker, which keeps every firing of such
  a rule and re-asks every refusal ("Two withdrawals a firing carries"). A `genl` edge
  under a calculus predicate queues the same rules `:all` from `recheck-genl-edge`, and a
  defeat queues them as the target's arrival does (`special/recheck-on-sentence`). A
  membership that moves which arguments a typed calculus predicate admits queues the
  rules whose exception mentions the predicate `:all`
  (`special/recheck-typed-admission`, [qcn.md](qcn.md#what-every-algebra-does-with-it)).

A KB not using a channel pays for it a cardinality check on the declaration extents, a
map lookup on the functor, and the `[:exception-index :rules]` emptiness check; the
composition channel tests the registered calculi against the arriving predicate's
supertypes. All five are read **globally** rather than per context, because a declaration
one context cannot see still qualifies a rule in one that can.

A firing's **stored bindings** are the part of the equality channel a trigger cannot fix.
A justification records what matched when it fired, and a merge does not edit it, so a
re-check substituting them asks about a term the KB no longer answers under. The
condition's own **written-in constants** can name a spelling the merge has retired, as
`(exceptWhen (mskip MOne) …)` names `MOne`. `provers/exception-holds?` puts each
substituted conjunct in its context's normal form before evaluating it, which settles both in one
walk, so the derive-time check and the re-check ask one question of one firing however
the merge is ordered against them. `chain/settled-bindings` rewrites the binding map itself, for the
conditions that read a binding rather than a goal: an aggregate's recount and an
inheritance re-check. Both scope to the conclusion's context, the scoping every other
read of the partition takes, since a merge the conclusion cannot see must not rename
what its own re-check asks about.

The general rule these five are instances of: **a re-check trigger is sound only for the
provers whose answer is addressed by the key it uses.** Keying on the exception's
predicate covers every prover that reads content *at* that predicate; a prover that
reads the arguments, or reads one predicate to answer another, needs its own channel or
belief depends on arrival order. When a new prover joins the registry, the question to
ask of it is which content can move its answer, and the answer to a doubt is to queue.

## Blocking and the TMS

`vaelii.impl.jtms` is pure and in-memory: it has no KB and cannot run a level-6 query, so
every condition is evaluated outside the TMS and the result handed in. An `exceptWhen`
exception or an `unknown` antecedent that holds is handed in as a guard `defeat` resting
on its blockers, an ordinary justification. A condition the rule carries
(`chain/rule-firing-blocked?`: a closed extent, an aggregate, a computed antecedent, a
`different`, a separation, an inheritance or an entailment withdrawal) and an `except` hiding an antecedent
(`chain/justification-excepted?`) are handed in as `:blocked`, a set of justification ids
`valid?` reads as invalid.

Belief and blocking are mutually dependent — a level-6 query reads believed facts, and
belief depends on which justifications are blocked — so `settle` iterates: relabel,
re-evaluate the conditions in the region, relabel again if the blocked set moved.
`jtms/set-blocked` **replaces** the blocked set, so the fixpoint test is set equality.
Stratification is what makes the loop terminate (below), and the loop is bounded at **16
passes** (`settle/max-settle-passes`) regardless.

`core/blocked-justifications` reads that set: the ids blocked as of the last settle. A
blocked justification's antecedents can all be IN, so belief alone does not report it. The
read answers the whole set, one read per rendered proof tree, and is served
(`:blocked-justifications`) to `vaelii.client` and the access facade, so an attached
browser draws the same pills as an in-process one.

## Garbage collection, not defeat

The two ways of handing a block to the TMS (above) store different things.

- **A guard defeat keeps the conclusion stored.** An `exceptWhen` exception or an
  `unknown` antecedent that holds, through `:default` or `:monotonic` blockers alike,
  places the firing and its `(defeat (sentexHandle F))` resting on the blockers, and the
  read walk decides belief per reader ([naf.md](naf.md)). Retracting the blocker takes the
  defeat OUT, and the conclusion is believed again under its own handle with nothing
  re-chained (`except_test/a-blocker-stores-the-conclusion-with-a-defeat-resting-on-it`).
  The store holds one firing and one defeat per firing a blocker blocks.
- **A blocked justification is garbage-collected.** A justification in the blocked set is
  invalid, and the dependency-directed sweep (`jtms/sweep!`, the retraction path) deletes
  its conclusion along with everything resting on it alone. A release re-derives the
  conclusion: from the refusal record where the sweep recorded the firing
  (`chain/record-swept-firing!`), and otherwise by re-chaining the released rules.

`retract!` settles inside `settle-after-teardown!`, so a conclusion a retraction releases
is believed by the time `retract!` returns. A rule queued only by sentences is not
re-chained over its extent (`settle/rechain-owed`): the settle releases each firing from
the refusal record. `lein perf`'s `except-of-a-guard-blocker` holds an except of a
blocker, and its retraction, flat in the rule's other firings.

## What surfaces where

Blocking produces no nogood: an excepted conclusion is stored under a guard defeat and
not believed, so nothing is contradictory and nothing is arbitrated. `conflicts` is
empty for it.

`conflicts` lists irreducible clashes among known-true content. A coexisting `P`/`¬P`
pair at `:default` is a represented dilemma, which an application ranks, and
`contradictions` lists each such pair with both handles and both justifications.

## Stratification

A rule whose exception depends on what another rule concludes, and vice versa, is a
cycle through negation. Level 6 cannot recurse through rules *at query time*, but an
exception can read a forward-derived stored fact, so a cycle across two rules remains
constructible even though the exception evaluator itself never expands a rule.
[why](defenses.md#a-cycle-through-negation-is-rejected-not-resolved)

So a rule set with a cycle through negation is **rejected at assert time**, as a
well-formedness check over the rule dependency graph alongside the `genl` cycle
check in [wff](../src/vaelii/impl/wff.clj).

### The graph

Two kinds of node — rules and predicates — and two kinds of edge:

```
rule R --depends-on--> P     P appears in R's antecedents        (positive)
rule R --excepts-on--> P     R's exception mentions P            (negative)
P --concluded-by--> rule R   R concludes P                       (positive)
```

A cycle crossing **at least one** negative edge is refused. A purely positive cycle
is ordinary recursion, which the engine supports and bounds by depth, and is
deliberately left alone — `stratification_test` asserts both directions, because a
check that rejected recursion would be worse than no check at all.

**Predicate dependence is not literal.** An antecedent `(animal ?x)` is satisfied by
a stored `(dog Muffet)`, and an exception on `flightless` by a stored `(penguin Opus)`
when `(genl penguin flightless)` — so both kinds of outgoing edge fan out over the
genl **spec** closure, which is the fan-out matching does and the one
`special/recheck-on-predicate` keys the exception trigger on, read in the same
direction. A cycle that exists only through a subtype is caught. Expanding the
*consuming* side downwards is equivalent to expanding the producing side upwards, and
the walk expands upwards: a type's ancestors are bounded by the hierarchy's depth, and
its descendants are most of a broad ontology. Where the two
readings differ, **over-approximate**: refusing a stratified program is annoying,
accepting an order-dependent one is a correctness hole.

### The search

`wff/negation-cycle` is a breadth-first walk from the rule being asserted, and looks
only for cycles **through that rule**: adding one rule can only close a cycle passing
through it. The walk runs against the graph's edges (`wff/negation-walk`): from a rule it
steps to every rule reading a predicate in the upward closure of the rule's consequent,
and closes on reaching the start again with a negative edge on the way. A cycle reversed
is a cycle, so this finds what a walk along the edges finds, and a step reads an upward
closure where a step along the edges reads every spec of each predicate a rule reads. A store written by the import path, which skips the rule checks that read the KB,
can hold a cycle already; a walk finds it only when the rule or edge being added is on
it. The search state is the consequent and a `negative?` flag: two rules concluding one
predicate have the same edges into them, and a node reached with and without a negative
edge behind it are different states, since only the negative one closes a bad cycle —
which is exactly what lets positive recursion reach the start node, find the flag false,
and stop. A rule concluding `(?p …)` concludes every predicate, so every rule reads it.

The rule being asserted **is not stored yet**, so `checks/stratification-readers` adds it
to the graph by hand under each predicate it reads. Without that, a rule whose exception
mentions what it concludes — a one-rule cycle, and the easiest one to write by accident —
would look stratified. Everything else is reached through the rule index: a predicate's
readers are the rules posted under it in the antecedent index (every `[:not f]` key for
`not`) and in the re-check index, plus the `different` readers for an equality relation
and the `[:not P]` readers for a closed extent, each kept when its node reads the
predicate. Nothing scans, except that a rule concluding `(?p …)` reads every stored rule
when the walk reaches it.

A check builds each stored rule's node once. `checks/stratification-readers` returns a fn
that memoizes the readers per predicate and the node per rule handle, and an edge's walk
starts are memoized per upward closure. An `assert` and a `settle` bind
`rules/*stratification-memo*`, so every check of the write or the pass reads one stored
graph: a pass minting many `genl` edges reads each rule's node once, not once per mint
(`lein perf`'s `edge-stratification-mints-in-one-pass`). A write to the rule index or the
re-check index empties the memo, as does a rule's engines moving, and a check compares the rest of what the graph read
before it reuses it: the closed-extent marks by identity, and the belief of each
exceptWhen meta-sentex a node read. Without the binding, each check builds its own graph
and drops it when it returns. The walk expands
each predicate's readers once per flag and pushes each state once, so it costs the rules
it reaches and the upward closures of their consequents, not the spec closures of what
they read. `lein perf`'s `edge-stratification-walk` holds the shape: a `genl` edge's check
over a chain of eight rules, each reading a type with n specs, reads under 2x at 16x the
specs.

The check runs **before anything is written**, so a refused rule leaves no partial
state: no sentex, no justification, and no posting in the rule or exception indexes. It
throws `ex-info` with `:type :not-stratified` and a `:cycle` naming the nodes and
edges around the loop, in the graph's direction. Where several cycles pass through the
start, the walk takes each upward closure and each predicate's readers in content order,
so the cycle named is the same in every arrival order
(`stratification_test/two-cycles-through-one-rule-name-the-same-cycle-in-either-arrival-order`).
A stored rule's node is labelled `rule#<handle>`, so the label's number is not.

**Fast path:** with no negative dependency on the rule being added — no exception, no
`unknown`, no aggregate, no closed-extent negative and no `different` — and no exception
on any stored rule, the graph has no negative edge at all and the walk is skipped. That
is every rule in an ontology that uses none of them, which is most of them. The second
half of the guard is the KB's whole exception index, so **one** exception anywhere ends
the fast path for everything asserted after it: the bundled starter takes it until
`CxBiology`'s `dead` exception loads, and pays the walk from there on.

### A taxonomy edge closes a cycle too

Both kinds of outgoing edge fan out over the genl spec closure, so a rule is not the
only thing that can close a cycle: an exception on `flightless` reaches a rule
concluding `penguin` the moment `(genl penguin flightless)` holds, and it does not
matter which of the three arrived last. Walking on rule assert alone would accept an
unstratified program silently whenever the **edge** is the newcomer.

So the walk runs on `genl` assert as well, once per edge, from the edge
(`wff/genl-negation-cycle`, called by `checks/edge-negation-cycle`):

- `(genl a b)` puts every spec of `a` into the spec closure of every predicate at or
  above `b`. The graph edges it adds therefore run from each rule reading a predicate
  at or above `b` to each rule concluding a spec of `a`, and a cycle the edge closes uses
  one of them.
- The walk starts at the rules reading a predicate at or above `b`, in content order, and
  goes against the edges to a rule concluding a spec of `a`, which closes the cycle when
  the path or the edge from the start is negative. It reads only the rules those starts
  reach, so its cost does not grow with the excepted rules the edge does not reach
  (`lein perf`'s `edge-stratification-unreached`: 16x the excepted rules, under 2x). A
  cycle already stored, which the import path can write, refuses only an edge on it.
- The edge is added to a **detached copy** of the taxonomy, so the question is asked
  of the graph-as-it-would-be without the real closures learning anything.
- Only *additions* need checking. `specs` grows monotonically with the edge set, so
  removing an edge only removes graph edges; a retraction can never close a cycle.
- Only an addition that moves the closure needs checking. When `b` is already in `a`'s
  unscoped `genl` closure, the edge adds no graph edge, and the check stops at that one
  reachability test before any rule-key read. A re-derived argument-type mint that a stored
  edge subsumes is this case (`lein perf`'s `edge-stratification-subsumed`: 16x the
  excepted rules reading `b`, under 2x).
- Only an addition with a rule concluding a spec of `a` needs checking. Every graph edge
  the edge adds ends at such a rule, so with none, and no rule concluding `(?p …)`, the
  edge adds no graph edge. The check reads the consequent index under each term of `a`'s
  unscoped spec closure, which the edge does not move, and stops before it reads a rule
  above `b`. A spec closure holding more terms than the store holds rules skips this test
  and walks. An edge between two types of a generated vocabulary, which no rule
  concludes, is this case (`lein perf`'s `edge-stratification-unconcluded`: 16x the rules
  reading `b`, under 2x).

`stratification_edge_test` compares the walk with the probe's whole graph, built along
the edges over the spec closures, on the reference generator's random worlds: the same
verdict on every candidate edge, a cycle through the edge, and the same cycle content in
two arrival orders.

**The edge is refused.** The `genl` assert is the operation at fault, so refusing it
is the consistent answer: it is what `wff` already does to an edge that would make
the taxonomy cyclic, and it keeps the invariant that stored state is *always*
stratified — which is what lets the rule-side walk look only for cycles through the
rule being added. As on the rule path, the check runs before anything is written and
before the taxonomy is touched, so a refusal leaves no sentex, no justification, and no
closure that learned the edge.

**Fast path, again:** no stored rule carries a negative edge
(`checks/negative-edge-rules`), so the graph has none and nothing is walked. An
ordinary `genl` assert pays two set reads and stops — which is every `genl` assert in
the bundled starter. `stratification_edge_test` asserts that by *counting* the walks
rather than timing them.

A `genlCx` edge is not walked. The dependency graph is over **predicates**, and its
edges read the `genl` closure alone, so a `genlCx` edge adds no graph edge.

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

With stratified negation the **settled** state is unique and order-independent, and
the intermediate states during a load are not: a rule may fire and then have its
exception arrive and defeat the conclusion. Only the fixpoint is guaranteed.

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
exception restores it. `handle-of` on the `exceptWhen` sentence answers the meta-sentex's
handle, the one `assert` returns, so `retract!` on it removes the exception and leaves the
rule (`public_api_test/handle-of-an-exceptWhen-answers-the-exception-assert-returned`). A
rule can carry several independent exceptions (block-if-any).
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
same meta-sentex. The conjunctions and binders inside a conjunct are ordered as a rule's
`unknown` antecedent's are, except that a deferred literal keeps its written place after
the generators ([canonicalization.md](canonicalization.md#a-naf-conjunctions-conjuncts-sorted)).

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
on the wrapped form before the bare rule is stored): a free variable no antecedent binds
has no canonical number to align to. It throws `ex-info` with `:type :exception-not-closed`.
The anonymous wildcard `_` is refused for the same reason range restriction refuses it —
two occurrences are two different variables, so no antecedent can ever bind one.

**Degenerate wrappers.** `exceptWhen` around a non-rule is refused `:not-well-formed` by
`assert` and reported so by `check`: an exception blocks what a rule concludes, and a fact
concludes nothing. Two `exceptWhen`s written together conjoin into one meta-sentex
(block-if-all); two asserted separately are independent exceptions (block-if-any).

## The parts

- **Evaluation.** `provers/exception-holds?` substitutes the firing's bindings into a
  conjunction from `provers/rule-exceptions`, puts each conjunct in the normal form its
  context answers under (`condition-normalizer`, so a term an equality merge has retired
  is asked under its representative), and runs the conjuncts through
  `provers/conjunction-solutions` over the level-6 registry, which expands no rule.
  `exceptions-block?` ORs this over a rule's exceptions.
- **Blocking, in every chainer.** Forward chaining checks before placing
  (`derive-conclusion`); `res/prove` carries a `:guard` on the parsed rule and the node
  engine a `:guards` list, each dropping the argument once it is complete, so
  `sentexes-matching` and `ask` agree about one rule. `prove` pushes a rule's antecedents,
  so its guard rides the goal stack as a marker behind them.
- **Triggers.** A fact arriving or leaving queues the rules whose exception mentions its
  predicate or any supertype of it; a `genl`/`genlCx` edge change queues the rules its
  closure reaches; a declaration queues the rules whose exception mentions its subject.
- **Narrowing.** `recheck/exception-candidates` filters the firings from memory before
  any query runs, and the re-chain after a productive pass is seeded from what the pass
  released plus the rules queued with no sentence to read.
- **The refusal record.** `(reasoning/refused kb)` holds the firings refused before they
  became justifications; `recheck/released-refusals` re-evaluates the queued rules'
  entries, and `chain/release-refusal!` re-derives the ones that no longer block.
- **Guard defeats.** `chain/place-guard-defeats!` places the `defeat` of a firing an
  exception or an `unknown` antecedent blocks
  ([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)).
- **Sweeping.** `jtms/sweep!` is `retract!`'s sweep without the retraction, and `settle`
  runs it over the conclusions of the newly blocked justifications.
- **`why-not`** takes a `(kb sentence context)` arity and answers `:excepted`; a
  conclusion stored with a guard defeat answers `:excepted` through the handle arity too
  (`except_test`).
- **Stratification.** `wff/negation-cycle` on every rule assert and
  `wff/genl-negation-cycle` on every `genl` assert refuse a cycle through negation before
  anything is stored; a derived edge that closes one is dropped and reported in
  `violations`. `stratification_test` and `stratification_edge_test` cover both.

### The fixpoint question, measured

`settle` keeps the bounded fixpoint loop, and stratification stays a correctness check
rather than an evaluation order: `core/settle-stats`' `:iterations` count the passes in
which the blocked set moved, and on a chain of up to eight exceptions the count never
exceeds one ([measured](defenses.md#the-settle-loop-is-bounded-not-ordered-by-strata)).

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
