# Negation as failure: `unknown`, `thereExists` and `forall`

- **Covers:** closed-world negation as a query operator — `unknown`/`thereExists`/`forall`,
  ground/closed evaluation, and how a rule antecedent stays maintained as belief changes.
- **Not here:** the rule-level exception this reuses block/sweep/revive from →
  [exceptions.md](exceptions.md); aggregation, the third member of the same family →
  [aggregate.md](aggregate.md).
- **Assumes:** belief, justification, prover, `genl` → [glossary.md](glossary.md).

Closed-world negation as a query operator, and the existential that closes a
variable off so it can be negated. Neither is ever stored.

## The two operators

```clojure
(unknown S)          ; holds iff S is not derivable — closed-world negation
(thereExists ?x S)   ; holds iff some binding of ?x makes S derivable
(thereExists [?x ?y] S)
(forall ?y (implies Body Head))   ; sugar: the nested NAF below
```

`unknown` is negation as failure: `(unknown (flies Tweety))` holds exactly while the
KB cannot derive `(flies Tweety)`. `thereExists` existentially quantifies its
variable (or vector of variables) and **projects it out** — it produces no binding,
it is a test. Its point is to *close a variable off* so `unknown` can negate an
existential:

```clojure
(unknown (thereExists ?c (parentOf ?c Tom)))   ; "Tom has no known parent"
```

All three are answered by a prover (`vaelii.impl.provers` — `UnknownProver`,
`ThereExistsProver`, `ForallProver`), usable as a top-level goal (`ask` / `ask?`) and as
a rule antecedent. None is assertible: a `wff` arm refuses `(unknown …)` /
`(thereExists …)` / `(forall …)` as a stored fact, the way `different` is refused — a
query operator states no fact.

## Fully bound to evaluate

`unknown` and `thereExists` are **ground/closed only**. Applicability refuses a goal
with a free variable — `sentex/free-vars`, which counts every variable *except* the
ones a quantifier binds: a nested `thereExists`'s, a `forall`'s, and an aggregate's own
`?v` and `?n`:

| form | `free-vars` |
|------|-------------|
| `(parentOf ?x ?y)` | `{?x ?y}` |
| `(unknown (flies ?x))` | `{?x}` (unknown is transparent) |
| `(thereExists ?x (parentOf ?x ?y))` | `{?y}` (the binder subtracts `?x`) |
| `(unknown (thereExists ?x (parentOf ?x ?y)))` | `{?y}` |
| `(unknown (thereExists ?x (parentOf ?x Tom)))` | `{}` — closed |

An open `(unknown (flies ?x))` is not a test but a search over the whole domain's
*complement* — every `x` that does not fly — so the prover **refuses** it rather than
answering explosively, exactly the honest refusal `different` makes. In a rule, the
free variables must be bound before the `unknown` runs (closure, below) — by a
*generator* antecedent, or by one of the deferred literals that **writes** rather than
only reads: an aggregate's `?n`, an `evaluate`'s output. A `thereExists`'s own variable
never has to be — that is what it is for.

`check-naf-closed` holds every consuming literal to that rule, not only `unknown`: a
`(lessThan ?m 35)` whose `?m` nothing in the rule writes is refused at assert time
too. A bare *goal* nothing binds still answers empty, and the difference is the point
— a goal is asked and gone, while a rule is stored and re-run, so an unbindable input
would silently find nothing backward and throw mid-fixpoint forward, after the rule
was already stored.

## Evaluated over the registry

The argument runs through the **registry** — level 6 of the lookup stack, the *same*
list `exceptWhen` uses. This is a deliberate choice, and it is the same one
[exceptions.md](exceptions.md) makes: closed-world reasoning must read what the KB
**derives without an unbounded proof search**. So a forward-derived fact counts — it is
stored and believed by the time the query runs — while something reachable only by
backward chaining does not. The registry reaches genl specificity, the genlCx
visibility closure, the transitive/symmetric/inverse metadata, disjointness and the
evaluables, and no member of it expands a rule — so nothing here can start a proof
search from inside a relabel loop.

`(unknown S)` is answered by running `S` at level 6 and inverting: **no** solution
means `S` is not derivable, so `(unknown S)` holds. `(thereExists ?x S)` is answered
by running `S` at level 6 and reporting existence, binding nothing outside. A
conjunctive `S` is **joined** across its conjuncts ("The conjunction is joined", below)
— the registry answers one goal at a time, and the join is the thin thread of bindings
over it that a quantified conjunction needs and nothing else does.

## In a rule antecedent

`(unknown S)` in a rule body is `exceptWhen` **inlined per-literal**: the rule does
not conclude for a binding under which `S` is derivable.

```clojure
(set/forwardRule (implies (and (bird ?x) (unknown (flies ?x))) (walks ?x)))
;; birds walk, unless they are known to fly
```

It shares `exceptWhen`'s whole machinery — evaluation point, re-check index, block /
sweep / revive — differing only in **polarity and combination**:

- an `exceptWhen` exception is one condition, block-if-**all**-conjuncts-hold;
- each `(unknown S)` antecedent is an **independent** condition, block-if-**any**-holds
  — one derivable `S` withdraws the conclusion.

The two block conditions are OR'd wherever a firing's block status is decided.

### `S` may be a conjunction

```clojure
(implies (and (bird ?x) (unknown (and (flies ?x) (adult ?x)))) (walks ?x))
;; birds walk, unless they are known to be adults that fly
```

The exception's conjunction, inlined per literal — and read the same way, since the
same evaluator answers both (`provers/exception-holds?`): the conjunction is derivable
only if **every** conjunct is, so one conjunct short leaves `(unknown S)` holding and
the rule fires. Closure makes this one cheap: every variable is bound before the query
runs, so after substitution the conjuncts share nothing and each is an independent
ground existence check. The join below runs it, of which a ground conjunction is
the degenerate case — one evaluator, and no second reading of `and` to drift from it.

The same argument refuses a **disjunctive** body. `(unknown (or A B))` would need the
evaluator to union two runs and nothing at level 6 does, so the disjunction would decide
the rule without being evaluated — the one way a guard passes everything silently. Nor is
the rule expanded on it, since `(unknown (or A B))` reads as "neither A nor B is
derivable", which is the De Morgan *opposite* of what one rule per alternative would
mean. Write the two `unknown` literals as two antecedents; that is the conjunction the
form already meant.

Conjunct order is **not** the rule's identity — the conjuncts are sorted (blind to
variable names) in the constructor, so two spellings of one condition are one rule, the
claim `sort-conjuncts` makes for an exception. Nesting is not either: `(and A (and B
C))` flattens, because conjunction is associative and a nested `and` is a goal no prover
claims — left as one conjunct it would come back unanswerable, read as *not derivable*,
and the whole query would never hold. A lone conjunct loses the `and` it never needed,
and a repeated one is dropped.

A conjunct may itself be a `thereExists`: the binder is local to that one conjunct, so
the *outer* conjuncts still share nothing, and the predicate watched is the one *inside*
the quantifier — recursively, so a conjunction under the quantifier is watched conjunct
by conjunct too.

Every conjunct's predicate is posted in the re-check index, not just the first: a
conjunction blocks on the *last* of its conjuncts to arrive, so a rule watching one of
them would miss the arrival that completes the query. The predicate posted is the one
the conjunct *reads* (`rules/watched-predicates`, shared with the exception's own
registration) — an aggregate conjunct is watched by its census body, an existential one
by what it quantifies. A negated conjunct is watched under `not`, which is also how the
trigger side keys an arriving `(not S)`.

### The conjunction is joined, so its conjuncts may share a witness

```clojure
(unknown (thereExists ?c (and (childOf Tom ?c) (sick ?c))))   ; "Tom has no sick child"
```

The conjuncts here share the binder, so reading them independently would take each from
a *different* witness — "has a sick child" would hold of anyone with a child while
anyone at all was sick. That reading is wrong, and it is the one
[defenses.md](defenses.md#a-conjunction-under-a-quantifier-is-joined-never-read-flat)
refused. A **join** answers it correctly, and that is what
`provers/conjunction-solutions` is: each conjunct is substituted with what the conjuncts
before it bound, run through the registry, and its solutions thread on. One evaluator,
used by `unknown`, by `thereExists` and by an `exceptWhen` alike.

A **ground** conjunction is the degenerate case of it and is unchanged: every conjunct
substitutes to a ground goal, each contributes one solution or none, and the join *is*
the independent existence check it always was. Nothing about the flat reading was wrong
where closure made it ground — what changed is that closure is no longer the only way to
be answerable.

The conjuncts are run in a **planned** order (`planned-conjuncts`), generators first and
each computed conjunct — a nested `unknown`, an evaluable, an aggregate — once the
variables it reads are bound. Canonical order sorts a query's conjuncts blind to
variable names, so the written order is not available to rely on; the plan is recomputed
at evaluation, the decision `plan/order` makes for a rule body, in the small.

Two things are refused, and both are refused at assert time:

- A **quantified variable no generator conjunct of the same query binds**
  (`:naf-not-closed`) — `(unknown (thereExists ?c (and (childOf Tom Tom) (unknown (sick
  ?c)))))`. Nothing outside can bind `?c`; that is what the quantifier is for. So the
  computed conjunct can never run, and the query would answer *not derivable* whatever
  the KB holds.
- An **empty** conjunction (`:type :not-well-formed`): nothing can make it derivable, so
  the antecedent would guard nothing.

**An aggregate's census body is joined by the same evaluator.**
`provers/aggregate-values` runs it through `conjunction-solutions`, so
`(agg/count ?n ?c (and (childOf Bob ?c) (asleep ?c)))` counts the children who are
asleep — one witness satisfying both conjuncts, and the reduction reads `?v` off it. The
two refusals above have their aggregate spelling: a census variable no conjunct of the
body binds and nothing outside the aggregate names is `:naf-not-closed`, and a
disjunctive body stays refused for a reason no join repairs
([aggregate.md](aggregate.md)).

A **standalone positive** `(thereExists ?y (and …))` antecedent needs none of this. Its
conjunction is spliced in as that many antecedents (`desugar-there-exists`), which is the
join a reader would have written by hand: the binder is shared by the conjuncts and by
nothing else, and antecedents sharing a variable are exactly a join.

### `forall` is sugar for a nested `unknown`

```clojure
(implies (and (person ?x)
              (forall ?y (implies (childOf ?x ?y) (asleep ?y))))
         (all_kids_asleep ?x))
;; "all of ?x's children are asleep"
```

∀?y (Body ⇒ Head) is ¬∃?y (Body ∧ ¬Head), and in a closed world ¬ is `unknown`. So the
universal is two negations around the existential the engine already answers, and that
is exactly what it canonicalizes into (`sentex/desugar-forall-literal`):

```clojure
(unknown (thereExists ?y (and (childOf ?x ?y) (unknown (asleep ?y)))))
```

The desugar runs at the **entry point** — the sentex constructor, and `rules/inner-rule`, which
every pre-storage check reads through. So range restriction, closure, quantifier
locality and the stratification graph all see the nested NAF, `canonical-sentex` shows
it, and the sugared rule and the hand-written nested one are **one rule with one
handle**. A conjunctive `Body` contributes that many conjuncts to the join; a `Head` is
left whole, so an `(and …)` head is one nested `unknown` over a conjunction.

Nothing new evaluates it. The inner `unknown` is a conjunct of the outer query like any
other, reached once the generators of that query have bound `?y` — which is why the join
plans its conjuncts rather than running them as written. **NAF nests exactly as far as it
stratifies**: the inner query's predicates are negative edges too
(`rules/naf-predicates-of` reads through the quantifier and through the nested
`unknown`), so a cycle through either half is refused at assert time as any other cycle
through negation is.

Closedness is the same rule read twice: `?y` is local to the `forall` — it may appear
nowhere else in the rule (`:quantifier-not-local`) — and every *other* variable in the
body is bound by an antecedent outside it (`:naf-not-closed`).

**The vacuous case reads true**, and deliberately: Bob having no children at all makes
the existential unsatisfiable, so the `unknown` holds and "all of Bob's children are
asleep" is true. That is the classical reading of a universal over an empty domain, and
it is what falls out of the desugar rather than a case decided separately.

A `forall` an arriving fact can **release** directly is the one place the maintenance
differs from a plain `unknown`. `(unknown S)` is antitone in what a fact states: an
arriving `S` can only make `S` derivable, so it can only block, and the one arrival that
releases it does so through a defeat of a believed `S`, which the settle handles (below).
A nested one is not antitone — an arriving `(asleep Kid3)` removes the witness the inner
query had found — so the rule is owed a fresh join whether or not the blocked set moved,
exactly as an aggregate is (`rules/arrival-releasable?`, `settle/rejoin-on-arrival-rules`,
and the same exemption at the two taxonomy edge triggers).

### Evaluated in the placement context, not the join

An `unknown` antecedent is **not** a join filter. Forward chaining *skips* it in the
join (it binds nothing and names no fact) and checks it at **derive time, per
placement context** — precisely where `exceptWhen` is checked, and for the same
reason: forward and backward must evaluate a NAF condition in the *same* context, or
`sentexes-matching` and a backward search would disagree about one rule. Backward
solves it as a deferred antecedent through the prover at the query's context, which
is the backward analogue of the placement context. Both read the identical level-6
judgement (`chain/unknown-inner-holds?` → `provers/exception-holds?` over the query's
conjuncts), so the two can never drift.

### Standalone positive `thereExists` desugars

A *standalone* positive `(thereExists ?y S)` antecedent — one **not** wrapped in
`unknown` — is **desugared to `S`** in the `sentex` constructor, with `?y` a fresh
local variable. A standalone existential is exactly `S` with a variable that the
match binds and that (by locality) reaches nothing else, so `S` alone is the
faithful native reading: it joins the store like any generator, one witness per
solution, and needs no special matcher. A person-with-a-child is a parent:

```clojure
(implies (and (person ?x) (thereExists ?y (parentOf ?x ?y))) (a_parent ?x))
;; stored as (implies (and (person ?x) (parentOf ?x ?y)) (a_parent ?x))
```

A `thereExists` **inside** `unknown` is a NAF query, evaluated by the prover, and is
left intact. So `thereExists` is deliberately *absent* from `deferred-predicates`;
only `unknown` is deferred.

## A closed extent: `(not (P a))` without a stored negative

`unknown` chooses closure **per goal** — the author writes it where they want it. A
`closed_extent_predicate` grant chooses it **per predicate**, for everything read under it:

```clojure
(v/assert kb '(closed_extent_predicate month_of_year) 'CxCalendar)
;; "the months of the year are exactly these twelve"
```

Where the grant is visible, `month_of_year`'s **believed** extent is complete, so nothing
answering `(month_of_year Smarch)` at level 6 is what answers `(not (month_of_year Smarch))`.
`ClosedExtentProver` does that: a ground negative goal, the positive run through the
registry, and the negative held exactly while the positive finds nothing. Cost tier
`:compute`, nothing stored — a closed extent creates no negative space, the same refusal
`exceptWhen` and `unknown` make.

It is a **grant**, and the only thing that closes an extent: an undeclared predicate stays
open-world, where a fact nobody stated is not thereby false. And it is a **policy of the
context that gives it**, read from the asking context's `genlCx` ancestor set the way
`abducible_predicate` is ([abduction.md](abduction.md)) rather than universally — one
theory may state the twelve months and read a thirteenth as refuted while a sibling,
reading the same predicate, answers only what it was told. It is belief-following like the
other predicate marks: a defeated or retracted member leaves the extent, and the closure
follows.

### Under the grant, a negative antecedent is NAF

```clojure
(implies (and (candidate_month ?m) (not (month_of_year ?m))) (not_a_month ?m))
```

Without the grant that `(not (month_of_year ?m))` is an ordinary literal, satisfied by a
stored negative. Under it the literal is negation as failure, and it takes `unknown`'s
whole path: **withheld from the join** (`planned-join`, beside the post-join literals),
decided at **derive time in the placement context** (`chain/closed-extent-blocks?`),
recorded in the refusal record under the `:naf` reason, and swept and revived by the
ordinary block / sweep / revive.

Three details make that sound:

- **Only a *closed* negative antecedent** is read this way
  (`rules/closed-negative-antecedents`) — one every variable of which another generator
  antecedent binds. A negative antecedent whose variable nothing else binds is what
  *produces* that binding by matching a stored negative, and withholding it would leave
  the rule with nothing to fire on.
- **The question asked at derive time is the whole level-6 one**, not "is there a positive
  answer". So a stored `(not (P a))` answers it as it always did, and a placement context
  that cannot see the grant reads the literal exactly as it does today. The join is
  withheld unconditionally once the predicate is granted **anywhere** — over-selecting,
  which derive time then decides correctly per context.
- **What the withholding costs is the support handle**, and the re-check index gives it
  back. The rule is posted under `P` (`rules/closed-extent-predicates-of`), and
  `recheck-on-sentence` posts an arriving sentence under its own functor *and* its
  underlying body's — so one key catches a `(P a)` arriving and a `(not (P a))` leaving
  alike, and the firing comes round for re-decision either way.

A grant asserted **after** the rules it governs reaches them too:
`special/index-closed-extent-rules` posts every stored rule with a `[:not P]` antecedent
and queues it `:all-rejoin`, because the grant blocked nothing for the blocked set to
notice and the firings it licenses have no justification yet — the same asymmetry a
widened `genlCx` ancestor set takes that marker for.

### Stratification, from both arrival orders

A closed-extent negative antecedent is a **negative edge** on `P`, so a rule concluding
`P` whose body reads `(not (P …))` under the grant is a cycle through negation and is
refused (`:type :not-stratified`). The edge is conditional on the grant, so the *grant* can
close a cycle too — `checks/check-closed-extent-stratified` walks from each stored rule
with a `[:not P]` antecedent (one antecedent-index lookup, no scan) and **refuses the
declaration**, which is the same answer `check-edge-stratified` gives a `genl` edge that
closes one, and for the same reason: stored state is always stratified.

`why-not` reports `:closed-extent` for a positive goal nothing answers under a visible
grant. That is the more specific answer than `:not-stored`: the KB is not silent about the
sentence, it says the extent is complete and this is not in it.

**`defns` and `disjoint` are untouched.** A `defnIff` states a condition, not an extent —
a thing whose condition is merely unknown is concluded neither a member nor a non-member
([defns.md](defns.md)) — and disjointness refutes from a *positive* claim about a sibling
type. Both stay open-world by design; this grant is the one place a KB says otherwise, and
it says it per predicate and per context.

## Order independence, and the re-check

Belief must not depend on arrival order. A conclusion drawn while `S` was absent must
be **withdrawn** when a later fact makes `S` derivable, and **revived** when that fact
leaves. This is the `exceptWhen` block/sweep/revive path, reused verbatim:

- The rule is posted in the re-check index (`[:exception-index <predicate>]`) under every
  predicate its `unknown` antecedents mention — `rules/recheck-predicates` unions the
  NAF antecedents' predicates with the aggregate bodies'. An exception's predicates ride
  its own meta-sentex into the same index (`special/index-exceptWhen-meta`), so both
  kinds of block condition key one index. A fact arriving or leaving on one
  of those predicates (or any subtype, via the genl spec fan-out) queues the rule.
- An **equality** queues it too, and that one no predicate can key. `(unknown (flies
  Tweety))` is answered under Tweety's representative, so merging Tweety with a Birdy
  that flies makes the inner query derivable with nothing on `flies` having moved at
  all — and the firing's own stored binding is now a spelling the KB does not answer
  under. `special/recheck-equality-edge` is the trigger, and the inner query is put in
  its context's normal form before it is evaluated (`provers/condition-normalizer`), so
  the binding and any constant the antecedent was written with are both asked under the
  representative. This is the direction where the wrong answer is **unsound** rather
  than merely unguarded: an `unknown` reporting a term absent when the KB answers it
  under another spelling draws a conclusion, where a silently-false exception only fails
  to withdraw one. [exceptions.md](exceptions.md) has the shape, which `unknown`
  inherits along with the rest of the machinery.
- At the next `settle`, the queued firings are re-evaluated; a firing whose `S` is now
  derivable is **blocked**, and the ordinary dependency-directed sweep **deletes** the
  conclusion and everything resting on it — *garbage collection, not defeat*, exactly
  as for an exception ([exceptions.md](exceptions.md), "Garbage collection, not
  defeat").
- `retract!` captures the rules whose NAF condition a retraction *released* and
  re-chains them, so a revival — which is a re-derivation, not a flipped bit — is
  visible by the time it returns.
- A **defeat** releases too, with nothing stored or removed: a monotonic `(not (happy
  Zed))` arriving after a firing was blocked and swept defeats the default `(happy Zed)`,
  so `(unknown (happy Zed))` holds again. The swept firing left no blocked justification
  and no refusal record to re-ask, so the settle pass that newly defeats a datum re-chains
  every rule watching its predicate (`settle/released-by-defeat`, keyed as
  `special/rules-watching` keys an arrival). A defeat the previous settle already applied
  re-chains nothing.

The settle-time firing filter (`firing-reachable?`) shapes the exception's conjuncts
and the `unknown` antecedents' inner queries the same way: a ground inner narrows
against the trigger, an existential one (`(thereExists ?x …)`, never ground) falls
through to "keep", which is the safe over-approximation. Both sides of that comparison
are read under the equality-class representative, so a firing bound to a retired
spelling narrows against a trigger spelled under the representative rather than being
dropped as unrelated ([exceptions.md](exceptions.md), "The re-check index").

## Stratification

Negation as failure needs a stratified rule set. An `(unknown S)` antecedent is a
**negative** dependency on `S`'s predicate (fanned over the genl spec closure), joined
to the same dependency graph as `exceptWhen` and `different`
([exceptions.md](exceptions.md), "Stratification"). A rule set with a cycle through
negation — one rule's `unknown` depends on what another concludes and back — is
**refused at assert time** (`:type :not-stratified`), including the one-rule cycle (an
`unknown` on what the rule concludes) and a cycle a `genl` edge would close. Ordinary
positive recursion is untouched.

## The out-list decision — why nothing is stored

Doyle's JTMS gives a justification an **out-list** — a negation-as-failure antecedent
set: a justification is invalid if any of its out-list datums is IN. It is the textbook
home for `unknown`. A Vaelii `Justification` has **no out-list** ([nmtms.md](nmtms.md)),
and NAF is maintained by **re-evaluation** instead. The reasons are the ones
[exceptions.md](exceptions.md) already gives for `exceptWhen`, plus one that is
decisive:

- **An existential NAF has no handle.** `(unknown (thereExists ?x (parentOf ?x Tom)))`
  is negation over a *pattern*, not a proposition. There is no single node whose
  OUT-ness stands for "nobody is a parent of Tom", so an out-list — a set of handles —
  cannot represent it. The moment `thereExists` enters, the out-list is the wrong shape.
- **An out-list stores the negative space.** Using one for the ground case
  `(unknown (flies Tweety))` when `(flies Tweety)` is not stored means *materializing*
  an unbelieved node for it — a probe for every proposition that happens not to hold.
  Over a large domain that is the negative space `exceptWhen` refused to store.
- **An out-list cannot compose with computed truth.** A level-6 answer reached through
  transitivity, disjointness or arithmetic has no single node to mark OUT either.

So: **we do not track things that are known-false-but-not-in-the-KB as negated
facts.** Nothing about a NAF condition is stored; it is re-evaluated on the same
triggers an exception uses. This keeps NAF consistent with the codebase's existing
closed-world mechanism (`exceptWhen`) and the store free of negative space.

**A dump cannot add one.** A justification frame in a dump is a field map, so a frame
can carry an `:out` key, and `vaelii.impl.io.import` refuses a non-empty one
(`:naf-justification`): imported without its out-list, the justification would support
its conclusion where the exporting KB's did not. Two relabel invariants depend on the
absence: `region-fixpoint`'s semi-naive warrant is that `valid?` is monotone in the IN
set, which a justification an arriving datum *invalidates* is not; and the exception
fixpoint reads a justification's antecedents and its rule and nothing else.

`unknown` is also **belief-sensitive** for free: a stored-but-OUT `S` (a defeated
default) is not believed, so a level-6 match skips it, so `(unknown S)` holds of a
defeated `S` — closed-world negation reads current belief, not mere storage.

## What surfaces where

- Blocking produces **no nogood**: a blocked conclusion does not exist, so nothing is
  contradictory and nothing is arbitrated. `unknown` is undercutting, like
  `exceptWhen` — not a rebuttal.
- A blocked conclusion has no handle, so the sentence arity `why-not (kb sentence
  context)` is the only one that can be asked of it. It reports `:excepted` for an
  `exceptWhen` block and `:closed-extent` for a positive goal under a visible grant; a
  conclusion an `(unknown S)` antecedent blocked reads `:not-stored`, nothing having
  been placed.

## Deferred antecedents in every chainer

`unknown` in a rule body is honoured by **all** the chainers — forward chaining
(`chain/solve-deferred`), `res/prove`, and the node engine.
The last two discharge an antecedent by fact matching and rule expansion, which on its
own proves nothing for a *deferred* antecedent — `unknown`, `different`, `evaluate`.
`res/solve-deferred` closes that: `resolution` sits below the prover registry (`provers`
requires `resolution`), so it cannot name `solve-goal` at compile time and reaches it
through `wiring/solve-goal` — one of the three calls [`vaelii.impl.wiring`](namespaces.md)
collects, because `unknown` runs the registry back over its own argument and so is mutually
recursive with the chainer asking for it. Resolved once into a `delay` rather than carried
on a thread binding, because `query` is lazy and a deferred literal reached mid-stream
must still find the solver; an optional `*deferred-solver*` var overrides it. So `prove` /
`query` / `ask` / forward chaining all agree about a rule with an `unknown` (or `different`
/ `evaluate`) antecedent, and they agree by construction rather than by four separate
implementations.

## Limitations

- **No existential `unknown` witness.** `(unknown (thereExists ?x S))` answers only
  *whether* a witness exists, never *which*; that is inherent to negation as failure.
- **No witness from a `forall` either.** `(forall ?y …)` answers *whether* every `?y`
  satisfies the head, never *which* one does not; the counterexample is what the inner
  existential found and projected out.
- **No disjunctive census body.** An aggregate's body is joined across its conjuncts and
  refused when it disjoins (`:not-well-formed`): a count over a union is not the sum of
  two counts, since a witness satisfying both alternatives would be counted twice. Name
  the extent with a rule — whose antecedent may disjoin — and aggregate over the
  conclusion ([aggregate.md](aggregate.md)).
- **No rule expansion inside a query.** The join runs over the registry, so a conjunct
  reachable only by backward chaining does not contribute — the bound that keeps
  closed-world reasoning out of an unbounded proof search, unchanged by the join. A
  closed extent reads the same level: a member derivable only by a `set/backwardRule` is
  not in the extent the grant calls complete.
- **A closed extent is read where the goal is, not where a rule is.** The registry is
  reached from a query, from a rule antecedent's derive-time check, and from a backward
  chainer whose leaf *is* the registry. A backward chainer running over the stored facts
  alone answers a `(not (P a))` subgoal from what is stored, as it did before the grant —
  an under-answer rather than a disagreement, and the same boundary level 6 draws
  everywhere else.

## Where the pieces are

- **Three provers** over the level-6 list, ground/closed only, complete and
  authoritative; members of `default-provers` and of the `wff` refusal table.
  `ForallProver` desugars and hands the goal **back to the registry**, so the goal and
  the rule antecedent are answered by one mechanism.
- **`ClosedExtentProver`**, the fourth, for a ground `(not (P …))` under a visible
  `closed_extent_predicate`. Partial rather than complete (completeness 50): a stored
  negative is `FactProver`'s answer, and this augments it.
- **Representation** in `sentex`: `unknown?` / `there-exists?` recognizers, `free-vars`
  respecting the quantifier, `unknown` in `deferred-predicates`, the standalone
  `thereExists` desugar (splicing a conjunctive body into that many antecedents),
  `conjuncts` / `naf-query-conjuncts` (the query's conjuncts, the `unknown` spelling of
  `exception-query-conjuncts`) with the conjunct sort beside the other literal
  normalizations, `desugar-forall-literal` / `desugar-forall-rule` (the `forall` sugar,
  applied at both entry points), `census-bound-vars` (what a census body binds for itself), and
  `check-naf-closed` (closure, quantifier locality, the producible-quantified-variable
  rule, and the aggregate's census check).
- **The joined evaluator**, `provers/conjunction-solutions` — one function, used by
  `UnknownProver`, `ThereExistsProver` and `exception-holds?` alike, so the goal, the
  antecedent and the exception cannot drift about what a conjunction means.
- **Forward chaining**: `unknown` skipped in the join and blocked at derive time per
  placement context (`naf-blocks?`), alongside the exception.
- **Belief maintenance**: `justification-excepted?` blocks on a NAF antecedent too;
  `index-rule-sentex` / `disintegrate-sentex!` post the NAF predicates in the re-check
  index (`rules/recheck-predicates`); `settle` narrows NAF firings the same way it
  narrows exception firings. Sweep and revival are the ordinary paths — including the
  refusal record ([exceptions.md](exceptions.md), "A refused firing is remembered as
  bindings"), which covers a firing an `unknown` blocked at derive time exactly as it
  covers one an exception blocked: both are re-askable from the bindings alone, and
  both are entries in the same record.
- **Stratification**: `checks/negative-predicates` and `check-stratified` treat an
  `unknown` antecedent's predicate as a negative edge, so a cycle through it — by rule
  or by `genl` edge — is refused.  A closed-extent negative antecedent adds one too, and
  `check-closed-extent-stratified` refuses the *grant* that would close a cycle with
  rules already stored.
- **The closed extent** in `rules` (`closed-negative-antecedents` / `closed-extent-antecedents`
  / `closed-extent-predicates-of`, the structural half), `special` (the
  `closed_extent_predicate` entry and `index-closed-extent-rules`) and `chain`
  (`closed-extent-blocks?`, the withheld join literal, the `:closed-extent` slot on the
  rule view).
- **Every chainer**: `res/solve-deferred` (the registry reached through
  `wiring/solve-goal`, overridable via `*deferred-solver*`) lets `res/prove` and the
  node engine evaluate a deferred antecedent, so every chainer agrees about `unknown`,
  `different` and `evaluate` alike.

`naf_test` covers `free-vars`, both operators at top level (belief-following, the
open-goal refusal, the combination, non-assertibility), the `unknown` antecedent firing
and derive-time block, order-independence (block-and-sweep on late arrival, revival on
retract), `unknown (thereExists …)` and standalone positive `thereExists` in a rule, the
conjunctive query (`naf-query-conjuncts` itself, block only when every conjunct holds,
every conjunct's predicate watched — including a `thereExists` conjunct's, the goal and
backward-rule readings agreeing with the antecedent one, and order, nesting, repetition
and a lone conjunct all not being the rule's identity), the **joined** query (one witness
for every conjunct rather than one apiece, blocking and reviving on the *second*
conjunct's predicate, the same answer from the other arrival order, and the standalone
positive existential splicing into the hand-written join), the closure, locality,
unproducible-quantified-variable, aggregate census and empty-conjunction
refusals, and the stratification cycle refusals — through *any* conjunct, including one
reached through a quantifier, which is the edge a single-predicate key would miss.  It
also covers `forall`: the desugar itself, the sugared and nested spellings storing to one
handle, "all of Bob's children are asleep" through the vacuous case, two asleep children,
a third awake one withdrawing the conclusion and its retraction reviving it, the goal
form agreeing with the antecedent, the other arrival order settling the same way, the
cycle through either half of the desugar, the escaping binder, and non-assertibility.
And the **closed extent**: the negative answered from the absence of a positive, the grant
scoped to the theory that gives it, the rule antecedent firing on nothing stored and
withdrawing when a member arrives, the reverse arrival order (facts, rule, then grant), a
stored negative still answering, the cycle refused from the rule side *and* from the grant
side, and `why-not` saying the extent is closed.

## The third member of the family

[aggregate.md](aggregate.md) adds `agg/count` and its four siblings against the
same code path: query operators, refused by the same `wff` arm, deferred literals with the
same closure rule and the same `:naf-not-closed` diagnostic, level-6 bodies, negative
edges in the same stratification graph, and firings maintained through the same
re-check index. Two things differ, and both follow from an aggregate binding a
**value** where `unknown` is a test — it is evaluated per placement context rather than
skipped in the join, and a queued aggregate rule is re-joined whether or not anything
blocked (a count that rose licenses a firing no block ever suppressed).
