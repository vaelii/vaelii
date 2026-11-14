# Negation as failure: `unknown`, `thereExists` and `forall`

- **Covers:** closed-world negation as a query operator — `unknown`/`thereExists`/`forall`,
  ground/closed evaluation, closed extents, and how a rule antecedent stays maintained as
  belief changes.
- **Not here:** the rule-level exception this reuses the guard defeat from →
  [exceptions.md](exceptions.md); aggregation, the third member of the same family →
  [aggregate.md](aggregate.md).
- **Assumes:** belief, justification, prover, `genl` → [glossary.md](glossary.md).

## The two operators

```clojure
(unknown S)          ; holds iff S is not derivable — closed-world negation
(thereExists ?x S)   ; holds iff some binding of ?x makes S derivable
(thereExists [?x ?y] S)
(forall ?y (implies Body Head))   ; sugar: the nested NAF below
```

`unknown` is negation as failure: `(unknown (flies Tweety))` holds exactly while the
KB cannot derive `(flies Tweety)`. `thereExists` existentially quantifies its
variable (or vector of variables) and **projects it out**: it produces no binding and
is a test. It closes a variable off so `unknown` can negate an existential:

```clojure
(unknown (thereExists ?c (parentOf ?c Tom)))   ; "Tom has no known parent"
```

All three are answered by a prover (`UnknownProver`, `ThereExistsProver`,
`ForallProver`), usable as a top-level goal (`ask` / `ask?`) and as a rule antecedent.
None is assertible: a `wff` arm refuses `(unknown …)` / `(thereExists …)` / `(forall …)`
as a stored fact, the way `different` is refused, because a query operator states no
fact. The negation of a query is a query too, so `special/wff-problems` refuses
`(not (unknown …))` with the `unknown` arm, at any depth of `not` and inside an `ist`.
No prover answers a `not` over `unknown`, `thereExists` or `forall`, so
`sx/connective-problems` refuses one as a rule antecedent or an `exceptWhen` query, at
any depth, with `:not-well-formed`, at `assert`, `check`, `try-assert` and import alike.
The closed-world spelling is `(unknown (forall …))` or `(unknown (thereExists …))`, and
`(not (unknown S))` is `S`. `ask` refuses no such goal, and answers it false.
The same check covers every `:query-only` term ([predicates.md](predicates.md)):
`different`, `minCommonGenl`, the aggregates, `bravely` and `cautiously`. The KB marks each
of them `(not_assertible P)`, and `special/wff-problems` refuses a literal or a denial of
any predicate a believed `not_assertible` marks, `genlMonad` included. A mark arriving after
facts of `P` are stored holds those facts in the `:out` forced set, so they are believed in
neither arrival order, and retracting the mark releases them.

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

A binder is a variable or a list of variables, and the list's order is not the rule's
identity ([canonicalization.md](canonicalization.md#a-naf-conjunctions-conjuncts-sorted)).
A rule whose `thereExists`, `forall` or head `exists` binds a constant is refused
`:not-well-formed` (`sentex/check-naf-closed`): a
constant binds nothing, so `(unknown (thereExists Kid (owns ?x Kid)))` would test for an
individual named `Kid`.

An open `(unknown (flies ?x))` is a search over the domain's *complement*, every `x`
that does not fly, so the prover **refuses** it, as `different` refuses an open goal. In
a rule, the free variables must be bound before the `unknown` runs: by a *generator*
antecedent, or by a deferred literal that **writes** (an aggregate's `?n`, an
`evaluate`'s output). A `thereExists`'s own variable is exempt; binding it is the
quantifier's job.

`check-naf-closed` holds every consuming literal to that rule, not only `unknown`: a
`(lessThan ?m 35)` whose `?m` nothing in the rule writes, or a `(matchesPattern ?s ?p)`
whose pattern `?p` nothing binds, is refused at assert time too. A bare *goal* nothing
binds answers empty. The two differ because a rule is stored and re-run: an unbindable
input would find nothing backward and throw mid-fixpoint forward, after the rule was
stored.

## Evaluated over the registry

The argument runs through the **registry**, level 6 of the lookup stack, which is the
list `exceptWhen` uses and for the same reason
([exceptions.md](exceptions.md#the-exception-is-a-query-not-a-literal)): closed-world
reasoning reads what the KB derives without an unbounded proof search. A forward-derived
fact counts; a fact reachable only by backward chaining does not.

`(unknown S)` runs `S` at level 6 and holds when there is **no** solution.
`(thereExists ?x S)` runs `S` at level 6 and reports existence, binding nothing outside.
A conjunctive `S` is **joined** across its conjuncts ("The conjunction is joined", below).

## In a rule antecedent

`(unknown S)` in a rule body is `exceptWhen` **inlined per-literal**: the rule does
not conclude for a binding under which `S` is derivable.

```clojure
(set/forwardRule (implies (and (bird ?x) (unknown (flies ?x))) (walks ?x)))
;; birds walk, unless they are known to fly
```

It shares `exceptWhen`'s whole machinery (evaluation point, re-check index, guard
defeat) and differs in **polarity and combination**:

- an `exceptWhen` exception is one condition, block-if-**all**-conjuncts-hold;
- each `(unknown S)` antecedent is an **independent** condition, block-if-**any**-holds:
  one derivable `S` withdraws the conclusion.

`chain/block-conditions` reads the two kinds together. A firing of a rule with either
confers `:default` ([nmtms.md](nmtms.md#strength-propagates-from-the-antecedents)).

### `S` may be a conjunction

```clojure
(set/forwardRule (implies (and (bird ?x) (unknown (and (flies ?x) (adult ?x)))) (walks ?x)))
;; birds walk, unless they are known to be adults that fly
```

The conjunction is derivable only if **every** conjunct is, so one conjunct short leaves
`(unknown S)` holding and the rule fires. The evaluator is the exception's
(`provers/exception-holds?`), and the join below runs it.

A **disjunctive** body is refused. `(unknown (or A B))` would need the evaluator to
union two runs, and nothing at level 6 does. The rule is not expanded on it either:
`(unknown (or A B))` reads as "neither A nor B is derivable", the De Morgan *opposite*
of one rule per alternative. Write the two `unknown` literals as two antecedents.

Conjunct order is **not** the rule's identity: the conjuncts are sorted, blind to
variable names, in the constructor (`sort-naf-conjuncts`), as `sort-conjuncts` sorts an
exception's, so two spellings of one condition are one rule. The sort reaches a nested
`unknown` or `thereExists` conjunct's conjunction too, and conjuncts it leaves tied are
ordered by the rule's canonical numbering
([canonicalization.md](canonicalization.md#a-naf-conjunctions-conjuncts-sorted)).
Nesting is not either: `(and A (and B C))` flattens (`sentex/conjuncts`), because a nested `and` is a goal no
prover claims, and left as one conjunct it would read as *not derivable*. A lone
conjunct loses its `and`, and a repeated one is dropped.

A conjunct may itself be a `thereExists`. Its binder is local to that conjunct, and the
predicate watched is the one *inside* the quantifier, recursively.

Every conjunct's predicate is posted in the re-check index, because a conjunction blocks
on the *last* of its conjuncts to arrive. The predicate posted is the one the conjunct
*reads* (`rules/watched-predicates`, shared with the exception's registration): an
aggregate conjunct is watched by its census body, an existential one by what it
quantifies. A negated conjunct is watched under `not`, which is also how the trigger
side keys an arriving `(not S)`.

### The conjunction is joined, so its conjuncts may share a witness

```clojure
(unknown (thereExists ?c (and (childOf Tom ?c) (sick ?c))))   ; "Tom has no sick child"
```

The conjuncts share the binder, so reading them independently would take each from a
*different* witness: "has a sick child" would hold of anyone with a child while anyone
at all was sick. [defenses.md](defenses.md#a-conjunction-under-a-quantifier-is-joined-never-read-flat)
refuses that reading. `provers/conjunction-solutions` joins instead: each conjunct is
substituted with what the conjuncts before it bound, run through the registry, and its
solutions thread on. `unknown`, `thereExists` and `exceptWhen` use the one evaluator. A
**ground** conjunction is the degenerate case: each conjunct contributes one solution or
none.

The conjuncts are run in a **planned** order (`planned-conjuncts`): generators first,
and each computed conjunct (a nested `unknown`, an evaluable, an aggregate, a
closed-extent negative) once the variables it reads are bound. A conjunct the registry
estimates at `provers/deferred-est` waits the same way for the variables its prover reads
(`provers/input-vars`), because the prover answers it completely only with those bound, as
the calendar clock and the point prover answer an `instantBefore`. A result-binding
evaluatable reads every argument but its result slot, and `argN` reads its formula, so a
conjunct reading the variable one of them binds runs after it. Canonical order sorts a
query's conjuncts blind to variable names, so the written order cannot be relied on; the
plan is recomputed at evaluation, as `plan/order` plans a rule body.

Two things are refused at assert time:

- A **quantified variable no generator conjunct of the same query binds**
  (`:naf-not-closed`) — `(unknown (thereExists ?c (and (childOf Tom Tom) (unknown (sick
  ?c)))))`. Nothing outside can bind `?c`, so the computed conjunct can never run, and
  the query would answer *not derivable* whatever the KB holds.
- An **empty** conjunction (`:type :not-well-formed`): nothing can make it derivable, so
  the antecedent would guard nothing.

The binder is shared by the conjuncts of one query and by nothing else:
`check-naf-closed` refuses a `thereExists` binder that appears anywhere in the rule
outside its own literal (`:quantifier-not-local`). A binder named in the consequent
leaks: nothing outside the query binds it, so the rule is not range-restricted. A binder
named in another antecedent is captured: that antecedent's binding is substituted into
the query, binder included, so the query tests one value instead of looking for a
witness, and the rule misjoins with no error.

**An aggregate's census body is joined by the same evaluator.**
`provers/aggregate-values` runs it through `conjunction-solutions`, so
`(agg/count ?n ?c (and (childOf Bob ?c) (asleep ?c)))` counts the children who are
asleep. The two refusals above have their aggregate spelling: a census variable no
conjunct of the body binds and nothing outside the aggregate names is `:naf-not-closed`,
and a disjunctive body is refused ([aggregate.md](aggregate.md)).

A **standalone positive** `(thereExists ?y (and …))` antecedent is spliced into the rule
body instead ("Standalone positive `thereExists` desugars", below).

### `forall` is sugar for a nested `unknown`

```clojure
(implies (and (person ?x)
              (forall ?y (implies (childOf ?x ?y) (asleep ?y))))
         (all_kids_asleep ?x))
;; "all of ?x's children are asleep"
```

∀?y (Body ⇒ Head) is ¬∃?y (Body ∧ ¬Head), and in a closed world ¬ is `unknown`. So the
universal is two negations around the existential, and it canonicalizes into exactly
that (`sentex/desugar-forall-literal`):

```clojure
(unknown (thereExists ?y (and (childOf ?x ?y) (unknown (asleep ?y)))))
```

The desugar runs at the **entry point**: the sentex constructor, and `rules/inner-rule`,
which every pre-storage check reads through. Range restriction, closure, quantifier
locality and the stratification graph therefore see the nested NAF, `canonical-sentex`
shows it, and the sugared rule and the hand-written nested one are **one rule with one
handle**. A conjunctive `Body` contributes its conjuncts to the join; a `Head` is left
whole, so an `(and …)` head is one nested `unknown` over a conjunction. A `forall` whose
second argument is not an `(implies …)` is refused `:not-well-formed`.

The inner `unknown` is a conjunct of the outer query, reached once the generators of
that query have bound `?y`, which is why the join plans its conjuncts. **NAF nests
exactly as far as it stratifies**: the inner query's predicates are negative edges too
(`rules/naf-predicates-of` reads through the quantifier and through the nested
`unknown`), so a cycle through either half is refused at assert time.

`?y` is local to the `forall`: it may appear nowhere else in the rule
(`:quantifier-not-local`), and every *other* variable in the body is bound by an
antecedent outside it (`:naf-not-closed`).

**The vacuous case reads true.** Bob having no children makes the existential
unsatisfiable, so the `unknown` holds and "all of Bob's children are asleep" is true:
the classical reading of a universal over an empty domain, which the desugar yields with
no separate case.

A `forall` is the one place the maintenance differs from a plain `unknown`. `(unknown S)`
is antitone in what a fact states: an arriving `S` can only make `S` derivable, so it can
only block, and the one arrival that releases it does so through a defeat of a believed
`S`, which the settle handles (below). A nested one is not antitone: an arriving
`(asleep Kid3)` removes the witness the inner query had found. So the rule is owed a
fresh join whether or not the blocked set moved, as an aggregate is
(`rules/arrival-releasable?`, `settle/rejoin-on-arrival-rules`, and the same exemption at
the two taxonomy edge triggers).

### Evaluated in the placement context, not the join

The question is asked at the placement context when the firing is made, in the network
and through the excepts. Where it holds at the placement, the firing is stored with a guard
defeat at the placement, whether its blockers rest on `:default` or `:monotonic` handles.
Where it holds only below the placement, the firing places a
guard defeat there, and a reader at or below it does not believe the conclusion through
that firing (decision 4 of [reference.md](reference.md#decisions)).

An `unknown` antecedent is **not** a join filter. Forward chaining *skips* it in the
join (it binds nothing and names no fact) and checks it at **derive time, per
placement context**, where `exceptWhen` is checked. Forward and backward must evaluate a
NAF condition in the *same* context, or `sentexes-matching` and a backward search would
disagree about one rule. Backward solves it as a deferred antecedent through the prover
at the query's context. Both read the same level-6 judgement
(`provers/exception-holds?` over the query's conjuncts).

**A guard below the placement places a defeat.** When a firing's `unknown` query or
`exceptWhen` holds at a context below its placement and not at the placement, the firing
stores `(defeat (sentexHandle F))`, F its conclusion, at each context a firing over the
handles the query matched is placed at (`chain/place-guard-defeats!`): the maximal contexts
that see the placement, those handles and the `genl` edges the match climbed, where no
except hides one of the handles (`chain/placements-over`, which reads no defeat). Its
justification, under informant `guard`, names those handles, the `exceptWhen`'s own handle,
the firing's rule and antecedents, F, and the `genl` and `genlCx` edges the context sees
them over. The blocker is found by the forward join over the query's conjuncts
(`chain/solve-rule`), so a conjunct a prover answers from stored facts names the facts it
read, as a firing's antecedent does: a `genl` conjunct the closure answers names the edges
of one path, and a conjunct on a `(transitive P)` predicate names the hops of its walk. A
prover answer that names no stored fact places no defeat. An inner `unknown` binds nothing
and is decided at the placed context, so a context the reader does not see moves no
defeat. The condition is checked at the placed context in the network and through the
excepts, with no defeat read (`tax/*network-belief*`): a blocker a defeat hides there
still places the defeat, which rests on it, and the walk reads the two defeats together
([nmtms.md](nmtms.md#a-defeat-dependency-cycle)). The firing is examined when it is made
and whenever the re-check index re-decides it, so a blocker arriving or leaving, an
`exceptWhen` arriving, a `genl` or `genlCx` edge moving, or an except of a blocker
arriving or leaving places or drops its defeat. A retracted or defeated blocker or
climbed edge takes the defeat's justification OUT, or out of force at a reader that does
not believe or see it. With `(pp ?x) & (unknown (qq ?x)) => (rr ?x)` and `(pp Zed)` in
CxA, and `(qq Zed)` in CxB below it, the defeat is stored in CxB: CxA believes `(rr Zed)`
and CxB does not.

**A blocker at the placement places a defeat there.** When the condition holds at the
firing's own placement, the firing is stored and its guard defeat is placed at the
placement by the same reading (`chain/guard-solution-placements`), whatever the class of
the handles its solutions rest on. A condition that holds at the placement with no
solution placed there (a prover answer naming no stored fact) places the defeat on the
condition's own handle, when the placement context sees that handle. The store is the
same in every arrival order, and the walk decides belief: a reader where a defeat hides
the blocker believes the conclusion. With `(pp Zed)` and `(qq Zed)` `:default` in CxA,
`(rr Zed)` and its guard defeat are stored in CxA, and a `:monotonic` `(not (qq Zed))` in
CxA gives `(rr Zed)` back with nothing re-chained
(`refused_firing_test/a-late-blocker-of-either-class-defeats-the-firing-and-records-nothing`).

**An except or a defeat that takes a blocker's defeat out of force is a supporter.** A
blocker a placed defeat hides at the firing's placement is believed at a reader whose
excepts or defeats take that defeat out of force: an except of a handle in the defeat's
support can lower a member's class, or hide a member, a ground or the defeat, and a defeat
of a `:default` ground in that support hides the ground. Each such except or defeat
(`chain/blocker-support-hiders`: the defeats naming a blocker, their support past
premises, and the excepts and other defeats naming a handle in it) places the guard defeat
as one more supporter beside the blocker handles, and the defeat's justification names it.
A context that sees a placement made without it takes none. With W `:monotonic` through X
and `:default` through Y, its nogood's loser L and the guarded firing F in CxD, and
`(except X)` in CxR below, the nogood is a dilemma at CxR, L is believed there, and the
guard defeat is stored in CxR. Retracting the except takes the defeat OUT. With the
nogood's loser defeated through a `:default` `(genl poodle dog)` in CxD and `(not (genl
poodle dog))` `:monotonic` in CxR, the negation pair's defeat hides the edge at CxR, and
the guard defeat is stored in CxR resting on it.

**A guard defeat removes one firing, not the sentence.** A justification `j` of F is
covered at a reader R when a justification of a guard defeat of F that is in force at R,
with every antecedent but F believed and seen there, names `j`'s rule and every antecedent
of `j`, carries `j`'s bindings, and names no firing of that rule with those bindings over
more antecedents than `j` (`exc/guard-owners`). A firing over a subset of a second firing's
antecedents therefore owns neither the second firing's guard justification nor the right
to drop it. The read walk (`exc/defeat-hidden-fn`) drops the covered justifications from its
fixpoint, so F stays believed at R through a premise or a second justification no guard
blocks there. A guard defeat reads F at its label (the exemption a placed nogood's own
`defeat` takes), so it does not hide itself. `chain` reads no defeat.

A blocker a reader below does not believe or see leaves the guard defeat at the placement
out of force there, and the reader believes the conclusion. At a reader below its
placement where an inner `unknown` of the condition fails, a guard defeat stays in force.

### Standalone positive `thereExists` desugars

A *standalone* positive `(thereExists ?y S)` antecedent, one **not** wrapped in
`unknown`, is **desugared to `S`** in the `sentex` constructor
(`sentex/desugar-there-exists`), with `?y` a local variable the match binds. By locality
`?y` reaches nothing else, so `S` joins the store like any generator, one witness per
solution. A conjunctive `S` is spliced in as that many antecedents, which is the join a
reader would write by hand. A person-with-a-child is a parent:

```clojure
(implies (and (person ?x) (thereExists ?y (parentOf ?x ?y))) (a_parent ?x))
;; stored as (implies (and (person ?x) (parentOf ?x ?y)) (a_parent ?x))
```

A `thereExists` **inside** `unknown` is a NAF query, evaluated by the prover, and is
left intact. So `thereExists` is absent from `deferred-predicates`; `unknown` is
deferred.

## A closed extent: `(not (P a))` without a stored negative

`unknown` chooses closure **per goal**: the author writes it where they want it. A
`closed_extent_predicate` grant chooses it **per predicate**, for everything read under it:

```clojure
(v/assert kb '(closed_extent_predicate month_of_year) 'CxCalendar)
;; "the months of the year are exactly these twelve"
```

Where the grant is visible, `month_of_year`'s **believed** extent is complete, so nothing
answering `(month_of_year Smarch)` at level 6 is what answers `(not (month_of_year Smarch))`.
`ClosedExtentProver` does that: a ground negative goal, the positive run through the
registry, and the negative held exactly while the positive finds nothing. Cost tier
`:compute`, completeness 50 (a stored negative is `FactProver`'s answer, and this
augments it), nothing stored: a closed extent creates no negative space, as `exceptWhen`
and `unknown` create none.

It is a **grant**, and the only thing that closes an extent: an undeclared predicate stays
open-world, where a fact nobody stated is not thereby false. It is a **policy of the
context that gives it**, read from the asking context's `genlCx` ancestor set the way
`abducible_predicate` is ([abduction.md](abduction.md)): one theory may state the twelve
months and read a thirteenth as refuted while a sibling, reading the same predicate,
answers only what it was told. It is belief-following like the other predicate marks: a
defeated or retracted member leaves the extent, and the closure follows.

### A closed extent for one argument value

`(closedExtentForArg P n v)` is the same grant narrowed to the goals whose argument `n` is
`v`:

```clojure
(v/assert kb '(closedExtentForArg accountOn 2 HostA) 'CxHosts)
;; "the accounts on HostA are exactly the stored ones"
```

Under it, nothing answering `(accountOn Carol HostA)` at level 6 is what answers
`(not (accountOn Carol HostA))`. `(not (accountOn Carol HostB))` stays open-world in the
same context, because argument 2 is not `HostA`. `ClosedExtentProver` answers both
grants (`provers/closed-extent-for?`). The goal is ground, so argument `n` is ground too;
an open `(not (accountOn Alice ?host))` is not closed.

The per-argument grant is scoped and belief-following as the whole-predicate grant is.
Its arms mark `P` under the taxonomy prop `:closed-extent-arg`, read from the asking
context, as the presence check; the prover then reads the grant's position and value back
from the believed grants visible there. A position past the goal's arity matches no goal.
CxUniverse's `interArgEqual` rows type the predicate by the grant's position, so a grant
past a stated arity is a clash that `try-assert` refuses
([argtypes.md](argtypes.md#a-type-conditioned-on-an-argument-value-interargequal)).

`closedExtentForArg1` through `closedExtentForArg5` are binary spellings:
`(closedExtentForArg2 P v)` means `(closedExtentForArg P 2 v)`. A CxUniverse forward
rule derives the ternary from each, and the engine reads only the ternary. An inert rule
states the reverse direction, so a ternary grant mints no binary twin.

A whole-predicate grant entails the per-argument grant at every admitted position and for
every value. CxUniverse states that as an inert rule over `admitsArgnum`, with `(thing ?value)`
binding the value, so a `closed_extent_predicate` grant stores no per-argument grants.

### Under the grant, a negative antecedent is NAF

```clojure
(implies (and (candidate_month ?m) (not (month_of_year ?m))) (not_a_month ?m))
```

Without the grant that `(not (month_of_year ?m))` is an ordinary literal, satisfied by a
stored negative. Under it the literal is negation as failure, and it takes `unknown`'s
whole path: **withheld from the join** (`planned-join`, beside the post-join literals),
decided at **derive time in the placement context** (`chain/closed-extent-blocks?`),
recorded in the refusal record under the `:naf` reason, and swept by the settle and
released from the record when the extent changes. A backward rule expansion, a
conjunctive query and a NAF query's conjunction run the literal after the generators that
bind it (`plan/order`, `provers/planned-conjuncts`), because `ClosedExtentProver` answers
it only ground.

Three details make that sound:

- **Only a *closed* negative antecedent** is read this way
  (`rules/closed-negative-antecedents`): one every variable of which another generator
  antecedent binds. A negative antecedent whose variable nothing else binds is what
  *produces* that binding by matching a stored negative, and withholding it would leave
  the rule with nothing to fire on.
- **The question asked at derive time is the whole level-6 one**, not "is there a positive
  answer". So a stored `(not (P a))` answers it as it always did, and a placement context
  that cannot see the grant reads the literal as an ordinary one. The join is withheld
  once the predicate is granted **anywhere** (`rules/closed-extent-declared?`, which reads
  a per-argument grant too): this over-selects, and derive time decides each literal per
  context and for the value it holds.
- **What the withholding costs is the support handle**, and the re-check index gives it
  back. The rule is posted under `P` (`rules/closed-extent-predicates-of`), and
  `recheck-on-sentence` posts an arriving sentence under its own functor *and* its
  underlying body's, so one key catches a `(P a)` arriving and a `(not (P a))` leaving
  alike, and the firing comes round for re-decision either way.

A grant asserted **after** the rules it governs reaches them too:
`special/index-closed-extent-rules` posts every stored rule with a `[:not P]` antecedent
and queues it `:all-rejoin`, because the grant blocked nothing for the blocked set to
notice and the firings it licenses have no justification yet, the same asymmetry a
widened `genlCx` ancestor set takes that marker for. The trigger is
`special/recheck-on-sentence`, so it runs on every move of the grant's belief: the grant
or its denial arriving or leaving, a defeat of the grant placed or lifted, an except of it,
a suspension. The posting stays when the grant leaves; a spurious posting costs one
re-check query. A re-decision of a firing reads the posting: it asks the whole level-6
question of every closed negative antecedent on a predicate the rule is posted under,
grant or no grant (`chain/redecided-negative-antecedents`). A firing made under the grant
holds no support handle for the literal it withheld, so the level-6 question withdraws
the firing, or keeps a refused one refused, once the grant leaves or is defeated and no
stored negative answers the literal. `recheck/exception-candidates` narrows the queued
firings by those literals beside the rule's `unknown`, `exceptWhen` and aggregate
literals, so an arriving `(P a)` reaches the firings naming `a` whatever other block
conditions the rule carries
(`naf_test/a-closed-extent-antecedent-beside-another-block-condition-is-redecided-when-its-member-arrives`).

A closed-extent negative **inside** an `unknown` antecedent, an aggregate's census body
or an `exceptWhen` query is not withheld: the condition is evaluated through the
registry, where `ClosedExtentProver` answers it. The re-check index posts the rule under
`not`, as it posts every watched negated literal, and under `P` as well
(`rules/closed-extent-query-predicates`), because a `(P a)` arriving or leaving is posted
under `P` alone and moves the condition.
`index-closed-extent-rules` finds such a rule through its `not` posting
(`provers/closed-extent-rules`), so a grant arriving or leaving after the rule posts and
queues it as it does a rule with a `[:not P]` antecedent.

The guard join withholds the closed-extent negative as the rule join does, so the
literal adds no matched handle to a guard solution. `chain/grant-supported` adds one:
the solution is taken once per handle that answers the ground literal alone
(`provers/closed-extent-supports`), each visible grant that covers it and each stored
`(not (P …))`. The guard defeat's justification names that handle, so a defeat or an
except of the grant takes the guard defeat out of force at a reader where the grant is
hidden, and the firing is believed there as `ask?` of the condition answers. A literal a
prover other than `ClosedExtentProver` and `FactProver` answers names no handle, and its
guard defeat rests on the rule and its antecedents alone. The guard defeat's `why` lists
the grant among its `:because` entries.

**A reader below the placement decides the literal at its own context.** When a
closed-extent negative antecedent `(not (P a))` holds at the placement and fails at a
context below it, the firing places a guard defeat there
(`chain/closed-extent-guard-placements`), as an `unknown` antecedent's guard below the
placement does. Two kinds of blocker place it. A `(P a)` member blocks as it blocks
`(unknown (P a))`, through `chain/guard-solution-placements`, at each context where
`(not (P a))` fails at level 6, so a stored `(not (P a))` visible there keeps the
conclusion believed. A set of excepts and defeats holding one hider of each grant the
placement sees (`provers/closed-extent-supports`) blocks at each context
`chain/placements-over` gives the set where no other answer of `(not (P a))` is visible,
so a `:monotonic` denial of the grant below the placement blocks through the defeat its
nogood places. Both are read in the network with no defeat read
(`tax/*network-belief*`). With the rule, `(kid K)` and the grant in CxA and `(asleep K)`
in CxB below it, CxA believes `(conclf K)` and CxB does not, and `provable?` of the same
rule written backward answers alike at both
(`naf_test/a-closed-extent-antecedent-is-read-at-each-reader-below-its-placement`).

### Stratification, from both arrival orders

A closed-extent negative is a **negative edge** on `P`, as an antecedent and inside an
`unknown` antecedent, an aggregate's census body or an `exceptWhen` query alike, so a
rule concluding `P` whose body reads `(not (P …))` under the grant is a cycle through
negation and is refused (`:type :not-stratified`). Inside a query the edge is on `P` as well as on `not`
(`rules/closed-extent-query-predicates`, the keys the re-check index posts it under). The
edge is conditional on the grant, so the *grant* can close a cycle too.
`checks/check-fact-stratified`, the check a `genl` edge takes, walks from each stored rule
the grant governs (`provers/closed-extent-rules`: the `[:not P]` antecedent-index lookup
and the rules posted under `not`, no scan). It **refuses the declaration** when a walk
closes a cycle, so stored state is always stratified. A grant a forward rule concludes or an argument-type mint
entails takes the same walk as a value (`checks/fact-stratification-violation`), and is
dropped and reported in `(violations kb)` as `:not-stratified`, as a derived `genl` edge
is ([exceptions.md](exceptions.md#a-derived-edge-is-dropped-not-thrown)). A refused or
dropped grant leaves no record, no mark and no posting. A rule arriving after a derived
grant it would close a cycle with is refused, so whichever of the two arrives second goes
(`naf_test/a-derived-closed-extent-grant-keeps-the-rule-set-stratified-in-both-arrival-orders`).
Only a stored grant marks its predicate, so a backward or lazy-forward rule concluding a
grant closes no extent.

A per-argument grant adds the same negative edge on `P`, whatever value it names, so
`(closedExtentForArg P n v)` and its binary spellings are refused where
`(closed_extent_predicate P)` would be.

`why-not` reports `:closed-extent` for a positive goal nothing answers under a visible
grant that covers it, a more specific answer than `:not-stored`: the KB states that the
extent is complete and the sentence is not in it.

**`defns` and `disjoint` are untouched.** A `defnIff` states a condition, not an extent:
a thing whose condition is merely unknown is concluded neither a member nor a non-member
([defns.md](defns.md)). Disjointness refutes from a *positive* claim about a sibling
type: a believed `(S x)` of a type a separation keeps apart from `T` answers `(not (T
x))` over `:monotonic` edges ([taxonomy.md](taxonomy.md#disjointness), "A separation
answers a denial"). Both stay open-world; the grant is the one place a KB says
otherwise, per predicate and per context.

## Order independence, and the re-check

Belief must not depend on arrival order. A conclusion drawn while `S` was absent must
be **withdrawn** when a later fact makes `S` derivable, and **revived** when that fact
leaves. This is the `exceptWhen` block/sweep/revive path, reused verbatim:

- The rule is posted in the re-check index (`[:exception-index <predicate>]`) under every
  predicate its `unknown` antecedents mention: `rules/recheck-predicates` unions the
  NAF antecedents' predicates with the aggregate bodies'. An exception's predicates ride
  its own meta-sentex into the same index (`special/index-exceptWhen-meta`), so both
  kinds of block condition key one index. A fact arriving or leaving on one
  of those predicates (or any subtype, via the genl spec fan-out) queues the rule.
- A negated literal `(not (T …))` in either kind of condition is posted under the types
  a declaration separates from `T` as well (`rules/separation-denial-predicates`), since
  a membership of a type below one of them answers the denial
  (`provers/DisjointnessNegationProver`). The spec fan-out reaches that membership's
  type, and the firing filter keeps a firing whose literal the membership denies
  (`recheck/separation-reaches?`). A separation or a `genl` edge that moves `T`'s
  separations posts the rule again and queues it whole
  (`special/repost-separation-denial-rules`), so the block does not depend on whether
  the rule, the separation or the membership came last.
- An **equality** queues it too, and no predicate can key that one. `(unknown (flies
  Tweety))` is answered under Tweety's representative, so merging Tweety with a Birdy
  that flies makes the inner query derivable with nothing on `flies` having moved, and
  the firing's own stored binding is now a spelling the KB does not answer under.
  `special/recheck-equality-edge` is the trigger, and the inner query is put in its
  context's normal form before it is evaluated (`provers/condition-normalizer`), so the
  binding and any constant the antecedent was written with are both asked under the
  representative. A reader below the placement can elect another representative:
  `chain/guard-solutions` asks the inner query once per distinct normal form among the
  readers `special/reader-contexts-at` names and keeps the union of the solutions, so a
  merge visible only below the placement places the guard defeat at that reader. In this
  direction the wrong answer is **unsound**: an `unknown` reporting a term absent when the
  KB answers it under another spelling draws a conclusion, where a silently-false
  exception only fails to withdraw one.
- At the next `settle`, the queued firings are re-evaluated. A firing whose `S` is now
  derivable at its placement keeps its conclusion and places a guard defeat there,
  whatever the blocker's class ("Evaluated in the placement context, not the join",
  above).
- Retracting a blocker takes the guard defeat resting on it OUT, and the conclusion is
  believed again under its own handle with nothing re-chained
  (`naf_test/retracting-the-blocker-takes-the-guard-defeat-out`). `retract!` settles
  inside `settle-after-teardown!`, so the revival is visible by the time it returns.
- A **defeat** releases at read time, with nothing stored or removed: a monotonic `(not
  (happy Zed))` arriving after a firing was blocked by the default `(happy Zed)` defeats
  it, so the guard defeat resting on `(happy Zed)` is out of force wherever that defeat is
  in force, and `(unknown (happy Zed))` holds again there. The settle pass that newly
  places a defeat posts its target's sentence and the sentences of what rests on it, as an
  arrival posts them (`settle/post-defeat-moves!`), so the guards watching it are decided
  again. A defeat the previous settle already applied posts nothing.

The settle-time firing filter (`firing-reachable?`) shapes the exception's conjuncts
and the `unknown` antecedents' inner queries the same way: a ground inner narrows
against the trigger, and an existential one (`(thereExists ?x …)`, never ground) falls
through to "keep", the safe over-approximation. Both sides of that comparison are read
under the equality-class representative, so a firing bound to a retired spelling narrows
against a trigger spelled under the representative rather than being dropped as
unrelated ([exceptions.md](exceptions.md#the-re-check-index)).

## Stratification

Negation as failure needs a stratified rule set. An `(unknown S)` antecedent is a
**negative** dependency on `S`'s predicate (fanned over the genl spec closure), joined
to the same dependency graph as `exceptWhen` and `different`
([exceptions.md](exceptions.md#stratification)). A rule set with a cycle through
negation (one rule's `unknown` depends on what another concludes and back) is
**refused at assert time** (`:type :not-stratified`), including the one-rule cycle (an
`unknown` on what the rule concludes) and a cycle a `genl` edge would close. Ordinary
positive recursion is untouched.

## Nothing is stored

A Vaelii `Justification` has **no out-list** ([nmtms.md](nmtms.md)): nothing about a NAF
condition is stored, and it is re-evaluated on the triggers an exception uses. Why an
out-list was not used is
[defenses.md](defenses.md#naf-is-re-evaluated-never-an-out-list).

**A dump cannot add one.** A justification frame in a dump is a field map, so a frame
can carry an `:out` key, and `vaelii.impl.io.import` refuses a non-empty one
(`:naf-justification`): imported without its out-list, the justification would support
its conclusion where the exporting KB's did not. Two relabel invariants depend on the
absence: `region-fixpoint`'s semi-naive warrant is that `valid?` is monotone in the IN
set, which a justification an arriving datum *invalidates* is not; and the exception
fixpoint reads a justification's antecedents and its rule and nothing else.

`unknown` is **belief-sensitive**: a stored-but-OUT `S` (a defeated default) is not
believed, so a level-6 match skips it, so `(unknown S)` holds of a defeated `S`.
Closed-world negation reads current belief, not storage.

## What surfaces where

- Blocking produces **no nogood**: nothing is contradictory and nothing is arbitrated.
  `unknown` is undercutting, like `exceptWhen`, not a rebuttal.
- A conclusion an `unknown` guard defeat covers reads `:unsupported` in `why-not`, with
  the covered justification's verdict `:guard`. A conclusion a closed-extent antecedent
  refused has no handle; the sentence arity `why-not (kb sentence context)` reads it
  `:not-stored`.

## Deferred antecedents in every chainer

`unknown` in a rule body is honoured by **all** the chainers: forward chaining
(`chain/solve-deferred`), `res/prove` and the node engine. The last two evaluate a
deferred antecedent (`unknown`, `different`, `evaluate`) through the registry
(`res/solve-deferred`, reaching it through `wiring/solve-goal`), so `prove` / `query` /
`ask` / forward chaining agree about a rule with one
([inference.md](inference.md#the-two-side-by-side)).

## Limitations

- **No existential `unknown` witness.** `(unknown (thereExists ?x S))` answers only
  *whether* a witness exists, never *which*; that is inherent to negation as failure.
- **No witness from a `forall` either.** `(forall ?y …)` answers *whether* every `?y`
  satisfies the head, never *which* one does not; the counterexample is what the inner
  existential found and projected out.
- **No disjunctive census body.** An aggregate's body is joined across its conjuncts and
  refused when it disjoins (`:not-well-formed`): a count over a union is not the sum of
  two counts, since a witness satisfying both alternatives would be counted twice. Name
  the extent with a rule, whose antecedent may disjoin, and aggregate over the
  conclusion ([aggregate.md](aggregate.md)).
- **No rule expansion inside a query.** The join runs over the registry, so a conjunct
  reachable only by backward chaining does not contribute. A closed extent reads the same
  level: a member derivable only by a `set/backwardRule` is not in the extent the grant
  calls complete.
- **A closed extent is read where the goal is, not where a rule is.** The registry is
  reached from a query, from a rule antecedent's derive-time check, and from a backward
  chainer whose leaf *is* the registry. A backward chainer running over the stored facts
  alone answers a `(not (P a))` subgoal from what is stored, as it did before the grant:
  an under-answer rather than a disagreement, and the same boundary level 6 draws
  everywhere else.

## Where the pieces are

- **Provers:** `UnknownProver`, `ThereExistsProver` and `ForallProver` (complete,
  members of `default-provers` and of the `wff` refusal table; `ForallProver` desugars
  and hands the goal back to the registry), and `ClosedExtentProver` (partial).
- **Representation** in `sentex`: `unknown?` / `there-exists?` / `forall?`, `free-vars`,
  `deferred-predicates`, `desugar-there-exists`, `conjuncts` / `naf-query-conjuncts`,
  `sort-naf-conjuncts`, `desugar-forall-literal` / `desugar-forall-rule`,
  `census-bound-vars` and `check-naf-closed`.
- **The joined evaluator:** `provers/conjunction-solutions`.
- **Forward chaining:** `chain/guard-solution-placements` and
  `chain/place-guard-defeats!`; `chain/closed-extent-blocks?`, the withheld join literal,
  the `:closed-extent` slot on the rule fields (`chain/rule-fields-of`), and
  `chain/redecided-negative-antecedents`; `chain/grant-supported` with
  `provers/closed-extent-supports`.
- **Belief maintenance:** `justification-excepted?`; `index-rule-sentex` /
  `disintegrate-sentex!` with `rules/recheck-predicates`; a closed-extent refusal in the
  refusal record ([exceptions.md](exceptions.md#a-refused-firing-is-remembered-as-bindings)).
- **Stratification:** `checks/negative-predicates`, `check-stratified`,
  `check-fact-stratified` and `fact-stratification-violation`.
- **The closed extent:** `rules/closed-negative-antecedents` /
  `closed-extent-antecedents` / `closed-extent-predicates-of` /
  `closed-extent-query-predicates` / `closed-extent-recheck-predicates-of`,
  `provers/closed-extent-rules`, and `special`'s `closed_extent_predicate` and
  `closedExtentForArg` entries with `index-closed-extent-rules`.

## The third member of the family

[aggregate.md](aggregate.md) adds `agg/count` and its four siblings on the same code
path: the same `wff` arm, closure rule and `:naf-not-closed` diagnostic, level-6 bodies,
stratification graph and re-check index. An aggregate binds a **value** where `unknown`
is a test, so it is evaluated per placement context rather than skipped in the join, and
a queued aggregate rule is re-joined whether or not anything blocked.
