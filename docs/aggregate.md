# Aggregation: a reduction over a query's solutions

- **Covers:** the five reduction operators
  (`agg/count`/`agg/sum`/`agg/min`/`agg/max`/`agg/avg`) as query operators, grouping by
  binding discipline, and how a firing resting on a count is maintained.
- **Not here:** the `unknown`/`thereExists` family this extends → [naf.md](naf.md); the
  rule-level exception whose re-check and stratification machinery this reuses →
  [exceptions.md](exceptions.md).
- **Assumes:** context, belief, `genl`, justification → [glossary.md](glossary.md).

Counting, summing and averaging as **query operators** — the third member of the
`unknown` / `thereExists` family. Nothing here is stored, and nothing here is new
engine machinery.

## The five

```clojure
(agg/count ?n ?v Body)   ; ?n = how many distinct ?v satisfy Body
(agg/sum   ?n ?v Body)   ; ?n = the sum of the distinct numeric ?v
(agg/min   ?n ?v Body)
(agg/max   ?n ?v Body)
(agg/avg   ?n ?v Body)
```

One shape, one prover (`prover-types/AggregateProver`), one `wff` arm. `?v` is
**projected out** — `thereExists`'s rule applied to a variable that is counted rather
than merely witnessed — so `?n` is the only binding produced and no solution ever
mentions `?v` outside the aggregate.

```clojure
;; (scoreOf Team 3) (scoreOf Team 1) (scoreOf Team 4) (scoreOf Team 1) (scoreOf Team 5)

(v/ask kb '(agg/count ?n ?v (scoreOf Team ?v)) 'CxWell)   ; => ({?n 4})
(v/ask kb '(agg/sum   ?n ?v (scoreOf Team ?v)) 'CxWell)   ; => ({?n 13})
(v/ask kb '(agg/avg   ?n ?v (scoreOf Team ?v)) 'CxWell)   ; => ({?n 3.25})
```

Four, thirteen and 3.25 — over the four **distinct** values, not the five solutions.

Exactly one answer or none. Never a stream: a reduction has a value or it does not.

## Bind or check

A variable `?n` takes the computed value; a **bound** `?n` is compared against it, so
`(agg/count 2 ?v (scoreOf Team ?v))` is indistinguishable from a test. `EvaluateProver` makes the
same pair, and this is not merely symmetry — the check arm is what lets a *firing* be
re-verified against the count it rested on, which is the whole of maintenance below.

Numbers compare numerically (`==`), so a long and a double naming one value agree.

## Fully bound to evaluate, and that is where GROUP BY comes from

`free-vars` subtracts **both** of the aggregate's own slots: `?v` because it is
projected out, `?n` because it is the operator's output.

| form | `free-vars` |
|------|-------------|
| `(agg/count ?n ?v (ancestorOf ?v Tom))` | `{}` — closed |
| `(agg/count ?n ?v (ancestorOf ?v ?x))` | `{?x}` |
| `(agg/sum 3 ?v (mass ?v Tom))` | `{}` |

Whatever is left splits in two, and which half a variable is in is decided by whether
the rest of the rule names it:

- A variable the rule also mentions **outside** the aggregate is the **group**, and must
  be bound by a generator antecedent before the aggregate runs — the same contract
  `unknown` has ([naf.md](naf.md)), refused with the same `:naf-not-closed` diagnostic.
- A variable mentioned **only** inside the aggregate is **local to the census**: the
  join binds it itself, and no antecedent could have supplied it. `?c` in
  `(agg/sum ?n ?a (and (childOf Bob ?c) (ageOf ?c ?a)))` is the join between the two
  conjuncts, not a group — that rule sums the ages of Bob's children.

A local variable still has to be one the census can reach a witness for:
`sentex/census-bound-vars` is what a generator conjunct matches plus what a computed
conjunct writes, and a local variable outside it — the reduction variable above all — is
refused `:naf-not-closed`, because the join runs generators first and would never reach a
conjunct that only reads it.

An aggregate is a deferred literal (`sentex/deferred-predicates`), so canonical
antecedent order and the planner both pin it after its binders and neither can hoist it.

A **disjunctive** body is refused too (`:not-well-formed`), and here there is no rewrite
that preserves the number: a count over a union is not the sum of two counts, since a
witness satisfying both alternatives would be counted twice. Name the extent with a rule
— whose antecedent *may* disjoin ([canonicalization.md](canonicalization.md)) — and
aggregate over the conclusion.

**The body is one query, and a conjunctive one is joined.**
`provers/aggregate-values` runs it through `provers/conjunction-solutions`, the same
evaluator `unknown`, `thereExists` and `exceptWhen` read ([naf.md](naf.md)), so the
conjuncts share `?v` and one witness has to satisfy all of them
([why](defenses.md#a-conjunction-under-a-quantifier-is-joined-never-read-flat)).

```clojure
;; (childOf Bob Kid1) (childOf Bob Kid2) (childOf Bob Kid3)
;; (asleep Kid1) (asleep Kid2) (asleep Stranger)

(v/ask kb '(agg/count ?n ?c (and (childOf Bob ?c) (asleep ?c))) 'CxWell)   ; => ({?n 2})
```

Two: the children who are asleep. Read conjunct by conjunct it would be three children
or three sleepers, and neither is the question. A one-literal body is the degenerate case
of the same thread — one conjunct, one registry call, the same solutions.

Grouping falls out of that, with no `GROUP BY` construct to design:

```clojure
(implies (and (node ?x)
              (agg/count ?n ?a (ancestorOf ?a ?x)))
         (ancestorCount ?x ?n))
```

`?x` is bound by the generator, so the aggregate runs **once per `?x`** and yields one
`?n` each — which is the grouped count. Every node gets its own answer because every
node is its own binding.

The reduction variable is **local**, like a `thereExists` binder: `?a` may appear
nowhere outside its own aggregate literal. A `?a` in the consequent would be a
range-restriction hole `range-problems` cannot see (it reads occurrences, and `?a`
does occur), so it is refused as `:quantifier-not-local`. And the reduction slot must
hold a **variable**: `(agg/count ?n Ada Body)` reduces over nothing, so no prover
claims it — as a rule antecedent that is a rule which stores and can never fire, which
is the one outcome worse than an error, so it is refused as `:not-well-formed`.

## Comparing the count

A count nobody can compare is barely a count, and *"a person with more than two
children"* is the first thing anyone asks for:

```clojure
(implies (and (person ?x)
              (agg/count ?n ?c (childOf ?x ?c))
              (lessThan 2 ?n))
         (large_family ?x))
```

This needs one thing that is not obvious. `?n` is bound per **placement context**
(below), so it does not exist for the whole join — and `(lessThan 2 ?n)` is a
*computed* literal, so unlike a matched one it has no fact to wait on and no empty
answer to give. It is not a join literal at all. `rules/post-join-literals` moves it,
and anything reading what *it* writes, into the placement phase beside the aggregate
that feeds it:

```clojure
(and (person ?x)                          ; joined
     (agg/count ?n ?c (childOf ?x ?c))    ; placement: binds ?n
     (evaluate ?d (+ ?n 1))               ; placement: reads ?n, binds ?d
     (lessThan 3 ?d))                     ; placement: reads ?d
```

**In written order**, which is the order they run in: a computed literal reads what is
written before it. That is not a rule aggregates introduce — an `evaluate` chain has
always had to be written downhill, canonical order holding a deferred literal where
the author put it. An aggregate could have been made an exception, by reordering the
placement phase so a comparison could sit above its own count, and deliberately was
not: the *forward* chainer can reorder that phase and the backward one cannot, so the
exception would buy one writing order at the price of the two disagreeing about one
rule. The uphill writing is refused instead.

Two consequences worth naming. The re-check runs the **whole** list, so a firing
licensed by `(lessThan 2 ?n)` at a count of 3 is withdrawn at a count of 1 — the
aggregate alone would report only that the number moved, not that the rule stopped
applying. And each literal keeps the context it would have had in the join: the
aggregate runs in the placement context because a census is of what that context
believes, the comparison in the wildcard because arithmetic is not knowledge asserted
somewhere.

**A literal that answers two ways answers nothing.** Every output the placement phase
computes reaches the conclusion — through the literals still to run, through the
`exceptWhen` and `unknown` checks that read these bindings, and through the consequent
itself — so taking the registry's first solution would place a *different fact*
depending on which solution came first, and which comes first is a function of how the
facts were stored. `chain/post-join-bindings` therefore declines a literal whose
solutions disagree, exactly as `provers/table-read` declines a unit that declares two
conversion factors: nothing is concluded, and a `:post-join-ambiguous` entry naming the
literal and its disagreeing solutions goes into `violations`. At most two distinct
solutions are ever realized, so the check is one extra pull off a lazy seq. A registry
where nothing disagrees never reaches it, which is every KB whose post-join literals are
the built-in computations — each of those answers once or not at all.

**What is bound**, then, is a generator's variables *plus* what the deferred literals
themselves write — an aggregate's `?n`, an `evaluate`'s output. A deferred literal
reading a variable nothing in the rule writes is refused at assert time
(`:naf-not-closed`), which is where that diagnosis can still be acted on: the join
throws on an unbound computed input rather than reporting a comparison that never ran
as one that failed, and a throw mid-fixpoint arrives after the rule is already stored.

A written output binds only the literals written **after** it, aggregates included, so
`(and (evaluate ?z (+ ?q 1)) (evaluate ?q (+ 1 1)))` is refused and always was.

A bare **goal** has no rule around it, so every variable of its body is local by the
same reading, and `AggregateProver` claims it when the census binds them all. One it
cannot — a variable only a computed conjunct reads — answers empty rather than being
refused, and the difference from a rule is the point: a goal is asked and gone, while a
rule is stored and re-run.

## Evaluated over the registry, which expands no rule

The body runs through the **registry** for exactly the reason `unknown` does: a count
that could launch an open-ended backward search is a count whose cost is unbounded, and
it is reached from inside a relabel loop.  Nothing in the registry backchains, so the
restriction is structural — there is no list to remember to use.

That is less of a restriction than it sounds. A **forward-derived** fact is counted:
it is stored and believed by the time the query runs. So is a relation held in the
cached closures — `genl`, or a `(transitive ancestorOf)` walked by
`TransitivePredicateProver` — which is what a per-node transitive-ancestor count is
actually made of. What a level-6 body cannot see is a relation reachable **only** by
backward chaining: a `set/backwardRule`'s conclusions.

`cost` is `:compute`, not `:lookup`, and that is a claim with enforcement: a reduction must
exhaust the body before it has any answer at all, which is precisely what the tier
names, so a `{:max-cost :lookup}` budget **drops** the prover and `:compute` admits
it. `completeness` is `100` — an aggregate is not assertible, so nothing else can hold
a claim about one, and nothing may be unioned in.

## Distinctness is by the equality closure

Count and sum are over *distinct* `?v`, and distinctness reads the equality closure's
representative. Two names for one thing are one value:

```clojure
(knows Ada Alan) (knows Ada Turing)     ; (agg/count ?n ?v (knows Ada ?v)) => 2
(sameAs Alan Turing)                    ;                                      => 1
```

That is the whole point of holding the partition. A count that read raw terms would
report a merge as two things and be wrong in the one direction the KB has already
decided.

**Read from the asking context**, the same scoping `different` puts on the same
partition ([equality.md](equality.md)) and for the same reason: a census is of what
*this* context believes, and the unique names it holds are the ones it has not been told
to merge. A `(sameAs Alan Turing)` stated in a context collapses the two there and
nowhere else — the context above it was never told, its own solutions still name both,
and it still counts two. Read globally instead, a private merge would silently retire a
name for readers who cannot see it.

## The empty body, where the five differ

**Count is 0 and sum is 0** — the identity of each reduction, and a true answer about
an empty group. **Min, max and avg over nothing have no answer at all** and yield no
binding: a zero minimum is a claim about a group with no members, and an average over
nothing is a division by zero however it is dressed up. Not nil, not zero — nothing.

## Numbers, measures, and what is neither

A non-numeric value under `sum` / `min` / `max` / `avg` is an **error, not a silent
skip**. A count of names is meaningful; an average of them is not, and quietly
dropping the non-numbers would answer a different question than the one asked. It is
recorded in the violations ledger (`(violations kb)`, `:violation :aggregate`) and
yields nothing. `count` is unaffected — counting is the one reduction that never reads
the values.

It goes to the ledger rather than a throw for the derivation path's reason: an
aggregate is reached from inside a fixpoint that must not abort. It is filed **once**
per distinct error, which a dropped conclusion does not need to be: a count is
recomputed and never cached, so the same bad extent is reduced again on every query,
every re-check and every settle pass, and filing each would fill a ledger capped at
its newest 1000 entries with copies of one defect and evict the real drops.

**The reduction is over sorted values**, because floating-point addition is not
associative and the values arrive in *solution* order — a function of how the facts
were stored rather than of what they say. Without it, six readings that sum to `8.0`
sorted sum to `7.7`, `8.2` and `8.6` in three arrival orders, so asserting the same KB
in another order would change what the aggregate reports, and order independence is
the engine's first invariant ([nmtms.md](nmtms.md)). Exactness is not on offer and is
not claimed; determinism is. The integer permutation test cannot see this — counting
is exact whatever the order — which is why the float case is pinned separately.

**Measures are not non-numeric.** `agg/sum` over `(QuantityFn 5 Meter)` is a
legitimate sum, normalized through `provers/normalize-quantity`, added in base units,
and rendered back by `render-quantity` — out of the same `conversionFactor` table the
normalization multiplied by, so nothing separate can disagree about the unit the
arithmetic happened in.

* `:sum` and `:avg` are linear in the `[lo hi]` bounds, so an over-approximation
  carries through honestly: an interval in gives a `QuantityIntervalFn` out, which
  says so rather than picking a figure out of a range it only bounded.
* `:min` and `:max` need a **total** order and measure bounds give only a partial one.
  They answer for point measures (`lo = hi`) and refuse a genuine interval rather than
  guessing which of two overlapping ranges is the smaller.
* A **dimension mismatch** is refused, not added. Metres plus seconds is not a sum.

## Not assertible

A `wff` arm refuses all five as stored facts, the way `unknown` and `different` are
refused — a query operator states no fact. For an aggregate there is a sharper version
of the reason: it would state a **stale** one. A count is a function of what is
believed now, so storing one puts a computed value under truth maintenance with no way
to invalidate it. That is also why deriving one is out of scope (below).

The naming checks see the operator as a **frame**, not a literal: an aggregate's body
is a goal, and read as an argument it would never be checked at all, while the
aggregate itself would masquerade as a three-place `agg/count`.

## Nothing is stored, and no JTMS node is created

Asking an aggregate leaves the sentex and justification sets identical. A count is
recomputed, never cached — the same discipline `unknown` has, and for the same reason:
the answer is a function of current belief, and a cached function of belief is a wrong
answer waiting for the next assert.

## Maintenance, when the aggregate is a rule antecedent

"Recomputed, never cached" answers a *query* completely and a *firing* not at all. A
rule that fired because the count was 2 must not stay fired when the count becomes 3.
This is the part an implementation over raw reads gets silently wrong, and it is not a
new mechanism — it is `exceptWhen`'s, with one addition.

**The trigger.** The rule is posted in the re-check index
(`[:exception-index <predicate>]`) under every predicate its aggregate bodies mention —
**every conjunct's**, read through `rules/watched-literals`, since a fact arriving on any
one of them changes which witnesses the join finds and so what the count is.
`rules/recheck-predicates` unions those with the `unknown` antecedents' because they
are one problem — both read what the KB believes rather than a fact the justification
names, so both need an arriving fact on those predicates to bring the firing back for
re-decision.

**The withdrawal.** `chain/post-join-withdrawn?` — reached through
`rule-firing-blocked?`, which `justification-excepted?` asks of every firing — re-runs
each aggregate in the conclusion's own context under the firing's **stored bindings**, where
`?n` is already bound — so each runs in check mode, and a mismatch blocks the firing
exactly as an exception does. The antecedents could not express this: they name the
facts the join matched, and every one of them is still stored and believed when some
other fact changes the census.

**The other direction, which is the addition.** Most re-check conditions are a
*block*, so releasing one shows up as a justification leaving the blocked set and
re-chaining is owed exactly to the rules that released. An aggregate is not, because it
binds a **value** — and a nested `unknown` is not either, for the same asymmetry
(`rules/arrival-releasable?` covers both). A count going 1 ⇒ 2 makes a firing that never existed: there is no
blocked justification to release, nothing moves in the blocked set, and the settle pass
would converge having derived nothing. So `settle` re-joins a queued aggregate rule
whether or not anything blocked. (2 ⇒ 3 is the other half, and *that* one is a block —
both halves happen in the same pass.)

**Belief, not storage.** A defeated fact is stored and not believed, so it drops out of
the census — and that direction rests on one detail. `special/recheck-on-sentence` reads
`sentex/underlying-body`, **not** `sentex/positive-body`, which is nil for a genuinely
negative sentence: an arriving `(not S)` has to post under `S`'s predicate, or no
re-check condition reading *belief* can ever see the defeat, since a defeat stores and
removes nothing. `underlying-body` is the content-side answer to `positive-body`'s
constraint-side one: `(not (penguin X))` **is** content about `penguin`.

So four things move the conclusions resting on a count, and each of them both ways: a
counted fact asserted and retracted, and one defeated and un-defeated.

**And a fifth, which is neither.** An equality moves a census without a fact arriving,
leaving, or changing label: distinctness reads the closure, and the merge also *retires*
a spelling, so the counted sentex is still stored and still holds its handle while being
gone from the belief-filtered read the census is. Nothing on the counted predicate moves,
so the re-check index cannot see it — `special/recheck-equality-edge` is the trigger,
and it covers an asserted `sameAs` / `rewriteOf` / `equals`, the equality a `functional`
declaration derives, a schematic rewrite rule, and the removal of any of them.
[exceptions.md](exceptions.md) has the general shape, of which this is one of four
instances. The firing's **stored bindings** are the other half: a justification records
what matched when it fired, so a firing that grouped on a term the merge retired would
re-take its census under a name the KB no longer answers under and read the empty
answer as a count of zero.

**And order cannot decide the answer.** A count is a function of belief maintained by
re-joining on arrival, which is exactly the shape an order-sensitive re-join would hide
in — so the four edges of a chain are loaded in all 24 orders and the counts are
compared. One distinct answer. Order independence is the engine's first invariant
([nmtms.md](nmtms.md)) and it is not one an aggregate gets for free by inheriting
machinery; it is a claim about the machinery being right.

## What it costs, said out loud

A count is recomputed, never cached, so a rule joining on one is **re-joined** — not
merely re-checked — whenever a counted fact arrives. A chain of *n* nodes under
`(transitive ancestorOf)`, with the grouping rule above (`lein bench-aggchain`):

| nodes | no rule | rule first | deferred chaining | one `edit!` | rule last |
|---|---|---|---|---|---|
| 10 | 1.7 | 21.3 | 20.2 | 5.1 | 4.4 |
| 20 | 1.6 | 45.8 | 48.6 | 7.9 | 6.8 |
| 40 | 4.3 | 160.0 | 170.7 | 17.6 | 15.4 |

Quadratic on purpose rather than by accident: every arriving `(ancestorOf a b)` re-joins
the rule over every node, and each grouping re-reads its whole ancestor set.

Two readings are worth having.

**`{:chain? false}` buys nothing.** The re-join is not the assert's forward chain — it
is queued in the re-check index and drained by **settle**, and settle runs per assert
whether or not chaining did. Deferring the half that was never the cost changes nothing,
which is why the column is in the table rather than left as an assumption.

**One `edit!` lands exactly on `rule last`** — the floor, where the reductions happen
once over a finished extent. One settle, one drain of the queue, one join. The ratio is
4x at n=10 and 9x at n=40 and keeps climbing, which is the shape to read rather than
either number: the per-assert path is quadratic and the batch is not. So the actionable
advice for a bulk load against an aggregate rule is to batch it, and the batch reaches
the identical counts.

A count is **recomputed**, never maintained: nothing keeps a running total on the assert
path, so every re-check runs the census again over the finished extent.

## Stratification

An aggregate over a relation that depends on the aggregate is unstratified, exactly as
negation as failure is: adding a fact changes the count, which can withdraw the
conclusion, so there is no settled answer and which one you land in would depend on
arrival order.

This costs no machinery of its own. The aggregate bodies' predicates — one per conjunct
of a joined body — join the `unknown` antecedents' as **negative edges** in the rule
dependency graph, and
`checks/check-stratified` refuses a cycle through them at **assert time** — before
anything is stored, `:type :not-stratified`, with the cycle. A rule counting what it
concludes never reaches the store.

## Where it plugs in

| protocol | what it contributes |
|------|---------------------|
| `provers/default-provers` | one `AggregateProver` beside `->UnknownProver` / `->ThereExistsProver` |
| `provers/conjunction-solutions` | the joined evaluator the census body runs through, shared with `unknown` / `thereExists` / `exceptWhen` |
| `wff/naf-problems` | the five, through `special/entries` — one arm, five table rows |
| `sentex/deferred-predicates` | the five, so canonical order and the planner pin them after their binders |
| `sentex/free-vars` | one arm subtracting both slots |
| `sentex/deferred-input-vars` / `-output-vars` | what a computed literal reads and what it writes, in one place for the three consumers |
| `sentex/census-bound-vars` | what a census body binds for itself — read by the assert-time census check and by the prover's applicability |
| `sentex/check-naf-closed` | group-variable closure and binder-locality, plus the reduction-slot and census refusals |
| `naming/literals` | one frame arm, so the body is checked as a goal |
| `rules/recheck-predicates` | unions the aggregate bodies' predicates, one per conjunct |
| `rules/post-join-literals` | which antecedents the join withholds for the placement phase |
| `checks/check-stratified` | the same predicates as negative edges |
| `chain` | withhold from the join; bind per placement; the withdrawal arm |
| `settle` | re-join a queued aggregate rule whether or not anything blocked |
| `kb/CxCore.txt` | five `(comment …)` + `(ternary_predicate …)` declarations |

## Where the census is taken

An aggregate binds a **value**, and which facts are in the census depends on the
context. The join cannot answer that: placement is computed from the matched facts
*afterwards*, so at join time there is no context to count in. So the aggregate is
withheld from the join, exactly as `unknown` is, and evaluated per **placement
context** in `chain/place-conseq` — the bindings it produces are the ones every check
there reads, so an exception or a NAF literal mentioning `?n` sees the count this
placement rests on. `(unknown (banned ?n))` over a count works for that reason and no
other.

**It counts where the conclusion lands, and has no say in where that is.** An
aggregate matches nothing, so it contributes no handle, so it is not an ingredient of
placement — the rule's *other* antecedents decide that alone. One rule therefore gives
each context its own count, which is the useful half:

```clojure
;; Left and Right under Root; the rule in Root
(person Ann)@Left  (person Ann)@Right
(childOf Ann C1)@Left  (childOf Ann C2)@Left  (childOf Ann C3)@Right
;; => (childCount Ann 2)@Left  and  (childCount Ann 1)@Right
```

And the surprising half is the same fact read the other way: group on something only a
*general* context holds and the count is taken there, where the children's facts are
invisible. `(person Ann)@Root` with every `childOf` below it concludes `(childCount
Ann 0)@Root` — not a bug, and the first thing to check when a count comes back 0.
Bind the grouping variable from a fact in the context you mean to count.

That is what makes the chainers agree. Backward (`prove` and the node engine)
evaluates it in the goal's context, forward in the conclusion's placement context, and
both are *the context the conclusion is about* — the same answer
[exceptions.md](exceptions.md) gives to the same question. The parity is worth testing
rather than assuming: the comparison-on-a-count shape is one the two chainers can
disagree about silently, backward evaluating the aggregate inline as it walks the body
while forward has to arrange for it.

## Scope

**In:** the five operators as one prover, the `wff` refusal, the CxCore
declarations, the closure and stratification checks, the re-check maintenance.

**Out:**

* **Aggregates as rule consequents** — deriving and storing an aggregate fact. That
  puts a computed value under truth maintenance and needs an invalidation story the
  JTMS does not have. Query-only here.
* **Incremental / maintained aggregates** — a count updated on assert rather than
  recomputed. It rests on the consequent case above, which is also out.
* **`GROUP BY` as a construct.** Grouping comes from the binding discipline; syntax for
  it would be a second way to say the same thing.

Not designed for, but working, and tested so it stays that way: an aggregate **inside
an `unknown`** — `(unknown (agg/count 9 ?v Body))` holds exactly while the count is
not 9. Nothing arranges for it. `unknown` runs its argument through the level-6 list the
aggregate is registered in, so the composition is what registering it already meant.
