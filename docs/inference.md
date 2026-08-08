# Inference and truth maintenance

- **Covers:** how a rule fires forward and backward — direction, the forward agenda, the two
  backward chainers (`prove` and the node engine), predicate subsumption, query planning, and
  the `ask` prover registry.
- **Not here:** resumable, resource-bounded search → [anytime.md](anytime.md); belief
  maintenance, defeat classes and contradiction resolution → [nmtms.md](nmtms.md).
- **Assumes:** sentex, context, `genl`, JTMS → [glossary.md](glossary.md).

`vaelii.impl.rules`, `vaelii.impl.resolution`, `vaelii.impl.jtms`, the forward chainer in
`vaelii.impl.chain`, and the fixpoint that follows it in `vaelii.impl.settle`.

For this machinery as worked, verified examples rather than prose, see the `/reasoning`
browser page ([web.md](web.md)) — each card runs a real query against the shipped
ontology, kept honest against KB drift by
[`examples_test.clj`](../test/vaelii/examples_test.clj).

## Rules are sentexes

A rule's sentence is an implication `(implies (and <ante> ...) <conseq>)`, in a
context — an ordinary sentex, so it gets a handle, TMS support, and retraction
for free (its handle is an antecedent of every justification it licenses, so
retracting the rule sweeps them). Rules must be **range-restricted**: every
consequent variable appears in an antecedent, so a fired consequent is ground.

A rule that concludes a **conjunction** is polycanonicalized into one rule per
conjunct (`rules/expand-consequent`): `(implies A (and C1 C2))` is stored as two
rules `(implies A C1)` and `(implies A C2)`, keeping any virtual wrapper (default /
forward / backward / inert). `assert` and `assert-rule` do the split and return
the **vector** of handles in that case (a single handle otherwise).

## Rule direction (virtual predicates)

By default a rule is used in *both* directions. Wrap it to constrain that — these
`set/*Rule` virtual predicates are interpreted on assert, not stored as facts:

| Wrapper | Forward-chained? | Used in backward? |
|---------|------------------|-------------------|
| `set/forwardRule`  | yes | no |
| `set/backwardRule` | no  | yes |
| `set/inertRule`    | no  | no (documentation) |
| (bare `implies`)   | yes | yes |

Direction is not an indexing choice: **every** rule is registered under all of its
antecedent predicates *and* its consequent predicate, whatever its direction
(`special/index-rule-sentex`, [indexing.md](indexing.md)). What the wrapper decides is
which chainer will *use* what the index already holds.

`assert-rule` also accepts `{:direction :forward|:backward|:inert|:both}` — and so
does `assert`, as the programmatic spelling of the `set/*Rule` wrappers.

Re-asserting an α-equivalent rule dedups to the one stored handle, and its
`:direction` / `:defeasible` slots resolve from **content**, not arrival order: the
least restrictive direction of the spellings seen (`join-direction`), and strict
over defeasible. A rule asserted bare after `set/inertRule` therefore fires, and one
asserted strict after `set/defaultRule` ties with a monotonic rival — the same two
assertions reaching the same beliefs whichever arrived first, which is what
[nmtms.md](nmtms.md) requires. The resolution reaches the justifications already
recorded (`restrength-informant`), so conclusions derived under the earlier spelling
carry the resolved class too. To *remove* a direction or defeasibility a rule has
acquired, retract it and re-assert the narrower spelling.

## Forward chaining

Semi-naive fixpoint (`chain/chain`), with **one agenda for every forward rule,
strict and defeasible alike**. A newly asserted **fact** fires rules keyed
by its predicate *and its supertypes* (specificity); a newly asserted **rule** is
joined over existing facts. Each full match records a `Justification` (including
the rule handle) and places the consequent in its placement contexts (see
[contexts.md](contexts.md)), at the firing rule's own **strength**: `:monotonic` for a
bare rule — which adds no defeasibility, so the conclusion is capped at its weakest
antecedent — or `:default` when the rule is defeasible. `rule-view-of` reads that off the record's
`:defeasible` field, the same authority `:direction` is read from — a rule needs no
index entry to know how it fires.

**There is no separate defaults phase, and adding one is the trap here.** Defaults
look like they need their own rounds — derive the strict consequences, then the
defeasible ones, then re-run the strict chainer over what that produced — and a phase
built that way cannot use the agenda, because the datums it must revisit are the ones
already believed. It degenerates into re-solving *every* default rule as a full
unindexed join over all facts, per round: a single defeasible rule then makes every
assert a full KB scan, and loading N facts costs O(N²).

Nothing is bought for it. One agenda is **semantically neutral** against two phases,
and the reason is narrow enough to state exactly: a default conclusion is placed
*unconditionally*, and whether it survives is decided later by `settle` from
recomputed belief. Phase ordering therefore cannot affect *what* is derived, only how
expensively it is found — either scheme computes the least fixpoint of the same
monotone immediate-consequence operator. The one thing separate phases are reaching
for is that a **strict consequence of a default conclusion** still gets derived, and a
unified agenda gets that for free: the default conclusion lands on the agenda and
triggers strict rules like any other new datum. A default rule's truncation reaches
the run's `:truncated?` flag on the same path as any other rule's.

**Connected conjunctive antecedents.** Antecedents that share a variable **join** —
a binding from one match is carried into the next. The starter leans on this:
`(implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z))` joins on
`?y`; a transitive `locatedIn` plus `(implies (and (partOf ?part ?whole) (locatedIn
?whole ?place)) (locatedIn ?part ?place))` puts a part wherever its whole is; and
`(implies (and (owns ?p ?whole) (partOf ?part ?whole)) (owns ?p ?part))` propagates
ownership to a whole's parts (its placement is context-sensitive — see
[contexts.md](contexts.md)). The `vaelii.world-fables` stories derive their morals the
same way — a 2- or 3-antecedent join over the tale's facts.

**Antecedents nothing stored.** Two kinds of antecedent are satisfied by content that
has no handle to be an antecedent *of*: a relation a constraint network entails
([qcn.md](qcn.md)) and a claim argument-position preservation licenses
([inherit.md](inherit.md)). Both are answered the same way, in `chain/join-antecedent`
and beside the ordinary matcher rather than in place of it: the join contributes the
handles the answer was **read from**, so the firing's justification names them, the
conclusion is withdrawn when any of them goes, and placement sees where they live.
Both also need a trigger the predicate-keyed index cannot give — the arriving sentence
need not unify with the antecedent it enabled — so both re-join their rules in full and
drop them from the trigger set. The deferred (evaluable) path does neither and correctly
does not try: `(lessThan 1 2)` is a function of the bindings, where an entailed or
inherited claim is a function of what is stored.

**Recursion guard:** a derived datum carries a depth (`1 + max` antecedent
depth); a derivation past `:max-depth` (default 64) is skipped and the run flagged
`:truncated?`, with `:max-derivations` as a hard backstop. Re-deriving an existing
sentex only adds a justification (never re-enqueues), so cyclic non-productive
recursion terminates.

## Incremental rule matching (`vaelii.impl.rete`)

The reference chainer re-joins a candidate rule's non-trigger antecedents against the
store on every assert, through `res/match-pattern` (the count-aware trie). The trie
narrows strictly left to right, so a non-trigger antecedent with a **leading
variable** — `(parentOf ?x Pi)`, the second half of a grandparent join — has no
selective prefix. The **secondary argument roots** answer it instead, by one set
intersection rather than a fan-out over every first-argument value
([indexing.md](indexing.md), "Argument-root retrieval", `res/*arg-root-retrieval*`,
on by default), so that shape is flat in the extent on the reference path.

`vaelii.impl.rete` is an opt-in **TREAT-style alpha network** over the same question.
It keeps the stored facts in RAM — grouped by functor and indexed by argument value,
the *alpha memories* — and answers a non-trigger antecedent by a hash lookup on its
most selective ground argument. What that is worth depends on the rule shape, and the
two measurements bracket it. On the grandparent load (`lein bench-forward`, a 2-join
and a 3-join over a sparse random parent graph) the two paths are level from n=2000
up, both flat at ~500µs/fact with identical derived counts and RAM — the argument
roots already answer what the alpha memories would. On the OpenRuleBench join pyramid
(`vaelii.bench.pyramid` at join.1k, C2, six interleaved runs a side) the alpha memories
hold a thin lead on the identical answer set: 11.8s against 12.5s. Matching is ~12% of
that run (the rest is placement), which is the ceiling on what any matcher moves there.

**One seam, one novelty.** The only thing the network changes is *which stored facts a
non-trigger antecedent finds*. Forward chaining looks them up through a dynamic
`chain/*matcher*`, whose default is `res/match-pattern` (the reference path,
unchanged). `rete` binds it to a matcher that returns the **identical set** —
`rete-match-pattern` mirrors `match-pattern`/`raw-match`/`match-one` line for line
(belief filter via `jtms/in?`, polarity, the symmetric mirror, sub-predicate fan-out at
every arity,
the `?ctx` context binding), differing only in the candidate *source*: a RAM bucket (a
superset of the trie hits) filtered by the identical `unify`. So the agenda, the trigger
match (`match1`), context placement, `exceptWhen` blocking, the definitional checks,
justification dedup, functional twins, and the depth guard are all the reference's,
reached by binding one var and calling `chain/chain-all` unchanged. The network decides
which firings are new; the reference does everything else.

**Belief is not baked into the memories.** A datum stays in its alpha memory when it is
defeated or superseded; `in?` is consulted at read time exactly as `match-one` does. So
a belief flip needs no memory update — the only structural mutations are a stored fact
arriving (`kb/create-sentex`) or leaving (`integrate/sentex-removed!`), routed to the
network through the leaf `vaelii.impl.observe` seam so no require cycle forms. Subtype and
symmetric resolution also happen at read time over the live taxonomy, so a `genl` or
`symmetric` edge change needs no memory update either.

**Correctness is gated by an oracle**, the same discipline the taxonomy closures get:
`rete_oracle_test` pins `rete-match-pattern`'s set-equality against `match-pattern`
directly, and the derived sentex + justification sets end-to-end against the reference
`chain` over randomized assert/retract sequences, with targeted tests for recursion +
the depth guard, `exceptWhen`, a deferred antecedent, a symmetric non-trigger antecedent,
a functional twin, sibling-context no-placement, and retraction. The whole suite also
runs through it (`VAELII_RETE=1 lein test`) with a failing-set identical to the reference
path. It is **off by default** (the reference matcher is the root of `chain/*matcher*`);
`(rete/enable!)` installs it globally, `rete/chain-all` / `rete/track!` drive one KB.
There is no **beta network**: TREAT re-joins from the alpha memories on every firing,
so a repeated multi-way join is recomputed rather than cached.

## What a run pays per witness (`chain/*agenda-arrivals*`)

A conclusion reached k ways costs k **firings**, and the cost of a firing is not the
join — it is what happens after one: placement, the definitional checks, the JTMS node,
the justification. So a firing is worth generating once. Measured on the OpenRuleBench
join pyramid at 1k (the field bench's W4 cell: five base relations of 1,000 pairs, four
rules, 65,236 derived facts), one run stores **428,900** justifications, 6.6 per derived
fact — one per distinct witness, which is what a JTMS is for: a conclusion with k
justifications survives the retraction of any one of them.

**One firing per combination** (`chain/*agenda-arrivals*`). A rule
`a(x,y) ← b1(x,z), b2(z,y)` is triggered by its `b1` datum at position 0 and by its `b2`
datum at position 1, and both enumerate the same pair — the second runs the whole join,
rebuilds the same conclusion, resolves the same placement contexts, and is thrown away
by `jtms/has-justification?`. `chain/chain` therefore stamps each datum with the
position at which it joined the agenda, and `complete-antecedents` admits at the other
antecedents only facts that arrived **no later than the trigger**, so every satisfying
combination is enumerated by the trigger holding the latest arrival among its facts and
by no other. Attempts fall from 884,379 to 462,150 at 1k (duplicates 51.5% → 7.2%), for
the identical 428,900 justifications: 13.4s against 10.2s on the W4 cell, six
interleaved runs a side.

This **decides work, not belief.** The firing that survives is the firing the other
trigger would have made — same bindings, same antecedent set, same justification — so
the derived set and its supports are the same either way, and nothing here is read when
belief is computed. `chain/*suppress-duplicate-firings*` bound **false** enumerates
every trigger, which is the reference `witness_order_test` and `rete_oracle_test`'s
third oracle compare against, and `vaelii.bench.pyramid`'s `-nosup` modes measure.

The order is the run's **arrival** order and not the creation order the handles carry,
because a datum can be put *back* on the agenda with an old handle: a fact revived from
OUT, a fact newly matchable under a `genl` edge the run itself derived
(`special/subsumption-seeds`), a seed list in whatever order `jtms/in-datums` produced.
Stamped on arrival, such a datum sorts after the partner already processed and so is the
one that enumerates the pair. Four things then decline the filter outright, each because
a firing there is enumerable at one trigger and not at the other:

- **A handle the run never enqueued** has no arrival — the equality twins
  `special/derive-functional-equalities` places, and every join outside a run.
- **A disbelieved trigger.** A datum triggers on `res/match1`, a plain unify; the join
  finds facts through `*matcher*`, which follows belief. So a spelling superseded by an
  equality merge still fires its rules while no other trigger's join can find it.
- **A mirrored antecedent** — a binary literal whose predicate is `symmetric`. The join
  probes both argument orders (`res/raw-match`) where the trigger unify does not, so a
  mirrored hit is a firing the join can make and the arriving datum cannot.
- **A qualitative antecedent**, whose handles are the support of a network entailment
  rather than the fact that satisfied the position, and `rejoin-qualitative`, which
  re-joins over the pairs that moved rather than at a trigger position at all.

A `<=` at every position rather than a `<` after the trigger admits one combination
twice, the **self-join** where one fact satisfies two positions of the same rule and
ties with itself; both of its triggers build the identical justification and the dedup
rejects the second.

Two further per-witness costs are paid once a run rather than once a witness.

**The stored-handle cache.** `place-conclusion` opens by asking whether its conclusion
is already stored (`kb/find-sentex-handle`), which canonicalizes the sentence and walks
the trie — for a handle the run itself minted moments earlier. `observe/*handle-cache*`
is a positive memo over that lookup, bound for the length of a run by `chain/chain`
(`observe/with-handle-cache`). Three things make it safe to believe:

- **Only hits are cached, never misses.** A sentence absent now is one a firing is
  about to store, so a cached absence would be wrong within microseconds; a cached
  presence stays true until the sentex is removed.
- **Removal is a choke point.** `integrate/sentex-removed!` drops the entry, so the
  invalidation lives beside the event rather than in whichever caller has a cache bound.
  (Within a run there is nothing to invalidate — `settle` runs after chaining, not
  during it — but the cache is correct without leaning on that.)
- **Every entry is stamped with what canonicalization reads off the KB**, which is one
  thing: the set of predicates declared `symmetric` (`kb/canon-stamp`, consumed by
  `res/kb-sentex`). A raw sentence reaching a *different* canonical form — a
  `(symmetric p)` declaration arriving, leaving, or changing belief — replaces that set,
  and a stamp mismatch empties the map. Nothing else in a sentex's key is a function of
  the KB, so nothing else can go stale.

**Justification dedup, indexed for the length of a run.** `has-justification?` asks
whether a conclusion already rests on exactly these antecedents, and a conclusion
re-derived by k witnesses is asked once per witness. The reference answer scans every
justification the conclusion already holds — Θ(k²) `same-antecedents?` comparisons
apiece, testing mutual containment by index rather than building two hash sets, which
allocates nothing and is a large line in the W4 profile (~430k firings over ~66k
conclusions at 1k). `jtms/*dedup-cache*`, which `chain/chain` binds for the length of a
run, builds each conclusion's key set from `-supports` on the first ask and answers
every later one in a single hash probe.

That cache is one of three fast paths on the placement path, with the `ensure-node`
no-op skip and the single-context placement answer; `observe/*chain-fast-paths*` is the
one switch over all three, and binding it **false** runs the reference paths instead.
Each is a pure cost decision that computes exactly what its reference computes, which is
what `chain_fast_paths_test` compares and what `vaelii.bench.pyramid`'s `-ref` modes
measure. `handle_cache_test` is the gate on the handle cache — its transparency, its
three invalidation cases, and a join pyramid checked for exactly one justification per
distinct witness. The two switches are independent, and the W4 fixpoint is
content-identical under all four settings of the pair.

## Predicate subsumption in matching

Matching fans the **functor** out over its genl spec closure, so a supertype is met
by its subtypes and — the same closure, one dimension over — a super-*predicate* by
its sub-predicates. The type case is the familiar one: `(animal ?x)` is satisfied by
a stored `(dog Muffet)`. Generalized to every arity, `(parentOf a ?x)` reaches a stored
`(fatherOf a v)`, and a `(parentOf ?x ?y)` rule antecedent fires on a
`(fatherOf Tom Bob)` fact, once `(genl fatherOf parentOf)` holds.

No new taxonomy state carries this. `wff` already accepts a genl edge between
predicates (it only forbids individuals), so the edge flows into the existing genl
closure and follows belief like any other — retract it and the subsumption is gone.
The whole change is `res/match1` and `res/match-pattern` reading `specs(functor)`
for all arities instead of only unary: when the functors are equal, or the
antecedent's functor has no sub-predicates (a singleton closure — the overwhelming
common case), it degenerates to a plain unify, so a KB with no predicate-genl edges
is unaffected. `fire-rules-for` already fans the *fact's* functor up via `genls` to
find candidate rules, and `match1` agrees with it — which is what completes the
forward-chaining subsumption an exact-functor unify rejects. `predicate_subsumption_test` pins
both directions (it is one-way — a sub-predicate satisfies a super, not the reverse),
forward chaining and `ask` reaching through it, belief-following on retract, and that
`match-pattern` equals exactly the union of raw matches over the spec closure.

**What already fired follows the edge too.** A subsumption match is a use of the edge,
so the firing's justification names a witness for the `genl` path it climbed
(`taxonomy/reach-support`, one supporter per edge, drawn from what the conclusion's
placement context can see) beside the fact and the rule. Retracting the edge therefore
withdraws the conclusion through the ordinary dependency-directed sweep, and `why`
shows the edge as one of the things the conclusion rests on rather than leaving the
reader to wonder how a `fatherOf` fact satisfied a `parentOf` antecedent. See
docs/contexts.md for the placement half and `subsumption_support_test`.

**Backward chaining has the dual.** `fire-rules-for` fans a *fact's* functor **up**
over `genls` to find rules whose antecedent it triggers; the mirror image is that a
rule concluding a *spec* of a **goal's** predicate answers the goal — a `(dog ?x)`
conclusion satisfies an `(animal ?y)` goal. So `candidate-rules` draws its candidates
from `res/concluding-rule-handles`, the intersection `specs(pred) ∩
rules-by-consequent` (iterate the small spec closure, probe the consequent index —
bounded by the number of concluding rules, never the taxonomy), and both chainers
(`prove` and the node engine) unify the goal against the consequent with
`res/subsuming-unify` — `match1` with the roles swapped, binding the goal variable to
the subtype instance. Exact-functor and inert cases still degenerate to a plain
`unify`. A supertype-concluding rule does **not** answer a subtype goal (the
one-wayness again), and the whole thing follows belief through the same closure. In the
default assert-then-query flow a forward-capable rule has already materialized the
subtype conclusion, so this only *adds* answers where forward has not run it — a
backward-only rule, `{:chain? false}`, or a goal past the forward run's depth.

This is the predicate dimension of the hierarchical query `(p a ?x)@c`; the context
dimension is the genlContext up-closure (`matches-visible`), and both are answered
efficiently by the set-algebra retrieval in [indexing.md](indexing.md), "Retrieval
from the roots".

## Backward chaining

**Two chainers**, both type-aware (specificity) and context-aware (`matches-visible`):

- `prove` — a `loop`/`recur` DFS over an explicit goal stack, with a per-path `seen`
  set of variable-collapsed goal keys so recursive rules terminate. A key keeps its
  *ground* arguments, so a recursion that walks a chain keeps expanding while one that
  re-asks the same open goal is cut. `provable?` is the boolean form.
- **the node engine** (`vaelii.impl.inference`) — a frontier of whole conjunctions
  ordered by cost, described below. `core/query` routes to it when given a
  `:max-depth`.

### The loop guard's scope is the subtree, not the frame

The `seen` set guards a goal against re-expanding **itself, below itself**. That is a
claim about a path, and a frame is not one: `prove-from` expands a goal by pushing a
single frame holding both the rule's antecedents and the conjuncts still queued behind
the goal, and those queued conjuncts are **siblings** of the expansion, not descendants
of it. Growing the guard for the whole frame would therefore charge a later conjunct for
a goal key an earlier one claimed, and a conjunctive query would answer less than its
own conjuncts do — `[(anc Tom ?y) (anc Tom ?z)]` empty where `(anc Tom ?y)` answers
twice, with `provable?` saying false and `prove-within` reporting `:status :complete`.

So the scope an expansion started from is **restored at the point that subtree ends**,
by a marker pushed behind the antecedents: one stack entry per firing, the same
mechanism and the same cost as the `exceptWhen` guard. The guard stays a statement about
descent, which is the only thing it is sound to be.

This is also why the planner cannot be allowed to change an answer. Reordering conjuncts
moves which one claims a key first, so a guard scoped to the frame would make
`plan/*enabled*` semantic rather than a cost decision, and adding facts could make a
query stop answering. Scoped to the subtree, the order conjuncts are tried in is free.

`ask` is **not** a third. It is the prover registry, and no member of the registry
expands a rule — which is what makes it the thing a closed-world reader can run from
inside a relabel loop, and what makes its cost a property of the goal rather than of
the rule graph.

`core/query` is the door in front of both, and `:max-depth` is the whole of what it
decides. A depth and it is the node engine, bounded there. No depth and it is the
registry alone — through `ask` for a single literal, and for a **conjunction** through
the DFS at depth 0, which is the registry as a leaf under a bound admitting no rewrite.
That last case is not a third semantics but the same one: a conjunction needs no rule to
be a conjunction, it needs its bindings threaded across conjuncts, and one `ask` per
literal cannot do that.

### The two side by side

They differ in **what a unit of work is** — a stack frame, or a whole conjunction — and
almost everything else follows from that.

| | `prove` (the DFS) | the node engine |
|---|---|---|
| **state** | an explicit goal stack | a frontier of nodes |
| **unit of work** | one stack frame | one whole conjunction |
| **structure** | path | set |
| **recursion** | `loop`/`recur`, heap | `loop`/`recur`, heap |
| **leaf** | stored facts, or any `:leaf-solver` | stored facts, or any `:leaf-solver` |
| **conjunctive query** | yes, a vector | yes, a vector |
| **laziness** | the loop is eager; `prove-seq` drives it lazily a solution per pull, and `prove-within` bounds and resumes | lazy, one node per pull |
| **termination** | per-path `seen` **+ optional `:max-depth`** | **the depth bound**, and nothing else |
| **deep chains** | 2000 fine | bounded by depth |
| **variables** | one flat map + `freshen-rule` | a namespace per node |
| **repeat work** | re-derives across branches | claimed keys, globally |
| **duplicate answers** | possible | deduped |
| **order** | rule/index order | a **policy** (`tactics`) |
| **continuation** | the goal stack | the session, a value |
| **artifacts** | dead ends (`*dead-end*`) | the whole search tree |
| **returns** | binding maps | binding maps |

**The leaf is a parameter, and it is where the two stop being about rules at all.**
`prove-from` and the node engine both take a `:leaf-solver` — how a literal the search
will *not* rewrite gets answered. nil is `matches-visible`, the stored facts, which is
what `prove` means by a leaf. `core/query` passes `provers/solve-goal` instead, so an
antecedent is answerable by transitivity, an evaluable, a calculus or an inferred
argument type. One engine, two leaf semantics; there is no third chainer that exists
only to reach the registry.

That division is load-bearing. A leaf that itself backchained would run the engine's
rewriting *plus* a nested search per binding under it. Measured on a converging DAG
(every node with two parents), against `ask`'s 6.7 / 3.9 / 4.0 ms:

| leaf solver | | |
|---|---|---|
| stored facts (`matches-visible`) | 6.5 / 4.5 / 5.4 ms | level with `ask` |
| the registry, which expands no rule | 5.2 / 6.4 / 9.6 ms | level with `ask` |
| a leaf that backchains too | 150 / 411 / 700 ms | 24–73× worse |

**Conjunct order is not a thing either of them can observe.** A rule's antecedents are
put into canonical order at *storage* (`sentex/canonicalize-rule`), so the same rule
written with its recursive literal first and last stores identically, and both engines
return the same answer set for either spelling with the planner on or off.
"Left-recursive" is not a state a rule can be in here; `plan`'s pinning of the recursive
literal keeps the *cost model* from re-introducing one.

**Neither answer is a justification.** By default both return binding maps and nothing
else, and a backward answer is *ephemeral*: it is not stored and has no handle. `query`
under **`{:proof? true}`** changes the result shape to `[{:bindings … :proof …}]` and
hands back one justification tree per answer, reading the way `why` does (`:goal` /
`:via` / `:because`). It needs a depth — without one no rule was expanded and there is
no derivation to show — and the tree is a record of that search, not a stored
justification anything else can read. `why` / `why-not` explain a **stored** belief by
reading the JTMS, which is a different question about a different object: what forward
chaining and `assert` left behind, not what a query just computed.

**Which to reach for.** `prove` terminates on the *data*: a chain of length n finishes
after n steps whatever bound it was given, so it answers a derivation deeper than any
number you would have guessed. It is also the bounded-and-resumable one, and the only
one that reports dead ends, which is what abduction listens on (`abduce`). The node
engine trades a hard depth ceiling for set-at-a-time evaluation: its residual stays
symbolic, so its node count is a function of the rule graph rather than of the data, and
a frontier is a thing you can *order*.

**Measured, on the same KBs** (`lein bench-tactics`, and the table further down):

| | `prove` | node engine |
|---|---|---|
| open query, wide data | baseline | **2–6× faster** |
| bound query | **baseline** | 2–4× slower |
| conjunctive query | **baseline** | 2–3× slower |
| time to first answer, shallow needle | **baseline** | 1.4× slower |
| time to first answer, deep needle | baseline | **on par** (1.01×) |

The pattern is one thing said twice: **the node engine's advantage is throughput and the
DFS's is latency.** A symbolic residual amortizes over many answers, so it wins where
there are many; a needle has one answer and nothing to amortize over, so the path
engine's straight dive wins — but only while the derivation is shallow enough that it
does not start re-deriving across branches, which is gone by depth 6.

Both evaluate a **deferred** antecedent (`different` / `evaluate` / `unknown`) by
*computing* it through the registry (`res/solve-deferred`) rather than matching or
expanding it. `resolution` sits below `provers`, so it reaches `solve-goal` through
`wiring/solve-goal` (resolved once into a `delay`) rather than on a thread binding, which
would be lost inside a lazily realized seq; an optional
`*deferred-solver*` var overrides it. Without this, a chainer silently proved nothing
for a rule with such an antecedent while forward chaining honoured it (docs/naf.md).

### One search scope per run (`observe/with-search-scope`)

A search opens two things for its length and closes them after: the resident-value
**pin** (`observe/*pin*`) and the transitive-closure **memo**
(`observe/*reach-memo*`). They travel together because a search is where both problems
appear at once — a rule's join solves one antecedent per binding of the join variable,
so the closure walk repeats over nodes those bindings share, and a caller placing
conclusions as it consumes the join would otherwise re-derive a network per solution.

The scope is one **search step**: one `prove-from` call (a `loop`, eager throughout) and
one node expansion for the node engine (`step!`, which reduces its solutions to a vector
before returning). Both compose with an outer scope rather than shadowing it, so a nested
expansion shares what its parent already paid for. The macro's one precondition is that
its body be **eager**: a lazy seq escaping the scope realizes later with the bindings
gone, which for the memo is a silent slowdown and for the pin is a join against a state
that moved.

A step rather than a query, because that precondition and laziness cannot both hold any
wider. `prove-seq` drives the loop in several calls, so a lazily consumed search opens one
scope per pull: the memo starts empty each time and resident values are re-read rather
than held across the seq. That is sound for a read — a query mutates no belief, so there
is nothing for the pin to hold still against, and what it buys there is only that a
consumer placing conclusions off the seq joins against one state per segment. An eager
`prove` keeps one scope and pays for the memo once, which is why it remains the call for
wanting the whole answer set.


### Each rule instance gets its own variables

A rule's variables are the rule's own, and every *use* of it needs a private set. Both
chainers here thread **one** binding map down a derivation path and hand it to every
expansion on that path, so the second use of a rule meets its own first use's bindings:
`(anc ?x ?z) :- (parentOf ?x ?y) (anc ?y ?z)` expanded twice asks `unify` to make `?x`
both the grandchild and the child. It cannot, the branch is dropped, and an ancestor
query answers at distance one — a wrong answer, not a slow one. The same collision
reaches sideways: an inner rule with a variable the outer rule has not bound yet (an
existential in its antecedent) binds the outer rule's still-unsolved conjunct.

Colliding is the normal case, not the unlucky one. A stored rule is spelled `?var0
?var1 …` (`sentex/canonicalize-rule`), so every rule in the KB draws its names from one
small pool — and a caller may write those names too.

`res/freshen-rule` renames each instance clear of every name already in play on the
path: what the bindings speak for, the goal's own variables, and the conjuncts still
queued (outer rules' unsolved antecedents). Names come from the `?v'`, `?v''` … series
rather than a gensym, so the binding maps `prove` returns are the same on every run of
the same query. Nothing is renamed when nothing clashes, which is the top-level
expansion of every query and every rule used once per path.

The node engine has no such shared map — every node carries a namespace of its own, and
a rule is numbered *past* the node it rewrites, so the two are disjoint by construction
and nothing has to be renamed apart. Rule variables are internal to an expansion; once
the argument is complete they name nothing the asker knows, and letting them out is how
they collide. The node's `:answer-terms` is the only record of what the asker called
its variables, which is why reading an answer out is resolving those terms and nothing
more.

`prove` also carries the seam **abduction** listens on. `res/*dead-end*` observes the
subgoals it could neither match nor expand — nil by default, and a sink rather than a
filter, so an observed run takes a byte-identical path. A branch cut short by the `seen`
guard or by `:max-depth` deliberately does *not* report: that is a search out of budget,
not out of knowledge. Only the DFS reports, for the same reason `*deferred-solver*` is
awkward anywhere lazy — a thread binding does not survive a lazily realized seq. See
[abduction.md](abduction.md).

## The node engine (`vaelii.impl.inference`)

The other chainer is **path**-structured: `res/prove` / `prove-from` walks an explicit
goal stack. This one's state is a set of **nodes** ordered by cost, where a node
is an entire conjunction plus everything accumulated to reach it, and expanding one is a
single rewrite:

```
node:   [ L₁ … Lᵢ … Lₙ ]                    σ
rule:   A₁…Aₖ ⟹ C,   with  b = unify(Lᵢ, C)
child:  [ b(L₁) … b(Aᵢ…) … b(Lₙ) ]          σ ∪ b
```

The rule's antecedents under the head unifier are the **residual** — what is left to
prove if this rule fires — spliced in where `Lᵢ` was. Applied repeatedly that is the
whole search: every node is the query rewritten through some sequence of rules, and a
node whose conjunction solves against facts alone is a completed proof. Popping a node
does two things in order: solve its conjunction inline at depth 0 (`plan/order` over
`matches-visible`, with a deferred literal computed through the registry and never
rewritten), then build its residual children.

Three things it does differently, each because a node has no rule frame to hide in:

- **Every node is a canonicalized conjunction** (`sentex/canonical-conjunction`), so each
  node has a variable namespace of its own: `?var0 ?var1 …`, numbered by first occurrence
  across the whole conjunction. A rule is numbered **past** the node's variables before
  anything is unified, which makes the two namespaces disjoint by construction — a stored
  rule is spelled the same way, so without that step every rule would collide with every
  node and with every other rule. The path-structured chainer threads one namespace down
  a whole derivation and so needs `res/freshen-rule` to rename instances apart; this one
  does not, and does not use it.
- **A guard is asked at the node's own solve**, which is the moment the argument is
  complete. `prove` reaches that moment by pushing a marker behind the antecedents; a
  node is already there.
- **Rewriting runs left to right and never backwards.** A conjunction is commutative, so
  rewriting literals 1-then-2 and 2-then-1 reach the same node by two routes; without a
  canonical order the frontier carries every interleaving. On a two-literal ancestor
  query that is 241 nodes against 49.

**Depth is per literal**, not per node: each conjunct carries its own remaining budget,
decremented only for the one actually rewritten, so the conjunct expanded first cannot
spend the whole allowance the way a single per-frame depth lets it.

Dedup is global rather than per-path — a key is claimed with a compare-and-set before a
node is enqueued, and a second arrival at an equivalent node is dropped. The key is the
node's literals, their depths, the map back to the asker's variables, the **set of
pending guard identities**, and the rewrite window. Identities, not a count: two distinct
rules each carrying its own `exceptWhen` can rewrite one goal to the same canonical
residual — through the `genl` fan — and a count reads those two children as one key, so
the second is dropped before it is enqueued and every answer only its exception admits is
lost. Each guard carries the rule it came from, which is what makes the two keys
distinct. The literals need no renaming to compare: they are
*already* canonical, which is what canonicalizing them is for, so two alpha-variant
conjunctions are one key with nothing further done about it. The map is in the key
because one conjunction can be asked **on behalf of different answers** — one path's
`?var0` is the asker's `?x` and another's is `?y` — and collapsing those loses an answer
set.

The price of a namespace per node is that nothing crosses between two of them for free.
Each node carries `:answer-terms` — the asker's variable to the term it stands for in
*this* node's numbering — and every rewrite **pushes** that map forward (`push-terms`):
each term is substituted through the head unifier, then renamed into the child's
canonical numbering. A **term** map rather than a variable map, because a rewrite can
*ground* what the asker asked about — unifying `(flies ?var0)` against a rule head for
the goal `(flies Robin)` leaves a child conjunction with no variable in it — and a map
carrying only the surviving variables would drop the answer at exactly the rewrite that
produced it. A solution is read out by resolving those terms against it
(`resolve-terms`); each pending guard carries a map of its own rule's names, pushed by
the same call and resolved the same way when the guard is asked.

The renaming half is `sentex/rename-vars`, applied in **one pass** — these maps are
permutations, and canonicalizing a query that already uses the canonical names, crossed
over, yields `{?var0 ?var1, ?var1 ?var0}`, which the chasing `res/substitute` would
follow forever (it raises `StackOverflowError`, which `canonical_vars_test` pins). A
renaming and a substitution look alike and cannot share a function.

Answer projection falls out of this rather than being enforced: a rule's own variables
are named by nothing above the rewrite that made them, so `:answer-terms` has no key for
them and they are dropped on the way up. There is no basis to carry and nothing to
exclude by name. The unifier binds *our* variable to the rule's (`subsuming-unify` tests
the goal side first), which leaves the rule's variable carrying our identity — so each
rewrite records the aliases it created, or the link to the parent is dropped silently and
an answer goes with it.

### What it buys, and what it costs

Measured against the DFS on the same KB:

| shape | nodes | `prove` | node engine |
|---|---|---|---|
| kinship DAG, 16 leaves, open | 7 | 4.80 ms | **2.06 ms** |
| kinship DAG, 64 leaves, open | 7 | 14.45 ms | **2.48 ms** |
| same-generation, open | 9 | 17.24 ms | **5.83 ms** |
| kinship DAG, head bound | 7 | **0.31 ms** | 0.83 ms |
| two-literal conjunction | 49 | **8.69 ms** | 28.66 ms |

The residual stays **symbolic** — `(anc ?y ?z)` is rewritten once, not re-asked per
binding of `?y` — so the node count is a function of the rule graph and the depth bound
and not of the data: the same seven nodes answer 16 leaves and 64. Each node's
conjunction is then one planned join rather than a tuple-at-a-time walk, which is where
the 2-6x on an open query comes from. A **bound** query loses, because the rewrite
ignores what the caller already knows and computes the relation before filtering it; a
conjunctive query loses further, having more ways to be rewritten.

The claimed-key set, notably, contributes almost nothing on these shapes: it fires on a
rule diamond and nowhere else, because a symbolic residual never creates the duplicate
that dedup exists to remove. Both economies are real; only one of them is the mechanism
the design is usually justified by.

### Which node pops next is a policy (`vaelii.impl.tactics`)

The frontier is a priority queue, so the ordering is a **number** rather than a
structure. That number is four additive terms:

```
estimate(node) = Σ literal-cost(Lᵢ)                     what the conjunction costs
               + size-penalty × |literals|              shorter conjunctions first
               + depth-sign × depth-weight × Σ dᵢ       rewriting allowance left
               + tree-sign  × tree-weight  × tree-depth search-tree level
```

The base term is the KB's own cost model and not a second one: `plan/explain` summed, so
each literal is estimated under the variables the literals ahead of it bind and the total
equals what `core/query-plan` prints for the same conjunction. One model, two readers.
The join *inside* a node stays strategy-blind (`plan/order` alone), because a complete
search has to visit the same literals whatever order nodes pop in.

A tactician is a pair of signs and a child bias, nothing more:

| tactician | depth | tree | pops first |
|---|---|---|---|
| `:cost` | 0 | 0 | the cheapest conjunction, and nothing else — the identity policy |
| `:budget-first` | −1 | 0 | the node with the most rewriting allowance left |
| `:ground-first` | +1 | 0 | the node closest to spending it, hence nearest to ground — **the default** |
| `:breadth-first` | 0 | +1 | level order |
| `:depth-first` | 0 | −1 | the deepest node — a dive |
| `:removal-first` | 0 | 0 | + a productive node's children sink |
| `:transformation-first` | 0 | 0 | + a productive node's children rise |

The last two act through a **child bias** — a large additive number applied at enqueue,
so `+bias` sinks a child behind the whole frontier without dropping it and `−bias` hoists
it. That is the only removal-versus-transformation distinction this engine has to offer:
a node solves its conjunction inline and rewrites it into children in one step, so there
are no two classes of child to choose between, only two readings of a parent that is
paying — finish it, or chase it. `:breadth-bias` scales the depth term for tuning without
a new tactician.

**Ordering is a cost decision and never a semantic one.** All seven return the same
answer set; only arrival order differs, and
`every-complete-tactician-returns-the-same-answers` is the gate — with the whole suite
behind it, since `VAELII_QUERY_STRATEGY=breadth-first` beside `VAELII_QUERY_ENGINE=inference`
runs all 2,426 tests under a different ordering and must be failing-set-identical. The one mode that
returns *fewer* answers is `:first-result?`, which stops a productive node building
children at all: it says so in its docstring, `tactics/complete?` reports it, the
portfolio refuses to race it, and the completeness sweep excludes it by name rather than
quietly failing on it.

Two knobs are off by default because they cost more than they decide. `:estimate-backchain?`
costs a literal through the rules that conclude it (`:first` takes the min — any one rule
suffices; `:all` the sum — a complete search runs them all; a repeated goal caps the
recursion). It exists because the index costs a **rule-only** predicate at zero, ranking
the most expensive literal in a conjunction as the cheapest — and it is a sub-search per
enqueued node, so it is asked only of a literal that still has allowance. `auto-strategy`
picks a tactician from the shape of the query in one index read: no allowance at all →
nothing to order; a conjunction or a literal several rules conclude → portfolio; one
route → dive.

`inference/portfolio-solutions` races whole searches and unions them. Its limit is the point
of it: **each racer is a complete search, so the union equals any single racer's answer
set** — diversity buys latency, not completeness. Racing is safe only because a query
here writes nothing; a search that wrote would have to stay out under the single-writer
contract (see [storage.md](storage.md)). A race is also not an *anytime* mode: it is
driven to completion before it can be unioned, so it has no partial answer to hand back,
and `prove-within` drives the ordinary stream instead.

### What an ordering is worth (`lein bench-tactics`)

The validator runs every mode over one query set, checks each answer set against the
`:cost` baseline, and then measures. Its first result is the completeness invariant
showing up as a number: over seven backchaining-heavy goals **driven dry**, every mode
expands the same 480 nodes for the same 742 answers within 0.98–1.01×. An exhaustive
search is the same search whatever order it runs in, so ordering can pay only a consumer
that stops early.

Bounded, over ten goals on a 1200-fact / 400-rule layered corpus — at the first answer
(**ttfa**) and at the first fifty, against `:cost` as the reference:

| mode | nodes → 1 | ttfa | nodes → 50 | to 50 |
|---|---|---|---|---|
| `:ground-first` | **2.9** | **0.47×** | 13.9 | 0.93× |
| `:cost` + `:estimate-backchain? :all` | **2.1** | 0.52× | **8.4** | 0.82× |
| `:cost` + `:estimate-backchain? :first` | 2.3 | 0.60× | 13.7 | 0.82× |
| `:cost` | 5.3 | 1.00× | 28.3 | 1.00× |
| `:depth-first` | 4.5 | 1.03× | 40.8 | 9.54× |
| `:breadth-first` | 5.5 | 1.47× | 11.2 | **0.81×** |
| `:budget-first` | 9.9 | **15.87×** | 36.9 | 10.31× |

**The two columns want opposite orderings, and that is the finding.** Level order is the
best way to collect fifty answers (0.81×) and among the worst ways to find one (1.47×):
the shallow nodes are the cheap ones and enough of them are productive, which is exactly
the wrong instinct when the only answer is deep. `:budget-first` is the pathological case
in both directions — preferring the node with the most allowance left is preferring the
least-rewritten node, which is the one furthest from an answer, and it costs **15.9×** on
ttfa. A single fixed priority function cannot serve both columns, which is the whole
argument for the frontier order being a policy.

`:ground-first` is the only tactician best-or-tied on every column measured, and is
therefore the default.

The **backchain estimate earns its overhead** where a query has many answers: it cuts
nodes-to-50 by 3.4×, because without it a rule-only predicate costs zero and the frontier
chases the literal that can least afford it. On ttfa it buys fewer nodes but not much
time — with one answer to find there is nothing to amortize a sub-search per node over,
and its own cost lands on the critical path.

Two tacticians are **unexercised by this corpus** and read exactly 1.00×: `:removal-first`
and `:transformation-first`. Their bias applies to a productive node's children, and in a
stratified corpus a node produces answers precisely when its literals have reached the
band no rule concludes — so it has no children to bias. A predicate carrying both facts
and rules is what exercises them, which is what the unit test builds and this corpus does
not; the bench says so rather than reporting a tie as a finding.

### The needle: which *engine*, not which ordering

A corpus query has hundreds of answers, so ttfa on it is still a throughput measurement in
miniature. The test that isolates latency is a goal with **one** answer, deep, among
decoys that look identical to the cost model — each decoy chain bottoming out in a real
join over the haystack against a disjoint individual set, so it does index work and yields
nothing. The true rule is asserted between the decoys at every level, so no engine finds
it by insertion order. Time to that one answer, against `prove`'s DFS:

| needle depth | `prove` (DFS) | `ask` | `:ground-first` | `:cost` | `:breadth-first` |
|---|---|---|---|---|---|
| 3 | **0.52 ms** | 15.03× | 1.37× (28 nodes) | 1.79× (40) | 1.84× (40) |
| 6 | **3.11 ms** | 3.65× | 1.01× (74) | 1.23× (115) | 1.46× (121) |
| 9 | **5.60 ms** | 2.74× | 1.02× (128) | 1.27× (190) | 1.66× (214) |

The path-structured DFS is the right shape for a needle and the node engine's advantage
is **throughput, not latency**: a symbolic residual amortizes over many answers, and a
needle has one, so 74 node expansions buy a single binding. But the margin is a *shallow*
phenomenon — 1.37× at depth 3, gone by depth 6, where `:ground-first` ties it. Deep
derivations are where the DFS's own re-derivation across branches starts costing it back.

`ask` is the slowest at every depth, by 2.7–15×. It runs the whole prover registry per
subgoal, and a needle is precisely the query where none of the other provers can help.

### The bound is the termination condition

`inference/*max-depth*` is not a tuning knob, and its root value is **nil**: the node
engine refuses a query that names no depth rather than picking one. A residual grows a
conjunct per rewrite, and the claimed-key set cannot stop that — each rewrite yields a
longer conjunction and so a key nothing has claimed. The DFS terminates on the **data**
(it substitutes as it goes, so a chain of length n ends after n steps whatever bound it
was given); the node engine terminates on the **bound**. So a derivation deeper than the
bound is found by one and not the other, and the depth a query needs is a property of the
data, which is why there is no default to pick.

Within the bound the two return the same answer **set**, which is what
`inference_parity_test` holds them to directly and what `VAELII_QUERY_ENGINE=inference`
checks across the whole suite — 2,655 tests, 239,998 assertions at `:all`,
failing-set-identical.

What the two do **not** share is multiplicity. The DFS returns one solution per
derivation, so a goal reachable two ways comes back twice with equal maps; the node
engine keys a `seen` set on the bindings, so two derivations of one answer are one
answer and the proof it hands back is the first found. Both spellings of that are
deliberate, and neither is a defect of the other — but it means **a caller counting
`prove`'s results rather than reading their set is reading an engine-specific number**.
`backward_test`'s multiplicity assertions therefore stand aside under the sweep
(`tu/query-engine-override`) while its answer-set assertions run under both. That is
why `*query-engine*` defaults to `:dfs`: two engines that disagree are worse than one
engine that is slow.

## The literal cache (`vaelii.impl.literal-cache`)

The per-path `seen` guards above stop a goal re-*expanding* itself on one path; they say
nothing about the same literal being re-*solved* on another. Two sibling branches that
both need `(parentOf Tom ?y)` each answer it in full, and a diamond-shaped rule set pays
for the shared literal once per path through the diamond. So `matches-visible` answers
are cached per KB, keyed by the literal itself.

**The key** is `[canonical-literal context hierarchical? arg-root? structural?]`. Canonical means
α-renamed to `?0 ?1 …` in first-occurrence order, **repetition-preserving**, with a map
back to the caller's names — so `(P ?x)` and `(P ?y)` share an entry while `(P ?x ?x)`
and `(P ?x ?y)` do not. Neither existing renaming would do: `res/goal-key` collapses
every variable to `?`, which is conservative enough for a loop guard and unsound here
(the second goal's answers include pairs the first excludes), and `sentex/alpha-rename`
builds an *index* key, where each `_` is a fresh wildcard — but `unify` binds `_` and
chases it, so `(P _ _)` fails against `(P A B)` exactly as `(P ?x ?x)` does. All three
retrieval-strategy vars are in the key rather than assumed away, so a cache cannot make
`retrieval_completeness_test` or `structural_index_test`'s differential oracle compare
one path's answers against themselves.

Answers are stored in canonical space and renamed on the way out — **values as well as
keys**, since a literal whose two variables unify carries a canonical name in the value
slot. Nothing downstream ever sees a `?0`.

**Invalidation is the change clock**, coarse and wholesale — the argument is
`observe/note-change`'s own docstring, not restated here. An entry is stamped with the
clock it was computed under, and a hit whose stamp has moved is a miss. Any mutation
moves the clock, so a hit is served only across a stretch in which the engine performed
no mutation at all — which is the stretch a query spends reading.

Two rules make that stamp honest, and each is a bug if broken:

- **The clock is sampled before the answer is computed, and the entry is stored only if
  it has not moved by the time the answer is complete.** Stamping afterwards would claim
  a value describes a state it was never computed from. A consequence worth naming: a
  scope that *writes while it reads* — forward chaining, under `observe/with-pin` — fills
  the cache with nothing, because its own conclusions move the clock under it. A backward
  query moves the clock never, so it stores everything it finishes.
- **Only a completed realization is stored.** The cached seq accumulates as its consumer
  pulls and stores at the moment the *source* runs dry — never when the consumer stops.
  A bounded run (`:max-results`, a deadline, a `take`) therefore stores nothing, and
  cannot leave a prefix behind for a later unbounded ask to be served as the whole
  extent. See [anytime.md](anytime.md).

**One clock-stamped layer, no per-query twin.** A per-query memo *of retrieval* would be
redundant: a query performs no mutation, so the clock cannot move while one runs, and
every repeat such a memo would catch this cache already serves under an unmoved stamp.

## Sharing a subgoal across branches

Retrieval is not the only thing a converging rule graph repeats. The per-path `seen`
guard stops a goal re-entering *itself*; it says nothing about two different branches
needing the same subgoal, which is the common case in any rule set whose paths converge.
Over a kinship DAG in which four children share a parent, `(anc <parent> ?z)` is reached
once per child, and again per grandchild.

**What repeats is a subgoal with a residual** — one that survives substitution with an
argument still open. That distinction decides whether the sharing is worth anything: a
rule whose antecedents are *unary over a single variable* substitutes to a ground literal
that is distinct per binding and shares nothing, while a relational rule whose join
variable is not the head's leaves `(anc P1 ?z)` for many branches to ask.

**The node engine shares it structurally.** A node is a canonicalized conjunction and
the session holds a set of *claimed keys*, so the second branch to reach a subgoal is
dropped before it is ever enqueued — the sharing is the search's own structure rather
than a cache laid beside it, and there is nothing to invalidate, key or measure the
soundness of. Measured on a genuinely converging DAG (every node with two parents, so a
subgoal is asked from both), that is worth 1.5× at 5×4 with the head bound, 2.4× at 6×5,
and 3.1× open. The convergence has to be real: a rule set shaped like a tree, one parent
per node, asks no subgoal twice and shares exactly nothing.

`prove` does not share, and pays it: a path engine re-derives the subgoal per branch.
That is the axis the two engines are chosen on, and it is the same one the throughput /
latency table above reports.


**Why retrieval is cached differently.** `matches-visible` answers survive the query, in
a clock-stamped per-KB cache; rule expansions do not, and are memoized only per query.
The asymmetry is not arbitrary — `solve-goal` results are tier-dependent (`ask-capped`
drops provers above a cost tier), so an answer outliving its query would have to carry
the tier that produced it. `matches-visible`
carries neither, and reads nothing through `observe/cached`, so a pinned scope cannot
hand it a view the clock has left.

`literal-cache/*enabled*` is the toggle — a cost decision that must never change the
answer set, the same claim `plan/*enabled*` makes and the same way it is checked: the
suite is a gate in both positions. `stats` reports `{:size :hits :misses :clock}` and
`clear-cache` drops a KB's entries.

## Conjunctive query planning (`vaelii.impl.plan`)

A conjunction is commutative — `[(parentOf Tom ?y) (dog ?y)]` and its reverse have
the same solutions — but it is not equicost. Solved left to right, the first
literal's matches are each re-driven through the second, so its **fan-out multiplies
everything after it**. On a measured three-literal join the good order ran 7× faster
than the bad one.

`plan/order` chooses that order, under **sideways information passing**: a literal is
never costed once and for all, but under the variables bound at the point it would
run. `(parentOf ?x ?y)` is the whole extent of `parentOf`; after `?x` is bound it is
one person's children, and only re-estimating sees that.

**One class of literal is placed on structure, not on cost.** A **cartesian factor** —
a literal sharing no variable with anything else in the conjunction — narrows nothing
and is narrowed by nothing, so wherever it runs it multiplies the row count of
everything after it. Its own extent therefore ranks it exactly wrong: a *selective*
cartesian factor is the worst kind, because taking the cheapest literal available
picks precisely that one first, where the multiplication lands on the whole rest of
the plan. `order` holds them to the back, cheapest first among themselves (a run of
pure multiplications sums to least with the smallest factor applied first).

Sharing no variable is what leaves such a literal unconstrained; it is not on its own
what makes it a multiplier, and the rule checks both. A literal matching at most once
multiplies by at most one — it can only prune — so it leads instead. The case that
makes the difference load-bearing is the **ground** literal: both chaining paths
substitute a rule's bindings into its antecedents *before* planning, so an antecedent
whose variables the trigger bound arrives fully ground, and a literal with no
variables shares none vacuously. Held back, `(dog Bob)` runs the whole join before the
single lookup that refutes it. `est-matches` bounds from above, so an estimate of 1 is
a *proof* the literal cannot fan out — the one direction that bound is sound in, and
the only decision it is trusted with here.

The rule is stated over one literal at a time, and that is its reach: two literals
disconnected from the rest but sharing a variable with **each other** are a cartesian
block just as much, and neither is held back, because each shares a variable with
something. Nothing in the shipped KB or the test world reaches that shape — no rule
there has three generators to disconnect.

**Why structure and not a cost search.** Do not replace this with a search for the
cheapest whole order — costing plans by the sum of their intermediate rows, minimized
over subsets — however well it reads. `est-matches` bounds a literal from **above**,
and those bounds do not compose across a join: minimizing estimated cost end to end
multiplies that error once per literal, and on randomized joins such a plan is
measurably *worse* than cheapest-first (mean 2.31× the best permutation's rows
against cheapest-first's 1.19× on one generated shape, losing 3 trials of 9 and
winning none). It wins handsomely on a chain beside a disconnected literal, which is
exactly the shape that makes it look right. Whether a literal shares a variable, by
contrast, is read off the conjunction and needs no estimate, so the placement rule
compounds nothing — and the estimate still decides the order within each group, where
it is compared once and locally. A join cardinality model that composes is what such
a search would need first.

What the rule is worth, and what it is not: on a chain beside one disconnected
literal (`lein bench-plan`) it cuts intermediate rows from 45,030 to 10,500 at six
literals for ~0.1 ms of planning, and on randomized joins where nothing is isolated
it changes no plan at all. A plan is **not** claimed to be optimal — on generated
joins the planner runs 1.2–3.2× the best permutation's rows on average, and that gap
is the cost model's, not the ordering rule's.

**The cost model is the trie.** Walk the literal left to right extending a known path
prefix:

| token | estimate |
|-------|----------|
| known value | extend the prefix; `count-at` it — exact, not an estimate |
| bound, value unknown | the average branch, `count-at(prefix) ÷ \|children(prefix)\|` |
| free | the prefix count stands; stop |

The middle row is what makes SIP pay: the trie's own fan-out is exactly the
distinct-value count a textbook N/V selectivity formula wants, and it is already
stored. Two corrections sit on top — the **argument roots** (`count-with-arg`) cover
a ground argument sitting *after* a variable, which no prefix can reach, and a
**unary type literal** is costed over its subtype closure, because matching fans out
there and a type high in the hierarchy usually has no instances of its own (costing
`animal` by its own extent would rank the dearest literal cheapest). Every input is
an upper bound on the true match count, so the minimum of them is the tightest bound
available without fetching a record.

**Every input must be an upper bound**, which is what decides how the two
functor-blind shapes are costed. Both of the functor-keyed models — the subtype fan
and the functor root — read the functor as a concrete symbol, and both answer *low*
when it is not one, which is the one direction a cost model may not err in: a lower
bound ranks the dearest literal cheapest and hoists it to the front, where its
fan-out multiplies everything after it. So an **open functor** (`(?type Muffet)`) is
costed by the argument roots alone — the same posting `res/candidate-handles`
actually reads for it — and a **dotted rest** (`(rel A . ?args)`), which pins no
argument position at all since its tail splices a whole list, falls back to the
functor root, or to unbounded when the functor is open too.

Where a **complete** prover owns a goal, its own estimate is authoritative instead
(`provers/est-goal`), mirroring `solve-goal-with`: a `genl` conjunct is answered from
the cached closure, so its cost is the closure's size, not the handful of stored
edges. A *partial* prover's estimate is not used — several are constants, and the
index models fan-out better.

That substitution is a **seam a caller opts into** (`plan/order`'s `:est-override`,
built by `provers/registry-est-override`), and which caller matters: it is right exactly
for an executor whose **leaf is the registry**, because only then is the closure what a
`genl` conjunct will actually be answered from. So level 7 and `query`'s depth-0
conjunction pass it, and `prove` — whose leaf is the stored facts — passes nothing and
keeps the index model, which for that leaf is the correct one. Getting this backwards is
not a slow plan but a wrong one: the index would rank the literal fanning out over a
whole type hierarchy as the *cheapest* in the conjunction. The override is memoized on
the goal, since `est-goal` reads only the goal and a query mutates nothing — without
that, `plan/order` re-estimating every remaining literal on every pick makes a
k-antecedent rule pay a full registry `applicable?` sweep O(k²) times.

**Ordering is a cost decision, never a semantic one.** Two literals are pinned,
exactly as `sentex/canonicalize-rule` pins them when canonicalizing a rule for
storage:

- **evaluables** (`evaluate`, `lessThan`, `greaterThan`) never outrun what binds
  them. This one fails quietly if got wrong: a hoisted `evaluate` yields *no*
  solutions rather than an error. (The forward join is the exception — it throws;
  see "Deferred antecedents in a forward join" below.) They are, though, pulled
  *forward* to the first
  point where their variables are all bound — a test that can run early prunes early,
  which the storage canonicalization (which parks them uniformly last) does not do.
- **a rule's recursive literal** stays last, so the cost model cannot reorder a
  recursion into the shape `prove` prunes after one expansion.

Ties break on written order, so a plan is a function of the conjunction and the KB's
counts, never of iteration order. Planning applies wherever a conjunction enters:
`prove`'s goal vector, each rule expansion in `prove`, and each node's inline join in
the node engine — antecedents are substituted *before* planning, so the planner costs
them against real values. Stored antecedent order is *canonical* order, chosen so two
spellings of one rule dedup to one sentex; it is structural and bears no relation to
what is cheap, which is why planning matters as much for a rule as for a query.

`(query-plan kb [g1 g2 …] ctx)` returns the chosen order with each literal's estimate
and the variables bound when it runs. Binding `plan/*enabled*` false runs unplanned,
which is how `plan_test` checks that every permutation of a conjunction returns the
one answer set.

## Deferred antecedents in a forward join

A **deferred** (evaluable) literal is computed, not stored. `sentex/deferred-predicates`
is the set, fifteen members: `evaluate`, `lessThan`, `greaterThan`, `different`,
`unknown`, the five measure comparisons (`sameQuantity`, `quantityLessThan`,
`quantityGreaterThan`, `quantityLessThanOrEqual`, `quantityGreaterThanOrEqual`) and the
five aggregates (`agg/count` / `sum` / `min` / `max` / `avg`). A forward join
that ran *every* antecedent through `res/match-pattern` would look a deferred one up
as a fact nobody ever asserts, find nothing, and kill the join — silently, since an
empty join is indistinguishable from a rule with nothing to fire on. The backward
chainers cannot make that mistake, because they discharge each antecedent through
`provers/solve-goal`, where the evaluable provers live; a forward join that did would
put the two chainers in disagreement about the same rule, the one thing they may never
do.

`chain/join-antecedent` closes it by sending a deferred antecedent to that same
registry rather than growing a second evaluator that could drift from it:

- **A test consumes bindings; `evaluate` produces one.** `solve-goal` returns
  solution binding maps, so `(lessThan 1970 1995)` yields `[{}]` (the join survives
  unchanged), `(lessThan 1995 1970)` yields `[]` (the join dies, correctly), and
  `(evaluate ?sum (+ 1 2))` yields `[{?sum 3}]` — the extension case falls out of the
  same call.
- **It carries no handle into the justification.** Every other antecedent contributes
  the handle of the fact that satisfied it; a computed one has no fact to name.
  Inventing a placeholder would be worse than omitting it — `retract!` withdraws a
  conclusion by walking its justifications' antecedents, so a handle naming nothing
  retractable is support that can never be taken away. Omitting it is also
  *sufficient*: the computed literal's truth is a function of the bindings, and those
  bindings come from the fact handles that **are** listed, so dropping any
  contributing fact still withdraws the conclusion. A firing whose antecedents are all
  computed lists the rule handle alone, which is the honest reading of it.
- **It contributes no context either**, for the same reason: a computed literal holds
  as arithmetic rather than as knowledge asserted somewhere, so it constrains
  `maximal-common-descendant-contexts` not at all, and the conclusion is placed by the
  real facts and the rule.
- **The two sides ask at different contexts, and for two provers that is a different
  answer.** `chain/solve-deferred` asks the registry at the wildcard `'?ctx` — nothing
  arithmetic could fail to be visible — while `res/solve-deferred` passes the caller's
  own context. For `evaluate` and the comparisons that is the same answer either way,
  since neither reads anything stored. It is not the same answer for the two deferred
  provers that *do* read the KB: `DifferentProver` reads the equality partition, so a
  forward join sees every merge rather than the ones the conclusion's placement context
  sees, and `QuantityProver` reads `dimensionOf` / `conversionFactor`, so it sees every
  context's unit table rather than one cone's. There is no context-scoped forward
  path for either. A KB that needs the two to agree states its equality and its unit
  declarations in a context every reader sees ([quantity.md](quantity.md),
  [equality.md](equality.md)).
- **Its inputs must be bound when the join reaches it.** `sentex/canonicalize-rule`
  holds deferred literals to the end of the canonical antecedent order, which
  guarantees it for any rule whose deferred variables some generator binds. A literal
  that arrives unbound anyway — `?b` occurring *only* inside `(lessThan ?a ?b)`, say —
  **throws** an `ex-info` naming the goal and the unbound variables. Reporting it as
  an empty join instead would present a comparison that was never run as one that
  failed, which is the exact failure mode the throw exists to remove. (`evaluate`'s
  first argument is its *output*, so it is exempt; every other argument is an input.)

A deferred literal at the *trigger* position is computed like any other and the
trigger handle is dropped. That position is reachable — nothing stops a caller
asserting `(lessThan 1 2)` as a fact, and the rule index keys the antecedent by its
functor — but a computed literal must not draw support from a stored twin, or one
conclusion would carry two justifications disagreeing about what supports it.

**The starter's `olderThan` rule is not an example of this**, despite joining
`birthYearOf` with `(lessThan ?bx ?by)`: it is asserted `{:direction :backward}` on
purpose, so that the O(n²) ordered pairs are never materialized. It derives nothing
forward, and correctly so — `query` at a depth answers it by backward chaining.
Restating the same antecedents as a forward rule is what shows the deferred join at
work, and is what `deferred_forward_test` does.

## Dotted rest patterns

`unify` and `substitute` support a Prolog-style rest pattern. A dotted tail
`(?pred . ?args)` unifies with `(parentOf Tom Bob)` binding `?pred=parentOf` and
`?args=(Tom Bob)`; `substitute` splices the tail back, so the same pattern with
those bindings rebuilds `(parentOf Tom Bob)`. Ordinary sentences (no `.`) are
unaffected — plain Clojure lists, no Java interop. This lets a rule quantify over an
arbitrary predicate and its whole argument list; it is what the inert
`decontextualizedPredicate` documentation rule uses (see [contexts.md](contexts.md)).

## The pluggable prover engine (`vaelii.impl.provers`, `ask`)

`ask` answers a goal through a registry of **provers**. Each prover declares:

| method | meaning |
|--------|---------|
| `applicable?` | can it answer this goal? |
| `est-bindings` | ~how many solution bindings |
| `cost` | a qualitative first-answer cost **tier** (see below) |
| `completeness` | 0..100; **100 = the sole complete method** for this goal |
| `solve` | the solutions (raw binding maps) |

The engine filters to applicable provers; if one may run *alone* it runs it, and
otherwise it unions the applicable provers cheapest first by `cost` tier and dedups.
`ask` projects solutions onto the goal's variables.

**Running alone takes two conditions, asked of different parties** (`provers/sole-prover`).
The prover claims `completeness` ≥ 100 — *for this goal shape my answers subsume every
prover whose sources I read* — which is a claim it is competent to make about itself. The
engine then asks the question no single prover can: is there a source that **none** of
them reads (`provers/shadowing-channels`)? If the channel set is non-empty, nobody runs
alone whatever they claimed, and the cheapest claimant is chosen by `est-bindings` only
once it is empty — each claimant's estimate taken **once** and carried, since a `sort-by`
keyfn is re-evaluated on every comparison and an estimate here is a real count over the
taxonomy rather than a constant. Putting the guard in the engine rather than in each
prover is what makes it hold — a new channel is one edit instead of one per claimant, and
a prover registered through `add-prover` is guarded without its author knowing the
mechanism exists. It is safe in one direction only, and that is the safe one: it can move
a goal from one prover to the union and never the reverse, and the union includes the
claimant.

`cost` is a tier keyword, not a millisecond count — one question, is the answer
something you **look up**, **compute**, or **search for**: `:lookup` < `:compute` <
`:search` (`provers/cost-tiers`), naming the *shape* of the work rather than a duration
no per-prover constant could honestly have supplied. The tier orders the union path and
is the ceiling `budget`'s `:max-cost` applies — see [anytime.md](anytime.md). `:search`
is unoccupied, since no registry member expands a rule; it stays for an application
prover that does.

Built-in provers (`default-provers`, held per-KB in an atom):

- **TransitivityProver** — `genl` / `genlContext` goals, answered directly from the
  cached closures (`genls`/`specs`, `context-up`/`context-down`). **Complete (100)** — the
  closure is authoritative, so `(genl dog ?y)` returns the full transitive set,
  and the engine skips facts/rules for it.
- **DisjointnessProver** — `disjoint` goals. `taxonomy/disjoint?` decides a ground one.
  An **open** one is enumerated from the declarations rather than from the vocabulary:
  a `(disjoint x y)` separates two subtrees and convicts `specs(x)` against `specs(y)`,
  and inheritance through `genl` is the only way a candidate is reached at all — so
  every answer is a subtype of a type some *visible* declaration names.
  `taxonomy/separating-partners` is that set for one ground argument and
  `taxonomy/separating-pairs` is it for none, which bounds the two-variable goal
  (a shape a user types by accident) by the declaration count instead of by the square
  of the type count. `est-bindings` is sized the same way — the convicted closures
  summed, an upper bound on the answer that costs a cached closure read per partner.
  **Complete (100)**: the caches are built from the stored declarations and follow
  belief, so they hold what a fact or a forward rule could say.
- **Generic relation provers** — from predicate metadata: `TransitivePredicateProver`
  (transitive closure over facts for a declared-`transitive` predicate; `:compute`, **70**
  — it reads the stored facts and the rule conclusions already among them, but not a rule
  that would conclude a further edge), and `SymmetricProver` / `InverseProver` /
  `ReflexiveProver` (swapped/derived matches; 50, they augment facts).
- **ArgPreservingProver** — `(argPreserving P n R)` / `argPreservingInverse` goals,
  answered by walking the `R`-reachability from a ground argument. `:compute`, **60**.
  Its declaration is also the `:preserving` shadowing channel, since it licenses a claim
  about a tuple that appears in no stored fact, no rule conclusion and no constraint
  network. See [inherit.md](inherit.md).
- **PredicateTypeProver** — answers `(symmetricPredicate ?p)` / `transitivePredicate` /
  `reflexivePredicate` / `functionalPredicate` directly from the cached taxonomy
  metadata (`taxonomy/props`), so the algebraic predicate types are queryable without
  materializing them as facts. Partial (50) — it augments facts rather than replacing
  them, since a directly-asserted membership still counts. (The CoreContext forward rules
  that also materialize these facts are kept — belt and suspenders: `isa?` reads the
  facts, `ask` reads the metadata.)
- **EvaluateProver** — `(evaluate ?result <expr>)` binds `?result` to the value of a
  symbolic arithmetic expression, computed by a safe whitelist evaluator
  (`+ - * / mod quot rem inc dec min max abs expt`), **not** `eval`. Nested
  expressions work; an unbound variable or unknown operator yields no solution; a
  ground `?result` slot is checked rather than bound. Complete (100).
- **EvaluableProver** — `lessThan` / `greaterThan` **computed** from ground numeric
  arguments rather than looked up (nothing is stored). Both are **variable arity**: a
  ground chain `(lessThan 1 2 3)` is checked end to end — every adjacent pair must
  hold — not just as a binary comparison. Complete for a ground comparison, so a rule
  antecedent like `(lessThan ?bx ?by)` is discharged by computation once its variables
  are bound (e.g. the `olderThan` rule over birth years). This is the extension point
  for arithmetic / CLP / any calculated relation.
- **AggregateProver** — the five reductions over a query's solutions:
  `(agg/count ?n ?v Body)` binds `?n` to how many **distinct** `?v` satisfy
  `Body`, `Sum` / `Min` / `Max` / `Avg` to the arithmetic ones. `?v` is projected out,
  so `?n` is the only binding produced, and there is exactly one answer or none.
  `:compute` — a reduction must exhaust the body before it has any answer, so a
  `{:max-cost :lookup}` budget drops it. Complete (100): an aggregate is not
  assertible, so nothing else can hold a claim about one. Bind or check, like
  `EvaluateProver`. See [aggregate.md](aggregate.md).
- **DifferentProver** — `(different A B …)` holds when no two arguments name the same
  thing under the equality closure read from the asking context, so a merge a
  context cannot see leaves the two names different there. **Ground only** — an
  open `(different ?x Y)` is a search of the whole domain's complement, and
  `applicable?` refuses it rather than answering it explosively. `:lookup`, 100. See
  [equality.md](equality.md).
- **QuantityProver** — the five measure comparisons (`sameQuantity`,
  `quantityLessThan` / `GreaterThan` / `LessThanOrEqual` / `GreaterThanOrEqual`)
  computed from two ground measure terms through the unit table. The interval reading
  is the *necessary* one — the comparison holds only when it holds of every point of
  each interval — and a dimension mismatch is never comparable, so the goal fails
  rather than throwing. `:lookup`, 100. See [quantity.md](quantity.md).
- **UnknownProver** — `(unknown S)` is closed-world negation: it holds exactly when a
  level-6 query for `S` through this same registry finds nothing. Since no registry
  member expands a rule, that reads what the KB derives *without* an unbounded proof
  search — a forward-derived fact counts, something reachable only by backward chaining
  does not. Ground/closed only. `:compute`, 100. See [naf.md](naf.md).
- **ThereExistsProver** — `(thereExists ?x S)` closes `?x` off and asks whether any
  binding satisfies `S`, which is what lets `(unknown (thereExists ?x S))` say "there
  is no `x` such that S". One answer or none, ground/closed only. `:compute`, 100. See
  [naf.md](naf.md).
- **ArgTypeProver** — infers an individual's type from *how it is used*: if a
  believed relation puts `x` in a position that `(argIsa P n T')` constrains, then
  `x` is a `T'` (and, by genl, every supertype). So `argIsa` reads two ways — a
  **constraint** when asserting, and an **inference** when querying (Muffet eats
  Bone1 and eat's 2nd argument is food ⇒ Bone1 is food). On-demand, never
  materialized. Partial (50).
- **FactProver** — index matches (`matches-visible`). Partial (50).

Seventeen in all, and `provers/registry` is the live list — an application's own
provers sit beside them in the same atom.

**No prover expands a rule.** Rule search is `core/query`'s, at a depth the caller
names, and the registry is what a backward search uses as its *leaf* — so the recursion
divides between the two rather than being nested inside one of them.  What draws the
candidate rules is `provers/candidate-rules`, which lives here beside the registry
because both chainers read it: `specs ∩ rules-by-consequent`, so a rule concluding a
subtype answers a supertype goal, unified against the consequent by subsumption.

`add-prover kb prover` registers a custom prover; `query-plan kb goal context`
returns the applicable provers with their `est-bindings`, `cost` tier, and
`completeness`. This is where a specialized solver (arithmetic, a temporal
reasoner, an external service) plugs in.

**The RCC-8 prover** (`vaelii.impl.space/spatial-prover`) is the worked example of that
seam: qualitative spatial reasoning over the generic constraint-network engine in
`vaelii.impl.qcn`. It reads every believed spatial fact visible from a context into a
network, tightens it by composition to a fixpoint, and answers a region goal by
entailment — `:compute`, complete (100), and opt-in via `add-prover` rather than
shipped in `default-provers`. The cardinal-direction prover
(`vaelii.impl.orientation/orientation-prover`) and the interval-time one
(`vaelii.impl.interval/allen-prover`) are the same shape over the same engine — literally
the same record, `qcn-kb/CalculusProver`, carrying a different calculus — which is the
point of the split: another qualitative calculus costs a relation algebra and a table,
not another reasoner. `core/add-reasoner` names them. See [qcn.md](qcn.md),
[space.md](space.md) and [time.md](time.md).

## Resource-bounded / anytime inference (`vaelii.impl.budget`)

Because `ask` (and the level stack, and the node engine's result stream) are lazy, a
**budget** is the
consumer-side act of realizing the answer stream under a bound and reporting
whether it ran dry or was cut short — with the unrealized tail as a free
continuation. `ask-within` / `prove-within` return a partial-result contract
(`:results` / `:status` `:complete`/`:timeout`/`:capped` / `:resume`), and `resume`
continues it. The budget carries `:max-ms` (wall-clock, checked between
solutions), `:max-results`, `:max-cost` (a `cost`-tier ceiling — run only the cheap
tiers under pressure), and, for `prove-within`, `:max-depth` (rule-expansion
depth). `prove` is the one eager engine, made resumable by returning its
unfinished DFS goal stack (`res/prove-from`). Full design: [anytime.md](anytime.md).

## JTMS → NMTMS

A node is IN if it is a premise or has a *valid* justification (all antecedents
IN), computed as a least fixpoint — **except** a datum in the `defeated` set is
forced OUT. Belief is a **relabelling**, recomputed from the current justifications
and defeated set rather than accumulated, so it is order-independent: a defeater
withdraws its target whether it arrives before or after, and removing the defeater
revives it. The relabel is *scoped to the affected region* with the rest of the graph
held fixed; the whole-graph `jtms/relabel` survives for one caller, `recover`, which
rebuilds the network from the durable store and so has no smaller region to start from
([nmtms.md](nmtms.md)). This is the non-monotonic upgrade — assumption strengths, the
defeated set, and the soft-contradiction layer that fills it are documented in
[nmtms.md](nmtms.md).

**Retraction is dependency-directed** (relabel-then-sweep):

1. **mark** — suspects = the consequence-closure of the retracted datum.
2. **relabel** — drop the premise and recompute labels; a suspect still derivable
   via another witness (a surviving justification) stays IN.
3. **sweep** — a suspect that ends OUT with no valid support and is *not merely
   defeated* is solely supported by the retraction; it and its non-premise
   justifications are returned for the caller to delete from the record store and both
   indexes (and to reverse their taxonomy / rule-index effects). A defeated datum
   keeps its support and is retained for revival.

Matching is **belief-sensitive**: a stored-but-OUT sentex (a defeated default) does
not match (`res/raw-match`, `core/sentexes-matching`, `core/types-of` filter by `jtms/in?`),
so a disbelieved default can stay in the store for revival without polluting
reasoning. Raw introspection still sees everything.

## Negation and defeasible defaults

- **Explicit negation.** `(not S)` is an ordinary sentex. Asserting `S` when
  `(not S)` is believed (or vice versa) is **not** rejected — it is a *soft,
  prioritized contradiction* resolved at settle time (see below).
- **Defeasible rules.** Wrapping a rule as `(set/defaultRule <implies>)` marks it a
  default: it forward-chains from the **same agenda** as every other rule, triggered
  by the facts that arrive, and confers `:default` justification strength instead of a
  bare rule's `:monotonic`. A default conclusion is placed *unconditionally*; whether
  it survives is decided afterwards by the non-monotonic layer. **Do not split this into
  two phases** — bare rules to a fixpoint, then a rescan-everything defaults loop is an
  O(N²) scaling wall, and one agenda derives the same set; see
  [Forward chaining](#forward-chaining).
- **Non-monotonic settle.** After chaining (and after every assert / retract /
  `recover`), `settle` relabels belief and resolves contradictions: the
  weaker-class belief is defeated, a default/default tie goes to the edge solver,
  and an irreducible known-true clash is reported in `(conflicts kb)`. Because
  belief is *recomputed* from the current facts, a default conclusion is withdrawn
  when its negation **arrives later** and revived when that negation is retracted.
  Full details: [nmtms.md](nmtms.md).

## Where the machinery stops

- **The `out` slot on a justification is modelled and carried, and nothing populates it**
  — `jtms/valid?` reads it on every relabel and finds it empty, so the check is vacuous.
  Negation as failure reaches a rule antecedent by a different road — `chain/naf-blocks?`
  evaluates an `unknown` antecedent at firing time in `derive-conclusion`, and the
  re-check index brings the rule back when a later fact would change the answer. So a
  blocked firing is a justification that was never made, not one carrying an OUT
  antecedent. See [naf.md](naf.md).
- **A relabel is scoped to the affected region, and that region is the full forward
  closure.** Inside it the fixpoints are semi-naive worklists, so only nodes whose
  inputs move are retouched; the region itself is not narrowed below the closure.
- **There is no beta network** over the alpha memories, so a repeated multi-way join is
  re-joined per firing (see "Incremental rule matching").
