# Equality: `rewriteOf`, `sameAs`, `equals`, and `different`

- **Covers:** how `rewriteOf`, `sameAs` and `equals` merge two ground names into one
  belief-following partition, and why `different` still holds afterward.
- **Not here:** orienting a schematic equation with variables into a rewrite rule →
  [equational.md](equational.md); reifying a function-application term to a constant
  before it can be merged → [nat.md](nat.md).
- **Assumes:** sentex, context, taxonomy, canonical form → [glossary.md](glossary.md).

How two names come to denote one thing, and why the unique-name assumption survives it.

## The problem

Nothing in the engine can say two names denote the same individual. Dedup is
syntactic — `find-or-create-sentex` keys on the canonical sentence — so `Obama`
and `BarackObama` are two individuals with two disjoint fact sets, two type sets,
two argument roots, and no way to ever connect them.

That caps the KB at hand-curated single-source data. Every real ingest pipeline
produces co-referents on day one, so this is the precondition for an import path,
not a refinement of one.

Identity can connect `(motherOf Tom Mary)` and `(motherOf Tom MrsSmith)` when
independent evidence establishes that the two names denote one woman. Motherhood itself
is not a uniqueness constraint: a child can have several distinct mothers, and sharing
a child does not merge their names.

## Three assertable relations, one closure

| relation | scope | contract |
|----------|-------|----------|
| `(rewriteOf P D)` | any term | directional: `D` is **deprecated**, migrate off it |
| `(sameAs A B)` | individuals, by OWL's reading | OWL: reflexive, symmetric, transitive, substitutive |
| `(equals A B)` | any terms | equality without OWL's individual restriction |

All three feed **one equivalence closure**. They differ in what they say *about*
the members, not in the classes they produce:

- `rewriteOf` names the representative and marks the loser deprecated. Because it
  is about *spelling* rather than identity, it applies to predicates and types as
  well — which is what vocabulary alignment on import needs.
- `sameAs` follows OWL, which uses `sameAs` for individuals, `equivalentClass` for
  classes and `equivalentProperty` for properties. Both names stay first-class;
  neither is deprecated; the representative is an internal detail. No check holds a
  `sameAs` to individuals: core.txt types both arguments `thing`, so `(sameAs dog cat)`
  is stored and merges two types.
- `equals` states an identity between any two terms, with no individuals-only reading.

Picking a canonical representative and rewriting to it is how OWL reasoners
implement `sameAs` anyway, so one mechanism serves all three.

### Choosing the representative

The choice is keyed on content, never on a handle or on arrival order
([nmtms.md](nmtms.md)), since handles are allocated in assertion order.

1. The candidates are the class's **preferred** terms minus its **deprecated** ones, so
   the head of a `rewriteOf` chain wins. Chains compose: `rewriteOf A B` and `rewriteOf B
   C` make `A` the representative of all three, and with `(rewriteOf A B)` and `(sameAs B
   Aardvark)` the representative is `A`, though `Aardvark` sorts first.
2. Otherwise, and to break a tie among several heads, the **lexicographically smallest
   symbol**, the same content key as `solve/content-key`.

A **preference is per supporter**, not per edge. One edge may be supported by a `sameAs`
and a `rewriteOf` at once, and disbelieving the `rewriteOf` withdraws the deprecation
while the merge stands on the `sameAs`.

`wff` refuses a `rewriteOf` self-edge, `(rewriteOf A A)`, and an edge closing a cycle over
the active preferences, found by reachability, as it refuses a `genl` cycle. `(sameAs A
A)` is accepted, since OWL makes `sameAs` reflexive. The taxonomy's election
(`tax/class-rep`) stays **total**, because `wff` runs above the taxonomy: a cycle falls
back to the smallest preferred term, then to the smallest member, and the closure never
returns nil for a term it holds.

## The unique-name assumption survives

OWL drops UNA. We do not. `(different X Y)` is **provable exactly when the
arguments lie in no shared equivalence class** — so distinct symbols denote
distinct individuals until an equality sentex says otherwise.

One carve-out: an **indeterminate term** suspends the UNA for every name of its
equivalence class. A believed member of the extensible `indeterminate_term` category is
one, and the membership holds of every name the context sees merged with it. A skolem
constant is one only while no merge names it, so a `rewriteOf`, `sameAs` or `equals`
merging it lifts the exemption (`provers/indeterminate-term?`). An indeterminate term
stands for some object without determining which, so neither `equals` nor `different` is
provable between it and a determinate term. The category, what it does to `same-class?`,
and the stratification edge it adds are in [predall.md](predall.md#the-identity-exemption).

A rule guarded by `different` is re-checked when either input moves. Both a merge and an
indeterminacy declaration withdraw the firing they licensed, and retracting one brings it
back, so the guard is order-independent though the prover can name no handle for a
justification to carry ([predall.md](predall.md#a-different-guard-is-re-checked-not-supported)).

This is negation as failure over the equality closure, and it is what keeps
counting meaningful: counting distinct symbols stays correct except for terms
somebody explicitly merged, so `count-with-arg` and friends do not acquire a
blanket caveat.

`different` is:

- **Variable arity.** `(different A B C)` asserts the arguments are pairwise
  distinct.
- **Not assertible.** A prover answers it and nothing stores it, and an assert of it is
  refused ([defenses.md](defenses.md#there-is-no-assertible-differentfrom)).
- **Ground only.** The prover is inapplicable unless every argument is bound.
  `(different ?x Y)` would enumerate every term in the KB that is not `Y`, so it is
  refused rather than answered explosively.
- **Not canonicalized.** No chain merging, no clique merging, no subsumption
  elimination, no argument sorting
  ([defenses.md](defenses.md#different-is-not-chain-merged-or-clique-merged)).
- **At least two arguments.** Fewer is inapplicable, matching the evaluable
  provers. `(different A)` asserts nothing and `(different)` is meaningless.

Two contract details the closure must settle, because `different` reads them:

- **A term the closure has never seen is its own singleton class.** So
  `same-class?` is reflexive everywhere, and an unmerged symbol is different from
  every other unmerged symbol. The prover answers `(different A A)` false before it
  reads the closure.
- **The closure holds symbols, not compound terms.** `wff` refuses a compound argument
  to all three relations, except a `rewriteOf` NAT declaration ([nat.md](nat.md)) and a
  schematic `equals` ([equational.md](equational.md)) (`wff/equality-problems`). `different`,
  though, may compare ground compounds: it normalizes each argument by replacing
  its symbols with their representatives and compares the results, which is
  congruence-consistent and needs no theory.

Because it consumes bindings rather than producing them, `different` is a
**deferred literal**, the same class as `lessThan` / `greaterThan` / `evaluate`.
`sentex/canonicalize-rule` keeps that class in the author's order
(`sentex/deferred-literal?`), because a deferred literal's position is operational
rather than logical. The generators are sorted by `sentex/cmp-blind`, which never sees a
deferred literal and ignores variable names, so two spellings of one rule that differ in
`?x` against `?a` canonicalize together.

## Answering an equation

A believed equation is answered by every read, and three rules make that hold.

- **A stored equation is never retired.** Migration never restates a positive
  `rewriteOf` / `sameAs` / `equals` (`kb/rewritable-sentex?`), so the stated spelling is
  the only one there will ever be. `res/retired-for?` therefore never drops one: the
  per-reader filter that hides a displaced spelling (`res/without-retired`) would
  otherwise hide `(sameAs A B)` from every reader that sees the merge it states, and no
  read would return it under any name. An equality relation nested inside a sentence,
  `(not (sameAs A B))` say, is read through the mention walk, since its arguments move
  by a spelling rename and not by an identity merge.
- **Raw equation retrieval keeps the authored spelling**
  (`res/goal-held-as-spelled?`). This remains the storage/mention policy, not a rule
  that public positive `rewriteOf` answers must expose a retired spelling.
- **Positive `rewriteOf` queries read visible witnesses through the reader's
  representatives.** Both the goal endpoints and each stored witness's endpoints are
  normalized as terms before matching, with existing closed applications resolved
  without minting. Thus `(rewriteOf P D)` may answer `(rewriteOf P P)` and bind an open
  endpoint to `P`; that binding roundtrips as a closed query and composes with another
  conjunct. A variable predicate does not bypass normalization. This is the canonical
  image of actual visible rewrite witnesses, not universal reflexivity: an unrelated
  `(rewriteOf X X)` is unsupported. Negative equations keep their existing mention
  policy. No stored self edge, converse edge, or retirement record is synthesized.
- **`sameAs` and `equals` goals are answered from the closure** by
  `provers/EqualityProver`, scoped to the asking context the way `same-class?` is. A
  ground goal holds when both sides reach one normal form (congruence, then the visible
  schematic equations), so the stated form, its symmetric form, the reflexive form and a
  form joining two ends of a chain all answer true. A goal binding a symbol on one side
  and a variable on the other enumerates that symbol's class, itself included. A
  spelling a visible `rewriteOf` retired is returned through its spelling representative;
  ordinary nonretired identity aliases remain separate answers. This does not collapse
  a `sameAs` class to one identity representative or change the stored class members.

Two `sameAs` / `equals` shapes are not answered from the closure, and each is left to
the stored equations. A goal open on both sides asks for every pair over the domain, reflexive
pairs included, so it returns the stated equations only. A goal binding a **compound**
beside a variable asks for every term that normalizes with it, which is E-unification
("What is not built" below). A stored **`rewriteOf`** preference is still directional;
its public positive answers use the representative image described above. This
does not change write admission or the stored preference graph.

`sentexes-matching` is a storage read, so it returns the stated equation as spelled and
nothing else: the symmetric form of an equation stated one way round is not a stored
sentex. Public registry-backed `ask`, `query` and `prove` use the semantic readers;
a caller explicitly supplying a raw storage leaf still reads the stored records
([inference.md](inference.md)).

## What a merge does

`rewriteOf`, `sameAs` and `equals` are in the baseline forced-monotonic set,
so on every KB, upper layer or not, an equation premise is never the loser of a nogood whatever
strength it was written at ([nmtms.md](nmtms.md#the-forced-monotonic-set)), and no
placed `defeat` hides a merge ([reference.md](reference.md#decisions), decision 13). A denial of a stored equation premise loses to it
at either strength, and no denial undoes a merge or blocks a rewrite.

Four parts, all reusing machinery that already exists:

1. **Migrate.** `find-sentexes` returns every sentex containing a term some reader
   retires, at any nesting depth, in one index lookup. Each gets a rewritten twin
   under the representative, **derived and justified** by `[the original sentex,
   the equality sentex]`. Dedup falls out: when the rewritten form already exists,
   find-or-create returns that handle and it simply gains a second justification.
   One twin per *reader* whose election differs, placed where that reader lives —
   "Scope, context, and re-election" below.
2. **Supersede the original.** The stale spelling stays stored but is not believed
   and does not match. Handles that callers already hold stay valid.

   Supersession is TMS state of its own, `jtms`'s `:superseded` map, `datum ->
   {old-term representative}`. `exceptWhen`'s `:blocked` holds *justification* ids, and
   a directly asserted `(bornIn Dep Chicago)` is a **premise** with no justification,
   which `relabel` holds IN unconditionally. `:superseded` subtracts *reported* belief
   (`in?`, `in-datums`) and leaves the label alone
   ([defenses.md](defenses.md#a-supersession-is-not-a-forced-out)), and `why-not`
   reports the datum `:superseded`. It is read from the sentex's own context, the
   context migration writes it in.

   **A superseded spelling does not fire a forward rule**, and it is the one
   unbelieved datum that does not — a defeated default still fires, because a defeat is
   a label and the conclusion drawn off it is labelled OUT with it and revives with it
   ([nmtms.md](nmtms.md)). Supersession is not a label. It subtracts *reported* belief
   with no relabel behind it, so a conclusion drawn off a retired spelling would stand
   believed under a name no read asks after: the same three sentences concluding once
   where the merge preceded the fact and twice where it followed. The restatement is on
   the chaining agenda beside the retired spelling, so the firing is made once at the
   elected name; and when the merge goes away the spelling comes back through `settle`'s
   un-merge channel and fires then. `chain/process-datum` is where that supersession check sits.

   A firing made over the spelling **before** the merge arrived is withdrawn at the
   merge, so the store holds the firings the merge-first order holds. With `(pp Zz)`,
   `(not (pp Aa))` known-true, `(pp ?x) => (rr ?x)` and `(rewriteOf Aa Zz)`, the firing
   over `(pp Zz)` would otherwise leave `(rr Aa)` justified by `[(rr Zz) (rewriteOf Aa
   Zz)]`, a restatement no defeat names, and `(rr Aa)` believed in the merge-last orders
   only. The settle drops the firing ([nmtms.md](nmtms.md#the-other-half-a-spelling-an-un-merge-gives-back)),
   and `(rr Aa)` is not believed in any of the 24 orders.

   An argument-type mint ([argtypes.md](argtypes.md)) is drawn over a superseded
   spelling, and the mint is spelled at the retired term. `special/restate-retired`
   restates the mint as it is stored, as `assert` restates a fact naming a retired term,
   so the mint is superseded and its twin is believed at the elected name. A merge that
   arrives after the mint migrates the mint with the fact, and every order believes the
   same membership
   (`argtype_entail_test/a-mint-over-a-retired-spelling-is-believed-at-the-elected-name-in-every-order`).
3. **Rewrite goals.** A query naming a non-representative is rewritten before
   lookup, since its own sentexes are no longer believed. `handle-of` and the `lookup`
   levels do not rewrite, since they answer about storage.
4. **Queue the re-check.** Steps 2 and 3 are exactly what a closed-world condition —
   an `exceptWhen` query, an `unknown`, an aggregate's census — cannot see coming. A
   retired spelling leaves no fact arriving or departing on its predicate, and a
   rewritten goal changes an answer with nothing on the queried predicate moving at
   all, so neither the predicate keying nor the firing keying that narrows the taxonomy
   triggers can reach it. `special/recheck-equality-edge` therefore queues every rule
   carrying such a condition, both when the closure grows and when it splits, and
   `chain/settled-bindings` rewrites the firing's stored bindings before the condition
   is re-evaluated — a justification records what matched when it fired, and a merge
   does not go back and edit it. [exceptions.md](exceptions.md) is where that channel
   sits beside the other three.

**`different` is exempt from step 3.** Rewriting a `different` goal would map every
argument to its class representative, so a merged pair would compare equal — and
since the whole job of `different` is to *read* class membership, every goal would
come out false the moment anything merged. Its arguments are already
rewrite-invariant: the prover consults the closure directly. Exempt it explicitly
rather than relying on the rewrite being a no-op.

**A positive equation is exempt from step 3 too**, for the reason "Answering an
equation" gives: its arguments are mentions and the stored equation is never restated,
so the goal meets it only as spelled.

Dropping the equality invalidates the derivations, the dependency-directed sweep
collects the twins, and un-superseding revives the originals.

**The reconcile in step 2 runs on the write path.** An entry reads the displaced
datum's record, the class its terms belong to, the rewrite rules, the `genlCx` ancestor
set and whether the restatement is stored. The equality relations, the rewrite rules and
`genlCx` are forced monotonic, so an entry moves only when a sentence is stored or
removed, or an `except` moves, and never with a settle's belief: a merge rests on
`:monotonic` evidence alone ([reference.md](reference.md#decisions), decisions 6 and 13)
and is undone only by retracting a premise it rests on. Re-examining an entry is a record
fetch, a rewrite through the closure and a store probe for the restatement, and the
standing displaced set is not a small fixed thing: `owl:sameAs` is what an RDF import
emits in quantity, so a pass over the whole set per write is one probe per standing merge.

So each write reconciles what it moved. A migration hands over the entries it restated,
and `migrate-class` walks the whole class an edge moved, so a merge arriving is described
by its own output. A sentence leaving the store reconciles at the removal choke point
(`special/reconcile-removed-supersession!`): a displaced datum leaving drops its entry,
and an equality leaving names the classes it moved term by term
(`tax/take-equality-moves!`), so an un-merge re-examines the stored sentexes naming a term
of that class and no other entry. A `genlCx` edge, stored or removed, and a schematic
rewrite rule removed can retire an entry no class move names — a context edge changes
which merges a reader can see, and a rule leaving re-normalizes every sentence it reached
— so each re-examines the whole set while any spelling is superseded, and `recover` does
too. The settle reconciles only after an `except` moved (the data it reaches,
`special/except-move-region`), and after an equality edge moved in belief. A settle
that moved no equality premise calls no reconcile.

**A supporter believed by a relabel migrates as one that arrived believed.** A firing
held void stores its equality OUT
([taxonomy.md](taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches)), so its
arrival restates nothing. A forced-monotonic declaration that releases the firing, or a valid
firing of the stored conclusion, makes it believed with no arrival. The partition
reconcile records each supporter it moves from disbelieved to believed
(`tax/take-believed-again!`), and `settle-finish` runs the arrival's re-check and
migration over that supporter's class (`special/believed-again-sweeps`). The KB then
stores the twins the order with the valid firing first stores.

`settle-finish` then reconciles the taxonomy's caches over the region and the data whose
supersession changed since the last settle (`special/take-supersession-moves!`), since a
supersession flip moves belief with no relabel behind it.

### Scope, context, and re-election

**An equality applies where it is visible.** A merge asserted in `CxUniverse`
applies everywhere; one asserted in a context applies there and below, by the
ordinary `genlCx` up-closure. That answers "is equality global or scoped" the
same way everything else in the engine answers it, and it is what lets a story
merge two characters without leaking into an unrelated one.

That holds on the **question** as much as on the answer. `kb/rewrite-goal` takes the
goal's context and rewrites only by the merges it can see; the class reads
(`representative` / `same-class?` / `equiv-class` / `deprecated?`) take one too, and
`different` reads the scoped partition, since the unique-name assumption is what a
context holds until *it* is told otherwise. Scoping migration alone would be worse
than scoping nothing: the goal would be renamed to a spelling migration correctly
declined to create, and the asking context would lose a fact it still believes, under
either name. An invisible edge can **split** a class, so the scoped read is its own
election over the visible edges rather than a filter of the global answer
(docs/taxonomy.md).

#### The reader is not the fact's own context

Which makes the twin's placement the hard half, because **a fact and the merge that
restates it need not live in the same context**, and the party whose spelling is at
stake is neither of them — it is whoever *reads* the fact, which is any context below
it, each electing over a different set of visible edges.

Two shapes make the point, both with `Leaf` under `Mid`:

- The merge sits **below** the fact. `(likes Tom Bravo)` in `Mid`, `(rewriteOf Alpha
  Bravo)` in `Leaf`. `Mid` has been told nothing and keeps its spelling. `Leaf` sees
  both, so `Leaf` elects `Alpha` — and a context that can see a fact has to be able to
  ask for it. One normal form computed at the fact's context serves `Mid` and leaves
  `Leaf` asking under two names that both miss.
- The class is **split across** the chain. `(rewriteOf Bravo Charlie)` in `Mid` and
  `(rewriteOf Alpha Bravo)` in `Leaf` put `Mid` and `Leaf` on different heads of one
  `rewriteOf` chain: `Mid` elects `Bravo`, `Leaf` elects `Alpha`. One normal form
  computed *globally* serves `Leaf` and hands `Mid` a spelling only `Leaf`'s edge
  produces — while `Mid`'s own fact, superseded, is retrievable under nothing.

So migration runs **once per reader whose election differs**, and each twin is placed
in the context that elected it. The readers are the fact's context closed under where
it meets the equalities' — `tax/meet-closure`, the same enumeration a qualitative
network takes over the contexts holding its facts ([qcn.md](qcn.md)) and for the same
reason: knowledge stated in several contexts is read by whoever inherits some
combination of them, and which combination changes the answer. Two readers electing the
same form share one twin, at the more general of them; a reader that changes nothing
costs one rewrite. The candidate set is the whole **class**, not the edges incident on
the sentence's own terms — chain composition means an edge touching nothing in the
sentence still moves what its terms rewrite to.

**A reader can retire the KB's own representative.** `(sameAs Pa Qb)` and `(rewriteOf Qb
Pa)` elect `Qb`; a reader that sees the `sameAs` and not the `rewriteOf`, because the
`rewriteOf` is stated in a context it does not inherit or excepted in it, elects `Pa`. So
a sweep over a class (`migrate-class`, `migrate-under-context-edge`, an `except` moving)
walks the representative's facts too when a reader can retire it (`tax/retirable?`): a
`rewriteOf` names it preferred and the class holds a supporter that is not such a claim. A
representative no `rewriteOf` names preferred is the smallest member, which every reader's
election keeps, so a class merged by `sameAs` and `equals` alone walks its other members
only.

The fact's own context is always a reader, and it is the one that supersedes: a reader
*below* it restates the fact for itself and leaves the original believed where it
lives, because that context has been told nothing.

**Which leaves supersession short by one, and the shortfall is a read filter.**
`jtms/superseded` is per *datum* — a sentex lives in one context, so one flag answers
for one context — while staleness is per *reader*. `Leaf` inheriting `Mid`'s
un-superseded spelling alongside the twin it elected would report one fact twice, under
two names it knows denote one thing, and every count over the answer set would double.
`res/without-retired` drops the matches whose stored spelling the asking context has
retired, beside the `except` filter that already removes what a context may not see.
It runs only when the closure is non-empty, so a KB that has merged nothing pays one
set-empty test per query.

#### A late `genlCx` edge is a third arrival order

An equality applies where it is visible, so the `genlCx` ancestor set decides what a merge
restates as much as the closure does — and the ancestor set is knowledge that arrives in its own
time. `(equals Tom Thomas)` in `Up`, `(mammal Tom)` in `Low`, and `(genlCx Low Up)` are
three sentences that must yield one KB in all six orders, and the edge is the ingredient
whose arrival nothing keyed on: `migrate-class` covers the merge arriving last and the
assert path's `migrate-sentex` covers the fact arriving last, while a supersession is
only ever *dropped or restated* by the reconcile and so cannot write a restatement that
was never made. With the edge last, `Low` would keep the spelling it stored the fact
under while every read from `Low` asks after `Thomas` — a sentex believed and answering
no query, under either name.

`special/migrate-under-context-edge` closes that, and it is the equality twin of the
`genlCx` seeding forward chaining takes ([inference.md](inference.md)). **Both ancestor sets**,
because the whole of the new reachability is that a reader in `context-down(sub)` now
sees `context-up(super)`: a reader, a fact and a merge form a new triple only if the
reader newly reached one of the two, which puts that one in `super`'s ancestor set and the
reader in `sub`'s descendant set — a merge above meeting the facts the widened readers
already saw, and a fact above meeting the merges they already saw. It is **enumerated
from the merges**, not from the ancestor set: the merges are the believed equalities stated
in a context some reader under `sub` sees, and the candidates are the stored sentexes naming a
term one of those merges displaces, which the inverted term index answers in one lookup
per term. The cost is proportional to the merges the readers see and to what they reach,
not to the merges stated elsewhere or to how much ontology the ancestor set holds
(`lein perf`'s `genlcx-edge-beside-distant-merges`). A KB that has merged nothing pays one
set-empty test, and each half runs only when the other side holds a merge the reader can
see, so wiring a context under one whose merges it already inherits enumerates nothing.
A **derived** edge runs the same arm from `chain/place-fact-conclusion`, so which
spelling a context reads a fact under does not depend on whether the context edge was written
or inferred.

The removal side needs no twin of this: dropping an edge narrows what a reader sees, and
a twin names, for each term its reader's election displaces, every equality on one path
from the term to its representative (`tax/scoped-path-supporters`), one justification per
choice of supporter along the path, and the `genlCx` edges its reader sees the original
and each equality through (`special/migrate-into`). The ordinary dependency-directed
sweep collects one whose merge, link or original the reader can no longer see,
`rederive-descended` restates it again over a surviving path, and
`refresh-supersessions` hands the spelling back.

**A late `rewriteOf` can move a representative, and that means re-migration.**
`(sameAs A B)` elects a representative lexicographically; a later `(rewriteOf B A)`
names `B` preferred and re-elects it. Everything already migrated to `A` migrates
again: `migrate-class` walks the whole class an edge moved, so a re-election
re-migrates with no separate code path.

### Congruence comes free

Congruence — if `a = b` then any term containing `a` equals the same term with `b`
substituted — has no algorithm of its own here. The inverted term index
locates a term at **any nesting depth**, and migration rewrites it there, so
merging performs congruence closure eagerly over all ground content. No congruence
algorithm is written, because the index already answers the question it would ask.

**One position is exempt: a mention.** A term named as *syntax*, rather than one the
sentence refers with, does not fold onto its referent's class — the arguments of a quoting
function (`Quote` and `Quasiquote`, fixed by the engine and declared by nothing), and the
proposition a `modal_predicate` attributes to its agent. `(believes Oedipus (marriedTo
Oedipus Jocasta))` is not rewritten by a `sameAs` the *asker* holds, because an attitude is
opaque and the asker's identities are not the agent's; the agent's own merges do rewrite
it, where the projection reads them. A `rewriteOf` **spelling** rename reaches into a
mention either way, since it retires a name rather than merging referents. The rule and
both halves of what it provides are [belief.md](belief.md), "Opacity: the proposition is a
mention"; the exemption is in the congruence walk itself, so migration and query hold it
alike.

## `functional` infers equality instead of throwing

`(functional P)` plus two different **symbols** for the same first argument, both
facts `:monotonic`, **derives `(equals V1 V2)`**, with antecedents `[both facts, the
functional declaration]`. Every other collision is a nogood the settle decides: two
numbers, two strings or a compound, because no merge can make two numbers one thing, and
a pair with a `:default` fact, because a merge is never defeated and is undone only by
retracting a premise it rests on, so it rests on `:monotonic` evidence alone
([reference.md](reference.md#decisions), decisions 6 and 13). Two measures that can
denote one magnitude are no collision
([quantity.md](quantity.md#a-functional-measure-slot)). The settle places the
`defeat` of the unique `:default` fact of such a pair, and two `:default` facts are a
dilemma. A defeasible identity is
written with a predicate that does not merge.

**The merge follows each member's class, not only its arrival.** A member's class moves
under an unchanged label when a justification of it arrives or leaves: a `:monotonic` rule
firing over a `:default` fact, or that firing's premise retracted. At the start of each
settle pass `special/class-moved-merges` re-asks the collisions of the relabelled handles
(`jtms/touched`) whose class can have moved, conditional on the marks as the write path is. A
member IN at `:monotonic` goes back through the write-path derivation, so the merge is the
one the member would have met arriving at that class. A collision justification with a
member IN at `:default` is dropped, as retracting that member drops it, and an equality
with another justification stands on it. A settle whose own defeats stand when a merge
moves settles again from no defeat (`settle/*unmerged-sink*`). `core/preview` keeps every
handle, so it leaves a dropped merge standing.

**`(functionalInArg P n)` is the same machinery with the determined position named**
rather than fixed at argument 2 ([taxonomy.md](taxonomy.md)). Everything in this section
holds of it unchanged: the same merge-or-nogood rule, the same four arrival directions, the
same justification shape. Two differences matter. The clash the checks hand
back carries the **position** — with the generalized mark a predicate may be constrained
at more than one position at once, and two slots of one sentex are two different incoming
fillers — so the filler is read at the clash's position (`checks/functional-filler`),
not as argument 2. And the merge rests
on *every* declaration constraining that position, both spellings unioned
(`checks/functional-declaration-supporters`), so a predicate carrying `(functional P)` and
`(functionalInArg P 2)` keeps its merge when either one is retracted — the same rule two
`(functional P)` sentexes in different contexts follow, applied one level up
([defenses.md](defenses.md#a-functional-merge-rests-on-every-declaration-of-the-convicting-mark)).

The merge derives `equals`, not `sameAs`, because a functional value need not be an
individual.

The fluent lane has its own counterpart. A value carried under `initiates` never becomes a
bare literal, so this closure never sees it; `(functional_at_instant F)` states that `F` has
at most one value for one subject at a single instant, and
`vaelii.core/functional-at-instant-violations` reports a moment carrying two — a merge for
two symbols, a contradiction otherwise. It reports rather than merges: whether two fluents
overlap at an instant follows from the clipping closure and is read on demand, the shape
`specified-violations` uses. See [time.md](time.md).

The merge is a justified derivation: `why` names the declaration and the two facts, and
retracting any one of them un-merges. One wrong `functional` declaration merges two
individuals across the KB, and the justification makes that merge inspectable and
reversible.

**The mark is read up the predicate hierarchy**, since two `fatherOf` mothers for one
child are two `parentOf` values and `(functional parentOf)` is what says a child has one
([taxonomy.md](taxonomy.md)). The slot is probed at the marked predicate — `(parentOf a
?v)` finds a filler written either way through the matcher's fan, where `(fatherOf a ?v)`
would miss one written at the general spelling — and the merge then rests on the
subsumption as well, so the `genl` edges **both** members descended through join the
declarations of the mark that convicted the pair (`via`) in the antecedents.
Retracting the edge un-merges, exactly as retracting the declaration does; without them
two names would stay merged on a declaration that no longer reaches either of them.

**Four directions, because a declaration reaches the facts already stored exactly as it
reaches the facts that follow, and so does either edge that can bring a slot's fillers
into view.**
`special/derive-functional-equalities` is a fact meeting the declaration — it runs on
every asserted fact and on every derived conclusion — `special/equate-existing` is the
declaration meeting the facts, sweeping the predicate extents of `P`'s whole `genl` spec
subtree when `(functional P)` itself arrives, `special/equate-under-edge` is the `genl`
edge meeting both, sweeping the arriving `(genl sub super)`'s own subtree when a mark
stands at or above `super`, and
`special/equate-under-context-edge` is the fourth: a `genlCx` edge meeting both, over the
*context* ancestor set rather than the predicate one. It has no subtree of its own to sweep — a
context edge changes no predicate and no fact, only which contexts see one another — so
what it sweeps is the **part of the widened ancestor set `super` does not see**: the
contexts a reader under `sub` sees and `super`'s ancestor set does not hold
(`context-move`'s `:under` and `:below`). `super` sees every context of its own ancestor
set, so a pair whose facts, mark and `genl` edges all lie there was merged at `super` when
the last of them arrived, and the readers see that merge through the edge. When a context
of the swept part states a cached relation (a mark, a `genl` edge, an equality) or an
`except`, a pair stored above can clash at a reader and not at `super`, and the sweep
reads every context the readers see instead (`special/below-sweep-side`; `lein
perf`'s `genlcx-edge-beside-seen-functional-facts`). It keeps the stored facts there whose functor a mark
could reach, up to `tax/*exposure-instance-budget*` candidates (below), and hands each
to `special/derive-functional-equalities` **at its own storage context**, which sweeps
every reader below that context (`context-down`), the joining context the edge connected
among them. The readers are swept most general first (`special/merge-readers`), so a reader
below one that holds the merge sees it and skips the pair. A fact stored in CxUniverse
sweeps CxUniverse and every context storing a fact of a predicate related to its functor,
since every context sees CxUniverse with no stored edge
(`equality_test/a-fact-in-cxuniverse-merges-with-one-in-a-context-no-edge-names`). Two blind sibling contexts
each holding one of two clashing fillers derive nothing until *both* of the edges wiring
some context under both of them have landed — visibility is the union of every edge that
grants it, not the effect of the latest one alone. Written the
ordinary way — declaration first — the sweep finds an empty extent and costs one root
read.

**This one direction is budgeted, unlike the other three.** A `genl` edge's subtree is
bounded by the vocabulary under the predicate the edge names —
where a `genlCx` edge names two *contexts*, and the ancestor set they open can be large even when
the edge itself is small: a context wired under a large store exposes all of it. `equate-under-context-edge` caps its candidates at
`tax/*exposure-instance-budget*` (shared with `vaelii.impl.settle`'s own bounded sweeps,
so one dial governs every cross-context sweep in the KB) and, past it, files a
`:context-edge-exposure-truncated` violation — never silently. Unlike a cut sweep in
`settle`, whose residual a later settle's resumed sweep re-examines, a merge this cap
prevents has no second chance: nothing re-triggers on a `genlCx` edge that already
finished landing, so the pairs past the cut stay unmerged for good, this edge.

**All three run for an edge nobody asserted.** A `genlCx` edge reaches the store by
three entry points: asserted (`assert-entry/assert-one`), concluded by a rule
(`chain/place-fact-conclusion`), or **computed** by the structural producer off a
`contextArgSubrelation` declaration ([context-nat.md](context-nat.md)). The settle's
drain runs `migrate-under-context-edge`, `equate-under-context-edge` and
`antisym-equate-under-context-edge` for every `genlCx` move, whichever entry point stored
the edge ([contexts.md](contexts.md#one-context-move)), and the producer settles once it
has built an edge. A calendar month→year edge therefore merges two fillers of one
functional slot it makes jointly visible, whether the year's fact was written before or
after the month existed.

**Past that cap, and only past it, order independence is a residual rather than a
guarantee.** The ancestor set is enumerated in handle order — assertion order — and the budget
takes a prefix of it, so which merges a cut edge derives depends on when the facts
arrived. Sorting the ancestor set to content order would remove that and is refused for a
measured reason: the sort forces the whole extent, which is the cost the cap exists to
refuse, and a context cycle makes the ancestor set the graph ([taxonomy.md](taxonomy.md) has the
measurement). So the residual is left, and left **named** — the violation is filed on
every cut, so no reader has to infer completeness from silence. Below the cap, which is
every KB that has not put more than `*exposure-instance-budget*` marked facts in one
ancestor set, the sweep is exact and the invariant holds outright.

The four directions hand each pair to one derivation, so the equality names both facts
and the declaration whichever way round it was reached, and retracting any of the direct
antecedents un-merges. Re-deriving is idempotent — `same-class?` skips a pair the closure already holds and
`has-justification?` skips an argument it already has — so a slot filled by three values
collapses to one class rather than to the first pair walked. The sweep reads what is
**stored** rather than what is believed, for `entail-existing`'s reason: an equality
derived off a defeated fact rests on that fact and is defeated with it, where skipping it
would leave the merge missing when the fact revives.

**A merge copy that a more general merge covers is dropped.** A reader that sees a pair in
one class derives no merge of it, and the readers are swept most general first, so a
merge stored first in a context holds no copy below it. A merge placed later in a more
general context, or a `genlCx` edge that puts a copy's context under a context holding the
merge, leaves a copy that the other arrival order never stores. The settle drops the
copy's collision justifications, as it drops a mint placement a `genlCx` edge displaced
([argtypes.md](argtypes.md#where-a-mint-is-placed)), and the twins restated under the copy
go with it (`special/covered-merges`). A copy at context `c` is covered when `c` sees its
pair in one class over the equality supporters stored in a context `c` sees and that does
not see `c`: the reader's own skip test (`res/same-class-in?`), so a class joined by
several merges or a stated equality covers a copy as a literal copy does, and a supporter
an `except` or a placed defeat hides from `c`, directly or through an antecedent, covers
nothing there. The candidates are the merges in each class the equality partition moved
since the settle's last pass, and the merges stored in the contexts where a `genlCx` move
can displace a placement (`tax/context-move`'s `:displaced`). A `recover` replays every
equality supporter into the partition, so its settle asks every class. So an `except` of
the more general merge hides the pair below it in every order
(`genlcx_move_gain_test/a-merge-below-a-more-general-one-is-retired-in-every-order`), and
an `except` of a `genlCx` edge the more general merge rests on lets the reader below
derive and keep its own copy (`a-merge-whose-cover-an-except-hides-is-derived-again-in-every-order`).

**A mark that revives runs its arrival sweep again.** A defeat of the declaration or of a
`genl` edge the merge descended through takes every merge it licensed OUT through the
JTMS, since each names it among its antecedents, and a revival brings them back the same
way. A fact that arrived **while** the declaration was OUT merged nothing: its own
direction read a taxonomy without the mark, and the declaration's arrival was already
over. So `settle` hands every datum it revives to `special/revived-declaration-sweeps`,
which runs `equate-existing` and `antisym-equate-existing` for it as its arrival did
(`order_independence_test/a-revived-mark-reaches-the-facts-that-arrived-while-it-was-out`).
The sweeps read the taxonomy, so the settle reconciles its caches over the revived datums
before them: a datum a relabel inside the settle revives, such as a `genl` edge whose void
firing a forced-monotonic declaration releases, is otherwise in no cache until `settle-finish`
(`order_independence_test/a-genl-edge-a-released-firing-concludes-merges-what-its-arrival-merges`).
A rule-concluded declaration the labeller holds OUT at its arrival, such as one a void
firing concludes, runs neither sweep then. The settle that brings it IN runs them, so the
equality arrives believed and migrates the class
(`order_independence_test/a-mark-a-void-firing-concludes-merges-nothing-until-the-release`).
An `except` of the declaration moves which readers see it without a relabel, so a fact
that arrived while the except stood merged nothing either. Every `except` that arrives,
leaves or changes label queues its target, and the settle runs the same sweeps for it
(`special/except-move-sweeps`), together with the migration an equality's arrival runs
when the target is an equality ([equational.md](equational.md#an-except-of-an-equation);
`order_independence_test/an-except-that-moves-reaches-what-an-equality-or-a-mark-restates`).

A revived `genl` edge under a `functional`, `functionalInArg` or `anti_symmetric` mark
runs `equate-under-edge` and `antisym-equate-under-edge` over one walk of its spec subtree
(`special/revived-edge-sweep`), offering the walked facts to the candidate index as the
arrival does: to the converse candidates alone under an `anti_symmetric` mark
(`order_independence_test/a-revived-genl-edge-offers-its-subtree-to-the-converse-candidates`).
That walk is **budgeted** where the arrival's is not:
a settle revives an edge far more often than one arrives, and `lein perf`'s
`constraint-genl-mark-descent` holds a revived edge flat in the subtree past
`tax/*exposure-instance-budget*`. Below the budget the revival merges what the same
sentences in any other order merge. Past it the walk stops, files one
`:genl-edge-revival-truncated` violation naming the edge, and the facts past the cut that
arrived while the edge was OUT stay unmerged. The walk reads the subtree's predicates in
content order and each posting in the index's order. An edge under no such mark reads two `props-over` closures and walks
nothing, which `constraint-genl-edge-unmarked` holds flat
(`order_independence_test/a-revived-genl-edge-merges-up-to-the-budget-and-names-the-cut`).

The equality also names the `genlCx` edges its reader sees each fact and the declaration
through, one path each (`checks/visibility-support`), in all four directions. Retracting
the edge that made the pair jointly visible un-merges, and a second path draws the merge
again (`special/rederive-descended`;
`order_independence_test/a-merge-seen-through-a-context-edge-given-back-is-the-merge-that-never-came`).

## Storage

The closure is a fourth cached relation in `vaelii.impl.taxonomy`, beside `genl`,
`genlCx` and the predicate metadata, and inherits their `:support` discipline: an edge
is active only while some sentex asserting it is IN in the network, a scoped read filters
each supporter through the read walk ([nmtms.md](nmtms.md#a-read-with-no-reader)), and
`refresh-beliefs` reconciles at the end of every `settle`.

It is an **equivalence**, not a partial order, so it is stored as a partition —
member → class, class → members and representative — rather than as up/down
closures. Insertion is a union that re-keys every member of the joined class, so growing
one class to n members costs Θ(n²). Deletion can **split** a class, which
union-find cannot undo, so a retraction rebuilds the affected class from its
remaining believed edges — the same shape as the ancestor-set-local `genl` deletion, and
bounded by the class rather than the KB.

`closures`-style from-scratch recomputation survives as the oracle, and the
incremental result is checked against it after every edit, as
[taxonomy.md](taxonomy.md) describes for `genl`. `recover` rebuilds the partition from
the stored `rewriteOf` / `sameAs` / `equals` sentexes and recomputes supersession from
it.

## Public surface

`genl` has `genls` / `specs` / `genl?`; `genlCx` has `context-up` / `sees?`.
Equality gets the same treatment, or an application cannot see what merged:
`representative`, `same-class?`, `equiv-class`, `deprecated?`. Without
`deprecated?` in particular, nothing outside representative *selection*
distinguishes `rewriteOf` from `sameAs` at all, and the doc's claim that one
deprecates and the other does not would be unobservable.

All four take an optional context, and all four have to: they read one partition, so a
scoped `representative` electing `Bravo` beside an unscoped `deprecated?` calling
`Bravo` retired is two answers about one context. The unscoped arity asks about the KB
rather than from a vantage, which is what a `?ctx` goal means everywhere else.

`why-not` gains a reason. A superseded spelling is none of `:not-stored`,
`:defeated` or `:unsupported` — it is `:superseded`, naming the representative that
displaced it.

## Interactions

- **Disjointness.** A merge can *create* a clash: `(dog Rex)` + `(cat Fluffy)` + merge
  makes one individual both. Migration asks each twin what `place-conclusion` asks a
  rule's conclusion (`checks/derivation-violation`), so the twin is stored, supersedes
  its original, and the clash is placed as a nogood and reported in
  `contradictions` or `conflicts` like any stored clash. A member OUT when the merge
  arrives is restated too, with a twin labelled OUT beside it, so which spellings are
  stored does not depend on which member the clash had defeated. A nogood placed over
  the originals before the merge keeps its placement, since the families detect over
  the network's IN label, and the reports leave out its `contradicts`, which names a
  superseded member ([nmtms.md](nmtms.md#a-nogood-placed-as-a-conclusion)). An
  inadmissible twin (an argument conviction, a malformed sentence) is dropped, its
  original stays believed, and `violations` reports the drop.
- **Stratification.** `different` in a rule antecedent is a **negative
  dependency**, so it joins the rule dependency graph beside `exceptWhen`
  ([exceptions.md](exceptions.md)). A rule concluding an equality from a
  `different` antecedent is a cycle through negation and is rejected — otherwise
  belief would depend on arrival order. The same refusal covers a rule concluding
  `indeterminate_term` or a `genl` into it, since the unique-name assumption is
  suspended for a member and the guard is withdrawn the same way
  ([predall.md](predall.md)). The negative edge runs to the three equality relations.
  `different` reads stored merges, memberships and edges, so the edge leaves only a rule
  whose conclusions are stored: a `set/backwardRule` concluding an equality closes no
  cycle through a `different` reader.
  `checks/negative-edge-rules` reads the re-check index beside the antecedent index, so
  a stored `different` rule keeps a `genl` edge's stratification walk on, and a cycle a
  later taxonomy edge closes beneath it is refused.
- **A rule concluding one of the three relations merges.** A rule-concluded
  `(sameAs A B)` reaches `special/integrate-equality-sentex` — the same arm the table
  runs for an asserted one — so the closure learns the edge, migration restates every
  sentex it displaces, the retired spelling stops being believed, and a migration the
  integrity checks refuse is filed as a violation. `rebuild-taxonomy` replays every
  stored `rewriteOf` / `sameAs` / `equals`, so a derivation path that skipped the merge
  would leave a running KB and its own restart disagreeing about what the KB entails.

  It is reached **by name rather than by the `:derived?` flag** `genl` carries, and the
  reason is the return value: `integrate-transitive` discards what an arm hands back,
  and here that is the work — the twins, which are seeds this chaining run has to take,
  and the violations, which are somebody's to report. It runs **after the conclusion's
  justification**, since migration justifies each twin by the equality edges it believes
  and a node nothing supports yet merges nothing.

  The migration writes from inside the join that concluded the equality, under two
  conditions. The twins go **back on the agenda**, like every other new datum
  `place-conclusion` returns, because the retired spelling stops matching the moment the
  supersession lands, and a rule that had not yet reached the original would otherwise
  fire on neither spelling. The arms migration runs re-enter neither `assert` nor
  `chain`: they add cache entries, justifications and re-check queue items
  (`special/integrate-twin`). `derive-functional-equalities` concludes a merge from the
  same place.
- **A rule naming a retired spelling is restated.** A merge that displaces a symbol a
  rule mentions migrates the rule, an individual constant as much as a predicate or a
  type (`kb/rewritable-sentex?`; "Merging predicates and types" has the mechanism). The
  twin names the representative and fires on the facts restated under it, and the
  original is superseded where the merge is visible
  (`equality_test/a-rule-naming-a-retired-spelling-fires-under-the-representative-in-every-order`).
- **Symmetric predicates.** Argument sorting for a symmetric predicate is done at
  canonicalization time against the *stored* symbols. A later merge changes what
  the sorted order should be, so migration must re-canonicalize rather than
  substitute textually.

- **Deferred literals are evaluated in a forward join, and `different` at the
  placement.** Being deferred is about *ordering*, and ordering is not evaluation. A
  forward join that matched every antecedent against the index would look a `lessThan`
  (or `evaluate`) antecedent up as a fact nobody stores, find nothing, and
  kill the join; `chain/join-antecedent` instead sends a deferred antecedent to
  `provers/solve-goal`, the same registry the backward chainers discharge it through.
  The two ask at **different contexts**, though: the forward join asks at the wildcard
  `'?ctx`, which reads the whole equality partition, where a backward search reads the
  partition its goal's context sees. So the forward join withholds a `different`
  antecedent (`chain/join-order`) and decides it at the placement: a firing whose
  `different` fails in the conclusion's context is refused and recorded
  (`chain/refusal-reason`, `:naf`), and the re-check re-decides it when a merge arrives
  or leaves. A reader below the placement that sees a merge joining the two arguments
  reads a guard defeat of the conclusion, as an `unknown` that holds there does
  ([naf.md](naf.md)). The defeat rests on the supporters of one path joining them at
  that reader, or on the membership making an argument an indeterminate term, and on
  the `genlCx` edges the reader sees them through (`chain/different-guard-placements`),
  so retracting one releases the conclusion there
  (`equality_test/a-merge-below-the-placement-defeats-a-different-guarded-firing-there-in-every-order`).
  See [inference.md](inference.md) for the pair and for what the justification records.

## What is not built

A schematic equation with variables is oriented by the Knuth-Bendix order into a rewrite
rule that normalizes stored terms and goals alike ([equational.md](equational.md)). A
compound equality over **reifiable NATs**, `(equals (MotherOf A) (MotherOf B))`, needs
nothing more: each side reifies to its constant before it reaches the closure
([nat.md](nat.md)). These are not built:

- **E-unification and paramodulation**: proving `(equals ?x ?y)` by searching rewrites
  of a goal on demand. A goal open on both sides returns the stated equations only
  ("Answering an equation").
- **Knuth-Bendix completion**: a non-confluent rule set is reported as a
  `:non-confluent` violation and not completed ([equational.md](equational.md)).
- **AC-rewriting**: a permutative equation, `(rel ?x ?y) = (rel ?y ?x)`, is refused.
- **Equality over structural NAT and evaluated functions**: the compute provers
  (`sameQuantity`, `evaluate`) answer it, not the closure.
- **`differentFrom`**: `different` is not assertible
  ([defenses.md](defenses.md#there-is-no-assertible-differentfrom)).

## Merging predicates and types

`rewriteOf` reaches predicates and types, not only individuals — vocabulary
alignment on import (`birthplaceOf ⇒ bornIn`, `dog ⇒ canine`) produces co-referent
*predicate* and *type* names on day one. Because a merged term now heads sentences
(functor position) as well as filling arguments, the migration reaches further than
individual merging:

- **Facts and declarations** headed by the retired term are re-canonicalized under
  the representative and stored as justified twins, exactly as an argument-position
  occurrence is. So `(birthplaceOf Ada London)` becomes `(bornIn Ada London)`, and
  the predicate extent of `birthplaceOf` no longer answers a believed query.
- **The `genl` closure** moves with a merged type: `(genl dog animal)` migrates to
  `(genl canine animal)` and `isa?` / `genls` / `specs` answer under the
  representative, the retired type's edge dropping as its declaration is superseded.
  A twin edge brings the facts under it to the rules above it, as an asserted edge does
  (`special/minted-seeds`), whichever path stored the twin: the merge, a fact or edge
  arriving after it, or an `except` of the merge leaving.
- **The flat caches** — `disjoint`, the predicate metadata (`transitive`,
  `symmetric`, `inverse`, `functional`, …), metatype membership — follow, since each
  declaration is a sentex the merge re-canonicalizes.
- **Rules** are migrated too (the supersession check above), through the same justified-twin path:
  the rewritten rule re-posts under the representative's predicates in the rule
  index, keeps its `:engines` / `:defeasible` / `:effect` (re-applied by `rules/rewrap-sentex`,
  since the wrappers ride the record, not the stored sentence), and fires under the
  representative while the original is superseded. **In both arrival orders**, which is
  the rule entry point's own arm: `migrate-class` restates a rule already stored when the merge
  arrives, and `assert-rule-sentence` restates one written afterwards, seeding the twin
  beside the rule itself — the spelling the author wrote in stops firing the moment the
  supersession lands.
- **Handle-naming metas travel with their target.** A meta names another sentex by
  handle — an `exceptWhen` names the rule it guards, an `except` names the sentex it
  hides, a `target_following_predicate` reply names the claim it hangs on — all shaped
  `(P … (sentexHandle H) …)`. Migrating H to a new handle H′ would strand every one of
  them, so the twin fires *unguarded*, becomes *visible*, or names a claim no longer
  believed. `migrate-handle-metas` re-points each of H's believed metas onto the twin
  (an `exceptWhen`'s query rewritten and realigned too; an `except` or reply's terms
  rewritten and its handle retargeted), derived and justified by `[the meta, the
  equality]`, so the twin ends properly qualified and retracting the merge collects the
  meta twins and revives the originals. This runs in **both arrival orders**: for a meta
  that predates the merge, `migrate-into` carries it as it migrates the target; for a
  meta asserted *after* the merge — when migration already ran and never saw it —
  `migrate-meta-onto-twins` replays the same carry onto the live twin at the meta's
  entry point (the exceptWhen entry point and the ordinary fact entry point alike), idempotent for the metas
  already carried. A NAF `(unknown …)` antecedent lives *in* the rule sentence, so it
  rewrites with the rule and re-posts through the twin's own `index-rule-sentex`. A
  predicate merged only in an exception's *query* (the rule itself not migrated —
  `penguin` in `bird ⇒ flies exceptWhen penguin`) is handled by the ordinary
  meta-sentex migration, which rewrites the query onto the representative so it keeps
  blocking the migrated facts.

`rewriteOf` is the spelling relation, so it is the one that carries alignment across
predicates and types, and
`wff` enforces that a `rewriteOf`'s two sides are the **same role** —
predicate-with-predicate, type-with-type, individual-with-individual — since a
cross-role merge is meaningless and a likely import bug. A bare lowercase word is
`:either` and accepts any non-individual partner; a **namespaced** symbol is `:opaque`
and accepts every partner, because the roles are conventions over names a person chose
and a reified NAT constant ([nat.md](nat.md)) is one the engine minted — what it
denotes is settled by its materialized result types, so retiring one into the real term
its function's corresponding predicate names is exactly the move this check must not
refuse.
