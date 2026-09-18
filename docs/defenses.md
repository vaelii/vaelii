# Design defenses

- **Covers:** why a belief-and-contradiction decision is shaped the way it is, and why
  the alternative a reader would reach for is worse. The argument a how-to doc points at
  rather than restates.
- **Not here:** how any of it works — each entry names the subsystem doc that describes
  the mechanism, and assumes you have read it. The vocabulary → [glossary.md](glossary.md).
- **Assumes:** the mechanism you came for the rationale of. This doc argues about a
  design; it does not teach it.

A subsystem doc says **how** the engine works. A few of its decisions are non-obvious, or
have a tempting alternative that fails for a reason recorded here once — and left in
the how-to doc that argument grows until the mechanism is hard to find under it, and the
same argument gets re-derived in three sections because it bears on all of them. So the
argument lives here, under a stable heading, and the how-to doc states the rule and links
to it. Where one argument bears on several places, those places link to **one** entry
rather than each carrying a copy.

Each entry names the doc it defends, and the sections below follow the grouping the
[doc map](README.md) uses.

Many of the entries defend a **refusal**, and none of them indexes one. The `:type`
keyword a refusal carries is looked up in
[troubleshooting.md](troubleshooting.md#i-have-a-type-and-do-not-know-what-it-means),
which holds the whole vocabulary and the page that owns each; come here for why the entry point
refuses, go there for what a keyword you caught means.

## Belief and truth maintenance

Defends [nmtms.md](nmtms.md).

### Two strength classes, not three

There are exactly two assumption strengths, `:monotonic` and `:default`, and derivation
adds none. A third is tempting: something between them would let `penguin ⇒ ¬flies`
outrank the default `bird ⇒ flies` without the penguin fact having to be known-true.

Do not add it. That one problem is [`exceptWhen`](exceptions.md)'s, and it needs no rank:
a rule states its own exception and does not fire, so nothing has to out-rank anything. A
class between the two buys that single case and costs the total order **monotonic >
default** everywhere else — and the total order is what lets `decide-nogood` resolve a
clash by defeating the strictly-weaker member with no solver. An intermediate class turns
every unequal pair into a question of which of three ranks each side holds, for a case
already handled structurally.

### A bare re-assert never downgrades the class

A re-assert takes the stronger of the two classes (`strength/max`), never the weaker. The
mark is resolved from *content*, the way a re-asserted rule's slots are
([canonicalization.md](canonicalization.md)).

The alternative — last-writer-wins, the mark taking whatever the latest assertion carried
— reads a re-assert's silence as a claim. A re-assert carrying no `:strength` states
nothing about the class; the `:default` it falls back to is the entry point's fallback, not the
caller's claim. Treat that silence as a downgrade and arrival order decides belief: assert
`S` known-true, re-assert it bare, then assert the known-true `¬S`, and a last-writer-wins
mark leaves `S` **defeated**, while the same three sentences in the other order leave the
pair an irreducible clash. `strength/max` is commutative and idempotent, so every order
agrees and a third assertion changes nothing. Narrowing a class is deliberately not a
re-assert but `retract!` and re-assert — the retraction takes the mark with it, so nothing
is inherited across one.

### A firing is capped by its weakest ground

A justification confers `min(its own strength, the weakest of its antecedents' classes)`,
and the taxonomy edges a firing names — a `genl` edge a subsumed match climbed, a `genlCx`
edge the conclusion's context reads the rule or facts over — are grounds like the facts and
cap it the same way.

Without the cap, a bare rule over a merely-default premise would conclude `:monotonic`,
and a rule would **launder** a default into something a directly-asserted default cannot
contradict: a conclusion carrying more authority than any of its grounds. Read across a
merely-default context edge, known-true facts under a bare rule conclude `:default` for the
same reason — the sighting is as defeasible as the edge that carries it, and a conclusion
stronger than the wiring it was read over is the same laundering.

The **informant is not in the cap**, though a justification is valid only while its rule
is believed. That condition is what makes retracting or defeating the rule withdraw
everything it licensed — a *validity* role, not a ground. A rule takes `:default` unless
its own assertion says otherwise, exactly as a fact does, so capping on it too would drop
every datum an ordinary rule licensed to `:default`. This is why a rule's own class
(`:strength`, what `defeat-class` answers for its handle) and its defeasibility
(`:defeasible`, which `set/defaultRule` spells and `chain/rule-view-of` reads to decide
what its firings confer) are two slots: only the second moves belief, and nothing in the
engine defeats a rule, so the first takes part in no contest.

### The subsumption path is the widest bottleneck, not the shortest route

A `genl` edge can itself be defeasible, so when a fact reaches a rule antecedent of a
different functor across the closure, the edges the match climbed become antecedents of
the firing and the cap above floors the conclusion at their weakest class. Which *route*
through the taxonomy the walk names therefore decides how strongly the conclusion holds,
and the obvious walk names the **shortest** one — the fewest supports the reachability can
be made to depend on.

Do not keep the shortest route here. Fewest supports is a reasonable thing to optimize and
it is not the same thing as strongest: on a hierarchy offering a one-hop `:default` edge
beside a two-hop all-`:monotonic` chain, the short route floors the conclusion at
`:default` while a `:monotonic` derivation of the identical conclusion exists and the
engine merely declined to find it. "Fewest edges" never asked how strongly each edge
holds, so the class a conclusion is reported at would be an accident of how many hops its
cheapest witness happened to take — arrival order wearing another hat, since the cheapest
witness is the one that happened to be asserted.

The walk takes the **widest bottleneck** instead: the route whose floor — the `min` defeat
class along it — is highest, tie-broken by depth then by the name order every closure read
uses, so the choice is a function of the hierarchy and never of a handle. It adds no third
class and invents no second lattice — a path's rank is the `min` over its edges' classes,
the same fold `strength` folds over a justification's antecedents, so the two compose
rather than competing. `kb/reach-strength` reads that floor off the same chosen path, so
the reported class and the witness that justifies it never disagree ([taxonomy.md](taxonomy.md),
*Strength of a subsumption path*).

Only the `genl` subsumption a firing rests on asks for the widest route, because only there
does a supporter's *class* change an answer the engine gives. The `genlCx` visibility a
placement is recorded over still takes the shortest path — most general supporter per edge
— because placement asks whether an edge is *seen*, not how strongly it holds; routing it
to the widest bottleneck would make where a firing is filed depend on a defeat class that
can move under it.

### The class fixpoint is a least fixpoint, not a single pass

`jtms/region-classes` solves the recursive class equation — a node's class depends on its
antecedents' — as a least fixpoint inside the region relabel, every in-region IN node
starting at `:default` and a semi-naive worklist iterating to stability.

A single pass would be wrong in a way that looks fine. Visited one way it reads a
not-yet-computed antecedent as bottom and under-rates the conclusion; visited the other it
reads a stale value and over-rates it — so the answer would depend on visit order, which is
arrival order wearing a different hat. The operator is monotone and the iteration starts at
bottom, so the least fixpoint is unique and therefore independent of the worklist's visit
order and of the order the knowledge arrived in. Uniqueness is also why locality costs no
order independence: a least fixpoint over the region with boundary labels fixed has the
same unique solution a global fixpoint would produce, so there is nothing for a visit order
to influence.

### Locality is a claim about every representation

The locality guarantee — no operation recomputes the whole graph — is a claim about every
representation of the network, and a perf table over the reference network tests only one.

The reference network's persistent maps are region-local by construction. The dense network
([density.md](density.md), Phase 3) holds belief in `RoaringBitmap`s, where any operation
that rebuilds a bitmap costs one pass over all of its 65,536-value containers — so it
satisfies locality up to 65,536 nodes, where there is exactly one container, and silently
violates it above. At the largest graph a reference-network table measures, nothing could
show it; it takes a rebuild over three million premises, where the copying shape costs
14.9× per premise and the reference stays flat. So whatever else a second
representation is proven to match, **cost shape is part of it** — an oracle test that
compares only answers passes a representation whose answers were never wrong and whose cost
grew with the KB.

So the guarantee is carried in three pieces, and they are secured three different ways.
**Equivalence** — a region relabel reaches the same labels a global one would — is
semantic, and `jtms_dense_oracle_test` holds it by comparing the whole network after every
step. **Containment** — the flips sit inside the published window and the window inside
the region — is what says a small region was *asked for*; the oracle checks it on both
networks after every step, and `jtms_locality_test` measures the published window across
graph sizes on both, since a widened region answers identically and would pass a
comparison of labels alone.

**Cost shape** is the third, and it is really two claims. That no work is paid *per
boundary node* is structural: the `Tms` protocol passes the network plus integers and
plain values and nothing else, so no implementation of it can turn a boundary read into a
lock and a slot decode, or into a round trip. That is why the strength cache is resident,
and it is what makes this a claim about representations rather than about the reference's
happens-to-be-free reads. The cost of the in-region work itself is what is left, and that
is where the bitmap-rebuild shape hides — it satisfies equivalence, satisfies containment,
pays nothing per boundary node, and still grows with the KB. Nothing structural rules it
out and no unit test reaches the scale that shows it, so it is held by `lein bench-jtms`
and by review. Which is why it is written into the `Tms` docstring beside the three
obligations that do have gates: an implementation that is never told about a claim cannot
be held to it.

### Two TMS implementations, not one

The network sits behind a `Tms` protocol with a `:reference` and a `:dense` implementation
rather than one adaptable structure, and two properties are why — both easy to assume and
both wrong. (What a *third* one would owe is not restated per implementation: the `Tms`
docstring lists the four obligations with the gate that holds each.)

A dense network cannot simply replace the reference. `RoaringBitmap` is mutable, and
`jtms_atomicity_test` pins that a mutation applies all-or-nothing; a mutable bitmap inside
a persistent value would break `swap!`'s retry and let a reader observe a half-applied
relabel. So the dense one serializes its writers on the exclusive stamp of a `StampedLock`
and validates its readers against them (below), while the reference one gets its consistent
snapshot from a single deref.

Order independence rests on the backward dependency and the forward propagation being the
**same** edge set. The class fixpoint re-examines a node when something it derives from
moves, reached through `:consequences`; if a justification id were ever rebound to a
different justification, a node's `:supports` would name a justification that now concludes
elsewhere, and its class would depend on a value the propagation can never carry to it — at
which point the answer depends on visit order, in either implementation. `p/next-id` is
monotonic, so the engine cannot construct that state.

### Tie-breaks and orderings key on content, not the handle

Every place the engine linearizes a set of beliefs — the tie-break in a dilemma, the stored
antecedent vector, a report's two sides, the list of reports, a list of justifications —
orders on **content**, never on the integer handle. This is one rule, and it is the subtle
half of order independence, so it has one home.

The handle is allocated in assertion order, so a lower handle marks a belief typed into the
KB earlier — "typed first" throughout this section means exactly that. Key any of those orderings on it and arrival
order is smuggled back in: the Nixon diamond elects the pacifist or the non-pacifist by who
was typed first; `(first (:sides c))` on a clash report means "which side was typed first"
on a report whose `:sentence` reads the same either way; `(first (contradictions kb))`
answers which pair was typed first on a call whose every other reading is
order-independent; a firing seeded by whichever antecedent triggered it would store `[h_b2
h_b1 rule]` one way round and `[h_b1 h_b2 rule]` the other. What a sentex *says* is the same
whenever it is asserted, so every one of those keys reads content: `solve/content-key` and
`kb/antecedent-order` take the sentence and then the context, and
`kb/justification-content-key` takes the informant's own sentence, its antecedents'
sentences, the firing's bindings and the conclusion's sentence and context — enough to
separate one firing placed into two contexts, which the sentence alone leaves tied. The two
`kb` keys are **structural** — `nm/compare-form` walks the two forms in place, so
nothing is printed and no ambient `*print-length*` can elide two long sentences to one
prefix, collapse the key and drop the tie back onto arrival. `solve/content-key` is the
one printed key of the three, with the print vars bound off, and it alone appends the
handle — only for a pair a reader cannot otherwise tell apart, since the solver needs a
*total* order to name atoms stably across runs. That last step does not undo the
rule: two beliefs with an identical content key *say the same thing*, so which one sorts
first is unobservable, and the handle separates only beliefs that are interchangeable —
never two that differ. Content decides between different beliefs; the handle only sequences
duplicates. The choice a dilemma's tie-break
makes stays arbitrary; arbitrary and stable is the contract, arbitrary and order-dependent
is the bug.

The informant enters a content key as its *sentence*, never as its handle: two
justifications for one conclusion usually differ in their rule before anything else, so a
handle there would decide the whole comparison on which rule was typed first. Ordering the
antecedent vector once, where it is built, is what makes `why`'s `:because`, `why-not`'s
`:missing` and `preview`'s `:antecedents` functions of the knowledge rather than of the
write.

The rule reaches one more shape, which is a read rather than an ordering: taking **one**
member out of a set. `matches-visible` promises the set of matches and the three extent
readers (`sentexes-in-context`, `sentexes-with-functor`, `sentexes-with-arg`) answer
everything under one index key — none of them promises which comes first, so a `first` on
one is a question about what the postings enumerate, and that is arrival order again. A
caller wanting a single answer orders on content before it takes one, bounds the read and
counts (the LLM inventory reads 64 of a functor's facts and answers the arity most of
them carry), or states why there can be only one — a `functional` predicate leaves one
value in the slot, a second symbol merging into the first through the `(equals V1 V2)` the
KB derives from the pair and a second non-symbol refused outright, and resting on that is a
claim recorded here.
`sort_by_content_key_test`'s positional-take scan reads `src/` for the ones that do
neither.

Each of those scans reads the ordering **key** as a *form*, from the call to the key's
own closing paren, rather than as the rest of the call's line. Reading it as the rest of
the line misses a key written on the next line, and the scan then passes a call it should
have flagged. A guard that narrows what it checks without turning red is the failure mode
this page collects. The same reading
carries a fourth scan that is about cost rather than order: `sort-by` runs its key fn
inside the comparator, so a key that reads the KB is a taxonomy closure re-read
~2·n·log₂n times where `nm/sort-by-content-key` reads it n times.

### The touched window is a superset, not the flip set

`settle` publishes the region it moved so three readers — a consequence preview, a
consequence report, a change feed ([preview.md](preview.md), [feed.md](feed.md)) — get one
answer instead of each diffing the believed set at O(KB) per write. The window
deliberately means *what I published about this datum may be out of date*, which is a shade
larger than *whose belief flipped*.

That extra shade is required. A **redundant justification** — a second derivation of an
already-believed conclusion, conferring no stronger a class — is the write the JTMS declines
to relabel for, and that fast path is what collapses a recursive forward load from
O(derived²) to O(derived). Belief does not move, so no label does; but in a dilemma the
engine declines to decide, and the *reason* it hands back is the whole answer — so the
consequence's handle is noted as touched even on the fast path, O(1) at the write. Polling
every standing pair for its support count at report time would be O(standing) per settle
instead. Every consumer reads the window as a superset, so an extra handle costs a
re-derivation and never a wrong answer — which is exactly what lets a clash report be
carried forward for any pair the region did not move.

### The settle memoizes standing clashes

`settle` runs after every mutation, and both the negation nogoods and the definitional
clashes carry forward the answer for any pair whose members did not move. This is a memo on
the recomputation, not an optimization to taste.

One check per standing pair per settle is quadratic in the clashes a load creates: measured
at roughly 35 ms an assert with 300 standing definitional clashes against under 10 ms with
50, and the negation half separates 12x on `lein perf`'s `negation-arbitration`, which holds 8x the
standing dilemmas to under 11x the per-assert cost. The carry is sound because the memo
compares as **values** every input a check reads that is small enough to — the
separations, the predicate properties,
the disjoint metatypes' membership — and weighs per pair the one input too big to compare,
the `genl` closure: a pair of unary memberships is decided by `disjoint?` of the two types
its sentexes name, so the memo stamps those two supertype closures, and an edge leaving both
standing is an edge the pair was not about. A `genlCx` edge retires the whole carry, since
which contexts can convict a pair is a question about the context relation rather than about
either half's reading of it.

The rule the whole scheme rests on: **a nogood whose detection reads a belief-following
cache its own member supports is not stable.** That is why `arity` is not a nogood though it
names a second believed sentex — `declared-arity` answers from a cache that follows belief,
so a nogood defeating the declaration would destroy its own premise — and reports instead.

### An un-merge re-seeds through a second channel

A datum displaced by an equality merge is OUT while its twin joins in its place, so a
partner arriving during the merge concludes at the twin's spelling. Stop believing the
equality and the twin is swept while the displaced spelling comes back — and the conclusion
has to be made again at the surviving spelling, or the KB believes both antecedents of a
forward rule and holds neither spelling of what they conclude. `settle` re-seeds the
recovered spellings and settles again.

Two other designs lose to that one on what they cost elsewhere. **Moving the reconcile into
the settle loop** keeps a single fixpoint, the better property in the abstract — but
`settle-finish` decides what the settle moved by diffing the supersession map it brackets,
so a reconcile running earlier would have to thread its own flips forward or a merge would
stop being reported as `:believed-removed` at all: a change to what every preview and feed
event says, to save a re-derivation. A **re-enter signal** from `settle-finish` is this same
second-settle loop with the bound further from what it bounds. What the shipped shape costs
is that a KB whose settle un-merges something settles twice; one that does not pays a deref
of an unbound var.

### A nogood must survive being acted on

A nogood is not merely a set of incompatible sentexes: it is a set the settle may resolve
by **defeating a member**, which makes admission a stronger question than incompatibility.
The criterion ([nmtms.md](nmtms.md), *What qualifies as a nogood*) is that a nogood stays
derivable exactly as long as what it convicts stands.

`arity` is the case that makes it concrete, and the alternative to avoid is to file it as a
nogood and let the class decide — it names a second believed sentex, it ranks like a
definitional clash, and the machinery is already there. That gives a clash decided
once. `declared-arity` answers from a cache that follows belief, so a defeat aimed at the
`(arity P n)` declaration removes the conviction's own premise: the offending sentex goes on
standing, nothing can look at the pair again, and the KB is left holding exactly what the
check exists to catch — silently, because the report is derived from the pair too. So the
retroactive half reports instead
([taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order)).

The line is **not** "a member the detection reads through". That wording indicts
`preserving-nogoods`, which is sound: its members deliberately include the reasons the
claim was inherited — the general claim, the declaration permitting the move, the relation
edges the reach travelled. Defeating one of those does dissolve the detection, and there it
is the answer rather than the bug, because an inherited claim has no sentex of its own for a
defeat to reach instead of its reasons; withdrawing the reach withdraws the claim, and the
reason stays defeated so it stays withdrawn. The two are separated by what stands
afterwards, not what the detection touched. `nogood_admissibility_test` pins the member
sets of all three shipped sources against the criterion.

### There is no second axis

Defeat-class alone cannot separate "birds fly" from "penguins do not" — both are defaults,
and since strength propagates, the exception cannot buy rank from its rule either. The
tempting second axis is a **specificity heuristic**: score a type by the size of its
reflexive-transitive `genl` up-closure, a rule by the greatest such score among its
antecedent predicates, a datum by the greatest among its valid justifications, and on a tie
in class let the more specific member win.

Do not build it. `exceptWhen` makes the relation such a heuristic can only reconstruct
explicit: the exception is stated *on* the rule it excepts, so the general rule does not
fire and there is no tie to break. Deriving an ordering from the `genl` hierarchy is
inference *about* the knowledge rather than *from* it — it works when the exception happens
to be keyed on a narrower type and silently ties when it is not, so whether it applies
depends on how the ontology was written rather than on what it says. There is a single axis,
defeat-class, and a default/default clash it cannot separate is reported as a dilemma rather
than decided.

### The solver split is guarded in both directions

Only `:default` content is ever decided; `:monotonic` is the fixed background a solve
reasons *from*. `decide-nogood` already implies it, and `settle` makes that a check rather
than a consequence, guarding both ends: `check-solver-eligible` rejects a contested handle
that is not `:default`
(read before any defeat lands, since `defeat-class` reports nil once a datum is OUT), and
`accepted-defeat` keeps only defeats the program actually offered.

The guards matter because `set-solver` takes any implementation, and an unclamped `:defeat`
would let a third-party solver withdraw known-true content the program never handed it. The
cost of a regression here is not a wrong answer; it is the engine quietly giving away
something it knows to be true. `nmtms_test` covers both guards directly; `asp_label_test`
covers the surface above them — that a plain rebuttal reaches no solver at all, and that a
monotonic handle is never given an atom.

## Namespaces and layering

Defends [namespaces.md](namespaces.md).

### The two recursion calls live in wiring.clj, not at the call sites

The engine's requires run one way, from `kb` up through `checks`, `special`,
`integrate`, `chain` and `settle` to `vaelii.core`, and the compiler checks every edge.
Two calls break that order, and both live in `impl/wiring.clj` instead of at the
call site that needs them.

Neither is a misplaced function waiting to be moved somewhere that restores the one-way
order — both are genuine mutual recursion. `assert-sentence` is called back from
`impl/nat.clj`, `impl/skolem.clj` and `impl/quasiquote.clj` because storing is a whole
assert — naming, the definitional checks, the index, chaining, settle — so the write path
itself runs chaining, and chaining mints a constant by calling back into that same write
path. The cycle is in the behaviour a NAT, a skolem witness or a quasiquotation mark
needs, not in how the code happens to be arranged, so no rearrangement removes it.
`solve-goal` is the prover registry that `impl/resolution.clj` calls to discharge a
deferred antecedent, and `unknown` runs that same registry back over its own argument —
negation-as-failure is mutually recursive with the chainer that asked for it, not merely
calling down into it.

A layering *inversion* — a namespace above `vaelii.core` that consumes its public API — is
a different case, and none is written here: a call that can point downward is made to point
downward. Two once pointed up through this file and no longer do. `impl/io/import.clj`
recovered a loaded dump by calling `vaelii.core/recover`; the rebuild moved to
`impl/recovery.clj`, below `vaelii.core`, and both `vaelii.core/recover` and the importer
call it downward. `impl/predall.clj` audited by calling `vaelii.core/ask`; the audit now
reads through `impl/provers.clj` with each goal prepared by
`quasiquote/prepare-goal-for-read`, and the `genlCx` ancestor scoping it depends on is
applied in the matching layer below anyway ([predall.md](predall.md)). Both are below
`vaelii.core` now, which requires them, so the public audit and import entry points are
ordinary downward delegations.

Gathering the two in one file beats leaving each as a `requiring-resolve` at its own
call site. Scattered, a `requiring-resolve` is invisible: nothing counts it, nothing
stops the next one, and the set of places the layering is broken can only be recovered
by grepping for it. Gathered, they are an inventory — two entries, each owing the
reason it cannot be an ordinary require — and `lein lint`'s E8 fails a written-out
`requiring-resolve` anywhere else under `src/`, excepting the optional dependencies it
names by target. Only the written-out form breaks the one-way order: a symbol computed off
a keyword-dispatch registry names no edge at read time, so E8 never sees one. A call with a
real downward fix takes the fix; one that lands in the inventory argues for itself in
writing first.

### What a term says lives below what the engine does about it

Everything the engine interprets about a functor is two things: what the term *says* —
its sentence shape, the table it caches into, the lanes that read it — and what the
engine *does* about it, the integrate / disintegrate / rebuild arms and the
well-formedness check. They are written in two namespaces, `vaelii.impl.predicates` and
`vaelii.impl.special`, and joined at load. Keeping them adjacent is the obvious
alternative and it is not available.

The arms need functions from four layers — `taxonomy` to install a mark, `wff` to check a
shape, `checks` to convict, `settle` to sweep — so a namespace holding arms sits at the
**top** of the require order by construction. Put the data there with them and `taxonomy`
cannot read it, which is precisely the namespace that most needs to know which relations
it closes. So the data goes to the bottom, requiring nothing but `clojure.*`, and every
layer above reads it: [predicates.md](predicates.md) lists the seven views that result.

Splitting them buys a check that adjacency cannot give. Two halves written side by side
agree because whoever wrote them agreed; the agreement is maintained by review, and review
is what the defects here get past. Written apart and *joined*, the agreement is arithmetic
over two enumerations, and the join is a function that can refuse: `:cached` with no cache
triple, `:checked` with no `:wff` arm, a functor armed and never declared. Each is a defect
neither half can see alone, and each reports nothing at runtime — a mark installed by one
arm and not removed by another leaks silently rather than throwing.

Where a field seems to want a *function* it holds a keyword naming one, resolved by the
layer that owns the function. That is the whole cost of the split, and it buys the
direction of the requires.

## Storage and the single writer

Defends [storage.md](storage.md).

### An as-stored read is named, never implied

Every `IndexStore` posting is storage rather than belief — a defeated default, a
withdrawn conclusion and a retired spelling all stay in it, because all three are
revivable and the JTMS is where belief lives. Both readings of a posting are therefore
legitimate, and a great deal of the engine wants the stored one: a stratification refusal
is about what is written, a re-check trigger has to over-approximate, a report on rules
that never fired must include the rules that never fired.

What is not legitimate is leaving which one unsaid. Read straight off the protocol, a
caller that meant to filter belief and forgot looks exactly like one that meant not to —
the difference is invisible in the code, invisible in review, and shows up as a wrong
answer on the first KB that defeats something. Comments do not close it: the two reads are
the same call, so there is nothing for a comment to attach to that a copy-paste will not
carry along with it.

So both readings get a name — `reads/as-stored-…` and `reads/believed-…` — and the raw
protocol read is refused outside the implementers (`lein lint`'s E16). The as-stored entry point
is the one that had to be named rather than left as the default, because it is the one
whose omission is silent: a missing belief filter answers *more* than it should, and more
is what an unfiltered read looks like whether or not anybody chose it. Naming it also
forces the docstring, which is where the actual argument lives — the roster in the lint
check records that a caller has a reason, and the docstring says what it is.

The same argument, one relation over, produces `tax/genls-global` beside `tax/genls`
(E17): a scoped closure and a global one return the *same object* on a KB where no edge is
context-restricted, so the caller that meant to scope and did not is right on every KB but
the one it is wrong on.

### Records and the index are separate stores

The record store and the index store sit behind separate protocols rather than
one, and the split follows directly from an asymmetry between what each holds. The
records are what has to survive: lose one and the knowledge behind it is gone, so
durability is the record store's problem. The index is a cache over the records —
every entry is recomputable from them, which is what lets `reindex` throw the whole
index away and rebuild it from scratch. Merging the two into one store would force
a single durability answer onto both, either persisting index structure that adds
nothing (since it is always rederivable) or leaving records exposed to whatever
cheaper guarantee suits the index. Keeping them separate lets each answer to what it
actually is: the record store to durability, the index store to representation.

### RAM records under a durable index is refused

The `:disk-log` index needs durable records, and RAM records under it is the
pairing `open-kb` refuses. The index is derived from the records, so persisting it
over a record store that empties at JVM exit would leave index files on disk
describing records that no longer exist once the process ends. The next open of
that directory would find a populated-looking index and answer every query out of
stale index state rather than out of any record actually present, with no signal
that anything is wrong. Refusing the pairing outright is cheaper and safer than
trying to detect or repair that mismatch after the fact, so the axis combination is
rejected before a KB is ever built from it.

### The two records are named for the sentence's shape, not for its role

Defends [storage.md](storage.md#the-sentex-records--literalsentex-and-rulesentex).

The record holding a non-rule sentex is `LiteralSentex`. The tempting pair is
`FactSentex` / `RuleSentex`, which looks like the obvious split and is wrong: that record
holds a fact, a metadata declaration **or** a query pattern, and only the first of those
is a fact. `literal` is the one word covering all three, because it names the sentence's
*shape* — one signed predicate application — rather than the role a caller puts it to.

Shape is also what the split is for. The discriminant every consumer uses is
`(some? (:antecedent sx))`, a question about structure, and the reason the two records
exist at all is that a literal must not carry the seven rule-only slots at 100M+ facts.
A name taken from the role would have to be re-read against the structure at every use.

### Frames are positional, not tagged

A frame holds its record's fields positionally rather than as a self-describing
map, because nippy's default encoding writes the record's type tag and every field
name into every frame it serializes. Measured on a corpus of ordinary ground facts,
that per-frame tagging costs **over half** the store's size — more durable bytes go to
field names and type tags repeated once per record than to payload. A positional frame
carries only the values, in a fixed field order the decoder already knows from the
frame's shape, so the redundant tag and name bytes are never written at all.

### The index WAL logs the operation, not the value

The index's write-ahead log records the write operation itself — `[:add-to-set k
m]`, `[:increment k]`, and so on — rather than the value the key holds after the
write. Logging the resulting value instead would mean re-serializing the whole set
on every add: the i-th add to a set of size i would write a value of size i, so N
adds to one key would cost O(N²) total WAL bytes rather than O(N). A few roots take
this hit hardest — `[:functor-root p]` and the common contexts — since they are
exactly the keys a bulk load adds to thousands of times each. Logging the operation
keeps every write O(1) in the size of what changed, independent of how large the
set it is changing has already grown.

### Torn tail recovery reads lengths, not frames

Finding where a log's readable tail ends is answered by reading each frame's
length and skipping ahead, never by decoding the frame's payload. The question
being answered is only how long the log is, not what it contains. Answering it by
thawing every frame ties the length-finding walk to the frame decoder's own ability
to read that data — and that coupling is exactly what makes a record class rename
dangerous: thawing every frame to find the tail would read the decoder's failure on
old data as a torn or unreadable log, and delete the store it could not decode
rather than the store it could not read. Reading only lengths keeps the walk
independent of the frame decoder, so a decoder that cannot read old data has no
power to make the recovery path erase it.

### The columnar and dense backends use unsynchronized fields

The `:columnar` and `:dense` index backends hold their mutable state in
`^:unsynchronized-mutable` fields — and, for the token dictionary the columnar trie
labels its edges from (`vaelii.impl.tokens`), in a bare `HashMap` and `ArrayList` —
rather than behind a lock or an atom, unlike the
rest of the engine's single-writer contract. Making them synchronized would buy a
consistent view for an incidental reader thread — one who reads the index
concurrently with the writer, such as a browser thread beside a REPL's KB — but the
engine's own single writer never needs that guarantee, since it is always the
thread doing the writing. The walk reads these fields at every frontier node, which
is the index's hottest loop, so paying for a volatile read or a lock acquisition
there would tax every lookup to protect a case that does not occur under the
contract the engine actually requires. The cost is pushed onto whoever keeps an
incidental reader off the writer's thread or behind a synchronizer of their own,
rather than paid by the writer on every read the walk makes.

The **dense truth-maintenance network** (`:tms :dense`) makes the opposite call, and
the difference is that it is the *default* — an opt-in index backend can push the
synchronization cost onto whoever selected it, but a default cannot ask that of every
KB, so it must honour the incidental-reader guarantee itself. It does, through a
`StampedLock`: point reads run optimistically and validate, so the steady-state read
stays lock-free like the index walk, while a reader that races a relabel is validated
into a consistent retry rather than left to tear. What the steady-state `in?` pays for
that is a stamp read and a validate, and no allocation — the torn case is marked with an
interned keyword, measured at 0 extra bytes against the unlocked read. The dense probe is
still an order of magnitude faster than the reference network's hash-set lookup it stands
in for as the default ([density.md](density.md)), so unlike the index there is no
hot-loop tax to weigh against the guarantee. Iterating reads take a
shared stamp outright; they already allocate O(nodes), so the acquisition is lost in
the walk.

### A reasoning image is installed whole or not at all

A label is a fixpoint over the justification graph, and one assert can move an unbounded
region of it, so the network cannot be a write-ahead log
([why the index persists and these two do not](storage.md#why-the-index-persists-and-these-two-do-not)).
A reasoning image is a snapshot instead: the whole network and the state around it, written
between operations and installed on the next open in place of a recover
([storage.md](storage.md#the-reasoning-image)).

An image is installed only against the exact records, source identity and policies it was
written under, and any mismatch discards all of it. Nothing reconciles an image against
records that moved. A partial reconciliation would label a node with a value no derivation
over the current records produced, and a label nobody computed is the failure
[order independence](nmtms.md) rules out. Installed whole, an image is the state of the KB
that wrote it: an image written after a recover is that recover, and one written at close
by a KB built assert by assert carries that KB's labels, which equal a recover's because
belief is order independent.

The stamp covers the source as well as the records because a label is a function of both:
the same records under a changed settle rule label differently. The source identity hashes
the engine definitions recovery and the write entry points can run, read as forms with
comments and docstrings removed. A prose edit keeps an image, and so does an edit to a
definition recover never reaches; an edit to a definition it reaches discards the image.
The walk over definitions reads no local scope, so a local that shares a var's name reaches
the var, and the digest covers more forms than recover runs rather than fewer. A KB running a prover or evaluatable registered from outside the engine takes no image,
because that code is outside the digest. Every mismatch class costs a recover, which is the
path an open without an image runs, so the worst a declined image does is make an open as
slow as it is with no image at all.

### The bulk-load protocol is a sink, not a batched put

A store that can write many records at once — `COPY` on a server, one packed append on the
disk log — needs the engine to hand it many records, and the obvious protocol is a `put-many`
taking a batch. It does not fit what the loader does. `import!` indexes each record from
the copy it holds and needs that record's **handle now**, before the next one is read: a
batched put decides the handles inside the store and answers them afterwards, so the loader
would have to hold the whole batch's frames a second time and re-walk them to index. So the
handle is decided caller-side and the sink is told, which is also what preserves a dump's
own numbering through a load. What that costs is one restriction stated rather than
discovered: a record written to a sink is not readable until the sink closes, since a store
buffering a copy stream has nothing to answer a `get-sentex` with. A loader reads its own
input, not the store it is filling, so nothing in the engine asks.

### The enumerations promise a Set, not a Clojure set

`sentex-ids`, `justification-ids` and `premise-ids` say a caller may `contains?`, `count`,
`seq`, `sort` and `=` the answer — the `java.util.Set` contract — rather than that it is an
`IPersistentSet`. The narrower promise is the point: the shape is what costs at scale. A
`PersistentHashSet<Long>` retains 48–75 bytes a handle — 9.47 GB at 100M records, which is
what `lein bench-budget` carries that shape to ([storage.md](storage.md)) — held while
`recover` walks the premises and the justifications on top of it; the same handles as a
`Roaring64Bitmap` behind a `java.util.Set` measure 33.0 MB over the strided run
`next-id` mints, and answer
`contains?` faster than the hash set rather than slower. Promising `IPersistentSet` would
make that substitution a breaking change for every store rather than a choice each one
makes. A caller wanting `conj` / `disj` / `clojure.set` converts with `(set …)` at the site
that wants them, which is the site that can afford it.

The disk store takes the substitution one layer in rather than at the boundary: it *holds* the
bitmap and still *answers* a Clojure set
([storage.md](storage.md#the-enumerations-and-what-a-roster-costs)). Residency and a
caller's peak allocation are separate arguments, and keeping them apart is what let the
first be won without touching the second.

### A frame naming a class is refused, never resolved

Every nippy thaw the engine runs over a file goes through one entry point
(`vaelii.impl.io.thaw`), and that entry point's allowlist of class names is **empty**: a frame
that names a class is refused (`:disallowed-class`) before the name is resolved.

The reason it has to be an entry point rather than a trust is what a class name costs on the way
in. nippy's frozen form can name a class in three of its type ids, and reading one
resolves the name and *builds from it* — a record frame loads the class and invokes its
static `create`, a deftype frame invokes the first public constructor over the fields
that follow, and a `Serializable` frame opens an `ObjectInputStream` over the bytes that
follow. A store directory and a dump are whatever an operator copied, so all three are
reachable from a file the engine is handed, and only the third is allowlisted by the
library at all — behind a dynamic var an embedding application is invited to widen.

Empty is the right allowlist because it is what the formats already promise. A dump
frame is a field map and carries no class name by the format's own rule
([storage.md](storage.md)); a log frame is a positional vector for a size reason; and
every leaf a sentence may carry is a type nippy has an id for. So a name in a file is a
name this engine did not write, whatever it turns out to be.

A **version pin** holds the wrap to the nippy release it was written against. Only the
`Serializable` allowlist is a published hook; the other two readers are gated by wrapping
nippy's own vars, and nippy's call to `serializable-allowed?` is an implementation detail
of the same release. A bump that renamed any of the three would fail the namespace at
load, which is visible enough — but one that kept the names and stopped routing a class name
through them would install cleanly and cover less, which on a deserialization boundary is
the worst available outcome. So `thaw/pinned-nippy-version` states the release the wrap
was written against, the resolved dependency is read off its own Maven descriptor, and a
mismatch refuses to load. The cost is one line per upgrade; what it provides is that the three
attachment points are re-read by a person each time the dependency moves.

One alternative to avoid is to allowlist the classes a *value* may be — nippy's own
curated set, which admits `java.time.LocalDate` and the throwables. It reads as
generous and is the wrong shape twice over: it is an allowlist of what is safe to
*deserialize* rather than of what this engine *writes*, so it grows whenever the library's
does; and it blesses leaves whose only durable form is Java serialization, which makes
every later read of that store open an `ObjectInputStream` to answer a query. The front
entry point refuses such a leaf instead — `check-encodable` probes a class through this same
thaw — so what a store can contain and what its readers accept are one decision rather
than two that agree today.

### An EDN manifest is read under a bound, and a torn one is not a rewrite

`meta.edn`, `format.edn`, `report.edn`, `index.edn` and a machine's `catalog.edn` are
read through one bounded reader (`import/read-edn-manifest`, `manifest-bytes`), and past
the bound is a refusal naming the file. The bound is on the **read** rather than on the
file's stated length, because `File.length` answers 0 for a FIFO and a symlink to one is
a `slurp` that never ends.

The reason a manifest needs a bound at all, where a data stream does not, is *when* it is
read: it is the **first** thing read about a directory, before anything about that
directory has been established. Discovery probes every entry of the KB search path this
way, so a file that merely has the right name decides how much goes into the heap. A
data stream is read after its manifest has said what it is.

The store sentinel gets the other half of the same argument. A `format.edn` cut mid-write
is refused (`:unreadable-store`) rather than stamped with today's version — the absent
sentinel's treatment — because a directory whose stamp was being written is a directory
whose *records* were being written at the same moment, and adopting whatever is beside it
as today's layout is the one reading that is certainly wrong. An index's `layout.edn`
reads the same damage the opposite way, as `:stale`: it answers "can I prove these entries
are keyed the way this build keys them", a torn stamp proves nothing, and the answer to
an unprovable stamp is a rebuild from the records. An index is a cache and records are
not, and that difference is the whole of why one refuses and the other rebuilds.

### A bulk load installs by compare-and-set, not by overwrite

A bulk index load accumulates on a transient taken off the in-memory backend's state map
and installs it in one step at the end ([storage.md](storage.md), the bulk-write path).
The step could be a `reset!`, and one reading of the single-writer contract says it may
be: one thread mutates a KB, so nothing else can have touched the atom.

That reading is one step short. The atom is held per **space**, and every index store
over that space shares it — so what the single-writer contract rules out is a second
*thread*, not a second *batch*. A bulk load stacked inside another over the same space
installs its own map on the way out, and the enclosing batch, whose accumulator was
snapshotted before the inner one began, then writes straight over it. Nothing throws and
nothing logs; the inner load's entries are simply not in the index, and the first symptom
is a query that answers empty a long way downstream.

So the install compares against the value the batch snapshotted and refuses
(`:stacked-batch`) when it has moved. The alternative — merging the two maps — is worse
than the refusal, because the merge has no way to tell an entry the batch added from one
it inherited, so it would silently pick a winner per key on a KB that had already left
the contract. And the check costs one compare-and-set per batch, not per record, which is
why an argument that it can never fire is not a reason to leave it out.

The accumulator is closed as it installs, for the same reason one step out. It lives in a
dynamic binding, and a binding is conveyed — to a future, to a lazy seq realized after the
load — so a body that leaks one would otherwise reach a `persistent!`-ed transient and
throw from wherever it happened to be realized. Cleared, `txn-for` answers nil and the
write takes the atom, which is where a write outside the batch belongs.

## Indexing and retrieval

Defends [indexing.md](indexing.md).

### Handles get a key separate from tokens

The trie is ragged: arity varies and one sentex's path can be a proper prefix of
another's, so a node is leaf and interior at the same time. If a handle shared the
child-set token with the trie's other tokens, it would be indistinguishable from an
ordinary token — a handle is an integer, and so is a stored numeric argument like
`1970` — so `lookup [bornIn Tom]` over a stored `(bornIn Tom 1970)` would return
`1970` as a phantom handle, and `get-sentex 1970` names a real, unrelated sentex.
Neither rejecting a non-leaf terminus nor discriminating by type fixes this: the node
genuinely is a leaf, and a handle and a token are both integers with no marker to
tell them apart at read time. The fix is structural rather than a check: handles
live under their own key, `[:trie :handles prefix]`, and tokens under
`[:trie :children prefix]`, so `lookup` reading only the leaf key at its terminus
never returns a token as a handle, and `p/children` reading only the child set is
correct at such a node with no phantom branch reaching `plan/prefix-estimate`'s
fan-out.

### Child count is its own read

`p/count-children` answers a node's width off a cardinality directly — the set's
own count in the KV family, an edge-array span or a map's size in the columnar trie
— rather than by materializing the child set and counting it. The query planner's
cost model asks this once per literal per plan, so the cost of answering it is paid
on every plan the engine builds. Building the children to answer it would make
planning one fixed conjunction scale with the size of the KB rather than staying
flat: measured, over a 32x larger corpus, building the children to answer this reads
32x the facts and costs 30x the planning time, on a conjunction that never changed.
`lein perf`'s `plan-scaling` check holds the cost flat instead, which is what a
direct cardinality read buys.

### Rule defeasibility is not indexed

Nothing indexes `:defeasible`, and nothing should. Defaults fire from the same
agenda as strict rules — found by predicate like any other candidate, and fired at
the strength their own record reports — so nothing ever needs to enumerate the
defeasible ones as a group. An index that could enumerate them is an index that has
to be kept in step with a field the record already carries: every assert or retract
touching `:defeasible` would have to maintain a second copy of a fact the sentex
record already answers, for a query nothing in the engine actually asks.

### The exception index stays coarse

The exception re-check index answers "which rules might need re-checking", at two
coarse granularities. The trigger is coarse in what it is *addressed by*:
a fact on a predicate arriving or leaving re-checks every rule whose exception mentions
that predicate, a `genl` edge every rule whose exception is keyed at or above the edge's
supertype (`special/recheck-genl-edge`, over `tax/genls-global` of it), and a `genlCx` edge
every excepted rule with a firing placed in the ancestor set the edge widened
(`special/recheck-genlCx-edge`) — never which cached closure entry a particular exception
query actually read. Exception-bearing rules are few, so a coarse address is cheaper than a
fine-grained one — and it cannot be subtly wrong the way a closure-tracking scheme could,
since it re-checks everything the change could possibly affect rather than trusting a
derived subset. Where a channel's own narrowing is blind — a `recover`, an equality class
splitting — the answer is the blanket `special/recheck-every-exception`, which is the same
preference stated at its limit: queue conservatively, never skip. The unit indexed is coarse
too: the rule, never the individual firing. A rule handle is already an antecedent
of every justification it licenses, so each conclusion it produced is reachable
through the consequence links that exist anyway. Indexing individual derivations
would buy nothing beyond what those links already answer, and it would grow the
store with entries for the exceptions that do not apply — against a rule index
whose scale is tens of entries, never millions.

### A variable functor rule is refused, not silently accepted

Where a variable functor sits decides whether the rule can be run, so the entry point splits
on it. In an **antecedent** — `(?p ?x ?y)` as a trigger — it names no predicate, and the
rule index is keyed by predicate (canonicalization numbers the functor to `?var0` like any
other variable), so no arriving fact can ever spell the key. Such a rule is **refused** at
`assert` with `:not-indexable`. Accepting it would leave it silently inert: reported as
asserted, never reachable by an antecedent lookup, so it would fire only when a concrete
antecedent beside it arrives — joining over whatever happened to be stored at that instant,
two arrival orders giving two answers. Refusing it surfaces the mistake where it is made.

In the **consequent** — `(implies (holds ?p ?x ?y) (?p ?x ?y))` — it is **allowed**. Range
restriction guarantees the functor is bound by an antecedent, so the rule fires forward with
the predicate ground, through its concrete antecedent's own index entry; and its consequent
is filed under one catch-all bucket (`protocols/var-consequent-key`) that
`resolution/concluding-rule-handles` unions into every backward answer, since a rule
concluding `(?p …)` could conclude any predicate once `?p` binds. So the half the engine can
key is kept and the half it cannot is refused, rather than refusing both. The workaround for
the refused half is the instantiated rule, one per predicate, or a generator that stamps
them with the functor ground.

An **inert** rule (`set/inertRule`) is exempt from the antecedent refusal — it runs in
neither engine, so it promises nothing the index must answer for — and, concluding nothing,
its own variable consequent stays on the dead `?var0` key rather than the live catch-all,
so it never surfaces as a phantom concluder for every goal.


## Taxonomy and disjointness

Defends [taxonomy.md](taxonomy.md).

### An inert rule records transitivity, not a forward rule

A KB that computes transitivity in code rather than from a rule is a KB whose most
important rule is written nowhere. Asserting the transitivity rule bare would not be
documentation: it would be a forward rule materializing what the closure already
answers, one derived sentex per pair the closure already covers (see
[taxonomy.md](taxonomy.md) for the closure). The inert rule (`set/inertRule`) is the
spelling that writes a rule down without running it, so a claim can sit on the record with
no second engine computing it beside the closure.

Which leaves each account free to take the cheaper spelling. `CxCore.txt` ships no inert
rule: `genl`'s transitivity and the decontextualized-predicate lift are both carried by the
`comment` on their predicate. Prose describing a closure is a smaller thing to keep true
than a rule sentence nothing runs, and the argument above only says the account must be
somewhere a reader finds it, never that it must be a rule. The lift cannot be written as a
rule at all, because its consequent would be an `(ist CxUniverse …)`, which a rule is
refused ([contexts.md](contexts.md#ist-find-or-create-in-a-context)).

### Recording a disjoint clique beats asserting it

`(disjoint_metatype Metatype)` records that a metatype's members are pairwise disjoint
rather than asserting the pairs as `(disjoint …)` sentexes (see
[taxonomy.md](taxonomy.md)).

Asserting the clique instead would mean n(n-1)/2 stored premises for n members, and
premises rather than justifications is a teardown no retraction can reach. Recording
makes teardown exact: dropping the metatype releases every pair at once, and dropping
one `(M T)` releases exactly that member's pairs while the remaining members stay
separated.

### The answer is not found by testing every type

A goal with an open argument — `(disjoint a ?t)` — asks which types are separated
from `a`, not whether one candidate is. Testing every type in the KB would answer it,
but the cost is then a function of the vocabulary rather than of the goal: on an
imported ontology the vocabulary is six figures ([kbs.md](kbs.md)) where a term's own
declarations are three or four. The answer is read off `a`'s own declarations instead,
sized by what `a` actually declares rather than by everything the KB knows (see
[taxonomy.md](taxonomy.md) for `tax/separating-partners`).

## Contexts and placement

Defends [contexts.md](contexts.md).

### A goal every literal of which is computed names no context

A variable context is the **joint** reading: the answer must hold from some one reader's
`genlCx` ancestor set, and that reader is unified into the variable. Reading the union instead is
unsound for the reason [the QCN prover fans](#a-variable-context-goal-fans-over-readers-rather-than-reading-one-unioned-network)
rather than unioning — a conjunctive read would join a fact in `CxA` to a fact in `CxB`
when no context sees both, which is an answer no reader of the KB has.

One shape is exempt, and it is exempt because the joint reading has nothing to say about
it. A goal whose every literal is *computed* rather than matched — `different`, `evaluate`,
`unknown` and the rest of `sentex/deferred-predicates` — rests on no stored fact, so there
is no witness to pick and no reader that
could be the one that answers. Fanning it over the readers would be existential over them,
and a fanned `(unknown X)` is then satisfied by the most ignorant reader in the KB: the
one context that happens to know nothing about `X` answers for all of them, which turns a
negation-as-failure question into a search for somebody who has not heard the news. Such a
goal is read whole-KB. A *mixed* goal needs no exception and gets none: its matched
literals decide which readers can answer, and the computed ones are evaluated at those.

### Post-hoc placement is the default because it is bounded

`CxInference` and a variable context are answered either by fanning over the readers and
asking each the ordinary scoped question, or by asking once unscoped and placing each
answer by what it rested on. The two owe the same answers, so the choice is pure cost — and
the wrong move is to predict it: read the lattice, guess which will win, dispatch.

That does not work, and the measurement is what says so: which strategy wins is a fact
about the **data**, not about the lattice. A predictor fitted to lattice shape (reader
count, average ancestor set depth) called it right five times in fourteen. Post-hoc's edge is on
small joins, and it loses on large ones two different ways — a wide flat lattice discards
most of what the join builds, while a deep one discards nothing and still loses, because a
quadratic join costs less partitioned across readers than done whole. Only the first is
visible as waste, which is why the meter counts rows *built* rather than rows discarded:
size is the signal both failures share.

So post-hoc runs by default and is **measured out** rather than predicted out. It prunes a
partial solution whose ingredients already have no common descendant — a later literal only
adds contexts, so a dead row stays dead — and it abandons past a row budget sized off the
lattice, mid-stage rather than between literals, because the cost is in the rows. The fan
then answers whatever was abandoned. A strategy that wins 1.5× to 17× in
its regime and costs at most about 1.5× outside it, the extra being the bounded probe; on
a store where every join outgrows the budget it simply *is* the fan, reached after that
probe. The
budget is sized off the lattice rather than off the readers for the same reason the bail
exists: enumerating the readers costs O(the goal's match set), which would put that scan on
the one path that never needs it.

## Argument types

Defends [argtypes.md](argtypes.md).

### A value is typed by its kind, and the openness moves to the declared type

A type membership cannot be *asserted* of a value — there is no `(dog "Bob")` to store —
and the tempting conclusion is to exempt every non-symbol from the argument constraints,
since nothing could ever satisfy them. That reads a missing assertion as an unanswerable
question. It is answerable: a value's EDN kind is knowable from the value itself
(`checks/value-kind`), and those kinds sit in the `genl` lattice precisely so the
comparison can be made. A string is a `string`, a `string` is not a `dog`, and a
declaration that admits `(P "Bob")` constrains only the half of the position somebody
happened to spell with a name.

The openness does not disappear, it moves — to the **declared type**. A `t` the lattice
cannot place the kind against exempts, which is the imported-constraint case; a **symbol**
stays open-world, violating nothing until it holds a membership. That is what keeps the
check from turning an incomplete ontology into a wall of refusals: what is unknown is the
declaration's reach, not the value's kind.

A **compound** is the one leaf shape no *kind* answers for, and it is answered from the
other side. What `(QuantityFn 5 Meter)` denotes is its function's business, so no syntactic
answer would be the right one — `result` and `genlResult` are the declarations that say
it, and the checks read them from the asking context. A *reifiable* application never
reaches that arm: it is minted first, and its constant carries the same declarations
materialized as `(T K)`, which the symbol reading picks up. So one declaration gives one
verdict whichever kind of function wrote it, and the two paths differ only in where the
type is stored.

**Why a result declaration does not join the disjointness check.** `args-problem` and
`genls-problem` state a *demand* and convict on an absence, which is what a claim about a
function can answer. `disjoint-problems` is a different shape: it names an
`:opposing-handle` — the conflicting membership's own sentex — so `settle` can weigh the
two and defeat one. A structural application holds no membership sentex, so the only pair
available is *the fact and the function's declaration*, and letting one application's
assertion defeat that declaration would unbind every other application of the same
function. Naming no opposing handle instead would make it a hard entry point refusal, harsher
than the reifiable case it mirrors. So the demand-shaped checks read the result
declaration and the pair-shaped one does not.

### One vocabulary, not two

`string`, `number`, `integer`, `keyword`, `boolean`, `character` and `symbol` are the KB's
only names for the kinds a value can carry — one per leaf kind, and `arg` and
`quotedArg` both read the same seven, along with the four sign-refined integer types below
`integer` (`checks/value-kinds`). One alternative to avoid is a
parallel spelling per declaration, so that what an argument *denotes* and what is *written*
there never share a name.

It buys nothing and costs a trap. The use/mention distinction is already carried by which
predicate you write, so a second set of names restates it; and a declaration naming one of
them stores clean and convicts nothing, because `quotedArg` reads a type outside the
syntactic lattice open-world. A refusal would be a mistake a reader is told about. Silence
is one nothing reports.

**The sign refinements are the case that shows why the shared reader has to be shared all
the way down.** They were added denotation-only, on the reasoning that a sign is a fact
about a value and `quotedArg` asks about syntax. But they live *below* `integer` in the
lattice, so they are inside `quotedArg`'s domain and the open-world escape above does not
reach them: the mention check compared a value's bare kind upward against the declared
type and convicted every integer written in such a position. Half a vocabulary is worse
than two, because the half that is missing does not go quiet — it answers wrongly. A
value denotes itself, which is the whole reason the kinds are in the `genl` lattice, and
it is why both readings now go through one reader.

## Inference and chaining

Defends [inference.md](inference.md).

### There is no separate defaults phase

Defaults look like they need their own rounds: derive the strict consequences, then
the defeasible ones, then re-run the strict chainer over what that produced. A phase
built that way cannot use the agenda, because the datums it must revisit are the ones
already believed — it degenerates into re-solving *every* default rule as a full
unindexed join over all facts, per round. A single defeasible rule then makes every
assert a full KB scan, and loading N facts costs O(N²).

Do not add the phase. One agenda is semantically neutral against two phases, and the
reason is narrow enough to state exactly: a default conclusion is placed
unconditionally, and whether it survives is decided later by `settle` from
recomputed belief. Phase ordering therefore cannot affect *what* is derived, only how
expensively it is found — either scheme computes the least fixpoint of the same
monotone immediate-consequence operator. The one thing separate phases are reaching
for is that a strict consequence of a default conclusion still gets derived, and a
unified agenda gets that for free: the default conclusion lands on the agenda and
triggers strict rules like any other new datum.

### Why a sort and not a search

Costing a plan by searching over candidate whole orders — summing intermediate rows
per candidate order, minimized over subsets, using `est-matches` as the per-literal
cost — is refuted, and measurably: on randomized joins such a search ran a mean of roughly
2.3× the best permutation's actual rows, against cheapest-first's roughly 1.2×, losing 3
trials of 9 and winning none.

The reason is not that a search is the wrong shape but that it minimizes the wrong
quantity. `est-matches` is a *bound*, one-sided by contract, and a plan's cost is a sum of
expected intermediate sizes — maxima of products do not factor, so summing bounds across a
join adds numbers that answer a different question than the one being minimized.
`est-rows` fixes that by giving every literal an expected value that composes across a
join, and once the numbers compose the ordering does not need a search at all — the
transposition law (descending `s/(n-1)`) sorts blocks in O(k log k), no search.

### The loop guard's scope is the subtree, not the frame

A frame is not a path. `prove-from` expands a goal by pushing a single stack frame
that holds both the rule's antecedents and the conjuncts still queued behind the
goal, and those queued conjuncts are **siblings** of the expansion, not descendants
of it. Growing the guard to cover the whole frame would charge a later conjunct for a
goal key an earlier one claimed, and a conjunctive query would answer less than its
own conjuncts do: `[(anc Tom ?y) (anc Tom ?z)]` would come back empty where
`(anc Tom ?y)` alone answers twice, `provable?` would say false, and `prove-within`
would report `:status :complete` on a wrong answer.

This is also why the planner cannot be allowed to change an answer. Reordering
conjuncts moves which one claims a key first, so a guard scoped to the frame would
make `plan/*enabled*` semantic rather than a cost decision, and adding facts could
make a query stop answering. Scoping the guard to the subtree instead keeps it a
statement about descent — a claim about a path, not about a frame — so the order
conjuncts are tried in is free to change without changing what the query proves.

### The leaf must never itself backchain

`prove-from` and the node engine both take a `:leaf-solver` — how a literal the
search will not rewrite gets answered — and the division between rewriting and the
leaf is required: a leaf that itself backchained would run the engine's rewriting
*plus* a nested search per binding under it, compounding the two costs instead of
paying one.

Measured on a converging rule graph — the structure that asks one subgoal from many branches
— a leaf that started its own backward search ran **24-73x slower** than the divided
arrangement on the same queries. Both shipped leaf solvers expand no rule: `nil` is
`matches-visible`, the stored facts, and `core/query` passes `provers/solve-goal`, whose
registry backchains nowhere. That is what keeps either one level with `ask`, and a leaf
that searches is the one leaf shape the design excludes.

### A defeated datum's other derivations are not a second chance

A rule expansion that reaches a defeated conclusion is dropped even when it reaches it
from **other believed premises** than the ones the defeat was decided over. The tempting
alternative is to let the second derivation stand: the defeat was about the first one, and
here is a route to the same sentence that does not use it.

It is not, and reading it that way confuses two things belief keeps apart. A defeat is a
claim about the **datum**, not about a derivation of it: `decide-nogood` resolves a clash
by forcing the strictly-weaker *side* OUT, and the side is a stored sentex with every
justification it has. Its other derivations are not evidence against the defeat — they are
already in the JTMS, already counted in the `:groundable` set the relabel recomputes
beside belief, and already the reason it is retained for revival rather than swept
([nmtms.md](nmtms.md)). A chainer that answered on one of them would be re-litigating a
settled clash from inside a read, and answering it
differently from `ask`, `sentexes-matching` and `why` about the same KB.

The revival path is what makes that added no work. Retract the defeater and the datum is IN
again on those very derivations, with no cache to invalidate and nothing to re-derive — so
what the filter withholds is exactly what belief currently withholds, and for exactly as
long.

### A generator cycle is refused, not depth-capped

A rule that concludes a rule stamps out new rules as it fires, so two generators that feed
each other mint without end. The tempting bound is a depth cap: let the cycle run *n*
rounds and stop. That makes the KB's contents a function of how long the chainer ran — the
same knowledge loaded twice holds different rules, and reloading it from nothing does not
reproduce it, which is [order independence](nmtms.md) spent on a shape nobody asked for. A
cycle is refused where it is written instead, beside the five other shapes a generator
cannot have. A refusal is a fact about the rule, and it reads the same on every load.

## Exceptions

Defends [exceptions.md](exceptions.md).

### The exception belongs on the rule it excepts

A defeasible generality and its exception can be written as two unrelated rules
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
genl hierarchy ([why no such ordering is derived](#there-is-no-second-axis)).

The deeper cost is that no argument survives. `why (flies Opus)` and
`why (not (flies Opus))` are two disjoint trees, and nothing records which won or
why — so an application cannot argue for or against a proposition, which is the whole
point of keeping justifications.

The exception belongs on the rule it excepts instead, naming the rule directly rather
than leaving the connection to be rediscovered:

```clojure
(exceptWhen (flightless_bird ?b)
  (set/defaultRule (implies (bird ?b) (hasAbility ?b flying))))
```

### The exception is not materialized per instance

An exception naming a rule could instead be materialized per instance: for each
ground binding under which it would hold, store the ground exception as an unbelieved
node and list its handle in the justification's `out` set. That implementation is
wrong twice over.

It would store the negative space. `(exceptWhen (flightless_bird ?b) ...)` over ten
thousand birds would materialize a probe for every bird that *is not* flightless,
which is nearly all of them — the store would grow with the exceptions that do not
apply, rather than with the exceptions that hold.

An arbitrary query has no handle to materialize either. `out` is a set of handles and
can only say "these specific propositions are not believed"; an exception answered
through transitivity or arithmetic has no single node whose OUT-ness stands for it.
The `out` slot is the wrong shape for this, independently of the materialization cost
above.

So a rule's exception is stored once, as a meta-sentex naming the rule, and
re-evaluated per firing rather than expanded into ground instances.

### A cycle through negation is rejected, not resolved

A rule set in which one rule's exception depends on what another rule concludes, and
that second rule's exception depends back on the first, is a cycle through negation —
the kind of program that admits zero or several stable models. Which model a reader
gets would depend on arrival order: settle the first rule before the second and one
model results, settle the other way and a different one might. That breaks the
order-independence invariant [nmtms.md](nmtms.md) holds non-negotiable — the same
knowledge asserted in any order must yield the same beliefs.

So a rule set with a cycle through negation is rejected at assert time, as a
well-formedness check over the rule dependency graph, rather than evaluated under
some fixed pick of stable model. An exception is not the only edge that closes one, so
the graph is not walked from the excepted rules: `checks/negative-edge-rules` starts at
every rule a negative edge leaves — an `exceptWhen`, an `(unknown S)`, an aggregate, a
closed-extent negative, or a `different` — because a roster short of one of those is a
roster some cycle passes through no member of, and a cycle nothing walks is a cycle that
stores. Refusing the assert is what keeps every stored rule set stratified, which is what
lets the exception evaluator stay within one settle pass instead of hosting its own
model-selection machinery.


### A conjunction under a quantifier is joined, never read flat

`(unknown (and A B))` is a guard over two conditions, and under a quantifier the flat
reading is the wrong one: each conjunct would be free to find its own witness, so "has a
sick child" would hold of anyone with a child as long as anybody at all is sick. That
reading is never taken. Reading it the way its author means requires binding one witness
across both conjuncts, and the boundary the argument fixes is where that binding comes
from.

A NAF query **carries** it. Its conjuncts are threaded left to right in a planned order
(`provers/conjunction-solutions`), each substituted with what the ones before it bound —
a join, and a small one: the registry still answers one goal at a time, and the quantifier
gives the shared variable a scope the guard does not have to invent. A ground conjunction
is the degenerate case of exactly that thread, so the flat reading is not a second
mechanism sitting beside this one; it is this one with nothing to carry.

An **aggregate** carries it too, through the same evaluator: `provers/aggregate-values`
runs the census body as a joined conjunction, so `(agg/count ?n ?c (and (childOf Bob ?c)
(asleep ?c)))` counts the children who are asleep. Reducing over `?v` rather than testing
for a witness changes what is done with the solutions, not how they are found — the join
produces one witness per solution either way, and the reduction reads `?v` off it.

The line is not the structure of the conjunction but whether the operator reading it threads
bindings, and both of them do. Still refused is what no join can repair: a
**disjunctive** body, since a count over a union is not the sum of two counts and a
witness satisfying both alternatives would be counted twice; and a census variable no
conjunct of the body binds and no earlier antecedent names (`:naf-not-closed`), which is
a census of nothing whatever the KB holds. Both are refused at assert time and in the
same words as the `unknown` half ([naf.md](naf.md), [aggregate.md](aggregate.md)).

## Anytime inference

Defends [anytime.md](anytime.md).

### Qualitative cost tiers over time estimates

`ask-within`'s `:max-cost` ceiling is a qualitative tier (`:lookup` < `:compute` <
`:search`), not a per-prover time estimate. Wall-clock is a real measurement; a
per-prover millisecond estimate is not — no implementation has a way to compute one, so
it would be a constant standing in for a number nobody measured, and a real budget
cannot be gated against a number nobody measured. The qualitative tier asks a question
every prover can honestly answer instead: is the result looked up, computed, or searched
for? Admission stays coarse for the same reason there is no finer gate: reading a
prover's `est-bindings` against the remaining budget would gate on the same kind of
unmeasured estimate.

The `:search` tier stays in the taxonomy even though the shipped registry occupies none
of it. The tier is a claim about what a prover **may** cost, not a census of the ones
that ship — an application prover added through `add-prover` can claim it. Rule
expansion is not the registry's at all, so it is priced by the engine that does it, as
`query`'s and `prove-within`'s `:max-depth` — a bound on depth rather than a claim about
cost.

### Refusing an unrecognized cost ceiling

`ask-within` refuses a `:max-cost` value outside `:lookup`/`:compute`/`:search` (`:type
:unknown-option`) rather than reading it as no ceiling. A caller writing `:cheap` for
`:lookup` is asking to exclude the expensive tier, so running every tier anyway is the
one reading of that typo that is certainly wrong. Treating the bad value as unbounded
would also hide the mistake: a ceiling that admits everything returns exactly the
answers a correct one would, only slower, having done the work the bound existed to
avoid. Refusing the value surfaces the typo instead of silently discarding the budget's
intent.

### A deadline on `ask` / `prove` refuses; a depth does not

`ask`, `ask?`, `prove` and `provable?` take a bound of their own, and a `:max-ms` those
entry points *reach* is `:budget-exhausted` rather than the answer they had in hand. That reads
as harsh next to `ask-within` / `prove-within`, which hand the same prefix back happily —
and the difference between the two entry points is the whole argument.

An anytime entry point's return shape **says what it is**: `:status` is `:timeout`, `:count` is
what this step found, `:resume` continues. A caller that asked for a partial gets one and
is told. `prove` returns a vector of solutions and `provable?` returns a boolean, and
neither shape has room for that: a truncated vector is indistinguishable from the whole
answer of a KB that knows less, and `false` from a search that stopped looking is
indistinguishable from a KB that does not say so. Silently returning either is the same
failure `assert`'s option rosters exist to refuse — an answer taken at a setting nobody
chose, arriving in the structure of one somebody did — and it is worse here, because the
setting *is* the ceiling the daemon filled in on a request that named no clock at all.

`:max-depth` is on the same entry points and does not refuse, which is not an inconsistency but
the other half of the same rule. A depth **prunes**: the space under it is genuinely
exhausted, so the run reports `:complete` and the answer is the whole of what that depth
admits. `(provable? kb g ctx {:max-depth 2})` answering `false` is a true statement — no
derivation within two rewrites — and a caller who wanted a deeper one names a deeper one.
A clock cannot be re-read that way: "no answer within 250 ms" is a fact about the machine,
not about the knowledge, and it is not a question anybody meant to ask.

The rejected alternative is a marker in the result — a truncation flag beside the
solutions, or a metadata key. It fails on being ignorable: every existing caller reads the
vector and the boolean, so the flag would be correct, present, and unread, and the wrong
answers would flow on exactly as before. A refusal is the only signal a caller cannot
accidentally skip, and `ask-within` / `prove-within` are one call away for the caller who
wants the prefix.

## Qualitative constraint networks

Defends [qcn.md](qcn.md).

### Path consistency computes the greatest fixpoint, not the least

A fixpoint of the tightening operator is a network `X` with `tighten(X) = X`, and
tightening is monotone over a finite lattice, so more than one exists — a smallest and a
largest, each reachable only by iterating from its own end. Path consistency iterates
from the top, the network as given, and only ever removes; that lands it on the greatest
fixpoint, the one that says nothing is ruled out beyond what the constraints rule out.

The least fixpoint of the same operator is a genuine fixpoint and a useless one: every
constraint set to `#{}`. Intersecting the empty set with anything stays empty, so it is
perfectly stable, and it claims that no two regions can stand in any relation at all —
every KB's theory is contradictory, always. Nothing in the tightening equations rejects
that fixpoint; only starting from the top does.

The dual case sits a couple of namespaces away in this codebase, and the contrast is
exact. `jtms/region-classes` solves the defeat-class equation by starting every in-region
node at `:default` and iterating upward to stability — a least fixpoint, for the mirrored
reason: starting *that* computation from the top would let a node claim a strength
nothing conferred, the same way starting path consistency from the bottom would let the
network deny a relation nothing refuted. A least fixpoint means nothing is in unless
something put it in; a greatest fixpoint means nothing is out unless something took it
out. Reachability and derivation want the first kind; possibility and consistency want
the second — and path consistency is answering a possibility question, so it has to
start at the top.

Both ends are unique, which is what makes both order-independent regardless of which one
a given computation needs; uniqueness is available at either end, but only at an end, so
picking the wrong one does not fail loudly — it silently computes a different,
well-defined, wrong answer.

### An impossible network is reported off the pass, not thrown as a wff check

`wff` throws, and which fact it would throw on is whichever arrived last — the clash a
qualitative calculus finds is a property of a *set* of facts, not of any one of them, so
blaming a single member makes the stored KB's error depend on the order the facts were
asserted in. Throwing would also cost a fixpoint per assert, run whether or not anybody
asked for it, and the provers are opt-in, so a KB that never registered one would be held
to a calculus it never asked for. Recording the inconsistency where the pass already
proved it, in the violations ledger, adds no work beyond a pass the KB already ran and
holds the property every other check in the engine holds: the answer does not depend on
the order the facts arrived in.

### A variable context goal fans over readers rather than reading one unioned network

A goal whose context is a variable means "in some context", the same reading every other
prover gives it, and the tempting implementation is to read every context's facts into a
single network and ask that. It is unsound: `(ntpp A B)` asserted in one context and
`(ntpp B D)` asserted in an incomparable one compose for nobody, since no context
inherits both, yet a single wildcard network holds them together and reports `A ⊏ D` — a
relation no reader of the KB actually sees. The prover instead fans over the readers (the
fact-holding contexts closed under where they meet) and unions their answers, so every
binding it yields is entailed for a reader that genuinely exists.

Reading only where facts are stated, rather than wherever is convenient, is a soundness
rule rather than a cost decision, and the two read the same on a KB that never retracts
anything — which is what makes the difference easy to miss. A join that read facts from
wherever was cheapest would wait for some unrelated fact to be asserted into the meeting
context — any fact, entailing nothing about the pair in question — and would then survive
that unrelated fact's retraction, because by then the firing has a justification of its
own that no longer depends on anything about the meeting. Reloading the identical content
from nothing would then not reproduce the KB, which breaks order independence
([nmtms.md](nmtms.md)): the belief a KB ends up holding would depend on which unrelated fact
happened to pass through the meeting context first, not on what was asserted.


## Operations and the daemon

Defends [operations.md](operations.md).

### A read that crosses the wire is realized inside the write monitor

Projecting a query's answer for the wire, or walking a KB's records for an export, is
what realizes what would otherwise be a lazy result. Doing that after releasing the
daemon's write lock is the tempting shortcut, since the lock is nominally for writes and
a query stores nothing — but a lazily realized result reads the KB at whatever moment it
is finally walked, not at the moment the op was dispatched. Run outside the lock, a
`:query` could straddle a concurrent `:assert` and report a KB that never existed at any
single instant: part of the answer reflecting the state before the write, part reflecting
the state after. An export has the same exposure for the same reason — it fetches record
by record rather than atomically, so a dump taken while something is asserting into the
KB is a dump of no single state, just a different KB shape than any that was ever
believed.

So both run *inside* the write monitor the daemon serializes every op through, trading a
query's chance to overlap a write for the guarantee that whatever it returns is a
snapshot of one real moment.

### Unknown subscription and bad cursor refuse rather than answer an empty feed

`:unknown-subscription` and `:bad-cursor` could each be answered with `{:events []}`
instead of a refusal — a dropped, timed-out, or foreign token, and a cursor that is
malformed or already ahead of what the subscription has delivered, all look like "nothing
new happened yet" from the wire. That is the tempting shortcut, and it is wrong for
exactly the reason a refusal exists at all: a feed that has stopped and answers
`{:events []}` is a feed its reader believes is still running, and a reader that believes
a dead subscription is live never resubscribes, never notices it has stopped receiving
events, and silently falls behind forever. Refusing by name — with a `:type` the client
can act on, by dropping the subscription or re-subscribing with a fresh cursor — costs
nothing an empty answer would have saved and tells the caller the one thing an empty
answer cannot: that there is nothing to wait for.

### The default collector is chosen against this engine's measured footprint

No collector flag is set for either the daemon or the container image, and that omission
is measured rather than skipped. `lein perf`, two alternating passes at a fixed 6 GiB
heap, 2026-08-06, put the JDK default at about 41 s and roughly 1.5 GB peak resident
against generational ZGC's 56 s and roughly 6 GB — about a third slower while holding
four times the resident set, and ZGC alone tripped the `:negation-arbitration` growth
bound on both passes.

A concurrent collector earns its throughput cost on a live set of tens of gigabytes,
where pause time dominates and a bigger resident set is the price willingly paid for it.
This engine's peak measured heap is about 1.5 GB, nowhere near that regime, so the trade a
concurrent collector offers is not one this workload benefits from — it pays the
resident-set cost with nothing to buy back in return. The JDK default collector is not a
placeholder waiting for someone to pick a better one; it is the measured right answer for
this footprint, and picking ZGC is left to `lein with-profile +zgc`, for a JVM that runs a
different workload with a reason to want it.

### A search bound may be lowered by a request and not raised

`:max-depth` and `:max-ms` are the two dials a caller sets on a served read, and each is
held under a ceiling (`config/max-query-depth`, `config/max-query-ms`) that a request may
name a smaller value than and is refused (`:over-ceiling`) for naming a larger one. An
anytime read that names no clock at all is given the ceiling's, since absent there means
*no clock*, and the daemon has an answer to "how long may this run" for every other read.

The exposure is not the caller's own latency; it is that every op runs under the daemon's
single write monitor, so a read a caller sized holds every other caller's request behind
it. That is what makes a bound the daemon's business at all: on a KB with rules, a depth
a caller chose is an exponential a caller chose to spend on somebody else's behalf.

The ceiling is **30 seconds** because that is when the caller stops listening — the
zero-dep client's own read timeout ([operations.md](operations.md)) — so a read still
running past it is holding the writer for an answer nobody is waiting for. The depth
ceiling is **256** because it is the largest depth the API's own defaults name (`why`'s),
so every documented call sits inside it.

Two shapes were rejected. **Silently clamping** — answering under a lowered bound — hands
back a partial result labelled as the one that was asked for, which is the anytime
contract's `:status` lying; a refusal carrying the ceiling tells the caller what the next
request has to name. And **applying the ceiling at the HTTP route** would be a ceiling the
model's generated tool surface does not have, since that surface dispatches through the
same op table ([llm.md](llm.md)) — so the clamp lives in the table, where both entry points
reach it.

An op with no option map is deliberately not on the table. `:prove` and `:ask` take no
bound, so a caller has nothing to raise; what bounds them is the KB's own rule set.

### What a server binds decides what it requires

Naming a non-loopback address is refused (`:unauthorized`, exit 2) unless
`VAELII_API_TOKEN` is set, and the rule is the same fn for the daemon and the browser
(`guard/require-token!`). A loopback bind is unchanged: the token is used when set, and
its absence is a startup warning.

The argument is that the exposed configuration must not also be the one with the fewest
checks. The flag that publishes a server's write routes is the *same* flag that drops the
`Host` allowlist — the name you reach a public bind by is yours to know, so the allowlist
cannot be guessed at — which leaves an address-bound server with strictly less standing
between an anonymous caller and `POST /op` or `/edit` than a loopback one has. The
routes on the other side are not incidental: the daemon's is the KB's only writer, and
two of the browser's (`/kbs/export`, `/kbs/load`) write the host filesystem at a path the
request names.

A **warning** was the previous shape and is the tempting one, because a refusal at
startup is a server that does not come up. It fails for the reason every fail-open
default fails: the operator who most needs the line is the one who will not read it, and
a warning that has never once stopped a deployment is indistinguishable from a comment.
The loopback default is deliberately not held to the same rule — `lein serve` and `lein
browser` on a laptop are real workflows, and a credential required there teaches an
operator to export a constant, which is worse than no credential because it looks like
one.

The browser presents the token only on a public bind. Wrapping the loopback default in it
as well would take a variable a daemon on the same machine already needs and make it a
password on the operator's own browser, for a bind that answers only that machine.

## The web browser

Defends [web.md](web.md).

### Loopback only for the browser plus nREPL pairing

`lein browser` pairs two things that are each a considered risk alone and a remote shell
together: the browser's write route, unauthenticated, and an nREPL, arbitrary code
execution by design. Either one on a shared network interface is a risk that stays local to what
it grants; combined, a request that reaches the browser can drive the REPL, and a REPL
is a way past every check the browser's own write routes enforce. So the pairing is not
configurable — the profile pins nREPL to `127.0.0.1` rather than trusting Leiningen's
own default, and the browser binds loopback with no flag to widen it. Exposing the
browser to another interface stays `--listen` on `-main`, which starts no REPL at all,
so the one config that is reachable off-machine never carries the arbitrary-code-execution
half of the pair.

### The term graph renders live, not behind a reveal button

A term page's concept graph draws itself on every render — server-drawn, no click, no
route, no state recording whether it is shown — rather than sitting behind a reveal
button a reader clicks to see it. A reveal button looks like the safer default: nothing
is spent until a reader asks. It is not, because it buys a saved read from the readers
who never click it and charges a whole extra round trip to the readers who do — the read
it defers is one the page already paid for in its own index groups and closures, so
deferring it saves nothing there and only adds a request most readers would end up
making anyway. A route to reveal it would also mean a `show=0` parameter, a
collapsed-versus-expanded fragment, and a second entry point rendering the same picture
with different chrome — three things to keep in sync for a feature that is otherwise one
function called from one place.
