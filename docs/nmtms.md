# Non-monotonic truth maintenance

- **Covers:** how belief is computed from justification strength, how `settle`
  resolves soft contradictions without throwing, which features a settle is built from,
  and what each step of a settle costs.
- **Not here:** the belief a batch would move before it commits →
  [preview.md](preview.md); the ASP backend a contested edge renders to →
  [asp.md](asp.md). Nor what an *agent* believes — `(believes Alice P)` is a projection
  into Alice's context and no part of this layer → [belief.md](belief.md). Nor what
  belief *is*, as a function of the stored content → [reference.md](reference.md).
- **Assumes:** sentex, context, justification, strength → [glossary.md](glossary.md).

`vaelii.impl.strength`, `vaelii.impl.solve`, `vaelii.impl.jtms`, and the settle layer in
`vaelii.impl.settle`.

A plain JTMS is a *monotone* least fixpoint: adding a belief can only turn nodes IN.
Defeasible common sense needs the opposite too — a new fact can *withdraw* an earlier
conclusion. This is the non-monotonic layer. Its design is
shaped by one observation:

> Most of a common-sense KB is default-true with no conflict. Only the **edges** —
> where defaults collide — need real arbitration. So resolve the easy majority in
> the engine, and hand only the contested edges to an external solver. Known-true
> content is never sent to a solver.

## Strengths and the defeat-class (`vaelii.impl.strength`)

Every assertion carries an assumption **strength**:

| Strength | Meaning | Defeasible? | Sent to solver? |
|----------|---------|-------------|-----------------|
| `:monotonic` | known-true | never | never |
| `:default` | defeasible (the common case) | yes | yes, at a tie |

Assert monotonic content with `(assert kb S ctx {:strength :monotonic})`; the
default is `:default`, because most of the KB is.

There are exactly **two** classes, and derivation adds none. They form a total order
**monotonic > default**. A node's **defeat-class** is the strongest support it
currently has: its premise strength, or the class any valid justification *confers*
on it. `relabel` computes it alongside the label; `core/defeat-class` (via
`jtms/defeat-class`) reads a believed handle's class back. Two classes and no third:
[why](defenses.md#two-strength-classes-not-three).

**A re-assert takes the stronger of the two classes, and never the weaker.** The mark is
resolved from *content*, like a re-asserted rule's slots
([canonicalization.md](canonicalization.md)). `strength/max` is commutative and
idempotent, so every order agrees and a third assertion changes nothing. Narrowing a class
is `retract!` and re-assert — the retraction takes the mark with it, so nothing is
inherited across one. Why a bare re-assert's silence is not a downgrade:
[why](defenses.md#a-bare-re-assert-never-downgrades-the-class).

**A premise's strength is written in two places, and the record is the authoritative
one.** `assert-entry/put-premise-mark` writes both halves together — `jtms/add-premise` into the
network and `p/mark-premise` into the record store, where every backend keeps it as the
sentex's own `:strength` field; the disk store also caches the strength's rank in the record's
slot flags, and the field stays the durable copy. The record is what `recover` replays
(`rebuild-tms` reads `p/premise-strength`, never the network), so it is the copy that
survives a restart and the copy an import writes. The network's copy exists because the
class fixpoint reads it once per in-region node per worklist pop, under the dense
representation's write lock: on the disk store that read is a lock and a slot
decode, and on a server store a round trip, so the resident copy is what keeps
[locality](#2-locality) a claim about every representation. It is also the only copy
`preview` can move — a suspended premise is suspended in the network alone, which is
what makes that retraction reversible without writing a frame.

### The forced-monotonic set

**A forced-monotonic literal goes OUT only by retraction.** The nogood families
([The nogood families](#the-nogood-families)) need this of the literals
they read as grounds, and the forced-monotonic set closes each of the three ways a literal leaves belief:

| way out | what closes it |
|---|---|
| losing a nogood | `decide/verdict` never makes a forced-monotonic member the loser: the weakest member is chosen among the members that are not forced-monotonic, and a nogood with no defeasible member outside the set is `:hard` |
| a denial | a stored denial `(not S)` of a forced-monotonic literal `S` is the loser of their negation nogood at either strength (`decide/verdict`), so `S` stays believed; where no `S` is believed, the denial is believed like any other premise |
| its support | a firing concluding a forced-monotonic literal from a rule whose antecedents are not all forced-monotonic supports nothing (the `:void` forced set below, and the read walk at a reader that misses a declaration) |

An `except` does not take a forced-monotonic literal OUT. An `except` in force hides its target from
the context it is stated in and from every context below that one, a forced-monotonic literal
included, and the literal stays believed at every context that does not see the `except`
([contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree)). A firing
or a placed nogood resting on the hidden literal is blocked and swept below the `except`,
as for any other target, and retracting the `except` restores both
(`except_monotonic_test`).

A forced-monotonic literal keeps the strength it was written at, and what is derived from it is capped
by that strength as by any other antecedent's ([Strength propagates from the
antecedents](#strength-propagates-from-the-antecedents)): a fact preserved through a
`:default` predicate `genl` and a firing of `core.txt`'s `injection` rules from a `:default`
declaration are `:default`. A `genlCx` premise is the one exception: it confers `:monotonic`
whatever strength it was written at (the `:mono` forced set below), so a `genlCx` edge caps
no firing's class ([reference.md](reference.md#decisions) 1 and 9).

**Membership.** A predicate is forced-monotonic if and only if a nogood family reads its
literals as grounds, or taking one of its literals OUT adds belief elsewhere. Each family names the literals it reads as grounds under `:grounds` in
`decide/registry`, and `decide/held-members` names the members no family reads, each with
its reason. `decide/baseline-forced` is the union of the two, held on every KB whether or
not it loads the upper layer:

| member | forced-monotonic because |
|---|---|
| `arity`, the nine exact-arity classes, `variable_arity` and its two specializations, `arityMin` | grounds of the arity family |
| `irreflexive`, `anti_symmetric` | grounds of the self and converse family |
| `functional`, `functionalInArg`, `anti_transitive`, `asymmetric`, `negates` | grounds of the tuple-mark family |
| `genl` between two arguments spelled as predicates of arity 2 or more ([naming.md](naming.md)) | grounds of the arity, self and converse, and tuple-mark families, which read the stored predicate edges |
| `disjoint`, `covering`, `partition`, `sibling_disjoint`, `siblingDisjointException` | grounds of the membership family |
| `orthogonal` | the one member of the related-types family's clash of it, which is a conflict and never a defeat |
| `genlCx` | every context's ancestor set reads the stored edges |
| `except` | taking one OUT un-hides its target, so what a reader hides would shrink ([reference.md](reference.md#decisions) 2 and 14) |
| `exceptWhen` | taking one OUT unblocks the firings of the rule it names, so what a reader holds blocked would shrink ([exceptions.md](exceptions.md)) |
| `rewriteOf`, `sameAs`, `equals` | taking one OUT un-merges two terms, so what a reader hides would shrink |
| `injection`, `surjection`, `bijection` | premises of `core.txt`'s rules concluding `functional`, `functionalInArg`, `injection` and `surjection` (decision 17) |
| `functionCorrespondingPredicate`, `result` | premises of `core.txt`'s rules concluding `(arg P n T)` from a function's `result`, since `arg` is forced-monotonic |
| `fixed_arity`, `fixed_arity_predicate`, `fixed_arity_function`, `bounded_arity`, `unbounded_arity`, `at_least_binary`, `at_least_ternary`, `at_least_quaternary`, `at_least_quinary`, `arityMax`, `admitsArgnum` | the arity policies, read beside the arity bindings, so a policy goes OUT only by retraction as a length does |
| `relation`, `predicate`, `function`, `truth_valued_relation`, `logical_constant`, `logical_connective`, `quantifier`, `symbol`, `context`, `unrepresented_term` and its value kinds (`boolean`, `character`, `keyword`, `number`, `integer` and its four sign classes, `string`) | the term kinds: a clash between two of them is a conflict and never a defeat, so a `:default` `(predicate X)` beside a `:default` `(string X)` is reported in `conflicts` with both believed |
| `greaterThan`, `lessThan` | the numeric comparators: each holds of numbers only, and `core.txt`'s rules concluding `at_least_binary` through `at_least_quinary` read `greaterThan` beside `arity` and `arityMin` |
| `quantityGreaterThan`, `quantityGreaterThanOrEqual`, `quantityLessThan`, `quantityLessThanOrEqual`, `sameQuantity` | the quantity comparators, computed from the unit table as the numeric comparators are from the numbers |
| `arg`, `arg1`, `arg2`, `arg3`, `arg4`, `arg5` | the argument declarations: read beside the arity bindings, and `core.txt`'s twin rules conclude each projection from `arg` and `arg` from each, so the six are forced-monotonic together |
| `genlInverse` between two arguments spelled as predicates of arity 2 or more, by `forced_monotonic_between_predicates` | `genl` with its arguments swapped, forced as `genl` between predicates is |

CxTra declares its value kinds below `string` (`ip_address`, `ipv4_address`,
`ipv6_address`) by `forced_monotonic_predicate`, so they are forced-monotonic at the readers
that see CxTra and not on the baseline.

A `genl` between types stays defeasible, so a type edge admits exceptions: a placed
`defeat` of one hides every placed nogood resting on it as a ground, at the defeat's
vantage and below.
`transitiveInArg` is not forced-monotonic: the inherited family weighs a declaration as a member,
read through belief (`inherit/positions`), and a declaration loses like any other member.
A family's own grounds appear among the members of three nogood kinds only, and no
member of one is ever its loser: `:arity-descension`, whose members are all bindings, its
`contradicts` stored in CxUniverse with no `defeat`, and `:negates-arity` and
`:negates-unary`, whose one member is a `negates` declaration, placed in its context and
justified by the bindings stating the two lengths
([The nogood families](#the-nogood-families)).

**A forced-monotonic ground keeps the placed reading unique.** A ground that could lose would
let one placed `defeat` lose force through another, and two such nogoods, each one's loser a
ground of the other, would give two readings. The forced-monotonic set rules that shape out
([Why a read runs no rounds](#why-a-read-runs-no-rounds)).

`decide/forced-monotonic?` is the one reader of membership. Every reader reads the
**baseline forced-monotonic set** (`decide/global?`). A declaration stated in any
context, CxUniverse's included, makes its predicate forced-monotonic at the readers that see it
and believe it, and at no other (design ruling 28). A reader does not believe a
declaration that an `except` in force there hides, or that a stored `defeat` names whose
nogood the reader decides against the declaration over the baseline set alone
(`exc/forced-state`, through `exc/in-force?`). A placed `(contradicts …)` the reader
decides against a declaration does not hide it there. A declaration of a type a `:monotonic` denial of the
declaration defeats forces nothing at the contexts below the denial, except at a context
whose `except` hides the defeat. `forced-monotonic?`'s 4-arity reads one reader's
forced-monotonic set, its 3-arity the union over every reader, and `decide/forced-literal?` reads a
literal through either (`checks/forced-monotonic?` with a KB). `has-prop?` with a context
answers the two forced-monotonic kinds as that context reads them, and `props` answers the union. The source digest covers the
baseline, so a reasoning image computed under another baseline is declined and the store
recovers under the new one. The decisions that make each group forced-monotonic are
[reference.md](reference.md#decisions) 1, 7 and 10 to 13 and 17.

**Forcing is applied when belief is computed, never when content is stored.** Every write
is stored as written: a premise at the strength it was written at, a denial of a forced-monotonic
literal as an ordinary premise, and every rule firing whatever its rule and conclusion. The
network holds three forced sets beside the strengths (`jtms/set-forced`), each a set lookup
on the relabel path:

| set | members | what the labeller does |
|---|---|---|
| `:mono` | a premise of a `genlCx` edge (`checks/forced-premise?`) | its premise mark confers `:monotonic` |
| `:out` | a stored tuple that breaks its functor's length, at either strength (`arity/inert-tuple?`, [taxonomy.md](taxonomy.md#arity)), a stored fact whose argument fails its declared argument type (`checks/argument-conviction`, [argtypes.md](argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert)), and a stored rule one of whose variables no term can fill ([argtypes.md](argtypes.md#a-rule-whose-variable-no-term-can-fill-is-held-inert)) | the fixpoint never adds it, so it is never believed, forms no nogood and fires no rule; a firing of a held rule is never valid |
| `:void` | a firing convicted with its conclusion read against the baseline forced-monotonic set and its antecedents against the union of every reader's set (`checks/network-void?`) | the justification is invalid: it supports nothing and confers no class |

**The network reads the most permissive forced-monotonic set, and the read walk hides.** A
denial of a literal forced-monotonic only by a declaration stated outside CxUniverse forms
its negation nogood under the network's verdict, and the placement the declaration adds
defeats the denial at the readers that see it (`chain/declared-placements`). A
firing valid in the network because some declaration makes its antecedents forced-monotonic
is invalid at a reader that sees none of them, and a firing concluding a literal
forced-monotonic only by a declaration is invalid at a reader that sees the declaration unless its
rule is a forced-monotonic rule there (`:void?`, `exc/forced-void`); `why-not` answers
`:forced-conclusion` at such a reader, and `core/violations` reads an entry for a firing
void at some reader. Where either can hide a handle at a reader, the walk takes no `:monotonic`
handle at its label. The reader decides whether it sees a declaration, which reads the
defeats naming it, only for a declared predicate that a rule reads or concludes, so a write beside declarations of other predicates does not read their defeats
(`lein perf`'s `membership-clash-beside-denied-cxuniverse-declarations`). A rule that only
reads a declared predicate makes no read owe the walk when its own context's ancestor set holds a
declaration of the predicate that is IN and that no stored `except` or `defeat` names: every
reader of the rule sees that declaration (`exc/forced-reads?`). The upper ontology's
classifier rules (`typeOrthogonal`, `partitionedByType`) are of that kind.

**A verdict is placed at the readers whose forced-monotonic set gives it.** `chain/place-justified!`
places the verdict the baseline forced-monotonic set gives, which rests on no declaration. A declaration,
CxUniverse's included, whose predicate a member literal holds is an ingredient of a second placement, as an
except is of a guard defeat (ruling 23): at the maximal contexts that see the placement
and the declaration, resting on it, with the verdict that declaration gives, so a loser
there has a stored `defeat` (`chain/declared-placements`). A declaration leaving takes
only the placements resting on it. The inherited family's memo asks again the entries a
moved declaration reaches (`discovery/preserving-entries`), since the declaration moves
which claims a vantage believes. At a reader, `exc/verdict-at` re-decides with
that reader's forced-monotonic set, so a `defeat` placed above a declaration is out of force at the
readers that see the declaration.

`checks/force-sentex!` writes a stored sentex's `:mono` and `:out` memberships before its
premise mark lands, the arity family's store hook writes the `:out` membership of a
breaking tuple that a mint, a lift or a rewrite stores (`decide/note-candidate!`),
`checks/hold-rule-conviction!` writes the `:out` membership of a convicted rule a
generator or a `defn*` fact mints before its justification is added, and the
chainer writes `:void` before it adds a convicted firing's justification
(`chain/place-fact-conclusion`), so no element holds a label its set rules out, even for
one relabel. A binding or an edge moving moves the arity members at the settle's next
pass (`arity/drain!`).

**A denial of a forced-monotonic literal is believed until the literal is.** A stored
`(not S)` is an ordinary premise: it is believed, forms nogoods and fires rules while no
`S` is believed. Where `S` and the denial are both IN in the network, `decide/verdict`
makes the denial the loser of their negation nogood at either strength, since `S` is never a loser,
and the placed `defeat` hides the denial and what rests on it at the vantage and below.
`why-not` answers `:defeated` for the denial, with `S` under `:contradicted-by`. A denial
written `:monotonic` is the one `:monotonic` handle a `defeat` names, so while a body
that is a forced-monotonic literal is stored in both polarities
(`exc/yielding-reads?`, which reads the opposed bodies by functor, one or two counts per
predicate of the forced-monotonic set: [indexing.md](indexing.md#the-bodies-stored-in-both-polarities)),
the read walk takes no `:monotonic` handle at its label. The
negation nogood pairs stored sentexes, so a denial stays believed beside a literal that a
closure or an equation answers without storing it; a denial of an equation instance is
one of these, and the equation rewrites the denied instance as it rewrites every other
(`equational_test`).

**A rule concludes a forced-monotonic literal from forced-monotonic antecedents only.** A
firing is convicted when its conclusion is a denial of a forced-monotonic literal, or a
forced-monotonic literal and its rule is not a `checks/forced-rule?`: every antecedent a
forced-monotonic literal, no `unknown`, no
`set/defaultRule`, and no believed `exceptWhen`. A convicted firing is stored and held void,
and `core/violations` reads a `:forced-conclusion` entry for it, whose `:not-forced-monotonic` names the
rule's antecedent predicates that are not forced-monotonic (`checks/unforced-antecedents`). The entry is
not filed: `checks/forced-conclusion-entries` reads it at each call off the `:void` forced set
and off the firings of the rules concluding a declared predicate in a context that a
context seeing the declaration sees, so it stands exactly while the firing is stored and
void at some reader, and names the conclusion's stored spelling. The chainer
logs a convicted firing once at `:warn`, as its justification is added. `why-not` on the conclusion
answers `:forced-conclusion` with the rule and the same predicates. A forced-monotonic rule's firings confer the class its
antecedents give. `core.txt`'s `injection`, `surjection` and `bijection` rules are of this
kind. A `genl` consequent with variable arguments is forced-monotonic only where a firing
binds two predicate-spelled terms. An `exceptWhen` arriving on a forced-monotonic rule convicts its
firings, and the last one leaving releases them (`special/index-exceptWhen-meta`,
`special/unindex-exceptWhen-meta`).

**A declaration makes a predicate outside the baseline forced-monotonic.** Asserting or
retracting `(forced_monotonic_predicate P)` (or `(forced_monotonic_between_predicates P)`)
for a `P` outside the baseline rewrites the forced memberships over what `P` reaches, and
the relabel each moved membership runs is the network's recompute
(`checks/force-reach!`, called from the declaration's special-table arms when `P` joins or
leaves the union or the baseline set). A move of the baseline set reaches everything
that mentions `P`; a declaration elsewhere reaches the rules reading or concluding `P` and
their firings, and no denial. The settle then places again the nogoods over the facts of
`P` stated where a context at or below the declaration sees (`chain/declaration-reach`: the
contexts stating `P` that one of them sees, so a CxUniverse declaration reaches the stored
facts of `P` and not the contexts), and
a retraction takes the placements resting on the declaration OUT, so their nogoods are
placed again where they stand. The write costs the readers that see the declaration
(`lein perf`'s `declaration-at-a-leaf-beside-unseen-memberships`,
`declaration-at-a-leaf-beside-a-wide-stating-context`,
`cxuniverse-declaration-beside-bystander-contexts` and
`declaration-beside-stating-contexts-over-a-wide-descendant`). A declaration of a baseline
member moves no membership and runs no
switch. The rules in that reach are queued for a fresh join (`:all-rejoin`), so a firing
swept while it was held void is placed again. There is no ratchet: a KB that retracted a
declaration believes what a KB that never held it believes. The recompute costs the reach
of `P`. Belief moving a declaration (a derived declaration going OUT) moves the property
and runs no switch.

`organism.txt` declares `(forced_monotonic_predicate folk_species)`. Taking a species membership
OUT removes the separations `(disjoint_metatype folk_species)` induces between that species
and every other, which adds belief elsewhere. Because `folk_species` is forced-monotonic, a
denial of `(folk_species S)` loses to a believed `(folk_species S)` at either strength, and a rule concluding a forced-monotonic literal
from `(folk_species ?s)` alone is a forced-monotonic rule.

`core.txt` declares `(forced_monotonic_predicate reifiable_function)` and
`(forced_monotonic_predicate unreifiable_function)`. Whether a function's applications are
minted is definitional of the function, so no context or exception makes a mark false: a
denial of either mark is held OUT, and the two marks stated of one function are a conflict
rather than a defeat ([nat.md](nat.md)).

**Retracting a declaration is refused where its predicate has no unforced semantics.**
`retract!` and `edit!` refuse the retraction of every declaration `core.txt` makes except those
of `injection`, `surjection` and `bijection`, with `:type :uncleared-forcing`, the
`:predicate` and the `:missing` semantics (`checks/uncleared-forcing`). `genlCx` is always
forced and lifted. The refusal reads the sentence alone.

**A restart rebuilds the sets from the records.** `recover` replays every premise at its
stored strength and every justification, then writes the forced memberships the
forced-monotonic set gives (`checks/force-stored!`) before it reads belief. A denial of a
forced-monotonic literal
stored with no premise mark and no support is the record a store from before this design
kept inert; `force-stored!` gives it the `:default` premise mark. A premise such a store
holds `:monotonic` stays `:monotonic`: no record tells a coerced strength from a written one. A
firing such a store dropped is placed again by the re-join a retraction of its
declaration queues, and by `forward-chain` where the declaration was retracted before
the upgrade. The reasoning image carries the forced sets and records the forced-monotonic
declarations in its policy (`reasoning-image/declared-forced`), so an image computed under
other declarations is declined.

### Strength propagates from the antecedents

A justification confers **`min(its own strength, the weakest of its antecedents'
classes)`**, where a rule's own strength is read off its defeasibility:

- a **bare rule** confers `:monotonic` — it adds no defeasibility of its own, so the
  conclusion is capped by whatever it rests on;
- a **`set/defaultRule`** confers `:default` — it introduces defeasibility, so its
  conclusions are always `:default`;
- a **guarded rule**, one with an `(unknown S)` antecedent or an `exceptWhen` stored
  against it, confers `:default` whatever its defeasibility and its antecedents' classes
  ([reference.md](reference.md#decisions), decision 14). A blocker arriving takes its
  conclusion OUT, so the conclusion is never `:monotonic`.

`provers/firing-strength` computes this class, and a firing records it as its
justification's `:strength`, which the dense network keeps in its `j-mono` bitmap. The
exceptions are read as stored, belief unread. An `exceptWhen` can arrive after the rule
has fired and can leave again, so `special/restrength-firings!` rewrites the strength of
the rule's recorded firings when one is stored or removed, as it does when a re-assert
resolves the rule's defeasibility ([inference.md](inference.md)).

A conclusion is therefore no stronger than the weakest thing it rests on: a bare rule
over a merely-default premise concludes a *default*, the same bare rule over known-true
facts concludes `:monotonic`. **The taxonomy edges a firing names are grounds like the
facts** — a `genl` edge a subsumed match climbed, a `genlCx` edge the conclusion's context
reads the rule or the facts over ([contexts.md](contexts.md)) — and cap it the same way.
The **informant is excluded** from the cap. So are the marks of a `respell` justification,
which caps its class at its first antecedent, the as-written row, alone
(`jtms/class-antecedents`, [canonicalization.md](canonicalization.md#a-mark-a-reader-does-not-believe)).

A rule's own class (`:strength` — `opts :strength` at the entry point, what `defeat-class` answers
for its handle, what a solver is shown) and a rule's defeasibility (bare versus
`set/defaultRule`, what its firings confer) are two slots, and only the second moves belief;
nothing in the engine defeats a rule. Why the cap, why the taxonomy edges count, and why the
informant does not: [why](defenses.md#a-firing-is-capped-by-its-weakest-ground).

This makes the class equation **recursive**: a node's class depends on its
antecedents' classes. `jtms/region-classes` solves it as a **least fixpoint inside
the region relabel**, so locality is untouched:

- every in-region IN node starts at `:default`, the bottom of the lattice;
- antecedents outside the region are boundary — their stored class is read and held
  fixed, exactly as their labels are (a boundary node whose class could move would
  have an antecedent in the region, and would therefore be in the region);
- iterate to stability with a **semi-naive worklist** — a node's class is recomputed
  only when one of its antecedents' classes moves (reached through `:consequences`), so
  the cost is O(region edges) rather than O(region depth × region).

The least fixpoint is unique, so it is independent of visit order and of the order the
knowledge arrived in: [why a single pass would be
wrong](defenses.md#the-class-fixpoint-is-a-least-fixpoint-not-a-single-pass).

## Three invariants

Everything below is in service of these. They are not negotiable. The first two pull
against each other, and the third decides where the state that reconciles them may live.

### 1. Order independence

**The same knowledge, given in any order, yields the same beliefs.** A common-sense
KB learns generalities and specifics in whatever order the world supplies them —
"birds fly" before or after "Tweety is a penguin" — and an engine whose answers
depend on that order is answering a question nobody asked.

Belief is therefore *a function of current state*, whether the engine maintains it at the
write or computes it at a read. The property holds of belief over the stored knowledge.
`try-assert` is the one write entry point that reads arrival order. It refuses a write
that would clash with stored content, so arrival order decides what is stored
([api.md](api.md#refusing-a-clash)). The stored knowledge still yields the same beliefs
whatever order it was stored in.

Two leaks would let arrival order back in. The first is **tie-breaks**: when two beliefs
are equally strong something has to choose, and every such choice keys on **content**
(`solve/content-key`) rather than on the handle — [why content and not the
handle](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle). The second is
**a dependency a justification does not record**: retracting X must leave what a KB built
without X would hold, so a justification names every reachability its firing rests on — the
`genl` edges a subsumed match climbed, and the `genlCx` edges the conclusion's context sees
the rule and the facts over ([contexts.md](contexts.md)) — and both retract and defeat run
the ordinary dependency-directed path. Where a reachability outlives the one witness the
firing named, the conclusion comes back as a re-derivation: after a retraction or a network
defeat of the witness in the network. After a placed `defeat` or an `except` of it, a
reader that still reaches the path's ends reads the firing standing ("Where the layer
stops" states what each leaves stored).

**The invariant is over the writes offered.** No definitional clash is refused
(decision 8 of [reference.md](reference.md#decisions)): a sentence that completes a
disjointness, functional, cover, `asymmetric` or `anti_transitive` clash with content the
KB already holds is stored, and the settle places the nogood with the verdict its members'
classes give.
So the same sentences in any order leave the same store and the same beliefs, and a clash
whose members are all `:monotonic` stands in `conflicts` whichever member arrived last.
`try-assert` is the one write entry point outside the invariant: it refuses a clash with
believed content, so whether a write lands depends on what arrived before it
([api.md](api.md#refusing-a-clash)).

**What a refusal may rest on.** A refusal reads the sentence and nothing the KB holds
beyond the vocabulary that spells it: naming (which reads the sentence's own argument
count), groundness, a malformed special predicate, and a length binding against an engine
term's shape or the bound term's spelling
([taxonomy.md](taxonomy.md#arity)).
`checks/refuses-assert?` answers false for a clash that names the other stored members
of its nogood (`checks/arbitrable?`), so the entry point stores it, and what is stored is
a function of what was offered. A declaration over two `genl`-related types, and a cover naming a part
disjoint from its whole, are stored like any other declaration, and each is a hard clash
`conflicts` reports
([Declarations over related types](#declarations-over-related-types)). A tuple under
`irreflexive`, a non-mergeable `anti_symmetric` converse and a tuple whose length breaks
its predicate's arity binding are stored in every order, and each is placed as a nogood
([The nogood families](#the-nogood-families)). A fact whose argument fails its declared
argument type is stored and held OUT
([argtypes.md](argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert)). A write the
forced-monotonic set rules out is stored as written and held OUT or void by the
labeller ([The forced-monotonic set](#the-forced-monotonic-set)).

`test/vaelii/order_independence_test.clj` enumerates every permutation of each
scenario and demands a single distinct outcome. Note that the weaker assertion —
"exactly one side wins" — is true under every order *even when the winner flips*, so
it passes against an order-dependent engine. Asserting the **same** side every time is
what catches it. `subsumption_support_test` and `placement_context_witness_test` are the
retraction half, each asking whether losing an edge lands where never having had it does.

### 2. Locality

**No operation recomputes the whole graph.** A change can only affect what is
downstream of it, so every relabel is scoped to the **affected region** — the
forward consequence closure of whatever changed — with the rest of the graph held
fixed as a boundary. Cost is proportional to the region, not to the size of the KB.

The reconciliation with invariant 1 is the crux: a least fixpoint over the region
with boundary labels fixed has a **unique** solution, and it is the same one a
global fixpoint would produce. Uniqueness is why locality costs no order
independence — there is nothing for a visit order to influence. Well-foundedness
survives too: the region starts with nothing believed inside it and only ever adds,
so a support cycle within the region that has no ground outside it never enters,
exactly as in the global computation.

**Locality is more than one claim, and they are secured differently.** The
*equivalence* — a region relabel reaches the labels a global one would — is semantic,
and the differential oracle holds it by comparing the whole network after every step.
The *containment* — the flips are inside the published set, and the touched set inside the
region — is what says a small region was asked for, and it is measured on both networks.
That **no work is paid per boundary node** is neither: it is structural, secured by the
`Tms` protocol passing no store, so no implementation of it *can* turn a boundary read
into a lock and a slot decode or a round trip. That is the same fact the resident
strength copy rests on. What is left — the cost of the in-region work itself — is the
one piece nothing on the protocol holds, and
[defenses.md](defenses.md#locality-is-a-claim-about-every-representation) is where the
shape that would break it is measured. The obligations a second network inherits are
listed once, with the test that enforces each, in the protocol's own docstring
(`src/vaelii/impl/jtms_protocol.clj`).

The region is also **the answer to a question callers ask**, which is why `settle`
publishes it rather than discarding it. Three readers want the same thing — a
consequence preview, a consequence report, and a change feed
([preview.md](preview.md), [feed.md](feed.md)) — and each of them would otherwise diff
the believed set, which is O(KB) per write and flat in nothing. `settle-finish` decides
once what the settle moved (the relabelled regions plus the flips no relabel records)
and hands that one answer to all three. That region collects a **superset** of the
handles whose belief flipped, on purpose:
[why](defenses.md#the-touched-set-is-a-superset-not-the-flip-set).

Measured, on an in-memory graph of N premise→conclusion pairs (no store in the way).
Each cell is a whole-graph relabel against the region-scoped one, so the pair reads as
what locality is worth at that size:

| nodes | `add-justification` | `sweep!` (2 nodes) |
|-------|--------------------|--------------------|
| 500   | ~760µs / **~18µs**  | ~150µs / **~38µs** |
| 1000  | ~1,300µs / **~20µs** | ~340µs / **~40µs** |
| 2000  | ~2,100µs / **~20µs** | ~540µs / **~41µs** |
| 4000  | ~4,000µs / **~20µs** | ~1,200µs / **~48µs** |
| 8000  | —                  | ~2,500µs / **~40µs** |
| 16000 | —                  | ~5,600µs / **~46µs** |

The `sweep!` column collects a fixed two-node chain out of a graph of N
premise→conclusion pairs, so the region is the same size at every N and only the
background grows. A whole-graph relabel therefore tracks the background exactly, which
is what the left-hand figure shows.

The whole-graph column grows linearly with the graph; the region-scoped one is flat.
That is the whole point — the gap widens without bound, so locality is an asymptotic
property rather than a constant factor. At present KB sizes it is invisible end-to-end:
a single `assert` is dominated by fixed per-assert overhead, not this join. It is a
claim about what happens at a million facts, not at a thousand — and a claim about every
representation of the network, not only the one this table measures:
[why cost shape is part of matching the reference](defenses.md#locality-is-a-claim-about-every-representation).

### 3. Separated state

**Knowledge lives in the KB, belief-free indexes live in the IndexStore, and belief and
every structure that reads it live outside both.** A cache filled at a read may sit
anywhere. The derived-state register ([caches.md](caches.md#the-derived-state-register))
holds every such structure as a row, and `lein lint`'s `derived` check reads the rows.

**Knowledge in the KB.** A sentence the engine holds, or would hold once an absence is
filled, is a stored sentex. Such a sentence is called *content* here: a conclusion, a
membership or edge a declaration entails, a lifted copy, and a firing refused only because
something is absent. A firing an `exceptWhen` or an `unknown` blocks is a stored sentex
with a guard defeat ([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)). A stored sentex is indexed, browsable, removable, read by `why` and
export, and read back by `recover`. While an absence or a conviction rules it out, the
sentex is held OUT. A refusal that reads the sentence alone is not content: naming,
well-formedness, and a `genl` cycle through negation refuse a sentence no later content
can admit.

Every row declares `:holds-content?`, and the `derived` check fails a row that declares
true unless the check's `HOLDS_CONTENT` list names it. The list names one row, S5, the
refusal record ([exceptions.md](exceptions.md), "A refused firing is remembered as
bindings"): its closed-extent and separation refusals, `:constraint` and `:lift` entries
are sentences no store holds, so `recover` re-derives them (`chain/rerecord-refusals!`,
`special/rebuild-pending!`) and a `:constraint` entry of a rule no trigger watches is not
re-derived.

**Belief-free indexes in the IndexStore.** A structure computed in full at the write from
stored content alone is an index, and belongs in the IndexStore as a count-trie family
([indexing.md](indexing.md)). The IndexStore holds only what is stored, so every posting
read names the reading it takes (`reads/believed-…` or `reads/as-stored-…`). The `derived`
check fails a row of kind `:index` or `:cache`, computed at the write or the settle, whose
`:reads` do not reach the labels (M1) and whose namespace does not implement `IndexStore`,
unless the check's `OUTSIDE_INDEX` list names it. The list names one row, R9, the rete
matcher's alpha memories, which exist only under `VAELII_RETE=1` or `rete/track!`. Queues,
journals, counters and pass-scoped memos are not indexes and are not checked.

**Belief outside both.** The JTMS labels are the only record of belief. A structure that
reads belief may be kept at the write (the taxonomy relations, the equality partition, the
placement candidates) or filled at a read (the taxonomy closures, the literal matches).
Either way it is a function of the stored content and the labels, its row declares the
write events that retire its entries, and `derived_state_test` fails a row that moves under
an event its row does not name. No property here requires belief to be recomputed rather
than maintained.

## The TMS (`vaelii.impl.jtms`)

Belief is a least fixpoint, recomputed region-locally rather than accumulated:

- **`:in`** is the believed set and the sole authority on belief — nodes carry no
  label of their own, so there is no second copy to drift. It is maintained
  region-locally. Nothing forces a datum OUT: a contradiction stores a `defeat` that a
  read applies ([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)),
  so the network holds support labels only, and a datum OUT is one with no valid derivation.
- `affected-region` — the forward consequence closure of whatever changed. A node's
  label is a function of its justifications' antecedents, so a node whose label can
  move is by construction reachable from what moved; everything else is boundary and
  is never even looked at.
- `relabel-region*` — the localized least fixpoint. Also recomputes defeat-classes,
  but only inside the region: a boundary node whose class could move would have an
  antecedent in the region, and would therefore be in the region.
- `set-blocked` seeds it with the **consequences of the justifications whose blocked
  status moved** — the ones blocked in both the old and the new set are already
  accounted for in the current labels, so a call that changes nothing does no work at
  all.
- the **sweep** (`sweep!`, and `retract!`'s tail) is region-local in the same way: the
  justifications to tear down are read off the dead nodes' own `:supports` /
  `:consequences`, never found by scanning the justification map. `exceptWhen` makes
  sweeping routine rather than a retraction-only path — a blocked justification leaves
  its conclusion OUT and the sweep collects it on ordinary fact arrival — so
  a sweep that scanned the whole graph would make a run of them quadratic.
- `relabel` (the whole-graph version) has **no engine caller at all**. The assert /
  retract / settle path relabels regions, and a rebuild composes the region relabels its
  own adds run rather than closing with a global pass (`recovery/rebuild-tms`), because a
  region relabel over the affected closure is equal to a global one. What `relabel` is
  for is the differential oracle: a whole-graph operation both representations implement,
  so the two can be compared on one.

### Derivation depth

A node's depth is what the forward chaining bound reads
([inference.md](inference.md#forward-chaining), `:max-depth`). The network holds every
depth at the least solution of one equation: a premise sits at 0, and any other node at
the least, over its justifications, of one more than the justification's deepest
antecedent. A justification's informant is not one of its antecedents. The solution is a
function of the network, so a network reached by any sequence of operations holds the
depths the same network built directly holds.

Two walks keep the stored depths there, each over a part of the region the relabel
already walks:

- **A depth that falls** — `ensure-node` placing a node shallower, or a premise mark
  landing on a derived node — is pushed down the consequences it lowers, shallowest
  first, and the walk stops at a consequence whose depth does not move
  (`jtms/lowered-depths`).
- **A node that loses a premise mark or a justification** — through `retract!`,
  `suspend-premise`, `drop-justification!`, or a sweep that removes a survivor's
  justification — has the consequence closure of the survivors among such nodes solved
  afresh, with every node outside it held fixed (`jtms/region-depths`, Knuth's
  generalization of Dijkstra's algorithm). A retraction that sweeps its whole closure
  walks nothing.

Both walks read the network through accessor functions, so the dense network runs the
same code over its columns, and `jtms_dense_oracle_test` compares the depths of the two
after every step of its streams.

A stored depth departs from the equation's solution in two cases:

- A firing places its conclusion at one more than its deepest **matched fact**
  (`chain/derive-conclusion`), and its justification also names the `genl` and `genlCx`
  supporters the match climbed. A supporter that is a premise sits at 0 and changes
  nothing. A supporter derived deeper than every matched fact leaves the placed depth
  shallower than the equation's, until a walk above re-solves the node.
- `recover` rebuilds the network with every depth at 0
  ([storage.md](storage.md)); only a later walk re-solves a node.

### Belief filtering is a namespace boundary

`jtms/in?` is the whole of the belief question, and the fourth invariant — a stored sentex
is not a believed one — is a claim about who asks it. The `IndexStore` postings are
storage: they hold a defeated default, a conclusion whose support was withdrawn and a
spelling an equality retired, because all three are revivable and belief lives here rather
than there. So a caller reading a posting owes an answer to *which* it wants, and read
straight off `vaelii.impl.protocols` a forgotten filter and a deliberate as-stored read are
the same three characters.

**`vaelii.impl.reads` is where the question gets asked, in the name of the read.**
`as-stored-…` takes the index store, because an as-stored read *is* an index operation, and
each entry point's docstring says what a stored-but-disbelieved answer is for. `believed-…` takes
the KB, because belief is a question about the KB — and it filters with `in?`, which drops a
superseded spelling along with a defeated one, so a believed entry point means what
`kb/sentexes-matching` means. An entry point is a wrapper and never a rewrite: one call to the
protocol method it names, the same laziness, the same count-aware path, so it adds no index
operation. The cardinalities, the term-name set and the watched-rule set carry one
entry point each, and each says why there is no second.

`lein lint`'s **E16** is what makes it a boundary rather than a habit: a raw index read
anywhere under `src/` but the implementers fails, and the allowlist in that check is the one
place an exception is written down. The implementers are the entry points themselves, the protocol,
the retrieval a believed read is built from (`kb`, `resolution`), the storage backends, and
the dump that copies every entry the index holds. `RecordStore` is deliberately outside the
check — a record *is* the storage, so fetching one asks nothing about belief. Why the
as-stored half is named rather than assumed:
[why](defenses.md#an-as-stored-read-is-named-never-implied).

### Two representations of the same network

The network is always resident, which makes it a scale wall of its own (the reference map
measured ~467 B/node — see
[density.md](density.md#phase-3--the-dense-truth-maintenance-network-tms-dense)), so it
sits behind a `Tms` protocol with two implementations, chosen by `open-kb`'s `:tms`:

| `:tms` | the graph is | |
|---|---|---|
| `:dense` (default) | bitmaps + primitive-keyed maps, and no justification object at all | 5.5× denser on a fact corpus, 3.3× on a rules-heavy one, ~3.8× at corpus scale |
| `:reference` | one atom over one persistent map | readers get a consistent snapshot from a single deref |

**The boundary is the representation, not the algorithm.** Both run the same least fixpoint
over the same affected region, because that is the semantics of belief here and not an
implementation detail; what differs is where a node's premise flag, depth and adjacency
live. What a second network owes — the fixpoint, atomicity to a concurrent reader, the
containment `touched` promises, and holding no store — is enumerated with its enforcing
test per item in the `Tms` docstring, which both implementations depend on. The dense network also
requires the reference namespace for two helpers (`jtms/graph-just`, `jtms/dissoc-all`), and the
reference requires nothing of the dense one. `jtms_dense_oracle_test` compares the two in full after every step of randomized
operation streams; plain `lein test` runs the whole engine through the default dense one,
and `VAELII_TEST_TMS=reference lein test` through the persistent-map baseline.

**Every method is in one of seven roles, and the protocol says which.** The network is
one function — `label(graph, attributes, blocked) -> (in, classes)`,
with `believed = in - superseded` — so a method either supplies an argument, reads a
result, or edits the domain. `jtms-protocol/roles` writes the division as data and
`jtms_protocol_test` holds it. The division is of what a method *touches*, never of what a
network may be implemented without: every mutation relabels, so every role's mutators
write the output role's state.

The two sets a caller replaces whole each settle are two roles rather than one, because
they enter belief at two different points:

| override | enters at | moves | decided by |
|---|---|---|---|
| `blocked` | inside `valid?`, so a blocked justification supports nothing | `in`, so a conclusion a closed extent or a withdrawn `different` blocks is swept | the rule's block re-evaluation (`chain/rule-firing-blocked?`), bounded by the recheck queue's triggers |
| `superseded` | subtracted at the read, after the fixpoint | nothing — the datum stays in `in` so its rewritten twin keeps its justification | the equality closure |

Neither is computed by the network, which holds no KB. Each method applies a set it was
handed, so its cost is the region that set seeds and never the cost of deciding the set.
A **third** place belief is decided is not on the protocol at all: a placed `defeat` and
a visibility `except` are applied per reading context above it, by the read walk over
`jtms/region-in`, and the network's labels do not move for either (*[A defeat is scoped
to its vantage](#a-defeat-is-scoped-to-its-vantage)*).

The eighth role, `:hold`, is the settle's and not the fixpoint's. A settle moves labels in
more than one relabel before it publishes, so for a reader on another thread it holds the
belief it began from: while a hold is open, each relabel records the labels it moves as
they were before the first move, the region it already walks being the cost, and a thread
other than the settle's reads those until the settle publishes
([storage.md](storage.md#the-single-writer-contract)).

**The network keeps the graph; the record store keeps the record.** A justification is
stored durably, and belief reads only part of it — the antecedents, the consequence, the
strength and the informant. The firing's **variable bindings** are no
part of that: they are read only to re-evaluate an `exceptWhen` query or a NAF antecedent
per firing, and both readers hold the KB and take the record from the store. So
`jtms/graph-just` projects a justification on the way in, and neither representation
holds a second copy of one. `core/justification` and its two neighbours read the store
for the same reason — a justification *is* a record, and a record's home is the store.
(The projection also normalizes, which is what makes the two representations store values
equal to each other's however a caller spelled the justification.)

**No stored antecedent vector is in arrival order**, because belief reads it as a set and
every *report* reads it as a list. Three of the eleven builders get there by **sorting on
content** (`kb/antecedent-order`) — forward chaining's two placement sites and
`special/derive-equality`, the three handed a vector whose order is an arrival. The order
is the sentence then the context — a **structural** key, walked in place by
`nm/compare-form` rather than printed, so no ambient `*print-length*` can elide two long
sentences to one prefix and drop the tie back onto arrival — and the vector never holds
the informant: the record names a rule once, in its own `:informant` slot, and
`jtms/rests-on` adds it back for a reader that wants everything a justification stands on.
Nothing reads a position — `valid?` and `has-justification?` read the set.

**A rule informant is an implicit antecedent.** `valid?` needs the rule believed, and
both representations list the justification under the rule's node in the adjacency, so
retracting or defeating a rule withdraws everything it licensed through the same region
walk a fact's retraction takes.

**The other eight build the vector positionally instead, or copy a stored one, and the
position is a role.** `special/deduce-lift` writes `[fact, declaration]`, `special/justify-twin!` writes
`[original, one path's equality edges…, genlCx edges…]`, and `special/entail-arg-type` writes `[fact, declaration,
genl edges…]` — each slot filled by what that supporter *is* to the derivation, so there is
no arrival to sort out; the tail of the third is `checks/edge-support`, a shortest
**visible** path expanding in name order. `special/materialize-defn-rule` writes the one
definition the rule rests on, and `context-nat/materialize-edge` writes `[sub NAT's
natFormula, super NAT's natFormula, declaration]`, plus the relation fact when one is the
evidence. `io.import/import-justifications!` remaps a dumped vector handle for handle,
carrying the exporting KB's order across. `integrate/fold-dependents!` and
`integrate/fold-supports!` copy a stored vector onto the surviving row of a fold, the first
putting the survivor in the folded handle's position.

**A list of justifications is ordered by the same rule**, through one key
(`kb/justification-content-key`): the informant's own sentence and context, the
antecedents' sentences, the bindings, then what it concludes.
`core/supporting-justifications`, `core/dependent-justifications` and a clash report's
`:justifications` all sort by it, and all three start from an id **set** — `jtms/supports`
and `jtms/dependents`. That both the stored vectors and these lists order on content and
never on the handle is one rule with one home:
[why](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle).

**The key is built once per entry, not once per comparison.** `sort-by` calls its key fn
from inside the comparator, so a naive sort builds it ~2·n·log₂n times — and each build
is a `get-sentex` per antecedent. The adjacency lists every firing a rule licenses
under the rule's node, so `dependent-justifications` on a rule pays that multiple on the
whole history:
at 100k firings, ~3.3M key builds where 100k would do. All three sites decorate, sort and
undecorate through `nm/sort-by-content-key`, which is the same comparator over the same
keys and stable either way.

Two properties are easy to assume and would be wrong — a dense network cannot simply
replace the reference (`RoaringBitmap` is mutable, and `jtms_atomicity_test` asserts that a
relabel applies all-or-nothing), and order independence rests on a node's backward
`:supports` and forward `:consequences` naming the **same** edge set:
[why both, and why they mean two implementations rather than one](defenses.md#two-tms-implementations-not-one).

### Blocked justifications (`exceptWhen`)

`:blocked` is a set of **justification ids** whose rule's exception currently holds,
and `valid?` reads it alongside its antecedent and rule checks. The TMS has no KB and
cannot run the level-6 exception query: the caller evaluates the exception and hands the
answer in with `set-blocked`, which *replaces* the set rather than adding to it. A block
therefore holds only while its exception holds now,
whatever order the exceptions were discovered in. The set is the placement context's
answer; where the exception holds only below the placement, the firing stores a guard
`defeat` there ([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)).

A blocked *justification* is invalid: it supports nothing and confers no defeat-class
(`node-class` never reads a blocked justification's strength), so an excepted conclusion
with no other derivation is OUT and the retraction sweep deletes it
([exceptions.md](exceptions.md#garbage-collection-not-defeat)).

**Recovery starts unblocked**, because it starts from an empty network and no store holds
an exception's answer. The interval between the rebuild and the next settle believes an
excepted conclusion, and that settle withdraws it by replacing the set. The whole-graph
`relabel` clears the blocked set and the supersession map, since neither can be recovered
from the store, and `retract!` prunes swept justification ids from the blocked set so a
stale id is never reapplied.

Both premises and justifications carry a **strength**: a premise its assumption strength
(on the sentex record), a `Justification` a `strength` field (the defeat-class it
confers). A `Justification` has no out-list: NAF is built, as `unknown` /
`thereExists`, by re-evaluation, see [naf.md](naf.md).

**Retraction** is dependency-directed relabel-then-sweep: drop the premise, relabel, and
delete every datum in the retracted datum's consequence closure that ends OUT. A datum
with another derivation survives. The closure it marks **is** the region it relabels, so
the two walk the graph once between them, and the sweep reads the `:in` set that relabel
just recomputed.

`suspend-premise` is the first two steps without the third: drop the premise, relabel
the region, sweep nothing. It is a retraction's whole effect on **belief**, because the
sweep never moves a label — it collects datums that are already OUT.
That makes it the one *reversible* retraction: `add-premise` at the same strength puts
it back, at the same handles, with every justification still where it was.
`core/preview` is the caller ([preview.md](preview.md)).

**Belief-sensitive reads.** A default a placed `defeat` hides stays *stored* but is not
*believed* where the defeat is in force. So matching is belief-sensitive: `res/raw-match`,
`core/sentexes-matching`, and `core/types-of` skip handles that are currently OUT, and a
read at a context skips what that context does not believe or see. Raw introspection
(`core/sentex`, `find-sentexes`, the web browser) still sees everything.

## Soft, prioritized contradictions (the settle layer)

`assert` does not throw on `S` vs `(not S)`. The write path relabels the region a write
affects, and `settle` runs after every assert / retract / `forward-chain` / `recover`.
Belief at a context comes out of four steps. The write path and the settle run the first
three, and a read runs the last at its reader:

1. **Relabel.** `jtms/relabel-region*` runs two least fixpoints over the affected region:
   `region-fixpoint` computes the members that are IN, then `region-classes` computes the
   defeat-class of each. No verdict and no `defeat` enters either fixpoint, so a nogood's
   members keep their network labels.
2. **Find the nogoods.** A **nogood** is a set of believed sentexes that cannot all hold.
   A negation pair comes off the index family of the bodies stored in both polarities
   ([The nogood families](#the-nogood-families)). A tuple-mark nogood, a membership
   nogood, an `irreflexive` or `anti_symmetric` nogood, and a declaration over
   related types come off the write-time candidate index. The settle finds the remaining
   family itself:
   `discover-inherited!` records each inherited nogood whose members the network believes,
   with its vantages (`inherited/install-inherited!`). The inherited family is:
   - a stored claim against a **known-true claim reached by argument preservation**
     (`preserving-nogoods`), whose second side was never stored. `(largerThan dog cat)`
     asserted `{:strength :monotonic}` reaches `(largerThan chihuahua maine_coon)`, and a
     stored `(not (largerThan chihuahua maine_coon))` denies a claim with no handle, as a
     stored `(largerThan maine_coon chihuahua)` does under an `asymmetric` mark on
     `largerThan` or a super-predicate of it (`inherit/converse-claim`), and as a stored
     membership `(S x)` does when a separation holds `S` apart from a preserved `P`
     whose claim reaches `(P x)` (`inherit/separated-claims`). The
     members are the stored claim and everything the reading rests on: the general claim,
     the declaration that permits the move, the relation edges the reach travelled, and
     any `(transitive R)` or `(symmetric …)` the reading hangs on. An inherited claim has
     no sentex to defeat instead of its reasons, so `decide/verdict` weighs that set as it
     weighs any other. Priority is the rebuttal range. Discovery reads the settle's
     region and what it re-opens, since a `genl` edge changes what reaches whose tuple
     without either side going near the region, and carries a standing clash whose
     inputs did not move ([The inherited-clash memo](#the-inherited-clash-memo)). A KB
     that stores no `transitiveInArg` or `transitiveInArgInverse` declaration pays two
     predicate-extent counts. [inherit.md](inherit.md) has the readings, and why a
     `:default` general claim produces no pair.

   The argument constraints are not nogood sources; the table in
   [What qualifies as a nogood](#what-qualifies-as-a-nogood) gives the reason.
3. **Place.** Each nogood is placed the way a firing places its conclusion
   (`chain/place-nogoods!`, `chain/place-inherited!`, [A nogood placed as a
   conclusion](#a-nogood-placed-as-a-conclusion)): at each maximal common descendant of
   the contexts its members and grounds are stated in, the nogood's **vantages**.
   `decide/verdict` resolves it from its members' **defeat-classes** in the network, read
   over the whole member set:
   - **a unique weakest member** → that member loses. The vantage stores
     `(defeat (sentexHandle L))` beside the `(contradicts …)`, and the network keeps the
     member IN. No solver. (Monotonic beats default.)
   - **a minimum shared by several, and defeasible** → a **dilemma**. Every member stays
     believed at `:default`, and `contradictions` reports the stored `contradicts`.
   - **a minimum shared by several `:monotonic` members** → irreducible; `conflicts`
     reports it (never throw).
4. **Read.** A read at context `C` subtracts what the placed sentexes `C` sees remove from
   the network's labels:

   ```
   believed(C) = in − superseded − defeat-hidden(C)
   visible(C)  = believed(C) − except-hidden(C)
   ```

   `jtms/in?` answers `in − superseded`. `defeat-hidden(C)` is every handle a `defeat` in
   force at `C` names, with every handle that rests only on such a target; `res/believed-at?`
   answers `believed(C)` through `exc/belief-hidden-fn`. `except-hidden(C)` adds every
   target of a believed `except` visible from `C`, with what rests only on one, and
   `exc/hidden-fn` applies both. Each is a walk over the asked handle's support, made when
   the read asks and kept for that read alone.

Step 1 runs region-locally. A relabel is a belief fixpoint over the consequence
justifications, held to the affected region by [Locality](#2-locality). Finding a nogood
reads no justification edge. The negation pairs come off a write-time index, and whether
some context sees both members of a pair in two contexts is a walk over the `genlCx`
lattice, so a `P` and a `(not P)` many contexts apart pair on the same terms as two in one
context. Locality is by **range**, and range cuts across the seven roles:

| range | what is in it | bounded by |
|---|---|---|
| support-graph-local | labels, the class fixpoint, the sweep | the affected region |
| lattice-ranged | nogood discovery and placement — does some context see every member and ground | the candidates the moved content reaches |
| query-ranged | the `exceptWhen` re-evaluation that fills `blocked`, and the guard defeats it places | the recheck queue's triggers |
| read-ranged | a placed `defeat` or a visibility `except` in force at the reader, and the conclusions resting only on one | the asked handle's support, walked once per read |

A protocol method's locality claim is about applying a set, never about computing one.

A default/default clash is **not** decided: defeat-class is the only axis
([There is no second axis](#there-is-no-second-axis)). Where one rule names the other's
case, [`exceptWhen`](exceptions.md) settles it structurally and no contradiction forms.
Where neither does (the Nixon diamond), the clash is a dilemma the engine reports.

No nogood the settle places reaches the `Solver` below
([defenses.md](defenses.md#a-settle-hands-no-nogood-to-a-solver)). The solver
`set-solver` installs is read by [`do/label`](solving.md) when no ASP backend is
reachable.

### What qualifies as a nogood

A nogood is a set the settle may resolve by defeating a member, so it has to survive
being acted on
([why the criterion is not "a member the detection reads through"](defenses.md#a-nogood-must-survive-being-acted-on)):

> **A nogood must stay derivable exactly as long as what it convicts stands.** Defeating
> its weakest member may dissolve it, but only by removing something the conviction was
> **about**. Inadmissible is a set whose defeat makes the clash undetectable while the
> content it convicted goes on standing.

The members and the reading, per source:

| source | members | read *through* | admissible because |
|---|---|---|---|
| negation, placed at the settle | the believed `P` and the believed `(not P)` | joint visibility — the placement sees both contexts ([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)) | no member supports the visibility verdict, and defeating either side removes one of the two claims the pair was about |
| a membership nogood, placed at the settle | the clashing memberships and denials alone, keyed on the **handle set**; the separations, covers and disjoint metatypes are read through and never members | the separating declaration or the cover, and the `genl` closure | no defeat this nogood licenses can unmake the reading that convicted |
| `preserving-nogoods` | the stored claim **and its reasons** — the general claim, the declaration permitting the move, the relation edges the reach travelled, any `(transitive R)` the reading hangs on | the same reasons, which here *are* members, and for a stored membership the separation that makes it a denial | defeating a reason withdraws the reach, which is what the pair was about, and the reason stays defeated |
| `arity`, placed at the settle | the offending tuple alone; for two related predicates, their bindings | the binding, a ground of the placement, and at the reader the bindings it believes ([The nogood families](#the-nogood-families)) | the binding is forced-monotonic and goes OUT only by retraction, so no defeat unmakes the conviction |
| **not** `arg` / `genlArg` / `interArg`, under the constraint-only reading or over a value | there is no second sentex: no membership is derived | the argument's believed type and the separation from the declared type | nothing derived to weigh and no class to compare. A refusal at the entry point, a drop on the derivation path, re-asked when the separation, the argument's memberships or the `genl` / `genlCx` closures move |

`nogood_admissibility_test` asserts the first three rows: a definitional clash's `:nogood`
set holds the clashing sentexes and not the declaration that convicted them, and an
inherited clash's holds its reasons.

### The inherited-clash memo

`preserving-nogoods` keeps `{:flat :mark :entries :by :left :moved}` in
`(reasoning/preserved-clashes kb)`. `:entries` maps a stored claim to its last answer (`discovery/preserving-entry`): the
nogoods, every context asked, the handles of every denying reading and the contexts they
are stated in, and the defeat-class of every member. `:by` is the entries' inverted
index: each entry is filed under every handle it reads, every member, its predicate, every
context it reads or asked, and whether it is a separated membership or holds a nogood
(`discovery/file-entries`). Each input below looks up in `:by` the entries it names, so a
settle reads no entry no input names. `:left` holds the sentences removed since the call,
and `:moved` the belief moves the next call's region does not name. A settle asks again
only where an input moved. It hands the candidate index the member sets of the entries it
asked again and of the entries holding a handle whose belief moved, each with the nogoods
found for it now (`inherited/update-inherited!`); a settle that carries no entry hands it
every entry's nogoods (`inherited/install-inherited!`). The region is what the
touched set recorded since `:mark`, the mark taken before the last call's questions, so
the second pass of a settle asks only what the first pass moved, and not the settle's
whole touched set again; a mark from before the last reset reads that whole touched set. An
image install drops `:mark` (`reasoning-image/install-from!`): the installed network starts
its touched sets at generation 0, where the writer's mark would read as a mark of those sets. The
inputs:

- **a member.** An entry is asked again when a member other than the stored claim is OUT
  or holds another class. A member's belief moves in a relabel, which the touched set
  records, or in a supersession, which `special/pending-supersession-moves` names.
  `settle-finish` adds both to `:moved` before it empties them (`discovery/note-touched!`),
  so a move after a settle's last question reaches the next settle's discovery. The
  stored claim's own belief is not an input, since its question reads the tuple's other
  claims. An entry whose stored claim is OUT publishes nothing and stays.
- **the reading's vocabulary.** A handle in the region, or a supporter of a moved
  flat-cache key (below), re-opens the whole stored extent of
  every predicate a non-claim channel of `inherit/moved-channels` names: a declaration, a
  relation edge the reach can cross, a `(transitive R)` or a mark. A `genl` edge between
  predicates re-opens every preserved predicate above either end. For a predicate
  preserved along `genl` and along no relation above it, a `genl` edge re-opens the stored
  facts holding a term of the edge's closure at a position preserved along `genl` or at the
  other position of a binary converse, and the stored memberships at such a term of the
  types separated from the predicate (`inherit/edge-reach`). A walk along `genl` crosses
  the edge only from one of its two closures into the other (`inherit/crossing-claim?`),
  so a fact holding no such term reads the same reach on either side of it. Where a
  commuting mark stands on the predicate or below it, the edge re-opens the whole extent
  (`inherited_clash_oracle_test/a-genl-edge-asks-a-predicate-preserved-along-genl-at-its-closure-terms-alone`).
- **a claim.** A moved claim re-opens the stored facts it reaches
  (`inherit/claim-reach-extent`), and not the extent, when it can change an answer:
  believed and known-true, since `clashing-claim` reads known-true claims alone, or moved
  in the region and of a predicate holding an entry, since every entry is asked from the
  vantages of the readings `inherit/denial-readings` reads off claims of every class. A known-true claim leaving is a member of every entry
  it answers, and no `defeat` hides known-true content.
- **a flat-cache entry.** `tax/set-cache-ctxs` journals each flat-cache key whose
  supporting contexts it moves (`tax/flat-moves`), and `:flat` holds the live taxonomy's
  position in that journal (`discovery/flat-reading`). The keys moved since are read
  through their supporters (the vocabulary channel above). A separation is read only by
  the readings of a membership of a separated type, so a `disjoint`, a `separating` or `partition` declaration
  or any other entry that no such reading reads asks no entry. Where the journal does
  not reach back (an image install, a
  rebuild, a journal restarted past its bound), the moves are the keys `:flat`'s map of
  `tax/flat-contexts` and the current one differ on.
- **a separation.** The ends of a separation key in the region (`tax/separation-ends`)
  and the lower end of a `genl` edge in the region whose upper end a separation reaches
  (`tax/sentence-separation-ends`) are the types the write moves separations at or below.
  Each such type separated from a preserved predicate some stored claim states
  (`inherit/claims-stored?`) re-opens the stored memberships of every type at or below
  it. Each preserved predicate at or below such a type re-opens its extent. An edge changes
  the supertypes of the types at or below its lower end alone. The memberships of a type
  below its upper end and not below its lower end are not re-opened
  (`inherited_clash_oracle_test/a-genl-edge-asks-the-memberships-below-its-lower-end-and-none-below-its-upper`).
  A re-opened extent of such a preserved predicate re-opens the
  memberships of the types separated from it
  (`inherit/separated-types`), and a moved claim the memberships it can deny
  (`inherit/claim-reach-separated`). An entry of such a membership is asked again when a
  handle of its readings, a `genl` edge or a separation moved, since a separation leaving
  re-opens no extent.
- **an except.** An `except` that moved (`special/except-moved`, and an `except` in the
  region) asks again each entry one of whose readings' handles lies in the consequence
  closure of its target, followed down the except cascade (`discovery/except-reach`).
- **a `genlCx` edge.** The pass's `genlCx` moves ask again each entry with a reading's
  context in their reach's `:below`, or with a context asked at or below a moved lower
  end, whose ancestor set the move changed
  ([contexts.md](contexts.md#one-context-move)). A rebuilt relation, or a placement cursor
  restarted since the index was emptied, asks every entry again.
- **a deleted record.** `integrate/sentex-removed!` records a departing sentence under its
  handle in the memo's `:left` while an entry stands (`discovery/note-removed!`), so an
  entry whose stored claim left is read off `:left` and not off the records. A region
  handle with no record is read from `:left` through the two channels above: as
  vocabulary, and as an OUT claim moved in the region. A retracted `genl` edge between
  predicates is not a member, so its `:left` sentence is the only
  input that re-asks the clash the edge carried, whether the edge carried an `asymmetric`
  mark down (`tax/props-over`) or made a sub-predicate's claim the super's
  (`inherited_clash_oracle_test`). A region handle with neither a record nor a recorded
  sentence re-asks every entry.

`recover` empties the memo before its settle, and that settle's first discovery carries
nothing. It asks the stored extents of the preserved predicates, read off the index, and
the stored memberships those claims reach (`discovery/separated-reach`), and reads no
region handle. The region can miss a stored handle: a stored sentex with neither a
premise mark nor a justification is never relabelled, so the touched set does not hold
it. The memberships
are read from the claims, one `inherit/claim-reach-separated` per stored claim, and a
preserved predicate no stored claim states asks no membership. Every type below
`tangible`, `spatial`, `temporal` or `causal` is separated from `empty` and `nonempty`
(`core.txt`'s partitions of `thing`), so a KB that states neither asks none of those
types' memberships. The discovery reads no record of any
other sentex.

A stored claim asked and finding no clash is kept as an entry with no nogoods while
`inherit/denial-readings` names a claim that would deny it in a reader seeing both: the
`genlCx` edge or the except that makes such a reader asks it again. A stored claim with no entry has no clash in any reader the
lattice could add, and the region and the re-opened facts are the writes that can give it
one.

`*incremental-preserving*` bound false carries nothing and re-opens the whole extent for
every moved claim, the reference `inherited_clash_oracle_test` compares against step by
step; its streams do not generate the supersession shape. The same test replays the set a
stream leaves stored into a fresh KB, since both of those arms ask through
`preserving-entry`. `lein perf`'s
`inherited-clash-arbitration` and `inherited-clash-arbitration-split` hold the per-assert
cost against the standing set, `inherited-entry-retraction` the per-retract cost
against the carried entries, `inherited-entry-declaration` the cost of a declaration
no entry reads, and `inherited-entry-except` the cost of an except no entry's readings
rest on.

### A revived datum is a datum the agenda has not seen

A revival is a **relabel**, which brings back everything still stored: a premise
restored by `preview`'s rollback, or a derivation an unblocked justification or a
returning antecedent gives back, and the conclusions resting on it. A target a removed
`defeat` gives back at its own context is not a revival: the network kept the target IN, so
a rule's firings over it stand. It is re-chained only when the taxonomy derives an answer
from it (`tax/derives-from?`), and the merges and lifts a mark owes are re-read for it
(`settle/defeat-moves`). A relabel cannot bring back a conclusion that was never derived.
While a datum is OUT, `chain/*matcher*` does not match it, so a rule's *other* antecedent
arriving meanwhile joins against nothing and attempts no firing.

No other settle instrument finds that firing afterwards. It holds no justification, so
it is in no blocked set for `released-rules` to read, and it reached no placement, so it
left no entry for `released-refusals` to re-ask ([exceptions.md](exceptions.md)). A record
covering it would need one entry per **non-match**, which nothing bounds, where the
refusal record holds one entry per firing a rule declined to place. So `settle` reads the
trigger where the belief moved: it re-seeds the revived datums onto the chaining agenda
(`settle/revived-seeds`), and the ordinary fixpoint does the rest.

A relabelled region is mostly datums that did not move, and everything the settle
*created* reads as newly believed too. The JTMS keeps four touched sets, cleared
together when `settle` finishes with them:

| | |
|---|---|
| `touched` | the relabelled regions: a superset of every handle whose belief could have moved |
| `touched-in` | of those, the ones already believed when the settle first relabelled them |
| `touched-new` | the ones whose **node this settle created** |
| `touched-out` | the ones a forced-set change took from IN to OUT ([The forced-monotonic set](#the-forced-monotonic-set)) |

`jtms/revived` is `touched` minus `touched-in` and `touched-new`, plus `touched-out`,
filtered to what is believed now. A datum a declaration took OUT and a later write in the
same settle put back IN is in `touched-in` when it was believed as the settle began, and
a partner that arrived while it was OUT joined against nothing, so `touched-out` names it
for the re-seed. The change feed
and `preview` read `touched-in` to say which way each handle moved ([feed.md](feed.md));
`touched-new` exists only for `revived`. Without it every asserted fact and every
conclusion drawn from one would be re-seeded, since each is in its settle's region,
believed at the end of it and not at the start, and the settle would chain it twice.
The distinction exists only at the moment of creation: by the time the relabel runs, a
new node and one that has been OUT for a hundred settles are both unbelieved nodes about
to become believed.

A reader that asks the touched set more than once in one settle takes a mark
(`jtms/touch-mark`) and reads what the touched set recorded after it (`jtms/touched-since`): a
datum relabelled again after the mark is in that answer although `touched` held it
already, which a set difference over `touched` would drop. Each mark is the reader's own,
and `reset-touched!` outdates every mark, after which one reads the whole touched set. One
reader marks: the inherited family's discovery ([The inherited-clash
memo](#the-inherited-clash-memo)).

The seeds are **datums**, so re-chaining one costs what asserting it costs: a join per
rule keyed by its predicate. Seeding the *rules* instead joins each rule over its whole
extent. For a two-antecedent rule, re-chaining one datum is linear in the partner's
extent and re-chaining the rule is linear in the product of the two extents.

The re-check triggers are one idea over several populations: the rules a taxonomy edge
queued, an aggregate's moved value, a refused firing's recorded bindings, a relabelled
revival, and the spelling an un-merge gives back. Each has an instrument sized to its
own population, and they split on granularity. The three that can name a **datum** (a
released refusal's re-derived conclusion, a relabelled revival and an un-merged
spelling) hand it to `settle/rechain-seeds` and pay what asserting it pays. The two that
cannot (a rule queued with `:all` by a taxonomy edge, and an aggregate whose bound value
moved) have only the rule, so they take the extent-wide re-join through
`rechain-exception-rules` and are narrowed at the trigger instead.

A datum is seeded once per settle however many passes run, and a datum that revives and
is defeated again inside one settle is never seeded: the set is read after the resolve,
so it describes where the pass landed rather than what it passed through. A pass that
revived something is **productive** even when the blocked set stands still, as an
aggregate's is, or the loop would converge having derived nothing. So is a pass whose
placed defeats moved a datum a watched rule's `unknown` or exception reads
(`settle/post-defeat-moves!`, [naf.md](naf.md)): the pass re-chains the released rules
whether or not anything was queued. So is a pass that leaves the arity family a
refresh owed (`arity/moved?`): removing a `(unary_predicate T)` the refresh withdrew moves
`T`'s length after the refresh read it, and the next pass holds the tuples that length
breaks inert
(`absent_type_order_test/a-length-arriving-after-a-mint-holds-it-out-at-that-write`).
A **rebuild** stands
aside (`settle/*rebuilding?*`): `recover` relabels the whole graph, so most of what it
believes reads as newly believed, and the stored justifications it replays already carry
every derivation.

#### The other half: a spelling an un-merge gives back

One kind of revival is not in the region at all. A datum displaced by an equality merge
is OUT while its **twin** joins in its place, so a partner arriving during the merge
concludes at the twin's spelling. When the equality stops being believed (retracted, or
a derived one's support withdrawn), the twin is swept and the displaced spelling comes
back. The conclusion has to be made again at the surviving spelling, or the KB believes
both antecedents of a forward rule and holds neither spelling of what they conclude.

Supersession changes belief with **no relabel behind it**: a superseded datum stays in
`:in` for `valid?`'s purposes, because its twin is justified *by it* and forcing it OUT
would leave the merge believing neither spelling ([equality.md](equality.md)). So the
flip is in none of the three touched sets, and `jtms/revived` cannot see it.

`special/refresh-supersessions` runs on the write path, and it records each flip with the
entry it replaced (`special/take-supersession-moves!`), which `settle-finish` reads once
the loop has converged. So the spellings a flip gives back go into
`settle/*unmerged-sink*`, and **`settle` re-seeds them and settles again**, as `core/retract!` settles twice around its own re-derivation.
Rounds are bounded by `max-unmerge-rounds` (8); two is the structure of every real case,
and reaching the eighth is logged as a bug rather than looping. Two other designs, moving
the reconcile into the settle loop and a re-enter signal from `settle-finish`, cost more
elsewhere: [why](defenses.md#an-un-merge-re-seeds-through-a-second-channel).

The same rounds carry the opposite flip. `settle-finish` returns the spellings superseded
since the last settle, and `settle` drops each rule firing that names one of them as an
antecedent or as its rule (`settle/withdraw-retired-firings!`), deletes what the drop
sweeps, and settles again. A superseded spelling fires nothing (`chain/process-datum`), so
a firing made over it before the merge is one the merge-first order never makes; with
the firing dropped, the twin of its conclusion keeps only the representative's own
firings. A firing that the superseding merge rests on stays (`settle/merge-support`): a
rule concluding an equality from the spelling that equality retires has no order in which
the merge comes first. A dropped firing that climbed a retired `genl` edge is drawn again
over the edge's twin (`special/withdrawn-edge-seeds`, read before the drop), so `(dog Rex)`
under `(genl dog mammal)` and `(genl mammal animal)` keeps its firing of
`(animal ?x) => (alive ?x)` when `(rewriteOf mammalia mammal)` arrives last. The drop
reads the dependents of the retired spellings and the support of their merges, and
nothing else. `core/preview` (`*sweep?*` off) drops nothing. A rebuild's first settle
retires every superseded spelling, so a store written before 0.24.0, which kept the
firings over them, recovers to the store a fresh KB holds
(`negation_test/a-recovered-store-withdraws-a-firing-over-a-superseded-spelling`).

### The set-membership states a node can hold

A node carries two independent descriptions, one persistent and one per-settle. Its
**belief state** is read from the datum-keyed set `:in` and the `:superseded` map, and it
survives across settles. Its **touched-set membership** is read from `:touched`, `:touched-in`
`:touched-new` and `:touched-out`, and `reset-touched!` clears those four at
`settle-finish`, so a touched-set membership exists only during the settle that wrote it.
`:blocked` and the `:void` forced set are keyed by justification id rather than by datum,
so they name no node state of their own; each reaches a node through `valid?`, which reads
it in the fixpoint. A node is OUT exactly when it has no valid derivation or is in the
`:out` forced set.

Reported belief — the answer `in?` gives — is `:in` minus `:superseded`, because a
superseded spelling stays in `:in` to keep its rewritten twin's justification valid even
though it no longer matches. The invariant `superseded ⇒ :in` leaves three belief
states:

| belief state | in | superseded | `in?` |
|---|:--:|:--:|:--:|
| believed | ● | | yes |
| superseded | ● | ● | no |
| no derivation | | | no |

A `believed` node is a premise or a datum with a valid justification, and not in the
`:out` forced set. A node with `no derivation` has no premise and no valid justification,
or is held OUT: a retraction sweep deletes one that is no premise, and one still present
in `:nodes` is one a sweep has not yet reached or a premise the forced-monotonic set holds OUT.

The **revival slot** of the touched sets is `:touched` without `:touched-in` or `:touched-new`
— a datum this settle relabelled that was neither believed at the settle's start nor
created by it — together with `:touched-out`. `jtms/revived` reads that slot filtered to what is believed now, so a
believed node in the revival slot is a `revived` one. A believed node created this settle
sits under `touched-new`, and a believed node the settle relabelled without moving its
label sits under `touched-in`. A placed `defeat` moves no node state of its target: a read
applies it, and the settle publishes the move it makes beside the touched set ([The published
set](#the-published-set)).

### Which entry point the content came through

One logical situation, one representation: the nogood above, however the content
arrived. Neither the path the content came in on nor the members' classes decide whether
it is stored:

| where the clash arrives | members all `:monotonic` | a `:default` member |
|---|---|---|
| a **rule firing** (`place-conclusion`) | placed; a hard clash in `conflicts` | placed; the unique weakest is defeated with a `why-not`, a tie is a dilemma |
| an **`assert`**, disjointness / functionality / a refuted cover / asymmetry / anti-transitivity / irreflexivity / antisymmetry that does not merge | stored; a hard clash in `conflicts` | stored; placed as a firing's clash is ([The nogood families](#the-nogood-families)) |

The declaration, the functionality mark, the cover and the `genl` steps a conviction reads
are the nogood's grounds: read through, never weighed, and never a reason to refuse. A
known-true opposing claim beside a known-true declaration therefore makes a hard clash
rather than a refusal, whichever member arrived last.

A self tuple `(P a a)` of an `irreflexive` `P`, and a converse no equality could
reconcile under an `anti_symmetric` `P`, are placed in either arrival order, so a late mark
places the `defeat` of a `:default` self tuple where the tuple and the mark are seen
together.

A firing has no caller to refuse, so there the choice is between dropping the
conclusion — no sentex, no justification, and `why-not` reduced to `:not-stored` — and
placing it for `settle` to weigh. Placing it is what gives the loser a reason, and the
entry point makes the same choice for a writer.

The **retroactive** half runs the same way. A declaration arriving *after* the content it
convicts — what an import routinely does — reads no membership: the candidate index keeps
every term holding two memberships, or a membership and a denial, and the placement pass
places the term's nogoods through the declarations that convict them
([The nogood families](#the-nogood-families)). The weaker side is defeated, or an
equal-strength set is reported by `contradictions` or `conflicts`, so belief does not
depend on whether the schema or the facts arrived first, and a recover of the same records
places the same pairs. A pair only a common descendant context sees is placed there. A term **joining** a disjoint metatype is a declaration too, and the only
one the taxonomy rather than the sentence identifies ([taxonomy.md](taxonomy.md)).

**One retroactive half is an inference rather than a nogood.** `(functional P)` arriving
after two `:monotonic` symbol values for the same first argument does not convict either
of them — it *merges* them, so `special/equate-existing` runs it exactly as
`derive-functional-equalities` runs the same inference on the arriving fact
([equality.md](equality.md)). `anti_symmetric` is the same shape: a believed `:monotonic`
converse `(P b a)` beside a `:monotonic` `(P a b)` forces `(equals a b)` and merges,
`special/derive-antisymmetric-equalities` and `antisym-equate-existing` reaching it from
the fact side and the declaration side. A symbol pair with a `:default` member is a
nogood under either mark, placed as above ([The nogood families](#the-nogood-families)).

Content the engine stores on its own behalf is admitted as a firing's conclusion is
(`checks/derivation-violation`): the decontextualization lift's copy, the equality
migration's twin and the argument-type mint. A clash one of them forms is stored and
placed, since refusing it would read stored content and make the stored
set depend on the arrival order. Only the abducibility check on what `abduce` may assume refuses
a clash (`checks/constraint-violation`): a hypothesis is never stored.

### A nogood is a set: `anti_transitive` has three members

`(anti_transitive P)` says a two-step chain forbids the direct step: `(P a b) ∧ (P b c) ⇒
¬(P a c)`. The three cannot all hold and no two of them are the clash, so the conviction
is one nogood with three members:

- **Discovery** reads the chains a step is a member of when the step is stored, in each
  of its three roles — the direct step, the first step and the second step
  (`tuple/found-for`) — so the chain enters the candidate index whichever step arrives
  last.
- **Placement** reads `decide/verdict` over the whole member set: a unique weakest member is
  defeated, a defeasible minimum shared by several is a dilemma, and all-monotonic is a
  conflict. Three equal defaults are one three-sided dilemma.
- **Reporting**: `contradictions` returns one entry whose `:sides` are three, and
  `(contradicts …)` names all three sentences in content order. `:handles` is not a pair.

The mark is read **up** the predicate hierarchy like every other constraint mark, so
`(anti_transitive parentOf)` convicts a chain spelled in `fatherOf`; the steps are read under
every predicate below the mark, so a chain written half at each spelling is one chain. A
step reachable **only** by argument preservation is not enumerated
([Where conviction is one-sided](#where-conviction-is-one-sided)). A self tuple
`(P a a)`, its own whole chain, is admitted, as an `asymmetric` predicate's is:
`anti_transitive` does not imply `irreflexive`. No predicate is declared both
`anti_transitive` and `transitive` ([taxonomy.md](taxonomy.md)).

### Which contexts can contradict each other

Two beliefs clash when **some context sees both**: their contexts have a non-empty common
down-closure (`tax/maximal-common-descendant-contexts`). Asking whether one context
`sees?` the other catches only a comparable pair and exempts every sibling pair; two
incomparable contexts can share a descendant, and from there `X` and `(not X)` are both
visible. The common-descendant test generalises `sees?` (if K sees Y, K is itself a
common descendant), so it detects everything `sees?` would. A negation pair is placed at
the maximal common descendants of its two contexts.

A **definitional** clash reads the same rule from the other end. A disjointness needs the
separation and the `genl` edges it closes under to be visible too, so a membership
nogood is placed where the members, one separation's declarations and the `genl` edges
it climbs are all seen (`chain/place-memberships!`).

### A defeat is scoped to its vantage

A nogood has **vantages**: the most general contexts that see every member, and for a
definitional clash the grounds as well. They are the contexts it is placed in
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)). A placed `defeat`
removes its loser from belief at the vantage and at every context that sees it, and
nowhere else; the network keeps the loser IN ([reference.md](reference.md#decisions),
decisions 2 and 3). A context's belief therefore depends on its own ancestor set and on
nothing a spec context holds. `preserving-nogoods` takes the most general contexts that
see the stored claim's own context and the reading that denies it, and
`chain/place-inherited!` places each inherited nogood there.

```
CxA            (cat Rex)   :default
 └─ CxD        (dog Rex)   :monotonic       (genlCx CxD CxA)
(disjoint dog cat) is visible from both
```

CxD is the only context that sees both memberships, so CxD is the vantage, and the
`(defeat (sentexHandle <(cat Rex)>))` is stored there. A read from CxD finds `(dog Rex)` and
not `(cat Rex)`. A read from CxA finds `(cat Rex)`, because CxA does not see the defeat.

**A vantage sees the grounds as well as the members.** A definitional clash is its members
and what separates them — a `disjoint` declaration, the `genl` path up to a separated
type, a `functional` or `asymmetric` mark — so the most general context holding the whole
clash can sit below the members' maximal common descendant:

```
CxA  (t1 Pip) :monotonic     CxB  (t2 Pip) :default     CxDecl  (disjoint t1 t2)
CxW sees CxA and CxB
 ├─ CxX sees CxW
 └─ CxV sees CxW and CxDecl
```

CxW reads no separation and convicts nothing. The nogood is placed at CxV, the most general
context that sees the members and the separation (`chain/place-memberships!`): CxV and
every context below it believe `(t1 Pip)` alone, while CxW and CxX believe both
memberships. No write reads the contexts below CxW; `lein perf`'s `per-reading-vantages`
holds an assert flat in them. Two members stored in one context have that context as
their lowest, and a separation declared only below it places the nogood there
(`reference_test/a-declaration-below-a-pair-stored-in-one-context-decides-it-there-in-every-order`).

**A vantage sees every member, and some clashes have more than two.** An `anti_transitive`
chain is a triple, and a context seeing two of its steps reads no clash:

```
CxA  (nearP Aa Bb)     CxB  (nearP Bb Cc)     CxC  (nearP Aa Cc)
CxAB sees CxA and CxB, CxBC sees CxB and CxC, CxAC sees CxA and CxC
 └─ CxW sees CxAB, CxBC and CxAC
```

The chain is placed at CxW, and CxAB, CxBC and CxAC each keep both steps they see
(`reference_test/a-chain-in-three-contexts-is-decided-where-one-reader-sees-it-whole-in-every-order`).
An inherited clash has more than two members as well: a stored claim denied by a known-true
claim read by argument preservation rests on the general claim, the declarations and every
`genl` edge the reach travels, each possibly in its own context. `inherit/denial-readings`
names those handles, read from the whole KB, and `preserving-nogoods` asks the clash from
the most general contexts that see all of them with no except hiding one
(`res/exception-aware-placements`, the placement a firing takes) ([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

**A defeat of a ground hides what the ground convicts.** A placed sentex rests on its
nogood's grounds, so a ground a second nogood defeats takes the first nogood's placed
sentexes out of belief wherever that defeat is in force:

```
CxUniverse   (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
 ├─ CxA      (genl chi dog)                 :default
 └─ CxD      (not (genl chi dog))           :monotonic
      CxB sees CxA and CxD:  (chi Kit) :default   (cat Kit) :monotonic
```

CxB is the vantage of both nogoods. The negation pair places the `defeat` of the edge
there, and the membership nogood places the `defeat` of `(chi Kit)` there, resting on the
edge it climbed. At CxB the edge is not believed, so neither is the membership defeat: CxB
believes both memberships, and `contradictions` reports nothing, in every arrival order and
whatever number of passes the settle runs
(`reference_test/a-second-settle-pass-leaves-the-release-lattice-reading-unchanged`).

**A read applies the placed defeats through `exc/hidden-fn`**, the predicate every
belief-filtered read with a concrete context asks for the visibility `except`
([contexts.md](contexts.md)). The predicate reads a handle as hidden from reader K in
three cases: a believed `except` visible from K hides it, a `defeat` in force at K names
it, or every justification it has rests on a handle hidden for one of those two reasons.
The read walk computes the third case over the handle's support
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)), so a consequence
follows the reader. A forward rule `(cat ?x) ⇒ (meows ?x)` stated in CxA stores
`(meows Rex)` in CxA; a read from CxA finds it and a read from CxD does not. `believed?`
takes a context and applies the defeats, and a read with no context reads a sentex at its
own ([A read with no reader](#a-read-with-no-reader)).

**The taxonomy's closures apply it too.** A `genl` or `genlCx` edge is held up by stored
supporters, and a scoped read of a relation asks the KB per supporter whether the reader
believes it (`res/supporter-believed?`, installed by `kb/attach-visibility!`). The presence
check the taxonomy reads first is `exc/supporter-entries`: the `except` entries and the placed
defeats, by target. A `defeat` of a supporter hides it from `genl?`, `isa?`, `genls`, a
match that climbs the hierarchy and a `transitiveInArg` claim preserved along it, at and
below the defeat's vantage, the way `believed?` of the edge answers there. Without that the
two halves would disagree about one KB from one context — `believed?` false and `ask?`
true — which is the disagreement `res/believed-at?` exists to prevent. A defeat of a
supporter stored, removed or relabelled evicts the scoped `genl` closures that can cross
the edge it reaches, and no other ([A read with no reader](#a-read-with-no-reader); `lein
perf`'s `genl-defeat-beside-defeats` and `defeat-beside-unreached-readers`). A firing's witness search alone reads the
network and the stored `except`s and no `defeat` (`tax/*network-belief*`,
`exc/except-entries`), so a placed defeat moves no firing.

The recursion that shape invites does not close. Every ancestor-set read inside the walk
goes through `tax/context-up-global`: `except-hidden-fn`, `visible-exception-index` and
the walk's reader state each name it, and the walk's fixpoint is `jtms/region-in`, which
reads justifications and no taxonomy. The one taxonomy read inside the walk is the
second-route question. A read nested in it answers its own second routes into the memo of
the read that opened the search (`exc/*routes*`), so a route question met again on one path
reads as not reaching, and the recursion ends. So a filtered `genlCx` walk asks a question the
**unfiltered** genlCx closure answers, for the same reason exception evaluation reads that
closure ([taxonomy.md](taxonomy.md), "Reads are scoped by the asking context").

`relation-filter-active?` stays the presence check in front of all of it: a KB that stores no
`except` and no `defeat` never asks the predicate at all, and one whose stored targets
support no edge of the relation being read does not either.

**The discovery reads no inherited defeat.** An inherited nogood's reasons are known-true
(a reading with a `:default` reason opposes nothing, [inherit.md](inherit.md)), so its
only `:default` member is the stored denial, which the detector reads by its sentence and
not through the reads a placed `defeat` filters. A placed inherited `defeat` therefore
hides nothing the next ask at its vantage reads.

**A defeat binds no reader below the vantage against its own view.** A reader below the
vantage that sees a denial, an edge or an `except` dissolving the clash believes what the
vantage hides: the denial places its own `defeat` of the ground at the reader, and the
membership defeat rests on that ground.

| where `(not (genl chi dog))` sits, with `(chi Kit)` and `(cat Kit)` in CxB | CxC below CxB believes `(chi Kit)` |
|---|---|
| CxC, below the vantage CxB | true |
| a CxD that CxB sees | true |

`scoped_defeat_test`'s release tests assert both rows in every arrival order, the retraction
of the denial and the `except`.

A `siblingDisjointException` exempts its pair from the separation marks only at the
readers that see it ([taxonomy.md](taxonomy.md)): written below a vantage, it takes the
vantage's membership defeat out of force there and below (`membership/exempt-at?`).

#### Vantages that disagree

A nogood can have several vantages, when the contexts that see every member have more than
one maximal element, and each placement is read with the classes its reader reads. Two
readers can defeat different members: an `except` in force at a reader that hides one
member's monotonic support lowers that member's class there, and the read re-decides the
placed nogood with that class (`exc/verdict-at-reader`).

```
CxUniverse
 ├─ CxA        (cat Rex) :default, and :monotonic through (mono_cat_src Rex)
 ├─ CxB        (dog Rex) :default, and :monotonic through (mono_dog_src Rex)
 ├─ CxHide1    (except (sentexHandle <(mono_cat_src Rex)>))
 └─ CxHide2    (except (sentexHandle <(mono_dog_src Rex)>))
CxW1  genlCx CxA, CxB, CxHide1      CxW2  genlCx CxA, CxB, CxHide2
CxZ   genlCx CxW1, CxW2
(disjoint dog cat) is visible from every context
```

Both members are `:monotonic` in the network, so the nogood is a conflict, placed as a
`contradicts` with no `defeat` at CxW1 and at CxW2. CxW1 reads `(cat Rex)` as a default and
`(dog Rex)` as monotonic, so it treats `(cat Rex)` as defeated; CxW2 reads the pair the
other way and treats `(dog Rex)` as defeated. A read from CxW1 finds `(dog Rex)` and a read
from CxW2 finds `(cat Rex)`. CxZ sees both `except`s, reads both members as defaults, and
ties: it believes both, and `(contradictions kb CxZ)` reports the pair. No reader takes a
verdict from another; each reads the placed nogood with its own classes.

`contradictions` reports a nogood whose placements defeated different members as a
dilemma with `:vantages`, the `{context handle}` map of what each placement context
decided (`clashes/read-clashes`), read with the other reports.
`(contradictions kb context)` reads the placed `contradicts` the reader believes and sees
(`clashes/contradictions-at`), and keeps a nogood whose verdict at the reader is a tie
(`exc/verdict-at-reader`) and every member of which it believes and sees, which
is the reading `believed?` gives that reader for each member. A `contradicts` rests on
every member, so a reader that does not believe a member does not see it: a dilemma one of
whose members rests on a loser the reader sees is not that reader's dilemma
(`constraint_nogood_test/a-dilemma-over-a-member-resting-on-a-loser-is-not-reported-where-the-member-is-not-believed`).

**A defeat blocks no firing.** Derivation blocking reads the stored `except`s alone
(`exc/except-closure-hidden-fn`). A conclusion resting on a member a `defeat` hides is
stored, and the read hides it at the readers where the defeat is in force. An `unknown` or
`exceptWhen` is asked at the conclusion's placement context and reads that context's
belief, and a defeat that moves posts the re-check of the rules watching the member
([naf.md](naf.md)).

#### A read with no reader

A read that names no context answers belief at the handle's own context: what
`res/believed-at?` answers for the context the sentex is stored in, with the defeats that
context sees applied and the stored `except`s not applied: the read walk at that context
(`exc/own-hidden-fn`). `in?` and `believed`, `types-of` with no context, the extent fns'
`{:believed? true}` option and `why-not` all read it. An unscoped read of a fact therefore
never believes what no context believes.

- **The unscoped closures, the flat caches and the equality partition read the
  network.** A supporter resting on a handle a placed `defeat` or an `except` hides is
  hidden from the scoped reads where that handle is hidden: the scoped closures and the
  scoped flat-cache and equality reads filter each supporter through the read walk
  (`res/supporter-believed?`). A `genl?`, `genls`, `isa?`, `disjoint?`, `has-prop?` or
  `inverse-of` with no context reads an edge or a declaration at its network label, as a
  firing's witness search does. An equality no reader believes still decides the merge,
  and the reads at the contexts that do not believe it hide what follows. A permuting or
  `reifiable_function` mark a reader does not believe spells nothing that reader reads
  ([canonicalization.md](canonicalization.md#a-mark-a-reader-does-not-believe)). The
  scoped filter is on for a relation while some supporter of it rests on a target of the
  stored `except` and `defeat` entries (`kb/supporter-reaches?`: one count read when an
  `except` or `defeat` fact names a supporter itself, the `:tax-named` family of
  [indexing.md](indexing.md#9-the-taxonomys-supporter-families); otherwise the targets'
  forward consequence closure, or a probe of the entries' functors per handle of each
  supporter's support with no target set read, whichever side is smaller), read again
  after either set of entries moves. The `genlCx` filter reads the `except`s alone: a `genlCx`
  supporter rests only on forced-monotonic sentences, which no defeat targets. While no
  more `except`s are stored than `genlCx` supporters, it walks forward from their targets;
  otherwise it probes the `except`s naming a handle of each supporter's support and reads
  no target set (`exc/genlCx-excepted?`). The walk
  finds a supporter believed where one of its justifications rests on no hidden handle, so
  a second justification shows an edge a defeat or an `except` hid, and dropping one can
  hide it again, with the edge network IN throughout. A scoped read that reads supporter
  belief is therefore held for one stretch of the change clock under its reading, and no
  write evicts one ([taxonomy.md](taxonomy.md#reads-are-scoped-by-the-asking-context)).
- **A read with no context and no reader to fan over** (`vantage/answers` with nothing to
  witness, `ask-within`) binds `exc/*unscoped-own*`, under which `hidden-fn` of a variable
  context is `exc/own-hidden-fn`. The engine's own unscoped joins bind nothing and read the
  network, verdict-free.
- **A variable context** reads jointly ([contexts.md](contexts.md)): an answer stands when
  some reader believes every fact it rests on, and post-hoc placement keeps a placement
  only where each supporter some reader can hide is believed.
- **`why-not`** answers `:defeated` for the target of a `defeat` in force at its own
  context, with the stored sentences opposing it under `:contradicted-by`, the defeats
  under `:defeats` and the nogood's grounds under `:grounds`. A sentex IN in the network
  and not believed where it is stored only because it rests on a defeated handle answers
  `:withdrawn`, with the defeats of what it rests on under `:withdrawn-by`.

`belief-status` reports the network label as `:in?` and whether its context does not
believe or see the handle as `:withdrawn?`. A backward chainer drops a rule-derived answer
that a nogood's defeat in force at its query context removes (`res/defeated-answer?`), so a
rule cannot re-derive for that reader the sentence the reader's nogood defeats. A guard
defeat removes one firing and drops no rule-derived answer.

#### The published set

A placed `defeat` moves belief with no relabel, so the touched set alone misses the
move. `settle-finish` adds what a defeat can move to the published set `preview`, the
consequence report and the change feed read, as the belief each handle has at its own context: what
the defeats stored before the write reach, and what the defeats the settle stored or
removed reach (`settle/defeat-moves`, the removed ones read off the removal record). A
defeat reaches its target and the target's forward consequence closure, and a defeat in
that closure reaches its own target in turn (`kb/defeat-reach`).

A placed `contradicts` with no `defeat` moves its members too while an `except` is stored,
since a reader whose excepts lower one member's class reads that member as defeated
(`exc/conflicts-naming`); `kb/placed-targets` names what each placed sentex moves.

**Before and after.** While a write that reports runs, every choke point that moves a
structure records the value the move replaces, once per key (`observe/*write-record*`,
derived-state row R14). The record holds the removed and replaced records and
justifications, the index postings the write moves, the network's labels, classes,
justifications and blocked and forced sets, the taxonomy's relations, declarations and
exemption inputs, the nogood candidates, and the ancestor sets each drained `genlCx` move
changes (`special/drain-moves!`). `assert`, `retract!`, `edit!` and `preview` open the
record at the outermost `with-deferred-settle`, and `settle` opens one when none is open
(`settle/write-record`). A record opens only when a sink is bound or a listener registered.

`settle-finish` reads the KB as it stood when the record opened through `kb/prior-kb`: a
copy whose stores, network and taxonomy answer a recorded key from the record and every
other key from the live store, with fresh caches. The copy is read with no record and no
pass-scoped memo bound. For each handle the report reads, `exc/own-hidden-fn` decides
whether its own context hides it, once in the KB and once in the copy. The record is
emptied once the settle has reported, so a settle inside a deferred batch reports against
the state its predecessor left.

The handles the report reads beside the region are walked forward in both KBs
(`settle/report-reach`, `kb/moved-reach`) from:

- the region and the sentexes the write stored, removed or respelled;
- the handles whose support the network moved (`jtms/moved-supports`);
- the handles a moved sentence names, and the stored facts and denials a moved
  forced-monotonic declaration reaches (`chain/declaration-reach`);
- while an exemption can apply (`exc/exemption-reads?`), the memberships of every type under
  a symbol a moved interpreted or disjointness sentence names, and the handles naming a
  term of that symbol's equality class;
- the defeat targets, `contradicts` members and nogood candidates each drained `genlCx` move
  reaches (`settle/edge-write-seeds`, `settle/edge-declaration-seeds`).

The walk is skipped when neither KB holds anything the read walk reads
(`exc/walk-reads?`). `listener-write-beside-defeats` and `verdict-published-set-write` hold
the cost of a write naming no nogood member flat beside the standing defeats. Why the
report reads a record and not a reading at the entry point:
[defenses.md](defenses.md#a-writes-report-reads-the-kb-before-it-off-a-record-of-what-it-moved).

`feed_test/every-event-is-the-diff-of-own-context-belief-in-random-worlds` compares every
event with a diff of own-context belief over the whole KB, write by write and retraction by
retraction, and `scoped_defeat_test/the-reports-of-a-write-name-what-a-scoped-defeat-moved`
holds a consequence below a vantage in `preview`, the consequence report and the feed.

#### The candidate journal

The candidates by context follow every candidate, read off what moved since their last
reading and not off every candidate.

- **The journal.** Every update of the candidate index that can move a handle into or
  out of a family's `:handles` names the handle in the same update
  (`journal/note`): the record stored or removed, and the older handles it moves, such as a
  converse partner, a determinant partner, the other members of a chain, a term's other
  memberships, and the declarations and
  members a taxonomy sync reads again. `decide/candidate?` answers whether a journaled
  handle is a candidate now, from each family's `:holds?`. The journal
  (`vaelii.impl.journal`) holds at most 16,384 handles, a rebuild restarts it, and an image
  is written without it or the taxonomy's, both of which the install restarts; a position
  the journal no longer holds is read whole.
- **The candidates by context.** `decide/synced` keeps every candidate under the context
  its record is stated in (`journal/indexed`), read again for the handles journaled since
  the index's position, and built whole where the journal does not reach back. A moved
  `genlCx` edge's placement pass reads the candidates stated in the contexts it reaches
  (`decide/handles-at`, the reach of `special/drain-context-moves!`).

A write adding one candidate therefore reads the handles it journals and what rests on
them, and no other candidate. The discovery's install still reads every inherited clash,
and journals only the members that entered or left, so a clash found again moves no reader
of the journal.
`order_independence_test/the-candidate-journal-answers-what-a-recompute-answers-over-a-random-stream`
compares the candidates and the candidates by context with a recompute after every write
of random streams over every family, once with the journal cut to three handles. `lein
perf`'s `candidate-write` holds a write adding a candidate flat in the candidates standing
elsewhere, and `reached-reader-family-read` a write completing a pair at one context flat
in the converse pairs, determinants and chains stated where that context
does not see them.

### The nogood families

Every nogood family keeps its candidates in one write-time index (`vaelii.impl.decide`),
and every family places its nogoods as conclusions
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)); no reader decides
one. The mechanism has three parts, and a family adds one row to each:

1. **A write-time candidate index.** `:nogood-candidates` holds, per family, the stored
   sentences that could be a member of one of its nogoods, recognized from the sentence's
   own arguments at the store and removal choke points (`decide/note-candidate!`). Its
   rows are a superset over every context, so a family reads the unscoped closures there
   through one map (`decide/unscoped-closures`). Under `:converse` is every ground binary
   tuple with a stored converse, found by a trie read of `(Q' b a)` under the tuple's own
   functor and under every predicate below an `anti_symmetric` mark on it or above it
   (`tuple/converse-functors`). A tuple is read only while an `anti_symmetric` or
   `asymmetric` mark stands on its functor or above it, and the mark's arrival or a
   predicate `genl` edge bringing tuples under one offers the stored tuples to the index
   again. A ground binary self tuple keeps no row: the index keeps the self tuples in a
   count trie over `[pred ctx]` ([indexing.md](indexing.md#2-the-secondary-roots)), and
   the placement reads those of the predicates under an `irreflexive` mark there, by
   context where a `genlCx` move exposes contexts (`tuple/self-tuples-in`). The index holds
   storage, not belief, so a converse arriving later, or a member reviving, finds its
   candidates without reading a tuple. `recover` offers the stored facts of the
   predicates under a tuple mark to the tuple families, owes the inert shapes whole,
   which the first settle after it refreshes off the length set (`arity/drain!`), and reads
   the membership entries of the terms the unary predicate set
   lists two predicates of and of the unary bodies stored in both polarities, and reads no
   other record; the cover pairs are no row, and a reader reads them off the index
   (`related/nogoods-holding`). The inherited family's rows are the clashes the settle's
   discovery found (`inherited/install-inherited!`).
2. **Read by the placement pass.** `chain/place-nogoods!` reads each family's
   candidates the pass moved, and a moved `genlCx` edge's reach reads the candidates
   stated there (`decide/handles-at`). The pass computes the reach only when a family
   other than the arity refresh has work, since the arity refresh reads none of it
   (`lein perf`'s `recover-over-a-context-chain`).
3. **Placed with the verdict the network's classes give.** The pass stores the
   `contradicts` and, for a unique weakest `:default` member, its `defeat` at each
   vantage, and drops the placements the current state no longer gives. A read applies
   them ([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)).

**The arity family.** The family places no nogood for a tuple. A binding is a forced-monotonic
sentence read as storage: `(arity P n)`, an exact-arity class membership, a
`variable_arity` membership or `(arityMin P m)`, read off the index family
`:arity-binding` ([indexing.md](indexing.md#the-arity-bindings)) by predicate, in every
context. A stored tuple whose length breaks its functor's length
(`arity/relation-length`, read the same at every context,
[taxonomy.md](taxonomy.md#arity)) is a member of the `:out` forced set
([The forced-monotonic set](#the-forced-monotonic-set)). The settle's refresh
(`arity/drain!`) moves the tuples of each functor whose length can have moved since the
last pass: the predicates whose binding was stored, removed or relabelled, the functors at
or below them, and the functors at or below the lower end of each `genl` edge moved since
the generation the last refresh read. The refresh reads a functor's stored lengths off
the length set the index write keeps (`reads/as-stored-shape-lengths`), and a shape's
tuples off its node in the shape trie only where the shape's answer moved, so a binding
arriving over tuples of the right length reads none of them: `lein perf`'s
`arity-binding-arrival` holds it. Register row N3 records, per functor, the lengths whose
tuples `:out` holds. A `recover` owes the row whole, and the first refresh after it
rebuilds the row from the forced set and refreshes every functor of a stored fact. The
exact lengths stored at or above a type, and its own lengths and floors, are an entry in a
weighted LRU, register row N8 ([caches.md](caches.md)), built from the type's parents'
entries and probing `[:arity-bound]` once per type it reads, so an eviction costs a
recompute and changes no answer. A functor binding nothing of its own reads the
predicates above it grouped by the exact lengths they store, the smallest group first,
and stops at the second length it reads.

A `:monotonic` membership whose type reaches an exact-arity class through `:monotonic`
`genl` edges binds through a stored class membership (`chain/sync-arity-classes!`,
[taxonomy.md](taxonomy.md#arity)). Its store path syncs it, and a record a mint, a lift or
a rewrite stores is synced at the settle's next pass (`arity/take-classes!`): `lein
perf`'s `metatype-edge-arrival` holds the cost per member flat. A `genl` edge moving in
the taxonomy, whatever sentence installs it, syncs the memberships at or below its lower
end at the settle's next pass (`arity/take-class-ends!`), and so does a relabel of a
sentence installing one (`tax/installed-edges`), since a strength change moves no edge. Two exact bindings of one
predicate, or of two predicates a `genl` edge relates, whose lengths differ are a pair:
one `contradicts` stored in CxUniverse per pair of their CxUniverse copies, justified by
the two copies, with no route and no `defeat` (`chain/sync-arity-pairs!`). The refresh
answers the predicates whose pairs the settle syncs again (`arity/pair-sets`). A predicate
with one length stored at or above it reads no closure (`arity/lengths-of`), and the sync
reads each closure it needs once: `lein perf`'s `arity-refresh-under-bound-chain` holds a
whole refresh's cost per predicate flat. A `negates` declaration whose two sides' lengths no argument list fits, or
which binds both sides to one argument, is a one-member clash placed in the declaration's
context and justified by the declaration and the bindings stating the lengths
(`chain/sync-negates-lengths!`). The settle reads a declaration again when it is stored
or relabelled (`arity/take-negates!`), and when the refresh names one of its sides among
the terms whose length can have moved (`arity/drain!`); a whole refresh reads every
stored declaration. A write moving no side's length reads no declaration
(`relation_properties_test`).

**The negation family.** A body stored in both polarities, and its members, the handles
of its stored `B` and `(not B)`, are an index family of the `IndexStore` and keep no row
in the candidate index ([indexing.md](indexing.md#the-bodies-stored-in-both-polarities)).
The index write posts it from the sentence in hand and the trie's counts before the write,
so a bulk load and single writes leave the same family. The pair is placed as a nogood
with no grounds
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)). A pair whose body is
a `genl` edge or a type membership (`(M t)`, from which a disjoint metatype reads a
separation) is a ground of the membership families, so where the pair's `defeat` hides the
ground, it hides the membership nogood placed through that ground too
([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)).

**The tuple-mark family.** A tuple under a `functional`, `functionalInArg` or
`anti_transitive` mark on its functor or above it reads, when it is stored, the stored
tuples its own arguments name (`tuple/found-for`): for each mark the tuples of the
predicates below the mark that agree with it on the determinant, every position but the
marked one, one trie read of `(P a ?v)` or one intersection of argument roots; and for
`anti_transitive` the steps sharing an argument with it. A determinant holding two
fillers is kept with its members and their contexts, and a determinant already kept
takes a new tuple with no read, so an empty or a wide determinant is read once. A
determinant member is a candidate when a member with another filler sits in a context
some context sees together with its own, so fillers no context sees together place
nothing; `lein perf`'s `functional-in-arg-empty-determinant-sweep` holds that case flat.
An `asymmetric` converse is a stored converse pair (`:converse`) read under the
`asymmetric` marks. A tuple under a side of a `negates` declaration reads, with one trie
read of its argument list under each predicate below the other side, the tuples it pairs
with, and is one nogood alone when its functor is below both sides (`::neg`,
`tuple/found-for`). A mark arriving, or a predicate `genl` edge bringing tuples under
one, offers the stored tuples beneath the marked predicate to the index again
(`special/offer-marked-existing`, `special/offer-marked-under-edge`). Which contexts see
two members together is read off the unscoped `genlCx` closure, and a `genlCx` edge
moving reads it again over the index (`tuple/sync-tuples`). `lein perf`'s
`tuple-mark-determinant-write` holds a tuple's arrival flat in the tuples of other
determinants. Each tuple nogood is placed
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)).

**The membership families.** A `disjoint` nogood is two memberships of one term whose types
a separation holds apart, a `supertype` nogood is a membership beside a denial of a strict
supertype of its type, `(dog Rex)` and `(not (animal Rex))` under `(genl dog animal)`, and
a cover nogood is a membership under a cover's whole with a denier of each part; all
three are keyed by the term. A denier of a part is a denial of the part or of a supertype
of it, or a membership of another type a declaration separates from the part: the
separation's denial `provers/DisjointnessNegationProver` answers, so `contradictions`
lists the cover `argue` reads as refuted. The denying membership is a member, and the
separation and the `genl` edges it climbs are grounds. The candidate is read over the
unscoped taxonomy (`tax/pair-separated?`, held in the closure cache under the `genl`
generation and the separation inputs), and the placement holds the separation to the
denial's soundness rule: each edge it climbs reaches at `:monotonic` from the placement,
a disjoint metatype's membership is supported at `:monotonic`, and a
`siblingDisjointException` the placement sees exempts the pair
(`chain/route-placements`, [taxonomy.md](taxonomy.md#disjointness)). A cover nogood whose
member set a `supertype` or a `disjoint` nogood holds is that one nogood, with the
cover's routes beside the edge's or the separation's. The index keeps
each term holding two memberships, or a membership and a denial, read off the term's unary
predicate set once when the second arrives and kept in step after (`membership/note-membership!`),
with each kept term's memberships and denials by type. The kept terms under a type are
read off the index, which lists each term of two unary predicates under each of them and
each term a stored denial names under its type
([indexing.md](indexing.md#the-unary-predicate-set-and-why-position-1-was-not-narrow-enough)). A term
the read finds holding denials and no membership is noted, so a further denial of it reads
nothing; `lein perf`'s `negation-load` holds a denial's arrival flat in the denials of its
term. Each kept term keeps the pairs of its types the unscoped taxonomy separates, each pair
tested when its second type arrives: a membership of a type new to the term tests that type
against the term's other types, and tests none when no separation reaches it
(`tax/separation-test`). `lein perf`'s `membership-beside-held-types` holds that arrival
flat in the term's types, and `separated-membership-beside-held-types` holds the arrival of
a type a separation reaches linear in them. A declaration moving tests again the pairs
holding a type at or below a type whose separations it moves (`tax/separation-moves`), and
a moved `genl` edge the pairs holding a type at or below its lower end
(`membership/sync-memberships`), both found through the index's kept terms by type. A
declaration arriving therefore reads no membership; `lein perf`'s
`membership-declaration-arrival` holds it flat in the memberships under the types it
separates, and `separation-beside-kept-terms` flat in the kept terms holding no type under
it. A cover nogood moves only with its membership's chain up to the
cover's whole or a denier's chain down to a part, so a cover or a `genl` edge moving places
again the kept terms with a membership beside a denial or a second type at or below the
whole of a moved cover (`tax/cover-moves`), the lower end of a moved edge, or the whole of
a cover with a part at or below one. A `genl` edge the pass relabels places them again
too, since its defeat class moves which placements read a separation's denial
(`membership/terms-under-edges`); `lein perf`'s `cover-beside-kept-denials` holds a cover's arrival flat in
the kept terms with a denial it does not reach. A `supertype` nogood moves with the
membership's chain up to the denied type, so the moved edge's lower end places it again.
A term holding a pair the unscoped taxonomy separates, a membership and a denial, or two
memberships under a stored cover, keeps its nogoods through that taxonomy (`::ngs`), a superset
of what any reader reads, and its members are candidates. Each is placed as a nogood with
its separating declarations and the `genl` edges its reading climbs as grounds; a
`supertype` nogood has the edges alone
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)). A `supertype`
nogood reads the edges' contrapositive, so it is placed only where the held type reaches
the denied type at `:monotonic` ([inference.md](inference.md#predicate-subsumption-in-matching)),
and a cover nogood's denial of a supertype of a part denies the part only where the part
reaches it at `:monotonic`.

**The reports.** `conflicts` and `contradictions` read the placed `contradicts` at the
read ([The clash reports](#the-clash-reports)): each placed nogood reports its verdict at
each context it is placed in, and a report names the most general contexts that read it
so. A nogood whose placements defeat different members is reported once, with
`:vantages`. A negation pair reports as a rebuttal: no `:kind`, and the rebuttal
priority.

**The published set.** A placed `defeat` moves belief with no relabel, and the published
set reads the move at each handle's own context ([The published set](#the-published-set)).

**The family the settle finds.** An inherited nogood is found by the settle and placed at
its vantages (`chain/place-inherited!`), beside these families'. A nogood one of whose
members rests on a loser rests on that loser through its placed sentexes, so it is hidden
where the loser's `defeat` is in force.
`reference_test/an-irreflexive-loser-leaves-no-disjoint-pair-at-its-reader-in-every-order`
holds a loser whose consequence is a `disjoint` member.

### Declarations over related types

A `disjoint` over two types one of which reaches the other through `genl` is a one-member
nogood of the declaration, and a cover naming a part that a `disjoint` separates from its
whole is a two-member nogood of the cover and the `disjoint` ([reference.md](reference.md#decisions),
decision 8). The declarations are forced `:monotonic`, so each is a hard clash: `conflicts`
lists it, every member stays believed, and no belief moves.

```
(genl dogw animalw)  (disjoint dogw animalw)  (dogw Fido)          ; {(disjoint dogw animalw)}
(covering animalw dogw catw)  (disjoint dogw animalw)              ; {(covering …) (disjoint …)}
```

A cover states the edge from each part to its whole, so the `disjoint` of the second line
is over related types too and reports its one-member clash beside the cover's. Both are
found from the declarations' own arguments, which the argument trie reads: the
`disjoint`s naming a type at argument 1 or 2, and the `covering`, `separating` and
`partition` facts naming a whole at argument 1. The candidate index keeps the `disjoint`s
whose arguments are related over the unscoped closure (`:related-dj`), read again for the
declarations naming a type at or below the lower end of an edge that moved
(`tax/moves-since`). A cover pair, a cover beside a `disjoint` separating its whole from a
part, is read from the store when a placement asks for it, and the store and removal
choke points queue its members when either side arrives or leaves. Each is placed as a nogood
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)), a `disjoint` with
the `genl` edges relating its arguments as grounds and a cover pair with none.

An `(orthogonal a b)` states that the two types are not disjoint and that neither is a
`genl` of the other. It exempts nothing ([taxonomy.md](taxonomy.md#disjointness)), so it
is the same family's one-member clash, of the `orthogonal` declaration, wherever a reader
reads a `genl` edge between the two, the two are one type, or a separation of the two or
of two supertypes that no `siblingDisjointException` the reader sees exempts. A stored
`(siblingDisjointException a b)` states the orthogonal it entails through
`(genl siblingDisjointException orthogonal)`, and is the member of that clash.

```
(genl betaw alphaw)  (orthogonal alphaw betaw)                              ; {(orthogonal …)}
(disjoint upperw otherw)  (genl subw upperw)  (genl subv otherw)  (orthogonal subw subv)
                                                                            ; {(orthogonal …)}
(disjoint alphaw betaw)  (orthogonal alphaw betaw)                          ; {(orthogonal …)}
(sibling_disjoint pw)  (genl alphaw pw)  (genl betaw pw)  (orthogonal alphaw betaw)
                                                                            ; {(orthogonal …)}
  + (siblingDisjointException alphaw betaw)                                 ; no clash: exempt
(disjoint alphaw betaw)  (siblingDisjointException alphaw betaw)            ; {(siblingDisjointException …)}
```

The declaration is forced-monotonic, as `disjoint` is, so it is never the
loser of its nogood at any strength: the clash is a hard one `conflicts` lists, with the separating
declarations under `:grounds`, every member left believed, and the pair reading both
statuses (`:inconsistent`). The stored facts whose functor the unscoped `genl` closure
places under `orthogonal` are read off those functors' extents and argument tries, and
the candidate index keeps those some reader can read contradicted — over the
unscoped `genl` closure, or separated by `disjointness-test` with no exemption read
(`:related-orth`). One is read when it is stored, again with the `disjoint`s when an edge
moves an argument's ancestor set (`tax/moves-since`) or moves its functor under or out of
`orthogonal`, and again when the settle relabels a separation declaration over a type at
or above an argument (`related/reread-separated!`).
A `siblingDisjointException` stored or removed places again the contradicted ones with an
argument at or below its own pair, since it moves which of their routes are exempted. Each
is placed as a nogood once per route: the `genl` edges relating its pair, and the
declarations and edges of each separation of its pair that no exception its placement
reads exempts, are the grounds of one route each, with the predicate `genl` edge for an
exception. A reader whose ancestor set states an exception
exempting every separation that convicts the declaration does not believe an inherited
placement of it (`related/exempt-at?`), as for a membership nogood
([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)).
`reference_test/a-disjoint-over-related-types-is-a-hard-clash-of-the-declaration-in-every-order`
holds the `disjoint` over related types in every arrival order, and `orthogonal_test` holds
the `orthogonal` clash of each route in both arrival orders of the declaration and what
contradicts it.

### There is no second axis

Defeat-class is the only axis, and a default/default clash it cannot separate is reported
as a dilemma. The engine builds no specificity heuristic (a score from the size of a
type's `genl` up-closure):
[why a genl-derived ordering is inference about the knowledge rather than from
it](defenses.md#there-is-no-second-axis).

### Definitional constraints on the derivation path

arg types, disjointness and functionality hold of *derived* content as much as of
asserted content. A rule that concludes `(cat Rex)` where `(dog Rex)` is believed and
the two are declared disjoint has concluded something the KB says cannot be, so a check
that runs on only one path lets a rule produce what `assert` refuses.

`chain/place-conclusion` runs the same three checks `assert` does, and **does not
throw**: chaining is a fixpoint and cannot abort halfway through one without making
the resulting belief set depend on which rule fired first, and the engine's stance is
that contradictions are soft. A failing conclusion is *dropped* — no sentex, no
justification, nothing believed — logged at `:warn`, and recorded in
`(core/violations kb)` as `{:violation <kind> :sentence :context :rule :detail}`, the
kind naming which check refused (`:arg-type`, `:arg-genl`, `:inter-arg-type` and the rest
of the argument-constraint family). A disjointness or functionality clash is placed and
arbitrated rather than dropped ([Which entry point the content came
through](#which-entry-point-the-content-came-through)). An argument-constraint drop convicts on a type
the taxonomy separates from the declared one, so it is also remembered and re-asked once a
`genl` or `genlCx` edge, a separation (`tax/separation-inputs`), or a membership of the
convicted term stored or removed can have lifted it; placed then, its ledger entry is
withdrawn ([exceptions.md](exceptions.md), "A refused firing is remembered as bindings"). Two more kinds ride the same path: a completed firing
with **no placement context** is recorded as `:no-placement`, and a *derived*
`genl`/`genlCx` edge that would close a cycle through negation is dropped and recorded as
`:not-stratified`. A rule a **generator** minted and the rule checks refuse is dropped
the same way, under whichever refusal type the check threw. A conclusion naming a
reifiable application that has no constant yet is checked before the constant is minted,
so a dropped conclusion mints nothing, and a mint that refuses drops its conclusion as
`:mint-refused`, the refusal's own type under `:refusal` ([nat.md](nat.md), "Derivation
path").

One kind on this path drops nothing, and reports instead: `:non-confluent` is two
schematic equations disagreeing about a shared term.

`:context-edge-exposure-truncated` and `:genl-edge-revival-truncated` come from the merge
sweeps in `special` and in the settle, bounded by `tax/*exposure-instance-budget*`, and
nothing re-examines a merge past either cut ([equality.md](equality.md)).

The kinds are not only this path's. An aggregate prover that cannot reduce an extent
files `:aggregate`; the qualitative and metric-temporal networks file
`:qualitative-inconsistency`, `:metric-temporal-mixed-dimensions` and
`:metric-temporal-inconsistency` when a context's constraints cannot be satisfied; and
the sign arithmetic files `:sign-inconsistency` when they leave a quantity with no
possible sign at all. Each of those is a report and drops no conclusion. The full list,
kind by kind with the `:detail` keys each carries, is the set of tables in `core/violations`' docstring,
and `violation_kinds_test` fails on a kind the engine files with no row there, on a row
naming a kind nothing files, and on a row whose `:detail` keys are not the ones the
entry builds.

`(core/violations kb)` reads an **accumulating** ledger, not a per-run snapshot. Each
ledger entry carries the run id from `(core/chain-stats kb)`, the ledger is capped at the
newest 1000 entries, and only `(core/clear-violations! kb)` empties it, so a bulk load's
drops survive the next assert. The `:forced-conclusion` entries follow the ledger's and
are read off the stored firings, so neither the cap nor `clear-violations!` removes one.

The checks run only when the conclusion is **new** to its context. Re-deriving a
sentence already stored there adds a justification, not content — whatever it says was
admissible when it was first placed — so a second derivation cannot introduce a
violation that was not already there. `checks/args-problem` reads the memberships of
every constrained argument, a posting read, a record fetch and a belief test per type the
term holds, and forward chaining re-derives the same conclusion on every round of every
defaults pass, so a check per firing would repeat that read every round.

A conclusion is dropped only for a violation with **no opposing sentex**: an argument
constraint, a malformed special predicate, an unstratified derived edge. So
`violations` is the ledger of what cannot be represented, and a contested conclusion is
found in `contradictions` or `conflicts` instead.

### The clash reports

Contradictions never fail a settle. A conflict is a nogood whose weakest members are all
`:monotonic`, and a dilemma one whose shared minimum is defeasible; `conflicts` and
`contradictions` return them as reports.

`(contradicts X Y)` over the member sentences is the **report form** the reports compose.
Every family stores its nogoods as `(contradicts (sentexHandle h) …)` naming the members
by handle ([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)), so
`(sentexes-matching kb '(contradicts ?a ?b) '?ctx)` holds those
(`constraint_nogood_test`), and every report is read off one of them.

**A verdict lives exactly as long as its grounds do.** What makes two sentexes a pair is
the separation or the functionality the KB declares, and a known-true denial of it defeats
it: the pair stops being a pair, and the loser is believed again at every context that
reads the denial, whether the pair had been decided or stood as a dilemma. A membership
reported `:defeated` with an empty `:contradicted-by` would be a verdict that outlived its
grounds. A placed nogood holds this through its justification: its grounds are
antecedents, so a ground leaving takes the placed sentexes OUT, and a ground hidden at a
reader hides them there
([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)).

`conflicts` and `contradictions` report the **same entry shape**, down to `:kind` and
every side's justifications (`clashes/clash-report`):

```clojure
{:nogood #{h1 h2} :handles [h1 h2] :priority int :kind kw-or-nil
 :sentence (contradicts X Y)
 :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]
 :grounds [{:handle :sentence :context} ...]
 :inherited {:sentence :context :claim handle :via [handle …]}   ; :kind :inherited only
 :vantages {vantage handle}}                                      ; a vantage disagreement only
```

`:kind` is the violation `:type` a definitional clash convicted on
(`checks/arbitrable-kinds`), `:inherited` for a preserving clash, and nil for a rebuttal.
`:inherited` is the one part of a report that is **not** a stored sentex, so it cannot be
a side: the claim nobody wrote, the context it was read in, the handle of the sentex it
was inherited from, and the handles that licensed carrying it there. Each of those
handles is also a member, so the sides carry their justifications and `why` explains the
reach. The two readings differ in *why* the set was left standing, not in what a caller
needs in order to act on it.

**`:grounds` names the declarations a definitional clash convicts through**, in content
order: the believed supporters of the flat-cache entries the conviction reads, among
those a vantage of the report sees (`clashes/clash-grounds`). For two memberships those
are the separating `disjoint` declarations, the disjoint metatype and its two
memberships, the `sibling_disjoint` parent and the separating cover; for tuples, the
`functional`, `functionalInArg`, `asymmetric` or `anti_transitive` mark; for a refuted
cover, the cover; for an `:arity` conflict, the bindings stating the length its tuple
breaks (`clashes/inert-binding`). No `genl` edge
is named, so the list is bounded by the declarations and not by the paths between them,
and it is the same in every arrival order. An edge an argument declaration minted is named
by the sentence it was minted from: `(disjoint gladdens saddens)` mints
`(genl gladdens thing)` through `(genlArg disjoint 1 thing)`, and an `:arity` conflict
whose length is inherited through that edge names the `disjoint`
([taxonomy.md](taxonomy.md#disjointness)). A rebuttal and an `:inherited` clash have none:
their reasons are members. `why-not` of a sentex a placed `defeat` takes OUT names its
nogood's grounds under `:grounds`. Retracting every ground
dissolves the clash. The grounds are read when a report is read, one supporter read per
declaration, and no reading is kept ([What a reading reads](#what-a-reading-reads)), since
a declaration can move under a report whose members did not.

**`:sides` and `:handles` name the members in content order, and so does the list of
reports around them**
([why](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle)). The sides
are ordered by sentence, then context, compared by `nm/compare-form`. Those two keys are
total, since sentence-plus-context identifies a sentex, so no handle enters the key;
`report_order_test` reads that line of `clash-report` and fails on a handle in it. Each
side's justifications follow `core/supporting-justifications`' content order.

**The ordering is the read's.** `clashes/read-clashes` builds the two vectors in the
order the `contradicts` extent answers in, and `clashes/ranked` orders a reading when it is
asked for; `conflicts`, `contradictions` and the preview's standing filter each call it,
and any further reader of `clashes/conflicts-of` or `clashes/contradictions-of` owes the
same call ([why the reading is sorted per read](defenses.md#a-clash-reading-is-sorted-at-the-read-not-on-the-settle-path)).
One `read-clashes` call builds both readings from one pass over the stored `contradicts`. The
labeling solver re-sorts the dilemmas by priority then content for itself
(`solve_test/the-result-does-not-depend-on-the-order-the-nogoods-arrive-in`).

### A nogood placed as a conclusion

`chain/place-nogood!` places a nogood the way a firing places its conclusion. Given the
member handles and the ground handles the detection read, it reads the verdict
(`decide/verdict` over the members' classes in the network) and stores, at each maximal
context that sees the contexts the members and grounds are stated in and where no except
hides one of them (the placement a firing's conclusion takes, which reads the stored
`except`s and no `defeat`):

| verdict | stored |
|---|---|
| a unique weakest member `L` | `(contradicts …)` and `(defeat (sentexHandle L))` |
| a `:default` minimum shared by several (dilemma) | `(contradicts …)` |
| no defeasible member outside the forced-monotonic set (conflict) | `(contradicts …)` |

`(contradicts (sentexHandle h1) (sentexHandle h2) …)` names the members in content order
(sentence, then context), so two detections of one nogood store one sentex. Each placed
sentex is justified under the informant `nogood` at `:default` by the members, the grounds
and the `genlCx` edges the placement sees them over (`visibility-support`, as a firing
names them), so retracting any of them takes it OUT with no release code, and `why` names
them. A `defeat` is read off the trie by its target (`reads/as-stored-naming`).

The placed justifications are a function of the current state. A call drops each
justification the nogood placed earlier whose context, sentence or edges the state no
longer gives, and the sweep collects a placed sentex it leaves unsupported. Each family
places its nogoods again when a `genlCx` edge moves where it reaches (below), so the edge
arriving first and last store the same placed sentexes (`placed_nogood_test`).

**A nogood with a superseded member keeps its placement.** The negation, membership,
related-types and tuple families detect their nogoods over the network's IN label,
which holds a spelling an equality merge superseded (`jtms/network-in?`), and none of them
removes a placement when a member is superseded. So a nogood over premise members places
the same sentexes whether it was detected before the merge or after it, and the restated
spellings form a second nogood beside it. A defeat placed over the superseded spelling
hides what a restatement derived from it, in every arrival order of the merge
(`negation_test`, `constraint_nogood_test`). The clash reports leave out a `contradicts`
naming a superseded member (`clashes/placed-verdicts`), because the restated spellings'
`contradicts` reports the same clash.

A superseded datum does not fire, and the settle withdraws a firing made over it before
the merge ([The other half](#the-other-half-a-spelling-an-un-merge-gives-back)), so a
member derived over a superseded spelling is stored in no arrival order unless the
superseding merge rests on it. A twin restated under an earlier representative can still
exist in one order only: `(sameAs CI4 CI1)` restates `(plant CI4)` as `(plant CI1)`, and a
later `(sameAs CI0 CI1)` elects `CI0` and supersedes that twin, which a KB given both
merges first never stores. A nogood over such a member is placed in that order alone.
Belief and the reports still agree across orders, because every context that believes the
merge reads the representative's spelling, and a context that does not believe it
restates the spellings it reads for itself. Only the placed sentexes over the superseded
member differ.
`clash_oracle_test/randomized-streams-read-as-their-writes-loaded-from-scratch` compares
belief and the reports for a superseded member, not the stored set, and
`constraint_nogood_test/a-context-that-excepts-the-merge-reads-the-superseded-spelling-alike-in-both-orders`
holds a context below an excepted merge.

The inherited family is placed outside `place-nogoods!` and reads its claims through
`res/matches-visible`, which drops a superseded spelling. So an inherited clash over a
superseded member is not placed, and loses a placement it held before the merge. That
loss moves no belief: the settle withdraws the firing over the superseded denial at the
merge, and the clash over the restated spelling hides the representative's own firings,
in every arrival order (`inherited_clash_test`).

**A defeat is applied at read time, and sweeps nothing.** The network keeps the loser
and every consequence of it IN; `chain` reads no `defeat`. A read at a context `C` asks
`exc/defeat-hidden-fn`, which walks the asked handle's justification ancestors, forces
OUT each one a defeat in force at `C` names, and reads the handle's label with
`jtms/region-in` over that support. At a reader whose ancestor set states no except and
no defeat reaching a statement of a permuting or `reifiable_function` mark
(`exc/mark-hazard?`), on a KB that stores no forced-monotonic literal beside its denial
(`exc/yielding-reads?`), the walk stops at a `:monotonic` handle, in a belief read and a
visibility read alike. `mark-hazard?` reads the smaller side by index counts: the defeats
stated in contexts the reader sees, each target walked up its dependents to a mark
statement, or the mark statements, each walked down its support. The marks are read from
every context, since a mark the reader does not see still sorts the rows it reads. The answer reads stored content and justifications alone, so it is held per
ancestor set for one stretch of the change clock, which every write moves: a check that
asks the visibility of each supporter it reads walks the defeats once. Apart from such a denial, a defeat hides only a `:default` handle, only an except lowers a
class, and only a `respell` row takes no class from a handle it rests on. At such a reader,
when no placement can be exempt there either, the walk reads the `defeat` extent's
contexts the reader sees before any support handle, and answers from the network label
when no defeat is stated in one (`exc/region-at`). A placement can be exempt at a reader
when a `(contradicts …)` is stated in a context the reader sees, and a
`siblingDisjointException` or an equality relation is stated in one too
(`exc/exempting-at?`); each of these is read off its
predicate extent by context ([indexing.md](indexing.md)). Each read
builds its own memo and keeps nothing past the predicate it returns, so nothing about a
reader is kept between reads and nothing needs invalidating. A read costs the support of
the handle it asks and is flat in the standing defeats and excepts outside that support:
`lein perf`'s `read-below-vantage`, `read-beside-unseen-defeats`,
`hidden-check-beside-excepts` and `decided-warm-read` hold it.
`default-chain-beside-many-unseen-defeats`, `default-chain-beside-unseen-contradicts`, `default-chain-beside-unseen-arity-candidates`
and `monotonic-chain-beside-seen-defeats` hold a read flat in the depth of the derivation
it asks, and `monotonic-read-beside-marks` holds one flat in the permuting marks. A
justification resting on a hidden witness edge stands where the reader reaches the path's
ends another way (`exc/rerouted`, [Where the layer stops](#where-the-layer-stops)). Belief
and visibility stay apart: `exc/belief-hidden-fn` (read
by `res/believed-at?`, the levels and `belief-status`) forces the defeats alone, and
`exc/hidden-fn` forces the excepts in force at `C` beside them. A defeat is in force at
`C` while all of these hold:

- it is IN, stated in a context `C` sees, and no `except` in force at `C` hides it;
- for one of its `nogood` justifications, `decide/verdict` over the members of the nogood
  that justification places (the `contradicts` in the defeat's context with the same
  antecedents) names its target, with the classes `C` reads: the network's, or, where an
  except in force at `C` reaches the members' support, the classes that support carries
  with the except targets forced OUT (`jtms/classes-in-region`);
- the defeat is believed and seen at `C` through such a justification, its other
  justifications read as invalid.

Two nogoods with one loser in one context, or a nogood and a guard over one conclusion,
store one `defeat` with one justification each, and the read takes each justification
apart: a reader that excepts one nogood's winner or ground still reads the other nogood's
conviction, and a `guard` justification never holds a nogood's defeat in force
(`scoped_defeat_test`, `naf_test`). A placed conflict is read the same way, through its
`nogood` justifications alone.

**The exemption.** A placed sentex rests on the loser it hides, so the walk would remove
it at every reader the defeat reaches. For a placed nogood's own justifications the loser
is read at its label when only a `defeat` hides it (`exc/placed-belief-only`, beside the
reader's copy that `exc/belief-only-antecedent` reads at its label). An except of the
loser, or of the winner, a ground or the defeat, takes the defeat out of force below the
except (`placed_nogood_test`).

**A justification's verdict at a reader.** The walk reads each justification of a handle
in its support at the reader as `jtms/region-in` reads it, and `exc/verdict-reader`
returns that reading per justification beside the handle's belief, one of `:supports`,
`:antecedent-out`, `:blocked` (the network's `exceptWhen` set), `:void` (the network's, or
the reader's forced-monotonic reading), `:guard` (a guard defeat in force there covers it,
[naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)) and `:exempt` (a placement
the reader exempts). A handle IN, named by no defeat or conflict in force at the reader,
is believed there exactly when it is a premise or one of its
justifications reads `:supports`. `core/justification-verdicts` is the public read; `why`
puts the verdict at each node's own context on its `:support` entries, `why-not` on its
`:support`, and the browser's proof pages draw it. One reader keeps one reader state per
context, so every verdict of one tree or page breaks a defeat cycle alike. The read
streams of `order_independence_test`, `scoped_defeat_test`, `inherited_clash_oracle_test`
and `genlcx_move_oracle_test` check the reading against belief at every step
(`test-util/verdict-violations`).

**A pass's reader states.** A pass that reads many handles between its own writes binds
`exc/*reader-states*` (`exc/with-reader-states`): the settle, the withheld-mint release
and the argument-hold refresh. It keeps each context's reader state while the change clock
stands, and the state's frame (`exc/reader-frame`) across writes that move nothing the
frame reads. A frame reads the stored facts of the defeat, except, conflict, sibling
exception, equality and forced-monotonic declaration functors and the stored rules, which
`exc/note-stored!` counts at each index write; the `genlCx` closure and the taxonomy's
forced-monotonic sets, which `frame-inputs` compares; and the labels of the stored excepts
and declarations, which it reads again for the watched handles the touched sets record
(`jtms/touched-since`). A defeat naming a declaration makes the frame read belief beyond
these, so while one is stored a frame lasts one clock value. `yielding-reads?` is kept
apart: a forced-monotonic fact leaving makes it read whole, and one stored makes it ask
that fact's functor alone (`exc/held-yield`). A release of n withheld mints that each read
belief through the walk builds one frame where it built one per check (`perf`'s
`release-beside-forced-declarations`), and every state a pass reads equals the one a fresh
build answers
(`placed_nogood_test/every-reader-state-a-pass-reads-is-the-one-a-fresh-read-builds`).

A defeat stored, removed or relabelled posts the re-check of its target's sentence
(`special/recheck-defeat-target`), as a store of that sentence does, and so does an `except`
arriving or leaving that can take a defeat in or out of force: an except of the defeat, of
a handle it rests on through any chain, or of its target (`special/recheck-except`). While
a watched rule is stored, the settle pass that stores or relabels a defeat also posts the
sentence of each handle resting on the target and re-chains the rules watching them, so a
guard watching the target or a consequence of it is decided again. A defeat among those
handles moves in force with the target, so its own target and that target's consequences
are posted too (`kb/defeat-reach`).

**A guard defeat** is the second source of `defeat`: a firing whose `exceptWhen` or
`unknown` holds below its placement stores `(defeat (sentexHandle F))` for its conclusion
under the informant `guard` (`chain/place-guard-defeats!`). It removes the one firing it
guards and not the sentence: the walk drops each justification of F that a guard defeat in
force at the reader covers, and F stays believed through any other justification
([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)). A guard defeat reads F
at its label, as the exemption reads a nogood's loser. A guard defeat is in force at a
reader where it is IN, no except in force there hides it, and the blockers of one of its
`guard` justifications are believed and seen there (`exc/guard-seen-fn`). The force read
does not read F or the guarded firing's rule and antecedents: where one of them is not
believed, the firing is void at the reader and dropping it moves nothing. A nogood defeat
of a firing antecedent therefore forms no cycle with the guard defeat
(`placed_nogood_test/a-nogood-loser-a-guarded-firing-rests-on-is-hidden-in-every-order`).
The n guard defeats of one firing are each read once per read of F, not once per order of
the other n − 1 (`lein perf`'s `guard-defeats-at-a-reader`).

**A conflict a reader's excepts lower.** A placed nogood whose members are all
`:monotonic` in the network stores `(contradicts …)` and no `defeat`. At a reader where an
except in force lowers a member's class, the read re-reads the members' classes over their
support, past a premise to the other justifications that decide its class, with the
except targets forced OUT (`exc/verdict-at-reader`), and treats a unique weakest member as
defeated there (`exc/conflicts-naming`): two placements of one conflict read by readers that
except different supports defeat different members, and a reader below both reads the tie
its own excepts leave (`scoped_defeat_test`). A defeat's verdict is read the same way, so a
defeat whose verdict does not hold at a reader is not in force there.

**The negation family places its pairs** (`chain/place-negations!`, once a settle pass).
The pass reads one count first, the number of bodies stored in both polarities
(`reads/stores-opposed?`), and places nothing when it is 0. A pair is placed when both
members are IN in the network, over the bodies with a member the pass relabelled (a stored member is
among them), the bodies whose placed `contradicts` the pass relabelled or removed
(`negation/take-moved!`), and the bodies with a member stated in a context a context at
or below a moved `genlCx` edge's lower end sees and its upper end does not (the `:below`
of the pass's moves, [contexts.md](contexts.md#one-context-move); why that reach is enough
is in the next paragraph). That read is the
family's members by context, `[:opposed-in ctx]`, one leaf per context the edge exposes,
so its cost does not grow with the opposed bodies the edge does not reach (`perf`'s
`genl-cx-edge-beside-opposed`). The first pass after `recover` places every pair
(`decide/take-edge-cursor!`). A pair
reached through that last set alone compares only its placements in the contexts at or below
the lower end (the moves' `:under`), the only contexts whose ancestor sets the move
changed, and reads them by context (`kb/find-sentex-handle` on the `contradicts` and each
`defeat`), so the edge's cost per pair does not grow with the pair's other placements
(`perf`'s `context-edge-beside-placements`). A placement a pass creates is not read as
relabelled by the next pass, so a settle places each pair once. A `genlCx` edge removed or gone OUT takes the
placements it witnessed with it, and the pair is placed at its common descendants as they
stand, so the edge arriving and leaving holds what the KB without it holds
(`negation_test`). The membership, related-types and tuple families read the same
way (`chain/place-sets!`): a nogood or a placed member set reached only through the
moves' reach compares its placements in `:under`, and finds its stale placements from the
`contradicts` stated in `:under` while those are fewer than its members' term postings
(`perf`'s `context-edge-beside-membership-placements`, `-related-` and
`-tuple-placements`).

**The membership and related-types families place their nogoods** in the same pass
(`chain/place-memberships!`, `chain/place-related!`). A nogood's routes are each way the
unscoped taxonomy convicts it (`tax/separation-routes`, `membership/routes`,
`related/routes`): the flat-cache keys of a separation or a cover, and the `genl`
subsumptions it climbs. For each route and each choice of one believed supporter per key,
the nogood is placed where a firing over the members, those supporters and those
subsumptions would be (`chain/placements-over`, the placement a subsumed firing takes:
a premise except hiding a member or ground removes the placement at and below its
context, and a `defeat` is not read), justified by the members, the supporters, the `genl` edges of
one path and the `genlCx` edges the placement sees them over. Each route places independently, so retracting one
separation leaves the placements another gives. A placement that reads a
`siblingDisjointException` exempting a mark route's separated pair is left out, and a
defeat of two memberships is not in force at a reader whose ancestor set states an
exception that removes the separation
there (`membership/exempt-at?`). Neither family's inherited `contradicts` or `defeat` is
believed at such a reader through that nogood: the read walk reads the nogood's
justifications as invalid there (`exc/exempt-justifications`, `decide/exempt-at?`). A
family re-places a nogood whose index rows moved
(`membership/take-moved!`, `related/take-moved!`), whose member or placed `contradicts` the
pass relabelled, whose types lie under a separation or cover declaration the pass
relabelled (`membership/terms-under`), or that a moved `genlCx` edge can give or take a
placement. A placement the edge moves lies at or below its lower end, and is the most
general common descendant of a route only when one of the route's ingredients is stated in
a context a context at or below the lower end sees and the upper end does not: otherwise
the upper end is a common descendant above it. So the edge reaches the candidates stated
in those contexts, and the nogoods over the types below a `genl` edge or a declaration
stated there (the moves' `:below`); `lein perf`'s
`context-edge-beside-membership-nogoods` holds an edge flat in the nogoods it does not
reach.
The pass reads the `genl` edges and declarations stated in the moves' `:below` once for
the membership, related-types and tuple families, off the postings of the functors that
state one (`chain/reach-grounds`, `tax/grounds-stated-in`), so the other facts stated in
those contexts are not read; `lein perf`'s `context-edge-beside-stated-facts` holds an
edge flat in them.
A nogood the index no longer holds has its placements removed.

**The tuple family places its nogoods** in the same pass (`chain/place-tuples!`). A
nogood's routes are the marks that convict it over the unscoped taxonomy
(`tuple/routes`): each predicate carrying the family's mark at or above every member's
functor, the mark's flat-cache key, and the `genl` subsumption from each functor to it. A
self tuple reads the `irreflexive` marks, a chain the `anti_transitive` ones, a converse
pair the `asymmetric` ones and the `anti_symmetric` ones, and a determinant pair the
determinant's own `functional` and `functionalInArg` marks. A pair that merges (two
symbols, both members `:monotonic`; reference.md decision 6) gives no route. Each route
is placed as a membership route is.

One read at the reader removes a placed tuple nogood there, and it is the read of the walk
that is not a verdict (`decide/exempt-at?`, read through the reader's own belief of each
handle): two symbol fillers of a determinant pair that the equality edges the reader sees
and believes make one class (`tuple/exempt-at?`). The family re-places a nogood whose
index rows moved (`tuple/take-moved!`; a tuple joining or leaving a determinant queues
itself and not its partners, whose nogoods with each other do not move, and a tuple
placement that leaves with a departed member queues nothing), whose member, placed
`contradicts`, mark or `genl` edge the pass relabelled, or that a moved `genlCx` edge can
give or take a placement: a candidate stated in its `:below`, or a mark or `genl` edge
stated there.

**The inherited family places its nogoods** first in each pass (`chain/place-inherited!`):
each clash whose memo entry was asked again is placed at its vantages, justified by its
members and the `genlCx` edges each vantage sees them over, and the placements of a member
set no longer found are removed. A carried entry keeps its placements.

**A `recover` places the nogoods its store does not hold.** The rebuild's settle places
the inherited clashes its discovery finds, since that discovery asks every stored claim
with nothing carried. It stands aside from the negation, membership, related-types, tuple
and arity families, and the rebuilt candidate index queues every standing nogood, which
one closing settle places (`chain/placement-queued?`). The same settle refreshes every
arity shape and stores the class memberships a records-only store holds no justification
for (`chain/resync-arity-classes!`). A store written with no belief, a
records-only import among them, believes after the recover what it believes after its
first write (`negation_test`, `inherited_clash_test`), and that write places nothing
(`perf`'s `first-write-after-recover`). Over a store holding its placements, each
placement finds its justification stored and neither settle writes it again.

### Why a read runs no rounds

Detection and placement read the network, which a `defeat` never changes, so no verdict
reads another verdict. A placed sentex rests on everything its verdict read: the members,
the grounds and the witness edges. A ground that another nogood defeats is hidden by that
nogood's `defeat`, and the walk then hides every placed sentex resting on it, at the
contexts where the ground is hidden. The dependency is in the justification and needs no
ordering.

**A defeat lowers a class only through a `respell` row.** A defeat is in force only while
the verdict at the reader names its target, which is then `:default`. Everything resting
on a `:default` handle is capped at `:default`
([Strength propagates](#strength-propagates-from-the-antecedents)), and a guarded firing
is `:default`. A `respell` justification is the one exception: it takes the class of the
as-written row, and the marks it rests on cap nothing. A defeat of a mark therefore hides a
`:monotonic` `respell` row at the readers it is in force at, with what rests on the row
alone, and those handles lose that class there. A premise `except` lowers a class too.
The read re-decides the nogoods whose members either reaches in one pass ("A conflict a
reader's excepts lower" above): the verdict at a reader forces OUT the targets of the
excepts in force there and of the defeats in force there that reach a mark a `respell`
justification in the members' support rests on (`exc/mark-defeated`), and reads the
classes the support carries then. The pass reads a mark's defeat, whose own members rest
on no `respell` row unless the mark is derived from a respelled fact. That case is a
defeat-dependency cycle ([A defeat-dependency cycle](#a-defeat-dependency-cycle)).

**Without a rule-derived ground or a guard, a defeat rests on at most one other.** The
forced-monotonic set keeps the defeat-dependency graph two deep:

1. In a decided nogood every member but the loser is `:monotonic`, and a defeat hides a
   `:monotonic` handle only through a `respell` row, so a defeat loses force through
   another only by way of a ground or of a mark's defeat.
2. Every ground is forced-monotonic except a `genl` edge between types, and
   only the membership family takes one for a ground; `genlCx` witness edges are forced-monotonic.
3. A stated type `genl` edge loses only in a nogood where it is a member: a negation pair or
   an inherited nogood, neither of which has a ground that can lose.

`placed_nogood_test` holds both two-deep shapes in every arrival order. Two sources go
past them, and the next section describes the cycle they make.

### A defeat-dependency cycle

A rule-derived `genl` edge between types is `:default` and rests on what derived it, so a
membership nogood grounded on it rests on that fact. A guard defeat rests on its blocker,
which can be a nogood's loser. Either lets a defeat rest on itself through other defeats:

```
CxA  (disjoint dog cat) M   (disjoint bird fish) M   (poodle Rex) M   (sparrow Tweety) M
     (dog_breed poodle) M   (bird_breed sparrow) M
     L1 = (cat Rex) :default        L2 = (fish Tweety) :default
     (fish ?x) & (dog_breed ?t) => (genl ?t dog)    G1 = (genl poodle dog), from L2
     (cat ?x) & (bird_breed ?t) => (genl ?t bird)   G2 = (genl sparrow bird), from L1
D1 defeats L1 and rests on G1; D2 defeats L2 and rests on G2
```

D1 in force hides L1, which hides G2 and takes D2 out of force; D2 in force does the
mirror. Both readings are consistent, and nothing in the sentences prefers one. The walk
breaks the cycle in content order (design ruling 18). It keeps each defeat it reads open
(`exc/in-force-once`). A defeat met again while open answers false, and a value that met a
defeat open below its own is provisional and is not kept. The defeats left provisional when
the first of them closes form the cycle, and `exc/close-cycle` orders them by the handle
each removes (`nm/compare-form` on sentence, then context). A read of a member holds the
members removing another loser at an assignment's values. A cycle of at most eight members
reads every assignment, each member once, and takes the first in content order, in force
first, that every member reads as its own value, so a cycle with two consistent readings
takes the content order. One enumeration reads 2^m assignments of m member reads each. A
defeat a read opens that no member has read yet and that rests on a member joins the
members, and the enumeration starts again, so each defeat that joins costs another
enumeration. A member's read keeps in the read's memo every value that read no held
member, the values of a cycle closed inside that read among them, and the reads after it
take those values from the memo. A cycle nested in a member's read that rests on no
member is therefore closed once per read. In the test's d nested rings of m members the
reads are at most d · m · (2^m + 3m + 2)
(`placed_nogood_test/a-cycle-nested-in-a-members-read-is-closed-once-per-read`). Each
ring's enumeration reads 2^m · m, and its other reads number at most m · (m + 1). A ring
of odd m has no consistent assignment, so its passes add at most (2m + 1) · m. Closing
each inner ring again under every assignment of the rings around it would multiply the
enumerations instead. Because
every assignment is read, the members and the reading are the same whichever defeat the
read entered at and whichever order the defeats are asked in
(`placed_nogood_test/a-cycle-reads-its-first-consistent-assignment-from-every-entry-and-order`).
A read that meets a defeat open at an index below the cycle's own leaves the members to
the frame that owns that defeat, which closes them with it
(`placed_nogood_test/a-cycle-resting-on-an-outer-open-defeat-is-closed-with-it-from-every-entry`).
A cycle with no consistent assignment, or of more than eight members, starts every member
out of force, and a pass reads each member in content order at the current values; the
passes stop at the first pass that changes no value, or after 2m + 1 passes over m
members. The walk does not hold a cycle of more than eight members to one reading across
the defeats a read can enter it at. A member whose value does not depend on the others reads the same in
every assignment, so the break never holds it out of force: a read can meet a defeat whose
answer it does not move, and the walk counts that as a cycle too
(`placed_nogood_test/a-defeat-held-by-an-unguarded-firing-is-in-force-beside-a-guard-defeat`).
Two defeats of one loser do not compete.
Here `(cat Rex)` sorts first, so D1 is in force: L1 and G2 are hidden at CxA, and L2 and G1
are believed, in every arrival order and whichever loser a read asks first
(`placed_nogood_test/a-defeat-dependency-cycle-is-broken-in-content-order`).
An `(except G1)` at a reader below CxA hides D1's ground there, and that reader reads
D2 in force (L2 and G1 hidden, L1 and G2 believed), while CxA and a reader beside the
first, which see no except, read D1 in force
(`placed_nogood_test/a-cycle-whose-first-defeat-is-out-of-force-at-a-reader-puts-the-second-in-force-there`).

A cycle is not a dilemma: each nogood has its verdict, and the tie between the defeats
takes the content tie-break the engine uses everywhere else. Nothing is stored, and the
memo lives for one read. A cycle of one defeat, a ground derived from the nogood's own
loser, is in force: met again inside its own read it answers false, so its own target does
not count against it. A guard defeat and a nogood defeat resting on each other take the
same rule (`placed_nogood_test/a-guard-defeat-and-a-nogood-defeat-resting-on-each-other-are-broken-in-content-order`),
since the guard is checked in the network and stores its defeat in every order
([naf.md](naf.md)). A cycle through the guard itself is refused at assert time
([exceptions.md](exceptions.md#stratification)).

The guard at a firing's own placement takes the same reading for a blocker of either
class (design rulings 25 and 30): the firing is stored and its guard defeat placed beside
it.
A guard whose blocker is the loser of a nogood grounded on the firing's conclusion, all in
one context, is the two-defeat cycle above, and the walk reads it in content order in
every arrival order (`placed_nogood_test/a-guard-at-the-firings-own-placement-and-a-nogood-defeat-resting-on-each-other-are-broken-in-content-order`).
A guard defeat's justifications are read inside the defeat's own read, so a cycle of guard
defeats whose blockers rest on each other's firings is met again and closed, not read
without end (`exc/guard-in-force?`).

### What a reading reads

The settle publishes no report and no reading is kept. `read-clashes` reads every stored
`contradicts` at its own context, once per call, and keeps those that context believes and
sees, so a dilemma is reported KB-wide where a placement context believes every member. `(contradictions kb context)` reads only
the `contradicts` stated in a context the reader sees, from the smaller of two sides
compared by index counts: those contexts' extents, or the `contradicts` extent. So a
reader's reading costs the lesser of what it sees and the placed nogoods, and reads no
nogood placed outside both (`lein perf`'s `reader-dilemmas-beside-unseen-ones`).

### Where conviction is one-sided

A step read **through argument preservation** convicts one way only inside an
`anti_transitive` chain: the chain's steps are the ones `matches-visible` finds over the
marked predicate's spec closure, and a step that exists only because preservation reaches
it is not enumerated. Why discovery does not read preservation downward:
[defenses.md](defenses.md#discovery-does-not-read-argument-preservation-downward).

A stored claim denied by a claim read through preservation is not one-sided.
`preserving-nogoods` re-asks the stored facts a moved claim reaches, and the stored
extent of every predicate whose licence the settle otherwise moved
([The inherited-clash memo](#the-inherited-clash-memo)), so a general claim arriving
after the specific one forms the pair too. `(outranks animal cat)` beside `(outranks cat reptile)` under
`(asymmetric outranks)` is one `:inherited` nogood in either order, and the entry point
stores the second write
([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

`clash_oracle_test` makes no `transitiveInArg` declaration, so it covers the visibility
shape and not this one.

### How a settle finds the clashes

No clash is found by re-running a check over what moved. Each family's nogoods come off
the write-time candidate index, and the placement pass places the ones whose candidates
moved ([The nogood families](#the-nogood-families)).

What reaches a membership nogood with no relabel reaches it through the index:

- **a declaration** moves `tax/separation-inputs`, and the index reads the separations
  again over the pairs of the kept terms holding a type at or below a type the declaration
  moves (`tax/separation-moves`), queueing the terms whose nogoods moved; **a `genl` edge**
  moving is logged at its lower end (`tax/moves-since`), and the index reads again only the
  pairs holding a type at or below it, queueing those terms
  (`membership/sync-memberships`); a cover or an edge moving places again the kept terms
  with a membership at or below the whole it moves a cover nogood under, beside a denial
  or a second type.
  Neither reads a membership. The index compares its
  separation inputs with the taxonomy's, one input at a time, on identity. An installed
  image holds the two as equal values read back apart, so the first read compares them by
  value once and takes the taxonomy's;
- **a declaration's supporter** arriving or relabelled in a context of its own reaches the
  terms under the types it separates (`membership/terms-under`);
- **a `genlCx` edge** reaches the nogoods `chain/place-memberships!` names;
- **a membership or a denial** of a kept term joins it with no read and queues the term.

`clash_oracle_test` compares a stream's reading, write by write, with the same writes
loaded from scratch, over the membership routes a clash arrives by.

## What a settle is built from

A settle composes 20 features. Each one requires some others to exist, and removing a
feature removes every feature that requires it. This section lists the features, what each
requires, the reserved words that reach each one, and what a removal takes with it. The
cost of each step is the next section.

### The dependency layers

`─►` means *requires*: the target's removal removes the source. `⇢` means *supplies*: the
target's removal leaves the source with no input and nothing broken. The relation has no
cycle, because a cycle in it would be two features neither of which can be built first.

```
layer 5   published set ─► read walk, touched set
layer 4   read walk ─► placed nogood, visibility except
layer 3   placed nogood ─► decide/verdict, context scoping, forward chaining
          placed nogood ⇢ nogood discovery                edge solver ⇢ decide/verdict
layer 2   decide/verdict ─► strength classes              generators ─► forward chaining
          visibility except ─► context scoping
layer 1   touched set ─► region relabel           forward chaining ─► region relabel
          context scoping ─► genl/genlCx closures nogood discovery ─► genl/genlCx closures
          exceptWhen · NAF ─► recheck queue       supersession ─► equality partition
layer 0   region relabel, genl/genlCx closures, strength classes, recheck queue,
          equality partition ─► justification network ─► record store and index
```

| feature | code | reserved words | removing it |
|---|---|---|---|
| record store and index | `vaelii.impl.protocols` | none | removes everything |
| justification network | `vaelii.impl.jtms`, `vaelii.impl.dense-jtms` | none | removes everything above layer 0 |
| region relabel | `jtms/relabel-region*` | none | removes forward chaining, generators and the touched set |
| genl/genlCx closures | `vaelii.impl.taxonomy` | `genl` `genlCx` `isa` `genlInverse` | removes context scoping, nogood discovery and the arbitration bundle |
| context scoping | `tax/context-up` | `genlCx` `ist` | removes the visibility except and the arbitration bundle |
| strength classes | `jtms/region-classes` | `:monotonic` `:default` (assertion options) | removes `decide/verdict` and the arbitration bundle |
| recheck queue | `settle/drain-recheck!` | none | removes `exceptWhen` and NAF, its only fillers |
| equality partition | `tax/add-equality`, `tax/representative`, filled by `special/integrate-equality-sentex` | `rewriteOf` `sameAs` `equals` `different` | removes supersession |
| touched set | `jtms/touched`, and a reader's mark in it: `jtms/touch-mark`, `jtms/touched-since` | none | removes the published set; `preview`, the change feed and the cache reconcile diff the believed set instead, at O(KB) per write |
| forward chaining | `vaelii.impl.chain` | `implies` `set/forwardRule` `set/defaultRule` `set/backwardRule` `set/assumptionRule` `set/inertRule` | removes generators and the placed nogood; backward proof still answers |
| generators | `vaelii.impl.chain` | `implies` `set/forwardRule` with a rule consequent | removes nothing |
| nogood discovery | the candidate index (`vaelii.impl.decide`), `discovery/preserving-nogoods` | `not` `disjoint` `disjoint_metatype` `sibling_disjoint` `orthogonal` `siblingDisjointException` `functional` `functionalInArg` `asymmetric` `anti_transitive` `covering` `partition` `transitiveInArg` `transitiveInArgInverse` | leaves the placed nogood with nothing to place |
| `exceptWhen` · NAF | `recheck/exception-blocked-set`, `chain/place-guard-defeats!` | `exceptWhen` `unknown` | removes nothing; `:blocked` stays empty and no guard defeat is placed |
| supersession | `special/refresh-supersessions` | `rewriteOf` `sameAs` | removes nothing; `:superseded` stays empty |
| visibility except | `exc/except-hidden-fn`, `exc/except-closure-hidden-fn` | `except` `sentexHandle` | removes nothing |
| `decide/verdict` | `decide/verdict` | `bravely` `cautiously` | removes the arbitration bundle |
| edge solver | `vaelii.impl.solve` | `set/hardConstraint` `set/softConstraint` | changes nothing for a KB on the built-in `decide/verdict` |
| placed nogood | `chain/place-nogoods!`, `chain/place-inherited!`, `chain/place-nogood!` | `contradicts` `defeat` | removes the read walk's defeats; every nogood stands believed and no clash is reported |
| read walk | `exc/defeat-hidden-fn`, `exc/hidden-fn` | none | removes the published set's defeat moves; a placed `defeat` hides nothing |
| published set | `settle/defeat-moves`, `kb/defeat-reach`, `kb/prior-kb`, `settle/report-reach` | none | `preview`, the consequence report and the change feed miss a move a `defeat` makes with no relabel |

Strength classes, `decide/verdict`, the placed nogood and the read walk are the
**arbitration bundle**, and the bundle is the one region of the table where one removal takes several
features with it. Strength classes do not leave with arbitration: `core/defeat-class` is
public, and `vaelii.impl.inherit`, `vaelii.impl.chain` and `vaelii.impl.checks` read it for
supporter and declaration strength.

### A dependency no removal can separate

**A verdict requires strength classes.** `decide/verdict` names the unique weakest member
of a nogood as the loser. With no defeat-class the engine has no content-keyed minimum, so
a loser would be chosen on arrival order, which breaks order independence.

### The cycles a settle runs

The layers above have no cycle. The algorithm iterates in five places, each stated where
its mechanism is documented:

| cycle | what closes it | why it terminates |
|---|---|---|
| the exception loop | a blocked set moves belief, and belief moves what an exception query answers | a cycle through negation is refused at assert time; 16 passes bound it ([exceptions.md](exceptions.md#blocking-and-the-tms)) |
| a defeat's force | a `defeat` is in force only where it is itself believed, and its support can hold another defeat's target | a defeat met again on one read closes a cycle, which the walk breaks by reading every assignment of a cycle of at most eight members, then at most 2m + 1 passes over m members ([A defeat-dependency cycle](#a-defeat-dependency-cycle)) |
| a support cycle | `A` justified by `B` and `B` by `A` | `region-fixpoint` starts from nothing IN inside the region and only adds ([Locality](#2-locality)) |
| the class equation | a node's defeat-class reads its antecedents' classes | `region-classes` starts every member at `:default` and applies a monotone operator ([Strength propagates](#strength-propagates-from-the-antecedents)) |
| a `genl` or `genlCx` loop | an edge that would close a cycle in the closure | refused, or dropped and recorded when derived ([exceptions.md](exceptions.md#stratification)) |

### No switch removes a feature

Every feature above runs on every KB. Each optional feature sits behind an emptiness check
instead: a KB storing no `exceptWhen`, no merge, no clash declaration, no `except` or no
`defeat` pays a set read for that feature per settle or per read. No option on the KB
handle moves belief; the reasoning image records the one process switch that does,
`VAELII_ASSERTIVE_ARG_TYPES` ([storage.md](storage.md#the-reasoning-image)).

## The runtime of a settle

Invariant 2 states that a relabel costs its region. A settle does more than relabel, and
each of its other steps is bounded by a different quantity: the candidates a move reaches,
the rules a trigger reaches, a sweep budget, or the whole store. This section lists the
steps in the order `settle*` runs them, gives the quantity that bounds each one, and names
the check that enforces the bound. The last part lists the steps where the bound is not the
region.

### The runtime state

`n` is the store, `r` the relabelled region (`jtms/touched`), `q` the rules the recheck
queue holds, and `k` the nogoods whose placement a move can change.

```
write entry point (assert / retract)                          bound
 ├─ canonicalize · checks · index · record · JTMS node        O(1) per fact
 ├─ chain: join each rule keyed on the fact's predicate       O(rules on the predicate × join)
 └─ add-justification → relabel the affected region           O(edges in r)

settle*
 ├─ 2  the reconcile a caller's relabel owes                  O(r)
 ├─ restore-depths (only after a deferred batch)              O(V + E) of the taxonomy, once
 └─ passes, until one queues, revives and releases nothing, at most 16
     ├─ 3  class-moved-merge-seeds (only under a merge mark)  O(r)
     ├─ 4  place-inherited!: one discovery
     │     ├─ preserving-nogoods                              O(1) check; else O(r), asks O(r); O(standing) carrying nothing
     │     └─ place the clashes asked again                   O(clashes asked × vantages)
     ├─ 5  place-nogoods!: each family's moved candidates     O(k × one placement)
     ├─ 6  post-defeat-moves! · drain-recheck!                O(min(r, stored defeats) + q)
     ├─ 7  defeat-belief-moves · revived-seeds                O(r + moved defeats' targets)
     ├─ 8  exception-blocked-set · place-guard-defeats!       one level-6 query per trigger-reachable firing
     └─ 9  set-blocked · sweep · re-chain released firings    O(released firings);
                                                              a blanket re-join is O(fact extent) per rule

settle-finish
 ├─ restore-depths (only after a pass left it loose)          O(V + E) of the taxonomy, once
 ├─ refresh-beliefs (only when belief moved)                  O(caches a supporter in r feeds)
 ├─ refresh-supersessions (only after an except or an         O(data the except reaches + classes moved)
 │   equality edge moved in belief)
 └─ the published set, with what a defeat reached (only when  O(r + what the moved defeats and the write reach)
     a sink or listener wants it)

recover                                                       O(n): one settle, r = every sentex
```

Inside every relabel, the two least fixpoints are `region-fixpoint` for `:in` and
`region-classes` for the defeat-classes. Each is a worklist over the region's edges, so
each is O(edges in r)
([Locality](#2-locality) has the measurement).

A settle materializes the region `passes + 1` times, which `settle_region_cost_test` asserts
as a count. On the dense network each read copies the touched bitmap into a set, so that
count is a multiplier on O(r), and on a `recover` it is a multiplier on O(n).

### The placement pass

Steps 4 and 5 place the nogoods, and the network records no verdict. Step 4 asks
`preserving-nogoods` once over the live KB, records the nogoods whose members the network
believes, with their vantages, in the candidate index for each member set it read again
(`inherited/update-inherited!`), and places the clashes asked again. Step 5 places each
family's nogoods whose candidates, members, grounds or placed `contradicts` the pass moved,
and those a moved `genlCx` edge reaches ([A nogood placed as a
conclusion](#a-nogood-placed-as-a-conclusion)). Step 5 reads the routes of a family's
nogoods before it places the first (`chain/plan-sets`), since a placement moves no route,
witness or member label another nogood of the family reads. Past 4,096 nogoods it reads
and places them a batch at a time in the same content order, so the routes held at once
are bounded by the batch
(`settle_region_cost_test/a-placement-pass-holds-the-routes-of-one-batch`). The witnesses of the routes'
`genl` subsumptions and of their placements' `genlCx` reaches, and the supporters'
classes, are held for the pass while the change clock does not move
(`chain/*witnesses*`), keyed by the walk's scope (`tax/read-scope`), so nogoods that share
a subsumption under one scope walk it once
(`settle_region_cost_test/a-recovers-placement-settle-walks-each-subsumption-once-per-vantage`).
Walks to one target under one scope share the route lengths of the types above their
sources, held there too, so a pass enters each type once per target and threshold however
many subsumptions climb through it
([taxonomy.md](taxonomy.md#strength-of-a-subsumption-path), `lein perf`'s
`recover-placement-own-leaves`).
The reads hold the walks' sorted neighbours and edge supporters (`tax/with-neighbours`),
and a witness walk past its first expansions keeps only the types under its target
([taxonomy.md](taxonomy.md#strength-of-a-subsumption-path)).
A `defeat` the pass stores posts its
target's re-check before the drain (step 6), and a target a removed defeat gives back is
re-chained only when the taxonomy derives an answer from it (`tax/derives-from?`): the
network kept it IN, so a rule's firings over it stand. A defeat takes two passes, the
placement and the chaining it releases, and a revival one
(`settle_region_cost_test/a-defeat-takes-two-passes-and-a-revival-one`). No placement
defeats an `except`: an `except` is forced-monotonic, never a loser, and its denial is held
OUT ([The forced-monotonic set](#the-forced-monotonic-set)). The reports read the
placed `contradicts` (`clashes/read-clashes`).

### What `settle-finish` reconciles

`settle-finish` runs once, after the last pass, in this order:

1. `restore-depths`, for a depth potential the passes left loose. The repair a
   `with-deferred-settle` batch owes runs before the passes.
2. `refresh-beliefs` over the region, only when belief moved: a defeat, a revival, a
   pass that moved the blocked set, or a relabel before the settle
   (`belief-moved?`). Those are the only label flips a settle sees. The last is
   `preview`'s: `suspend-premise` and the rollback's `add-premise` flip labels with no
   defeat, block or write, so `preview` binds `settle/*relabelled-before?*`, and the
   settle also reconciles at its start, as after a revival, before the passes read the
   closures. A declaration that arrives or leaves reaches the caches
   through `special`'s integrate hook on the write path, so a settle that flipped no label
   leaves the caches consistent. `restore-depths` runs again after the reconcile, since
   the reconcile can open or close a cycle
   ([taxonomy.md](taxonomy.md#what-a-batch-does-to-the-depth-potential)). An equality
   supporter a reconcile found disbelieved and this one finds believed met its arrival
   with nothing to restate, so its class takes the arrival's re-check and migration here
   (`special/believed-again-sweeps`), and the supporter and its twins go to `settle`'s
   re-seed ([equality.md](equality.md#what-a-merge-does)).
3. `refresh-supersessions`, only after an `except` moved, or an equality edge that the
   forced-monotonic set does not hold moved in belief. The write path reconciles every supersession a
   stored or removed sentence moves, so a settle that moved no equality premise reconciles
   none ([equality.md](equality.md#what-a-merge-does)).
4. `refresh-beliefs` again whenever a supersession entry changed since the last settle,
   over the region plus those data (`special/take-supersession-moves!`). A merge
   supersedes a `genl` or `disjoint` declaration with no label moving, and step 2 read
   the region alone. The spellings an un-merge gave back go to `settle`'s re-seed
   ([the other half](#the-other-half-a-spelling-an-un-merge-gives-back)).
5. The published set: the region, the supersession flips, the twins step 2 stored, and the
   handles a `defeat` stored, removed or standing before the write reaches, read at their
   own context ([The published set](#the-published-set)), handed to
   `*touched-sink*`, `*touched-in-sink*` and the change feed. The sets are built only when
   a sink is bound or a listener is registered, and the feed is skipped on a rebuild,
   whose region is the whole KB.
6. `reset-touched!`.

`jtms/touched` is read once, into a delay every step shares, because the dense network
copies its bitmap into a set on each read.

### Where the time goes, measured

`lein bench-settlephases [n] [memory|disk|both] [defeats=<k>]` charges each settle's wall
clock to the cost centre running at that instant (`vaelii.impl.settle-phases`). The reading
below is n=60,000 facts (104,157 sentexes and 52,074 justifications; with `defeats=50`,
104,357 and 52,174), one run per backend and configuration. A range spans the two
backends, and a cell that names them gives each. The split is a ratio between centres in
one run;
the harness reports absolute milliseconds as untrusted on a shared machine.

| centre | additive load | load, 50 standing defeats | `recover` replay | `recover`, 50 standing defeats |
|---|---|---|---|---|
| `:chaining` — the generative join | **45–46%** | **42–43%** | 0% | 0% |
| `:outside` — canonicalization, checks, index, minting | 42–45% | 41–46% | 30% memory, **77% disk** | 29% memory, **52% disk** |
| `:belief` — relabel and `add-justification` | 0.1% | 0.1% | **67% memory**, 21% disk | **59% memory**, 28% disk |
| `:discovery` — the inherited family's discovery | 1–2% | ~1% | ~0% | ~0% |
| `:finish` + `:glue` | 8–11% | 10–15% | 2–3% | 12% memory, 20% disk |
| relabelled region, p50 | 2 | 2 | 104,157 | 104,357 |

A centre is charged its **self-time**, the interval while its span is on top of the stack,
so nested centres are not counted twice and the six buckets sum to the run. `:belief`
holds the relabels, the reconcile a caller's relabel owes and `recovery/rebuild-tms`'
replay; `:finish` is `settle-finish`, where the published set is built; `:glue` is the settle loop outside every span, and `:outside` the time between settles.
`add-justification` carries no probe of its own: its time goes to the span its caller
opened. A span on a timing run costs two `System/nanoTime` reads and two unsynchronized
mutations, which the single writer permits. `settle-phases/stop` returns the run totals
and one record per settle with its region size and pass count, since one root-edge
retraction moves the whole graph and a mean over settles hides it.

Three shapes follow from the table:

- **A clean load spends its time writing and chaining, not believing.** The per-assert
  region is 2 nodes, so the belief fixpoint is 0.1% of the run. The per-fact write path
  is [storage.md](storage.md#what-a-bulk-load-costs)'s table: 43.4 µs per fact at one
  million facts, with the one deferred settle under the measurement floor.
- **A `recover` spends its time relabelling on `:memory` and outside its settles on
  `:disk-log`.** Its region is the store. On `:disk-log` the work between the recover's
  two settles is 77% of the run. A `:disk-snapshot` open skips the replay when it installs
  the [reasoning image](storage.md#the-reasoning-image).
- **Standing defeats move time into `:glue`.** Fifty placed negation pairs take
  `:finish` + `:glue` from 8–11% of a load to 10–15%, and from 2–3% of a recover to 12–20%;
  the other centres keep their shares within a few points.

The `defeats=<k>` option seeds k negation pairs in `CxUniverse`, which the settle places.

The exception loop is measured separately in
[exceptions.md](exceptions.md#the-fixpoint-question-measured): the blocked set moved in
**0** passes on every settle of the starter and stories load, and in at most **1** in every
`except_test` scenario. On `except_recheck_test`'s workload, where a
second rule makes the exception hold on every firing, step 8 costs **1.0** level-6
evaluation per assert and the whole settle **2.0**, flat from n=25 to n=200.
`except_recheck_test` asserts the growth of that count, not its value.

### Where the scaling arguments hold

`lein perf` asserts each scaling claim as a growth ratio between two sizes, never as a
duration. `bench/vaelii/bench/perf.clj` states the method, and each check there carries
its `:claim`, `:sizes` and `:max-ratio`, and the `:group` its timed operation runs in.
`lein perf --only <group>` runs one group, and `lein perf --list` prints each check's
group. The checks sort into four kinds by the quantity the claim bounds a step by. A fifth
kind lists the steps whose bound is the store, which no check holds.

**Flat.** The step costs its region, or what it returns, and not the quantity the check
grows. The ratio bound is 2.0× across a 6× to 128× size step unless the row names
another. These checks hold invariant 2 end to end:

| step | `lein perf` checks |
|---|---|
| a write that reaches its own region: a fact derived through a defeasible rule, a negative fact with no positive twin, a membership, a membership in a type with a deep ancestor set, a length binding, a fact of a predicate with a declared arity, a durable append, a fact into an existing context NAT, a retraction naming no NAT | `defeasible-load`, `negation-load`, `membership-check`, `membership-under-deep-type`, `bound-type-load`, `arity-reach-trigger`, `durable-fact-append`, `context-nat-existing-context` (3.0×), `retract-nat-scaling` |
| a region delivered to a feed listener | `feed-listener-scaling` |
| a write beside the standing definitional clashes, `P`/`¬P` dilemmas and merges it does not name, a `genl` edge separating nothing beside standing clashes, and a `genlCx` edge reaching nothing beside standing `P`/`¬P` dilemmas | `clash-arbitration` (3.0×), `negation-arbitration` (3.0×), `retract-merge-scaling` (3.0×), `except-merge-scaling` (4.0×), `taxonomy-edge-arbitration` (3.0×), `context-edge-arbitration` (3.0×) |
| a `genl` edge deep in a chain, one `genl` edge or `inverse` declaration defeated and revived beside n `disjoint` declarations (the relabel and `refresh-beliefs`), and a `symmetric` mark defeated and revived below its facts beside the facts under another mark | `taxonomy-depth`, `taxonomy-belief-flip`, `flat-cache-belief-flip`, `permuting-mark-defeat-flip` |
| a write on a KB whose marks the fact does not reach | `unrelated-fact-under-marked-kb-fanout`, `constraint-exposure-shared-arg`, `constraint-genl-edge-unmarked` (2.5×) |
| a membership or a `genl` edge into a `sibling_disjoint` clique, in the clique's size | `disjoint-clique-membership`, `sibling-disjoint-new-spec` |
| a `genl` or `genlCx` edge, in the graph, the excepted rules, the firings and the readers it does not reach, the `genl` edges its `sub` already sees, the stored `genlCx` edges beside an `except` no edge rests on, the functors under an arity conflict it is not above, the rules reading above it when no rule concludes below it, and in the spec closures of the rules its stratification walk reaches | `genl-edge-negation-recheck`, `genl-edge-beside-arity-conflicts`, `edge-stratification-unreached`, `edge-stratification-unconcluded`, `edge-stratification-walk`, `genl-defeat-rejoin` (4.0×), `genl-crossing-many` (3.0×), `genlcx-edge-reader-fan` (3.0×), `genlcx-edge-under-a-seen-taxonomy`, `genlcx-edge-beside-declared-facts`, `genlcx-edge-beside-excepted-declarations`, `genlcx-edge-beside-seen-excepts`, `genlcx-edge-revealing-one-except`, `genlcx-edge-beside-stored-context-edges`, `retract-context-cycle-scaling`, `retract-context-cycle-beside-cycle`, `assert-context-edge-beside-cycle` |
| an un-merge of one class beside standing merges it does not touch, a merging assert in a deferred batch, a merge withdrawing its spelling's firing beside standing merges whose firings were withdrawn, a write beside the subsumed mints the KB withholds, the settle after a `genl` edge beside declarations waiting on a type bound to another length, and an `arg` declaration over stored facts beside a deeper declared type | `unmerge-over-standing-merges` (3.0×), `deferred-merge-batch` (3.0×), `merge-withdrawing-a-firing` (3.0×), `mint-withdrawal-under-busy-term`, `settle-beside-withheld-mints`, `mint-release-after-genl-move`, `arg-declaration-over-facts` |
| a recover's rebuilds, per claim, declaration, fact or negation pair each re-reads: the inherited discovery's questions and the placements they give, the lifts, the closing settle's placements, the membership index's first sync over a kept term's types under a deep ancestor set, the discovery's denial probes over a type with many supertypes and its probes that match nothing beside forced-monotonic declarations; and the first write after a recover | `recover-inherited-discovery`, `recover-discovery-own-out`, `recover-discovery-separated-term`, `recover-membership-cover-sync`, `recover-preserved-negated-fan`, `recover-preserved-empty-probes`, `lift-rebuild`, `recover-negation-pairs`, `first-write-after-recover` |
| an `exceptWhen` rule-membership check, a write beside believed `except`s it does not reach ([contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree)), an `except` beside the firings that do not rest on its target, a write beside refused firings ([the refused-firing record](exceptions.md#a-refused-firing-is-remembered-as-bindings)), a retraction releasing a firing beside a guarded rule's firings ([what is re-chained](exceptions.md#re-chaining-what-was-released-not-what-was-touched)), a first read below an `exceptWhen` rule's context ([asked at every reader](naf.md#evaluated-in-the-placement-context-not-the-join)), a scoped read beside what the `except`s hide, and an `except` of a guard's blocker beside the guarded rule's other firings | `watched-rule-membership`, `assert-over-standing-excepts` (3.0×), `assert-beside-naf-refusals`, `released-refusal-beside-guarded-firings` (4.0×), `guarded-firings-read-below`, `visibility-reading`, `except-beside-unrelated-firings`, `except-of-a-guard-blocker` |
| the placed nogoods ([The nogood families](#the-nogood-families)): a mark, a binding or a declaration arriving over its candidates and the first read after it, a metatype edge arriving over its members, a write beside the placed pairs it does not reach, a write beside contexts each holding a placed nogood, a membership joining one of n standing dilemmas or joining a nogood as its loser, a write adding a candidate beside the candidates standing elsewhere, a write beside the candidates of four families stated where its context does not see them, a warm read of a placed loser, a read beside the candidate tuples a binding holds, a vantage below the members' maximum, the join naming a chain's contexts, a brave or cautious ask between writes, an ask of the candidate index after an image install, and the first write after one | `irreflexive-mark-arrival` (3.0×), `arity-binding-arrival` (3.0×), `metatype-edge-arrival`, `membership-declaration-arrival`, `tuple-mark-determinant-write`, `functional-in-arg-empty-determinant-sweep`, `negation-reader-write`, `verdict-published-set-write`, `reader-scoped-write`, `standing-nogood-write`, `standing-loser-write`, `candidate-write`, `reached-reader-family-read`, `decided-warm-read`, `held-shape-first-withdrawal`, `per-reading-vantages`, `chain-join`, `brave-ask-between-writes` (3.0×), `installed-image-reads`, `first-write-after-install` |
| placement and the read walk ([A nogood placed as a conclusion](#a-nogood-placed-as-a-conclusion)): a write naming no placed nogood, a write making a nogood whole or dissolving one beside its loser's consequences, a `genlCx` edge reaching none of the placed nogoods or changing none of their contexts' views, a membership beside the types its term holds, a separation beside the kept terms, a read below a vantage beside the defeats outside its support, a `belief-status` beside the excepts and defeats on other targets, a read of a tuple whose supers bind two lengths, a `genl` edge's defeat beside the defeats of other edges, a hidden route beside the unclaimed types under its end, a reading of a context's dilemmas beside those it does not see, a `genl` edge beside the contradicted `orthogonal`s (3.0×), a fact naming no nogood member asserted under a listener, a read beside the defeats in contexts its reader does not see, a read in the depth of the derivation it asks beside defeats, placements or arity candidates its reader does not see, a read of a `:monotonic` fact beside the permuting marks, a backward query beside the candidates no context places, a `genlCx` edge giving a nogood one more placement beside the placements it holds, a closure read at the readers a `genl` edge's defeat does not reach, a hidden firing's read beside the memberships under their own hidden edges, an `except` beside the carried inherited-clash entries whose questions do not read its target, and a `genl` edge into a type separated from a preserved predicate beside that type's memberships, with its closure under or past the crossing cap | `vantage-unrelated-write`, `whole-beside-loser-consequences`, `dissolving-beside-loser-consequences`, `whole-beside-unary-loser-consequences`, `dissolving-beside-unary-loser-consequences`, `vantage-dissolving-write`, `vantage-context-edge-unreached`, `context-edge-beside-membership-nogoods`, `membership-beside-held-types`, `separation-beside-kept-terms`, `read-below-vantage`, `hidden-check-beside-excepts`, `arity-exempt-read`, `genl-defeat-beside-defeats`, `hidden-route-beside-unclaimed-types`, `hidden-route-beside-untyped-types`, `reader-dilemmas-beside-unseen-ones`, `edge-beside-contradicted-orthogonals` (3.0×), `listener-write-beside-defeats`, `read-beside-unseen-defeats`, `default-chain-beside-many-unseen-defeats`, `default-chain-beside-unseen-contradicts`, `default-chain-beside-unseen-arity-candidates`, `monotonic-read-beside-marks`, `monotonic-chain-beside-seen-defeats`, `backward-query-beside-candidates`, `context-edge-beside-placements`, `defeat-beside-unreached-readers`, `hidden-route-beside-hidden-claims`, `inherited-entry-except`, `genl-edge-under-separated-type`, `genl-edge-past-the-crossing-cap` |
| retrieval: an argument after a variable, a compound, an intersection or an overlay posting, a columnar insert, a closure already asked, an open `disjoint` goal, a membership of a busy term, and a plan | `arg-root-retrieval`, `compound-probe`, `intersect-selectivity`, `overlay-selectivity`, `columnar-fanout`, `closure-membership`, `disjoint-enumeration`, `membership-read-under-busy-term`, `plan-scaling` |
| solving, the qualitative calculi, and a datum on a `SupportingProver` source beside the firings of rules whose computed antecedents no prover reading it answers | `solve-rule-grounding`, `label-beside-unrelated-facts`, `qcn-network-residency`, `qcn-arrival-over-standing-firings` (3.5×), `qcn-arrival-beside-an-unmoved-network` (2.5×), `source-datum-beside-computed-firings` |

`second-route-over-a-deep-chain` claims a read of a firing flat in the length of the
`genl` chain its second route climbs. The search asks whether the goal's type is in the
claim type's scoped ancestor set (`tax/genls`), which the closure cache holds across reads
under the search's scope. The first read builds that whole ancestor set, so it costs the
ancestor set even where the goal sits one edge above the claim's type. An ancestor set
built while a route question is open is not held, so a read that opens one builds it again.

**Flat past a cap.** A budgeted merge sweep implicates every instance below a type or
inside an ancestor set, which is the extent rather than the region. The sweep stops at
`tax/*exposure-instance-budget*` instances (8192; the checks bind it to 100) and files a
notice naming its trigger, so the cost is flat once the extent is larger than the budget
and linear in the extent below it: `constraint-exposure-context-edge` and
`constraint-genl-mark-descent`, each 2.0× past the budget. A `genl` edge whose closure holds more than `inherit/crossing-closure-cap`
terms (512) moves every predicate preserved along `genl` with no read per term:
`genl-crossing-wide`, 3.0× past the cap.

**Linear in the standing set.** `k` is the standing set: the nogoods and the carried
inherited-clash entries the KB holds. A placed nogood is stored and a read walks only the
asked handle's support, so the standing set enters a write through the steps that read it
whole: the inherited discovery when it carries no entry, and a report that orders what it
returns.
`padding_blindness_test` lists every step that reads a stored handle of standing content
the write does not name, each with a world that shows the read, and fails a read no row
lists. The checks bound the per-member cost, so a regression to a full re-derivation
of the set on every settle fails them:

| claim | `lein perf` check | growth | bound |
|---|---|---|---|
| standing inherited dilemmas, per assert | `inherited-clash-arbitration` | 32× | under 10× |
| standing inherited clashes split across contexts, per unrelated assert | `inherited-clash-arbitration-split` | 512× | under 90× |
| carried inherited-clash entries, per unrelated retract | `inherited-entry-retraction` | 32× | under 10× |
| carried inherited-clash entries, per declaration no entry reads | `inherited-entry-declaration` | 32× | under 5× |
| `contradictions`, which orders the standing set it returns | `standing-clash-reading` | 32× | under 125× |
| standing dilemmas in a context, per `preview` of a fact there no nogood reads and of an empty batch | `preview-beside-standing-dilemmas` | 16× | under 2× |

**Grows with a structure the step walks.** The step walks something the fact or the
question names, and the claim is that it walks that structure once rather than once per
pair:

| claim | `lein perf` check | growth | bound |
|---|---|---|---|
| a `disjoint_metatype`'s members, per membership assert | `disjoint-metatype-membership` | 8× | under 12× |
| the vocabulary (2.8× while the stored facts grow 8×), per `kb-quality` | `quality-report-scaling` | 8× | under 4× |
| the declarations, per declarations census | `quality-declaration-census` | 8× | under 15× |
| the super-predicates, per declarations census | `quality-declaration-depth` | 32× | under 45× |
| the claims reaching one term, per ask | `inherit-reach-memo` | 8× | under 12× |
| the routes between two terms, per preservation support | `witness-route-search` | 8× | under 12× |
| the nogoods a `genlCx` edge makes whole, per edge | `context-edge-making-nogoods-whole` | 8× | under 16× |
| the contexts under each edge of a `genlCx` chain moved in one pass beside a held nogood, per edge | `genlcx-chain-moved-beside-a-nogood` | 8× | under 16× |
| the postings of the facts a deferred batch stores after its `genlCx` edge, per closing drain | `deferred-facts-after-a-context-edge` | 16× | under 6× |
| the guard defeats a reader sees naming one firing, per read of the firing there | `guard-defeats-at-a-reader` | 2× | under 4× |
| the instants of a metric network, per arriving constraint | `metric-closure-warm-start` | 8× | under 35× |
| the regions of a containment chain, per arriving fact with a forward rule over the calculus | `qcn-chain-load` | 4× | under 40× |
| the firings of a rule excepted on a relation the calculus composes, per arriving spatial fact | `qcn-arrival-over-composed-exceptions` | 8× | under 12× |
| the links of a sign chain, per ask after a write | `sign-chain-rebuild` | 32× | under 100× |

**Proportional to the store by construction.** No perf check bounds these steps, because
their region is the store:

- **`recover`**, whose single settle relabels every sentex. The reasoning image is the
  mitigation, not a scaling argument.
- **A root edge.** The affected region of a `genl` edge at the top of the taxonomy is its
  whole consequence closure, so O(r) is O(n) for that write. Locality bounds a write by
  what depends on it, and some writes have everything depending on them.
- **A blanket re-join** in step 8, for a rule whose refusal record overflowed
  `chain/max-refusals-per-rule` (4096 entries) or a context-visibility transition. Each
  such rule joins over its fact extent once per productive pass.
- **`restore-depths`**, O(V + E) of the taxonomy once per `with-deferred-settle` batch.

### What neither check sees

`lein perf` reads ratios, so a constant added to every write moves both readings and
passes. `assert_cost_test` asserts the exact index operations seventeen fixed workloads
cost (twelve asserts and five retractions), and `settle_region_cost_test` asserts how often
a settle materializes its region and what it re-derives. Those counts are the regression
tests for a constant. No test watches the phase split above: `lein bench-settlephases`
reports it, and a change that moves time between centres without changing a ratio or a
count passes both checks.

## The `Solver` protocol (`vaelii.impl.types.solve`)

The external solver is a plug-in behind a protocol, defined in `vaelii.impl.types.solve`;
`vaelii.impl.solve` builds the `Program` and holds the local solver:

```clojure
(defprotocol Solver
  (solve [solver program]
    ;; -> {:defeat #{handle...} :violated [nogood...]}
    ))
```

A `Program` carries five fields: `assumptions` (the contested defeasible handles, never
known-true), `fixed` (known-true background referenced by a contradiction, assumed and
not decided), `contradictions` (nogoods with priorities and sentences), `content`
(`{handle {:sentence s :context c}}`, so a tie-break keys on what an assumption says
rather than on its handle), and `cardinalities` (at-most / at-least bounds over contested
heads, which only `solve-context` fills, from `asp/atMost` / `asp/atLeast` rules). A
backend renders it to ASP:

- default nodes → choice/`{a}` atoms;
- `:monotonic` `fixed` nodes → **omitted** (assumed true, never sent);
- contradictions → **weak constraints** with priorities, so the program is always SAT and
  the violated weak constraints are the reported result.

### Only `:default` content reaches a solver

A settle hands no nogood to a solver: `decide/verdict` answers a defeat, a dilemma or a
hard clash. Labeling is the solver's one caller
([why that holds the split](defenses.md#a-settle-hands-no-nogood-to-a-solver)).
`label/dilemma-program` builds its `Program` from the dilemmas, whose tied minimum is
defeasible, and `solved-labeling` keeps the program's assumptions minus the solver's
`:defeat`, so a defeat outside the assumptions moves nothing.

Two solvers ship. The default is `local-solver`, a deterministic stub that satisfies
contradictions highest-priority-first by defeating the greatest-`content-key` contested
member and reports any nogood it cannot satisfy. `vaelii.impl.asp.edge/edge-solver`
renders the Program to ASPIF and solves it with clingo or clasp; install it with
`(core/set-solver kb :asp)`. It falls back to the stub when no backend is reachable.
Where the stub walks contradictions one at a time, ASP optimizes globally: given two
nogoods sharing a member it defeats the shared one. See [asp.md](asp.md).

## API

```clojure
(assert kb S ctx {:strength :monotonic})   ; known-true; never defeated, never solved
(assert kb S ctx)                           ; :default (the common case)
(conflicts kb)                              ; the irreducible known-true clashes, as reports
(contradictions kb)                         ; the dilemmas, as reports
(violations kb)                             ; derived conclusions dropped as inadmissible
(preview kb {:add […] :remove […]})         ; the belief a batch would move, then rolled back
(set-solver kb :asp)                        ; the real answer-set backend, by name
(set-solver kb solver)                      ; or any Solver value
```

Every refusal `assert` throws carries an `ex-info` `:type`;
[troubleshooting.md](troubleshooting.md#i-have-a-type-and-do-not-know-what-it-means)
holds the vocabulary and the page that owns each keyword.

## Where the layer stops

- A violation with **no opposing sentex** on the derivation path is dropped and
  reported, never arbitrated: an argument constraint, a malformed special predicate, an
  unstratified derived edge ([Definitional constraints on the derivation
  path](#definitional-constraints-on-the-derivation-path)).
- NAF is not a nogood. `unknown` / `thereExists` in a rule antecedent is re-evaluated on
  the `exceptWhen` triggers and stores nothing ([naf.md](naf.md)). A `Justification` has
  **no out-list**: an existential NAF negates a pattern, which has no single handle for an
  out-list to hold.
- A default/default clash is reported as a dilemma and never arbitrated
  ([There is no second axis](#there-is-no-second-axis)), so the engine orders no two
  equally strong rebuttals.
- A settle commits to one optimal answer set, so `in?` alone does not distinguish a forced
  belief from a pick between equals. `vaelii.impl.asp.label/classify` enumerates the
  optima to recover the distinction, and `label/classify-local` does so region-locally
  with no backend ([labeling.md](labeling.md), [asp.md](asp.md)); belief itself still
  commits.
- Cardinality/aggregate contradictions are not expressed; a nogood is a flat set.
- **An equality is not defeasible by its own negation.** Once `(rewriteOf Pref Dep)`
  merges the two, every sentence naming `Dep` is rewritten — including
  `(not (rewriteOf Pref Dep))`, which is stored as a claim about `Pref` alone and so
  clashes with nothing and defeats nothing. The ways an equality stops being believed are
  retracting it and withdrawing what a *derived* one rests on; both un-merge, and both are
  re-seeded ("The other half" above).
- **A firing names one witness, so a second route is re-derived or read rather than recorded.** A
  justification names one path for each reachability it rests on: the `genl` path a
  subsumed match climbed, the `genlCx` path its placement is seen over, and the path a
  `transitiveInArg` claim travelled. A route arriving after the firing that the witness
  rule names instead re-joins the firing over itself, and the justification it adds
  **replaces** the one over the older route (`special/drop-replaced-routes!`): the same
  informant, conclusion, bindings and subsumptions, and antecedents that differ only in
  believed `genl` and `genlCx` edges. The store then holds what the order bringing the
  route first holds, and `why` answers the same in both (`late_route_test`).

  A bounded `genl` or `genlCx` rule literal matches a stored edge as the closure's pair,
  so a stated edge and a cover installing it yield one justification in every arrival
  order ([inference.md](inference.md#a-genl--genlcx-antecedent-reads-the-closure)).

  A justification's **subsumptions** are the `[sub super]` predicate pairs its firing
  matched a fact to a rule literal through (`chain/subsumption-links`), stored under
  `:subsumptions` and absent for a firing that matched every literal on its own key. They
  record which fact matched which literal. The antecedents cannot record it, because they
  are a content-ordered set. Two firings over one individual of two types that each reach
  both literals of `(inspace ?x) ∧ (intime ?x)` pair the two facts with the literals
  swapped, and their subsumptions differ, so neither replaces the other and both are
  stored in every order. The dedup key (`jtms/has-justification?`) holds the subsumptions
  too, because two such firings can name one antecedent set: when both types reach both
  literals through one intermediate type, the two firings name the same four edges. A
  justification stored before subsumptions were recorded has none, and the replacement
  compares it on its edges alone when its antecedents name a `genl` edge. The argument-type entailment
  replaces its route the same way. Four things take a named path away. The first two
  start a re-derivation over a surviving route, and the other two leave the firing standing
  at a reader that reaches the path's ends another way:

  | what takes the path | where | what re-derives |
  |---|---|---|
  | a retraction of an edge | the network | the re-join of the facts under the edge, from what the sweep collected (`special/resubsumption-seeds`) |
  | a network defeat of an edge | the network | the same re-join, from the edges that went IN ⇒ OUT in the settle (`settle/departed-seeds`) |
  | a placed `defeat` of an edge | the defeat's placement and below | nothing: the read walk reads the edge at its label for a firing whose goals the reader reaches from a believed claim over edges it does not hide (`exc/rerouted`) |
  | an `except` of an edge | the excepting context and below | the same read |

  The argument-type entailment and the equality a descended `functional` or
  `anti_symmetric` mark derives name a `genl` route the same way (`checks/edge-support`),
  and the first two rows re-derive them too: a retraction draws each derivation the sweep
  deleted again after the teardown, and a network defeat draws each one the edge took OUT
  (`special/rederive-descended`, [argtypes.md](argtypes.md)).

  A placed `defeat` and an `except` leave the edge IN in the network, so no relabel starts
  and nothing is chained again. The read walk takes each justification that rests on a
  handle hidden at the reader and asks whether the firing stands another way
  (`exc/rerouted`). For a rule firing it reads the goals the firing matched through a
  reach: each antecedent literal of the rule no antecedent of the justification states,
  instantiated from the conclusion and the stated antecedents. It then searches backward
  from each goal for a believed claim that reaches it over edges the reader believes and
  sees (`inherit/goal-reached?`): a stated match through the matcher's sub-predicate fan,
  or, at a position a `transitiveInArg` or `transitiveInArgInverse` declaration preserves,
  a claim whose term reaches the goal's term. The search starts from the stored claims
  with the goal's other arguments when they number no more than the goal term's reach, and
  from the reach's terms otherwise, and it stops at the first claim. A claim the
  justification does not name counts, so the answer is the same whichever claim the
  arrival order made the firing name. A justification of no rule, or whose goals the walk
  cannot instantiate, stands where the reader reaches the two ends of every path its
  hidden edges lie on: the scoped `genl` closure, or the fact relation a
  `transitiveInArgInverse` claim moves along. A hidden `genlCx` edge is on no path, so a
  justification resting on one stands nowhere it is hidden ([contexts.md](contexts.md), "An
  except on a `genlCx` edge"). Either answer is memoized for one read, and nothing
  is stored.

  The search reads claims and edges as the read that asked it does. A belief read
  (`res/believed-at?`, `in?`) counts a claim or an edge an `except` hides at the reader, and
  a visibility read (`ask?`, `believed?`) does not (`tax/*search*`). A claim or a derived
  edge inside the search is read with its own second routes, the same way as outside it,
  so a claim that stands only on a second route still reaches the goal. A route question
  met again on one path reads as not reaching. An answer that read false off a question
  still open above it is not kept (`exc/route-answer`). The literal cache and the scoped
  closure caches key on the search's reading, so a read outside a search is never served
  an answer read inside one. An entry computed inside a search (a scoped closure, a
  neighbour set, a context's down-set, a literal's matches) whose computation read a route
  question still open is answered and not stored (`caches/*open-mark*`), so a later search
  is not served a closure or a match set read while another question was open. The
  justifications of one conclusion that share a goal ask the search once per read.

  The preservation witness is the route whose most specific asserting context is the most
  general available ([inherit.md](inherit.md)), so a clash that denies an edge of the
  specific route costs a reader nothing: the conclusion is placed above that route and does
  not rest on it. A clash that denies an edge of the **named** route hides the firing at
  the clash's vantage and below, except at a reader that reaches the path's ends another
  way. Two shapes show it. The first is a clash in the specific route's own context:

  ```
  CxUniverse   (genl mid dog) (genl chi mid)   the long route, named
               (largerThan dog cat)  (transitiveInArgInverse largerThan 1 genl)
               forward rule (largerThan ?x ?y) ⇒ (noted ?x ?y)
   └─ CxA      (genl chi dog)                  the short route
               (not (genl chi mid))  :monotonic
  ```

  CxA reaches `chi` up to `dog` over its own edge, so it reads the CxUniverse firing over
  that route and believes `(noted chi cat)`, as the short-route-first order believes it.

  The second is a pair of routes that **tie** on generality, where the shorter one is
  named:

  ```
  CxUniverse   (largerThan dog cat)  (transitiveInArgInverse largerThan 1 genl)
               forward rule (largerThan ?x ?y) ⇒ (noted ?x ?y)
   └─ CxA      (genl chi dog)  and  (genl chi mid) (genl mid dog)   both routes
        └─ CxB (not (genl chi dog))  :monotonic
  ```

  Both routes lie in CxA, so the one-edge route is the witness and `(noted chi cat)` is
  stored in CxA. CxB is the vantage of the clash over that edge, and reaches `chi` up to
  `dog` over the two-edge route, so it reads the justification over that route.

  Replacement stops at two places, each of which changes what is stored and not what is
  believed. An older
  route with an edge OUT is kept, so an edge defeated and then revived leaves the firing
  with the route it had and the route the re-derivation named. And the equality a
  descended `functional` or `anti_symmetric` mark derives keeps the route it first named:
  a pair already merged is not derived again, so a later shorter route adds no
  justification to replace it with.

  **Routes stated in sibling contexts are each named, and none is re-derived.** The
  witness searches return every route no other route covers — a route covers another
  when each of its asserting contexts is seen from one of the other's — and the join
  makes a firing of each ([inherit.md](inherit.md), "Placement follows the reasons";
  [contexts.md](contexts.md#the-consumers-and-what-each-of-them-may-reach) for a
  subsumed match). Two contexts neither of which sees the other cannot rank their
  routes, and each route places the conclusion in a reader the other does not reach:

  ```
  CxUniverse   (aRel high val)  (transitiveInArgInverse aRel 1 genl)
               forward rule (aRel ?x ?y) ⇒ (noted ?x ?y)
   ├─ CxA      (genl low mid) (genl mid high)
   ├─ CxB      (genl low high)
   └─ CxD      sees CxA and CxB
  ```

  `(noted low val)` is stored in CxA over the CxA route and in CxB over the CxB route,
  whichever arrived first, and a knock of a CxA edge — at CxA or scoped to CxD — leaves
  CxB's firing and CxD's reading of it standing. The four rows of the table above apply
  to each route alone: a knock takes the path one firing names, and a reader that still
  reaches over the same route's other supporters reads the firing as described.
  `second_route_test` builds these shapes in every order, with and without each knock, and
  [defenses.md](defenses.md#routes-in-sibling-contexts-each-carry-a-firing) gives why one
  named sibling route would not do.

  A reader that reads a firing over a second route stores nothing, so lifting the defeat
  or the `except` leaves the store as it was. The covering test that decides which routes place a firing leaves a
  surplus of the same kind, a firing placed below another it is read beside, in a lattice
  that splits one route across sibling contexts
  ([defenses.md](defenses.md#routes-in-sibling-contexts-each-carry-a-firing) gives the
  shape and its count).
