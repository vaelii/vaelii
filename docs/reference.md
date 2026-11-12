# What belief is: the reference semantics

- **Covers:** belief defined as a function of the stored premises and a context, with no
  region, memo, budget or pass; the invariants that definition holds every world to; the
  decisions on the questions the other pages left open; the fragment of the engine the
  definition covers; and the harness that holds the engine to it.
- **Not here:** how a settle computes belief, and what each step costs →
  [nmtms.md](nmtms.md); the state a settle keeps between writes and the write events that
  retire each part → [caches.md](caches.md#the-derived-state-register); why a decision is
  shaped the way it is → [defenses.md](defenses.md); what a context sees →
  [contexts.md](contexts.md).
- **Assumes:** sentex, context, premise, justification, defeat-class, nogood, vantage →
  [glossary.md](glossary.md).

A settle maintains belief incrementally, through the justification network and the
standing state [caches.md](caches.md#the-derived-state-register) registers, each part with
the write events that retire it. This page states the function that state approximates.
`vaelii.ref.believe` and `vaelii.ref.nogoods` implement it, by brute force, in the test
tree.

## The function

`believed?(W, S, C)` holds when sentence `S` is believed at context `C`, given a world `W`.
The engine is held to this predicate. The predicate is computed when asked, and it is
local: it reads the supports of `S` and the nogoods `S` could be a member of, and every
family keys those nogoods by the arguments of `S`. Negation keys on the body of `S`,
`disjoint` and `covering` on the individual of a membership, `functional` and
`functionalInArg` on the predicate and the positions the mark does not determine,
`irreflexive` and `anti_symmetric` on the argument pair of the tuple, `anti_transitive` on
each argument `S` shares with another step, `negates` on the argument list of the tuple,
and the inherited family on the predicate and the arguments outside the preserved
position. The set `believed(W, C)` of every `S` with `believed?(W, S, C)` is the
enumeration a spec over a small world uses.

**A world is a set of premises.** Each premise is a sentence, a context and a strength:
a ground fact, a denial `(not S)`, a `genl` or `genlCx` edge, a declaration, or a rule.
A world holds the writes offered to a KB, whether or not the engine stored them
(invariant 3), and never what the KB derived. Two premises of one sentence in one context
are one premise at the stronger of the two strengths
([nmtms.md](nmtms.md#strengths-and-the-defeat-class-vaeliiimplstrength)). The order the
premises arrived in is not part of the world.

`believed(W, C)` is the least fixpoint of the following definitions, taken together.

```
up(C)              = C and every context C reaches over the stored genlCx edges
visible(C)         = the premises of W whose context is in up(C)
forced(C)          = the baseline forced-monotonic set and every P a (forced_monotonic_predicate P)
                     in visible(C) declares, unless an except at C hides the
                     declaration or a defeat at C names it, decided over the baseline
                     set alone
derived(C, O)      = the closure of visible(C) − O under the rules in
                     visible(C) and under argument preservation
believed(W, C)     = derived(C, O*), where O* is the least O closed under the decisions below
believed?(W, S, C) = S is in believed(W, C)
```

1. **Visibility.** `up(C)` is reflexive and transitive. A context no `genlCx` edge names
   sees itself and CxUniverse, the implicit root
   ([contexts.md](contexts.md#cxuniverse-is-the-implicit-root)). `up(C)` reads the stored
   edges and the implicit edge alone, whatever context stores them, and does not depend on belief (invariant 1).
2. **Taxonomy.** At `C`, `A` is a subtype of `B` when a chain of `genl` edges, each
   believed at `C`, leads from `A` to `B`; every type is a subtype of itself and of
   `thing`. The closure reads only edges `C` believes
   ([taxonomy.md](taxonomy.md#reads-are-scoped-by-the-asking-context)). A `covering`,
   `separating` or `partition` declaration states a `genl` edge from each part to the
   whole ([taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it)).
3. **Derivation.** A rule visible at `C` fires on sentences believed at `C`. An antecedent
   `(T ?x)` matches `(S x)` when `S` is a subtype of `T` at `C`, unless no path of
   `:monotonic` edges leads from `S` to `T` there and a member believed at `C` convicts
   `(T x)`: `(not (T x))`, a membership `(R x)` whose type reaches the other side of a
   `(disjoint T B)` over `:monotonic` edges, or for each part of a `(covering T …)` a
   denial of a type the part reaches so or such a separated membership. The member
   undercuts the edge's reading at either strength
   ([inference.md](inference.md#an-edges-reading)). The derivation repeats until the
   members it reads are the members it believes. An antecedent also
   matches a claim reached by argument preservation
   ([inherit.md](inherit.md#forward-chaining-on-a-claim-nobody-stored)). The rules are
   evaluated stratum by stratum over the rule dependency graph, which the engine keeps
   acyclic through negation by refusing a rule set that is not
   ([exceptions.md](exceptions.md#stratification)). An `(unknown S)` antecedent blocks a
   binding under which `S` holds, and an `(exceptWhen E R)` blocks every binding of `R`
   under which all of `E` holds. Both are judged over the lower strata's result, without
   backward chaining, and a question with no answer does not block
   ([exceptions.md](exceptions.md#semantics), [naf.md](naf.md#in-a-rule-antecedent)).
   The question is asked at `C`, so a fact only `C` sees blocks the conclusion at `C`
   (decision 4).
4. **Inherited claims.** An inherited claim `(P … sub …)` is believed at `C` when a
   believed `(transitiveInArgInverse P k genl)`, a believed general claim `(P … sup …)`
   and every `genl` edge on some route from `sub` to `sup` are believed at `C`, and no
   believed denial of the claim undercuts that reading (decision 5). A denial undercuts a
   reading of class `:default`; against a `:monotonic` reading it forms the inherited
   nogood of item 6 instead ([inherit.md](inherit.md)). Nothing stores an inherited claim.
5. **Classes.** A premise holds at its strength. A firing confers the weakest of its
   rule's defeasibility (`:monotonic` for a bare rule, `:default` for a
   `set/defaultRule`), its antecedents' classes, and the `genl` edges it rests on; a
   `genlCx` edge caps nothing (invariant 1). A firing whose rule has an `unknown`
   antecedent or an `exceptWhen` confers `:default` (invariant 9). The rule's own write
   strength is not in that minimum
   ([nmtms.md](nmtms.md#strength-propagates-from-the-antecedents)). The `genl` edges are
   read over the path whose weakest edge is strongest
   ([defenses.md](defenses.md#the-subsumption-path-is-the-widest-bottleneck-not-the-shortest-route)),
   and an inherited claim takes the same widest bottleneck: the maximum over its routes
   of the minimum class along each (decision 9). A sentence's class at `C` is the
   strongest class over its supports at `C`.
6. **Nogoods.** A nogood at `C` is a set of members, all believed at `C`, that cannot all
   hold, plus the declarations and edges the conviction reads (its grounds), all believed
   at `C`. Each family is one sentence:
   - **negation**: `S` and `(not S)`, members both
     ([nmtms.md](nmtms.md#soft-prioritized-contradictions-the-settle-layer));
   - **`disjoint`**: `(T1 x)` and `(T2 x)` where `T1` and `T2` reach, over `:monotonic`
     edges at `C`, two types a believed `(disjoint A B)` separates; grounds the declaration
     and the `genl` edges ([taxonomy.md](taxonomy.md#disjointness)). A climb over a
     `:default` edge is an edge reading the other member undercuts (decision 3);
   - **`functional`** and **`functionalInArg`**: two tuples of one predicate that agree
     on every position but the determined one and differ there, symbols or not, under a
     believed mark on that predicate or one above it; grounds the mark (decision 6)
     ([taxonomy.md](taxonomy.md#predicate-metadata));
   - **`irreflexive`** and **`anti_symmetric`**: a self tuple `(Q a a)`, one member, or a
     converse pair `(Q1 a b)` and `(Q2 b a)` with `a` distinct from `b`, two members,
     under a believed mark on that predicate or one above it; grounds the mark
     (decision 7);
   - **`anti_transitive`**: `(P a b)`, `(P b c)` and `(P a c)`, three members
     ([nmtms.md](nmtms.md#a-nogood-is-a-set-anti_transitive-has-three-members));
   - **`negates`**: two tuples of one argument list, `(Q1 a …)` and `(Q2 a …)`, with one
     side of a believed `(negates P R)` above each functor, or one tuple whose functor is
     below both sides; grounds the declaration and the predicate `genl` edges
     ([taxonomy.md](taxonomy.md#predicate-metadata));
   - **`covering`**: `(S x)` with `S` reaching `W` over `:monotonic` edges, and a denier of
     every part `A` of a believed `(covering W A …)`: a believed `(not (A x))`, or a
     believed membership `(S' x)` of another type a believed `disjoint` separates from `A`
     with every `genl` edge on both sides `:monotonic`; grounds the declaration, the
     `disjoint` and the `genl` routes
     ([taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it));
   - **related types**: a believed `(disjoint A B)` where `A` reaches `B` through `genl`
     at `C`, or the reverse, and the believed edges of one route between them, members
     all, one nogood per route; a believed `covering` naming a part that a believed
     `disjoint` separates from its whole, and that `disjoint`, two members
     ([nmtms.md](nmtms.md#declarations-over-related-types));
   - **inherited**: a stored `(not (P … A …))` beside a claim `(P … W …)` that a believed
     `(transitiveInArgInverse P n genl)` carries down a `genl` path from `W` to `A`, when
     every part of that reading is `:monotonic`; the members are the denial, the general
     claim, the declaration and each edge of the path, and a reading with a `:default`
     part is undercut and forms no nogood
     ([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).
     A stored membership `(S A)` of a unary `P`'s argument denies the reached `(P A)` the
     same way when a believed `(disjoint T1 T2)` separates `P` and `S` at `C`; its grounds
     are the declaration and the `genl` edges up to the separated types.

   The grounds of a definitional family are read through and never weighed. The inherited
   family is the one whose reasons are members
   ([nmtms.md](nmtms.md#what-qualifies-as-a-nogood)).
7. **Decision.** Read each member's class at `C`, and weigh the members outside `forced(C)`
   alone: a forced-monotonic member is never a loser
   ([nmtms.md](nmtms.md#the-forced-monotonic-set)). A member that is the denial `(not S)`
   of a member `S` on `forced(C)` goes OUT at `C` at either class. Otherwise a unique
   weakest weighed member at `:default` goes OUT at `C`. Two or more weighed members tied
   at `:default` are a dilemma, and every member stays believed. No weighed member at
   `:default` is a hard clash, and every member stays believed
   ([nmtms.md](nmtms.md#soft-prioritized-contradictions-the-settle-layer)); the clash is
   stored and reported, never refused (invariant 3). An all-`:monotonic` `functional`,
   `functionalInArg` or `anti_symmetric` nogood over two symbols is a merge, and every
   member stays believed (invariant 4). Defeat-class is the only axis
   ([nmtms.md](nmtms.md#there-is-no-second-axis)).
8. **The OUT set.** `O` starts empty. Each round recomputes `derived(C, O)`, finds the
   nogoods over it, decides each, and adds each nogood's loser to `O`. A round that
   defeats a ground applies those defeats first and alone. The rounds stop at the first
   round that adds nothing, and no round removes from `O` (decision 2). The engine reaches
   the same set without rounds: the settle places each nogood's `defeat`, and a read
   applies the defeats over the asked sentence's support
   ([nmtms.md](nmtms.md#why-a-read-runs-no-rounds)).

**Per-context computation turns four properties into consequences of the definition.**
Context scoping holds because nothing outside `up(C)` is an input to `believed(W, C)`.
Belief filtering holds because every read inside the definition (a match, a subtype test,
a class, a nogood member) reads `derived(C, O)`, and nothing reads a stored-but-OUT
sentence. Order independence holds because `W` is a set and the definition has no step
that picks one of several equals: a tie is a dilemma, and nothing is chosen. Locality
holds as a bound on dependence: a premise in context `X` can move belief only at the
contexts whose `up` holds `X`. The reference holds these properties by construction, so a
disagreement between it and the engine is a defect in the engine.

### Decisions

Each entry states the question, the decision, and the invariant or the section of another
page that holds it.

1. **Whose belief of a `genlCx` edge decides `up(C)`?** Nobody's: `up(C)` reads the stored
   edges (invariant 1). Section: [contexts.md](contexts.md#genlcx-the-context-hierarchy).
2. **Does a defeat decided in round 1 stand when its ground goes OUT in a later round?**
   Yes. The OUT set grows round by round, a defeat that withdraws a ground is applied
   first and alone, and the rounds are the semantics while the pass count is not. The
   engine places each nogood with the verdict the network's classes give, and a placed
   sentex rests on the grounds its verdict read, so a `defeat` of a ground hides what
   rests on that ground where the defeat is in force. A settle's answer does not depend on
   its pass count ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)).
3. **Does a verdict bind a context below its vantage that reads the clash released?**
   No. Each context decides from its own view: a context that sees what the vantage sees
   reaches the vantage's verdict, and a context that sees a denial or an edge dissolving
   the clash believes what the vantage hides. The engine places the `defeat` at the
   vantage, where it hides the loser there and below; a denial or an edge a context below
   sees places its own `defeat` of the ground there, which hides the vantage's placement
   ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)).
4. **Is an `exceptWhen` or `unknown` question asked from `C` or from the conclusion's
   placement context?** From both. The question is asked at the placement context when
   the justification is made. Where it holds below the placement, the firing places a
   guard defeat where a firing over the placement, the blockers and the `genl` edges the
   query climbed is placed, and at the context of each `except` that takes a blocker's
   own defeat out of force; a reader that sees the defeat does not believe the conclusion
   through that firing, which equals asking at `C`
   ([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)). A blocker the
   placement context sees and a context below does not believe still blocks the firing
   there.
5. **Is a claim reached by argument preservation a member of `believed(W, C)`?** Yes, as
   item 4 of the definition derives it, at the class decision 9 gives. The engine answers
   such a claim through `core/ask?`
   ([inherit.md](inherit.md#forward-chaining-on-a-claim-nobody-stored)).
6. **Is a `functional` clash between two symbol fillers a nogood?** Yes, unless every
   member is `:monotonic`, which is a merge (invariant 4). Section:
   [taxonomy.md](taxonomy.md#predicate-metadata).
7. **What does the reference do with `irreflexive` and `anti_symmetric`?** Both marks are
   forced-monotonic (invariant 2), and a violation of either is a nogood the settle places
   and decides like any other (decision 16). A converse pair of two symbols whose members
   are both `:monotonic` merges (decision 6). Section:
   [taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order).
8. **Is `W` the writes offered or the writes stored?** Offered: no clash is refused
   (invariant 3). Section: [nmtms.md](nmtms.md#1-order-independence), which claims order
   independence over what was stored.
9. **Which path caps a derivation's class?** The widest bottleneck: the maximum over
   routes of the minimum class along each route, for a derivation and for an inherited
   claim. A `genlCx` path caps nothing (invariant 1). Section:
   [nmtms.md](nmtms.md#strength-propagates-from-the-antecedents).
10. **Can a `genl` edge between two predicates be `:default`, denied or derived?** It is
    forced-monotonic (invariant 5): a `:default` write keeps its strength and is never a
    loser, a denial loses to it at either strength, and it is derived only from
    forced-monotonic antecedents (decision 17). A `genl` between types stays defeasible,
    so a type edge admits exceptions. Section:
    [taxonomy.md](taxonomy.md#predicate-metadata).
11. **Can a definitional declaration be `:default`, denied or derived?** `orthogonal`
    and the arity bindings are forced-monotonic (invariant 6), so each goes OUT only by
    retraction. A tuple that breaks its arity binding is held inert in the `:out` forced
    set at every context and forms no nogood ([taxonomy.md](taxonomy.md#arity)). A
    separation (`disjoint`, `covering`, `partition`, `sibling_disjoint`,
    `siblingDisjointException`) may be `:default`, denied or derived. It keeps its written
    strength, a stronger denial defeats it at the denial's vantage, and a membership
    nogood resting on it is hidden where that defeat is in force. Sections:
    [taxonomy.md](taxonomy.md#disjointness) and
    [taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order).
12. **Can an `except` be derived or defeated?** No (invariant 7). An `except` that targets
    an `except` still hides it. The reference leaves `except` outside v1. Section:
    [contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree).
13. **Can a merge be defeated?** No (invariant 8). A defeasible identity is written with a
    predicate that does not merge. The reference leaves equality outside v1. Section:
    [equality.md](equality.md#what-a-merge-does).
14. **What class does a firing through `unknown` or `exceptWhen` confer?** `:default`,
    whatever the classes of the rule and of the other antecedents, because the
    conclusion goes OUT when a blocker arrives (invariant 9). A sentence first believed
    after a defeat through such a rule is therefore `:default` and cannot defeat a
    `:monotonic` member, which bounds the rounds. Sections:
    [nmtms.md](nmtms.md#strength-propagates-from-the-antecedents) and
    [naf.md](naf.md#in-a-rule-antecedent).
15. **Does a caller choose whether a clash is refused?** No. `assert` takes no
    `:constraints` option, and no walk reads a clash's grounds at the entry point: the
    engine stores a clash, decides it and reports it (invariant 3), and a caller reads
    `conflicts` for a hard clash
    ([defenses.md](defenses.md#a-definitional-clash-is-stored-not-refused)).
16. **Is a nogood decided when a settle runs, or when a reader asks?** Placed when a
    settle runs, applied when a reader asks. The settle places each nogood at its vantages
    with the verdict the network's classes give: a `contradicts`, and for a unique weakest
    member its `defeat`. A read at `C` applies the defeats in force at `C` by a walk over
    the asked sentence's support. Two reads stay per reader: whether two fillers are one
    equality class, and which arity bindings bind a functor. The justification network
    keeps support labels (`:in`) alone, and a placed `defeat` moves no label
    ([nmtms.md](nmtms.md#a-nogood-placed-as-a-conclusion)).
17. **Can a rule conclude a forced-monotonic predicate?** Only from forced-monotonic
    antecedents. No rule is refused for its consequent, since a refusal would make the
    stored set depend on whether the forced-monotonic declaration or the rule arrived
    first. A rule whose antecedents are all forced-monotonic literals, with no `unknown`,
    `exceptWhen` or `set/defaultRule`, keeps the strength it was written at, and its
    conclusion is an ordinary belief at its antecedents' class, never a loser;
    `core.txt`'s `injection`, `surjection` and `bijection` rules are the case. Each firing
    of any other rule whose conclusion is a forced-monotonic literal or its denial is
    stored and held void, `core/violations` reads a `:forced-conclusion` entry for it, and
    `why-not` on its conclusion names the antecedent predicates that are not
    forced-monotonic. A declaration stated in any context puts its predicate on `forced(C)`
    at the contexts `C` that see it and believe it and at no other, so the verdict, the
    denial's defeat and the forced-monotonic rule all follow the reader; the reader decides
    a declaration's own defeat over the baseline set alone (`exc/forced-state`). A
    declaration's retraction gives back the belief a KB that never held it has. In v1,
    `vaelii.ref.believe` reads every declaration in `visible(C)`, since v1 admits no
    `except` and no denial of a declaration, and `vaelii.ref.world/inert-write?` reads a
    rule concluding a forced-monotonic literal as inert, since a v1 antecedent is never
    one. Sections: [nmtms.md](nmtms.md#the-forced-monotonic-set) and
    [taxonomy.md](taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches).

## Invariants the reference states

The world check reads every `genlCx` write `:monotonic`, leaves every other
forced-monotonic write at its strength, and sets every inert write aside
(`vaelii.ref.world/inert-write?`: a rule decision 17 makes inert), so no world breaks
invariant 1, 2, 5 or 6, and no write the forced-monotonic set rules out is refused. The
members of the forced-monotonic set and the mechanism that holds each are
[nmtms.md](nmtms.md#the-forced-monotonic-set)'s table.

1. **`genlCx` is universal and monotonic.** A `genlCx` edge holds at every context
   whatever context stores it, every write of one is `:monotonic` whatever strength
   it was written at, and a `(not (genlCx …))` loses to a believed edge and removes none,
   so `up(C)` is a function of the stored edges.
2. **The relation marks are forced-monotonic.** `irreflexive`, `anti_symmetric`,
   `asymmetric`, `functional`, `functionalInArg`, `anti_transitive` and `negates` are on
   the forced-monotonic set beside `genlCx`, and invariants 5 to 8 extend it. A write of a
   forced-monotonic predicate keeps the strength it was written at and is never the loser
   of a nogood, and a denial of one is believed until the literal it denies is, and is then
   the loser of their negation nogood at either strength (item 7). A mark's reach, the
   sub-predicates it convicts through predicate `genl`, is the stored edges visible at
   `C`, since under invariant 5 those edges are never OUT. A nogood's verdict reads its
   members' classes alone, and the predicate `genl` edges a mark's route climbs are its
   grounds, so no edge's class caps a violation.
3. **No clash is refused.** `W` is the writes offered, and the reference judges every
   one of them. A hard clash is stored and reported, as a `:monotonic` `S` beside
   `(not S)` is. A refusal remains only where it reads the sentence alone: naming (which
   reads the sentence's own argument count), groundness and the v1 fragment. A clash that
   reads other stored content, such as `(disjoint a b)` over two `genl`-related types,
   is stored and placed as a nogood (`checks/refuses-assert?`). A tuple an
   `irreflexive` or `anti_symmetric` mark convicts, or whose length breaks its predicate's
   arity binding, is stored for the settle to place as a nogood. A `disjoint` over
   `genl`-related types is a nogood of the declaration and the `genl` edges of one route
   relating its arguments, and a cover naming a part a `disjoint` separates from its
   whole is a two-member one of the cover and the `disjoint`
   ([nmtms.md](nmtms.md#declarations-over-related-types)).
4. **A merge needs monotonic evidence on every side.** A `functional` or
   `functionalInArg` collision between two symbol fillers, or an `anti_symmetric`
   converse pair of symbols, merges the two terms only when every member is
   `:monotonic`. Otherwise the collision is a nogood: the unique weakest member loses,
   and a tie at `:default` is a dilemma. The reference gives the all-`:monotonic` pair the
   verdict `:merge` and leaves equality outside v1, so the harness skips the belief
   comparison at a context holding one and compares the pairs it merges with the pairs
   the engine's equality holds there (`vaelii.ref.gen/merge-disagreements`, the kind
   `:merge-differs`).
5. **A `genl` edge between predicates is forced-monotonic.** A `(genl P Q)` whose two
   arguments are camelCase predicates is never a loser whatever strength it was
   written at, its denial loses to it, and it is derived only from forced-monotonic
   antecedents (decision 17). `vaelii.ref.world/predicate-genl?` reads the spelling. The
   engine reads such an edge forced-monotonic under `core.txt`'s
   `(forced_monotonic_between_predicates genl)`, so a merge `special/equate-under-edge`
   derives over such an edge, and a claim `discovery/preserving-moves` re-opens through
   it, move only when the edge is stored or retracted.
6. **An arity binding is forced-monotonic, and a separation is not.** `arity` is never a
   loser, a denial of it loses to it, and it is derived only from forced-monotonic
   antecedents, so it goes OUT only by retraction. An `arity` violation is a one-member
   nogood with the declaration as its ground, and two predicates a `genl` edge relates
   whose bindings differ are a hard clash ([taxonomy.md](taxonomy.md#arity)). `disjoint`,
   `covering`, `partition`, `sibling_disjoint` and `siblingDisjointException` keep their
   written strength. Each is a defeasible ground of the membership nogood, as a type
   `genl` edge is, and the membership verdict weighs the memberships alone. A separation
   loses as a member: beside its denial, or in a related-types nogood with the `genl`
   edges or the cover it clashes with (invariant 3). v1 admits `disjoint` and
   `covering`; `partition`, `sibling_disjoint` and `arity` stay outside it.
7. **`except` is forced-monotonic.** An `except` is asserted and retracted, derived only
   from forced-monotonic antecedents and never defeated, and an `except` that targets an
   `except` still hides it. `except` is outside v1. No settle resolution defeats an
   `except`, so the settle watches no `except` for a belief flip.
8. **Equality is monotonic.** A `rewriteOf`, `sameAs` or `equals` merge rests only on
   `:monotonic` evidence, is never defeated, and is undone only by retracting a premise
   it rests on. Equality is outside v1 ([equality.md](equality.md#what-a-merge-does)).
9. **A guarded firing confers `:default`.** A firing whose rule has an `unknown`
   antecedent or an `exceptWhen` confers `:default` on its conclusion, whatever the
   classes of the rule and of the other antecedents. The engine records `:default` as a
   guarded firing's justification strength, and the strength follows an `exceptWhen` that
   arrives or leaves after the firing
   ([nmtms.md](nmtms.md#strength-propagates-from-the-antecedents)).

## What the engine has to equal

A settle is an incremental computation of `believed(W, C)` for every context at once.
It reads a region, memos, budgets and passes, and none of them may change the answer: a
settle that differs from the function on any world and any context is wrong, whatever its
tests say, unless the difference is a known divergence below. `vaelii.reference-test`
is the witness. It loads random small worlds in every arrival order into fresh KBs and
compares the engine's belief at each context with the reference's, sentence by sentence:
a stored sentence through `core/believed?` on its handle, and an inherited claim, which
has no handle, through `core/ask?` at the context. A handle that holds only as an edge
reading stores a subsumption answer, which the function reads through item 3 alone, and
is not compared. A context whose view holds a merge
verdict is not compared, and the harness counts it. The first order's KB is also closed,
recovered and compared again.

**Every disagreement has a kind.** `gen/check-world` classifies each disagreement by the
shape of the minimal shrunk world, and a disagreement it cannot classify is
`:unclassified`. `vaelii.reference-test`'s `known-divergences` map names each known kind
with the decision it departs from, and is empty. The test fails on a kind outside the
map, `:unclassified` included, and counts and prints every known one. A write
the engine refuses and the reference stores is an `:engine-refused-other` divergence: the
reference judges `W` as offered, the engine side is read without the refused write, and
the run is reported under that divergence rather than as a belief disagreement.

## The fragment

v1 of the reference covers the rows marked yes. A KB holding a row marked no is refused
by the world extractor with `:unsupported`, so the generator cannot produce one.

| feature | in v1 | where the engine documents it |
|---|---|---|
| ground facts and denials, `:monotonic` and `:default` | yes | [nmtms.md](nmtms.md#strengths-and-the-defeat-class-vaeliiimplstrength) |
| `genl` between types, rooted at `thing` | yes | [taxonomy.md](taxonomy.md#genl-the-type-hierarchy) |
| `genlCx`, acyclic, `:monotonic` | yes | [contexts.md](contexts.md#genlcx-the-context-hierarchy) |
| `genlCx` at `:default` | yes, held `:monotonic` (invariant 1) | [contexts.md](contexts.md#genlcx-the-context-hierarchy) |
| forward `implies` with `and` bodies and variables | yes | [inference.md](inference.md) |
| `unknown` in a rule antecedent | yes | [naf.md](naf.md) |
| `exceptWhen` | yes | [exceptions.md](exceptions.md) |
| negation nogoods | yes | [nmtms.md](nmtms.md#soft-prioritized-contradictions-the-settle-layer) |
| `disjoint` | yes, defeasible (invariant 6) | [taxonomy.md](taxonomy.md#disjointness) |
| `functional`, `functionalInArg` | yes, symbol fillers included, except the all-`:monotonic` merge (invariant 4) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| `irreflexive`, `anti_symmetric` | yes, as nogoods (invariant 2) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| a `:default` write of a mark or a predicate `genl` | yes, kept `:default` and never a loser (invariants 2 and 5) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| a denial of `genlCx`, a mark or a predicate `genl` | yes, believed, and defeated at either strength beside the literal it denies (invariants 1, 2 and 5) | [nmtms.md](nmtms.md#the-forced-monotonic-set) |
| a denial of `disjoint` or `covering` | yes, a negation nogood weighed as any other: a `:monotonic` denial defeats a `:default` separation, and two `:default` sides are a dilemma (invariant 6) | [taxonomy.md](taxonomy.md#disjointness) |
| a rule concluding a forced-monotonic predicate | yes, its firings stored and held void (decision 17) | [taxonomy.md](taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches) |
| `anti_transitive` | yes | [nmtms.md](nmtms.md#a-nogood-is-a-set-anti_transitive-has-three-members) |
| `negates` | yes, as nogoods over two tuples; a declaration's length clash is not modelled | [taxonomy.md](taxonomy.md#predicate-metadata) |
| `covering` | yes, defeasible (invariant 6) | [taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it) |
| `transitiveInArgInverse` along `genl`, one position | yes, decision 5 | [inherit.md](inherit.md) |
| equality: `rewriteOf`, `sameAs`, `equals` | no | [equality.md](equality.md) |
| supersession | no | [equality.md](equality.md), [nmtms.md](nmtms.md#the-set-membership-states-a-node-can-hold) |
| visibility `except` | no | [contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree) |
| argument types, mints, lifts | no | [argtypes.md](argtypes.md), [contexts.md](contexts.md#decontextualized_predicate-a-fact-that-belongs-to-the-kb-not-to-one-theory) |
| generators (rules concluding rules) | no | [generators.md](generators.md) |
| backward-only rules | no | [inference.md](inference.md) |
| the qualitative calculi | no | [qcn.md](qcn.md) |
| NATs | no | [nat.md](nat.md) |
| quantities | no | [quantity.md](quantity.md) |
| `disjoint_metatype`, `sibling_disjoint` | no; `sibling_disjoint` is defeasible (invariant 6) | [taxonomy.md](taxonomy.md#disjointness) |
| `partition`, `separating` | no; `partition` is defeasible (invariant 6) | [taxonomy.md](taxonomy.md#partition-and-separating-add-no-separation-mechanism-of-their-own) |
| `arity` | no; forced-monotonic, and a tuple breaking a binding is inert (invariant 6) | [taxonomy.md](taxonomy.md#arity) |
| the ASP solver | no | [asp.md](asp.md), [labeling.md](labeling.md) |
| `asymmetric` | yes, as the `asymmetric` family; forced-monotonic (invariant 2) | [inherit.md](inherit.md#asymmetric-p) |
| `genl` between predicates of arity 2 or more | yes, forced-monotonic (invariant 5); the generator writes none | [taxonomy.md](taxonomy.md#predicate-metadata) |

## What the reference does not tell you

The reference says what belief is and never how fast a settle reaches it. It recomputes
every context from every premise on every call, which is the cost locality exists to
avoid. The cost contract of a settle, step by step, with the check that enforces each
bound, is [nmtms.md](nmtms.md#the-runtime-of-a-settle).
