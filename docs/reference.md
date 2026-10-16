# What belief is: the reference semantics

- **Covers:** belief defined as a function of the stored premises and a context, with no
  region, memo, budget or pass; the invariants that definition holds every world to; the
  decisions on the questions the other pages left open; the fragment of the engine the
  definition covers; and the standing state a settle keeps between settles, with what
  invalidates each part of it.
- **Not here:** how a settle computes belief, and what each step costs →
  [nmtms.md](nmtms.md); why a decision is shaped the way it is →
  [defenses.md](defenses.md); what a context sees → [contexts.md](contexts.md).
- **Assumes:** sentex, context, premise, justification, defeat-class, nogood, vantage →
  [glossary.md](glossary.md).

A settle maintains belief incrementally, through the justification network and about thirty
standing caches, each with an invalidation rule of its own. This page states the function
those caches approximate. `vaelii.ref.believe` and `vaelii.ref.nogoods` implement it, by
brute force, in the test tree.

## The function

`believed?(W, S, C)` holds when sentence `S` is believed at context `C`, given a world `W`.
The engine is held to this predicate. The predicate is computed when asked, and it is
local: it reads the supports of `S` and the nogoods `S` could be a member of, and every
family keys those nogoods by the arguments of `S`. Negation keys on the body of `S`,
`disjoint` and `covering` on the individual of a membership, `functional` and
`functionalInArg` on the predicate and the positions the mark does not determine,
`irreflexive` and `anti_symmetric` on the argument pair of the tuple, `anti_transitive` on
each argument `S` shares with another step, and the inherited family on the predicate and
the arguments outside the preserved position. The set `believed(W, C)` of every `S` with
`believed?(W, S, C)` is the enumeration a spec over a small world uses.

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
roster(C)          = the global roster and every P a (forced_monotonic_predicate P)
                     in visible(C) declares, unless an except at C hides the
                     declaration or a defeat at C names it, decided over the global
                     roster alone
inert(C)           = the denials in visible(C) of a literal on roster(C)
derived(C, O)      = the closure of visible(C) − inert(C) − O under the rules in
                     visible(C) and under argument preservation
believed(W, C)     = derived(C, O*), where O* is the least O closed under the decisions below
believed?(W, S, C) = S is in believed(W, C)
```

1. **Visibility.** `up(C)` is reflexive and transitive. A context no `genlCx` edge names
   sees only itself, with no implicit root
   ([contexts.md](contexts.md#a-context-outside-the-topology)). Every `genlCx` edge is
   `:monotonic` and a denial of one is inert (invariant 1), so `up(C)` reads the stored
   edges alone, whatever context stores them, and does not depend on belief.
2. **Taxonomy.** At `C`, `A` is a subtype of `B` when a chain of `genl` edges, each
   believed at `C`, leads from `A` to `B`; every type is a subtype of itself and of
   `thing`. The closure reads only edges `C` believes
   ([taxonomy.md](taxonomy.md#reads-are-scoped-by-the-asking-context)). A `covering`,
   `separating` or `partition` declaration states a `genl` edge from each part to the
   whole ([taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it)).
3. **Derivation.** A rule visible at `C` fires on sentences believed at `C`. An antecedent
   `(T ?x)` matches `(S x)` when `S` is a subtype of `T` at `C`. An antecedent also
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
   believed `(transitiveInArgInverse P k genl)`, a believed general claim `(P … sup …)` and every
   `genl` edge on some route from `sub` to `sup` are believed at `C`, and no believed
   denial of the claim undercuts that reading (decision 5). A denial undercuts a reading
   of class `:default`; against a `:monotonic` reading it forms the inherited nogood of
   item 6 instead ([inherit.md](inherit.md)). Nothing stores an inherited claim.
5. **Classes.** A premise holds at its strength. A firing confers the weakest of its
   rule's defeasibility (`:monotonic` for a bare rule, `:default` for a
   `set/defaultRule`), its antecedents' classes, and the `genl` edges it rests on; a
   `genlCx` edge is `:monotonic` (invariant 1) and caps nothing. A firing whose rule has
   an `unknown` antecedent or an `exceptWhen` confers `:default` (invariant 9). The
   rule's own write strength is not in that minimum
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
   - **`disjoint`**: `(T1 x)` and `(T2 x)` where `T1` and `T2` are subtypes at `C` of two
     types a believed `(disjoint A B)` separates; grounds the declaration and the `genl`
     edges ([taxonomy.md](taxonomy.md#disjointness));
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
   - **`covering`**: `(W x)` and a denier of every part `A` of a believed `(covering W A
     …)`: a believed `(not (A x))`, or a believed membership `(S x)` of another type a
     believed `disjoint` separates from `A` with every `genl` edge on both sides
     `:monotonic`; grounds the declaration, the `disjoint` and the `genl` routes
     ([taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it));
   - **inherited**: a stored `(not (P … A …))` beside a claim `(P … W …)` that a believed
     `(transitiveInArgInverse P n genl)` carries down a `genl` path from `W` to `A`, when every
     part of that reading is `:monotonic`; the members are the denial, the general claim,
     the declaration and each edge of the path, and a reading with a `:default` part is
     undercut and forms no nogood
     ([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).
     A stored membership `(S A)` of a unary `P`'s argument denies the reached `(P A)` the
     same way when a believed `(disjoint T1 T2)` separates `P` and `S` at `C`; its grounds
     are the declaration and the `genl` edges up to the separated types.

   The grounds of a definitional family are read through and never weighed. The inherited
   family is the one whose reasons are members
   ([nmtms.md](nmtms.md#what-qualifies-as-a-nogood)).
7. **Decision.** Read each member's class at `C`, and weigh the members off `roster(C)`
   alone: a roster member is never a loser
   ([nmtms.md](nmtms.md#the-forced-monotonic-roster)). A unique weakest weighed member at
   `:default` goes OUT at `C`. Two or more weighed members tied at `:default` are a
   dilemma, and every member stays believed. No weighed member at `:default` is a hard
   clash, and every member stays believed
   ([nmtms.md](nmtms.md#soft-prioritized-contradictions-the-settle-layer)); the clash is
   stored and reported, never refused (invariant 3). An all-`:monotonic` `functional`,
   `functionalInArg` or `anti_symmetric` nogood over two symbols is a merge, and every
   member stays believed (invariant 4). Defeat-class is the only axis
   ([nmtms.md](nmtms.md#there-is-no-second-axis)).
8. **The OUT set.** `O` starts empty. Each round recomputes `derived(C, O)`, finds the
   nogoods over it, decides each, and adds each nogood's loser to `O`. A round that defeats a
   ground applies those defeats first and alone. The rounds stop at the first round that
   adds nothing, and no round removes from `O` (decision 2). The engine reaches the same
   set without rounds: the settle places each nogood's `defeat`, and a read applies the
   defeats over the asked sentence's support
   ([nmtms.md](nmtms.md#why-a-read-runs-no-rounds)).

**Per-context computation turns four properties into consequences of the definition.**
Context scoping holds because nothing outside `up(C)` is an input to `believed(W, C)`.
Belief filtering holds because every read inside the definition (a match, a subtype test,
a class, a nogood member) reads `derived(C, O)`, and nothing reads a stored-but-OUT
sentence. Order independence holds because `W` is a set and the definition has no step
that picks one of several equals: a tie is a dilemma, and nothing is chosen. Locality
holds as a bound on dependence: a premise in context `X` can move belief only at the
contexts whose `up` holds `X`. The engine maintains each of these properties by
mechanism, and the reference holds them by construction, so a disagreement between the
two is a defect in the engine.

### Decisions

Each entry states the question in one sentence, the decision, how the engine holds it,
and the section of another page that describes it. The `TODO(spec)` markers the
builders of `vaelii.ref.*` wrote are now citations of these decisions by number.

1. **Whose belief of a `genlCx` edge decides `up(C)`?** Nobody's: every `genlCx` edge is
   universal and `:monotonic`, and a denial of one is inert (invariant 1), so `up(C)`
   reads the stored edges. The engine holds it through invariant 1. Section:
   [contexts.md](contexts.md#genlcx-the-context-hierarchy).
2. **Does a defeat decided in round 1 stand when its ground goes OUT in a later round?**
   Yes. The OUT set grows round by round, a defeat that withdraws a ground is applied
   first and alone, and the rounds are the semantics while the pass count is not. Before
   decision 14, a round that re-decided every nogood from scratch had no fixpoint on this
   world, all in one context, which `resolve-at`'s docstring in `vaelii.ref.believe`
   cites:

   ```
   :default    (genl chi dog)  (chi Kit)
   :monotonic  (disjoint dog cat)  (cat Kit)  (pp Kit)
               (transitiveInArgInverse pP 1 genl)  (pP dog Bone)
               (set/forwardRule (implies (and (pp ?x) (unknown (chi ?x))) (not (pP chi Bone))))
   ```

   Round 1 takes `(chi Kit)` OUT and the rule fires. With the conclusion `:monotonic`,
   round 2 took the edge OUT, and a from-scratch round alternated between those two
   states. Under decision 14 the conclusion is `:default`, round 2 reads a dilemma
   between the conclusion and the `:default` edge, and both readings stop with
   `(chi Kit)` OUT. No v1 world is known on which the two readings differ under decision
   14, and the rounds stay the semantics. The engine places each nogood with the verdict
   the network's classes give, and a placed sentex rests on the grounds its verdict read,
   so a `defeat` of a ground hides what rests on that ground where the defeat is in force.
   A settle's answer does not depend on its pass count
   ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)).
3. **Does a verdict bind a context below its vantage that reads the clash released?**
   No. Each context decides from its own view: a context that sees what the vantage sees
   reaches the vantage's verdict, and a context that sees a denial or an edge dissolving
   the clash believes what the vantage hides. The engine places the `defeat` at the
   vantage, where it hides the loser there and below; a denial or an edge a context below
   sees places its own `defeat` of the ground there, which hides the vantage's placement.
   The network keeps the loser IN
   ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)).
4. **Is an `exceptWhen` or `unknown` question asked from `C` or from the conclusion's
   placement context?** From both. The question is asked at the placement context when
   the justification is made. Where it holds below the placement, the firing places a
   guard defeat where a firing over the placement, the blockers and the `genl` edges the
   query climbed is placed, and at the context of each `except` that takes a blocker's
   own defeat out of force; a reader that sees the defeat does not believe the conclusion
   through that firing, which equals asking at `C` ([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)). A
   blocker the placement context sees and a context below does not believe still blocks
   the firing there.
5. **Is a claim reached by argument preservation a member of `believed(W, C)`?** Yes, as
   item 4 of the definition derives it, at the class decision 9 gives. The engine
   answers such a claim through `core/ask?`, and holds it. Section:
   [inherit.md](inherit.md#forward-chaining-on-a-claim-nobody-stored) states the engine
   side and needs no change.
6. **Is a `functional` clash between two symbol fillers a nogood?** Yes, unless every
   member is `:monotonic`, which is a merge (invariant 4). The engine holds it
   ([taxonomy.md](taxonomy.md#predicate-metadata)).
7. **What does the reference do with `irreflexive` and `anti_symmetric`?** Both marks
   are on the forced-monotonic roster, never a loser and never coerced, and a violation of either is a nogood decided like any other
   (invariant 2). The engine places both as nogoods (decision 16,
   [nmtms.md](nmtms.md#the-nogood-families)), and a converse pair of two
   symbols whose members are both `:monotonic` merges (decision 6). Section:
   [taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order).
8. **Is `W` the writes offered or the writes stored?** Offered: no clash is refused
   (invariant 3). The engine holds it through invariant 3. Section:
   [nmtms.md](nmtms.md#1-order-independence), which claims order independence over what
   was stored.
9. **Which path caps a derivation's class?** The widest bottleneck: the maximum over
   routes of the minimum class along each route, for a derivation and for an inherited
   claim. The `genlCx` half of the question has no case left under invariant 1, which the
   engine holds. Section:
   [nmtms.md](nmtms.md#strength-propagates-from-the-antecedents).
10. **Can a `genl` edge between two predicates be `:default`, denied or derived?** No. A
    `(genl P Q)` whose two arguments are predicates of arity 2 or more, which their
    camelCase spelling decides ([naming.md](naming.md)), is on the forced-monotonic roster
    (invariant 5): a `:default` write keeps its strength and is never a loser, a denial is
    held OUT,
    and it is derived only from roster antecedents (decision 17). A `genl` between types stays defeasible, so a type edge admits
    exceptions. A mark's reach through predicate `genl` reads the stored edges and no
    belief. The engine holds it through invariant 5. Section:
    [taxonomy.md](taxonomy.md#predicate-metadata).
11. **Can a definitional declaration be `:default`, denied or derived?** No. `disjoint`,
    `covering`, `partition`, `sibling_disjoint`, `orthogonal`, `siblingDisjointException` and `arity` are on the forced-monotonic
    roster, never a loser and never coerced (invariant 6), a denial of one is held OUT and it is derived only from roster
    antecedents (decision 17), so a ground goes OUT only by retraction and no verdict is re-asked
    because its ground moved. Four spellings bind an arity and each is on the roster:
    `(arity P n)`, an exact-arity class membership, a `variable_arity` membership and
    `(arityMin P m)`; for that read, a `:monotonic` membership whose type reaches an
    exact-arity class through `:monotonic` `genl` edges binds as the class membership does,
    those edges standing at roster strength. An `arity` violation is a one-member nogood, the tuple,
    with the binding as its ground, placed as an `irreflexive` violation is (decision 16,
    [taxonomy.md](taxonomy.md#arity)). A
    defeasible disjointness is written as a `:default` rule concluding a denial, which
    forms a negation nogood. The engine holds it through invariant 6. Sections:
    [taxonomy.md](taxonomy.md#disjointness), [taxonomy.md](taxonomy.md#arity) and
    [taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order).
12. **Can an `except` be derived or defeated?** No. An `except` is asserted and
    retracted, derived only from roster antecedents and never defeated (invariant 7). An `except`
    that targets an `except` still hides it. The reference leaves `except` outside v1.
    The engine holds it through invariant 7. Section:
    [contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree).
13. **Can a merge be defeated?** No. `rewriteOf`, `sameAs` and `equals` are on the
    forced-monotonic roster, never a loser and never coerced (invariant 8): a merge rests only on `:monotonic` evidence (decision 6), is never
    defeated, and is undone only by retracting a premise it rests on. A defeasible
    identity is written with a predicate that does not merge. The reference leaves
    equality outside v1. The engine holds it
    ([equality.md](equality.md#what-a-merge-does)).
14. **What class does a firing through `unknown` or `exceptWhen` confer?** `:default`,
    whatever the classes of the rule and of the other antecedents, because the
    conclusion goes OUT when a blocker arrives (invariant 9). A sentence first believed
    after a defeat through such a rule is therefore `:default` and cannot defeat a
    `:monotonic` member, which bounds the rounds; decision 2's world is the case. The
    engine holds it through invariant 9. Sections:
    [nmtms.md](nmtms.md#strength-propagates-from-the-antecedents) and
    [naf.md](naf.md#in-a-rule-antecedent).
15. **Does a caller choose whether a clash is refused?** No. The `:constraints` option
    (`:refuse` and `:arbitrate`) is removed, with the walk that reads the class of a
    clash's grounds at the entry point. The engine stores a clash, decides it and reports
    it (invariant 3). A caller reads `conflicts` for a hard clash. The engine holds it:
    `assert` takes no `:constraints` option, and no walk reads a clash's grounds at the
    entry point. Section:
    [nmtms.md](nmtms.md#which-entry-point-the-content-came-through).
16. **Is a nogood decided when a settle runs, or when a reader asks?** Placed when a
    settle runs, applied when a reader asks. Every family's nogoods are found off the
    write-time candidate index or the inherited discovery, and the settle places each at
    its vantages with the verdict the network's classes give: a `contradicts`, and for a
    unique weakest member its `defeat`. A read at `C` applies the defeats in force at `C`
    by a walk over the asked sentence's support, and the two reads that stay per reader,
    whether two fillers are one equality class and which arity bindings bind a functor,
    are made there. Forward firings, the `genl` and `genlCx` closures, merges and mints
    stay at write time. An `unknown` or `exceptWhen` keeps its block at the placement
    context, with a guard `defeat` below it, and the refusal record and its cap stay. The
    justification network keeps support labels (`:in`) alone, and a placed `defeat` moves
    no label ([nmtms.md](nmtms.md#a-nogood-placed-as-a-conclusion)).
17. **Can a rule conclude a forced-monotonic predicate?** Only from roster antecedents.
    No rule is refused for its consequent, since a refusal would make the stored set
    depend on whether the roster declaration or the rule arrived first. A rule whose
    antecedents are all roster literals, with no `unknown`, `exceptWhen` or
    `set/defaultRule`, keeps the strength it was written at, and its conclusion is an
    ordinary belief at its antecedents' class, never a loser, which goes OUT only when a
    roster premise it rests on is retracted; `core.txt`'s `injection`, `surjection` and `bijection` rules are the case, and
    those three are on the roster. Any other rule is stored, and each firing whose
    conclusion is a roster literal or its denial is convicted: stored and held void, and
    `core/violations` reads a `:forced-conclusion` entry for it off the stored firing, and `why-not` on its conclusion names the
    antecedent predicates off the roster. A rule whose trigger is an ordinary membership
    concludes a roster literal once the trigger's predicate is declared
    `forced_monotonic_predicate`, as `organism.txt` declares `folk_species`
    ([nmtms.md](nmtms.md#the-forced-monotonic-roster)). The baseline
    declarations form the global roster, which every context reads; a declaration stated
    in any context, CxUniverse's included, puts its predicate on `roster(C)` at the contexts `C`
    that see it and believe it and at no other, so the verdict, the inert denial and the roster rule all follow the reader.
    The reader decides a declaration's own defeat over the global roster alone, so no
    declaration takes part in deciding whether a declaration is believed
    (`exc/roster-state`). `vaelii.ref.believe` reads every declaration in `visible(C)`:
    v1 admits no `except` and no denial of a declaration, and `vaelii.ref.gen` draws no
    nogood a declaration is a member of.
    Forcing is applied when belief is computed, and a declaration is a switch whose
    retraction gives back the belief a KB that never held it has. `vaelii.ref.world/inert-write?` reads a v1 rule
    concluding one as inert, since a v1 antecedent is never a roster literal. The
    engine holds it ([nmtms.md](nmtms.md#the-forced-monotonic-roster)). Section:
    [taxonomy.md](taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches).

The docs answer three questions a builder may still ask. A context with no `genlCx`
edge sees only itself. A definitional family's declaration is a ground and not a member,
and under invariant 6 it is `:monotonic` and goes OUT only by retraction. A rule's write
strength does not cap its conclusions; its defeasibility and its guards do.

## Invariants the reference states

The world check reads every `genlCx` write `:monotonic`, leaves every other roster write at
its strength, and sets every inert write aside
(`vaelii.ref.world/inert-write?`: a denial of a roster literal, a rule decision 17 makes
inert), so no world breaks invariant 1, 2, 5 or 6, and no write the roster rules out is
refused. Each entry states how the engine holds it.

1. **`genlCx` is universal and monotonic.** A `genlCx` edge holds at every context
   whatever context stores it, every write of one is `:monotonic` whatever strength
   it was written at, and a `(not (genlCx …))` is inert, so `up(C)` is a function of the
   stored edges. The engine holds it: `genlCx` is on the
   forced-monotonic roster ([nmtms.md](nmtms.md#the-forced-monotonic-roster)).
2. **The relation marks are on the forced-monotonic roster.** The roster is `irreflexive`,
   `anti_symmetric`, `asymmetric`, `functional`, `functionalInArg`, `anti_transitive` and
   `genlCx`, and invariants 5 to 8 extend it. A write of a roster predicate keeps the
   strength it was written at and is never the loser of a nogood, and a denial of one is
   inert. A mark's reach, the
   sub-predicates it convicts through predicate `genl`, reads the edges believed at `C`
   and never their class. Under invariant 5 those edges are never OUT, so the reach is
   the stored edges visible at `C`. The engine stores every roster write as written,
   never takes one OUT through a nogood, and holds a denial of one OUT
   ([nmtms.md](nmtms.md#the-forced-monotonic-roster)). A nogood's verdict reads its
   members' classes alone, and the predicate `genl` edges a mark's route climbs are its
   grounds, so no edge's class caps a violation.
3. **No clash is refused.** `W` is the writes offered, and the reference judges every
   one of them. A hard clash is stored and reported, as a `:monotonic` `S` beside
   `(not S)` already is. A refusal remains only where it reads the sentence alone:
   naming (which reads the sentence's own argument count), groundness and the v1
   fragment. A refusal that reads other stored
   content, such as `(disjoint a b)` over two `genl`-related types, becomes a stored hard
   clash. The engine stores every write that names the other members of its clash, and
   every declaration over `genl`-related types, and the settle reports a hard clash in
   `conflicts` (`checks/refuses-assert?`), and stores a tuple an `irreflexive` or
   `anti_symmetric` mark convicts, or whose length breaks its predicate's arity binding,
   for the settle to place as a nogood. A declaration over `genl`-related types is a one-member
   hard clash of the declaration, and a cover naming a part a `disjoint` separates from
   its whole a two-member one of the cover and the `disjoint`, listed by `conflicts`
   ([nmtms.md](nmtms.md#declarations-over-related-types)).
4. **A merge needs monotonic evidence on every side.** A `functional` or
   `functionalInArg` collision between two symbol fillers, or an `anti_symmetric`
   converse pair of symbols, merges the two terms only when every member is
   `:monotonic`. Otherwise the collision is a nogood: the unique weakest member loses,
   and a tie at `:default` is a dilemma. The reference gives the all-`:monotonic` pair the
   verdict `:merge` and leaves equality outside v1, so the harness skips the belief
   comparison at a context holding one and compares the pairs it merges with the pairs
   the engine's equality holds there (`vaelii.ref.gen/merge-disagreements`, the kind
   `:merge-differs`). The engine holds it: a collision derives the equality only when
   every member is `:monotonic`, and any other is a nogood, which the settle places for
   `functional` and `anti_symmetric` (`vaelii.impl.decide`).
5. **A `genl` edge between predicates is on the roster.** A `(genl P Q)` whose two
   arguments are camelCase predicates is never a loser whatever strength it was
   written at, its denial is inert, and it is derived only from roster antecedents
   (decision 17). A `genl` between types stays defeasible.
   `vaelii.ref.world/predicate-genl?` reads the spelling. The engine holds such an edge
   never a loser and its denial OUT under `core.txt`'s `(forced_monotonic_between_predicates
   genl)`, so a merge `special/equate-under-edge` derives over such an edge, and a claim
   `discovery/preserving-moves` re-opens through it, move only when the edge is stored or
   retracted.
6. **Every definitional declaration is on the roster.** `disjoint`, `covering`,
   `partition`, `sibling_disjoint` and `arity` are never a loser, a denial of one is
   inert, and one is derived only from roster antecedents, so a ground goes OUT only by
   retraction. An `arity` violation is a
   one-member nogood with the declaration as its ground. v1 admits `disjoint` and
   `covering`; `partition`, `sibling_disjoint` and `arity` stay outside it. The engine
   holds a declaration never a loser and its denial OUT, and no rule concludes an
   `arity` from a classification: every reader of one reads the exact-arity class. The
   engine places an arity violation as a nogood, and two predicates a `genl` edge
   relates whose bindings differ are a hard clash ([taxonomy.md](taxonomy.md#arity)).
   The related-type declarations are one-member or two-member hard clashes
   ([nmtms.md](nmtms.md#declarations-over-related-types)).
7. **`except` is on the roster.** An `except` is asserted and retracted, derived only
   from roster antecedents and never defeated, and an `except` that targets an `except`
   still hides it. `except` is outside v1. The engine holds an `except` never a loser and
   its denial OUT on every KB, and no settle resolution defeats one, so
   the settle watches no `except` for a belief flip.
8. **Equality is monotonic.** A `rewriteOf`, `sameAs` or `equals` merge rests only on
   `:monotonic` evidence, is never defeated, and is undone only by retracting a premise
   it rests on. Equality is outside v1. The engine holds an equation premise
   never a loser and a denial of one OUT, and `refresh-supersessions` runs on the write
   path; a settle calls it only after an `except` moved, or an equality edge moved in
   belief.
9. **A guarded firing confers `:default`.** A firing whose rule has an `unknown`
   antecedent or an `exceptWhen` confers `:default` on its conclusion, whatever the
   classes of the rule and of the other antecedents. The engine holds it: a guarded
   firing records `:default` as its justification's strength, and the strength follows
   an `exceptWhen` that arrives or leaves after the firing
   ([nmtms.md](nmtms.md#strength-propagates-from-the-antecedents)).

## What the engine has to equal

A settle is an incremental computation of `believed(W, C)` for every context at once.
It reads a region, memos, budgets and passes, and none of them may change the answer: a
settle that differs from the function on any world and any context is wrong, whatever its
tests say, unless the difference is a known divergence below. `vaelii.reference-test`
is the witness. It loads random small worlds in every arrival order into fresh KBs and
compares the engine's belief at each context with the
reference's, sentence by sentence: a stored sentence through `core/believed?` on its
handle, and an inherited claim, which has no handle, through `core/ask?` at the context.
A context whose view holds a merge verdict is not compared, and the harness counts it.

**Under decision 16 the engine places at write time and applies at the reader.** The
nogoods are found by the keys [The function](#the-function) lists and placed when a
settle runs; forward firings, the `genl` and `genlCx` closures, merges and mints stay at
write time too. The costs the engine is held to:

- a write costs the forward chain, the closure updates, the support relabel and the
  placement of the nogoods its move reaches, O(touched × degree + nogoods reached);
- a read of `S` at `C` costs O(|support ancestor set of `S`|) plus the members of each
  placed nogood the walk meets there, and keeps nothing after it returns
  ([nmtms.md](nmtms.md#a-nogood-placed-as-a-conclusion)).

**Every disagreement has a kind.** `gen/check-world` classifies each disagreement by the
shape of the minimal shrunk world, and a disagreement it cannot classify is
`:unclassified`. `vaelii.reference-test`'s `known-divergences` map names each known kind
with the decision it departs from, and is empty. The test fails on a kind outside the
map, `:unclassified` included, and counts and prints every known one. A write
the engine refuses and the reference stores is an `:engine-refused-*` divergence: the
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
| `disjoint` | yes, on the roster (invariant 6) | [taxonomy.md](taxonomy.md#disjointness) |
| `functional`, `functionalInArg` | yes, symbol fillers included, except the all-`:monotonic` merge (invariant 4) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| `irreflexive`, `anti_symmetric` | yes, as nogoods (invariant 2) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| a `:default` write of a mark, `disjoint`, `covering` or a predicate `genl` | yes, kept `:default` and never a loser (invariants 2, 5 and 6) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| a denial of `genlCx`, a mark, a declaration or a predicate `genl` | yes, stored and held OUT (invariants 1, 2, 5 and 6) | [nmtms.md](nmtms.md#the-forced-monotonic-roster) |
| a rule concluding a forced-monotonic predicate | yes, its firings stored and held void (decision 17) | [taxonomy.md](taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches) |
| `anti_transitive` | yes | [nmtms.md](nmtms.md#a-nogood-is-a-set-anti_transitive-has-three-members) |
| `covering` | yes, on the roster (invariant 6) | [taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it) |
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
| `disjoint_metatype`, `sibling_disjoint` | no; `sibling_disjoint` is on the roster (invariant 6) | [taxonomy.md](taxonomy.md#disjointness) |
| `partition`, `separating` | no; `partition` is on the roster (invariant 6) | [taxonomy.md](taxonomy.md#partition-and-separating-add-no-separation-mechanism-of-their-own) |
| `arity` | no; on the roster, and a violation is a one-member nogood (invariant 6) | [taxonomy.md](taxonomy.md#arity) |
| the ASP solver | no | [asp.md](asp.md), [labeling.md](labeling.md) |
| `asymmetric` | yes, as the `asymmetric` family; on the roster (invariant 2) | [inherit.md](inherit.md#asymmetric-p) |
| `genl` between predicates of arity 2 or more | yes, on the roster (invariant 5); the generator writes none | [taxonomy.md](taxonomy.md#predicate-metadata) |

## The standing state

One row per atom the KB keeps between settles, ordered by the settle step that writes
it. The steps are the ones [nmtms.md](nmtms.md#the-runtime-view) numbers: *write* is the
assert and retract path with its store and removal choke points, 2–9 are `settle*`'s
steps, F1–F6 are `settle-finish`'s, and *read* is a cache a read fills. The last column
states the inputs whose change invalidates the atom, as the docstrings and the code state
them; **not stated** means no docstring, comment or stamp comparison says. **Partial**
marks a cell where the stated rule and the code disagree.

| atom | step | holds | written by | read by | invalidated by |
|---|---|---|---|---|---|
| `:nogood-candidates` | write | per family, the stored sentences that could be a member of one of its nogoods: the ground binary tuples under a converse mark with a stored converse, the tuples of a shape a stored arity binding breaks, the bindings of two related predicates whose lengths differ, the determinants under a tuple mark holding two fillers, the `anti_transitive` chains and the converse pairs, and per term holding two memberships or a membership and a denial its entries, its type pairs and the nogoods the unscoped taxonomy reads; the arity bindings and tuple shapes those read; the `disjoint`s over `genl`-related types, the contradicted `orthogonal`s and the covers paired with a `disjoint` separating their whole from a part; and under `:inherited`, every inherited nogood the settle found with its vantages; and every candidate by the context its record is stated in, read again off the journal by `decide/synced` | `decide/note-candidate!`; `decide/rebuild-candidates!` on recover; `inherited/install-inherited!` at step 4 | `chain/place-nogoods!`, `chain/place-inherited!`, `decide/candidate-handles`, `decide/handles-at` (the journal, [nmtms.md](nmtms.md#the-candidate-journal)) | a store or removal of a tuple, a membership, a denial, a binding or a `genl` edge, a tuple mark or a predicate `genl` edge under one (`special/offer-marked-existing`), a move of `tax/separation-stamp` for the membership separations, and a `genlCx` edge for the live determinant members; the inherited nogoods are installed again at step 4, every settle; belief is read by the placement |
| `:mint-queues` | write | the removed `genlCx` edges and the removed records that can have subsumed a mint (`:departed`), and the records a retraction left standing on a derivation alone (`:unpremised`) | `special/note-departure!`, `special/note-unpremised!` | the context-move drain (the edges) and the mint re-checks beside step 7 | two queues: the drain and the mint re-checks drain them, every settle pass |
| `:recheck` | write, 2, 5 | `{rule-handle triggers}`, the rules whose block conditions owe a re-evaluation | `special/mark-recheck` | step 6 | a queue: step 6 drains it. Partial: the record comment names fact moves on an exception's predicates and taxonomy edges; the code also posts on declarations, preserving extents, calculus entailments, `except` moves and rule indexing |
| `:except-moves` | write, 2, 5 | the handles an `except` began or stopped hiding | `special/note-except-move!` | the loop beside step 7, F3 | a queue: F3 takes it, and a leftover forces a full supersession pass |
| `:respell` | write | the predicates whose permuting marks moved | `special/note-permuting-moves!` | the re-seed after `settle*` | a queue, posted when the permuting-mark pair changes identity at a removal or a relabel |
| `:refused` | write, 9 | `{rule-handle #{refusal}}`, the firings a block condition declined, plus pending mints and lifts | `chain/record-refusal!`, `special/note-pending!` | steps 8–9 | a refusal dies when it fires, its rule goes, or its antecedents stop being believed; a rule's entries are re-asked only while the rule is on `:recheck`; constraint and lift entries on a move of the `genl` or `genlCx` generation or a region naming the term; mint entries on the generation alone |
| `:qcn-joined` | write, 9 | per calculus and context, the network the rules were last joined over | the chainer's qualitative re-join | the next join | none by design: a missing baseline makes the next join a full one |
| `:violations` | write, F2 | the ledger of dropped conclusions and sweep cuts, newest 1000 | `vaelii.impl.violations` | `core/violations` | not a belief input: a retraction does not withdraw an entry, `clear-violations!` empties it, and a refused firing placed later withdraws its entry. A `:forced-conclusion` entry is not in the ledger: `core/violations` reads it off the stored void firings (`checks/forced-conclusion-entries`) |
| `:preserved-clashes` | 4 | per stored claim, its inherited nogoods, the askers and the classes read | `discovery/preserving-nogoods` | step 4 | a member OUT or reclassed, a vocabulary move, a moved claim that reaches it, a retraction in the region, a moved flat-cache entry it reads (`tax/flat-moves`), and the `genlCx` generation and the excepts that moved (`special/except-moved`) ([nmtms.md](nmtms.md#the-inherited-clash-memo)) |
| network `:blocked` | 9 | the justification ids whose block condition holds at the placement context | `jtms/set-blocked`, from `recheck/exception-blocked-set` | `valid?` | the `:recheck` triggers. Partial: `set-blocked` says the caller re-evaluates every exception, and `exception-blocked-set` carries every block outside the queued candidates forward |
| taxonomy relations | write, 2, F2, F4 | per relation, the supporters, the active edges and a generation | `tax/add-edge` and its removal twin, `tax/refresh-beliefs` | every closure read | an edge change moves the generation; `refresh-beliefs` after a relabel re-activates an edge exactly when some supporter is believed ([taxonomy.md](taxonomy.md#the-closures-are-derived-state)) |
| taxonomy side caches | read | `:closure-memo`, `:closure-lru`, `:rewrite-order` | the closure reads | every closure read | the relation's generation. Partial: `:rewrite-order` is stamped on the identity of the active rewrite map, not a generation |
| network `:superseded` | write, F3 | the displaced spelling of each merged datum | `special/refresh-supersessions` | `in?` | a store or removal that moves an equality edge, a displaced datum, a restatement, a rewrite rule or a `genlCx` edge; an `except` move; an equality edge off the roster moving in belief |
| `:supersessions` | write, F3 | the datums whose supersession entry moved since the last settle, each with its entry before | `special/refresh-supersessions` | `settle-finish` (`special/take-supersession-moves!`) | a queue: F3 takes it |
| `:feed` | F5 | the change feed's listeners and the region filed for them | `feed/note-region!` | the delivery at the end of `settle` | not a cache: delivery claims and empties the region |
| `:settle-stats` | after F6 | counts of passes and blocked-set moves | `settle/settle-finish` | `core/settle-stats` | a counter; belief reads none of it |
| `:closures` | read | the reach sets the provers walked | `provers/cached-reach` | the provers | `observe/change-clock`, which every store, removal, relabel and taxonomy change moves |
| `:matches` | read | what `res/matches-visible` answered | `vaelii.impl.literal-cache` | `res/matches-visible` | `observe/change-clock` |
| `:qcn` | read | each calculus's network per context, and other clock-stamped readings | `vaelii.impl.qcn-kb` and its neighbours | the calculus provers | `observe/change-clock` |
| `:program` | none | the last Program handed to a solver | the labeling solver, a batch rollback | the labeling readers, `core/last-program` | **not stated.** No settle writes it, and no content or belief change invalidates it; `core/last-program`'s docstring says it is nil until a tie is arbitrated, and a settle's arbitration never writes it |
| `:chain-stats` | write, 9 | the run count and the last run's result | `chain/chain-all` | `core/chain-stats`, `core/preview`, the violation run id | **not stated**; nothing resets it |
| `:unrecovered` | open, recover | the write hazards declared and not yet retired | `kb/note-hazards!` and the recovery path | `kb/write-hazards`, `kb/read-view` | history rather than a derivation: `recover` and `reindex` retire what they rebuilt |

Four atoms are counters, queues or history rather than caches of belief: `:settle-stats`,
`:chain-stats`, `:violations` and `:unrecovered`. Belief reads none of them.

## What the reference does not tell you

The reference says what belief is and never how fast a settle reaches it. It recomputes
every context from every premise on every call, which is the cost locality exists to
avoid. The cost contract of a settle, step by step, with the gate that holds each bound,
is [nmtms.md](nmtms.md#the-runtime-of-a-settle).
