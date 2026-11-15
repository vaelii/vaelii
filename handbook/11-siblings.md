# 11. Siblings and intersections

- **Covers:** keeping a type consistent with its siblings; naming a recurring combination
  of two types once, as an intersection; and the checks to run before minting one.
- **Not here:** choosing the parent the siblings share → [ch. 10](10-parent.md); separating
  the siblings → [ch. 13](13-disjointness.md); siblings that overlap →
  [ch. 15](15-overlap.md).
- **Assumes:** [ch. 4](04-economy.md), [ch. 7](07-comments.md), [ch. 10](10-parent.md).

A type's siblings are the types a reader compares it with: the other specs of its parent,
the types it is separated from, and its `seeAlso` and `termsRelated` partners. Siblings
that are described alike let a reader learn one and predict the rest, and they let the
engine treat them alike through the same metatype, the same separations and the same rules.

## match the siblings

*Keep a type consistent with its siblings*

**Practice.** When ontologizing a type, check its siblings: everything it is `disjoint`
with, and its `seeAlso` and `termsRelated` partners. Place siblings at the same level and
describe them in the same terms. An asymmetry between siblings is either a finding or a
comment, never an accident.

**Example.** organism.txt states each vertebrate class with the same two sentences, a
`genl` to `vertebrate` and a membership in the `vertebrate_class` metatype:

```clojure
(genl mammal vertebrate)
(vertebrate_class mammal)
(genl bird vertebrate)
(vertebrate_class bird)
(genl fish vertebrate)
(vertebrate_class fish)
```

The stages of a lepidopteran are siblings under `lepidopteran`, and each is stated with the
companion relation for its stage:

```clojure
(genl caterpillar lepidopteran)
(larvalFormOf caterpillar lepidopteran)
(genl butterfly lepidopteran)
(adultFormOf butterfly lepidopteran)
(diachronicallyDisjoint caterpillar butterfly)
```

`caterpillar` differs from the species beside it in one respect, and its comment records
the asymmetry as a decision: "Not a species of its own, so not a folk_species, and
diachronicallyDisjoint from butterfly rather than disjoint: the same organism is a
caterpillar and later a butterfly."

**Why.**

- **Logic.** Siblings divide their parent along one distinction. When one sibling is
  described in other terms, it is either divided along another distinction, and so
  belongs at another level, or the description of one of them is wrong.
- **Engine.** A `disjoint_metatype` separates its members pairwise, and every kind below a
  member is separated from every kind below another, with nothing stored per pair.
  organism.txt's opening note says the metatype is consulted for the five vertebrate
  classes "rather than by ten `disjoint` sentences", so retracting one class's membership
  releases exactly that class's pairs. A sibling stated without the membership is outside
  the metatype: no separation reaches it, its pairs with the other classes read `:unknown`
  in `disjointness-audit`, and an organism stated a member of it and of another class is
  stored with no clash. A stage stated `diachronicallyDisjoint` from its sibling is never a
  clash: time.txt's comment on `diachronicallyDisjoint` says the relation is "Stated and
  queryable, not enforced: memberships are checked without time". The comment on
  `caterpillar` tells a reader why the stage has no `folk_species` membership and no
  `disjoint` separation.
- **Maintenance.** A sibling block that matches the others is checked by comparing it with
  them. An unexplained asymmetry makes every later reviewer decide again whether the
  difference was intended.

**Why not the other ways.** Placing a sibling one level higher or lower than the others,
for instance a vertebrate class stated directly under `animal`, gives it a different set of
inherited separations and rules from the other classes with no sentence saying why.
Stating the siblings' separations as individual `disjoint` sentences instead of one
metatype makes each new sibling a set of new sentences, one per existing sibling, where a
membership is one.

**Audit.**

- `direct-specs` on the parent lists the siblings, including those a cover installed.
- `describe` on the new type and on each sibling answers `:genls`, `:disjoint` and
  `:comment`. Compare the answers, and for each difference find the comment that states it.
- `disjointness-audit` after the change shows the new type's pairs with its siblings. A
  pair that reads `:unknown` where the other siblings read `:disjoint` is a missing
  membership or a missing separation.

## factor out commonalities

*Name recurring meta-type combinations once*

**genlPrinciple:** DRY

**Practice.** If facts keep stating `(A P)` and `(B P)` for the same `P`, and neither `A`
nor `B` is a `genl` of the other, mint the intersection of `A` and `B` and state one
membership in it.

**Check first.** If one type is a `genl` of the other, stating both is a case of
**strongest form** ([ch. 4](04-economy.md)): drop the weaker fact. core.txt states this
edge:

```clojure
(set/monotonic (genl instance_relation_predicate binary_predicate))
```

`(instance_relation_predicate P)` therefore entails `(binary_predicate P)`, and the
second membership beside the first is redundant, not a reason to mint an intersection.

**Example.** abstract.txt names the events that can be a cause, and the events located in
some space, as intersections, and core.txt names a relation that is reflexive, symmetric
and transitive at once:

```clojure
(intersection causal_event causal event)
(intersection spatial_event event spatial)
(intersection equivalence_relation reflexive symmetric transitive)
```

**Why.**

- **Logic.** An intersection is a definition: a thing is a member of the combined kind
  exactly when it is a member of each intersected type. It names a combination once, and
  the name says what the two repeated facts said together.
- **Engine.** core.txt's forward rules turn an intersection of two or three types into a
  `genl` edge from the combined kind to each type, so the edges reach the closure and the
  combined kind inherits every rule and separation of each type. A generator reads each
  intersection fact and generates a concrete membership rule, so a thing that is each type
  is concluded a member of the combined kind. The generated rule confers `:monotonic`, and
  its conclusion is capped at its weakest antecedent. core.txt's `implementationNote` on
  `intersection` states the limit: the rules are written for two and for three intersected
  types, so an intersection of four or more types derives neither its `genl` edges nor its
  memberships, and such a combination needs its edges stated.
- **Maintenance.** One membership in the intersection replaces two facts on each term, and
  a rule on the combination is written once on the combined kind instead of with both
  antecedents in every rule that needs them.

**Why not the other ways.**

- **An intersection nothing reads.** The membership rule stores a membership for every
  term that is each type, so an intersection whose members no rule, argument declaration
  or query reads adds stored conclusions and nothing else. core.txt places `spatiotemporal`
  below `physical` and `temporal` by `genl` edges for this reason, and records the
  definition as documentation beside them: "an intersection's membership rule would store
  a membership of every term under both types, and nothing reads one". Apply **does it have
  rules?** ([ch. 1](01-true-and-useful.md)) to the combined kind before minting it.
- **Repeating the two facts.** Each term states both memberships, each rule over the
  combination repeats both antecedents, and a term stated with one of the two and not the
  other is not found by a query for the combination.

**Audit.**

- For each pair of memberships that recurs across terms in a change, check first whether
  one type is a `genl` of the other (`genls` or `subsumption-status` answers it), and drop
  the weaker membership when it is.
- `kb-integrity` with `:categories #{:twin-genls}` reports two or more types whose direct
  `genl` sets are identical and name at least two types besides `thing`. The finding
  suggests a missing common parent: the intersection of the shared parents, or a named
  type the twins belong under.
- For each intersection of four or more types, the change states the combined kind's
  `genl` edges.
