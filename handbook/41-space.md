# 41. Space

- **Covers:** which places are objects and which are regions; `locatedIn` and
  `tangiblePartOf` beside the RCC-8 region relations; where a part is located; choosing
  a base or a derived spatial relation when knowledge is partial; cardinal and relative
  direction, and the context as a frame of reference; qualitative distance; what the
  four qualitative-constraint provers do with the stated relations, and what an author
  leaves to them.
- **Not here:** parthood as a general theory, `partType` and the kinds of part →
  [ch. 21](21-claims-about-kinds.md) and [inherit.md](../docs/inherit.md); a location
  that changes over time → [ch. 35](35-change-over-time.md) and
  [ch. 39](39-time.md); two names for one place → [ch. 37](37-coreference.md); a measured
  length → [ch. 38](38-quantities.md); the composition tables and the path-consistency
  engine → [space.md](../docs/space.md) and [qcn.md](../docs/qcn.md).
- **Assumes:** [ch. 6](06-definitional-block.md), [ch. 18](18-argument-types.md),
  [ch. 19](19-relation-properties.md), [ch. 23](23-contexts.md),
  [ch. 32](32-negation.md).

`space.txt` ships fifty spatial predicates in four calculi: RCC-8 topology (do two
regions touch, overlap or nest), cardinal direction (which way on the map), relative
direction (which way from a point of view) and qualitative distance (how far apart, in
classes). Each calculus is a set of base relations of which exactly one holds of any two
things, plus derived relations that each name a disjunction of base ones. A registered
prover reads the stated relations of its calculus into one constraint network per
context, tightens the network by composition, and answers a goal by entailment. Beside
the calculi, `abstract.txt` ships `locatedIn` and `tangiblePartOf` for physical objects.
This chapter says which of these an author states, and in what form.

## objects in locatedIn, regions in RCC-8
*Objects in locatedIn, regions in RCC-8*

**Practice.** Decide for each place term whether it has mass. A building, a box, a car
or a cave wall has mass: it is `tangible`, and an object inside it is stated with
`locatedIn`. A parish, a parking zone, a square of a board or the area a fence encloses
has no mass: it is a region, and it is related to other places with the four calculi
only. Declare a region of the world `spatiotemporal` and `intangible`; declare a region
of an abstract space `spatial`.

**Example.** `abstract.txt` types both positions of `locatedIn` tangible, and
`space.txt` types every position of the calculi at `spatial`:

```clojure
(arg locatedIn 1 tangible)
(arg locatedIn 2 tangible)
(arg partOfRegion 1 spatial)
(arg partOfRegion 2 spatial)
```

A composed declaration of a region of the world, and of a region of an abstract plane:

```clojure composed
(spatiotemporal TmpParish)
(intangible TmpParish)
(spatial TmpSquareA1)
(atemporal TmpSquareA1)
```

**Why.**

- *Logical.* `core.txt` cuts `thing` into `tangible` and `intangible` with a monotonic
  partition, and states `(orthogonal intangible spatial)`: a region has a location and no
  mass. `tangible` is below `spatiotemporal`, so every object is `spatial` and can stand
  in an RCC-8, direction or distance relation as a region can.
- *Engine.* Under the entailing reading, `(arg locatedIn 2 tangible)` derives `(tangible
  X)` for every `X` written in the second position ([ch. 18](18-argument-types.md)). A
  region declared `intangible` and written there makes a definitional clash, and
  `try-assert` refuses the write with `:definitional-clash`. A region declared only
  `spatial` and written there is made `tangible` with no refusal at all.
- *Engine.* The shipped KB states no rule between `locatedIn` and any RCC-8 predicate.
  The comment on `locatedIn` names the division: "a region is the spatial calculi's
  business, and partOfRegion is the relation to reach for there."
- *Maintenance.* `locatedIn` says one object sits within another. A cup in a box sits
  within the box whether the box's extent is read as its cardboard alone or as the
  cardboard and the hollow. An RCC-8 relation between the two needs that reading fixed,
  so a rule from `locatedIn` to `nonTangentialProperPart` would fix one reading for every
  container in the KB.

**Why not the other ways.** A region used as a container in `locatedIn` acquires mass in
the KB, and every rule over `tangible` then applies to it. An object related only by
RCC-8 answers no `locatedIn` question, and its parts receive no location from
`CxMereology`. A region related by a new containment predicate of its own repeats what
`partOfRegion` already states and what the RCC-8 prover already composes.

**Audit.** For each new place term, `describe` it and confirm it holds `tangible` or
`intangible` and not both. For each `locatedIn` fact naming a region, `try-assert` it; a
`:definitional-clash` marks a region written as a container.

## A part is where its whole is

**Practice.** State the location of a whole and the parthood of its parts, and let
`CxMereology` carry the location to the parts. Make the context the facts sit in see
`CxMereology`. Do not state the location of each part, and do not write the join rule.

**Example.** `CxMereology.txt` holds the declaration:

```clojure
(genlCx CxMereology CxUniverse)
(transitiveInArgInverse locatedIn 1 tangiblePartOf)
```

The test world states a whole's location and two parthood steps below it:

```clojure
(tangiblePartOf Engine1 Car1)
(tangiblePartOf Piston1 Engine1)
(locatedIn Car1 Garage1)
```

A context that sees `CxMereology` and holds these facts answers `(locatedIn Piston1
Garage1)`. The test that states the same facts over temporaries finds no stored
`locatedIn` fact for the piston
(`ontology_rules_test/a-part-is-located-and-owned-where-its-whole-is-and-nothing-is-stored`).

**Why.**

- *Logical.* `(transitiveInArgInverse locatedIn 1 tangiblePartOf)` licenses `(locatedIn
  A P)` from a stored `(locatedIn W P)` when `(tangiblePartOf A W)` holds. A part of a
  car parked in a garage is in the garage.
- *Engine.* The preservation is answered at query time from the context the query reads.
  The preservation composes with `(transitive locatedIn)`, so with the test world's
  `(locatedIn Garage1 House1)` the piston is also located in `House1`. A forward rule
  over `locatedIn` fires on a preserved answer, and the firing rests on the parthood
  edge, the location fact and the declaration: retracting the `tangiblePartOf` edge
  withdraws the firing.
- *Engine.* The declaration names `tangiblePartOf` and nothing else. `partOfRegion` sits
  below `partOf`, not below `tangiblePartOf`, so a region inside a region carries no
  `locatedIn` claim. A context that does not see `CxMereology` carries no location to
  any part.
- *Maintenance.* A car moved to another garage moves every part with one retraction and
  one assertion.

**Why not the other ways.** A location stated for each part is one sentence per part per
place, and each one goes stale when the whole moves. A forward rule joining
`tangiblePartOf` and `locatedIn` stores a conclusion per part per place, inside the
fixpoint; the test world keeps such a rule for its own placement tests, and the shipped
KB states the declaration instead.

**Audit.** From the context the change targets, `ask?` `(locatedIn P Place)` for one part
`P` two steps below a located whole, and confirm `sentexes-matching` finds no stored
`(locatedIn P ?w)`.

## Partial knowledge of a pair

*The case of **the known disjunction** ([ch. 39](39-time.md)) for regions*

**Practice.** When one base relation is known, state it. When only a disjunction is known,
state the derived relation that names the disjunction, and never a base relation picked
from it. When two partial facts about one pair are known, state both. When a relation is
known not to hold, state its negation.

**Example.** `space.txt` declares the derived relations beside the base ones, and links
the region relations to generic parthood:

```clojure
(set/monotonic (reflexive partOfRegion))
(genl partOfRegion permanentPartOf)
(set/monotonic (irreflexive properPartOfRegion))
(genl properPartOfRegion properPartOf)
```

The comment on `northwardOf` says what a derived relation commits to: "Derived, so it is
entailed by any of the three and asserts none of them." Two composed single-axis facts
about one pair:

```clojure composed
(northwardOf TmpMill TmpVillage)
(eastwardOf TmpMill TmpVillage)
```

**Why.**

- *Logical.* The base relations of a calculus are jointly exhaustive and pairwise
  disjoint, so a set of them is the constraint "one of these". A derived relation states
  that set: `partOfRegion` is TPP, NTPP or EQ, `regionConnectedTo` is everything but DC,
  `northwardOf` is N, NE or NW.
- *Engine.* Each fact intersects its pair's constraint with its relation's denotation. The
  two facts above leave `#{:ne}` and entail `(northeastOf TmpMill TmpVillage)`, which
  neither states. A believed `(not (regionConnectedTo A B))` intersects with the complement
  and leaves `#{:dc}`, so a negative fact entails a positive goal
  ([qcn.md](../docs/qcn.md#negation-refutation-and-negative-facts-as-constraints)).
- *Engine.* A goal is answered when every relation still possible between the pair
  satisfies it, so a derived goal is entailed by more networks than a base one. A pair
  left open answers neither a goal nor its negation.
- *Engine.* `(genl partOfRegion permanentPartOf)` makes an entailed `partOfRegion` tuple answer a
  `partOf` goal, and `(genl properPartOfRegion properPartOf)` does the same for
  `properPartOf`. An NTPP chain therefore answers generic parthood questions
  (`space_test/an-entailed-region-part-answers-generic-parthood`).
- *Maintenance.* A guessed base relation narrows the network further than the knowledge
  does. A later true fact that disagrees with the guess empties a constraint, and the
  whole component then answers nothing.

**Why not the other ways.** A base relation stated for a disjunction asserts what nobody
knows, and every composition through the pair carries the guess on. A derived relation
stated where a base one is known gives up entailments: two `partOfRegion` facts compose to
`partOfRegion`, where two `nonTangentialProperPart` facts compose to
`nonTangentialProperPart` and refute contact with the boundary. Leaving a known exclusion
unstated loses the constraint its negation would add.

**Audit.** For each stated pair, read `possible-relations` and compare the set with what
the source knows. A singleton the source does not support marks a guess; a set wider than
the source's knowledge marks a fact left unstated.

## the context is the frame
*The context is the frame of reference*

**Practice.** State cardinal direction for places on a shared map: `northOf`, `eastOf`
and the rest name the map's own axes, whoever looks. State relative direction (`leftOf`,
`inFrontOf`, `behindRightOf` and the rest) in a context whose content is one viewpoint,
and give each viewpoint its own context. Put the located thing first and the reference
second in every direction relation.

**Example.** A composed pair of viewpoints on one bridge, each stated in its own
context:

```clojure composed
(genlCx CxTmpFromNorthBank CxUniverse)
(genlCx CxTmpFromSouthBank CxUniverse)
(leftOf TmpMill TmpBridge)
(rightOf TmpMill TmpBridge)
```

The `leftOf` fact sits in `CxTmpFromNorthBank`, and the `rightOf` fact sits in
`CxTmpFromSouthBank`.

**Why.**

- *Logical.* Relative direction is ternary: A is left of B from viewpoint C. A
  constraint network is binary. `space.txt` takes the context as the viewpoint, so
  `(leftOf A B)` states A left of B in the frame that context is.
- *Engine.* A network is built per context from the facts that context sees. Two
  viewpoint contexts holding opposite facts each answer their own way.
- *Engine.* A context that sees both viewpoint contexts reads both facts into one network.
  `:left` and `:right` share no relation, so the pair's constraint empties and the network
  is unsatisfiable. The KB reports the merge of two frames as an inconsistency.
- *Engine.* Both direction calculi compose each axis separately: `(northOf B A)` and
  `(eastOf C B)` entail `(northeastOf C A)`. A chain that disagrees on one axis keeps the
  other, and a derived relation (`northwardOf`, `leftwardOf`) states what survives.
- *Logical.* `sameLocationAs`, `sameRelativePositionAs` and `coLocatedWith` are three
  claims: the same compass position, the same offset in a frame, and zero distance apart.
  `spatiallyEqual` makes a fourth claim, the same extent. None of the four is `sameAs`: two
  coextensive regions are still two regions ([ch. 37](37-coreference.md)).

**Why not the other ways.** A viewpoint written into the predicate name multiplies the
vocabulary by the number of viewpoints. A viewpoint written as a third argument leaves
the binary network engine. Relative facts from two viewpoints in one context make the
network unsatisfiable, and the component then answers nothing about the things it
relates. Cardinal facts used for "on the left" state a compass bearing nobody measured.

**Audit.** For each context that sees two viewpoint contexts, read `qualitative-network`
under `:relative`; `:consistent? false` marks two frames merged without a translation.

## Distance is for ruling out

**Practice.** State qualitative distance with the seven classes, from `coLocatedWith`
through `veryFarFrom`, or with a derived range (`withinNearDistanceOf`,
`beyondFarDistanceFrom`, `atSomeDistanceFrom`) when only the range is known. Expect the
calculus to refute an arrangement more often than it determines a class. For a measured
length, state the measure ([ch. 38](38-quantities.md)).

**Example.** Two composed very-close hops:

```clojure composed
(veryCloseTo TmpNest TmpBranch)
(veryCloseTo TmpBranch TmpTrunk)
```

**Why.**

- *Logical.* Each class denotes an interval of distance, and the seven tile every
  distance once. The bounds fix the ratio between neighbouring classes and not a length
  in metres.
- *Engine.* Composition follows the triangle inequality, so the two hops above leave
  `#{:co :very-close :close}` between the nest and the trunk. No single class is
  entailed. `(withinNearDistanceOf TmpNest TmpTrunk)` is entailed, and `(farFrom TmpNest
  TmpTrunk)` is refuted. A stated `(veryFarFrom TmpNest TmpTrunk)` empties the pair, and
  the network is unsatisfiable.
- *Engine.* Distance is symmetric in the algebra: the converse of every class is itself.
  Only a chain through `coLocatedWith` determines a class.

**Why not the other ways.** A class guessed for a pair whose distance is unknown is a
guess that composition carries to every pair the chain reaches. A number written into a
class name invents a unit the calculus does not have.

**Audit.** After a change to distance facts, read `qualitative-network` under `:distance`
in each changed context and check `:consistent?`.

## leave the converse to the algebra
*Leave the converse and the composition to the algebra*

**Practice.** Register the prover for each calculus the application reads. State each
relation once, in one direction, and do not add a second predicate as an alias for one.
An `inverse` between two calculus predicates is true, and the algebra already computes it,
so `space.txt` states each one inert, for a reader. When the network reports an
inconsistency, retract or correct a stated fact.

**Example.** Each prover is opt-in, and a composed call registers all four:

```clojure composed
(v/add-reasoner kb :rcc8 :cardinal :relative :distance)
```

`space.txt` writes each converse pair down for a reader, and holds it inert:

```clojure
(set/inert (inverse partOfRegion hasRegionPart))
(set/inert (inverse nonTangentialProperPart nonTangentialProperPartInverse))
```

**Why.**

- *Engine.* Without the prover, a calculus fact is an ordinary stored fact: it answers
  itself, and nothing composes. With it, `ask`, rule antecedents, `exceptWhen` and
  `unknown` all reach the network, and a forward rule with a positive calculus antecedent
  fires on an entailed relation and rests on the facts behind the entailment.
- *Engine.* The prover claims completeness for its own predicates and answers their goals
  alone. A believed `(inverse P Q)` between two predicates of one calculus is a pair the
  algebra's converse table implies, and the prover reads both predicates, so the prover
  still answers alone
  (`space_test/a-believed-inverse-the-converse-table-implies-leaves-the-prover-answering-alone`).
  A believed `inverse` naming a predicate outside the calculus is a source the prover
  does not read, and the engine takes the union of every prover
  (`space_test/a-believed-inverse-of-a-spatial-predicate-shadows-its-prover`).
  The inert copies in `space.txt` are not believed and move no answer
  (`space_test/an-inert-converse-fact-leaves-the-calculus-prover-answering-alone`).
- *Engine.* An unsatisfiable component answers no goal naming its nodes, and the KB files
  a `:qualitative-inconsistency` entry in `violations` naming the calculus, the context and
  the pairs. No nogood forms between two facts only the network finds incompatible, so
  both stay believed, and the network alone records that they cannot both hold.
- *Maintenance.* Composition and converse come from the algebra's table, so a fact stated
  in one direction answers both, and a fact added later narrows every pair it reaches.

**Why not the other ways.** A stated converse doubles the facts and adds nothing the
algebra does not compute. A rule writing out a composition stores a sentex per derived
pair and covers the table entries the author remembered. A fact added beside a clash, in
place of a correction to one of the clashing facts, leaves the network unsatisfiable.

**Audit.** `git grep -nE '\((inverse|genlInverse) '` over the changed files. A hit that
pairs a calculus predicate with a predicate outside its calculus is reported: that
calculus prover no longer answers alone. Read `violations` for
`:qualitative-inconsistency` entries in each context the change writes to.
