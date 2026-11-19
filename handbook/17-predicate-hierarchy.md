# 17. The predicate hierarchy

- **Covers:** placing a relation under a more general one with `genl`; the swapped form
  `genlInverse` and the two-way `inverse`; a `genl` between relations whose arguments are
  typed differently; separating two relations with `negates`.
- **Not here:** the argument declarations a `genl` carries down → [ch. 18](18-argument-types.md);
  the algebraic marks (`transitive`, `functional`, …) → [ch. 19](19-relation-properties.md);
  a rule that is not a hierarchy edge → [ch. 29](29-rules.md).
- **Assumes:** [ch. 8](08-kind-of-term.md) (a predicate is camelCase with arity 2 or
  more), [ch. 10](10-parent.md) (**tightest parent**).

`genl` relates predicates as well as types. `(genl P Q)` between two predicates says that
every tuple of `P` is a tuple of `Q`. The hierarchy of relations is the same `genl`
closure the type hierarchy uses, read one dimension over.

## Placing a relation under a more general one

**Practice.** When every tuple of `P` is a tuple of `Q`, state `(genl P Q)`. Choose the
tightest true parent, as for a type. State only the direction that is true, and say in a
`;;` note why the converse does not hold when a reader could expect it.

**Example.** `CxSocial.txt` places employment under membership and explains the missing
converse:

```clojure
(genl worksFor memberOf)
```

The note above it reads "Employment is one way of belonging to a body of people;
belonging is not a way of being employed by it, so there is no converse edge."
`CxKinship.txt` states `(genl parentOf ancestorOf)` under the note "Parenthood is ancestry:
parentOf specializes ancestorOf."

`CxSocial.txt` also shows a parent chosen for what is true rather than for what is short.
`friendOf` and `marriedTo` each reach `knows` by their own edge, and the header explains
that a `marriedTo` under `romanticPartnerOf` under `friendOf` chain would claim every
marriage is a friendship:

```clojure
(genl friendOf knows)
(genl marriedTo knows)
(genl romanticPartnerOf friendOf)
```

**Why.**

- *Logical.* `(genl P Q)` entails `(Q a b)` from `(P a b)`. It says nothing about a `Q`
  tuple that has no `P` tuple behind it.
- *Engine.* Matching fans a functor over its `genl` spec closure. A `(memberOf ?x ?y)` goal
  or rule antecedent is satisfied by a stored `(worksFor Ann Acme)` once the edge holds,
  and no `memberOf` fact is stored. The subsumption is one-way: a sub-predicate satisfies
  its super, never the reverse. Retracting the edge removes the subsumption.
- *Engine.* A `genl` between two predicates is forced-monotonic. `core.txt` declares
  `(forced_monotonic_between_predicates genl)`, which puts every `genl` whose arguments are
  both spelled as predicates of arity 2 or more in the forced-monotonic set. The edge is
  never the loser of a nogood and a denial of it loses. A `genl` between types stays
  defeasible.
- *Engine.* Facts travel up the predicate hierarchy, and some declarations travel with
  them. `Q`'s argument declarations constrain `P`'s tuples ([ch. 18](18-argument-types.md)),
  so a `genl` edge is also a claim about `P`'s argument types. A preservation declaration
  such as `transitiveInArg` is read for the goal's own predicate and does not descend to a
  sub-predicate ([ch. 21](21-claims-about-kinds.md)).
- *Maintenance.* A rule written against the general relation serves every relation placed
  below it, including ones added later.

**Why not the other ways.** A rule `(P ?x ?y)` ⇒ `(Q ?x ?y)` in place of the edge stores a
`Q` sentex per `P` fact and fires once per fact. The edge answers the same questions by
reading the closure, holds no copies, and leaves with one retraction. An edge from a
narrow relation to a broad one, where a closer true parent exists, misses the rules and
declarations on the closer parent.

**Audit.** For every predicate `genl`, name a tuple of the parent that is no tuple of the
child, to confirm the edge does not claim an equivalence. Read the parent's
`(direct-specs kb Q)` to check the child is placed beside its true siblings.

## genlInverse and inverse

**Practice.** When every tuple of `P` is a tuple of `Q` with the two arguments exchanged,
state `(genlInverse P Q)`. When the exchange holds both ways, so the two relations are one
relation read in the two directions, state `(inverse P Q)` and assert only one of them.

**Example.** `life.txt` relates parenthood and childhood both ways:

```clojure
(inverse parentOf childOf)
```

The `comment` on `childOf` says the two are never asserted together: "(parentOf Ann Tom)
states (childOf Tom Ann), and the two are never asserted side by side." Its
`implementationNote` adds that the inverse prover answers the one from the other, "and
retracting the one withdraws the other." The `comment` on `genlInverse` in `core.txt`
gives the one-way form: a stored `(?spec a b)` answers a `(?genl-inv b a)` goal, and "Does
not license the converse: a (?genl-inv b a) fact concludes nothing about ?spec."

**Why.**

- *Engine.* `genlInverse` edges are held beside the `genl` closure and walked with it under
  a parity bit: a `genl` edge keeps the parity and a `genlInverse` edge flips it, so a
  chain swaps the arguments exactly when it holds an odd number of `genlInverse` edges. A
  justification names the `genlInverse` edges as it names `genl` ones. A `genlInverse`
  between two predicates is forced-monotonic, as a predicate `genl` is.
- *Maintenance.* With `inverse`, a KB stores each relationship once and answers it under
  both names. Asserting both spellings stores two sentexes for one fact, and retracting one
  leaves the other.

**Why not the other ways.** A rule that swaps the arguments stores a second copy of every
tuple. Two `genlInverse` edges in opposite directions say what `inverse` says in one
sentence.

**Audit.** For every `genlInverse`, ask whether the converse also holds; if it does, the
sentence is an `inverse`.

## different-type genl
*Beware predicate genls between differently typed args*

**Practice.** Before stating `(genl P Q)`, compare `P`'s argument types with `Q`'s at each
position. When `P` admits arguments that `Q`'s types exclude, do not state the edge. Write
a guarded rule that concludes `Q` only where each argument has the type `Q` requires, and
name the type of each argument separately, since `Q`'s two positions can have different
types.

**Example.** `CxTra.txt` types `sees`'s second argument `spatial`, and an image or a video
need not be located. The note above the perception relations reads "A genl edge from
seeImage or watchVideo to sees would carry that declaration down and mint `(spatial Img)`
from `(seeImage Ann Img)`, so a rule guarded by the argument type concludes `sees`
instead":

```clojure
(set/forwardRule
  (implies (and (seeImage ?x ?y) (spatial ?y))
           (sees ?x ?y)))
```

**Example.** `CxSocial.txt` reads acquaintance from kinship only between persons:

```clojure
(set/defaultRule (set/forwardRule (implies (and (kinOf ?x ?y) (person ?x) (person ?y)) (knows ?x ?y))))
```

**Why.**

- *Logical.* `(genl P Q)` makes every `P` tuple a `Q` tuple, so `Q`'s argument types become
  claims about every `P` argument. Where `P`'s arguments are broader, the edge asserts
  something false: that every organism with kin is a person.
- *Engine.* Under the entailing reading of argument types, which is on by default, each
  `P` fact mints the memberships `Q`'s declarations demand: `(person Fido)` from a
  kinship between two dogs. Depending on the contexts the declarations sit in and on
  arrival order, the same fact may instead be refused with `:arg-type`. Neither outcome
  files a violation or a contradiction that names the edge, so nothing on the write path
  points at the cause.
- *Engine.* The guarded rule concludes `Q` only for the tuples whose arguments already
  hold `Q`'s types. Each conclusion rests on the `P` fact and the two memberships, so
  retracting any of them withdraws it.
- *Maintenance.* A widened edge corrupts the types of every term `P` is ever asserted of,
  and the damage grows with `P`'s extent.

**Why not the other ways.** Narrowing `P`'s argument types to `Q`'s makes `P` false of the
cases it was written for. Leaving `P` and `Q` unrelated loses the conclusion where it is
true. A guarded rule states exactly the subset of `P` that is `Q`.

**Audit.** Run `kb-integrity` and read `:genl-arg-widening`. Each finding names the spec,
the genl, the position, the spec's type and the type the genl demands; a spec type the
demanded type subsumes is compatible and is not reported. The pass reads `arg`
declarations and `genl` edges only, so compare `genlArg` declarations and `genlInverse`
edges by hand.

## negates: separating two relations

**Practice.** To say that no argument list satisfies two relations at once, state
`(negates P Q)`. Do not state `disjoint` between relations.

**Example.** `core.txt`'s `positiveExampleComment` for `negates` is `(negates likes
dislikes)`, and its `negativeExampleComment` explains a pair that fails: "(negates loves
hates), since one person can love and hate another at once". `abstract.txt` records why
it states no `disjoint` between `destroyedInput` and `preservedInput`: "a separation over
two relations constrains no tuple."

**Why.**

- *Logical.* `(negates P Q)` entails `(not (Q a b))` from `(P a b)`, and the converse.
- *Engine.* The `comment` on `negates` says the declaration is read down `genl` on both
  sides, that two stored tuples of one argument list under the two sides are a placed
  nogood, and that a ground denial is answered from a believed tuple of the other side.
  `negates` is forced-monotonic.
- *Engine.* A `disjoint` reads its arguments as types. A separation declaration names its
  arguments as subtypes of `thing`, so the entailing reading mints that edge for a relation
  named there, and the arity clash that follows names the separation.

**Why not the other ways.** A `disjoint` between two relations separates two sets of
one-place memberships that no relation has, constrains no tuple, and places an arity clash
on each relation.

**Audit.** For every pair of relations a change declares incompatible, confirm the
declaration is a `negates` and that a `negativeExampleComment`-style counterexample does
not defeat it.
