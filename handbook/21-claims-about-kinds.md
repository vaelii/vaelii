# 21. Claims about kinds

- **Covers:** relations whose arguments are kinds; carrying a claim along `genl` with
  `transitiveInArg` and `transitiveInArgInverse`; how a claim about a nearer kind stops an
  inherited one; why a claim about a kind does not reach its members; the `predAll`
  family, which states how each position of a binary relation is quantified.
- **Not here:** argument types for kinds (`genlArg`) → [ch. 18](18-argument-types.md);
  rules with exceptions → [ch. 30](30-exceptions.md); rules generated from a declaration →
  [ch. 34](34-generators.md); skolem witnesses → [ch. 33](33-existentials.md).
- **Assumes:** [ch. 17](17-predicate-hierarchy.md), [ch. 18](18-argument-types.md),
  [ch. 19](19-relation-properties.md).

`(typeLargerThan dog cat)` is a claim about two kinds. Whether the claim also holds of a kind
of dog and a kind of cat is not decidable from the sentence. The claim distributes for
some relations and not for others: a chihuahua is a kind of dog, a maine coon a kind of
cat, and the maine coon is bigger. The KB therefore states the distribution per relation
and per position.

## Preservation is declared, per relation and per position

**Practice.** For a relation between kinds, decide for each position whether a claim about
a kind holds of the kind's subkinds, of its supertypes, or of neither. Declare each
direction that holds with `transitiveInArgInverse` (down `genl`, to subkinds) or
`transitiveInArg` (up `genl`, to supertypes).

**Example.** `abstract.txt` declares downward preservation on both positions of
`typeLargerThan` at `:monotonic`:

```clojure
(set/monotonic (type_relation_predicate typeLargerThan))
(set/monotonic (transitive typeLargerThan))
(set/monotonic (asymmetric typeLargerThan))
(set/monotonic (transitiveInArgInverse typeLargerThan 1 genl))
(set/monotonic (transitiveInArgInverse typeLargerThan 2 genl))
```

`life.txt` declares the two positions of `capabilityType` in opposite directions:

```clojure
(set/monotonic (transitiveInArgInverse capabilityType 1 genl))
(transitiveInArg capabilityType 2 genl)
```

Its `comment` says the first carries a claim about a kind down to its subkinds ("a kind of
bird flies with nothing written about it") and the second carries it up the hierarchy of
happening kinds ("flying is a kind of travelling, so a kind that can fly can travel").
`partType` in `abstract.txt` is declared on the first position only; its `comment` says
"birds having wings says nothing about which kinds of wing they have."

**Why.**

- *Logical.* `(transitiveInArgInverse P n R)` licenses `(P … A …)` from a stored `(P … W …)`
  when `(R A W)` holds, and `transitiveInArg` licenses it when `(R W A)` holds. With `R` =
  `genl`, the first is downward inheritance and the second upward. The names match the
  direction of Cyc's `transitiveViaArgInverse` and `transitiveViaArg`; the argument order
  is `(P n R)`.
- *Engine.* `R` must be transitive. `assert` refuses a declaration naming a relation that is
  neither `genl`, `genlCx` nor declared `(transitive R)`, as `:not-well-formed`, because the
  reach is walked to a fixpoint and would manufacture a composition nobody declared.
  Retracting `(transitive R)` withdraws the inheritance while the declaration stays stored.
- *Engine.* A declaration is read for the goal's own predicate and does not descend to a
  sub-predicate. A sub-predicate's facts still answer the super-predicate's goals, so facts
  travel up the predicate hierarchy and licences do not travel down it.
- *Maintenance.* A kind added below `dog` is larger than `cat` from the moment its `genl`
  edge holds, with nothing written about it.

**Why not the other ways.** A rule that copies a kind-level claim to every subkind stores
one sentex per subkind and has no notion of a nearer claim stopping it. An undeclared
distribution assumed by the engine would be false for the relations it does not hold of,
and nothing in a sentence says which case it is in.

**Audit.** For each relation between kinds, each position has either a preservation
declaration or a banked denial. `core.txt` banks the four denials for `orthogonal`
([ch. 15](15-overlap.md)).

## A nearer claim stops an inherited one

**Practice.** State an exception to a kind-level claim as a claim about the nearer kind.
Do not write a rule exception for an inherited claim.

**Example.** `CxBiology.txt`:

```clojure
(capabilityType bird flying)
(not (capabilityType penguin flying))
(capabilityType butterfly flying)
(not (capabilityType caterpillar flying))
```

The note above the first pair reads "an inherited default is undercut by a claim about the
nearer kind, so stating that penguins do not fly stops the inheritance at penguin and
leaves its siblings flying."

**Why.**

- *Engine.* The specific claim undercuts the general one: the inherited claim does not
  fire for that pair, nothing is derived, and `contradictions` stays empty. Two claims are
  compared along the relation the inheritance travels down, here `genl`, so a claim about
  `penguin` is nearer than one about `bird` because `penguin` is below `bird`. Claims that
  are incomparable come back `:ambiguous`, and the prover answers nothing.
- *Engine.* A `:monotonic` general claim is never undercut. A contrary specific claim is
  then the weaker member of a nogood, stored and not believed. A `:default` general claim,
  as `(capabilityType bird flying)` is, yields to the nearer claim.
- *Maintenance.* The note in `CxBiology.txt` gives the reason the negative is a stated
  sentence: it is a positive claim that penguins are flightless, which an application can
  query and argue from, where the absence of a flight claim says nothing.

**Why not the other ways.** An `exceptWhen` has nothing to bite on here: the reach is the
taxonomy's, and there is no rule to block. A `:monotonic` general claim beside a known
exception makes the exception lose.

**Audit.** For each inherited claim with a known exception, confirm the general claim is
`:default` and the exception is stated about the nearest kind it is true of.

## Kinds and members are different claims

**Practice.** Keep a claim about a kind on the kind. Carry it to the kind's members only
with a rule written where the kinds are, and choose the quantifier reading the rule
encodes.

**Example.** `CxAnatomy.txt` states what kinds of thing have what kinds of part, as
`partType` claims such as `(partType bird wing)`, and concludes nothing about an
individual. `CxBiology.txt` writes the descent for flight as a default rule with its
exception:

```clojure
(exceptWhen (penguin ?x)
  (set/defaultRule (set/forwardRule (implies (and (bird ?x)) (hasCapability ?x flying)))))
```

**Why.**

- *Logical.* "Birds have wings" and "this bird has a wing" are two claims. Going from the
  first to the second needs a quantifier reading, every bird or some bird, and the
  sentence does not fix one.
- *Engine.* Preservation moves an argument along a relation and leaves the predicate and
  its level alone. `relation_kind` is a `disjoint_metatype` over `type_relation_predicate`
  and `instance_relation_predicate`, so one predicate that related kinds and things at
  once would be a clash. `typeToInstancePred` records which kind-level and thing-level
  predicates pair, and the engine infers nothing from it.
- *Maintenance.* A guessed quantifier reading turns a claim about kinds into a false claim
  about individuals, and nothing reports it.

**Why not the other ways.** One symbol read at both levels has to declare one argument
check for each position, and `life.txt`'s `comment` on `capabilityType` says that choice
"mistypes whichever half it was not written for."

**Audit.** For each kind-level relation, name its thing-level partner if one exists, and
confirm any descent between them is a rule with a stated quantifier reading.

## The predAll family

**Practice.** When a binary relation's positions are quantified over collections, state
the quantifier pattern with the `predAll` family instead of a rule with a variable in its
consequent. Choose the class by what the KB should do: an *Instance* declaration generates
a rule, an *Exists* declaration records a requirement and derives nothing, and a
*Specified* declaration states a requirement checked by an audit.

**Example.** `core.txt` states two *Specified* requirements of the upper ontology itself:

```clojure
(predAllSpecified typeGenl at_least_metatype)
(predAllSpecified genl unary_predicate)
```

The note above them reads "Every at_least_metatype names a type its instances specialize,
and every unary_predicate names a genl."

**Why.**

- *Engine.* `predAllInstance` and `predInstanceAll` are rule generators: `core.txt`'s
  declaration beside each one is a rule whose consequent is a rule, so each fact grounds a
  concrete rule with a concrete functor. The four *Exists* relations derive nothing, and
  `exists-violations` audits one declaration when asked. `predAllSpecified` and
  `predSpecifiedAll` derive the required filler type from the predicate's own argument
  declarations and are audited by `specified-violations` and
  `all-specified-violations`, which read the KB and store nothing.
- *Engine.* A *Specified* requirement is satisfied only by a determinate filler. A skolem
  constant is indeterminate, so a witness the engine invented does not satisfy it, and an
  *Exists* placeholder an author wrote does.
- *Maintenance.* A requirement stated as a sentence is visible to the next author and
  checked at each audit, where a requirement held only in a reviewer's head is neither.

**Why not the other ways.** A rule with a variable functor in its consequent is filed
under the catch-all for concluding rules, and the query planner then sees a candidate rule
for every predicate in the KB.

**Audit.** Run `all-specified-violations` from the context the change targets, and
discriminate on `:status`: a `{:status :gap …}` entry carries no `:violations` key and
reports a declaration whose predicate has no visible slot typing. `kb-integrity` composes
the same audit under `:all-specified-violations`.
