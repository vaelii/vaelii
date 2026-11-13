# 6. The definitional block

- **Covers:** the set of sentences every new term ships with, for a type and for a
  relation, and what the engine does with each part.
- **Not here:** what the comment in the block says → [ch. 7](07-comments.md); choosing the
  parent → [ch. 10](10-parent.md); choosing the separations → [ch. 13](13-disjointness.md);
  typing the arguments → [ch. 18](18-argument-types.md).
- **Assumes:** [ch. 5](05-search-first.md).

A term is evaluated by what the KB says about it. A symbol with no block around it has no
parent, no separations and no argument types, so a reviewer cannot tell what it entails,
whether it duplicates an existing term, or what it rules out. The block is the unit a
vocabulary change proposes and a reviewer reads.

## no naked terms

*Hypothesized vocabulary comes with its definitional assertions*

**Practice.** Every proposed term, including one in a thought experiment or a review
comment, ships as a block: its metatype or arity class, its `genl`, every `arg`, its
`disjoint`, `separating` or `orthogonal` relations to its siblings, and its `comment`.
Where they apply, the block also carries relation properties (`transitive`, `functional`,
…), example annotations and `termsRelated` or `seeAlso` links.

**Example.** abstract.txt ships `electronic_device` as a complete type block:

```clojure
(comment electronic_device "A mechanism built around an electronic circuit: the circuit and the parts that carry it make up the whole object. An organism with an implanted circuit contains an electronic device but is not one. Defined by how it is built, not by what it does, so it is rigid: a dead phone or an unplugged board is still one.")
(positiveExampleComment electronic_device "a phone")
(positiveExampleComment electronic_device "a dead phone")
(positiveExampleComment electronic_device "an unplugged board")
(genl electronic_device made)
(genl electronic_device mechanism)
(set/monotonic (orthogonal electronic_device machine))
(comment (orthogonal electronic_device machine) "A fan-cooled desktop computer is both, a wind-up clock is a machine but not electronic, and a single-board computer is electronic but not a machine.")
```

The block states no `disjoint` of its own because the separations it needs are inherited:
`(disjoint mechanism organism)` and `(disjoint mechanism substance)` reach it through its
`genl` to `mechanism`.

**Why.**

- **Logic.** A term means what the sentences about it entail. A bare symbol entails
  nothing, so a claim stated with it says nothing checkable.
- **Engine.** Each part of the block feeds one mechanism. The `genl` places the term in
  the closure, so rules on the parent fire on its members and the parent's separations
  reach it. The separations let a membership of two separated types be placed as a
  nogood. The argument declarations of a relation derive its arguments' types. The comment
  is what `describe` returns under `:comment`, and the first clause of a relation's
  comment is the template the gloss composer substitutes into; a term with no comment
  glosses as its bare name.
- **Maintenance.** A reviewer who reads a block can run every audit in this handbook on
  it. A reviewer who reads a bare term has to reconstruct the block, and two reviewers
  reconstruct it two ways.

**Why not the other ways.** Proposing a term by name and filling in the block later
produces a discussion about a term nobody has defined: each participant argues about the
block they imagine. A term asserted without its block is also live content from the first
write, so facts accumulate under it before anyone has decided what it rules out.

**Audit.** Every new term in a change carries the parts of the block that apply, and the
change states why each missing part does not apply. `kb-integrity` over the new terms
reports `:not-under-thing` for a type with no `genl` path to `thing` and `:implicit-genl`
for an edge a cover forces on it. With `:categories #{:missing-arg}`, it reports each
argument position of a declared predicate that no declaration types. `disjointness-audit`
after the change lists the new type's `:unknown` pairs, which are the separations the block
has not decided.

## The type block

**Practice.** A type's block holds these parts, in this order in its file:

| part | sentence | shipped instance |
|---|---|---|
| meaning | `comment` | `(comment arachnid "An eight-legged animal.")` |
| examples | `positiveExampleComment`, `negativeExampleComment` | `(negativeExampleComment hollow "a box crushed flat")` |
| parent | `genl` to the tightest true parent, or a cover that installs it | `(genl hollow spatiotemporal)` |
| separations | `disjoint`, `separating`, `partition`, `orthogonal` to siblings | `(set/monotonic (disjoint hollow substance))` |
| order | `type` or `metatype`, when a metatype or `typeGenl` requires it | `(type substance)` |
| links | `seeAlso`, `termsRelated` | `(termsRelated empty nonempty disjoint orthogonal)` |

The arity class of a type is `unary_predicate`. The starter loader asserts
`(unary_predicate X)` in CxUniverse for every subtype of `thing` after the KB files load. A
KB loaded another way gets no such step, so a type block that must stand on its own states
`(unary_predicate X)` itself.

**Example.** organism.txt's `arachnid` block carries meaning, examples, a parent and a
membership in the metatype that separates it from its siblings:

```clojure
(comment arachnid "An eight-legged animal.")
(positiveExampleComment arachnid "a spider")
(negativeExampleComment arachnid "an insect, which has six legs")
(genl arachnid invertebrate)
(invertebrate_class arachnid)
```

`invertebrate_class` is a `disjoint_metatype`, so the one membership separates `arachnid`
from `insect` and from every other member, and from every kind below each.

**Why.** A type is a unary predicate, and the engine reads a type through its arity, its
place in the closure and its separations. `kb-integrity`'s undeclared-arity pass reports a
`genl` node with no arity, because a rule guarded on `(unary ?t)` reads such a term as no
type and skips it. core.txt's `(predAllSpecified genl unary_predicate)` states in the KB
that every unary predicate names a `genl`, and `kb-integrity`'s specified pass audits every
visible `predAllSpecified` declaration.

**Audit.** Read each new type's block against the table, and run `kb-integrity` with the
new types as candidates.

## The relation block

**Practice.** A relation's block holds its comment, written as a signature and a
definition; its relation kind and arity; an `arg` (or `genlArg` for a position that holds a
type) for every position; its `genl` to a broader relation where one is true; and its
relation properties.

**Example.** life.txt's `siblingOf`:

```clojure
(comment siblingOf
         "(siblingOf ?first ?second) means ?first and ?second are siblings, by blood or by choice. Half-siblings count.")
(implementationNote siblingOf "Declared symmetric, so one assertion answers both orders and the two spellings store as one sentex.")
(set/monotonic (instance_relation_predicate siblingOf))
(arg siblingOf 1 causal)
(arg siblingOf 2 causal)
(generic_kinship_predicate siblingOf)
(set/monotonic (symmetric siblingOf))
```

The comment keeps the definition and the hard cases. The sentence on what the `symmetric`
declaration does to storage describes the engine, so it is an `implementationNote`
([ch. 7](07-comments.md)).

**Why.**

- **Logic.** The signature fixes which argument is which, and the properties state the
  inferences the relation licenses.
- **Engine.** `instance_relation_predicate` binds the relation to two arguments through
  core.txt's `:monotonic` edge from that mark to `binary_predicate`, so a tuple of another
  length is stored and read OUT. Each `arg` declaration derives the declared type for its
  filler under the entailing reading. `symmetric` makes the two argument orders one
  sentex. `transitive` hands the relation to a closure prover that answers chains without
  storing them. `functional` makes a second distinct value a contradiction, or a merge of
  two names for one value, as `fatherOf`'s comment describes.
- **Maintenance.** A relation without argument types accepts any filler, and the facts
  written under it are typed by nothing until someone declares the types and the
  declarations reach back over them.

**Audit.** `describe` on a new relation answers `:arity`, `:arg-declarations` and `:props`.
Each empty one is a part of the block the change either supplies or explains.
