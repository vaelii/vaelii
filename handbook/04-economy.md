# 4. The economy of statements

- **Covers:** stating the strongest true sentence; representing each distinction once;
  and leaving unstated what the KB already derives, with the two marked exceptions.
- **Not here:** the strongest form applied to parents → [ch. 10](10-parent.md), to
  separations → [ch. 13](13-disjointness.md) and [ch. 14](14-covers.md), and to argument
  types → [ch. 18](18-argument-types.md); searching for an existing representation →
  [ch. 5](05-search-first.md).
- **Assumes:** [ch. 1](01-true-and-useful.md), [ch. 2](02-representation.md).

Three principles decide how much a KB says. **strongest form** picks the sentence, **DRY**
picks the representation, and **state it once** decides whether a sentence that follows
from others is written at all. All three rest on one engine fact: vaelii derives a great
deal from little, through the `genl` closure, inherited separations and argument-type
entailment, so a sentence the engine could have derived is a second source for the same
belief.

## strongest form

*State knowledge in its strongest form*

**specPrinciple:** tightest parent, partition over disjoint, classify before you constrain

**Practice.** If you are about to assert P, and Q is also true and Q implies P, assert Q.

- **Instances.** Use the most specific true type. If it does not exist, mint it, with its
  `genl`, rather than settle for the general one.
- **Argument types.** Type each argument position as tightly as the truth allows. If only
  one kind of thing can fill a position, the declaration names that kind.
- **Disjointness.** State a separation at the highest level at which it is true. Once
  `(disjoint A B)` holds, a separation of a subtype of A from B is not stated as well.

**Example.** A dog in the test world is stated a `dog`, and `(mammal Muffet)` and
`(animal Muffet)` follow:

```clojure
(dog Muffet)
```

Argument positions name the one kind that fills them (life.txt, society.txt):

```clojure
(arg eats 2 food)
(arg birthDate 2 uninterrupted_time)
(arg speaks 2 language)
```

Separations sit at the top of what they separate (abstract.txt). The first line reaches
`organism`, `body_part` and every kind below either; the second reaches `machine`,
`electronic_device` and every kind below `mechanism`:

```clojure
(set/monotonic (disjoint biological substance))
(set/monotonic (disjoint mechanism organism))
```

**Why.**

- **Logic.** Q entails P, so a KB holding Q holds P as well, and a KB holding only P has
  lost Q.
- **Engine.** Matching a unary antecedent fans out over the `specs` closure, so a rule on
  `(animal ?x)` fires on `(dog Muffet)`, and `isa?` answers `mammal` for Muffet on demand.
  The converse does not hold: a rule or a claim on `dog` never reaches a term stated only
  `animal`. Under the entailing reading of argument types, the declared type is derived
  for each argument that fills the position, so `(eats Muffet Bone1)` derives `(food
  Bone1)`, and the tighter the declaration, the more each fact concludes. A separation is
  inherited by every subtype of each side, so one `disjoint` at the top separates every
  pair below it.
- **Maintenance.** A strong statement keeps working as the KB grows. A kind added below
  `biological` next year is separated from `substance` with no new sentence. A weak
  statement needs a companion statement for each new member, and the companion an author
  forgets is a pair the KB cannot rule out.

**Why not the other ways.**

- **A general instance type.** A term stated `bird` when it is a penguin misses every
  penguin rule. CxBiology concludes `(not (able ?x flying))` from `(penguin ?x)`,
  and that conclusion never reaches it.
- **An argument type broader than the truth.** The declaration derives a weaker membership
  than the facts support, and a declaration of `thing` derives none, so it rules out
  nothing and types nothing.
- **An argument type narrower than the truth.** The declaration derives a false
  membership for each filler outside the narrow type. `doneBy` declares `thing` at its
  second position for this reason: a machine or a storm can be the doer, and a type such
  as `agent` there would conclude each of them an agent.
- **A separation low in the hierarchy.** Each sibling then needs its own line, and a kind
  added later is unseparated until someone writes another.

**Audit.** For every line of a change, ask whether a more specific true fact entails it.
`kb-integrity` with `:categories #{:derivable-stated-edge}` reports each stated `genl` or
`disjoint` that still holds with that statement removed, with the path or the other
separation that derives it. `kb-quality`'s `:declarations` reading lists under
`:typed-thing` each declaration that types a position `thing`, with its predicate's stored
extent, so a reviewer can ask whether a narrower type is true of every filler.

## DRY

*One thing, one representation*

**specPrinciple:** factor out commonalities, look before you mint, state it once

**Practice.** Represent each distinction once at the vocabulary level. When the same thing
has two representations, merge them where feasible. Merging is infeasible when the two
encodings put some dimension (time, modality, provenance) in structurally different
places. Then keep both, bridge them with explicit rules, and say why in a comment.
Instance-level duplication can be correct: two sources asserting one fact, kept apart for
provenance, are two claims.

**Example.** `parentOf` is the primitive of the kinship theory, and `childOf` is declared
its inverse rather than asserted beside it (life.txt):

```clojure
(inverse parentOf childOf)
```

`(parentOf Ann Tom)` answers `(childOf Tom Ann)` through the inverse prover, and retracting
the one withdraws the other. `fatherOf` and `motherOf` are narrower relations, not second
encodings, and CxKinship places each under the primitive with its arguments exchanged:

```clojure
(genlInverse fatherOf parentOf)
```

A Davidsonian event encoding and an n-ary predicate for the same happening are the
standard case where a merge is infeasible: the event encoding states the time as a fact
about the event, and the n-ary predicate takes it from the context the fact holds in.
[ch. 20](20-events.md) states the bridge.

**Why.**

- **Logic.** Two encodings of one thing are two predicates that the KB does not know to be
  equivalent. Nothing asserts that a fact in one has a counterpart in the other, so the
  two can contradict each other with no sentence in the KB saying so.
- **Engine.** A query matches one functor, a rule fires on the predicates its antecedents
  name, and an argument declaration or a separation constrains the predicate it is stated
  on. Each mechanism therefore reads one encoding and misses the other. With one
  representation, every query, rule and declaration reaches every fact.
- **Maintenance.** Authors add facts to one encoding and rules to the other, and the two
  drift apart. A reader cannot tell which encoding is current, and a change to one leaves
  the other stale.

**Why not the other ways.** Two independent predicates kept in step by a pair of swapping
rules restate a declaration the engine implements. `kb-integrity`'s rule-macro pass reads
the pair `(P ?a ?b) ⇒ (Q ?b ?a)` and `(Q ?a ?b) ⇒ (P ?b ?a)` as the `inverse` declaration
it repeats and reports it. A merge across a dimension the two encodings place differently
loses that dimension for one of them, which is why the bridge with its comment is the form
there.

**Audit.** For each new term, search for an existing representation of the same
distinction ([ch. 5](05-search-first.md)). `kb-integrity`'s `:rule-macro` category
reports rules that restate an engine declaration, and `kb-quality`'s `:subsumption`
reading lists each rule that another stored rule already covers. Each kept pair of
encodings has a comment naming the dimension that blocks the merge.

## state it once

*Don't state what the KB already derives*

**genlPrinciple:** DRY

**Practice.** Leave unstated a fact that follows from facts already stated: a `genl`
implied by an intersection, a cover or a chain of edges, or a `disjoint` implied by a
partition or by two types' placements. An argument declaration is not dropped for being
derivable: each relation declares each of its positions, even where a `genl` parent's
declaration gives the type ([ch. 18](18-argument-types.md#each-position-declared-on-the-relation)).
Two exceptions apply. A stated `genl` or `disjoint` kept under one is marked with an
`(acknowledgedFinding :derivable-stated-edge S "reason")` record naming the sentence and
the exception, and any other kept sentence with a `;;` note saying which one:

- **Implementation.** The engine needs the fact stated, because it reads the fact directly
  and does not derive it, or because the fact must hold in a context that cannot see the
  facts it follows from.
- **Documentation.** Stating the fact makes the KB easier to read or browse, such as the
  parent edges an intersection implies.

The rule holds for comments too. A comment does not restate a definitional assertion: no
"the complement of X", no "with Y it partitions Z" and no bare member list when a
`partition`, `intersection` or `genl` says it. The comment says what membership means,
with examples, and leaves the structure to the assertions.

**Example.** abstract.txt states the partition and leaves the part edges unstated, and its
note says so:

```clojure
;; Every tangible is made or natural, and no tangible is both.  The partition installs
;; the genl edges from made and from natural to tangible, so neither edge is stated.  A
;; tangible denied made is concluded natural.
(partition tangible made natural)
```

An edge nothing derives is stated, and the note says why it is not redundant (abstract.txt,
core.txt):

```clojure
(genl spatial_event spatiotemporal)
(set/monotonic (genl situation intangible))
```

For the documentation exception, space.txt writes each converse pair inert, so a reader
finds the pair while the spatial algebra computes converses itself and the inert sentence
supports no belief:

```clojure
(set/inert (inverse eastOf westOf))
```

**Why.**

- **Logic.** A derivable sentence adds no content: the KB with it and the KB without it
  have the same consequences.
- **Engine.** A stated sentence is a premise, and a premise is its own support under truth
  maintenance. A `partition` installs each part's `genl` edge supported by the partition
  sentex, so retracting or defeating the partition drops the edges with it. A separately
  stated `(genl made tangible)` would stay believed after the partition left, and would
  assert an edge nobody chose any more. The same holds for a `disjoint` stated below a
  separation that later moves: the restated pair keeps the separation alive where its
  source has gone.
- **Maintenance.** A reader of a redundant line cannot tell which line is the source and
  which the copy. When the source is revised, the copy is left behind. A marked exception
  tells the next reviewer that the redundancy was chosen and why, so they keep it or drop
  it on purpose.
- **Maintenance.** An argument declaration is a constraint on its own relation. Stated on
  the relation, it does not change when a parent's declaration is revised.

**Why not the other ways.** Stating every derivable fact for completeness doubles the
premises that a single change must find and revise. Stating nothing for a reader, where an
inert or marked restatement would help, makes a term hard to browse. The two marked
exceptions keep both needs apart: the inert form documents without supporting belief, and
a marked premise is a known second source.

**Audit.** For every new `genl` or `disjoint`, ask whether the rest of the KB already
entails it, and drop it or mark which exception applies. Keep every `arg`, `genlArg` and
`quotedArg` that types a position of its own relation. `kb-integrity` with
`:categories #{:derivable-stated-edge}` reports each stated `genl` or `disjoint` with
another supporter, as `:path` (an edge chain that reaches the same pair), `:also-stated-by`
or `:separated-by`, and carries the reason of its acknowledgment as `:acknowledged`. For
every comment, delete each clause that a definitional assertion already states.
