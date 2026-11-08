# 12. Identity

- **Covers:** deciding whether two kinds can share an instance by asking what ends a member
  of each; rigid and anti-rigid types; and when a kind may sit below a property.
- **Not here:** stating the separation once the answer is no →
  [ch. 13](13-disjointness.md); stating the overlap once the answer is yes →
  [ch. 15](15-overlap.md); a thing that changes kind over time →
  [ch. 35](35-change-over-time.md).
- **Assumes:** [ch. 9](09-differentia.md), [ch. 10](10-parent.md).

Two kinds share an instance only if one thing can satisfy both kinds' conditions for
staying in existence. The question "can one thing be both?" is therefore a question about
identity: what makes a member the same member over time, and what event ends it.

## what ends a member

*Can one thing be both? Ask what ends a member of each*

**Practice.** Before stating an `orthogonal` between two kinds, or removing a `disjoint`
between them, ask what ends a member of each. An artifact survives breakage as a defective
one: a sunk ship is still a ship. Kinds whose members persist under incompatible
conditions share no instance, and a case that seems to be both is one kind plus a relation
or a classification. Being made on purpose does not change what a thing is.

**Example.** abstract.txt defines a mechanism by its construction, so a mechanism persists
while its construction does, running or not. An organism, in core.txt's comment, is
"Something alive in its own right: it is born, grows, reproduces, and (by default) dies."
The two persist under different conditions, and abstract.txt separates them with a note
saying how far the separation reaches:

```clojure
(set/monotonic (disjoint mechanism organism))
(set/monotonic (disjoint container organism))
```

A cloned sheep looks like a case of both a made thing and an organism. abstract.txt does
not make it a member of a made kind with its own identity. The file classifies tangibles by
where their form came from, with `origin_type`, and crosses that classification with
`organism`:

```clojure
(comment origin_type "A type of tangible by where its form came from: made or natural.")
(origin_type made)
(origin_type natural)
(typeOrthogonal origin_type organism)
```

The note above the block gives the witness: "A cloned sheep is a made organism and a wild
sheep a natural one." The sheep is one kind, `organism`, plus an origin, and
`mechanism`'s negative examples list it: "a cloned sheep".

Where two kinds do share instances, the `orthogonal` carries its witnesses as a comment on
the declaration itself:

```clojure
(set/monotonic (orthogonal electronic_device machine))
(comment (orthogonal electronic_device machine) "A fan-cooled desktop computer is both, a wind-up clock is a machine but not electronic, and a single-board computer is electronic but not a machine.")
```

**Why.**

- **Logic.** A thing has one set of persistence conditions. If one kind's members survive
  an event that ends the other kind's members, a thing in both kinds would both survive
  the event and not survive it, so no thing is in both. A case that seems to be both is
  one thing under one kind, and the second description is a relation it stands in or a
  classification that crosses the kind.
- **Engine.** A `disjoint` reaches every type below each side through the `genl` closure,
  so `(disjoint mechanism organism)` separates `machine`, `electronic_device` and every
  kind below them from every organism kind. A thing stated a member of both is placed as a
  membership nogood instead of believed in both. An `orthogonal` states that the two types
  are not disjoint and that neither is a `genl` of the other. It is forced-monotonic, and it
  is not inherited along `genl`, so each overlapping pair is stated. A separation over the
  pair or over a supertype of each, or a `genl` edge between them, makes the `orthogonal` a
  one-member nogood, and the separation stays believed.
- **Maintenance.** An `orthogonal` that banks a declined separation needs no witness, and
  a later separation over a supertype of the pair makes it a nogood. With a witness
  stated, the reviewer of that separation finds the counterexample in the KB.

**Why not the other ways.** Removing a `disjoint` because one case seems to be both kinds
gives up the separation for every instance of both kinds, and the case usually turns out
to be one kind plus an origin or a role. Stating an `orthogonal` from a vague sense that
the kinds overlap, without asking what ends a member of each, banks a decision nobody
weighed.

**Audit.**

- Every `orthogonal` between kinds names a witness when one is known, a thing that is
  both, and says what ends it under each kind. The witness goes in a `comment` on the
  `orthogonal` sentence or in a `;;` note beside it.
- `kb-integrity` reports `:orthogonal-over-separation` for an `orthogonal` declaration,
  or a `siblingDisjointException`, that a separation stated over its pair contradicts. The
  pass reads the separations with no exemption applied, because the exception would hide
  the conflict from every read.
- `disjointness-audit` reports a pair whose statuses hold `:orthogonal` with a `:witness`:
  `:declared` for a stated `orthogonal`, `:shared-instance` or `:shared-spec` for an overlap
  the KB shows, and `:unwitnessed-spec` for a shared subtype with no known instance.

## Rigid and anti-rigid types

**Practice.** For each new type, decide whether it is rigid or anti-rigid, and say which in
the comment. A rigid type holds of a member for as long as the member exists: nothing
stops being a mechanism while it exists. An anti-rigid type holds of a member at some times
and not others: a thing can stop being hollow and go on existing. Write the case that shows
the decision into the comment.

**Example.** abstract.txt's `electronic_device` states its rigidity and the case that
shows it, and `hollow` states the opposite:

```clojure
(comment electronic_device "A mechanism built around an electronic circuit: the circuit and the parts that carry it make up the whole object. An organism with an implanted circuit contains an electronic device but is not one. Defined by how it is built, not by what it does, so it is rigid: a dead phone or an unplugged board is still one.")
(comment hollow "Has, at that time, an interior space that other things can occupy. A thing can stop being hollow and still exist: a box crushed flat stops being hollow, and a hand is hollow only while it is cupped. What a thing is shaped like, not what it is for, and a container is made to be hollow. Spatiotemporal rather than tangible, since a cave is a space in rock and is made of nothing.")
```

A thing that passes through two kinds in turn, as a caterpillar becomes a butterfly, is
one organism under a rigid kind, `lepidopteran`, with each stage an anti-rigid type below
it. organism.txt states the stages as `diachronicallyDisjoint`, not `disjoint`.

**Why.**

- **Logic.** A rigid type gives its members their identity, so it decides what counts as
  the same member over time. An anti-rigid type is a phase or a role a member of some
  rigid kind passes through. A type defined by structure is rigid (**no teleology**,
  [ch. 9](09-differentia.md)); a type defined by a shape, a state or a stage is anti-rigid.
- **Engine.** A membership is checked without time. core.txt's comment on
  `diachronicallyDisjoint` says the relation is "Stated and queryable, not enforced:
  memberships are checked without time", so the engine does not tell an instance that is
  in both types at once from one that is in each in turn. A `disjoint` between two anti-rigid stages
  of one kind would make the organism that passes through both a membership nogood, so the
  stages take `diachronicallyDisjoint`, which states the constraint and places no clash. A
  `disjoint` between two rigid kinds is true at every time, so the engine's timeless check
  is correct for it.
- **Maintenance.** A comment that states the type's rigidity and its deciding case settles
  each later question of whether a separation over the type is true.

**Why not the other ways.** Leaving rigidity unstated lets a reviewer separate an
anti-rigid type from a kind its members pass into, and the separation then makes every
member that changes a clash.

**Audit.** Each new type's comment says whether a member can stop being one and go on
existing, with an example. Each separation the change states between two types is between
rigid types, or between types whose members can never pass from one to the other.

## A kind may sit below a property

**Practice.** A kind may be placed under a property it always has. Whether a name is
spelled as a noun or as an adjective is a style hint, not a rule of the hierarchy. The
constraint is OntoClean's: an anti-rigid type cannot subsume a rigid one, because a
property a thing can stop having cannot subsume a kind a thing never stops being.

**Example.** CxBiology states the warm-blooded classes by `genl` edges, and denies the
property of the cold-blooded classes by rules, with the reason in a note: "Every bird and
every mammal is warm-blooded, so each is placed under warm_blooded by a genl edge; the
three cold-blooded classes deny it by a rule, since a genl edge states no denial."

```clojure
(genl bird warm_blooded)
(genl mammal warm_blooded)
(set/forwardRule (implies (and (amphibian ?x)) (not (warm_blooded ?x))))
(set/forwardRule (implies (and (fish ?x)) (not (warm_blooded ?x))))
(set/forwardRule (implies (and (reptile ?x)) (not (warm_blooded ?x))))
```

**Why.**

- **Logic.** "Every bird is warm-blooded" is a subsumption from `bird` to `warm_blooded`,
  and nothing in it makes `warm_blooded` a kind that birds are a sort of. OntoClean allows
  a non-sortal above a sortal. A bird does not stop being warm-blooded while it is a bird,
  so the property does not change under the kind.
- **Engine.** A type is any unary predicate, and the `genl` closure reads a property and a
  kind the same way. The edges make every bird and every mammal a member of `warm_blooded`
  by the closure, with nothing stored per animal, as `warm_blooded`'s comment in life.txt
  says: "never asserted of any particular animal". The rules place `(not (warm_blooded ?x))`
  on each fish, amphibian and reptile. The five vertebrate classes are pairwise disjoint
  through `vertebrate_class`, so no typed animal reaches both the membership and the
  denial.
- **Maintenance.** The property is stated once per class, and a new species placed under a
  class inherits it with no further sentence.

**Why not the other ways.** Forbidding any spec below a property leaves "every bird is
warm-blooded" with only a rule to state it, and a forward rule's conclusion is a stored
membership per bird where the edge stores nothing per bird. Placing a rigid kind under an anti-rigid
property, a property its members can lose, makes the kind's members leave the property
while staying in the kind, which the edge says cannot happen.

**Audit.** For each `genl` from a kind to a property in a change, check that no member of
the kind can stop having the property while it remains a member: the property is rigid
over the kind, or the property's comment says how a member keeps it.
