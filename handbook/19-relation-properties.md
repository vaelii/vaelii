# 19. Relation properties

- **Covers:** the algebraic marks a relation carries (`transitive`, `symmetric`,
  `asymmetric`, `irreflexive`, `anti_symmetric`, `functional`), what the engine does with
  each, why the marks hold in every context, and how to record a property weighed and
  declined.
- **Not here:** where a relation sits under another → [ch. 17](17-predicate-hierarchy.md);
  carrying a claim along `genl` with `transitiveInArg` → [ch. 21](21-claims-about-kinds.md);
  equality and merging in general → [equality.md](../docs/equality.md).
- **Assumes:** [ch. 2](02-representation.md) (**bank the decision**),
  [ch. 17](17-predicate-hierarchy.md).

A relation property is a claim about a relation, not about any tuple of it. Each mark
changes what the engine concludes from every tuple, now and later, so each is decided by
asking whether the property holds of every possible tuple, including the hard cases.

## transitive

**Practice.** Declare `(transitive R)` when a chain of two `R` tuples always entails the
third. Do not write the closure as a rule.

**Example.** `abstract.txt` declares containment transitive. The `implementationNote` on
`locatedIn` states the engine's reading ([ch. 7](07-comments.md)): "Declared transitive, so
the transitive prover walks a chain of containments at query time and stores no conclusion
of it."

```clojure
(set/monotonic (instance_relation_predicate locatedIn))
(set/monotonic (transitive locatedIn))
```

**Why.**

- *Logical.* `(transitive R)` entails `(R a c)` from `(R a b)` and `(R b c)`.
- *Engine.* A declared-transitive relation is metadata only. Nothing about `R` enters a
  cached closure, so asserting an `R` fact is an ordinary assert. `TransitivePredicateProver`
  walks the believed facts at query time. One hop is a believed `R` fact visible from the
  asking context, a fact of a sub-predicate of `R`, the mirror of a fact when `R` is also
  symmetric, or a fact of `R`'s declared `inverse` read the other way round. A forward rule
  with an `R` antecedent is answered by the walk, and each firing rests on the handles of
  one chain of edges, so retracting a hop withdraws exactly the conclusions that crossed
  it.
- *Engine.* A query with both ends open is answered from the stored extent, not from the
  closure, because a closure is quadratic in a chain's length.
- *Maintenance.* A cycle in a declared-transitive relation is not refused. The walk guards
  with a seen set, and a cycle entails reflexivity around the loop.

**Why not the other ways.** A rule deriving `(R x z)` from `(R x y)` and `(R y z)` is the
closure written out: it stores a sentex per derivable pair, inside the fixpoint, and the
antecedents a conclusion records then depend on how far the rule had got. The declaration
stores nothing and answers the same pairs.

**Audit.** For each `transitive`, find a chain of three things where the first two links
hold and the third is false; the search for one is the check.

## symmetric

**Practice.** Declare `(symmetric R)` only when every `R` tuple's converse is true.

**Example.** `CxSocial.txt` declares the family relation symmetric, and declines symmetry
for `knows`:

```clojure
(set/monotonic (symmetric relativeOf))
```

The header comment reads "`knows` is deliberately not symmetric — a great many people
know someone who does not know them — so friendship and marriage, which *are* symmetric,
each yield acquaintance in both directions through their own symmetry rather than
through a symmetry `knows` does not have."

**Why.**

- *Logical.* `(symmetric R)` entails `(R b a)` from `(R a b)`.
- *Engine.* `symmetric` decides storage as well as inference. The entry point sorts a
  symmetric literal's arguments, so the two spellings of a pair are one sentex. A mark
  arriving after the facts re-spells the stored rows and folds a mirrored pair into one.
- *Maintenance.* A symmetry mark on a relation that is not symmetric makes the KB assert
  the converse of every tuple it ever learned. The `CxSocial.txt` note puts the cost of a
  `(symmetric knows)` in those words.

**Why not the other ways.** A rule concluding the converse stores two sentexes for each
pair. The mark stores one.

**Audit.** For each `symmetric`, name a tuple whose converse is false, or state that none
exists.

## asymmetric, irreflexive, anti_symmetric

**Practice.** Declare `asymmetric` when no two things stand in `R` both ways,
`irreflexive` when nothing stands in `R` to itself, and `anti_symmetric` when two things
standing in `R` both ways are one thing.

**Example.**

```clojure
(set/monotonic (asymmetric originatorOf))
(set/monotonic (asymmetric typeLargerThan))
(set/monotonic (irreflexive properPartOf))
```

The first is from `CxSocial.txt`, the other two from `abstract.txt`. The `comment` on
`typeLargerThan` says that the relation is "Transitive and asymmetric, so a cycle of size
claims is a contradiction the KB reports rather than a chain it walks."

**Why.**

- *Engine.* The three marks are in the forced-monotonic set. A tuple and its converse
  under an `asymmetric` mark are a nogood; at equal strength the pair is reported in
  `contradictions` with `:kind :asymmetric`. `irreflexive` makes a tuple `(R a a)` a
  clash.
- *Engine.* `anti_symmetric` merges. Two `:monotonic` tuples `(R a b)` and `(R b a)` over
  two symbols derive that `a` and `b` are one term; any other collision is a nogood.
- *Maintenance.* Each mark turns a modelling error in the data into a reported clash
  instead of a silent cycle.

**Why not the other ways.** An `anti_symmetric` mark on a relation where two distinct
things can stand in it both ways merges distinct things. `abstract.txt` declines the mark
for `partOf` for that reason ([below](#banking-a-declined-property)).

**Audit.** For each mark, name the case it rules out and confirm the case is false of
every pair, not only of the examples at hand.

## functional

**Practice.** Declare `(functional R)` when each first argument has at most one second
argument. Declare `(functionalInArg R n)` when position `n` is the determined one. A
relation whose value changes over time takes the mark too when it has one value at a
time: state each value in the time slice it holds in
([ch. 39](39-time.md#time-from-the-slice)), so that the values of two times are never
compared.

**Example.** `life.txt`:

```clojure
(set/monotonic (functional fatherOf))
```

The `comment` on `fatherOf` reads "Declared functional, one biological father to a child,
so a second, different father is not a second fact: the two names merge."

**Why.**

- *Engine.* Two `:monotonic` facts naming two different symbols for one subject derive
  `(equals V1 V2)`, justified by both facts and the declaration. Every other collision is
  a nogood the settle decides: two numbers, two strings, a compound, or a pair with a
  `:default` fact, because a merge is never defeated and so rests on `:monotonic`
  evidence alone.
- *Engine.* The mark is read up the predicate hierarchy, so `(functional parentOf)` would
  also judge two `fatherOf` values.
- *Engine.* The mark compares the values one context sees. Two time slices of one monad
  at sibling times see nothing of each other, so a value in each is never compared, and two
  status stretches that meet at an instant report no clash
  (`pr_status_true_when_test/adjacent-statuses-meet-without-a-functional-clash`). Two
  `:default` values in one context are a dilemma `contradictions` reports, and neither is
  merged (`functional_clash_test/assert-keeps-two-default-symbol-values-apart-as-a-functional-dilemma`).
- *Maintenance.* One wrong `functional` declaration merges two individuals across the KB.
  The merge is a justified derivation, so `why` names the declaration and the two facts,
  and retracting any one of them un-merges.

**Why not the other ways.** A rule concluding `equals` from two values merges what the
mark merges, and reports nothing for the collisions no merge resolves, such as two
numbers. A relation that changes over time, left unmarked, reports nothing when two
values are stated for one time. Its values stated in one context with no time compare the
values of every time, and the mark then reads a value that changed as a second value: a
reported dilemma, or a merge of two `:monotonic` symbols.

*In development:* three readings of the mark over time slices are in development:

- A slice sees neither its monad nor CxUniverse, so a `functional` mark stated there is not
  read inside a slice, and two values in one slice are not reported
  (`temporal_capability_test/a-slice-sees-its-monad-and-the-monad-does-not-see-the-slice`,
  red).
- A slice at an instant inside two overlapping stretches is not ordered under either
  stretch's slice, so the two values are not compared there
  (`pr_status_true_when_test/overlapping-statuses-clash-at-a-second-inside-both`, red).
- `try-assert` stores a second distinct symbol value, where it refuses a second number
  (`functional_clash_test/try-assert-refuses-a-second-symbol-value-of-a-functional-predicate`,
  red).

**Audit.** For each `functional`, name the subject that could have two values. Where the
values can change over time, confirm that each value sits in the slice of the time it
holds in. Where they cannot, confirm the two names would denote one thing.

## The marks hold in every context

**Practice.** State a relation property in the upper files or in the theory that defines
the relation, once.

**Example.** `core.txt` lifts each mark into `CxUniverse`:

```clojure
(decontextualized_predicate transitive)
(decontextualized_predicate symmetric)
(decontextualized_predicate functional)
```

**Why.**

- *Engine.* `(decontextualized_predicate P)` copies every `(P …)` fact, asserted or
  concluded, into `CxUniverse`, supported by the original and the declaration. Every
  context in the topology sees `CxUniverse`, so a `(symmetric P)` stated in one theory is
  the KB's claim about `P`.
- *Engine.* Canonicalization, the property tables and the definitional checks all key on
  the predicate. Two theories that disagree about whether a relation composes cannot be
  represented by a mark; such a KB states the closure as a rule in the theory that holds
  it, or uses two predicates.

**Why not the other ways.** A property stated per context would let one relation sort its
arguments in one theory and not in another, and the definitional checks would disagree
about one tuple.

**Audit.** For each new mark, confirm the relation means the same thing in every context
that can see it. Where it does not, the change needs two predicates.

## Banking a declined property

**Practice.** When a property is weighed and declined, state its negation in the KB beside
the relation, with a `;;` note giving the counterexample (**bank the decision**).

**Example.** `abstract.txt` declines antisymmetry for parthood:

```clojure
(set/monotonic (transitive partOf))
(set/monotonic (reflexive partOf))
(not (anti_symmetric partOf))
```

The note above the denial reads "Antisymmetry was weighed and declined: two coextensive
regions stay two regions, so two things each part of the other are not thereby one."

**Why.**

- *Logical.* `(not (anti_symmetric partOf))` records a decision. A missing
  `(anti_symmetric partOf)` records only that nobody stated it.
- *Engine.* `anti_symmetric` is forced-monotonic. The note in `abstract.txt` gives the
  consequence: the denial is believed while no `(anti_symmetric partOf)` is, and loses to
  one that is. A later change asserting the mark therefore meets the stated decision, and
  the denial goes OUT where the mark is believed.
- *Engine.* For a property outside the forced-monotonic set, such as `transitive`, a mark
  stated beside its denial is an ordinary negation pair: the settle places the two as a
  nogood decided by strength, and two `:default` sentences are a dilemma `contradictions`
  reports.
- *Maintenance.* The next reviewer sees the decision and its reason in the file, where a
  review thread or a code comment outside the KB would not reach them.

**Why not the other ways.** Silence leaves the question open for the next author to answer
again, and nothing reports a reversal. A `(not …)` stated for a property nobody weighed
claims a decision that was not made.

**Audit.** For each property a change weighed and declined, the KB states its negation,
and behind each `(not …)` stands a decision with its counterexample in a `;;` note.
