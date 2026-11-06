# 3. Truth, not provability

- **Covers:** stating a sentence in its natural form whatever the engine proves from it;
  shipping the right ontology when it collides with an engine limit; and order
  independence, the property that lets an author write sentences in any order.
- **Not here:** negation as failure and when a closed extent turns "not proved" into
  "false" → [ch. 32](32-negation.md); strength classes → [ch. 24](24-strength.md).
- **Assumes:** [ch. 1](01-true-and-useful.md), [ch. 2](02-representation.md).

An author writes what is true. The engine decides how to prove it. The two jobs stay
separate in vaelii: the engine canonicalizes a sentence before it stores it, plans its
own search, and computes belief from the stored content alone. The KB therefore gains
nothing when an author shapes a sentence for the prover, and it loses whatever the
reshaping gave up.

## truth, not provability

*Whether a sentence is true doesn't depend on how the engine proves it*

**Practice.** State true facts and rules in their natural form, without knowledge of the
inference engine. Write conjuncts in any order. Where the natural form costs too much or
proves less than it should, record the gap as an engine limitation and keep the form
(**ontology over quirk**, below). Read a failure to prove a sentence as "unknown", never
as evidence that the sentence is false.

**Example.** A type defined as the overlap of two others is stated with `intersection`
(abstract.txt):

```clojure
(intersection causal_event causal event)
(intersection spatial_event event spatial)
```

core.txt's rules for `intersection` derive both directions of the definition. Forward
rules install the edges `(genl causal_event causal)` and `(genl causal_event event)`, and a
generated rule concludes `(causal_event X)` from `(causal X)` and `(event X)`. A rule's
antecedents are written in the order a reader finds natural, as in abstract.txt's rule
that a tangible output of an intentionally initiated event is made:

```clojure
(set/forwardRule (implies (and (tangibleOutput ?e ?x) (performedBy ?e ?d)) (made ?x)))
```

**Why.**

- **Logic.** A conjunction is true or false whatever order its conjuncts are written in,
  and a sentence's truth is fixed by what it says about the world, not by the path a proof
  takes. A definition stated as two `genl` edges says that each member of the defined type
  is a member of both parents. It says nothing about a member of both parents, so the
  converse, which the definition asserts, is lost.
- **Engine.** vaelii canonicalizes a rule's antecedents at storage, so their written order
  is not recoverable and cannot steer anything. A conjunctive goal is ordered by a
  cost-based planner, and `query-plan` shows the order it chose. Sentences identical up to
  variable names, antecedent order, symmetric argument order or comparison direction store
  as one handle. The engine reads open-world: a goal it cannot prove answers unknown, and a
  negation is answered from a stated denial or from a mechanism that proves one, such as a
  separation the reader sees or a granted closed extent, never from a failed proof. A cover, for example, concludes the remaining part of a whole
  only from believed denials of the other parts, never from parts that merely cannot be
  proved.
- **Maintenance.** A sentence shaped to one engine's search records a property of that
  engine. When the engine improves, the KB still says the weaker or stranger thing, and
  nothing reports it. A sentence in natural form keeps its meaning across engine versions,
  and a reader takes it at face value.

**Why not the other ways.**

- **Reshaping for proof.** Splitting a definition into the half the engine proves fastest,
  or reordering antecedents so a solver finds answers sooner, gives up meaning and buys no
  speed in vaelii, since the planner and canonical form ignore the authored shape.
- **Reading failure as falsity.** Asserting `(not S)` because `S` was not derived states
  a negation nobody established. A later fact establishing `S` then meets a clash with a
  denial that rests on nothing.

**Audit.** For each definition, ask whether it is stated in full (an `intersection`, a
`partition`, a defining rule) or only in the direction the engine proves. For each
expected conclusion that does not derive, find which mechanism stops it before changing
any sentence: `escalate` climbs the eight answering levels in cost order and returns the
first that answers the goal, `query-plan` shows the search, and `why` and `why-not` show the support of a
stored sentex or the reason it is not believed. A conclusion that should follow and does
not is an engine finding, recorded with an `implementationNote` on the term.

## ontology over quirk

*Ship the right ontology over an engine quirk*

**Practice.** When the right form collides with an engine quirk, a fragile test or extra
work, ship the right form and fix the engine or the test. A workaround that weakens the
ontology needs an explicit decision, recorded beside the sentence it weakens, with an
`implementationNote` naming the limit. Surface a real engine bug that would corrupt
answers. Never work around it in silence.

**Example.** core.txt keeps `intersection` the right form for a definition and records
where the engine stops: an `implementationNote` on `intersection` says that the defining
rules are stated for two and for three intersected types, so an intersection of four or
more derives neither its `genl` edges nor its memberships. A second note records an
explicit workaround. The memberships that classify `spatial` and `aspatial` by location
in space are written at default strength, and the note on `spatiality_type` says why:
written monotonic, the orthogonals derived from them carry justifications that differ
between the authored load order and a reloaded text export.

```clojure
(spatiality_type spatial)
(spatiality_type aspatial)
(orthogonalMetatypes spatiality_type temporality_type)
```

core.txt makes one more explicit decision of this kind. It places `spatiotemporal` below
`physical` and `temporal` by `genl` edges, and a `;;` note states the definition,
`(intersection spatiotemporal physical temporal)`, as documentation rather than as a
premise: the intersection's membership rule would store a membership for every term under
both types, and nothing reads one. The note says that the converse is not concluded.

**Why.**

- **Logic.** A workaround changes what the KB says. The weakened sentence may be true and
  entail less, or it may be false in the cases the quirk does not reach.
- **Engine.** vaelii's correctness claims are stated over the stored knowledge: belief is
  a function of the stored content, the same knowledge in any order yields the same
  beliefs, and `order_independence_test` checks each scenario under every permutation of
  its writes. A quirk is a place where one of those claims fails. Shipping the right form
  keeps the test suite pointed at the failure. Weakening the ontology to dodge it hides the
  failure from every test that would have found it, and from every other KB that meets the
  same quirk.
- **Maintenance.** A workaround outlives the quirk it was written for unless something
  records it. core.txt's own comment on `implementationNote` says that a note can go stale
  when the engine changes and a comment cannot, which is why the two are kept apart: the
  notes are the list of workarounds to revisit when the engine moves.

**Why not the other ways.** A silent workaround leaves the next author two bad choices:
copy it without knowing why, or restate the right form and break whatever the workaround
was protecting. An unreported bug that corrupts answers corrupts them for every KB, and the
workaround protects only the one KB that has it.

**Audit.** Each workaround in a change carries an `implementationNote` on the term it
affects, naming the limit. `(v/ask kb '(implementationNote ?term ?text) 'CxUniverse)`
lists the notes. A test made to pass by weakening the ontology is a finding for review.

## Order independence

**Practice.** Write sentences so that their meaning does not depend on the order they are
written or loaded in, or on which file loads first. `load-text!` asserts every form of a KB file
through `assert`, which stores a clashing sentence and lets the settle place the nogood.
`try-assert` is the one write entry point that refuses a clash with believed content, and
it belongs to a caller that wants the refusal, not to a KB file.

**Example.** CxBiology states a claim about birds and the more specific claim about
penguins, and the result is the same in either order:

```clojure
(abilityType bird flying)
(not (abilityType penguin flying))
```

A cover asserted before any facts about its parts settles to the state it reaches when
asserted after them, because the cover installs its part edges itself and reads the
memberships already stored:

```clojure
(partition tangible made natural)
```

**Why.**

- **Logic.** A set of sentences has one meaning, and the order they arrive in is not part
  of it. A common-sense KB learns generalities and specifics in whatever order the world
  supplies them, so an answer that depends on order answers a question nobody asked.
- **Engine.** Belief is a function of the current stored content. Each tie between two
  equally strong beliefs is broken on content (`solve/content-key`), never on the handle,
  because handles are allocated in assertion order. A definitional clash is stored in every
  order and placed as a nogood whose verdict comes from its members' strength classes. A
  declaration such as a `disjoint` or a `partition` reads back over the content stored
  before it, so the separation and the memberships give the same nogoods whichever came
  first.
- **Maintenance.** The upper and middle files are discovered on the classpath, a merge or
  a rebase reorders lines, and an import from another system arrives in that system's
  order. A KB whose meaning survives every order survives all of these.

**Why not the other ways.** Relying on a definition being loaded before its facts, or on
`try-assert` keeping whichever of two clashing values arrived first, makes the KB's
content a record of its load history. The next load in another order holds a different KB.

**Audit.** Load the change's files in a second order and compare the answers to the
change's queries, `contradictions` and `conflicts`. A difference is an order dependence,
and it is reported as an engine finding under **ontology over quirk**.
