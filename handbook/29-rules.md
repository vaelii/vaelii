# 29. Rules

- **Covers:** when knowledge is a rule and when it is a taxonomy edge or a declaration;
  forward and backward direction; antecedents that guard a conclusion's argument types;
  the canonical form a rule is stored in; the supported antecedent every firing needs;
  and where a firing's conclusion is placed.
- **Not here:** a rule's exception → [ch. 30](30-exceptions.md); a definition expanding
  into rules → [ch. 31](31-definitions.md); negation as failure in an antecedent →
  [ch. 32](32-negation.md); a rule concluding a rule → [ch. 34](34-generators.md); why a
  predicate `genl` can widen argument types → [ch. 17](17-predicate-hierarchy.md).
- **Assumes:** [ch. 4](04-economy.md), [ch. 17](17-predicate-hierarchy.md),
  [ch. 19](19-relation-properties.md), [ch. 23](23-contexts.md),
  [ch. 24](24-strength.md).

A rule is a sentex: `(implies (and <antecedent> …) <consequent>)` in a context. It has a
handle, TMS support and retraction like a fact. Its handle is the informant of every
justification it licenses, and a justification is valid only while its rule is
believed, so retracting the rule withdraws everything it alone supported. Every rule is
range-restricted: each consequent variable appears in an antecedent, so a fired
conclusion is ground.

## Rule, edge or declaration

**Practice.** Before writing a rule, ask whether a `genl` edge or a declaration says the
same thing. A subtype relation between types is a `genl` edge. One predicate specializing
another is a predicate `genl` edge. Transitivity, symmetry and inverses are the
declarations `transitive`, `symmetric` and `inverse`. Write a rule only for what no edge
and no declaration states.

**Example.** `life.txt` declares the transitivity of `ancestorOf`, and `CxKinship.txt`
states its base link as a predicate edge:

```clojure
(set/monotonic (transitive ancestorOf))
(genl parentOf ancestorOf)
```

The grandparent link is a join over two facts, which no declaration states, so
`CxKinship.txt` writes it as a rule:

```clojure
(set/forwardRule (implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z)))
```

**Why.**

- Logical: `(transitive ancestorOf)` and the transitivity rule it abbreviates entail the
  same sentences. The declaration states the property of the relation; the rule states
  one consequence of the property per pair.
- Engine: a declared-transitive predicate is metadata only. Nothing about it enters the
  taxonomy's adjacency, so an `ancestorOf` assert is an ordinary fact assert, and
  `TransitivePredicateProver` walks the believed facts at query time. A forward rule
  stating the same transitivity would store one derived sentex per pair the walk already
  answers. The `genl` and `genlCx` closures are cached and kept current through every
  edge change, so a rule reading `(genl ?a ?b)` answers from the closure without a rule
  of its own.
- Maintenance: a declaration retracts in one sentence. `kb-integrity`'s `:rule-macro`
  category reads every stored rule and reports each declaration whose shape the rule
  matches (`transitive`, `symmetric`, `inverse`, a predicate `genl`, `transitiveInArg`,
  the two *Instance* generators), so a rule that repeats a declaration surfaces at review.

**Why not the other ways.** A hand-written transitivity rule, run forward, materializes
the closure as stored sentexes, one per reachable pair; run backward, it re-derives the
chain by search on every query. Either way it states twice what the declaration states,
which **state it once** forbids. A type subsumption written as a rule from one type
literal to another bypasses the `genl` closure, so disjointness, argument-type checks and
the audits never see the edge.

**Audit.** Run `kb-integrity` over the change. Each `:rule-macro` finding becomes the
declaration it names, or the KB banks the decline with `declined_rule_macro` over the
suggested declaration (**bank the decision**). `kb-quality`'s `:subsumption` reading
lists rules another stored rule already covers.

## Forward or backward

**Practice.** Leave a rule bare, which makes it backward-only, unless something needs its
conclusions stored. Wrap it `set/forwardRule` when a negation-as-failure antecedent, an
exception or an aggregate reads its conclusion, or when its extent is bounded and a
stored conclusion is wanted at every read. Use `set/backwardRule` to state the backward
choice explicitly, and `set/inertRule` for a rule that must never fire.

**Example.** `CxChange.txt` writes the rule concluding `clipped` as a `set/forwardRule`:
its extent is bounded by the terminating events times the moment pairs the narrative
orders, and each stored conclusion records why inertia stopped. It writes the inertia rule
concluding `holdsAt` as a `set/backwardRule`, because a fluent holds at every moment
between its start and its end. [Chapter 32](32-negation.md) quotes the inertia rule.

**Why.**

- Engine: forward chaining stores one conclusion per match, which on a large KB is
  intractable unless the extent is bounded, so a bare rule forward-chains only when its
  author asks. `set/forwardRule` adds forward chaining and keeps the backward use: its
  engines are both. An `unknown` antecedent, an `exceptWhen` query and an aggregate body
  run over the prover registry, which expands no rule, so they read a conclusion only
  when it is stored. So inertia's `unknown` joins the antecedents of `clipped` itself:
  a backward `clipped` would be invisible to it, and every fluent would persist for ever.
- Order independence: re-asserting one rule under two spellings dedups to one handle,
  and its engines are the union of the spellings seen, read from content rather than
  arrival order. Removing a direction a rule has acquired takes a retraction and a
  re-assert.
- Maintenance: an inert rule is believed and indexed under all its predicates, so a
  reader finds it by its terms; it states a definition without running it
  (**represent the definition**).

**Why not the other ways.** Making every rule forward stores conclusions nobody reads
and multiplies with the extent. Making every rule backward leaves the NAF, exception and
aggregate readers with nothing to read.

**Audit.** For each forward rule, name its bounded extent or the reader that needs it
stored. For each `unknown`, `exceptWhen` or aggregate body, the rules concluding what it
reads are forward.

## Guarded antecedents

**Practice.** When a rule concludes a predicate whose argument types are narrower than
what its other antecedents guarantee, add an antecedent per argument naming the type that
argument needs. Each argument gets its own guard, because two positions can need two
types.

**Example.** `CxSocial.txt` reads acquaintance from kinship only between persons:

```clojure
(set/defaultRule (set/forwardRule (implies (and (kinOf ?x ?y) (person ?x) (person ?y)) (knows ?x ?y))))
```

**Why.**

- Logical: `kinOf` relates causal individuals, and `knows` relates two persons.
  The guarded rule concludes `knows` exactly where both ends are known persons,
  which is the claim the author means.
- Engine: under the entailing reading, an `arg` declaration derives the type it names
  for the argument a fact puts there. Without the guards, the rule would conclude
  `knows` of two dogs, and `knows`'s `arg` declarations would derive
  `person` for each dog, or hold the conclusion inert where a separation rules `person`
  out. The guards keep the rule from firing on a pair the conclusion's types do not
  admit.
- Maintenance: this is **different-type genl** in rule form. A predicate edge
  `(genl kinOf knows)` would make every kinship an `knows`
  tuple; `kb-integrity`'s `:genl-arg-widening` reports such an edge.

**Why not the other ways.** A predicate `genl` between the two widens types silently. An
unguarded rule does the same through the conclusion's `arg` declarations.

**Audit.** For each rule, compare each consequent argument's declared type with what the
antecedents establish for that variable; a gap is a missing guard.

## Canonical form

**Practice.** Write a rule in its natural form, in any antecedent order and with any
variable names. Write a disjunctive condition as an `or` in the antecedent and a
conjunctive conclusion as an `and` in the consequent. Keep the order of evaluable
literals and of a recursive literal as written, since the engine keeps it.

**Example.** One rule with a disjunctive antecedent, over `CxKinship`'s vocabulary: a
sibling or a first cousin is close kin.

```clojure composed
(set/forwardRule
  (implies (or (and (parentOf ?p ?x) (parentOf ?p ?y) (different ?x ?y))
               (and (parentOf ?p ?x) (siblingOf ?p ?q) (parentOf ?q ?y)))
           (closeKinOf ?x ?y)))
```

The engine stores two rules, one per alternative, and `assert` returns both handles as a
vector. Each alternative joins several literals, so neither rule restates an edge or a
declaration. An `or` antecedent whose alternatives split into rules that each restate an
edge states the edges in a longer form: `(or (fatherOf ?child ?parent) (motherOf ?child
?parent))` ⇒ `(parentOf ?parent ?child)` splits into one rule per alternative, and each
states what `(genlInverse fatherOf parentOf)` or `(genlInverse motherOf parentOf)` states
([ch. 17](17-predicate-hierarchy.md)). `CxKinship.txt` states the two edges, the form
[Rule, edge or declaration](#rule-edge-or-declaration) asks for.

**Why.**

- Engine: the rule index keys a rule by its antecedent and consequent predicates, and an
  `or` or an `and` names no predicate. A conjunctive consequent therefore splits into one
  rule per conjunct, and a disjunctive antecedent distributes to one rule per
  alternative, to disjunctive normal form; together they store the product. Variables
  are renamed by first occurrence and antecedents sorted structurally, so two rules that
  differ only in variable names or antecedent order dedup to one handle. Evaluable
  literals (`lessThan`, `unknown`, the aggregates and the rest of the deferred set) and
  the recursive literal of a recursive rule keep the author's order, because their
  position decides what is bound when they run.
- Order independence: two authors who write one rule with different variable names or
  antecedent orders store one rule, so the KB's beliefs do not depend on which spelling
  arrived first.
- Maintenance: retracting one handle of an expansion retracts that alternative; retracting
  the written rule means retracting every handle `assert` returned.

**Why not the other ways.** Splitting a rule by hand into its alternatives states the
same knowledge in more sentences, with nothing recording that they are one rule.

**Audit.** For each rule written with `or` or `and`, the change keeps the vector of
handles `assert` returned, or states the alternatives as the rule was written.

## A firing needs one supported antecedent

**Practice.** Give every rule at least one antecedent matched against stored content.
A computed literal (a value kind such as `integer`, a comparison such as `lessThan`, an
arithmetic `evaluate`) tests or computes from what that antecedent binds.

**Example.** `CxKinship.txt` reads two birth years, then compares them:

```clojure
(set/backwardRule
  (implies (and (birthYearOf ?x ?bx) (birthYearOf ?y ?by) (lessThan ?bx ?by))
           (olderThan ?x ?y)))
```

`birthYearOf` is a `birthDate` at the precision of a year: life.txt's rules conclude it
from a `birthDate` stated as a `YearFn`, `MonthFn`, `DayFn` or `InstantFn` term, so a
birth date stated to the day reaches this rule too.

**Why.**

- Engine: a firing's justification names the handles its antecedents were read from, and
  retraction withdraws the conclusion when any of them goes. A computed antecedent may
  answer with empty support: `(lessThan 1 2)` holds by arithmetic and names no handle.
  The join accepts that answer, and `planned-join` drops the firing when the combined
  handles of all its antecedents are empty. A rule in which nothing binds a computed
  literal's input is refused at assert (`:naf-not-closed`), because the literal would
  find nothing backward and throw mid-fixpoint forward.
- Maintenance: each conclusion rests on a stored fact, so retracting that fact withdraws
  it, and `why` shows the fact.

**Why not the other ways.** A rule built from computed literals alone has nothing to fire
on. A sufficient definition whose condition is wholly computed expands to no forward rule
for the same reason, and a prover answers it at query time instead
([ch. 31](31-definitions.md)).

**Audit.** In each rule, name the antecedent that binds each variable a computed literal
reads, before that literal in the written order.

## Placement: a rule names no target context

**Practice.** Write a consequent plainly. A forward firing places its conclusion in the
maximal contexts that see the rule and every fact it matched. To make conclusions
visible in a context the placement does not reach, add a `genlCx` edge, or declare the
predicate `decontextualized_predicate`.

**Example.** The test-world's ownership rule (`test/vaelii/world.clj`) names no context:

```clojure
(set/forwardRule (implies (and (owns ?p ?whole) (tangiblePartOf ?part ?whole))
                          (owns ?p ?part)))
```

Fired over ownership facts stated in a story context below CxWell, the conclusion lands
in that story context, the most general context that sees both the rule and the facts.

**Why.**

- Logical: a conclusion is believed where its reasons are visible. A context that sees
  the conclusion also sees every handle the justification rests on.
- Engine: the `genlCx` edges the placement read join the firing's justification, so
  retracting one withdraws what it licensed. An `exceptWhen` query is evaluated in the
  conclusion's placement context. When no context sees the rule and every matched fact,
  the firing is dropped and a `:no-placement` notice goes into `violations`.
- An `(ist Ctx S)` is refused in every rule position with `:not-well-formed`. As a
  consequent it would place the conclusion in `Ctx` whether or not `Ctx` sees the rule
  or the facts: `Ctx` would believe a sentex resting on handles it cannot read, the
  rule's exception would run in `Ctx` and miss facts stated beside the rule, and a
  backward rule with the same consequent would answer nothing where the forward rule
  stored an answer.

**Why not the other ways.** A rule that targets a context breaks context scoping on the
write side and makes a rule's direction change what the KB believes. A copy of the rule
in each context that wants the conclusion repeats the rule (**DRY**).

**Audit.** For each forward rule, name the contexts its antecedents' facts are stated in,
and check that some context sees the rule's context and each of those contexts. A `:no-placement` entry in
`violations` after a load names a firing with nowhere to land.
