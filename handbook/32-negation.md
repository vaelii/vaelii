# 32. Negation

- **Covers:** the choice between a stated `not` and negation as failure; `unknown`,
  `thereExists` and `forall` in a rule antecedent; the closed, bound form each one needs;
  the `closed_extent_predicate` and `closedExtentForArg` grants; and the denial a
  separation answers with no stored negative.
- **Not here:** recording a declined modelling decision as a `not` →
  [ch. 28](28-vocab-pr.md); a rule-level exception → [ch. 30](30-exceptions.md); the
  negative answer a definition gives → [ch. 31](31-definitions.md); the separations
  themselves → [ch. 13](13-disjointness.md).
- **Assumes:** [ch. 3](03-truth-not-provability.md), [ch. 29](29-rules.md),
  [ch. 30](30-exceptions.md).

The KB is open-world. A sentence nobody stated and nothing derives is unknown, not false
(**truth, not provability**). Three mechanisms let a KB say otherwise, each in a
different place: a stated `(not S)` is a fact, an `(unknown S)` antecedent makes one rule
read absence, and a closed-extent grant makes one predicate's extent complete in one
context.

## A stated `not` or an `unknown`

**Practice.** When `S` is false, state `(not S)` or a rule that concludes it. When a rule
should conclude only while `S` is not derivable, write `(unknown S)` as its antecedent.

**Example.** `CxBiology.txt` concludes a stated negative:

```clojure
(set/forwardRule (implies (and (dead ?x)) (not (alive ?x))))
```

`CxChange.txt` states inertia with negation as failure: a fluent an event initiated at
one instant holds at a later instant unless an event terminated it at a moment the KB
does not place outside the two.

```clojure
(set/backwardRule
  (implies (and (happens ?event ?instant1)
                (initiates ?event ?fluent ?instant1)
                (instantBefore ?instant1 ?instant2)
                (unknown (thereExists (?ender ?instant)
                                      (and (happens ?ender ?instant)
                                           (terminates ?ender ?fluent ?instant)
                                           (unknown (equals ?instant ?instant1))
                                           (unknown (instantBefore ?instant ?instant1))
                                           (unknown (instantNotAfter ?instant ?instant1))
                                           (unknown (equals ?instant ?instant2))
                                           (unknown (instantBefore ?instant2 ?instant))
                                           (unknown (instantNotBefore ?instant ?instant2))))))
           (holdsAt ?fluent ?instant2)))
```

**Why.**

- Logical: `(not (alive X))` is a claim about `X`, and it clashes with a believed
  `(alive X)`. `(unknown (thereExists …))` is a claim about the KB: it holds while no
  terminating event the KB leaves unplaced against the two moments is derivable, and it
  is withdrawn when one arrives.
- Engine: an `(unknown S)` antecedent is the per-literal form of `exceptWhen`. In a
  forward rule it shares the evaluation point, the re-check index and the guard defeat,
  so a conclusion drawn while `S` was absent is withdrawn when `S` becomes derivable, and
  returns when `S` leaves. In a backward rule, as in `CxChange`, the literal is evaluated
  when a query reaches the rule. A firing of a rule with an `unknown` antecedent confers `:default`. Blocking
  produces no nogood, because undercutting contradicts nothing.
- Engine: a Justification has no out-list. Nothing about a negation-as-failure condition
  is stored; the condition is re-evaluated on the triggers an exception uses. `unknown`
  reads belief, so `(unknown S)` holds of a stored `S` that is defeated.

**Why not the other ways.** An `unknown` antecedent where the author knows `S` false
makes the conclusion retract the moment `S` is stated by mistake or by another theory,
and gives a query for `(not S)` no answer. A stated `(not S)` where the author knows only
that nothing says `S` asserts a fact nobody established.

**Audit.** For each `unknown` in the change, state in one sentence what the rule
concludes while the literal is absent, and check that the conclusion is meant to retract
when it arrives.

## Closed and bound

**Practice.** Bind every variable of an `unknown` literal with an earlier antecedent that
generates bindings. To negate an existential, close its variable with `thereExists`
inside the `unknown`. Read `forall` as the nested `unknown` it stands for.

**Example.** A composed rule over `life.txt`'s `parentOf`, with a temporary consequent:

```clojure composed
(set/forwardRule
  (implies (and (person ?x)
                (forall ?y (implies (parentOf ?x ?y) (asleep ?y))))
           (tmp_all_children_asleep ?x)))
```

The `forall` is canonicalized to
`(unknown (thereExists ?y (and (parentOf ?x ?y) (unknown (asleep ?y)))))`, so the
sugared rule and the nested rule written by hand are one rule with one handle.

**Why.**

- Logical: an `unknown` over a literal with an unbound variable asks for every value
  that fails the literal, a search over the complement of the domain. `thereExists` projects its variable out and binds
  nothing outside, so `(unknown (thereExists ?c (parentOf ?c Tom)))` is a closed test
  ("Tom has no known parent"). A `forall` over an empty domain holds: a person with no
  children satisfies the rule's universal.
- Engine: `sentex/check-naf-closed` refuses at assert a rule whose `unknown` literal has
  a free variable nothing binds (`:naf-not-closed`), a `forall` or `thereExists` variable
  that appears elsewhere in the rule (`:quantifier-not-local`), and a quantifier that binds
  a constant. A disjunctive body inside `unknown` is refused; two `unknown` antecedents
  state "neither". `(not (unknown S))` is refused at any depth, because `S` itself states
  it.
- Engine: the condition runs at level 6, the registry without rule backchaining, as an
  exception's condition does ([ch. 30](30-exceptions.md)). A forward-derived fact counts.
  A fact reachable only through a backward rule does not, so the predicates an `unknown`
  reads need stored facts or forward rules.

**Why not the other ways.** A rule that needs "every child is asleep" and states it as a
conjunction over the children it knows of concludes from a partial list. Writing a
negated existential as an `unknown` over an open literal is refused, so the author has
to name the binding anyway.

**Audit.** For each predicate an `unknown`, `thereExists` or `forall` reads, name the
facts or the forward rule that supply it.

## A closed extent

**Practice.** When a predicate's believed extent is complete in a context, so that every
true instance is stored or forward-derived, state `(closed_extent_predicate P)` in that
context. When the extent is complete only for one argument value, state
`(closedExtentForArg P n v)`.

**Example.** `measure.txt` closes the three sign values:

```clojure
(closed_extent_predicate sign_value)
```

The file states `SignNegative`, `SignZero` and `SignPositive` as the members, and the
comment of `sign_value` says that exactly one holds of any quantity.

**Why.**

- Logical: a closed extent is a claim the author makes about the predicate, not about the
  KB's state of knowledge: the members stated are all the members there are.
- Engine: under a visible grant, `ClosedExtentProver` answers a ground `(not (P a))` while
  nothing answers `(P a)` at level 6. Nothing is stored, and a member that is retracted or
  defeated leaves the extent. A negative antecedent `(not (P ?m))` whose variable another
  antecedent binds is read as negation as failure under the grant, decided at derive time
  in the placement context and re-decided when the extent changes.
- Context: the grant is a policy of the context that states it, read from the asking
  context's `genlCx` ancestor set. A sibling context reading the same predicate stays
  open-world.
- Stratification: a closed-extent negative is a negative edge on `P`, so a rule
  concluding `P` from `(not (P …))` under the grant is refused `:not-stratified`, and so is
  a grant that would close such a cycle over rules already stored.

**Why not the other ways.** Stating every non-member as a `not` stores one sentex per
non-member, and the list is never finished. An `unknown` antecedent in each rule that
needs the closure states the policy once per rule, and a rule written later without one
reads the extent as open.

**Audit.** For each grant, confirm that every member is stored or forward-derived in the
granting context. A member derivable only through a backward rule is outside the extent
the grant calls complete.

## A denial from a separation

**Practice.** When non-membership follows from membership in a kind that excludes the
type, state the separation and rely on it. Do not add a closed-extent grant or stated
negatives for it.

**Example.** `CxRealWorld.txt` states `(set/monotonic (disjoint animal vehicle))`. In a
context below CxRealWorld that believes `(vehicle TmpCar)` for a temporary `TmpCar`,
`query` answers
`(not (animal TmpCar))`, and `argue` of `(animal TmpCar)` answers `:false`.

**Why.**

- Logical: a separation states that no thing is in both kinds, so a member of one is a
  non-member of the other. The denial comes from a positive claim about the thing.
- Engine: `DisjointnessNegationProver` answers a ground `(not (T x))` from a believed
  `(S x)` and a separation between `S` and `T`, and stores nothing. The read climbs only
  `:monotonic` `genl` edges on both sides, because a `:default` edge does not
  contrapose: "a `pa` is typically a `pb`" leaves room for an atypical `pa` outside `pb`.

**Why not the other ways.** A stated `(not (animal TmpCar))` repeats per individual what
the separation states once, and stays when `TmpCar`'s membership is retracted.

**Audit.** For each stated negative membership in the change, check whether a separation
and a positive membership already answer it; when they do, drop the stated negative.
