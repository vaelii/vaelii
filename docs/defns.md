# Definitional collection relations

- **Covers:** `defnNecessary` / `defnSufficient` / `defnIff` — tying a collection's
  membership to a defining condition on the member `?x`, expanded into ordinary forward
  rules at assert so the entailment inherits indexing, TMS support, retraction and
  belief-following, plus the two registry provers that evaluate a condition at query
  time and the negative answer a violated necessary gives.
- **Not here:** the argument-type declarations `arg` / `genlArg` a term is checked and
  entailed against → [argtypes.md](argtypes.md); carrying a stated claim across a
  transitive relation → [inherit.md](inherit.md); the `genl` / `disjoint` collection
  hierarchy itself → [taxonomy.md](taxonomy.md); a rule whose consequent is a rule →
  [generators.md](generators.md).
- **Assumes:** forward rules, `implies`, justification, defeat-class, `genlCx` context
  visibility → [glossary.md](glossary.md), [inference.md](inference.md),
  [contexts.md](contexts.md).

A collection is a unary predicate whose instances are its members: `(bachelor Tom)` says
Tom is a bachelor. `genl` relates collections to one another and `disjoint` separates
them, but neither says what it *takes* to be a member. These three relations do, by
naming a **condition on the member** and pointing it in one of two directions.

```clojure
(defnNecessary  bachelor (unmarried ?x))   ; member => condition
(defnSufficient bachelor (unmarried ?x))   ; condition => member
(defnIff        bachelor (unmarried ?x))   ; both
```

The member is the distinguished variable **`?x`**. The condition is any sentence
mentioning it — a single literal, a conjunction, a negation — and a condition that never
names `?x` is refused, because it says nothing about membership.

## They expand into forward rules

Each `defn*` fact is stored like any other fact, and *what it means* is a forward rule
materialized beside it:

| assertion | expands to |
|---|---|
| `(defnNecessary Coll C)` | `(implies (Coll ?x) C)` |
| `(defnSufficient Coll C)` | `(implies C (Coll ?x))` |
| `(defnIff Coll C)` | both |

So `(defnNecessary bachelor (unmarried ?x))` beside `(bachelor Tom)` derives
`(unmarried Tom)`; `(defnSufficient bachelor (unmarried ?x))` beside `(unmarried Tom)`
derives `(bachelor Tom)`; and `defnIff` is exactly the conjunction of the two, no more.

```clojure
(defnNecessary bachelor (unmarried ?x))
(bachelor Tom)
(v/ask? kb '(unmarried Tom) 'CxUniverse)               ; => true
(v/sentexes-matching kb '(unmarried Tom) 'CxUniverse)  ; => the derived sentex
```

The expansion is **into the existing machinery**. The companion
rule is an ordinary rule sentex: it is indexed by its antecedent and consequent
predicates, forward-chained from the same agenda, and placed in the maximal context that
sees both it and the facts it fired on. A conjunctive necessary condition
`(and (male ?x) (unmarried ?x))` polycanonicalizes into one rule per conjunct like any
conjunctive consequent, and a sufficient conjunction becomes a conjunctive rule body that
needs every conjunct met. A **disjunctive** sufficient condition becomes a rule body that
disjoins, polycanonicalized into one companion rule per alternative — which is how "a pet
is a dog or a cat" is written ([canonicalization.md](canonicalization.md)). What the forward rule cannot
reach — a condition the KB never stores for it to fire on — is answered where the
question is asked instead, below.

## The rule is derived, so retraction and belief follow it

The companion rule is **justified by the `defn*` fact alone** — the mint a generator
makes for a stamped rule (`chain/mint-rule`), minus the join bindings. It is not a
premise: nobody asserted it, and it stands only while the `defn*` fact it rests on is
believed.

```clojure
(def dh (v/assert kb '(defnNecessary bachelor (unmarried ?x)) 'CxUniverse))
(v/assert kb '(bachelor Tom) 'CxUniverse)
(v/ask? kb '(unmarried Tom) 'CxUniverse)   ; => true
(v/retract! kb dh)
(v/ask? kb '(unmarried Tom) 'CxUniverse)   ; => false — the rule went OUT with the fact
```

Everything a derived rule gets for free follows from that one justification:

- **Retraction** of the `defn*` fact withdraws the rule and, with it, every conclusion the
  rule licensed — the JTMS relabel reaches them, nothing has to hunt them down.
- **Belief-following.** Defeat or retract the `defn*` fact and the rule stops firing; assert
  it again and the conclusions return. A `:default` `defn*` makes a `:default` rule
  (`conferred-class` caps the mint at the fact's own class), so a stronger contradicting
  belief can defeat what it concludes.
- **Recovery.** The rule and its justification live in the record store, so `recover`
  rebuilds the entailment from the store exactly as the running KB held it.

## Order independence and context scoping

The definition and its members may arrive in either order. When the `defn*` fact is
asserted, the companion rule is seeded onto the agenda and fires over the facts already
stored; when a member arrives later, it triggers the already-indexed rule. The same
knowledge yields the same beliefs whichever came first.

The rule is stored in the `defn*` fact's own context, so it fires only on facts that
context can see up the `genlCx` ancestor set, and its conclusions land where the reasons meet. A
definition in one context does not reach a member stated in a sibling context it cannot
see.

## Query time: the condition is evaluated, not only matched

The companion rule fires on a condition that is **stored and believed**. A condition
built out of *computed* predicates is neither: `(defnSufficient positive_integer (and
(integer ?x) (greaterThan ?x 0)))` — CxCore's own worked example — rests on checks the
evaluables answer rather than on facts anybody asserted. No conjunct of it is a stored
literal that binds `?x`, so the join has nothing to compute `integer` against, and a
sufficient condition of that shape expands to **no** companion rule (the rule
`check-naf-closed` would refuse, [naf.md](naf.md)). `(positive_integer 7)` therefore does
not arrive by forward chaining. Two provers in the registry answer the question where it
is asked instead.

`matchesPattern` extends the evaluable set from numbers to strings: `(matchesPattern
?string ?pattern)` holds when the whole of a ground `?string` matches the regular
expression `?pattern`, and it answers false for a non-string subject. A string subtype is
therefore defined by the shape check alone — `(defnSufficient dotted_quad (matchesPattern
?x "\d+\.\d+\.\d+\.\d+"))`, the pattern a Clojure string so each backslash is written
twice — with no separate `(string ?x)` conjunct, since `matchesPattern` already answers
false for a non-string. The
match runs through a step-limited view, so a catastrophically-backtracking pattern is a
`:pattern-too-costly` refusal rather than an unbounded match, and a pattern that does not
compile is refused at the assert entry point.

**`DefnSufficientProver`** takes a ground unary goal `(Coll a)`, substitutes `a` for the
member variable in the sufficient conditions `Coll`'s spec ancestor set carries, and asks the
registry whether the condition holds — which *evaluates* the computed conjuncts. It runs
at **level 6** ([levels.md](levels.md)), the registry with no rule expansion, so its
reach matches the forward rule's rather than exceeding it; at `completeness` 50 it
**augments** `FactProver` and the companion rule rather than replacing them, and a
condition that is believed is answered by both paths and deduped by the union.

- **It descends the spec ancestor set.** `(Coll a)` is proved by `Coll`'s own sufficient or by a
  **spec**'s, a spec being below `Coll` on the `genl` edges so that its members are
  members. The walk uses the reflexive `tax/specs`, which folds the own-sufficient case
  into the same iteration.
- **A failing necessary of a strict `genl` fast-fails first.** The strict-genl ancestor set is
  walked most-general-first, so the broadest disqualifier is checked first and a rejected
  query never evaluates the possibly-expensive sufficient at all. The ancestor set is a
  set, so a defn reachable by two paths through a diamond is evaluated exactly once.
  `Coll`'s **own** necessary is excluded from that veto: a sufficient is authoritative,
  and a collection whose two halves disagree has the inconsistency documented rather than
  arbitrated.
- **The goal is ground.** An open `(Coll ?x)` would ask a computed condition to
  *enumerate* its members, which a sufficient built from `integer` and `lessThan` cannot
  do, so the prover is inapplicable to one.
- **A self-referential condition is bounded.** Nothing forbids `(defnSufficient Coll
  (Coll ?x))` and level 6 carries no depth guard, so the walk holds a re-entry guard on
  the collections it is already inside, shared with the negative walk below.

## Open-world, and the one negative answer

The reading is **open-world**, and where it stops matters exactly. A `defn*`
relation licenses no closed-world membership completion: condition-*absence* concludes
nothing, and no path treats a failure to prove membership as a disproof of it.

- A thing the condition is merely silent about is **neither** a member nor a non-member.
  Under `(defnIff bachelor (unmarried ?x))`, a `Tom` mentioned nowhere yields neither
  `(bachelor Tom)` nor `(not (bachelor Tom))`, and neither `(unmarried Tom)` nor its
  negation.
- `defnSufficient` never fires on a condition it cannot see met. Failing to derive
  `(unmarried Tom)` is not evidence that Tom is married.
- `defnIff` is the conjunction of the necessary and sufficient rules — the "and nothing
  else is a member" a closed reading would add is not among them.

**A violated necessary is the exception, and it is a boundary rather than a feature.** A
necessary is a disqualifier as well as an obligation, and
`DefnNecessaryNegationProver` is the converse of the positive walk with three things
flipped: member ↔ non-member, sufficient ↔ necessary, and the direction of the `genl`
walk — the positive walk descends to a spec's sufficient, this one ascends to a genl's
necessary. `(not (Coll a))` is proved by the first necessary that positively **fails**
for `a` anywhere in `Coll`'s **reflexive** genl ancestor set, a member satisfying every necessary
at or above it. Reflexive, unlike the positive fast-fail's strict ancestor set, because a
collection's own failing necessary is itself a sound negative witness.

That is not negation as failure. The check is two-valued on the condition: the prover
fires on a condition that is evaluably false, never merely because `(Coll a)` could not
be proved, and a `Coll` with no necessary anywhere in its ancestor set makes the prover
inapplicable — so an absent proof is never mistaken for a disproof. Like the positive
prover it takes a ground goal only, an open `(not (Coll ?x))` being a search over the
domain's complement rather than a test, and at `completeness` 50 it augments a stored
`(not (Coll a))` and `ClosedExtentProver` rather than replacing either.

It is also a **query-time answer alone**: nothing is stored, no rule is materialized and
no JTMS node is created. A KB that states `(Coll a)` against a failing necessary is not
rewritten — it answers both halves, and `argue` reports the two sides
([api.md](api.md)).

A modeller who wants a negative conclusion drawn from the *absence* of a condition writes
it as knowledge: an `(unknown …)` antecedent for negation as failure ([naf.md](naf.md)),
or a `disjoint` declaration and an explicit `not` for a genuine exclusion
([taxonomy.md](taxonomy.md)).

## The vocabulary

`defnNecessary` / `defnSufficient` / `defnIff` are declared in `CxCore` as binary
predicates. The first argument names a collection (a kind, so `genlArg … 1 thing`); the
second is the condition sentence, a term (`arg … 2 thing`). They relate a kind to a
sentence, so they are mixed and marked neither `instance_relation_predicate` nor
`type_relation_predicate`, the way `result` is ([argtypes.md](argtypes.md)).

The condition carries the member variable `?x`, so a `defn*` fact is not ground — and it
is exempted from the ground check the way a schematic equation is
([equational.md](equational.md)): it is stored to retract and belief-follow, and the
variable belongs to the rule the fact expands into, where `check-range-restricted`
governs it.
