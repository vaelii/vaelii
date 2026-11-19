# 33. Existentials

- **Covers:** a rule whose consequent says that some filler exists; the skolem witness a
  forward firing mints for it; keeping the witness from re-firing its own rule; and the
  `predAll` *Exists* declarations, which record the same kind of requirement and derive
  nothing.
- **Not here:** a function that names a unique filler (`MotherFn`) →
  [ch. 22](22-functions.md); the `predAllSpecified` audit for a determinate filler and the
  `predAllInstance` generator → [ch. 21](21-claims-about-kinds.md); a negated existential
  in an antecedent → [ch. 32](32-negation.md).
- **Assumes:** [ch. 21](21-claims-about-kinds.md), [ch. 22](22-functions.md),
  [ch. 29](29-rules.md).

A KB often knows that something exists without knowing which thing it is: every mammal
has a parent, and the KB holds the parents of few. Two forms state that. A head
existential in a forward rule makes the engine mint a witness per member and reason about
it. An *Exists* declaration records the requirement, and an audit reports the members
that lack a filler.

## A head existential

**Practice.** When every member of a type has some filler the KB does not name, and the
application needs to reason about that filler, write the consequent as
`(exists ?y C)` in a forward rule. Wrap the rule in `set/forwardRule`: a bare `implies` is
backward-only, and only a forward firing mints a witness.

**Example.** A composed rule over `organism.txt`'s `mammal` and `life.txt`'s `parentOf`:

```clojure composed
(set/forwardRule (implies (and (mammal ?x)) (exists ?p (parentOf ?p ?x))))
```

Fired on a believed `(mammal TmpRex)`, the rule derives `(parentOf K TmpRex)`, where `K`
is a `nat/` constant standing for the parent that exists.

**Why.**

- Logical: the consequent says "some `?p`", and the witness is a name for that some. The
  witness states no identity: the unique-name assumption is suspended for it, so neither
  `(equals K Y)` nor `(different K Y)` is provable for a determinate `Y` until a
  `rewriteOf` or a merge identifies the two.
- Engine: the witness is the NAT `(SkolemFn <rule-digest> <index> <frontier values>)`,
  reified through the ordinary NAT path. The rule digest is a hash of the rule's canonical
  antecedents, consequent and context, and the frontier values are the antecedent bindings
  of the consequent's other variables. Re-firing on the same binding resolves to the same
  constant, so the forward fixpoint converges, and two KBs holding the same knowledge in
  different orders mint the same witness under the same spelling.
- Engine: range restriction exempts only the variables the `exists` names, so a typo
  that leaves another consequent variable unbound is still refused
  `:not-range-restricted`. A constant in the binder is refused `:not-well-formed`.
- Belief: the witness's facts are justified by the antecedent facts and the rule, as any
  derived fact is. Retracting `(mammal TmpRex)` withdraws `(parentOf K TmpRex)`, and the
  NAT orphan sweep removes `K`'s `natFormula`.
- Conjunction: `(exists ?y (and (Q ?x ?y) (R ?y)))` gives both conjuncts the same
  witness, so the rule states several facts about one filler.

**Why not the other ways.** A named individual per member, asserted by hand, states that
the parent is a determinate thing the author can name, and every member needs its own
sentence. A function applied to the member names one filler per member,
which a type with two parents per member does not have; a function belongs where the
filler is determined. `MotherFn` uses blood-qualified `motherOf`: one visible value can
resolve it, but ambiguous blood values select no mother and merge none ([ch. 22](22-functions.md)). A rule with
an unmarked variable in its consequent is refused at assert.

**Audit.** For each head existential, confirm that the rule is forward and that the
application reads the witness's facts. When nothing reads them, the requirement is an
*Exists* declaration instead (below).

## The witness does not re-fire its rule

**Practice.** Do not state in the consequent a fact about the witness that satisfies the
rule's own antecedent.

**Why.**

- Logical: "every mammal has a mammal parent" is true, and an infinite model satisfies
  it. A finite KB cannot hold that model.
- Engine: a consequent that made `K` a `mammal` would fire the rule on `K`, mint a parent
  for `K`, and repeat. Each round is a new binding, so each mints a new witness, and the
  run stops only at the forward chainer's term-nesting bound (`:max-term-depth`, 8 by
  default), past which a firing places nothing. The run then reports `:term-cut`.
- Maintenance: the cut chain holds up to 8 witnesses no author asked for, and the depth
  at which it stopped depends on the bound, not on the knowledge.

**Why not the other ways.** State the witness's type with an argument declaration: with
`(arg parentOf 1 organism)` visible, the parent's type is read from the declaration at
the position it fills ([ch. 18](18-argument-types.md)), and no rule fires on it. Where the
type the witness needs would re-fire the rule, state the requirement as an *Exists*
declaration, which mints nothing.

**Audit.** For each conjunct of a head existential's consequent, check that no rule in the
same context takes it as an antecedent that leads back to the same rule.

## The *Exists* declarations

**Practice.** When the KB should record that every member has some filler, with no
witness minted, state the matching *Exists* declaration: `predAllExists`,
`predExistsAll`, `predExistsInstance` or `predInstanceExists`. Name a known filler with
the cell's placeholder functor when the author wants the requirement met in the KB
without a determinate term.

**Example.** A composed declaration over `life.txt`'s `childOf`, whose first argument is
the child:

```clojure composed
(predAllExists childOf mammal mammal)
```

It states that for every `x` in `mammal` there is a `y` in `mammal` with
`(childOf x y)`. `(PredAllExistsFn childOf mammal mammal TmpRex)` names the filler the
declaration requires of `TmpRex`.

**Why.**

- Logical: the declaration states the same requirement a head existential states, with
  the universal outscoping the existential.
- Engine: the four *Exists* relations are inferentially inert. A declaration is stored
  and queryable, and the engine derives nothing from it: no generated rule, no witness, no
  membership. `exists-violations` audits one declaration on request and returns the
  members of the universal collection with no believed tuple to a member of the filler
  collection; a tuple to the placeholder for that member counts as a filler, and so does
  a tuple to any member of the filler collection, a skolem witness included. `all-specified-violations` audits every visible *Exists*
  declaration beside the *Specified* ones.
- Engine: the placeholders are `unreifiable_function`s, so a ground application stays a
  structural NAT the reader sees inside the sentence. The engine never asserts one.
- Cost: the audit reads once per member of the universal collection plus once per
  candidate filler, so it runs at a checkpoint and never at the write.

**Why not the other ways.** A head existential for a requirement nothing reasons from
mints one witness per member and stores its facts. A plain rule with a variable functor
in its consequent is filed under the catch-all for concluding rules, so the query planner
sees it as a candidate for a goal on every predicate.

**Audit.** Run `exists-violations` for each new *Exists* declaration over the change's
test-world, and account for each member it returns.

## Existence or a determinate filler

**Practice.** Choose by what the requirement asks. When it asks that some filler exist,
use a head existential or an *Exists* declaration. When it asks that the KB name the
filler, use `predAllSpecified` ([ch. 21](21-claims-about-kinds.md)).

**Why.** The two audits read the same tuples and disagree about one kind of filler. A
skolem witness is a member of `indeterminate_term`, so it satisfies an *Exists* audit and
fails a *Specified* one. A placeholder an author wrote down is determinate and satisfies
both. A further kind joins the indeterminate category with
`(genl NewKind indeterminate_term)`.

**Audit.** For each requirement the change states, name the class it belongs to and the
audit that checks it.
