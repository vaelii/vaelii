# Head existentials and skolemization

- **Covers:** how a rule's head existential is skolemized to a deterministic NAT
  constant on forward firing, keyed on the rule and its antecedent bindings.
- **Not here:** reifying an ordinary function-application term to a constant →
  [nat.md](nat.md); the range-restriction rule an existential head is the one
  exception to → [inference.md](inference.md).
- **Assumes:** sentex, context, justification, NAT → [glossary.md](glossary.md).

A rule normally must be **range-restricted**: every consequent variable is bound by
some antecedent, so a fired conclusion is ground. A **head existential** relaxes that
for one explicitly marked variable:

```clojure
(implies (person ?x) (exists ?y (hasMother ?x ?y)))
```

Fired forward on `(person Tom)`, this derives `(hasMother Tom K)` where `K` is a
**deterministic skolem constant**, a fresh witness standing for "the y that exists".

## The surface form

The consequent is wrapped `(exists <var-or-vars> C)`:

- `(exists ?y (Q ?x ?y))` — one existential witness.
- `(exists [?y ?z] (Q ?x ?y ?z))` — two independent witnesses.
- `(exists ?y (and (Q ?x ?y) (R ?y)))` — one witness **shared** across a conjunction.

A constant in the binder is refused `:not-well-formed` ([naf.md](naf.md#fully-bound-to-evaluate)).

Range restriction (`rules/range-problems`) exempts **only** the marked variables, so a
typo such as `(exists ?y (Q ?z ?y))`, with `?z` bound by nothing, is still refused
`:not-range-restricted`. The `sentex` constructor strips the wrapper: the stored
consequent is the inner `C`, and the marked variable stays an ordinary unbound
consequent variable, which the chainer finds still unbound after substitution.

## Determinism — why the constant is a NAT

The forward fixpoint terminates only because re-deriving an identical sentence resolves
to the same handle and adds a justification. A witness minted with a fresh gensym each
firing would produce a new sentence every round and never converge, so the witness is
the **same constant per `(rule, antecedent-binding)`**. The skolem is the NAT

```
(SkolemFn <rule-digest> <existential-index> <frontier-values…>)
```

reified through the ordinary NAT path (`reify-or-mint-nat`, [nat.md](nat.md)):
`natFormula` dedups it, so the first firing mints a `nat/` constant and every re-firing
on the same binding resolves to that one. The arguments key the witness:

- **rule-digest**, the hex SHA-1 of the rule's canonical antecedents, consequent and
  context, distinguishes one rule's existentials from another's. It is content, not a
  handle, so the same rule re-asserted after a retraction, or asserted into a KB built
  in another order, keys the same witness, and a fact stated about the witness keeps
  referring to it. The chase literature keys skolem terms the same way: on the rule and
  its existential position, never on a store id.
- **existential-index** distinguishes `?y` from `?z` in `(exists [?y ?z] …)`.
- **frontier-values**, the values of the consequent variables the antecedents bind,
  distinguish `(person Tom)` from `(person Sue)`. A post-join literal's output (an
  aggregate's `?n`) is not in the frontier: it is computed per placement, after the
  mint, and keying on it would mint a new individual per count. The frontier is the
  same for every conjunct of one head, so `(exists ?y (and (Q ?x ?y) (R ?y)))` gives
  `(Q Tom K)` and `(R K)` the **same** `K`.

One reifiable function carries all this in its arguments, so a single
`(reifiable_function SkolemFn)` declaration turns the mechanism on, the NAT
orphan-cleanup gate included. The assert path makes the declaration when it stores the
first rule with an existential head, so a rule that fires during its own assert finds
it. The witness's `nat/` symbol is `constant-for`'s digest of the NAT
([nat.md](nat.md)), so two KBs holding the same knowledge spell the same witness alike.

## Belief-following

The witness `(Q a K)` is justified through the JTMS on `[antecedent-facts, rule]` like
any derived fact, so retracting `(person Tom)` drops `(hasMother Tom K)`, which orphans
`K`; the NAT orphan sweep (`remove-orphaned-nats!`) then removes its `natFormula`, so no
raw `nat/` symbol dangles.

## Where it lives

- `vaelii.impl.sentex`: `head-exists?` / `head-exists-vars` / `head-exists-body`, and
  the constructor stripping the `exists` wrapper.
- `vaelii.impl.rules`: `range-problems`, exempting the marked variables.
- `vaelii.impl.skolem`: `skolemize-conclusion` (the minter), `ensure-skolem-function`
  and `has-existential-head?`. A namespace of its own because two layers call it: the
  assert path declares `SkolemFn` when it stores an existential-head rule, and the
  forward chainer mints at each firing. It is not part of `vaelii.impl.nat`, which
  knows nothing about rules.
- `vaelii.impl.wiring`: the mint is a whole assert, reached through `assert-sentence`
  because the assert path runs the chainer that calls the minter, and it runs under
  `*defer-settle?*` so it does not settle belief mid-fixpoint.
- `vaelii.impl.chain`: `derive-conclusion` skolemizes the substituted head before
  placement, never at a generator's firing ([generators.md](generators.md)).

## Scope

- **Forward firing only.** A backward-proved existential rule mints nothing: it
  answers a goal with a fresh variable in the head variable's place.
- **Out**: `forall` in heads / higher-order; ATMS / hypothetical-world witnesses;
  general equational reasoning over skolem terms.
