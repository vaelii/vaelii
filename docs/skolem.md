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
(implies (human ?x) (exists ?y (hasMother ?x ?y)))
```

Fired forward on `(human Tom)`, this derives `(hasMother Tom K)` where `K` is a
**deterministic skolem constant** — a fresh witness standing for "the y that exists".

## The surface form

The consequent is wrapped `(exists <var-or-vars> C)`:

- `(exists ?y (Q ?x ?y))` — one existential witness.
- `(exists [?y ?z] (Q ?x ?y ?z))` — two independent witnesses.
- `(exists ?y (and (Q ?x ?y) (R ?y)))` — one witness **shared** across a conjunction.

Range restriction (`rules/range-problems`) permits **only** the marked variable(s);
every other consequent variable must still be antecedent-bound, so an accidental typo
(`(exists ?y (Q ?z ?y))` with `?z` bound by nothing) is still rejected
`:not-range-restricted`. The wrapper is stripped in the `sentex` constructor: the
stored consequent is the inner `C`, and the existential variable survives as an
ordinary unbound consequent variable — which is exactly what firing re-derives it from.

## Determinism — why the constant is a NAT

The forward fixpoint terminates only because re-deriving an identical sentence resolves
to the same handle and merely adds a justification. A witness minted with a fresh
gensym each firing would produce a *new* sentence every round and never converge. So
the witness must be the **same constant per `(rule, antecedent-binding)`**.

The skolem is a NAT:

```
(SkolemFn <rule-digest> <existential-index> <frontier-values…>)
```

reified through the ordinary NAT path (`reify-or-mint-nat`, [nat.md](nat.md)):
`termOfUnit` dedups it, so the first firing mints a `nat/` constant and every re-firing
on the same binding resolves to that one. The arguments are what key determinism:

- **rule-digest** — the hex SHA-1 of the rule's canonical antecedents, consequent
  and context — distinguishes one rule's existentials from another's. It is
  *content*, so the same rule re-asserted after a retraction, or asserted into a KB
  built in another order, keys the same witness, and a fact stated about a witness
  keeps referring to it across that cycle. The chase literature keys skolem terms
  the same way: on the rule and its existential position, never on a store id.
- **existential-index** distinguishes `?y` from `?z` in `(exists [?y ?z] …)`.
- **frontier-values** — the bound values of the consequent variables the antecedents
  supply, less any a post-join literal *outputs* (an aggregate's `?n` is computed from
  the frontier rather than one of its values, so keying on it would mint a fresh
  individual per count) — distinguish `(human Tom)` from `(human Sue)`. The frontier is
  the same for every conjunct of one head, so `(exists ?y (and (Q ?x ?y) (R ?y)))` gives
  `(Q Tom K)` and `(R K)` the **same** `K`.

A single reifiable function `SkolemFn` carries all this in its arguments, so one lazy
`(reifiableFunction SkolemFn)` declaration — asserted when the first existential-head
rule is stored — turns the whole mechanism on, including the NAT orphan-cleanup gate.

The witness *name* is arbitrary, as skolem constants are: the `nat/…` symbol is minted
per KB, so two KBs holding the same knowledge may spell the same witness differently.
The witness's stored *content* — the `termOfUnit` NAT — is a function of the rule's
content and the frontier alone, so it is identical whatever order the KB was built in,
and belief tie-breaking reads neither the symbol nor any handle.

## Belief-following

The witness `(Q a K)` is justified through the JTMS on `[antecedent-facts, rule]` like
any derived fact, so retracting `(human Tom)` drops `(hasMother Tom K)`, which orphans
`K`; the NAT orphan sweep (`remove-orphaned-nats!`) then removes its `termOfUnit`, so no
raw `nat/` symbol dangles.

## Where it lives

- `vaelii.impl.sentex` — `head-exists?` / `head-exists-vars` / `head-exists-body`, and
  the constructor stripping the `exists` wrapper.
- `vaelii.impl.rules` — `range-problems` relaxed to permit the marked variable.
- `vaelii.impl.skolem` — `skolemize-conclusion` (the minter), `ensure-skolem-function`
  and `has-existential-head?`, over a private `frontier-vars`.  Its own namespace because
  it has two
  callers on two layers: the assert path declares the reifiable function when a rule with
  an existential head is stored, and the forward chainer mints at each firing.
- `vaelii.impl.wiring` — `*defer-settle?*`, the guard that keeps a mid-fixpoint mint from
  settling belief, and `assert-sentence`, the assert path the mint stores through.
- `vaelii.impl.chain` — `derive-conclusion` skolemizes the substituted head before
  placement and shares one witness across a conjunctive head.
- `vaelii.impl.resolution` — the occurs-check in `unify`, which safe unification and
  skolemization both need.

## Scope

- **Forward firing only.** Skolemization is a materialization act. Backward proving of
  an existential head is separate work: there the head variable is a *fresh answer
  variable*, not a stored constant — a single-literal existential rule already answers
  a backward goal that way, but it is not the subject here.
- **Out**: `forall` in heads / higher-order; ATMS / hypothetical-world witnesses;
  general equational reasoning over skolem terms.
