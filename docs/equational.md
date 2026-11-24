# Symbolic (schematic) equational reasoning

- **Covers:** how a schematic `(equals L R)` with variables orients into a terminating
  rewrite rule, so a stored term and a query goal meet at one normal form.
- **Not here:** merging two ground symbol names into one partition →
  [equality.md](equality.md); reifying a function-application term to a constant
  before equality or rewriting ever sees it → [nat.md](nat.md).
- **Assumes:** sentex, context, the equality closure, canonical form →
  [glossary.md](glossary.md).

Equations with **variables over function terms** — `(equals (fatherOf (fatherOf ?x))
(grandfather_of ?x))` — and how they come to rewrite and prove terms. This is the
gap [equality.md](equality.md) leaves open: the closure there is a partition over
**symbols**, so it merges names but says nothing about a term-level *definition*.

Two things are built on top of the partition, and both **reduce to machinery that
already exists** rather than adding a new theory engine.

## The two reductions

### Part A — compound equality over reifiable NATs

`(equals (MotherOf Alice) (MotherOf Bob))` — *Alice and Bob share a mother, so they
are siblings* — needs nothing new when `MotherOf` is a `reifiable_function`. Each side
is a **ground reifiable NAT**, so `assert` reifies it to its reified NAT constant *before*
well-formedness runs ([nat.md](nat.md)): the sentence the checks see is an ordinary
`(equals K1 K2)` over two symbols, and the partition + migration merge them. A fact
about one holds of the other, and retracting the equation un-merges them — all the
belief-following of ground equality, for free.

A compound that **does not** reduce is still refused. A measure
`(QuantityFn 5 Kilogram)` is an `unreifiable_function` application: it stays
structural, never reifies to a symbol, so `wff/equality-problems` sees the compound
and rejects it. Measure sameness is `sameQuantity`, a *computed* comparison
([quantity.md](quantity.md)), not the equality closure.

### Part B — schematic equational rules

`(equals L R)` with **variables** is not a merge — it is an oriented **rewrite rule**
over a schema. Stored and queried terms are normalized to a single normal form, so a
stored `(parent_chain (fatherOf (fatherOf Tom)))` and a query `(parent_chain
(grandfather_of Tom))` meet. Everything below is Part B.

A compound `(rewriteOf T E)`, with `E` a ground application and `T` a symbol among its
arguments, is a ground rule `E → T` beside its NAT reify-to-term reading
([nat.md](nat.md)) (`rewrite/equation-rule`). It rewrites an application that stays a
term, such as an `unreifiable_function` application, wherever a stored literal names it;
a meet's absorption is one
([canonicalization.md](canonicalization.md#a-meet-a-stated-inclusion-absorbs)). A `T`
outside `E`'s arguments names the reified NAT, and `nat-read`'s rival check answers for
it, so no rule is cached
(`rewrite_query_test/a-private-rival-rechecks-an-inherited-forward-rewrite-answer`).

`vaelii.impl.rewrite` is the pure term algebra — orientation, matching,
normalization — knowing nothing of the store, belief, or the taxonomy. The taxonomy
caches the active oriented rules (belief-following, like the partition),
`kb/rewrite-term` threads normalization into the same path ground congruence uses, and
`vaelii.impl.special` justifies each rewritten twin.

## Orientation and termination

A schematic equation is oriented into a rewrite `L → R` by a **reduction order**, so
rewriting strictly decreases every term at each step and therefore **terminates** —
whatever the rule set, with no confluence or completion argument. The order is the
**Knuth-Bendix order** with unit weights (`rewrite/kbo>`):

- Every function symbol and variable weighs 1, so a term's weight is its leaf count
  (`term-size`). The **heavier** side rewrites to the lighter.
- An **equal-weight** pair is decided by a fixed **symbol precedence** — the root
  symbols compared, then the arguments lexicographically. So `(f (g ?x)) = (g (f
  ?x))` orients (toward whichever root the precedence ranks lower), where a size-only
  rule would refuse it.
- Both are conditional on the **variable condition** (`var-dominates?`): every variable
  must occur at least as often in the bigger side as in the smaller. This is what
  keeps the order stable under *every* substitution — without it, a substitution
  duplicating a variable the smaller side has more of could make the rewrite grow.

`kbo>` is a genuine reduction order (stable under substitution and context,
well-founded), so a rule `l → r` with `l ≻ r` terminates. The **precedence is a total
order on symbols by their natural `compare`** — content-derived, never arrival-order —
so orientation is order-independent: the two spellings of one equation, and the
equation and its mirror, orient identically.

A **permutative** equation — `(rel ?x ?y) = (rel ?y ?x)` — is KBO-incomparable in
both directions and is **refused** at assert time (`wff/equality-problems`, before
anything is stored). No term order can orient a permutation; that needs AC-rewriting,
a separate and larger mechanism. An equation whose variable condition fails both ways
(a side carries a variable the other lacks) is refused for the same reason.

## Matching and normalization

- **One-way match** (`rewrite/match`): a rule LHS is a *pattern* whose variables may
  bind; the subject is a term (possibly variable-bearing). Only the pattern's
  variables bind — a variable in the subject is an opaque constant — so a rule never
  captures a query's variables. Because orientation forbids an RHS variable absent
  from the LHS, the match binds every variable the RHS substitutes.
- **`normalize`** rewrites a *term* to a fixpoint: innermost subterms first, then the
  root, repeating until nothing applies. Termination is the reduction order; a large
  guard is a pure safety net that a bug would trip rather than hang.
- **`normalize-sentence`** rewrites a *predication* `(pred arg…)` by normalizing each
  argument and **leaving the functor and shape untouched**. A schematic equation is
  about denoting terms, which live in argument position; a predication is an
  assertion, not a term. `fatherOf` the function symbol and `fatherOf` a predicate are
  the same symbol, so protecting the predication is what stops a rule about the *term*
  `fatherOf(fatherOf(x))` from rewriting a *fact* that merely shares the shape.
- **An equality relation's arguments are mentions**, and `normalize-sentence` leaves
  them as written at any depth (`rewrite/equality-relations`, the set ground congruence
  reads for the same purpose). The denial `(not (equals (fatherOf (fatherOf Tom))
  (grandfather_of Tom)))` keeps its spelling; normalizing inside it would give `(not
  (equals (grandfather_of Tom) (grandfather_of Tom)))`, a denial of reflexivity. A
  literal beside an equality literal, in a rule's antecedent for instance, normalizes as
  usual, and `rule-applies?` reads the same positions `normalize-sentence` rewrites.
- **A `natFormula` payload keeps its root.** The payload is the application its constant
  was minted for, so a rule rewrites its arguments and never the payload itself
  (`rewrite/payload-predicates`): `(natFormula K (CxTimeFn CxStory (TimeIntersectionFn
  Noon Y2000)))` restates as `(natFormula K (CxTimeFn CxStory Noon))` under `(rewriteOf
  Noon (TimeIntersectionFn Noon Y2000))`, and `(natFormula K E)` stays under `(rewriteOf
  T E)`.

## The write path — cache, migrate, supersede

When a schematic equation is asserted (`vaelii.impl.special`, the equality table's
integrate arm):

1. **Orient and cache.** `rewrite/orient` produces `[lhs rhs]`; `tax/add-rewrite-rule`
   stores it under the equation's handle in a support map and an active map, and
   `refresh-beliefs` keeps the active map equal to the believed equations, the same
   discipline as the equality partition. Retraction is the only write that takes a
   schematic equation out of belief. Its denial is refused `:not-ground`, a rule
   concluding it is refused `:not-range-restricted`, a monotonic denial of a rewritten
   twin defeats the twin and leaves the equation IN, and a denial of a ground instance
   is held OUT, since `equals` is forced-monotonic: it is never
   believed, and the equation rewrites that instance as it rewrites every other
   ([nmtms.md](nmtms.md#the-forced-monotonic-set)).
2. **Migrate.** Every stored sentex the rule's LHS head reaches (`kb/find-sentexes`,
   one term-index lookup — a superset the per-sentex check narrows) gets a **rewritten
   twin** under the normal form, placed in the original's context, **derived and
   justified** by `[the original, the equation]`. `migrate-sentex` counts each
   applicable rewrite rule (and each symbol equality) as an independent witness, so a
   twin gets one justification per contributor.
3. **Supersede.** The un-normalized original stays stored but is not believed and does
   not match — the same TMS `:superseded` state a merged spelling uses.

Because the twin is a justified derivation, dropping the equation invalidates it: the
dependency-directed sweep collects the twin and un-supersedes the original. So
retraction is a re-derivation, not a flipped bit — the same belief-following ground
congruence has.

## The read path — one normal form everywhere

`kb/rewrite-term` is where symbol congruence and schematic normalization compose: it
replaces every symbol with its class representative (ground congruence — the term
index locates a merged term at any depth) and then normalizes the argument terms
under the active rewrite rules. Each half runs only as far as the KB needs it: a KB with
no merges pays a representative lookup per symbol, and one with no schematic equations
skips normalization (`tax/rewrite-rules` is empty).

Migration and every query path go through `rewrite-term`, so a stored term and a goal
meet at one normal form. **All four query paths normalize the top goal**: `sentexes-matching` and
`ask` (via `kb/rewrite-goal`), and `prove` and `query` (via
`quasiquote/prepare-goal-for-read`, which reifies NATs *and* rewrites the goal). It is the
**top** goal that is normalized — stored facts are already in normal form via
migration, so a subgoal a rule expansion generates needs no further rewriting, the
same reliance `ask` makes. `different` is exempt from goal rewriting: its arguments
must stay un-rewritten to read class membership. An equality relation inside a goal keeps
its arguments as written, so a negated equation goal meets the stored denial as spelled.

## An except of an equation

`(except (sentexHandle E))` of a schematic equation `E` leaves `E` IN in the network, and
the contexts that read the except neither believe `E` nor rewrite under it
([contexts.md](contexts.md)).
`kb/rewrite-term` filters the rules by the reader's `visible?`, so a goal asked there is
not normalized under `E`, and every twin `E` raised rests on `E`, so `exc/hidden-fn`
hides the twins there. What a reader there answers follows from where the fact lives:

- **A fact whose own context reads the except is read as spelled.** A supersession is
  decided at the datum's own context (`special/displacement`), and `E` does not displace a
  spelling in a context that cannot see it, so the original stops being superseded and a
  read of the stated spelling returns it. The normal form's spelling answers nothing there
  unless a premise states it. Which equalities a context sees is recorded by no relabel,
  so an `except` that arrives, leaves or changes label adds to the settle's supersession
  region the superseded data it can change (`special/except-move-region`): those naming a
  term an equality in the excepted handle's reach re-spells — `E`'s LHS head, a ground
  merge's class, or the class of a merge resting on an excepted mark — and stored in a
  context that sees the except. The reconcile stays proportional to what the except
  reaches, not to every superseded datum.
- **A fact stored while the except stands** is stored as spelled, with no twin, since
  its context's normal form does not use `E`. When the except goes, the settle runs
  `E`'s arrival sweep again (`special/except-move-sweeps`: `migrate-matching` over the
  LHS head), so the fact gains its twin and its original is superseded, as in the KB
  that never held the except. The same sweep runs for an except of a ground `sameAs` /
  `equals` / `rewriteOf` (`migrate-class` over its class) and of a `functional`,
  `functionalInArg` or `anti_symmetric` mark ([equality.md](equality.md), "A mark that
  revives runs its arrival sweep again").
- **An except strictly below the fact's context** makes that context a reader of its
  own. The fact's context still sees `E`, so the original stays superseded there, and
  the twin rests on `E`, which the reader below cannot see. Migration takes the contexts
  holding an except of an equality that bears on the fact as readers
  (`special/reader-contexts-at`, the meet with the fact's context) and stores a
  **copy** of the fact's spelling in such a reader, justified by `[original, E, except]`
  under the informant `except` (`special/migrate-into`), as it stores a twin in a reader
  that elects another form. Reads and forward chaining in that reader and below it see
  the copy. `E` is hidden wherever the copy is read, so the read walk reads the copy's
  `E` at its current label (`exc/belief-only-antecedent`); an except of the except
  withdraws the copy through its third antecedent. Retracting the except or `E` takes
  the copy OUT. The copy is stored while the original is superseded or not, and the
  supersession reconcile retires it while an original it restates is not displaced (a
  second except in the fact's own context), examining a copy whenever it examines the
  original (`special/retired-copy`). So the stored copies and what a reader reads do not
  depend on the order the facts and the excepts arrive in. A ground `sameAs` / `equals`
  / `rewriteOf` excepted below the fact's context gives that reader a copy too, since the
  except splits the reader's class. An except of a handle an equality rests on counts as
  an except of the equality, for the readers migration takes and for the copy's
  witnesses. An except of `(equals JanA JanB)` therefore reaches the uses of the
  constants of `(FruitFn JanA)` and `(FruitFn JanB)` through the collision merge that
  rests on it. The sweep an except's move runs migrates every equality in its target's
  consequence closure (`special/except-move-sweeps`,
  `nat_test/a-context-that-excepts-a-merge-reads-each-use-under-the-name-it-was-written-with`).

An except of an equality is never carried onto the twins the equality raised
(`special/handle-twins`): migration never restates an equality, so the equality has no
twin of its own, and a premise stated in the normal form stays readable.

## Order-independence

Two properties keep the normal form a function of the *set* of equations, never their
assertion order — the invariant [nmtms.md](nmtms.md) makes non-negotiable:

- **Orientation** is content-derived (weight, then a total symbol precedence), so the
  same equation always orients the same way.
- **Rule application** tries rules in a **content-sorted** order (`tax/rewrite-rules`
  keys on LHS then RHS, compared structurally by `nm/compare-form` — never printed, since
  an ambient `*print-length*` would elide two long left-hand sides to one prefix and drop
  the choice back onto `:rewrite-active`'s handle-keyed iteration order), so two
  overlapping rules that could rewrite one term pick
  the same winner regardless of which was asserted first — order-independence holds
  even for a non-confluent rule set. The order is derived once per rule *set*, not per
  call: it is memoized in the taxonomy's `:rewrite-order` side atom, keyed by the
  identity of the `:rewrite-active` map, so every writer of that map retires it and no
  writer has to remember to, and a cleared taxonomy's fresh `{}` is a new object where a counter reset to 0 would read as the pre-clear one. Without it every read carrying a context would pay the sort
  — `kb/rewrite-goal` calls `rewrite-term`, which reads this.

## Recover

Supersession is derived from the rules, not stored, so `recover` re-establishes it.
`rebuild-taxonomy` re-orients each stored schematic equation into the rule cache, the
twins' justifications replay from the durable store on their own, and
`recovery/recovered-supersessions` nominates the rule-reached sentexes as supersession
candidates — `supersession-map` re-derives the actual displacement, since
`rewrite-term` normalizes. So the same beliefs stand either side of a restart.

## Confluence — surfaced, not completed

A terminating rewrite system is confluent iff every **critical pair** joins. The
engine does not *complete* a non-confluent set (Knuth-Bendix completion can loop), but
it does **detect and report** the conflicts. When a schematic equation is asserted,
`rewrite/non-joining-pairs` computes the critical pairs between the new rule and the
other active rules — a non-variable subterm of one LHS **unifies** with the other LHS,
giving two ways to rewrite the overlap — and normalizes both reducts. The subterms it
overlaps at are exactly the ones `normalize` reduces at: a term's own root and its
arguments, never a compound in **functor** position, which `normalize` rebuilds
untouched. A conflict reported over a head would be a warning about a reduction the
engine does not perform. A pair that does
not join is recorded in the [violations](api.md) ledger as `:non-confluent` (naming
both rules and both forms) and logged. So two equations that disagree about a shared
term — `f∘f = g` alongside `f∘f = h` — are surfaced to the author.

It is **detection, not resolution**: nothing is dropped. The normal form stays
deterministic (rules applied in content-sorted order), and `match` remains the arbiter
of every rewrite, so a non-confluent set can only make a term written one way miss a
theory-equal term written another — never match wrongly. **Self-overlaps are
excluded**: a lone rule's abstract non-confluence (`f³` reduces two ways) is absorbed
by the deterministic normalization — the same syntactic term always normalizes the
same way — so it never causes a miss and is not flagged; only two *distinct* equations
disagreeing is worth the author's attention.

## What is not built

The **open-goal / search** half — E-unification / paramodulation (proving `(equals ?x
?y)` by searching rewrites on demand), Knuth-Bendix **completion** (turning a
non-confluent set confluent), and AC-rewriting for permutative equations. See
[equality.md](equality.md), "What is not built".

## Where it lives

- `vaelii.impl.rewrite` — pure: `term-size`, `orient` / `kbo>`, `match`, `normalize` /
  `normalize-sentence`, `schematic-equation?`, `equation-rule`, `rule-key`, `rule-applies?`, and
  `non-joining-pairs` (critical-pair confluence detection). Requires only
  `vaelii.impl.sentex`.
- `vaelii.impl.taxonomy` — the belief-following rewrite-rule cache
  (`add-rewrite-rule`, `del-rewrite-rule!`, `rewrite-rules`, refreshed by
  `refresh-beliefs`, cleared by `clear-relations!`).
- `vaelii.impl.resolution` — `rewrite-rules-in`, the rules a reader normalizes under.
- `vaelii.impl.kb` — `rewrite-term` threads normalization into congruence.
- `vaelii.impl.special` — the equality table's schematic arm:
  `integrate-rewrite-rule`, `migrate-matching`, and the schematic contributor
  collection in `migrate-sentex`; `except-move-sweeps`, which the settle runs for an
  `except` that moved.
- `vaelii.impl.wff` — `equality-problems` waves the schematic shape through and
  refuses an unorientable one.
- `vaelii.impl.checks` — `check-ground` exempts a schematic equation from the
  non-ground refusal.
- `vaelii.core` — `prepare-goal-for-read` (the `prove` / `query` normalization),
  `recovered-supersessions` (the recover entry point).
- Tests: `rewrite_test` (the pure algebra), `equational_test` (the integration:
  Part A, Part B, belief-following, termination, order-independence, KBO orientation,
  the four-path parity, an except of the equation, a denial of an instance),
  `recovery_test` (durability),
  `order_independence_test` (an except arriving and leaving around the facts).
