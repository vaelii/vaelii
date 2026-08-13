# Changelog

## 0.7.1 — unreleased

- **A rule generator may stamp a generator, at any depth, and a variable an enclosing
  level fills may head a literal.** `(implies (typeVersion ?ipred ?tpred) (implies
  (?tpred ?type ?cap) (implies (?type ?instance) (?ipred ?instance ?cap))))` states a
  type-level/instance-level bridge once instead of once per predicate pair, and what
  reaches the index at the bottom is still an ordinary rule over concrete functors. The
  scoping rule needed nothing added to it: a variable belongs to the outermost level
  whose antecedents mention it. **A top-level rule antecedent is untouched** — nothing
  encloses it, so a variable functor there is refused as it always was, and so is one a
  literal *beside* it binds. Each level owes what a generator owes, at both doors.
  *Class:* **Additive** — a shape that was refused (`:not-well-formed`, "a rule
  generator nests one level") is now accepted.
  [docs/generators.md](docs/generators.md).

## 0.7.0 — 2026-08-12

- **Breaking: a context name is `Cx`-prefixed, not `Context`-suffixed.** `CoreContext`
  is `CxCore`, `UniverseContext` is `CxUniverse`, and the `assert` front door refuses a
  `Context`-suffixed name by the same naming check that already refused a malformed
  predicate or type. *Migration:* respell every context name — in a stored KB, an
  `assert` call, and a saved dump — to the `Cx` form. `docs/naming.md`.

- **Breaking: the context-transitivity predicate is `genlCx`.** `(genlContext sub super)`
  is `(genlCx sub super)`, so the relation between two contexts is spelled the way the
  contexts it relates are. The `genl` closure over types keeps its name. *Migration:*
  respell the predicate wherever an edge is asserted, matched or retracted; a stored
  `genlContext` edge is a fact under a predicate nothing reads, so re-assert it rather
  than expecting the taxonomy to find it. `docs/taxonomy.md`.

## 0.6.0 — 2026-08-12

What a stored rule is worth. A rule can now conclude a rule, a NAF guard written as a
conjunction guards instead of firing unconditionally, and every door that reaches a rule
reads **belief** rather than storage. Beside them, the arrival-order dependences left in
the belief loop itself are closed — a revived datum, an un-merged spelling, and every
report, digest and election that keyed on retrieval order — and two reads that grew with
what the KB *holds* rather than with what the write *touched* now read forward off the
region: `except`'s visibility set and the planner's subtype fan.

**Three entries are Breaking**, which is what makes this a minor rather than a point
release: the daemon answers an export refusal 400 where it answered 500, the model's tool
surface drops two ops, and the CLI's refusals move to stderr. Seven Refusal entries batch
here rather than each forcing its own release, which is what §3.8 of `CONTRIBUTING.md`
designates a minor for. Every Breaking and every Refusal entry carries its *Migration*
line.

**Triage, for a 0.5.1 caller.** This is the index to what touches something you have
written.

| If your code… | Then |
|---|---|
| treats a 5xx from the daemon's `:export` op as a backend fault | the five destination refusals answer **400** now; retry logic keyed on 5xx stops retrying a caller mistake |
| drives `:preview` or `:clear-caches` through the LLM tool surface | they are no longer exposed to a model — call the op on the daemon or the API directly |
| writes `(ist Ctx S)` in an antecedent or an `exceptWhen` | refused `:not-well-formed`; say it with `decontextualizedPredicate` or a `genlCx` edge |
| passes `(ist Ctx S)` to a read | it answers now instead of returning empty, with the named context winning over the argument |
| writes `(unknown (and A B))` as a guard | it guards now; it fired unconditionally before. Under a quantifier the same shape is refused |
| branches on `violations`' `:violation` with a defaultless `case` | `:functional`, `:asymmetric` and `:constraint-exposure-truncated` are new kinds |
| runs `check` over `(not (implies …))` | refused `:not-well-formed` at both doors, where `check` passed it and `assert` threw |
| runs a `:refuse` KB and reads an empty `violations` as a clean bill | cross-context `functional` and `asymmetric` pairs are reported there now |
| passes `--strength` to the CLI's `assert-rule`, or reads CLI refusals off stdout | the flag is honoured now, and refusals print on stderr |
| forks a KB with an opts map naming neither `:space` nor `:dir` | the fork lands on its own space instead of the shared process default |
| asks a `symmetric` predicate about a claim that is inherited rather than stored | the mirror composes with the other provers now, so an `ask` can answer more |
| writes a kind-level `(hasCapability <kind> …)` against the shipped ontology | kind-level claims are `capabilityType`; `hasCapability` is the instance-level reading alone |

**The shipped ontology now satisfies the declarations it ships.** `hasCapability` was
read at two levels by one symbol, and one symbol gets one argument check.

- **A capability claim about a *kind* is `capabilityType`, and about a *member* is
  `hasCapability`.** `(hasCapability bird flying)` said the kind flies and
  `(hasCapability Tweety flying)` said one bird does, off a single predicate whose first
  position was declared `argIsa … animal` — right for the member and wrong for the kind,
  since `bird` lies *under* `animal` rather than in it. So seven facts the starter shipped
  were convicted by a declaration the starter also shipped: `check` reported `:arg-type` on
  each and re-asserting any of them threw, while loading them was silent. They loaded
  because the declaration lives in `CxLife` and the facts in `CxBiology`, an
  ordering the open-world reading accepts and for which `violations` files no retroactive
  `:arg-type` report — so nothing said a word. The kind-level content moves to
  `capabilityType`, a `typeRelationPredicate` taking `argGenl` on both positions and
  carrying the `argPreserving`/`argPreservingInverse` pair that reaches the kinds beneath
  and the capabilities above; `hasCapability` keeps `argIsa … 1 animal` and is the
  instance-level reading alone. No kind-level travelling rule replaces the six conclusions
  that vanish with it: `argPreservingInverse` answers them at retrieval, and nothing at
  that level rests on a record. Guards: `ontology-test` asks each reading its own
  question and checks neither answers the other's, plus **two sweeps for the gate that
  was missing**, since loading is not checking and the ordering that admits a sentence is
  gone by the time anyone reads it. `starter-test`'s
  `every-sentence-the-starter-ships-is-well-formed-once-it-is-all-loaded` puts all 1,150
  sentences of `resources/kb/` to `check` against the fully loaded KB — the *authored*
  side, so it covers the rules, which reach the store as slots and a `sentexHandle`
  reference no `.txt` contains. `ontology-test`'s
  `every-fact-the-starter-ships-satisfies-the-declarations-it-ships` walks the *stored*
  facts, which is what catches the six a rule derived. Either alone misses what the other
  finds.
  *Class:* none. `resources/kb/` is data rather than surface (`CONTRIBUTING.md` §3.8), so
  a content edit rides any release; what it owes is the roster that makes it visible, and
  the sweep above is it.
  [docs/inherit.md](docs/inherit.md), [docs/taxonomy.md](docs/taxonomy.md).
- **The pairing is prose, because the vocabulary cannot state it.**
  `typeToInstancePred` is the link recording that two predicates are the type-level and
  instance-level readings of one relation, and it constrains its second argument to an
  `instanceRelationPredicate`. `hasCapability` cannot carry that mark: it relates one
  animal to a capability *kind*, and a marked predicate must use one argument-check family
  for every position, so the mark would cost `(argGenl hasCapability 2 capability)`.
  `relationKind` classifies a predicate whose two ends sit at one level — `resultIsa` and
  `functionCorrespondingPredicate` are unmarked for the same reason — so the pair is named
  in both comments and the enforced check is kept over the inert link.

**A guard keyed on the operator instead of on what it reads.** Two doors and one index
were answering about negation-as-failure conditions without ever being asked again.

- **An `exceptWhen` whose query is itself a query operator is now watched by what the
  query reads.** The exception is any closed level-6 goal, so `(unknown S)`, a
  `thereExists` and an aggregate all stand there — and the re-check index was keyed on
  the conjunct's own functor, which for those three is a symbol no sentex is ever stored
  under. The rule sat in the index under a predicate nothing arrives on, so no fact could
  queue it: the exception was evaluated correctly the first time and re-evaluated never,
  which is not an exception that fails safe but one that answers whatever happened first
  — `(exceptWhen (unknown S) R)` blocked `R` forever, including after `S` became
  derivable and the guard should have released. The stratification graph read the same
  keys, so a cycle through such an exception reached no rule and was refused nowhere.
  `rules/watched-predicates` peels the frames — an `unknown` to its conjuncts, a
  `thereExists` to its body, an aggregate to its census body — and is read by all four
  sites that key on them (the live registration, its removal half, the index rebuild, and
  the stratification graph), so a rebuilt index cannot disagree with a live one. `not` is
  deliberately not peeled: the trigger side keys an arriving `(not S)` under `not` too,
  so the two agree. Guards: `except_recheck_test`'s release-after-the-fact case, which is
  the direction an initial answer cannot show, and its stratification twin.
  *Class:* neither label — belief moves for a rule of this shape, and no working caller
  exists to break, the guard having answered from arrival order rather than from content.
  [docs/exceptions.md](docs/exceptions.md).
- **And the settle-time narrowing peels the same frames, or fixing the key would have
  bought a quadratic.** The filter that decides *which firings* to re-evaluate
  substitutes the firing's bindings into each block literal and asks whether the trigger
  could answer it; a literal that is not flat and ground has no shape to test and is
  kept, which is the safe direction and, for an exception that *is* a query operator, is
  every firing every time — `(unknown (qskip PX7))` reads as unshaped however specific it
  is. With the rule now correctly queued, that made the re-check cost the rule's whole
  history per arriving fact: **48 → 192** level-6 evaluations for the same 6 triggers as
  the firing count went 8 → 32, against **0** once the frames are peeled, the triggers
  being about individuals no firing binds. Both populations peel — the placed
  justifications and the **refusal record**, which is where this shape accumulates, since
  `(unknown S)` holds exactly while `S` is absent and that is the state a firing is
  refused in. Guard: `except_recheck_test`'s counting test for the query-operator shape,
  beside the flat one it mirrors — a call count rather than a clock, for the reason that
  file gives. *Class:* neither label — a cost, and one no released engine ever paid, the
  key that would have reached these firings having landed in the same change.
  [docs/exceptions.md](docs/exceptions.md).
- **`check` predicts the NAF-literal refusals instead of only `assert` throwing them.**
  Closure, quantifier locality, the aggregate reduction slot, a quantified or empty
  conjunction — all of them live in `sentex/check-naf-closed`, which the *constructor*
  runs, so both storage doors had them and the dry-run door did not: `check` predicts an
  assert without building a sentex. A caller validating a rule before writing it was told
  the rule was admissible and then handed a throw, which is the one answer `check` must
  never give. Moved into `checks/check-rule!`, the list every door reads, so the
  prediction is made where a prediction can see it. Guard: `check_test` holds seven
  shapes to one `:type` at both doors and to no writes. *Class:* **Additive** — `check`
  reports problems where it reported none, which is the promise its docstring already
  made.
  [docs/naf.md](docs/naf.md).

**A rule can conclude a rule.** `(implies <antes> (implies <antes'> <conseq'>))` is a
**generator**: its firing stores the rule it concludes, holes filled.

- **The hole split is computed, not declared.** A variable the generator's own
  antecedents also mention is a hole — bound by the join, ground in the mint; every
  other variable in the stamped rule is that rule's own and survives as a variable.
  Sharing a name *is* how an author says "fill this in", so there is no template
  vocabulary, no holes vector that could disagree with the template it annotates, and no
  synthetic predicate joining two sentences that have to be kept in step. Range
  restriction moves one level in accordingly: the generator's own is vacuous — its
  consequent is a rule, not a conclusion — so what is checked is the **stamped** rule's,
  with the holes counted as bound. A **hole may stand in functor position**, which is
  the point: one generator ranges over a family of predicates while every rule the index
  ever keys on has a concrete functor, so the variable-predicate refusal stands
  untouched and its advice — *assert the instantiated rules, one per predicate* — stops
  being manual labour. A stamped variable functor that is *not* a hole is refused like
  any other. *Class:* **Additive** — a shape that was refused is now accepted.
  [docs/generators.md](docs/generators.md).
- **A mint is derived content, which is the reason to mint rather than macro-expand.**
  The stamped rule is justified by the firing (antecedent handles plus the generator's),
  not marked a premise, so retracting or defeating what licensed it un-believes it
  through the ordinary relabel and it stops firing — no separate un-mint path, and
  `why` on a conclusion reads through a real rule handle to the facts that produced it.
  It is stored through the same check list the assert door runs (`checks/check-rule!`,
  now the one reader both doors share, so a check added at one cannot be missing at the
  other) and polycanonicalized the same way; a mint that cannot stand is dropped and
  recorded rather than thrown, since a fixpoint may not abort halfway through itself.
  Both arrival orders agree with no sweep of the generator's own: a generator is an
  ordinary rule, and a newly asserted or newly minted rule is a datum that joins over
  what is already stored.
- **Rules now follow belief, and that is what makes the above work.** Both chainers
  reached a rule through the rule index, which posts on storage and knows nothing of
  belief, so a rule whose support had gone went on firing forward and answering backward
  goals. `res/rule-believed?` is asked at all four sites (`chain/fire-rules-for`,
  `chain/process-datum`, and both `candidate-rules`). A sentex the TMS holds no node for
  is *available*, not disbelieved — an `:inert` rule is stored outside belief on purpose
  — so the arm reads an absence as an absence. No shipped behaviour moves: until now
  nothing could make a stored rule un-believed. *Class:* **Additive**, for that reason.
- **One level of nesting, and five refusals.** A rule generating a generator is
  `:not-well-formed` — the scoping rule needs one split per sentence, and a second would
  have nothing in the spelling to disambiguate it. An `exceptWhen` on the *stamped* rule
  is refused the same way, and this one is a silence rather than a nesting: an exception
  is a meta-sentex keyed by the rule's handle, split off by the assert path, which a
  firing does not run — so the mint would be a rule whose guard had evaporated, firing on
  exactly the bindings its author wrote it not to. An `(unknown …)` antecedent inside the
  stamped rule, or an `exceptWhen` on the generator, both work and the message names
  them. A `set/backwardRule` generator is
  `:not-indexable`: no backward goal asks for a rule, so it would claim a capability it
  cannot exercise. A generator sharing no variable with the rule it stamps is
  `:not-range-restricted` — every firing would stamp the same rule. And a **generator
  cycle** — a stamped rule concluding a predicate some generator reads — is
  `:not-stratified`, refused outright rather than depth-capped, because a cap makes the
  KB's contents a function of how long the chainer ran; the check runs both directions at
  every generator's assert, or the cycle would be admitted whenever the two were
  asserted in the other order. `check` predicts every one of them.

**A NAF guard written as a conjunction now guards.** `(unknown (and A B))` is the
`exceptWhen` conjunction inlined per literal, and reads the same way: block when every
conjunct is derivable.

- **The form was accepted and inert, in three places at once.** No prover claims the
  functor `and`, so `chain/unknown-inner-holds?` handed the whole `(and A B)` to the
  level-6 registry as one goal, got no answer, and read "not derivable" — which is the
  `unknown` *holding*, so the rule fired unconditionally. The two bookkeeping reads were
  blind the same way and for the same reason: `rules/naf-predicates` posted the rule in
  the re-check index under the predicate `and`, which no fact ever carries, so no arriving
  datum could ever queue it; and `checks/negative-predicates` drew its stratification edge
  from that same functor, so a cycle through such an `unknown` was invisible to the check
  that exists to refuse one. An author who wrote a two-condition guard got a rule with no
  guard at all, and nothing said so. `sentex/naf-query-conjuncts` is the one accessor all
  three now read — the `unknown` spelling of `exception-query-conjuncts` — so the query's
  conjuncts are evaluated by `provers/exception-holds?` (block-if-all, the exception's own
  evaluator, which is what keeps the two from drifting), every conjunct's predicate is
  watched by the re-check index, and every one is a negative edge. `UnknownProver` reads
  the same accessor, so the goal `(unknown (and A B))` and the antecedent agree. Neither
  order nor nesting nor repetition is the rule's identity: the conjuncts are sorted as an
  exception's are, and flattened, because a nested `and` is a goal no prover claims either
  — one left whole would come back unanswerable and read as not derivable, which is the
  same silent hold one layer down. A conjunct may itself be a `thereExists`, its binder
  being local to it, and the predicate watched is the one inside the quantifier. Guards:
  `naf_test`'s eleven new cases, including the arrival on the *second* conjunct's
  predicate, which is what the old index could not see, and the stratification cycle
  closed through that same conjunct, which is what the old negative edge could not see.
  *Class:* neither label — belief moves for a stored rule of this shape, but no
  working caller exists to break: the guard never guarded, so no author's code was doing
  what its author believed.
  [docs/naf.md](docs/naf.md).
- **A conjunction under a quantifier is refused** — `(unknown (thereExists ?c (and …)))`
  and the aggregate body that spells the same shape, both `:type :quantified-conjunction`.
  There the conjuncts share the binder, and the registry answers one goal at a time: read
  flat, each conjunct would be satisfied by a *different* witness, so "has a sick child"
  would hold of anyone with a child while anyone at all was sick. Accepting it stores a
  guard that convicts on evidence about two unrelated individuals, which is worse than the
  inert one it replaces — so `sentex/check-naf-closed` refuses it at the door, naming the
  repair (bind the witness with a generator antecedent). The existential `unknown` is
  therefore one literal deep, which is what it always evaluated as. An **empty**
  conjunction is refused beside it as `:not-well-formed`: nothing can make it derivable,
  so the antecedent guards nothing. *Class:* **Refusal** — no working caller exists, both
  shapes having silently held rather than blocked; the new `:type` keyword is Additive.
  *Migration:* bind the witness with a generator antecedent and leave one literal under the
  `unknown`; a KB that asserted either shape was storing a guard that never blocked.
  [docs/naf.md](docs/naf.md), [docs/aggregate.md](docs/aggregate.md).

**The strictest policy stops being the leakiest.** Under `:refuse` a cross-context
`functional` or `asymmetric` clash was neither refused nor reported; both are now ledger
entries, beside the `:disjoint` one that already was.

- **Two of the three clash kinds slipped through exactly where nothing was meant to.**
  The definitional checks are scoped to the writer's own cone, so a pair split across a
  `genlCx` edge is invisible to both writers and the assert door refuses nothing.
  Under `:arbitrate` that is answered by the vantages — a context that sees the pair
  whole weighs it — but under `:refuse` the vantages are deliberately withheld, and the
  exposure ledger had an entry kind for **disjointness only**. So a `functional` slot
  filled either side of the edge, and an `asymmetric` claim written across one, stood
  believed and unmentioned in the policy chosen precisely to let nothing through.
  `settle/expose-constraint-clashes!` is the reporting half: `:functional` and
  `:asymmetric` entries carrying `:pred`, the two `[sentence context]` halves as
  `:clash`, and the `:visible-from` vantage, shaped like the `:disjoint` entry beside
  them. It reports and never decides — belief is untouched under `:refuse` by
  construction, `contradictions` stays the answer to what was *arbitrated*, and a pair
  this settle arbitrated is excluded exactly as the disjointness pass excludes one.
  Guards: `exposure_test`'s twelve new cases, including the `:arbitrate` counterpart that
  catches the gate applied in the wrong place, and the same-context case that must still
  refuse rather than report. *Class:* **Additive** — a new entry kind in an accumulating
  ledger, and both renderers read `(name (:violation v))` rather than dispatching on a
  closed set. A `:refuse` KB that saw an empty `violations` may now see entries, which is
  the point rather than a migration.
  [docs/nmtms.md](docs/nmtms.md).
- **The discovery is the refusal's, asked from somewhere else.** The pass re-derives each
  clash through `checks/arbitrable-violations` from the vantages `clash-vantages` names —
  the same two reads `clash-askers` makes under `:arbitrate` — so the report cannot drift
  from what the door would refuse, and closing the gap widened no vantage. The pair was
  always visible from there; what was missing was an entry kind to say so.
- **It costs a KB that declares neither property two `seq`s.** The pass is `:refuse`-only
  and gated before any root is read, behind an O(1) check on the declared vocabulary
  (`tax/props :functional` / `:asymmetric`). Its candidates are the moved region's own
  binary facts rather than a declaration's reach, so on a plain assert it works out no
  extent — which also means a `(functional P)` arriving *after* the facts it convicts is
  the arbitrating sweep's question and not this pass's, an absence
  [docs/taxonomy.md](docs/taxonomy.md) states rather than implies.
- **A `genlCx` edge is the one trigger that reaches past the region, and it has to.**
  Visibility itself moves there: a pair whose halves are both stored and both believed
  becomes jointly visible with neither half relabelled, so taking candidates from the
  moved region alone reported the same knowledge when the edges arrived *before* the facts
  and never when they arrived after — the arrival-order dependence the pass exists to
  remove, showing up in the pass itself. An edge in the region reaches out over the cone it
  newly sees (`constraint-facts-in-cone`, the binary-fact parallel of the disjointness
  pass's `members-in-cone`, spending the same `*exposure-instance-budget*`), so both passes
  answer that trigger the same way. Below the cap a cone walk is proportional to the cone,
  deliberately; the checkable property is flatness *past* it, and
  `perf`'s `constraint-exposure-context-edge` reads 0.89x across 8x the facts behind one
  edge at a budget of 100. It failed on its first run at 5.42x, against a claim that was
  what was wrong.
- **And a KB that declares one costs what the region holds, which took a second pass to
  make true.** The vantage search read the argument-1 posting of *both* arguments of a
  candidate, where only one can hold a partner — a `functional` partner shares argument
  1, an `asymmetric` one holds it at argument 2 — and on a term shared across an extent
  the useless posting *is* the extent. Asserting into a declared-asymmetric slot sharing
  argument 1 grew 2.88x from 250 to 2000 facts against a flat 0.91x with the pass off,
  which is 3.9x per assert at the top end. `settle/partner-contexts` now reads the one
  posting each declared property could hold a partner in, and the same load reads 0.89x.
  The narrowing is on the shared path, so the `:arbitrate` vantages stop making the same
  useless read. `perf`'s **`constraint-exposure-shared-arg`** is the gate and is the only
  check in that file whose KB declares a predicate property — every other builds with
  `fresh-kb`, which declares none, so the pass shuts at its vocabulary gate and the suite
  could not see it at all. It failed on its first run.
- **Entries are capped, and never silently.** The candidates are the region but the
  *entries* are not: one slot filled from N contexts a single vantage sees is N−1 pairs
  off one arriving fact, against a ledger that keeps 1000. One pass files at most
  `settle/*exposure-instance-budget*` and files a **`:constraint-exposure-truncated`**
  entry when it had more. A separate kind from the two sweep notices for the reason they
  are separate from each other: a reader acts differently on *these pairs went
  unreported* than on *this trigger went unswept*. The same entry says how many
  `genlCx` edges went unswept, with a sample, a cone walk that stopped being the same
  class of thing to a reader — pairs visible and unreported, nothing left undecided.
- **One entry per pair, keyed on content.** Both halves can sit in one settle's region and
  each convicts the other, so a report keyed on the walked side would file a pair twice —
  or read differently — depending on which arrived last. The entry is keyed on the handle
  pair, the halves are ordered by printed form, and the top-level `:sentence` / `:context`
  name the first of that ordered pair rather than the side that found it. Guard:
  `exposure_test/the-report-is-the-same-in-either-arrival-order`.

**A hidden set kept where the sentexes are, not rebuilt per placement.** `except`'s
visibility read cost as much as the KB hides, every time it was asked — which is once per
placement and once per candidate justification. It reads a roster maintained at the store
now, and is flat in what the KB hides.

- **The read was linear in the number of excepts and is now flat in it.**
  `res/excepted-handles` answers which handles a believed `(except (sentexHandle H))` hides
  from a view context, and it fetched a record, re-derived a target and asked `jtms/in?` for
  every stored `except` in the KB per call. `kb/note-excepted!` maintains
  `{context -> {hidden-handle -> #{except-handle}}}` at `create-sentex` and
  `integrate/sentex-removed!` instead — beside the `:opposed` coincidence set, on the same
  terms and for the same reason, and rebuilt by `recover` because it is derived from storage
  and no store holds it. On a chaining run of 400 facts and 380 derivations
  (`lein bench-hotreads`, best of 3):

  | excepts | µs/derivation | ns/read | share of the run |
  |---|---|---|---|
  | 0 | 237.0 → 243.0 | 216 → 125 | 0.7% → 0.4% |
  | 10 | 184.4 → 165.3 | 3,562 → 594 | 12.0% → 2.5% |
  | 100 | 380.4 → 156.3 | 25,936 → 638 | 56.3% → 2.5% |
  | 1,000 | 2,294.1 → 143.6 | 185,458 → 553 | 88.8% → 3.1% |

  E = 0 is unmoved, which is the second claim: a KB that hides nothing still pays one
  question and gets an empty answer. *Class:* neither label — `res/excepted-handles` keeps
  its arity, its contract and its answer set; what moved is where it reads them from.
  [docs/contexts.md](docs/contexts.md).
- **Belief stays a read, and the roster is storage only.** An `except` can be defeated or
  revived with no sentex arriving or leaving, so there is no choke point a believed-set
  could be maintained at — the roster holds what is *stored*, and whoever reads it filters
  by belief, which is the line `:opposed` draws. It is also why this is a roster rather
  than a clock-stamped memo: the scope that asks is forward chaining, which writes while it
  reads, so a stamped entry would be retired between one placement and the next.
- **The callers with handles in hand stopped materializing a set to look one up.**
  `res/hidden-fn` hands back a predicate over one view context — nil when that vantage hides
  nothing, so a caller skips its filter rather than running one that can only answer false.
  `without-excepted`, `chain/antecedent-hidden?` and `kb/types-of` take it;
  `excepted-handles` remains for the caller that wants every hidden handle. Building the set
  costs one pass over the reader's excepts however few handles will be asked about, and the
  questions are bounded by the answer set while the excepts are not.
- **The gate is the roster being empty, which is tighter than the count it replaces** — a KB
  storing only `(not (except H))` roots under `except` and counts non-zero. Six
  `assert_cost_test` budgets are re-pinned for the index reads that gate no longer makes,
  every one of them downward.
- **A roster that drifts is a wrong belief, not a slow one**, so the guard is an oracle
  rather than a behaviour test: `meta_sentex_test` compares it against a full scan of
  storage after every kind of arrival, defeat, revival and removal, across a `recover`, and
  compares `hidden-fn` against the set read for every handle either could be asked about.
- **The planner's subtype fan is made cheap rather than remembered.** `est-matches` costs a
  unary type literal over the type's whole subtype closure — the one branch that is not a
  handful of O(1) index reads, asked once per pick, per plan, per firing attempt, and
  **13.2%** of a forward chaining run on a 364-type hierarchy. For the shape that costs, the
  argument a bare open variable, the general walk is provably a long way round to
  `count-at [t']`: the literal's token stream is the functor, which extends the trie
  prefix, and then the variable, which stops the walk. `fan-of-roots` reads those counts
  directly and the fan halves, to 6.8%. Any deeper prefix — a compound argument, or a
  partly-bound one — still takes the general walk, because for those the prefix genuinely
  is deeper. *Class:* neither label; the number returned is identical by construction, and
  `plan_test` pins it against the walk itself rather than against a number written down in
  a test. [docs/inference.md](docs/inference.md).
- **Remembering that answer instead does not work, and the harness says so on both paths.**
  A memo stamped on the change clock measures **0.98–0.99×** under chaining, because the
  run's own placements retire the entry between one plan and the next; on a query, where
  nothing moves the clock and every plan after the first would be served, the fan is under
  3% of the run and it measures **0.91–1.04×**. A finer stamp is unsound rather than merely
  fiddly — the estimate bounds from above, a reading of 1 is a proof `rank-blocks` and
  `cartesian-factors` rest on, so an entry computed before a placement is too small.
  `lein bench-hotreads`'s third arm reports both paths, so the next reader inherits the
  measurement rather than the idea.
- **`lein perf` gains the check that would have caught the visibility walk.** The read is
  now flat in what a KB hides, and flatness is a growth claim a ratio *can* see — which the
  old shape was not, being linear in it. `visibility-reading` times a scoped read at 8 and
  1,024 excepts, all of them hiding decoys the read never returns, so n moves the filter's
  input and leaves its output alone. Calibrated from both ends as this file requires:
  **0.91× and 0.90×** on full runs, against **27.33×** measured by running the check against
  a tree that re-derives the hidden set per call. The bound is the flat claim's own 2.0×.
  The literal cache is bound off inside it, because a repeat read under an unmoved clock is
  served whole from that cache and would report the filter free at both sizes — while the
  caller the check exists for, forward chaining, moves the clock per placement and meets
  this read cold every time.

**`ist` places, and four layers had it half-reading.** A rule cannot qualify a premise by
the context to read it from, and now says so at the door instead of storing a rule that
decides itself on a context it never consulted.

- **An `(ist Ctx S)` in antecedent or `exceptWhen` position is refused as
  `:not-well-formed`.** The literal is indexed and matched under the functor `ist`
  (`rules/antecedent-predicates`, `res/match-pattern`), which no sentex carries, so it
  satisfies nothing and no arriving datum triggers it — while four layers around it read
  the frame as meaningful: the naming check descends the context slot and refuses a
  non-context there, range restriction counts the slot's variables as **bound** by an
  antecedent that will never bind them, canonicalization sorts the literal by its inner
  predicate, and well-formedness accepted it in every role. So `check` reported no
  problems and `assert` returned a handle. What accepting it does to the store is the
  argument for the class: a positive antecedent yields a stored rule that cannot fire; an
  `exceptWhen` query never matches, so the guard never guards and the conclusion it was
  written to block **stands believed**; and an `(unknown (ist …))` is satisfied by that
  same emptiness, so the rule fires unconditionally. A rule that does nothing announces
  itself — the other two do not, which is why this is refused rather than left inert. The
  refusal names the two ways to say what such an author meant, since a violation reported
  without its repair is a second lookup: `(decontextualizedPredicate P)` takes every
  `(P ...)` into CxUniverse, which every context sees, and a `genlCx` edge puts
  `Ctx` in the rule's own cone — under either the premise is written plainly, and the
  context topology decides what is readable from where. The NAF frame is now descended by
  the connective walk in its literal's own role, which is what carries the refusal into
  `(unknown …)`; a top-level one is not descended, `unknown` being an
  antecedent/exception construct. Guard: `check_test`'s five frames, holding both doors to
  one `:type` and the store to no writes. *Class:* **Refusal** — no working caller exists,
  the shape having never matched anything. *Migration:* say it with
  `(decontextualizedPredicate P)` or a `genlCx` edge into the rule's own cone — the
  refusal names both.
  [docs/contexts.md](docs/contexts.md).
- **And it reads on a caller's behalf, which is the half that was missing.** `(ist Ctx S)`
  handed to a read returned nothing at all — the most natural thing to type against a
  context, answering as though the context were empty. Every read taking a **sentence and
  a context** now takes one, asking S in Ctx with the named context **winning over the
  argument**, which is the resolution `assert` already makes: one form, one meaning on
  both sides of the KB. That is `sentexes-matching`, `handle-of`, `ask`, `prove`, `query`,
  `query-plan`, `ask-within`, `prove-within`, `why-not`'s sentence arity and the three
  level diagnostics — the rule being the surface, so there is no list to learn.
  `contexts-of` and `find-sentexes` take no context and ask *which* contexts hold a
  sentence, so the form is not a question they have; `isa?` / `genls` take a context but a
  term rather than a sentence. Each door answers at its own notion of a context, and the
  two families differ on purpose: retrieval returns the sentexes **stored** in `Ctx`,
  while the reasoning doors answer from everything `Ctx` **inherits**. Both are "in
  `Ctx`", a fact `Ctx` inherits being true in `Ctx`, so the difference is the doors' and
  not `ist`'s — pinned rather than reconciled. This grants **no** visibility a context
  argument did not already grant, which is what separates it from the antecedent above:
  naming `CxA` is what `(sentexes-matching kb S 'CxA)` has always done, and the
  caller asking has said so, where a rule reading `Ctx` on the sly would decide belief
  from a context its own cannot see. Guards: `context_scoping_test`'s four, including the
  whole-surface one and the sibling lattice where the answer is a context the asker cannot
  see. *Class:* **Additive** — a goal shape that returned empty now answers, and no read's
  behavior on any other input moves.
  [docs/api.md](docs/api.md), [docs/contexts.md](docs/contexts.md).
- **Two read shapes are refused instead of answered empty.** A wrong-arity `(ist Ctx)` or
  `(ist Ctx S junk)` is `assert`'s own `:shape` — the same refusal on the read doors that
  `assert` and `check` already made, so a caller cannot get a silent empty from a form the
  write door rejects. And an `(ist …)` standing as a **conjunct** of a vector goal is
  `:not-well-formed`: a join's conjuncts share their bindings, so there is no per-literal
  context to honor, and it is the antecedent question wearing another frame. What
  accepting them does is the argument for the class — both return an empty result set,
  which is indistinguishable from a true negative, so the caller reads "nothing holds"
  where the engine meant "I did not understand the question". *Class:* **Refusal** — no
  working caller exists, both shapes having answered nothing. *Migration:* nothing; both
  forms returned an empty result set, so no answer a caller held moves.
  [docs/api.md](docs/api.md).

**A datum that comes back believed goes back on the agenda.** Two routes let belief
arrive with nothing chaining behind it, so the same knowledge in one order concluded and
in the other did not — the invariant the README states first, failing in the loop that
exists to hold it.

- **A revived antecedent licenses the firing its defeat withheld.** `chain/*matcher*` is
  belief-filtered, so an OUT datum is not a match and the join yields no candidate;
  reviving it yielded none either, because the firing that never happened left no
  justification for a blocked set to release and reached no placement for the refusal
  record to re-ask. Both existing instruments are blind to it by construction. So the
  trigger is read where the belief moved: `jtms/revived`, with `settle` re-seeding those
  datums onto the chaining agenda. The cost half is **`jtms/touched-new`**, a third window
  set naming the nodes the window created — without it every asserted fact and every
  conclusion drawn from one reads as newly believed, and the re-seed becomes a second
  forward chain per settle. The distinction exists only at creation, so both TMS
  representations take it there. A rebuild stands aside: `recover` relabels the whole graph
  and replays justifications that already carry what was derived. *Class:* neither label —
  belief moves only toward conclusions the same knowledge already reached in another
  order, which is not a contract a caller could hold. Guards: `revived_datum_test` and
  twenty orderings in `order_independence_test`, six of which disagreed.
  [docs/nmtms.md](docs/nmtms.md).
- **The equality door of the same defect, and `jtms/revived` cannot see it.** A merge
  displaces a spelling and its twin joins in its place, so a partner arriving mid-merge
  concludes at the twin; stop believing the equality and the twin is swept while the
  displaced spelling comes back — leaving both antecedents of a forward rule believed and
  neither spelling of their conclusion held. Supersession moves belief with **no relabel
  behind it**, deliberately (a superseded datum stays `:in` so its twin's justification
  survives), so the flip is in none of the three window sets. `refresh-supersessions` is
  where the answer exists — `settle-finish` already brackets it — so the spellings it gives
  back go into `*unmerged-sink*` and `settle` re-seeds and settles again, bounded by
  `max-unmerge-rounds`, the way `retract!` already settles twice around its own
  re-derivation. Two alternative designs lose on what they cost elsewhere and
  [docs/nmtms.md](docs/nmtms.md) says why; the route is not reachable by negating the
  equality, since the merge rewrites the negation's own terms. *Class:* neither label, on
  the entry above's argument. Guards: both un-merge routes — a retracted equality and a
  functional merge losing a filler — plus twenty orderings, six of which disagreed, and a
  cost guard on `rechain-seeds` whose merging arm requires that displacing a spelling puts
  nothing on the agenda. [docs/equality.md](docs/equality.md).

**An answer picked from a fan is keyed on content, never on arrival.** Fourteen reads
elected a survivor, a representative or a display line by retrieval order, which under the
columnar index is assertion order — so the same knowledge answered differently depending
on how it was loaded.

- **Two keys were being elided by an ambient print setting.** `solve/content-key` and
  `skolem/rule-digest` bind the print vars off: a caller's `*print-length*` cut the content
  — and `content-key`'s last-resort handle — out of a key that decides arbitration and out
  of a digest stored durably in `termOfUnit` content, felling both back to arrival order.
  The same binding is now made wherever EDN is written for something other than a human to
  read: the browser's editor seed line, `diff-order`, the proposal panel's hidden line and
  the LLM selection's edit line, since elided EDN is legal EDN naming something else — a
  saved but untouched editor panel would retract the real fact and store the mutilated one.
- **The elections themselves.** `dedup-constant` resolves a colliding expression to the
  survivor `group-collisions` elects; a clash report sorts each side's justifications by the
  key `core/supporting-justifications` reads through; `one-supporter` breaks a same-context
  tie on the printed sentence; a term commented in two contexts glosses from the
  content-least; `rewrite-target` answers nil unless exactly one believed `rewriteOf` names
  the expression, as `correspondence-of` already did; `why-not`'s `:contradicted-by` and
  `excepted-argument`'s completion are content-ordered; `quality`'s rule line adds the
  context to its tie key, one implication in two contexts having shared sentence and
  signature ahead of the display cap; `strongest-per-tuple` and `support-for` break class
  ties on printed form after the context, the matcher being type-aware; `edge/translate`
  sorts nogoods by member content before emission, so two arrival orders render one ASPIF
  text; and `label-context` mints its `ist` copies in content order, as `label-dilemmas`
  does. `core/supporting-justifications` answers in content order at the source —
  informant's sentence, then antecedent sentences — which is what `preview`'s named reason,
  `why`'s `:support` and a clash report's `:justifications` all read through.
- **And the handle cache stopped answering from another KB.** `canon-stamp` carries the
  record store beside the symmetric set and stamps compare with `=`: `with-handle-cache`
  reuses an outer run's map, and two KBs declaring nothing symmetric stamped the one shared
  empty set, so a nested run on a second KB read the first KB's handles.
  `find-sentex-handle` caches only a spelling canonicalization leaves alone, the removal
  choke point clearing the canonical key — a mirrored or folded spelling's entry outlived
  its sentex as a stale handle. `asymmetry-problems` compares the canonical converse, so a
  folded comparison predicate's opposing sentexes are found at all.
  *Class:* neither label for all three bullets — every read answers the same set, in an
  order that is now a function of the content; the previous order was not reproducible for
  the same knowledge, so there was nothing stable to depend on.

**A collected NAT leaves none of its bookkeeping behind.** `nat/bookkeeping-handles`
answered lazily and the caller retracts what it hands back, so the answer was being
computed against a KB the loop had already torn pieces out of: whether a sentex is one of
`k`'s own is read off `k`'s `termOfUnit`, and a tail forced after that map's own retraction
finds no expression. The materialized result types and the correspondence projection behind
it therefore stopped looking like bookkeeping and stayed stored — a raw `nat/` symbol left
naming a constant the sweep had collected, in the retrieval orders that hand back the map
first and not in the others. The set and the sweep's own orphan list are both realized
before the first retraction now. *Class:* neither label; what it removes is bookkeeping for
a constant that no longer exists.

**A stored sentex is not a believed one, and five reads had it the wrong way round.**
Beside the rule index above, four reads took storage for belief and one took belief for
storage.

- ASP grounding takes only **believed** assumption and constraint rules; a superseded rule
  minted choice heads and went on forbidding models. The `{:belief? false}` import stores
  each record with its dump strength and premise mark, so a later `recover` has premises to
  believe rather than a store where nothing grounds. The catalog's belief caveat probes for
  a believed **datum** rather than for any node, which a `recover` over a strengthless store
  builds per handle with all of them OUT. The generator reports `:stored` as storage rather
  than as a sum over the believed context closure.
- The **converse** correction is the reified-NAT sweep: uses count by **storage**, since a
  stored-but-OUT use revives and an inert choice head has no node, so collecting the map
  from under either dangles the constant and re-reifying mints a second one. The teardown
  list stops belief-filtering for the same reason, and [docs/nat.md](docs/nat.md) says
  stored where it said believed. *Class:* neither label — each read now answers the question
  its docstring already claimed.

**Retrieval answers what the reference answers.** Four matching reads disagreed with the
fan-out they are checked against, three of them silently.

- **The mirror probe asks the candidate's own functor.** `matches-hierarchical` mirrored a
  candidate whenever *some* predicate under the queried one was symmetric, so with a
  symmetric sub-predicate anywhere in the hierarchy a stored `(knows Bob Ann)` answered
  `(knows ?x Bob)` — an extra answer the reference fan-out refuses, on the **default**
  retrieval path. *Class:* neither label; the answer withdrawn was one the two paths
  disagreed about, and `docs/inference.md` names the fan-out as the arbiter.
- **`naf-query` unwraps an aggregate as it unwraps `thereExists`**, so a rule with an
  `unknown`-over-aggregate antecedent re-checks on the body's predicate rather than on
  `agg/count`, which no fact carries: the count moving no longer leaves the old conclusion
  believed, and stratification sees the negative edge. The same shape as the `and` guard
  above, arriving through the aggregate frame.
  [docs/naf.md](docs/naf.md), [docs/aggregate.md](docs/aggregate.md).
- **Three spellings stop being three sentences.** The rete alpha matcher skips `exceptWhen`
  meta-sentexes as `res/match-one` does; `aggregate-values` normalizes compound values
  through `representative-term`, so two spellings of one merged measure count once; and the
  three pre-canon reads that gated on the list spelling take the vector spelling as the same
  sentence, which canonicalization has always made it — the NAT leaf test reifies a
  vector-spelled application instead of storing the raw compound beside the constant, the
  editor line's `ist` guard catches a bracketed `ist` rather than letting it file into the
  model's context, and the reified-constant expansion walk descends the antecedent vector a
  rule's record keeps. [docs/canonicalization.md](docs/canonicalization.md).

**A symmetric or inverse reading composes with what is derived.** The mirror answered off
storage alone, so a claim that was *inherited* rather than stored had no mirror at all.

- **The mirror delegates instead of reading storage.** `(pred b a)` goes back through the
  registry minus `SymmetricProver`, so the mirror of a preserved, inherited or computed
  claim is an answer; `*mirror-depth*` bounds the re-entry at two levels and falls back to
  the raw stored read past it. *Class:* neither label — answers are added, none withdrawn.
  [docs/inference.md](docs/inference.md).
- **A partner declared on a sub-predicate is the same edge.** `tax/inverses-under` reads
  the partners of `p` and of everything under it, consulting the spec closure only where
  an inverse exists at all; the self-pair arm says what it answers.
  [docs/taxonomy.md](docs/taxonomy.md).
- **The mirror licenses the forward door too, and the firing names the symmetry it read
  through**, so retracting the `(symmetric …)` withdraws what only the mirror licensed.
  The declaration named is the stored sentence's functor's, the matcher mirroring each
  fanned literal on its own. [docs/inherit.md](docs/inherit.md).
- **A defeat inside arbitration re-joins what its sentence licensed**, over closures
  refreshed to what is believed now. Belief flips with nothing arriving or leaving, so
  nothing queues the re-join an arrival would, and the rest of the settle would otherwise
  walk a closure still holding the defeated edge.
  [docs/inherit.md](docs/inherit.md), [docs/nmtms.md](docs/nmtms.md).

**A negated rule is refused at the door.** `(not (implies …))`, bare or wrapped, built a
`RuleSentex` whose key cannot be computed — so `check` answered admissible and `assert`
then threw a bare `IndexOutOfBoundsException` from inside the store.

- `connective-problems` refuses the form as **`:not-well-formed`** at both doors, a
  `:type` a caller can discriminate on where a JVM exception was neither catchable by kind
  nor predictable by `check`. *Class:* **Refusal** — no working caller exists: the shape
  never reached storage, it reached a stack trace. *Migration:* nothing; assert it as the
  positive rule with the negation in the consequent, which is what could be stored all
  along.
- **And a rule cannot be stored inert.** `assert-inert` is the labeling primitive — a
  recorded truth value, never a claim about the base KB — and a labeling labels atoms, so
  nothing it exists for wants a rule. What one bought was a rule sentex that had never
  been through `index-rule-sentex`, since that runs where a rule is *created*: no chainer
  could reach it, and nothing afterwards could, an `assert` of the same rule resolving to
  the stored sentex and taking the branch that does not index. The state on the other side
  was a rule `in?` called believed and no fact ever fired — the accepted-and-inert shape
  `check-generator` refuses at the other door, with the same **`:not-indexable`**.
  The message names the **other** inertness, which is what a caller landing here usually
  wants: `set/inertRule` is a rule that is believed, indexed and browsable and fires
  neither way — the spelling for a rule kept as documentation, a transitivity the cached
  closure computes instead ([taxonomy.md](docs/taxonomy.md)). This door's inertness is the
  sentex's: not a premise, so never believed at all. One word for two states, so the
  distinction is now stated where each is defined — a **glossary** entry covering both
  (and recording that there is no `:inert` *strength*, the assertable classes being
  `:default` and `:monotonic`), `inference.md` on why indexing an inert rule is the point,
  `taxonomy.md` on writing the transitivity down rather than leaving the KB's most
  important rule unwritten, and `solving.md` on why this door refuses one.
  `res/rule-believed?` justified its absent-node arm by naming `assert-inert` and arguing
  from the `:inert` direction, two different things, and says what it means now. Guards:
  an inert rule is believed, `:default`, and posted under both its antecedent and its
  consequent predicates — the browsability half nothing pinned — and the transitivity
  pattern runs end to end, the closure answering `genl?` / `provable?` / `ask` while the
  rule materializes no edge of its own. *Class:* **Refusal** — every caller
  of this door materializes a labeling's atoms and their negations, which are untouched.
  *Migration:* a rule meant as documentation is `set/inertRule` (or `{:direction :inert}`)
  through `assert` / `assert-rule`; a rule already stored inert is one nothing was firing,
  so `retract!` the handle and assert it.
- Beside it, five legal API calls stop failing under `clojure.spec` instrumentation:
  `genl?`, `representative`, `same-class?`, `equiv-class` and `deprecated?` carry their
  context arity in the spec, and `term-role`'s `:ret` admits `:lexeme` and `:sense`. The
  dead `:arity` declaration row is gone, with `declared-arity`'s unused reader parameter and
  the comment claiming otherwise, and `mint-nat!`'s docstring says which of the three
  asserts chain (`termOfUnit` never does).

**Storage keeps no dead frames, and a torn dump refuses.** A round of durability fixes
across the disk store, the overlay and both import paths — the class the gate's memory
backend cannot see, which is why the matrix exists.

- **`:truncated-dump`** (rostered): a dump stream that ends early reads as a clean EOF, so
  the frames read are counted and compared against what `meta.edn` states, on both the
  belief and records-only paths — the comparison `replay-index!` already makes for index
  entries. The records-only import likewise refuses a dump naming a **handle twice**, a
  BitSet per handle so the streaming path stays streaming; the second frame silently
  destroyed the first record and counted both. *Class:* **Refusal** — no working caller
  exists: one input is a truncated file, the other loses a record it reports as loaded.
  *Migration:* nothing; re-export the dump. Both refusals name what was read against what
  was promised.
- **No frame whose only fate is a tombstone.** `unmark-premise!` re-stores only a record
  that carries a strength, on the disk store and the overlay alike (which also stops
  materializing an override for a derived base record), and the overlay's set insert removes
  a removal record only when one exists, so a durable fork stops paying two WAL frames per
  posting. The memory store marks a premise only for a **stored** record, so `premise-ids`
  agrees with the disk store for the same call sequence.
- **And two reads at open.** `validate-idx-tail!` rides `scan-idx!`'s chunked walk instead
  of paying one seek and one buffer per slot across the whole idx on every open of every
  kind; `rebuild-premises!` tombstones crash damage only (`:damaged-dictionary`,
  `:malformed-record`) and rethrows `:unknown-frame`, because a build that cannot read a log
  must not delete it. The fork projection reads entries with `first` rather than `key` — the
  tiered backend yields plain vectors where the map-backed ones yield `MapEntry`s, so a
  dense overlay half threw `ClassCastException` on any export of the fork — and index
  entries are normalized to vectors at the **export frame**, nippy freezing the two
  differently, so a byte-identical logical index stops dumping byte-differently per backend.
  The dead `:base-highest` field is gone.

**The uberjar loads the ontology it ships.** Layer discovery listed a directory, which a
packaged jar need not carry, so an uberjar started with `CxCore` alone and no upper or
middle layer — silently, the KB simply being smaller than the same tree run from source.

- Discovery lists the jar's own entries, anchored on `kb/CxCore.txt` when the jar
  carries no directory entry, and an unlistable protocol is **refused** rather than answered
  nil. *Class:* neither label — a caller running from source saw every layer already, and
  one running the uberjar was getting a KB nobody meant to ship. Beside it: the load
  generator drops a band past the vocabulary instead of drawing from an empty one
  (predicates 2 under layers 3 put `(nth [] 0)` inside the lazy rule draw, mid-load, after
  the vocabulary had been asserted), and `refuted-pairs` drops retired spellings with
  `res/retired-for?` as the positive read drops them through `without-retired`, a reader
  below a merge otherwise carrying one negative constraint under two names it knows denote
  one thing.

**ASP routes to a solver that can actually run.** `AUTO` handed off past the size cutoff on
`available?` alone, so a machine carrying `libclingo` and no `clasp` binary solved small
programs and threw on large ones — the failure arriving with the workload rather than at
the probe.

- The handoff is gated on a **once-per-JVM probe** that the binary runs, which the facade's
  `available?` now reads rather than forking `clasp --version` per ask. A missing binary is
  `:solver-unavailable`: `shell/sh` execs directly, so the failure is an `IOException` and
  the exit-127 arm could never run. `clingo`'s aspif temp file is deleted on **any** exit,
  `control_new` failures included, instead of leaking to `deleteOnExit`'s never-collected
  hook. `dense-roots`' reserved family 2 throws **`:reserved-family`** (rostered in
  `type_contract_test`) instead of pinning a three-element decode for a key whose real shape
  is four, the packed long having no room for the predicate. *Class:* **Refusal** for the
  two new `:type`s — no working caller exists, both paths having thrown or mis-decoded.
  *Migration:* nothing; install `clasp` if you were relying on the large-program path, which
  was throwing.

**The daemon answers a caller's mistake with 400, and the model's tool surface loses two
ops.** Both are contract changes a working caller observes, and both are why this release
is a minor.

- **`:export`'s destination refusals are client errors.** `:no-destination`,
  `:not-a-directory`, `:not-empty`, `:export-busy` and `:unsupported-format` join
  `serve/client-error-types`, so a directory that exists and is not empty stops counting as
  a backend fault at every reverse proxy and 5xx alarm between the caller and the daemon.
  `:sentence` leaves the set, a type nothing throws. *Class:* **Breaking** — a status code,
  §3.8's own example. *Migration:* a client that retries on 5xx and reports 4xx will now
  report these instead of retrying, which is the intent; `wire_contract_test` pins the
  pairing.
- **`:preview` and `:clear-caches` are excluded from the tool surface a model reaches.**
  `:preview` stores nothing but holds the single writer and advances the handle counter, and
  `:clear-caches` resets process measurement state — neither is a read, whatever its name
  suggests. *Class:* **Breaking** — the exposed tool set is `(keys serve/ops)` minus a
  roster, and this removes two from it. *Migration:* call either op on the daemon or through
  `vaelii.core` directly; nothing about the ops themselves moves.
- **A cancel cannot unsettle a finished job.** `jobs/cancel!` writes `:cancelling` through
  `update-job!` guarded on the job not having settled: stamped over a just-filed `:done`,
  the job never settled, the sweep kept it, the writer kept naming it, and every later
  writing job was refused against work that finished long before.

**The browser writes what it shows, and shows what the ledger holds.** Four rendering and
lifecycle defects, each one a renderer or a guard assuming a shape the data does not have.

- **A violation about no sentence is not a link to a term called nil.** Four ledger kinds
  are about a pair or a budget rather than a dropped sentence, so they carry a `:detail` and
  no `:sentence`; both renderers read those fields unconditionally and `term-link`'s
  fallback links whatever it is handed, so each row printed "nil" beside a live link to
  `/term?q=nil`. The mirror image beside it: `:message` sits at the top level on
  `:non-confluent` and `:aggregate` where every other kind puts it under `:detail`, and both
  renderers read only the `:detail` spelling, so the one line those entries exist to print
  was replaced by the generic fallback. Both read either now, and `core/violations` states
  plainly that `:sentence` and `:context` are not on every entry — the roster this exposed
  as incomplete (`:constraint-exposure-truncated` had reached the changelog and nothing
  else) is stated in all four places. The standing-clash row had the same defect from the
  other end, handing each `[type context]` pair to `term-link` whole.
- **The editor survives a conjunction line, and an export holds the write doors.**
  `edit-post` keeps the positional pairing per entry and lets a conjunction-concluding line
  (a vector of handles, assert-shaped) fall to unpaired, where `v/sentex` refused it
  `:bad-handle` *after* the write had landed and reported failure for a KB that had changed.
  `write-refusal` refuses while an export walks the KB (`catalog/exporting-kb?`, by identity,
  so a load of another KB is untouched) and the export job drains the write monitor before
  the walk; `unload!` waits for a `:cancelling` loader exactly as for a `:running` one, the
  retry the still-stopping refusal asks for having skipped the guard and cleared the stores
  under the live writer; and a repeat source's key suffix is one past the highest still
  loaded rather than a count, so unloading `generated#1` of two no longer collides the next
  load with the live `generated#2`. The caches page and [docs/web.md](docs/web.md) say what
  the clear does — this KB's entries alone, counters left running — instead of promising a
  process-wide zeroing the handler cannot ask for.
- **A fork with an opts map lands on its own space.** Fork opts naming neither `:space` nor
  `:dir` merge over `fresh-overlay-opts`: a non-empty map without one sent the fork's
  writable half to the shared process default, space 0, where two such forks saw each
  other's writes and a plain `open-kb` saw both. Naming a space explicitly is still the
  remount. *Class:* neither label — the shape it replaces had two forks writing over one
  another, which no caller can have been depending on.
  [docs/overlay.md](docs/overlay.md).
- **A KB whose store cannot be counted renders `:unreadable`**, not as a healthy empty one
  (`active-caveat` folded the throw into zero); a broken foreign reader logs `:warn` with the
  cause, and only a genuinely absent plugin stays `:debug`, the old line having sent
  operators to reinstall what was already installed; the torn-snapshot refusal carries
  `:entries`/`:expected` in its ex-data as its dictionary sibling does; and a portfolio racer
  that throws cancels the other racers instead of leaving complete searches running for
  nobody.

**CLI flags mean what they say.** Four parsing defects, one of which stored knowledge at a
strength the caller did not ask for.

- `assert-rule` passes the `--strength` it parsed — accepted-and-dropped stored a known-true
  rule at `:default`, so the record carried a class the caller had not asked for and
  `defeat-class` answered it. What that class governs is narrow, and worth stating so the
  fix is not read as more: it is the *rule's own*, nothing in the engine defeats a rule
  (a negated rule is refused, and a dilemma is a fact-level thing —
  [nmtms.md](docs/nmtms.md)), and what a firing confers is `:defeasible`'s to say.
  **Asserting a rule that is already stored now marks the premise**, which is the same
  door reading the same option and matters more than the class does: a generator's
  stamped rule is a conclusion resting on the generator, so asserting it returned a
  handle for a rule that retracting the generator took away — the assertion bought no
  ground of its own. **The class resolves from content, as the two slots beside it do**
  (`:direction`, `:defeasible` — [canonicalization.md](docs/canonicalization.md)): the
  stronger of the assertions stands, since a re-assert carrying no `:strength` states
  nothing about the class, and reading that silence as a downgrade left `defeat-class`
  answering differently for the same two assertions in the two orders. *Migration:*
  narrowing a rule's class is `retract!` and re-assert, exactly as it already is for
  direction and defeasibility. A value
  flag **refuses a following flag as its value** (`:shape`), instead of opening a directory
  literally named `--starter` and loading no schema. **A flag belongs to the commands that
  read it**, and one carried elsewhere is refused rather than dropped: `match …
  --strength monotonic` bound the option, ran a read that never looks at it, and reported
  nothing — from the outside, indistinguishable from a strength that was applied. The
  three KB flags (`--dir`, `--memory`, `--starter`) go with any command, `repl` carries the
  union since its options are fixed at start and every line reuses them, and `help` names
  the owner of each. Refusals print on **stderr**, so a
  script reading stdout as EDN gets data and the terminal gets the diagnostic; the REPL
  loop keeps stdout on purpose, its errors belonging in the transcript. *Class:*
  **Breaking** for the stream move — a script capturing only stdout stops seeing refusals —
  and for the per-command roster, since a line carrying a flag its command ignored now
  exits 1; **Refusal** for the flag-as-value. *Migration:* redirect with `2>&1` if you were
  reading refusals off stdout; drop the flags your commands were ignoring; re-assert any
  rule whose `--strength` was dropped if you read the slot back.
- `test-backends.sh` gives each run `target/test-backends/run-<pid>` with a `latest`
  symlink, two concurrent matrices having deleted each other's live disk scratch and
  interleaved one log, and its header names the `:fan` four-assertion divergence instead of
  calling every count difference a skip. The shellcheck roster gains `test-parallel.sh` and
  `run-bench-caches.sh`, the two drivers nothing checked.

**Three more costs read the change rather than the KB.** The pattern the `except` roster and
the planner fan above are the largest cases of.

- The overlay's removal record asks the base `kv-member?` instead of materializing the whole
  posting per probe, the rule `merged-member?` already states. `refresh-equality` walks the
  moved handles through a handle-to-edge reverse map — the moved-edges discipline the
  transitive relations hold — instead of re-asking belief of every supporter and re-deriving
  every edge per merge. And the qualitative join baselines live in their own bounded map, so
  the resident cache clearing at its limit no longer degrades every later delta join to a
  full one. *Class:* neither label; each answers what it answered.
- `settle`'s `clash-candidates` sorts the moved region only when something reads the order.
  It sorted twice per settle — `content-order` over `revisit` and over `touched` — before
  reading `checks/arbitrating?`, and the only reader of that order is the budgeted
  declaration sweep below it, which runs under `arbitrating?`. So a `:refuse` KB, the
  default, paid two sorts per settle to feed a pass that was never going to run.
- `core/check`'s docstring says what it predicts and what it does not: it answers `assert`'s
  refusals under the KB's **current** constraint policy, and `arbitrable` is narrower than
  `clashing`. Guard: `constraint_policy_test` runs its cases under both policies.

## 0.5.1 — 2026-08-11

What a write pays, and what an instrument can see. A run of costs that grew with what the
KB *holds* rather than with what the write *touched* — the taxonomy reconcile, the five flat
caches, the reified-NAT orphan sweep, a retraction's teardown, the standing-clash ordering, a
context-cycle repair, a repeated closure ask and a query plan's child count — each now reads
forward off the region a settle moved, and each has a `lein perf` check standing where the
claim is. Four places where **arrival order decided an answer** are closed: a predicate's
second declared inverse, `kb-quality`'s capped lists, the standing clash reports, and a
preview's capped diff. Beside them the process gained instruments for the rest — the change
feed crosses the process boundary as a subscription with a cursor, long work is a job registry
with a screen that watches it, `kb-quality` reads the knowledge where every other instrument
reads the engine, and the conjunctive planner costs a join rather than a column of literals.

**No entry is Breaking**, which is why this is a patch. Three carry a *Migration* line anyway,
because a caller can observe them and should be told what to expect.

**Triage, for a 0.5.0 caller.** This is the index to what touches something you have written.

| If your code… | Then |
|---|---|
| reads the first N of `preview` / `edit-with-consequences!`'s `:believed-added` or `:believed-removed` | you get a different N — the halves are content-ordered now, and were handle-ordered |
| calls `clear-caches` and expects the literal cache's hit rate to zero | pass `{:counters? true}`; the reset is off by default |
| walks a `declared-transitive` predicate that also declares an `inverse` | the walk sees the inverse-recorded hops too, so an `ask` can answer more |
| branches on `violations`' `:violation` with a defaultless `case` | `:arbitration-truncated` is a new kind |
| builds on the shipped Space or Time vocabulary | an argument position that held `thing` now names a type, so an assert 0.5.0 accepted can meet an `:arg-type` refusal — widen the convicting declaration it names, or state the argument at a type the position admits |

**Belief, and what a settle pays.**

- **A preview's capped diff is ordered by content, not by handle.** `preview` and
  `edit-with-consequences!` built `:believed-added` / `:believed-removed` off a region sorted
  numerically — handles, so assertion order — and `:max-results` took a prefix of that, so the
  browser's 50-row panel showed a *different fifty* depending on the order the KB was loaded
  in, with `:bounded?` true either way. Both halves rank on sentence then context
  (`diff-order`), at the point each caller caps. *Migration:* a caller reading the first N of
  either half gets a different N — a different, better-defined N. *Class:* neither label; the
  sequence moved with load order, so there was nothing stable to hold as a contract.
  [docs/preview.md](docs/preview.md).
- **The pass that decides told nobody when it ran out of budget.** A declaration arriving after
  the content it convicts reaches back over that content, bounded by
  `settle/*exposure-instance-budget*`. The reporting half filed `:exposure-truncated`; the
  *arbitrating* half, which spends the same budget before anything is decided, said nothing —
  so a KB could leave standing a pair a finished sweep would have defeated and show a clean
  ledger. It files **`:arbitration-truncated`** (`:triggers` `:sample` `:budget` `:message`),
  one entry per settle. The pairs past a cut go *undecided this settle* rather than decided the
  other way, and discovery accumulates in `:clashes`, so a later settle's region can surface
  them. *Class:* Additive — both renderers read `(name (:violation v))` rather than dispatching
  on a closed set. [docs/taxonomy.md, "Neither cut is silent"](docs/taxonomy.md).
- **Every mutation sorted every standing clash report.** `record-clashes!` ordered `conflicts`
  and `contradictions` by content on the settle path, so an assert into a KB holding N standing
  dilemmas paid O(N log N) to order a reading nobody had asked for. The vectors are stored in
  arrival order and **`settle/ranked`** orders at the read: 1.60 → 1.07 ms per assert at 800
  standing dilemmas, against 1.05 ms before the ordering existed. `perf`'s
  `negation-arbitration` reads 10.02x against its 12x bound, from 12.65x failing. *Class:*
  neither label — both readings answer what they did, in the same order.
- **A belief flip cost what the taxonomy held rather than what moved.** `refresh-relation` read
  the region backward: deciding whether to run walked every supporter, and running recomputed
  every edge's believed-supporter set — 176.6 ms in a 64k-edge relation, and **6.87x across 8x
  the edges the flip is not about**. `:handle-edge`, the transpose of `:support`, lets the scope
  be read forward off the moved handles: 9.2 µs at 64k edges, **0.61x** across the same 8x.
  Gate: `taxonomy-belief-flip`.
  [docs/taxonomy.md, "The belief reconcile is scoped to the moved region"](docs/taxonomy.md).
- **Every settle paid the size of the declared vocabulary to learn it had nothing to
  reconcile.** `:cache-support` holds every `disjoint` pair, predicate property, `inverse` and
  declared `arity` at once, and the five flat caches read it backward: the gate miss — nearly
  every settle — measured 5.0 ms at 32k declarations for finding nothing, and a flip 95 ms.
  Read forward off `:cache-handle-keys` they are 5 µs and 1 µs, flat across 64x the
  declarations. Gate: `flat-cache-belief-flip`.
  [docs/taxonomy.md, "The belief reconcile is scoped to the moved region"](docs/taxonomy.md).
- **What the scoping removed was a rescan four writers were leaning on.** `add-edge` /
  `del-edge` and `support-add` / `support-drop` run with no `believed?` in hand, so they
  recompute contexts from every *recorded* supporter — the believed reading on a single
  supporter, a superset on a **shared** one, which the whole-KB rescan corrected unasked. A
  writer touching a shared edge or entry records it in `:dirty` / `:cache-dirty` and the
  reconcile takes those whether or not belief moved there: a set proportional to the edits,
  never to the KB. Without `:cache-dirty` the flat-cache oracle fails 95 assertions.
- **The index behind the flat caches is a multimap where the closures' is 1:1.** A `genl`
  sentence names one edge, so `:handle-edge` can be `{handle edge}`; the flat-cache writers key
  one entry per sentence but nothing in the structure says so, and a 1:1 index would let the
  first `support-drop` take a handle out from under an entry the same sentex still supports.
- **The two caches that still gate read whichever side is smaller.** The equality partition and
  the rewrite rules hold asserted term-identity claims rather than vocabulary, and the equality
  scan rebuilds relation-wide state, so both gate rather than scope. `moved-touches?` compares
  the two counts and walks the smaller — 0.9 µs at every size, from 4.9 ms to decide a
  32k-entry cache was untouched.
- **A taxonomy edge retired every memo, because a counter says something moved without saying
  what.** At 400 standing dilemmas one `genl` edge with nothing above or below it cost 800
  `checks/arbitrable-violations` calls, and one `genlCx` edge under a context no
  contradiction was stated in re-derived all 400 opposed bodies. Both cost zero:
  `clash-nogoods` weighs the `genl` relation **per pair**, keyed `[type context]`, and
  `negation-nogoods` records the joint-visibility verdict per context pair and re-derives only
  what moved. Gates: `taxonomy-edge-arbitration` and `context-edge-arbitration`.
- **Two more settle-path guards charged the whole KB.** `refresh-supersessions` runs every
  settle and re-examined every displaced spelling each time — one probe per standing merge per
  write, which is what an `owl:sameAs` import emits. Narrowed to `jtms/touched` plus
  migration's own output, one unrelated retraction against 400 standing merges falls from 400
  `rewrite-term*` calls and 9.06x to 0 calls and 1.70x. Beside it, a negated exception conjunct
  registers under the functor `not`, which hides the predicate it is about, so the `genls(super)`
  walk waved it through to `:all` — one level-6 query per firing the rule had ever made, per
  `genl` edge written anywhere. Keyed on `specs(sub)` instead: at 800 firings, 1,600 exception
  evaluations and 10.16x become 0 and 0.91x.
  [docs/equality.md](docs/equality.md), [docs/exceptions.md](docs/exceptions.md).
- **A `disjointMetatype`'s membership is vocabulary, not a roster.** `clash-vocabulary` carried
  the metatype roster and not the metatype *membership*: `(disjointMetatype M)` separates M's
  members by being consulted, so `(M b_t)` leaving stops separating `a_t` from `b_t` while the
  mark still stands, no closure moves, and neither member of the standing pair is in the
  region — so the KB kept reporting a dilemma the oracle does not. Only the **departure** was
  silent, a member arriving reaching its pairs through `metatype-member-reach`.

**Where arrival order was deciding an answer.**

- **A predicate's second declared inverse hid its first, and which one survived was the order
  they arrived in.** `(inverse P Q)` and `(inverse P R)` are both legal and the taxonomy held
  one partner per predicate, so `(transitive beforeEv)` proved `(beforeEv A C)` with `afterEv`
  declared second and **failed** with it declared first; retracting one dropped the predicate's
  whole entry, leaving `P` with no inverse while `(inverse P Q)` was still believed. `:inverse`
  is `{predicate -> #{partners}}` now, maintained in both directions as `:disjoint-index` is.
  **`tax/inverses-of`** is the set the step relation and `solve-inverted` read; **`inverse-of`**
  keeps its shape — one partner or nil — and answers the lexicographically smallest.
  `vaelii.core/inverse-of` is unchanged in arity and return. *Class:* neither label — nothing
  documented which of two declarations won.
  [docs/taxonomy.md, "The step relation"](docs/taxonomy.md).
- **`kb-quality` ranked its capped lists on the handle**, which is assertion order, so two loads
  of the same knowledge reported the same `:never-count` over a different `:never`. The listed
  sets rank on content — consequent predicate, then sorted antecedent predicates, the stored
  sentence breaking a tie within a signature — so the store is read for the listed rules rather
  than for every rule. *Class:* neither label; `kb-quality` is new in this release.
- **A prompt is cut by content, and a sample says it is one.** The LLM prompt builders took
  their lines and *then* sorted them, so a term with more mentions than the cap was shown a
  prefix of arrival order, and the same knowledge loaded twice proposed against two different
  pages. The sort precedes the cut at all four sites, and the heading tells the model it is
  looking at a sample. `:max-scan` (4000) replaces a hidden 4x oversample. `used-with`'s own
  scan cap is the one place arrival order still shows, and closing it means walking the extent.
  *Class:* neither label — `vaelii.impl.llm.*` is impl. [docs/llm.md](docs/llm.md).
- **The scan above the cut was ordered by the index, which is not an order at all.** Those four
  cuts sat on a `take` over the term index's posting **set** — hash-ordered, moving with the
  representation, and differing between the columnar and KV backends over identical knowledge.
  The handles are sorted before the cap, which costs a sort and no extra record reads. Below the
  bound a page is a function of the knowledge alone; *at* the bound it is a sample of the term's
  earliest mentions, ranking by content meaning fetching all of them.
- **A card's cut is a count, including the cut that was not counted.** `used-with` claimed
  everything its scan missed was "still offered under a later tier", which is false for exactly
  the predicates it exists to find — one used with the term but never declared and never
  `argIsa`'d lives in that tier alone. `:dropped` gains **`:unscanned`**, one O(1)
  `count-with-arg` per position, and the card says in words that it did not read N further
  facts. Beside it, `correct.clj` took `first` of a position's `argIsa` declarations, so two
  contexts declaring one position decided by index order whether a reversed-argument
  alternative was offered; it ranks by **specificity** now, narrowest first.
- **A declaration's supporters were being lost or arbitrarily chosen, and the cycle goal could
  throw.** The `disjointMetatype` sweep walked the *believed* memberships where it records
  *supporters*, so a membership defeated at that moment never entered `:cache-handle-keys` and
  clearing the defeat could never revive it — and the live KB disagreed with the recovered one
  over the same store. It reads `stored-declarations` now.
  `derive-functional-equalities` took `first` of a `(functional P)` stated in two contexts, so
  retracting that one withdrew a merge the other still licensed; every supporter contributes a
  justification (`tax/prop-supporters`). And `(P ?x ?x)` ranked answers with a bare `sort`,
  which threw `ClassCastException` out of `ask` on two structural terms; it is `sort-by pr-str`.

**The model backends, the apply path, and what they refuse.**

- **A credential that cannot ride in an HTTP header is refused by name and never by value.**
  The JDK rejects a CR, LF, control or non-ASCII header character with an
  `IllegalArgumentException` **quoting the value verbatim**, and the browser renders an error
  onto the proposal panel — so a `.env` ending in CRLF was one hop from putting an API key on a
  page. The header call is re-raised as `{:type :llm-bad-credential :header "x-api-key"}`,
  carrying no value, and the environment reads are trimmed so the common case never reaches the
  JDK. *Class:* Additive: a `:type` where none was.
- **A streamed body has a deadline, so a host that goes quiet releases the thread.** A request's
  `.timeout` bounds the response *arriving*, and a streamed turn is almost entirely what comes
  after — the path the browser always takes. Both transports read the body under a daemon
  watchdog that closes it at `:timeout-ms`, measured from before the send, and a failure after
  it fires is `{:type :llm-timeout :timeout-ms n}`. *Class:* neither label.
- **A 200 whose body is not JSON carries a `:type` like every other refusal here.** A proxy
  answering HTML, or a chunk truncated mid-object, escaped as the JSON library's own exception —
  the one thing here a caller could not discriminate on. Both transports raise
  `{:type :llm-bad-response :status s :excerpt …}`, bounded at 200 characters and in the data.
  *Class:* Additive. Beside it the `ant` credential probe is killed at five seconds rather than
  waited on, and a backend that probes available and then will not build logs a warning naming
  the backend instead of falling through to the stub in silence.
- **A turn the model ran out of tokens in was being diffed into proposed deletions.**
  `:stop-reason` was read only through `refused?`, so every row the model never reached came
  back as a `:remove` — a transport artifact rendered to a human reviewer as an intended
  retraction. Truncation is decided **before** the diff: `:truncated` is a status on the diffed
  paths (carrying no batch, and ahead of the tool-use arm so a half-written tool call cannot
  run) and `:answer-truncated?` a flag on the additive ones. `propose-page` lifts `:page-found`
  and `:page-truncated?` into the returned map where a `select-keys` cannot drop them.
- **`apply-proposal!` catches, settles, and says what landed.** It calls `edit!`, which is
  documented as **not a transaction**, so a throw at entry N left 1..N−1 stored and **skipped
  the settle** — a KB holding a prefix nothing had reconciled, reported as a bare exception. It
  returns `{:result :applied :failed-at :error}`, with the settle run by hand on the failure
  path.
- **A `StackOverflowError` reading model text read as "the model proposed nothing".** Every read
  of model-written EDN caught `Exception`, and a deeply nested form throws an `Error`. Eleven
  sites catch `Throwable` now, and the depths were measured rather than assumed: the EDN reader
  overflows around 5,000 nestings and **`sentex/canon` at 500**, well inside what the reader
  accepts. One site marked its parse failure with `(.getMessage e)` — **nil** for a
  `StackOverflowError` — so the nil fell through to the map branch and returned an empty batch:
  a crash presented as a model with nothing to say. It names the class now.
- **The `^:llm` consent gate could be satisfied by a helper that does not consent.** The
  meta-test keeping the mark and `VAELII_LLM_LIVE` in agreement accepted *a call to any fn named
  `live-model`*, and one namespace defined one that was a bare provider constructor with no gate
  in it. The scanner follows the call now: it collects, to a fixpoint, the names whose own source
  reaches `live-llm?`, and takes `defspec` as a head too. Six marked tests, all proving consent.

**The taxonomy and its closures.**

- **A `genlCx` edge out of a context that sees another one back never returned.** The depth
  potential ranks the **condensation**, so `A` and `B` are level as one component, and
  `raise-depth` lifted the single node — which put `A` above its own mate, round the cycle
  without end. The lift moves whole components, and the condensation being a DAG terminates it.
  `taxonomy_depth_test` bounds the call on a daemon thread rather than trusting it.
- **Retracting one edge of a context cycle cost the whole context graph.** A deletion can split
  a strongly connected component, so `deactivate` surrendered the depth potential and rebuilt
  every component: **11.19x across 16x a background the retraction is not about**. An edge can
  only break the strong connectivity of a component it belongs to, so an edge merely *incident*
  on a cycle is left alone; the same retraction reads **0.97x**. Gate:
  `retract-context-cycle-scaling`.
- **A repeated closure ask reads the answer instead of walking it again.**
  `TransitivePredicateProver`'s open-argument arms hold the reach per
  `[direction predicate node context]`, stamped with the change clock: **0.10–0.14x on a repeat
  over a 2,000- to 8,000-node chain, and no record read at all**. A **closed** goal reads the
  cache without filling it, computing a closure to store charging a two-hop question for the
  whole extent. The clock is the whole invalidation story and is what makes the cache follow
  belief. **Additive**: no answer moves.
  [docs/taxonomy.md, "What is cached, what is not, and why"](docs/taxonomy.md).
- **`(P ?x ?x)` cost a closure per node to answer nothing.** The one-variable arm asked
  `reaches?` of every source term, and `reaches?` walks that source's whole reach in order to
  *fail* — so an acyclic chain cost O(n²) to answer the empty set it always answers. One
  iterative Tarjan condensation over the step relation now (`on-a-cycle`, O(V+E)). The answers
  are unchanged.
- **A transitive predicate's hops are the believed matches, and the inverse spelling is one of
  them.** `(transitive before)` walked stored `before` facts, so `(inverse before after)` left
  every `after`-recorded hop off the graph — the chain broke mid-walk and answered negative with
  no diagnostic. `succs` / `preds-of` probe the partner literal beside the direct one, as a
  `matches-visible` call rather than a goal handed back to the registry. `(inverse P P)` is a
  legal declaration and now a storable one. *Migration:* an `ask` over a declared-transitive
  predicate returns **at least** what it did and never less, so the only caller affected is one
  that counted on an inverse-recorded hop being invisible — including through `unknown` and
  `exceptWhen`, which read the same list. *Class:* neither label, on §3.8's own precedent.
  [docs/taxonomy.md, "The step relation"](docs/taxonomy.md).
- **The closure walk's per-edge cost is measured, and the record fetch is the minority of it.**
  `lein bench-walk` times an *n*-node walk against a direct sweep over the same records on the
  same mount. What it finds is a threshold rather than a slope, and the threshold is the
  hot-record LRU's capacity: under it a `:disk` fetch is 0.06 µs and *cheaper* than the `:memory`
  one; past it the fetch is a page-in at 3.03 µs and reaches 21% of the hop.
  [docs/taxonomy.md, "What one hop costs"](docs/taxonomy.md), [docs/storage.md](docs/storage.md).

**Reified NATs, and what a retraction sweeps.**

- **A unary fact about a reified NAT was deleted with the constant, silently.** One clause of the
  orphan sweep matched on **arity alone**, so `(prime (PrimeFn Seven))` — a claim somebody
  asserted — made `K` look orphaned once its other uses went, and the sweep retracted the claim
  with the constant. No error, no report. Bookkeeping is decided by **authorship** now:
  `nat/minted-for` re-derives what `mint-nat!` wrote from the same believed declarations, and
  everything else naming `K` is somebody's assertion whatever its arity. The one constant this
  keeps that arity would have collected is one whose `resultIsa` was retracted after the mint,
  and holding it is the direction to err in. *Class:* neither label — the surviving set moves in
  both directions, but a caller whose unary claim was being deleted underneath them was not
  getting what they believed.
- **One retraction cost what the whole KB had ever reified.** The sweep asked "which constant is
  orphaned?" by matching `(termOfUnit ?k ?e)` — every NAT in the KB — after every teardown and
  to a fixpoint: **16.70x across 16x the NATs the retraction is not about**, linear, which on a
  corpus of OpenCyc's order is seconds per retraction. No benchmark saw it, the sweep being
  gated on a declared `reifiableFunction` that no synthetic probe declares. It asks only about
  the constants the teardown's own removals named, one inverted-term-index read apiece:
  **1.22x**, gated by `retract-nat-scaling`.
- **A teardown records only what a sweep will read.** `integrate/removal-sink` retains every
  sentex that leaves the store for the length of a teardown — on a cascade, the whole cascade in
  a vector — and it exists for a sweep that is itself gated on a declared reifiable function.
  The gate decides whether the record is kept, so a KB that reifies nothing pays nothing.
  `edit!` reads the sink before its adds, so a batch declaring the KB's first reifiable function
  finds a nil sink and takes the whole-KB arm.
- **The removals reach that sweep through `integrate/*removed-sink*`**, arriving from three
  places of which only one is the caller's: the dependency-directed sweep, the settle that
  follows, and the orphan sweep's own retractions — the third being what makes the region grow
  with the fixpoint, so a NAT nested in a collected orphan's expression is collected rather than
  left dangling. A use that merely stops being **believed** is not a use that went.

**The change feed, and the daemon under load.**

- **The change feed crosses the process boundary, as a subscription with a cursor.** `watch`
  takes a function and a function does not cross an EDN wire, so the daemon's half is what
  request/response can carry: `:watch` answers a token, `:poll` reads that subscription's ring
  forward from an integer cursor, `:unwatch` drops it, `:watchers` says what is open. All four
  live in `serve/feed-ops` rather than `serve/ops`, which is what keeps a subscription out of
  the model's tool set. `:lagged` is on every reply rather than only the bad ones, and
  `{:wait-ms n}` parks the request outside the write monitor, capped at 30 s.
  [docs/feed.md, "Across the wire"](docs/feed.md).
- **A parked long poll held a thread nothing counted, so the feed could stall the daemon it
  exists to keep live.** 55 concurrent polls drove ring's 50-thread pool to 50/50 busy and
  `/health` from 62 ms to 25,997 ms, one subscription being enough since nothing bounded polls
  per token. `subscribe/max-parked` (16) bounds how many may wait and `serve/http-threads` (50)
  is stated rather than defaulted so the pair is checkable. Over the ceiling a poll *asking to
  wait* is refused (**`:too-many-waiters`**, 400); one that does not ask, or whose events are
  already there, is never refused. *Class:* neither label — the feed is new in this release.
- **Two ways the feed could be taken down or lied to, and the bounds that stop them.**
  `{:wait-ms 1e300}` answered 500: validated as `number?`, which admits a magnitude no long
  holds and admits `##NaN`, which coerced to 0 and made the long poll answer instantly forever.
  It is `nat-int?`, capped before the coercion. And a subscription dropped *while it was being
  registered* took the whole feed down permanently: an unguarded `assoc-in` recreated an entry
  with no `:polled-at`, so `reap` — at the head of every feed op — threw for every later call on
  that daemon. What one caller can allocate is bounded three ways, nothing authenticating
  `POST /op` on the loopback default: 64 subscriptions, 256 events per ring, and one unpolled
  for five minutes reaped at the next call. A ceiling refuses the **new** subscription
  (`:too-many-subscriptions`) rather than evicting somebody else's. *Class:* neither label.
- **The ceilings bound the event count, not the bytes**, and [docs/feed.md](docs/feed.md) says
  so: an event carries one settle's whole relabelled region, and 20 batches of 500 facts left
  one abandoned subscription holding 10,000 preview entries. `:watchers` reports `:delivered`
  and `:pending` — both client docstrings said `cursor`, the one word neither may use, neither
  number being the reader's position. `vaelii.client/watchers`, `vaelii.serve/feed-ops` and
  `vaelii.serve/op-names` join `public_api_test`'s roster, a subset check that had been letting
  them through unnamed. The browser is untouched, and that is a decision: its live regions poll
  an htmx fragment, and a job's percentage is not belief moving.

**Conjunctive query planning.**

- **Planning one fixed conjunction is flat in the size of the KB, and a gate says so.** The cost
  model divides by the trie's distinct-value count at a position and asked for it once per
  literal per plan, and `(count (children …))` answers that by *materializing* the child set —
  25x more against 32x the facts, per rule expansion, per node, per `prove` call.
  `p/count-children` is the same number off a cardinality. **Additive** — a new `IndexStore`
  read, owed by the two implementations of that protocol. `plan-scaling` reads flat with the
  count and 24.6x without; the one exception is the overlay's merge rule.
  [docs/indexing.md](docs/indexing.md), [docs/overlay.md](docs/overlay.md).
- **A conjunction is costed as a join rather than as a column of literals.** `plan/est-rows`
  answers the question `est-matches` does not — not *can* this literal fan out, a sound upper
  bound, but *how much*, an expectation wrong in both directions and composing for exactly that
  reason. It returns the relation's shape (`{:rows 400 :vars #{?x ?y} :distinct {?x 20}}`) and
  the planner threads it through its fold, so the *k*-th pick is costed against the rows
  reaching it. On three or more antecedents a per-literal count's error is multiplicative.
  [docs/inference.md, "Conjunctive query planning"](docs/inference.md).
- **A count the trie read beats one inferred.** `:distinct` holds only the column the walk can
  reach, and the join divides by the larger of the counts the two sides *read*; where neither
  read it the model falls back on a proxy rather than calling the join a cartesian product,
  which is the error that compounds fastest with depth. **No statistics table**: every number is
  already in the count-aware trie. The generators are split into blocks — two literals sharing a
  variable are one connected component — ranked by adjacent transposition, a descending sort on
  `s/(n−1)`, with two placements outside the law because they are claims an estimate cannot
  make: a block *proved* to match at most once runs first, and so does the block reached by the
  caller's bindings, the evaluables or the recursive literal.
- **The estimator is measured before the plans are, and `lein bench-plan` reports the curve.**
  q-error per join depth is the go/no-go: flat in the depth means the estimates compose. It
  reads **1.00 at every depth through six literals** on a uniform chain, and 1.00 / 2.75 / 2.87
  on a corpus built to break the independence assumption — wrong, and flat, where a compounding
  model would read about 7.5 at depth 3. Against an oracle over all 24 permutations of
  randomized four-way joins the planned order runs a mean **1.13x** the best possible (2.18x
  before), and the same conjunction as a rule's antecedents runs 7.1x and 8.4x faster planned at
  four and five antecedents. Two assumptions are stated rather than pretended away.
- **`query-plan` carries the numbers the order turned on.** Additive: `:est-rows`,
  `:est-prefix` and `:block` beside the `:est-matches` already there, in the browser's plan table
  too. A literal placed early on a small `:est-matches` whose `:est-prefix` then jumps is the
  model being wrong about a *join*, not about a literal. They are read off the plan that ran.

**The browser: jobs, caches, and a reading of the knowledge.**

- **Long work is one mechanism: a job registry, and the screen that watches it.**
  `vaelii.impl.jobs` holds every operation that takes minutes rather than milliseconds, with one
  status vocabulary (`:running` → `:cancelling` → `:done` / `:cancelled` / `:failed`), one
  progress reading and one cancel; the browser gained `/jobs`, `/jobs/rows` and `/jobs/cancel`.
  A job survives the request that started it, a finished job's report stays an hour, and nothing
  unsettled is ever dropped, since forgetting a job releases its writer claim while a thread
  still running is still writing. The catalog's load and export were moved **onto** the registry
  rather than left beside it. [docs/web.md, "Long work as jobs"](docs/web.md).
- **`POST /chain` is a job, with the derivation bound on the form.** A fixpoint over a corpus was
  minutes of this process's one writer inside a request, with nothing on screen and no way to
  stop it. It reports about four times a second, takes a cancel at its next report, and carries
  `:max-derivations`; a run that settles inside 250 ms still answers with the `/stats` page, so
  nothing small acquires a spinner. What a stopped run leaves is stated beside the button.
- **A second writing job is refused as `:job-busy`, where a second load answered `:busy`.** One
  job writes at a time — a load and a chaining run each claim the writer, an export claims
  nothing — and the refusal names the job that holds it. **Not Breaking**: `:busy` was thrown at
  one impl site and read by one impl namespace. It carries an entry because
  `type_contract_test` holds every `:type` in the sources.
- **The browser's status words are the registry's**, so `/kbs` says `running` and `done` where it
  said `loading` and `ready`. A screen-scraper is the only caller that can observe it.
- **What this process is holding, on a page — caches, heap, and the profiler.** Nothing measured
  what the engine holds *beside* the store, which is a dozen derived structures whose whole
  purpose is that a repeated question is not recomputed. `caches` is one read over all of them —
  entries, the bound they are cleared at, what one entry counts, and the hit rate where anything
  counts one — rendered at `/caches`. A hit rate is the cost model's report card. `VAELII_PROFILER`
  starts `clj-async-profiler`'s UI through a `requiring-resolve`, so it exists without the
  dependency and says so when the class is absent.
  [docs/web.md, "What this process is holding"](docs/web.md).
- **A number's scope is part of the answer, because two of them differ.** A row carries `:scope`
  for what its entries count and `:counters` for what its counters count: the literal cache's
  entries are one KB's and its counters are global, so rendering the second as the first
  attributes another KB's work to this one. `:unit` is on every row for the neighbouring reason,
  and `:limit` takes a thunk where the bound is a dynamic var.
- **The list is complete rather than merely finite.** Every cache-holding namespace declares
  itself into a register at load, so there is no central list to forget — and a cache in a
  namespace this process never loaded has no row, which is the honest answer where a row of
  zeroes would claim a cache that does not exist. A row that throws is reported as a cache that
  could not answer, and costs its own row and no other.
- **The clear is a measuring instrument, not an edit — and `clear-caches` took a KB and reached
  past it.** It drops every derived cache and reports what went; nothing is destroyed, so it is
  bare rather than `!`, moves no belief, holds no writer, and is usable *while* a load runs. It
  also reset the literal cache's process-wide hit and miss counters, so asking one KB to drop
  its entries zeroed the rate every other KB in the JVM was reporting. That reset is
  `{:counters? true}` now, off by default, with `:counters-reset` in the reply. *Class:* neither
  label — `clear-caches` is new in this release.

**The shipped ontology.**

- **The shipped ontology decontextualizes predicate metadata and nothing else.**
  `CxSociety` declared `(decontextualizedPredicate marriedTo)`, the one *domain* relation
  carrying a mark the rest of the ontology reserves for claims about a **predicate** — so a
  marriage stated anywhere became a claim of the whole KB, and a story, jurisdiction or
  hypothesis could not hold one the rest of the KB did not share. It reached past what the
  declaration names, too: a rule fires on the lifted copy, so `CxSocial`'s marriage rule put
  `knows` within reach of every data context. The declaration is gone; `marriedTo` keeps
  `symmetric`, and a KB that wants marriages lifted asserts the declaration where its reader can
  see it. *Class:* no label — ontology **content**, not the surface a caller writes against
  (§3.8). [docs/contexts.md, "What the shipped ontology declares it of"](docs/contexts.md).
- **Every argument position in the shipped ontology is declared.** 227 `argIsa` / `argGenl`
  declarations across `CxCore` and the four upper contexts that carried none, at `thing`
  throughout — the point being that every position is *stated*, not that any is narrowed. What it
  buys is schema completeness, a wrong-position refusal, and an edit rather than an addition when
  a position is later narrowed. `argGenl genl 2` is the one position left undeclared, and
  `CxCore` says why beside it. [docs/argtypes.md](docs/argtypes.md).
- **Six types enter the upper ontology, and the declarations narrow onto them**, so an argument
  constraint refuses something rather than only recording that the position was considered.
  `spatial_thing` takes `physical_object` beneath it, `time_point` sits under `temporal_thing`,
  `function` beside `predicate`, and `integer`, `character_string` and `context` name themselves.
  Space takes `spatial_thing` on all 100 of its positions, Time `temporal_thing` on 46 and
  `time_point` on 16, and the meta-vocabulary takes `predicate`, `function`, `context`, `integer`
  and `character_string` where it held `thing` — so `(before genlCx genl)` is an `:arg-type`
  refusal. *Class:* no label — ontology content (§3.8); what it owes instead is the roster that
  pins the shipped set, `vocabulary_audit_test`. *Migration:* a KB built on the shipped Space or
  Time vocabulary can be refused where 0.5.0 accepted it — the refusal names its convicting
  declaration, so widen that or state the argument at a type the position admits.
- **Flight is a capability of a kind, and the kind that cannot is an exception.** `flies` was a
  verb-shaped one-place predicate, which says the thing in a shape that cannot be generalized. It
  is `(hasCapability bird flying)` now, and `canTravel` goes the same way — `travelling` is a
  capability and `flying` a kind of it, so what flies travels off the `genl` closure rather than
  off a second rule. Three nouns enter the upper ontology: `capability` under `intangible`, with
  `flying` and `travelling` under it. `hasCapability` is read at **both** levels and carries no
  `relationKind`: `(hasCapability bird flying)` says the kind flies, `(hasCapability Tweety
  flying)` says one bird does, and a rule joins them rather than either being the other. The
  exception is written twice, because there are two things to except: `(not (hasCapability
  penguin flying))` at the kind, which leaves crow and eagle flying, and an `exceptWhen` on the
  descent rule at the member. *Class:* no label — ontology content (§3.8).
- **`has-prop?` and `props` accept every kind the engine marks.** `::prop-kind` named six of the
  ten kinds the special table records, so `:asymmetric` — which `has-prop?`'s own docstring and
  `docs/api.md` both list — along with `:abducible`, `:reifiable` and `:unreifiable` were
  documented calls that **instrumentation refused**. `prop-entry` records its kind in the table
  entry under `:prop`, so the roster is derivable from the vocabulary that defines it, and
  `special-table-test` holds the marked set and the specced set equal in both directions.

**Storage, and the instruments that price it.**

- **A bulk load is decomposed, and the index write is 57% of it.** `lein bench-loadphase` loads
  one corpus repeatedly through the same door, each run with one more phase stubbed out from the
  outside in, so consecutive runs differ by one phase and the deltas **sum to the baseline**. At
  1,000,000 distinct binary facts on the `:memory` pair — 43.4 µs/fact, 23,100 facts/s — the
  index write is **56.8%**, the JTMS node and premise mark 21.5%, the special-predicate suite
  10.5%, the public `assert` prelude 6.7%, the record store 3.5% and canonicalization 2.0%. Two
  decorators split the index write further: postings 35–39%, key streams 11–15%, count
  maintenance 6–10% — so the **counts are priced and are not the lever**. Two write-side tricks
  measured worse and are reported rather than built: a transient for the whole load ran 5–7%
  slower, and sorting by trie key buys locality a hash map has nowhere to spend.
  [docs/storage.md, "What a bulk load costs"](docs/storage.md).
- **The one write on that path that grows with the corpus is guarded, and the load reports its
  own rate.** A store posts its sentence's body to the negation memo's `:dirty` set, one `conj`
  per fact into a set that ends a load holding an entry per fact. Both readers filter by
  `:opposed` first, so `kb/note-opposed!` writes only for a body opposed before the store or
  after it. It does not move the wall clock (0.994x at 250,000 facts); what it removes is a
  structure proportional to the corpus, which is a claim about a ten-million-fact load's heap.
  Beside it, `bulk-assert-facts!` reads `:on-progress` — `{:phase :loading :done n :elapsed-ms ms
  :facts-per-sec r}` every 100,000 facts, and a closing `{:phase :done :total n …}`.
  [docs/storage.md](docs/storage.md), [docs/api.md](docs/api.md).
- **The workload profile grows the two arms no reasoning workload runs, and prices a
  retraction.** Every arm `lein bench-profile` had was a load, a chaining run, a proof or a
  synthetic probe, so the term index and roster read **zero** on every corpus — which reads as a
  family nobody uses and means a family no *reasoner* uses. The **interactive arm** makes the
  reads an application makes, and its read table is the inverse of every other arm's: 88%
  `:term-index`, 12% `:term-roster` on the shipped starter. The **churn arm** retracts a sample
  of premises and puts each back, the only way `unindex-sentex!` runs at all. A fifth tally
  `:retracts` catches what that costs, kept apart from `:writes` because `:dead` is decided by
  what else shares the prefix. On the starter a retraction is ≤23.8 batch ops against an assert's
  18.1. [docs/profile.md](docs/profile.md).
- **Eleven checks join the perf gate, and one of them was widened before it ever shipped.**
  `flat-cache-belief-flip`, `taxonomy-belief-flip`, `retract-context-cycle-scaling`,
  `retract-merge-scaling`, `retract-nat-scaling`, `closure-membership`, `plan-scaling`,
  `quality-report-scaling`, `genl-edge-negation-recheck`, `taxonomy-edge-arbitration` and
  `context-edge-arbitration` — plus **`standing-clash-reading`**, which costs what the standing
  clash entry above moved. **27 checks in the vector, and all 27 judge.** A read of the standing
  set is Ω(n log n) by construction, so its bound is calibrated from both ends: healthy it reads
  85.4x and 80.9x over a floor near 66x, and with the read filtering by cross product — the shape
  the claim rules out — 937.8x. It ships at **175x**. `retract-merge-scaling` reads 5.66x alone
  and 10.49x in place and ships at 18x, `lein perf` running one JVM over the whole vector: that
  position dependence is a property of the harness rather than of the engine.

## 0.5.0 — 2026-08-07

Operating the engine, in the two senses a running process needs: what it will let a
caller do, and what it will tell an operator it is doing. The daemon authenticates and
refuses to bind an address without a credential, ships as a container image, and says
which posture it started in; every switch the build reads has a row in a table a test
keeps honest, and the four that took a presence where they meant a value now refuse a
value nothing reads; the log level is a dial a running process turns; and the failures
that look like answers — a query that returns `()`, a KB that shares another's store, a
sentence legal enough to store and wrong enough to never match — each gained something
that says so. Beside all of that, two entries are about the vocabulary rather than the
process: a name can carry two more roles than it could, which is what a KB built by
reading text needs of it, and a reader that counted a context's contents was the only one
of three that did not say `count`. Nine entries are marked **Breaking**, one of which
simplifies a store's name from two numbers to one and one of which turns a switch's name
the right way up. The three **Refusal** entries (CONTRIBUTING §3.8)
cover input that is newly refused where what 0.4.0 did with it was run a configuration
nobody asked for and report a clean pass, so no working caller loses anything it had.
Each entry says what a reader would have observed; the mechanism is in the subsystem's
doc, and the entry names it.

**Triage, for a 0.4.0 caller.** Every Breaking and Refusal entry below carries its own
one-line *Migration*; this is the index to the ones that touch something you have
written or deployed.

| If your code… | Then |
|---|---|
| names `:record-space` / `:index-space` | one `:space` — keep the record number, drop the index one |
| runs a daemon on a non-loopback `--listen` | export `VAELII_API_TOKEN` there and in every client, or it exits 2 |
| reads a daemon 401, or branches on the wire `:type` | `:unauthorized` is a new one; `GET /health` is the only route without the token |
| relies on `VAELII_RETE=0` running the sweep | it means off now; unset, or `=1` for on |
| sets `VAELII_NOHIER` | it is `VAELII_HIER`, the other way up — `VAELII_NOHIER=1` becomes `VAELII_HIER=0` |
| sets `VAELII_QUERY_ENGINE` / `VAELII_QUERY_STRATEGY` | a name outside the roster is refused rather than silently running the default |
| sets `VAELII_WEB_PORT` for `lein browser` while `-main` stayed on 3000 | it moves both; pass `--port 3000` to pin `-main` |
| lists KBs out of a search-path directory holding more than 200 | name the ones that matter in the catalog file |
| depends on vaelii and has no SLF4J provider of its own | add one — `org.slf4j/slf4j-nop` no longer arrives transitively |
| branches on what `term-role` answers | `:sense` and `:lexeme` are two new answers — add arms, or a `default` |
| writes a `lex`-namespaced predicate | it names a lexeme now, and a lexeme names no relation |
| calls `core/context-size`, or sends the daemon `:context-size` | both are `count-in-context` — same arguments, same answer |
| compares two compound terms with `different` | a merged symbol inside one now makes them equal, where it did not |
| sets `VAELII_ASP_SOLVER` to a name outside `clingo`/`clasp` | it is refused at `open-kb` rather than silently running auto |

- **Breaking: a name can carry two more roles — a sense, and a lexeme.** `term-role`
  answers `:sense` for a disambiguated type (`abrasive-grit`) and `:lexeme` for a symbol in
  the `lex` namespace (`lex/fool's_gold`), so its documented domain gains two values a total
  `case` has no arm for. Two things move at a `:strict` front door with them: a lowercase
  dashed name is a legal unary type where it was refused, and a lexeme applied to arguments
  is refused (`:lexeme-functor`), a surface form naming no relation. *Migration:* a `case`
  over `term-role` gains `:sense` and `:lexeme` arms, or a `default`; nothing else changes
  unless you wrote a `lex`-namespaced predicate, which names a lexeme now and cannot be
  applied to anything. `docs/naming.md`.
- **Breaking: `context-size` is `count-in-context`.** The three O(1) cardinality readers
  are one family and two of them said so; the third delegates to a protocol method already
  called `count-in-context`, so the name it now carries is the one it always answered to a
  layer down. The daemon's op keyword moves with it. *Migration:*
  `(v/context-size kb ctx)` becomes `(v/count-in-context kb ctx)` and `{:op :context-size}`
  becomes `{:op :count-in-context}` — same arguments, same answer, and the old spellings are
  gone rather than deprecated. `docs/api.md`, `docs/indexing.md`.
- **Breaking: `different` descends into compound arguments.** It normalized each argument
  with one lookup in the equality closure, and the closure is keyed by symbol — so a compound
  was never found in it and `(different (QuantityFn 5 Kilogram) (QuantityFn 5 Kg))` answered
  *different* with `(sameAs Kilogram Kg)` believed. It replaces symbols at every depth before
  comparing, the congruence its documentation always described. *Migration:* a goal comparing
  two compounds can newly answer false where a merge reaches inside one; comparing symbols is
  unchanged. `docs/equality.md`.
- **Breaking: one space number names a KB's stores, `:space`.** `open-kb` takes a single
  number where it took `:record-space` and `:index-space`, and it defaults to 0; a
  `:disk` KB's derived directory is `space-<n>`, and the suite owns a block of two db
  numbers rather than four (scratch 15, isolated 14). *Migration:* `{:record-space 2
  :index-space 3}` becomes `{:space 2}` — keep the record number, drop the index one;
  either retired key is refused by name (`:type :unknown-option`) rather than ignored.
  Pass `:dir` to name a durable directory the derived spelling does not reach.
  `docs/storage.md`.
- **Breaking: the daemon authenticates, and refuses to bind an address without a
  token.** With `VAELII_API_TOKEN` set, every request carries `Authorization: Bearer
  <token>` or is answered 401 with `{:ok false :type :unauthorized}` — a new `:type` on
  the wire — and `GET /health` is the only route that answers without it. What the daemon
  binds decides what it requires: `--listen` naming a non-loopback address without a token
  is one line on stderr and exit 2, where 0.4.0 logged a warning and served the whole write
  block to anything that could reach the port. *Migration:* export `VAELII_API_TOKEN` for a
  daemon that names an address and give the same value to every client that reaches it;
  `vaelii.client` reads the same variable and takes `:token`. Nothing changes on the
  loopback default. `docs/operations.md`, "Daemon — `vaelii.serve`".
- **Every switch the build reads has a row, and a test keeps the roster honest.**
  `docs/operations.md` gains a configuration table — 56 environment variables and JVM
  system properties, grouped by who sets one, each with where it is read, its legal
  values, its default, and the one thing it decides. `config_surface_test` pins the
  names against `test/golden/config-surface.edn` in both directions and checks each
  `file:line` citation against the line it names, so the table cannot drift from the
  code without a failing test. CONTRIBUTING §3.8 files a renamed or removed switch as
  **Breaking**.
- **Refusal: the four harness switches read a value instead of a presence.**
  `VAELII_RETE` and the hierarchical-retrieval switch were membership tests, so `=0` ran
  the sweep it names and an exported-but-empty variable ran one nobody asked for; the two
  query switches took a bare `(keyword …)`, so a misspelt engine ran the *default* and
  reported a clean pass for a configuration nothing exercised — the worst shape a test
  switch can have, since the result reads as evidence. All four take the engine's boolean
  vocabulary now and refuse anything else by name, and a test calls each reader with the
  properties cleared so the table's **Default** column fails rather than merely reading
  wrong. All four are read only by the test harness, which is what keeps a silent change
  of sense inside a Refusal rather than making it a ninth Breaking. *Migration:* none for
  a value in the vocabulary; a job relying on `=0` meaning *on* now gets the sweep off.
  `docs/operations.md`, "Developer — the suite and the scripts".
- **Refusal: the ASP backend switches are read against their domains, at the door.**
  `VAELII_ASP_SOLVER` took a bare `(keyword …)`, so a misspelt backend matched no arm of the
  selector and ran **auto** — a run pinned to clasp could use clingo and report a clean pass
  for a backend nothing exercised. `VAELII_CLINGO_MAX_BYTES` parsed with a bare
  `Long/parseLong` inside a cached delay, so a non-numeric value threw from the first ASP
  solve rather than from the configuration that was wrong. Both go through `config/check!`
  now — refused at `open-kb`, by name. *Migration:* none for a legal value.
  `docs/operations.md`.
- **Breaking: `VAELII_NOHIER` is `VAELII_HIER`, and the sense is the other way up.**
  A switch that carries the negation in its own name makes `=0` mean *on*, which is the
  one thing a reader must not have to work out at a glance — and the entry above had
  just made the value load-bearing, so the two had to move together or `=0` would read
  as the fallback path it now selects. `VAELII_HIER` defaults `true` (the set-algebra
  retrieval), and `VAELII_HIER=0` routes every context-scoped match through the
  reference nested fan-out. *Migration:* `VAELII_NOHIER=1` becomes `VAELII_HIER=0`; a
  `VAELII_NOHIER` left set is simply unread, since a variable cannot be refused by name.
  `docs/operations.md`.
- **The log level is a dial a running process turns.** `vaelii.core/set-log-level` takes
  one of `:error :warn :info :debug :trace` and installs Trove's console backend at it;
  `log-level` reads back what is in force, and `VAELII_LOG_LEVEL` says it at startup (a
  value outside the five is refused by name). Unset, the engine installs **no** backend
  at all, so an application holding its own `taoensso.trove/*log-fn*` keeps it. Three
  `:debug` statements are what make turning it up worth doing: what a chaining run
  concluded and how long it took, what a settle cost and found, and the rule a dropped
  conclusion came from. `docs/operations.md`.
- **Breaking: `VAELII_WEB_PORT` moves `-main`'s port, and not only `lein browser`'s.**
  `dev-repl` read the variable and `-main` did not, so `VAELII_WEB_PORT=3011 lein run -m
  vaelii.web` bound 3000 and logged 3000. Both read one `default-port` now: the variable,
  else the `vaelii.web.port` property, else 3000; an explicit `--port` still wins.
  *Migration:* a deployment that set the variable for `lein browser` while relying on
  `-main` ignoring it now moves both; pass `--port 3000` to pin `-main`.
- **Breaking: a search-path directory is probed for its first 200 entries, and a KB
  below the cut no longer appears on `/kbs`.** `sources` is recomputed per request, which
  is what lets a corpus appear with no restart and what made the scan unbounded — a
  `classify` per candidate, and a size estimate per `:store` one, on every page load.
  `catalog/max-discovered` bounds it, and the cut is named on the page and in the log,
  since a list that quietly ends early reads as "this machine has no other KBs".
  *Migration:* name the ones that matter in the catalog file to list them regardless of
  the count. `docs/catalog.md`.
- **The front door says what a legal-but-wrong sentence should have been.** `(isa Muffet
  Dog)` breaks no naming invariant, so it stored a two-place relation nothing reads and
  `(isa? kb 'Muffet 'Dog)` answered false with nothing to search for. `nm/advice` reads
  intent where `problems` reads the invariants: it recognizes the shape and logs a
  `:warn` once per process spelling the rewrite that was meant. Beside it, a
  `:no-placement` drop names `genlCx` and points at the `:rule-context` /
  `:fact-contexts` already on the entry. `docs/naming.md`.
- **A second `open-kb` defaulting onto the shared in-RAM space now warns**, naming both
  fixes — give the KB its own number, or name `{:space 0}` explicitly to say the sharing
  is meant. A warning rather than a refusal, since sharing the space is how `recover`
  sees the same records and how a base is mounted. `docs/storage.md`.
- **Refusal: the CLI checks each command's argument count before it dispatches, and
  `help` names what each one takes.** `dispatch` reached into `args` with `nth`, so `lein
  cli assert '(dog Rex)'` answered `error: IndexOutOfBoundsException` — true about a
  vector, no help to someone who left off a context — and a long line was worse, since
  the extra operand was dropped in silence. One table now carries every command's arity,
  operands and gloss, so `check-arity!` and the usage text cannot go out of step.
  *Migration:* none for a call already at the right arity; `lein cli help` prints the
  count each command takes. `docs/operations.md`.
- **`docs/troubleshooting.md` is a new page, indexed by symptom rather than by
  subsystem.** The engine's hardest failures are the ones where nothing goes wrong — a
  query answers `()`, an `assert` returns a handle, and both are legitimate values no
  error distinguishes from the answer that was wanted — so a reader has to already know
  the cause to find the page explaining it. Nine symptoms, each with what you would have
  observed, how to confirm it in one call, and the fix.
- **`lein lint` gains a versions check, and the kondo row notes a local/CI version
  mismatch.** The `:with-foreign` pin and `defproject`'s own version are cut together and
  nothing held them to it: the 0.4.0 bump left the pin naming `0.3.0`, so every
  `lein with-profile +with-foreign` command failed to resolve. `lint-versions` reads that
  pair and the `lein-cloverage` version stated twice, failing when either disagrees. The
  kondo row prints a `NOTE` — never a failure — when the local binary is not the version
  CI pins, since a newer kondo infers more than an older one flags.
- **Three doc samples now print what they actually produce, and `prove`'s docstring says
  it counts proofs, not answers.** `prove` returns one solution per derivation, so a goal
  reachable both as a materialized fact and as the rule concluding it comes back twice
  with equal maps — wrap it in `distinct` for an answer set, or reach for `query` / `ask`,
  which project to the goal's variables and answer each binding once.
- **The daemon ships as a container image**, with a two-stage `Dockerfile` and
  `docker-compose.yml`: a build stage that runs `lein uberjar`, and a runtime stage of a
  JRE and the jar alone. The container binds an address, so the token is required — an
  image run without `VAELII_API_TOKEN` does not start rather than serving unauthenticated
  — and one container per volume, a second opener being refused `:disk-locked` rather than
  scaled, which is why the compose file carries no `replicas:`.
  `docs/operations.md`, "Container — the daemon as an image".
- **A reflection warning and an uncalled public var now stop the build.** Both signals
  were already emitted and neither was read. `lein lint` gains two rows: **`reflect`**
  compiles `src` and `bench` and fails on any reflection, auto-boxing or primitive-recur
  warning, and **`unused`** reads clj-kondo's analysis over `src test bench` and fails on
  a public definition with no usage, against `scripts/unused-publics-baseline.txt`. Ten
  warnings had to go first, none in `src`. CONTRIBUTING §1.1.
- **Breaking: `org.slf4j/slf4j-nop` no longer reaches a consumer's classpath.** It sat in
  top-level `:dependencies`, so every application depending on vaelii inherited it too,
  where it could win SLF4J's provider race against that application's own backend and
  silence it — the one thing a library must not do on a consumer's behalf. It lives in
  the `:dev` and `:uberjar` profiles now, so every entry point this repo ships still
  carries it while `lein deploy` publishes it as a test-scope declaration a consumer does
  not resolve. *Migration:* an application that ships Jetty, had no provider of its own,
  and relied on vaelii's to keep it quiet now sees SLF4J's "no providers" line again —
  add `org.slf4j/slf4j-nop`, or any other provider, as its own dependency.
  `docs/operations.md`.
- **A public `--listen` bind with no `VAELII_ALLOWED_HOSTS` now warns.** Naming an address
  drops the `Host` allowlist to every `Host` answered — a deliberate default, since a
  reverse proxy legitimately sets its own and an operator cannot always enumerate it in
  advance — but nothing said so at startup. `host-posture` names the policy
  (`:allowlisted` / `:open`) beside the token question, and a public bind left unset gets
  its own warning, apart from the token and TLS lines so a reader knows which check is
  missing.
- **`docs/troubleshooting.md` and `docs/storage.md` now name `:type :unknown-backend`.**
  `open-kb` throws it from five call sites — an unknown `:backend` sugar name, the one
  `{:records :memory :index :disk}` pairing the axes refuse, and an unknown `:records` /
  `:index` / `:tms` kind — and none carried a line in either doc. The new entry reads the
  other key each throw's `ex-data` carries to say which of the five it is.

## 0.4.0 — 2026-08-05

Correctness fixes found by reading the engine against its own stated invariants, in
the places 0.2.0 and 0.3.0 did not reach: a backward-chaining loop guard that made a
conjunctive query answer nothing, doors that disagreed about what they would accept,
an index trusted without being checked against the records it describes, slots and
keys that let arrival order decide belief, and derived caches a settle read one
revival out of date. Thirteen entries are marked **Breaking** — they refuse input
0.3.0 accepted, rename what it exported, or change an observable contract — which is
why this is 0.4.0. The **Refusal** entries (CONTRIBUTING §3.8) cover input that is
newly refused where what 0.3.0 did with it was corrupt state or answer a different
question in silence, so no working caller loses anything it had. Each entry says what
a reader would have observed; the mechanism is in the subsystem's doc.

**Triage, for a 0.3.0 caller.** Every Breaking and Refusal entry below carries its own
one-line *Migration*; this is the index to the ones that touch source you have written,
so the rest can be read at leisure.

| If your code… | Then |
|---|---|
| hands `assert` text it did not read as EDN | it is refused (`:shape`) — fix the producer |
| writes `exceptWhen` literals like `(lives_in ?x cold_place)` | spell them to the invariants; re-check any rule 0.3.0 left bare |
| spells an `edit!` batch `{:adds …}` | spell it `{:add […] :remove […]}` — the old key wrote nothing |
| names one of `:record-space` / `:index-space` | name both, or neither, in every opts map |
| passes `:direction` to `assert` on a non-rule | it is refused; a rule takes it and now acts on it |
| states one rule two ways (bare `implies` after a `set/*Rule`) | the slots join by content; `retract!` and re-assert to narrow one |
| calls `edit` or `edit-with-consequences` | they are `edit!` and `edit-with-consequences!` — the wire op stays `:edit` |
| matches `:bad-opt`, or a `:shape` from a non-map `opts` | match `:unknown-option` |
| reads a dump's `meta.edn` dialect | it is `:vaelii` |
| stores skolem witness names across runs | the names moved; rebuild from the assertions (`export!` / `import!`) rather than carrying both spellings |
| parses a daemon 500 for a client mistake | it is a 400 with a `:type` |
| writes `(ist Ctx S)` with other than three elements | it is refused with `:shape` |

- **A conjunctive query could answer nothing while each of its conjuncts answered.**
  `[(anc Tom ?y) (anc Tom ?z)]` was empty where `(anc Tom ?y)` answered twice, because
  the per-path loop guard grew for a whole frame and a queued conjunct is a sibling of
  the expansion, not a descendant. Silent in every direction: forward chaining and the
  node engine both answered, `provable?` said false, `prove-within` reported `:status
  :complete`, and the planner became semantic. `docs/inference.md`, "The loop guard's
  scope is the subtree, not the frame".
- **Breaking: `assert` refuses a sentence that is not an s-expression.** A string — what
  a failed EDN read hands back, from `impl.cli`'s `read-arg` and the daemon's `:args` —
  was stored, indexed and believed as an object no query can match; `nil` likewise; a
  symbol, number or map threw a bare `UnsupportedOperationException` with no `:type`.
  `check` refused all five, so the door built to predict `assert` disagreed with it.
  *Migration:* nothing a working caller sent is refused; fix the producer that handed
  `assert` unread text, and discriminate on `:shape`.
- **Breaking: an `exceptWhen` query's literals are held to the naming invariants.**
  `(exceptWhen (lives_in ?x cold_place) …)` stored a literal `docs/naming.md` says is
  refused, as an exception no query could match — so the rule read as guarded and fired
  as bare. Both doors now read each conjunct, before the rule is stored, so a refused
  exception leaves no bare rule believed. *Migration:* spell the exception's literals to
  the invariants (`livesIn`, not `lives_in`), and re-check any rule 0.3.0 left bare.
- **Breaking: an `edit!` batch key nothing reads is refused.** `{:adds […]}` bound nil,
  so `edit!` wrote nothing and reported `{:added [] :removed {…0}}` — a success — while
  `check-edit`, whose job is to predict exactly that, reported no problem. Over the
  daemon it was a `200 {:ok true}` for a write that did not happen. *Migration:* spell
  the batch `{:add […] :remove […]}`; a batch under any other key wrote nothing.
- **Breaking: naming one in-RAM space number and not the other is refused.**
  `:record-space` and `:index-space` default independently, so
  `{:backend :memory :record-space 77}` paired a private record store with the
  process-default index every other in-memory KB writes. `assert` then found the other
  KB's handle, read it as a duplicate, **stored nothing**, and returned a handle `in?`
  answered true for. A fork's `:base` and `:overlay` halves take the same keys and are
  refused the same way. *Migration:* name both or neither, in every opts map.
- **A durable index is checked against the records it claims to describe.** `layout.edn`
  gates the index's key shape; nothing gated its coverage, so a short index opened
  clean, answered short forever and re-cemented its own stamp — and re-asserting a fact
  it could not find minted a second handle for a sentence already stored. Three ways in:
  a torn `kv.log` tail, a directory grown under a derived-index mode, and a crash
  between the record write and the index batch. `docs/storage.md`.
- **Breaking: `assert` acts on `:direction` instead of accepting and dropping it.** Only
  `assert-rule` read the key, so a rule asserted `{:direction :backward}` stored `:both`
  and forward-chained, materializing the cross product a backward-only rule exists to
  avoid. A `:direction` on a non-rule, one contradicting the sentence's own wrapper, and
  a value outside the roster are refused rather than resolved. In the same pass a
  non-map `opts` answers `:unknown-option` from both doors, where `check` said `:shape`.
  *Migration:* spell the direction `:backward` (`:forward` `:backward` `:inert` `:both`);
  a `check` caller matching `:shape` for a non-map opts matches `:unknown-option` now.
- **Breaking: a re-asserted rule's direction and defeasibility resolve by content.**
  Neither slot is in the identity key, so a rule stated two ways resolves to one record
  and the second spelling was dropped — letting arrival order decide a slot that decides
  belief. A bare `implies` after a `set/inertRule` stayed inert and never fired; after a
  `set/defaultRule` it stayed defeasible and lost to a monotonic rival it should have
  tied with. The resolution reaches conclusions already derived, since a justification
  bakes the rule's contribution in as its `:strength` at fire time.
  `docs/canonicalization.md`. *Migration:* the join only widens a slot; to narrow one,
  `retract!` the handle and re-assert the intended spelling.
- **The derived caches are reconciled with what `clear-defeats!` revived.** A settle
  lifts last settle's defeats at its top, but the cached closures were refreshed only in
  `settle-finish` — after `constraint-nogoods` had read them — so discovery asked its
  question against a vocabulary one settle out of date. A `P`/`¬P` pair made visible by
  a revived `genlCx` edge went unarbitrated and `retract!` returned with both
  believed, a state `recover` over the same records disagrees with.
- **The disk KV index reads and publishes its RAM map under the lock.** `apply-ops!`
  read `@data` before acquiring and published after releasing, while `compact!` runs on
  the durability daemon's executor — a thread the single-writer contract says nothing
  about — so a compaction in either window rewrote the log from a map missing the
  in-flight write. `kv-clear!` was sharper: a compaction between its truncate and its
  publish wrote the entire pre-clear map back over the log just emptied.
- **Breaking: a client's mistake answers 400 with a `:type`, not 500 with none.**
  `docs/operations.md` promises every `{:ok false}` carries the type the engine threw;
  an unreadable body, a wrong argument count and an unknown op all answered untyped, the
  first two as 500s. The engine's whole refusal vocabulary now answers **400**, unlogged
  — answered 500 they count as backend faults at every reverse proxy and 5xx alarm.
  *Migration:* a client branching on the status code should branch on `:type`; every
  `{:ok false}` carries a non-nil keyword.
- **The browser's `/propose/*` EDN read catches `Throwable`**, as every other
  untrusted-EDN read in the namespace already does. A deeply nested form raises
  `StackOverflowError`, which an `Exception` catch let escape — and the browser has no
  exception middleware, so it left the handler entirely.
- **Refusal: `query` refuses a non-map `opts` and a negative or non-integer
  `:max-depth`.** Both read as "no depth", which is not an error condition but a
  *different question* — the no-rule-expansion answer, returned as if it were the
  bounded one asked for. `{:max-depth 0}` is admitted: it is that answer asked for by
  name. *Migration:* none for a working caller.
- **Breaking: `edit!` refuses what `check-edit` reports, before applying anything.** The
  two disagreed in both directions: a 4-element `:add` entry applied with the extra
  silently dropped where the dry run reported `:shape`, and a non-sequential entry threw
  a bare `ISeq` error from every door. An unknown `:remove` handle is refused before any
  entry is applied, so a checked-clean batch cannot half-apply. *Migration:* a
  remove-if-present batch filters its handles through `in?` first.
- **The recursive-literal hold-back keys on the peeled predicate.** A `not`- or
  `ist`-headed consequent read its own frame as the predicate, so every frame-headed
  antecedent was "the recursive literal" — two orderings of a negated-head rule minted
  two handles, and a genuinely recursive rule with a negated head lost the hold-back,
  turning right-recursion left-recursive.
- **Breaking: a skolem witness is a function of its rule's content, not its handle.**
  Retracting and re-asserting the same rule re-fired to a *different* witness, so a fact
  stated about the old one silently stopped co-referring — and two KBs holding the same
  knowledge in different orders stored different `termOfUnit` content, a handle in
  stored content that order independence rules out. `docs/skolem.md`. *Migration:*
  rebuild the KB from its assertions (`export!` / `import!` replays firings) rather than
  carrying both spellings.
- **Breaking: `edit` is `edit!`, and `edit-with-consequences` is
  `edit-with-consequences!`.** The batch's `:remove` half runs the same
  `retract-storage!` sweep `retract!` runs, while the name read as additive — the one
  gap in the `!` roster the convention exists to close. *Migration:* rename the calls;
  the wire op stays `:edit`, as `:retract` stays for `retract!`.
- **Breaking: `:bad-opt` is retired, and one compression spelling survives.** Two
  keywords split one failure class on no rule a reader could predict — seven sites said
  `:bad-opt` where thirty-four said `:unknown-option`. *Migration:* discriminate on
  `:unknown-option` and `:unsupported-compression`.
- **Breaking: the dump's `meta.edn` names its dialect `:vaelii`.** Decorative on the read
  side — the frame decides how a sentence is reconstructed — but it is a value in the
  frozen format and a documented key of `import-dump`'s return, so the name it carries
  is now-or-never. *Migration:* a reader matching the old value matches `:vaelii`;
  `import-dump` reads dumps written either way.
- **The node engine's claimed-key reads each guard's identity, not the guard count.** Two
  distinct rules, each carrying its own `exceptWhen`, can rewrite one goal to the same
  canonical residual through the `genl` fan; keyed on the count the two children were
  one key, so the second was dropped before it was enqueued and every answer only its
  exception admits was lost — silently, on the path `query` routes to whenever
  `:max-depth` is given. `docs/inference.md`.
- **A belief flip on a visibility `except` queues the same re-check as its arrival.**
  Only the store and removal chokepoints called `recheck-except`, so an except *defeated*
  by a settle's resolution revived nothing it hid: backward proving answered yes while
  the store held nothing, and which belief set the KB ended with depended on the order
  the except and its defeater arrived.
- **`recover` reads only positive, atomic declarations into the taxonomy.**
  `sentexes-with-functor` returns both polarities and the rebuild arms destructure the
  positive shape positionally, so a stored `(not (genl a b))` bound its inner sentence as
  a taxonomy node and nil as the other — poisoning every cache on any recover, the
  default `{:recover? :auto}` reopen included.
- **A `:neg` nogood is an at-least-one in every reader.** The ASP translation's soft
  branch emitted only the positive body atoms, so a `:neg`-only nogood — what
  `set/softConstraint` over negated choice literals produces — emitted its violation
  witness as an unconditional fact: no steering pressure, and `:violated` reported a
  satisfied at-least-one as broken. `docs/solving.md`.
- **`conflicts` and `contradictions` are content-ordered.** Each report's sides were
  already ordered by content; the *list* came off a hash set of handle-keyed nogoods, so
  which pair `(first (contradictions kb))` returned was an answer about which was typed
  first. `docs/nmtms.md`.
- **Refusal: the connective frames are shape-checked at every door.** An `implies` at
  arity 2 threw a bare `IndexOutOfBoundsException` while arity 4 stored a silently
  truncated rule `check` read as clean; `(not A B)` stored as a positive fact whose
  record and index disagreed; a bare symbol passed as a rule literal was accepted,
  unmatchable; and a non-finite measure magnitude stored cleanly, then threw out of every
  later duration goal in the context. *Migration:* nothing a working caller sent is
  refused — every one of these stored an object no query could match.
- **Refusal: the last open rosters close.** `find-terms` and `abduce` take key rosters (a
  misspelt `:mtch` ran the prefix default; a misspelt `:keep?` tore down the scratch
  context whose handles the caller meant to commit), the CLI refuses a flag outside its
  roster, `escalate` refuses a floor outside 0–7, and `import-dump` refuses an unknown
  `:framing` where it guessed a reader and failed as a `ZipException`. *Migration:* spell
  the key or flag as the refusal's roster lists it.
- **Refusal: the web and serve entry points refuse what their grammars do not know.**
  `vaelii.web --listen` with no address parsed to a nil host — Jetty's wildcard bind,
  with the Host allowlist reading nil as *any* — so a truncated command line put the
  browser's unauthenticated write routes on every interface with the rebinding guard
  off. `serve` read its positionals as a prefix, so `4200 --listen 0.0.0.0 /var/lib`
  dropped the directory and ran a disk daemon in memory. *Migration:* none beyond
  completing the command line.
- **Refusal: the opts and shape rosters reach the remaining doors.** The roster guard
  held at `assert`, `why`, `query` and `open-kb`, and every other door took the misspelt
  key in silence — answering a different question than the one asked. Now refused: an
  `open-kb` mount or durability key without its axis, an opts key nothing reads at
  `forward-chain`, the extent readers, `preview`, `export!`, `import!` and the anytime
  budget maps. *Migration:* spell the key as the refusal's roster lists it.
- **Refusal: the operator's mistakes answer in one line.** A CLI flag missing its value
  bound nil in silence — `lein cli assert '(dog Muffet)' Ctx --strength` stored known-true
  content at `:default` — and now exits 1 naming the flag; `--memory --dir` is refused as
  a contradiction. *Migration:* none beyond completing the command line.
- **The browser and CLI survive what they read.** The repl loop and the CLI command arm
  catch `Throwable`, so a deeply nested form answers `error:` and a next prompt; the
  browser's retract POST makes the `check-edit` round-trip `docs/operations.md` promises,
  so a stale handle answers the problem panel rather than a success-styled "Retracted 0
  sentexes".
- **Refusal: every durability switch is read against a domain, and a value outside it
  fails the open.** Each of the thirteen checkable `vaelii.*` / `VAELII_*` switches was a
  membership test or an equality against one spelling, so none of them had a wrong value —
  every misspelling was the *other branch*, silently: `vaelii.disk.auto-compact=disabled`
  read as compaction on, and `vaelii.disk.fsync=always` as the three-second tick, the level
  the operator was trying to leave. The three numeric reads had no catch at all.
  *Migration:* none for a working setup, but two spellings now *act* where they were
  ignored — `vaelii.disk.tokens=1` and `vaelii.index.snapshot=1` turn their features on,
  and `vaelii.disk.lock=0` disables the lock. Spell what you mean. `docs/storage.md`.
- **Refusal: the mapped index image refuses the platform it corrupts on.** The image
  publishes by renaming a new file over the live one while it is mapped, which is what put
  `vaelii.index.snapshot` on macOS and Linux only — `docs/storage.md` said so and nothing
  enforced it, so on Windows the publish failed part-way through a four-file commit, naming
  neither the cause nor the fix. *Migration:* none — the property never worked where it is
  now refused. `docs/storage.md`.
- **Breaking: `assert-rule` refuses a rule literal whose predicate is a variable.**
  `(implies (and (?p ?x ?y) (transitive ?p)) (?p ?y ?x))` asserted cleanly and was indexed
  under `?var0`, which no arriving fact and no goal can spell — so the rule answered no
  backward goal at all and fired forward only when the concrete-predicate antecedent
  beside it arrived. Two arrival orders, two answers, from a rule the engine reported as
  accepted. An `:inert` rule is exempt, which is what `CxCore`'s decontextualized-
  predicate lift is. *Migration:* assert the instantiated rules, one per predicate the
  metarule ranged over.

## 0.3.0 — 2026-08-04

Correctness fixes across the durable index, the snapshot, the JTMS, the export dump
and the bounded prover, a sweep that gives every refusal a `:type`, the one wire
contract 0.2.0's own sweep left qualified, and the serialization both servers' storage
layer already assumed. Then a run of **inference and belief** work: two orders that
reached two answers, the two doors that disagreed about an inherited claim, and two
enumerations that grew with the vocabulary rather than with their own answer. Eight
entries are marked **Breaking** — they refuse input 0.2.0 accepted or change an
observable contract, which is why this is 0.3.0 and not 0.2.1; the rest are compatible.

- **Breaking: the daemon's refusal `:type` keywords are plain** — `:not-edn`,
  `:cross-origin`, `:bad-host`, `:body-too-large`, where the namespace serving them
  qualified each one. This finishes tree-wide what 0.2.0's own breaking entry claimed.
- **Breaking: both servers hold one request-body ceiling.** The cap and its
  `VAELII_MAX_BODY_BYTES` override (16 MiB) live in `vaelii.impl.guard`, which both
  read, so the browser answers **413** for an oversized form body where only the daemon
  did. A daemon read is also fully realized **inside** the write monitor — `wire-safe`'s
  walk is what realizes a lazy answer, so running it after the monitor released let a
  `:query` straddle a concurrent `:assert`.
- **Breaking: the browser serializes its writes.** Jetty serves the write routes on a
  thread pool, so two POSTs were two writers — where the storage layer is written on the
  promise that they are not. Interleave two and the WAL holds both frames while the RAM
  map holds one, so the running index and the one replayed on the next open disagree.
  The browser now takes one process-wide monitor around every content write, as the
  daemon always did; a concurrent write waits rather than racing.
- **Every `ex-info` the engine throws carries a `:type`.** Twenty refusals threw an
  untyped map, so a caller had to guess from which keys were present. Two forms that
  threw a raw Java exception now answer instead: `(genl ?x ?x)` / `(disjoint ?x ?x)`
  answer the question one variable in both positions asks.
- **Breaking: an `ist` form must have exactly three elements.** 0.2.0 read `assert` and
  `check` positionally, so `(ist Ctx S junk)` asserted with the extra silently ignored
  and `(ist Ctx)` raised a raw `IndexOutOfBoundsException`. Both refuse with `:shape`.
- **The durable index is gated on its key layout at open.** A log whose stamp does not
  match `kv/index-layout-version` is cleared, rebuilt from the records and restamped,
  `:recover?` notwithstanding; without the gate such a log replays cleanly and then
  misses every read whose key shape moved. **A 0.2.0 durable store carries no stamp, so
  its first open under 0.3.0 pays one automatic reindex**: O(records), logged at `:warn`,
  paid once. `docs/storage.md`.
- **Breaking: `open-kb` refuses a `:base` whose durable index is at an older key
  layout** (`:stale-index-layout`). The repair is a write and a base is mounted
  read-only, so the refusal names the one place the rebuild can happen: open that
  directory as a KB, then mount the fork over it.
- **Breaking: `(fork (fork base))` is refused** (`:stacked-fork`), which is what
  `docs/overlay.md` has always stated.
- **Breaking: `open-kb` refuses a `:recover?` setting it does not name.** `:auto` is the
  default, `true` an alias for it, `:warn` and `false` the rest; any other value read as
  the warn branch and handed back an empty TMS over a store that is not empty, which
  answers `[]` to everything. A stale derived index is dropped on open whatever
  `:recover?` says.
- **Breaking: `close!` releases a durable fork's own directory.** A fork's writable half
  takes the same exclusive lock as any durable KB, so without its own `:dir` it could
  never be handed to another process short of exiting the JVM. 0.2.0's docstring promised
  the opposite, so code that closed a fork in a `finally` and kept reading it worked and
  now does not.
- **A failed compaction takes its temporary files with it.** A rewrite that threw closed
  its handles and left `<log>.compact` behind, and the next compaction in the same
  session opened that temp and appended to it — its replay then put back records deleted
  in between. The cleanup is scoped to the pre-commit phase: past the marker the temps
  are the only complete copy.
- **A failed open gives back the directory lock with no handles still on it.**
  `open-kv-backend` and `open-token-log` replayed their logs outside any guard, so a torn
  frame propagated to a caller that answers a failed open by releasing the lock —
  leaving it released while this JVM still held an open handle.
- **A fork's merged `kv-entries` is realized under its monitor.** Both halves were lazy,
  so the seq handed back from inside the lock realized outside it. An export of a fork
  taken while anything wrote it projected two states at once.
- **The rete alpha registry is synchronized.** It is JVM-lifetime shared state reached
  from the store observer hooks, which fire on whichever thread is writing, and a
  `HashMap` racing its own rehash can leave a reader spinning on a probe loop that never
  terminates. Its check-then-put is one step too, so two callers cannot leave the loser's
  alpha permanently unmaintained.
- **`load-source` claims the catalog under one monitor.** The busy test, the
  already-loaded test and the registration were three separate reads, so two requests
  arriving together each passed all three and spawned a loader.
- **The browser reads untrusted EDN under `Throwable`, as the daemon does.** A deeply
  nested form overflows the reader's stack with a `StackOverflowError`, which an
  `Exception` catch lets escape — a 500 where an unreadable term is the ordinary answer.
- **The index snapshot's roots-fallback blob is validated like the sections beside it.**
  `roots-fallback.nippy` carries argument-root postings, which are primary index truth,
  and a missing or torn blob loaded as `[]` behind a warning while every argument-root
  read answered `#{}` out of a snapshot that opened clean. The meta records the blob's
  count and byte length, and the load thaws strictly.
- **The mapped index snapshot survives a JVM shutdown, and a failed save leaves the
  previous image intact.** The stamp is taken against the records before a byte moves,
  durability registrants close in phases, and every section lands in a `.tmp` until the
  swap. A failed *open* likewise gives back the handles it took.
- **An export dump carries every provenance stamp, and `export → import → export` is
  byte-stable.** The provenance walk covers justification handles as well as sentex ones,
  and import stores a justification's antecedents as a **vector**, the shape the engine's
  own write path stores.
- **The JTMS dedup index carries the identity of the TMS it mirrors.** A nested chain
  over a second KB — legal from an `:on-progress` callback, with overlapping handle
  spaces — could answer one KB's dedup question out of the other's supports. Keys coerce
  fixnum boxing to `Long` at the boundary, since the map compares with Java `equals`
  where the scan compares with `=`.
- **`prove-within` prepares its goal**, through the same `prepare-goal-for-read` every
  other read path takes, so a reifiable NAT or a merge-retired spelling is the same
  question under the bounded prover that it is under `ask`.
- **The rete forward matcher fans over predicate-`genl` sub-predicates at every arity**,
  as the reference `res/match-pattern` does. Fanning only for a two-element sentence gave
  the opt-in matcher a different belief set on any rule whose antecedent had another
  arity.
- **A firing refused at derive time comes back when its exception releases.**
  `place-conseq` does not place a firing whose `exceptWhen` exception already holds, and
  such a firing left no justification and nothing in `jtms/blocked` — so a settle pass
  could not see it and the conclusion stayed suppressed after the block lifted. The same
  knowledge in the other order concluded it. The refusal is recorded as `[rule handle,
  bindings]`, capped at 4096 entries per rule. `docs/exceptions.md`.
- **Five order-independence repairs.** `contradictions` names the same side of a clash
  whatever order the two arrived in; the two settle sweeps sharing one exposure-instance
  budget walk their moved region in content order; `query` with `{:proof? true
  :portfolio? true}` returns each answer once; `negation-nogoods` writes with a
  compare-and-set; and the node engine's inline join plans with the `:est-override`
  belonging to its registry leaf.
- **A forward rule fires on a claim argument-position preservation licenses**, so
  `sentexes-matching` and `ask` stop disagreeing about the same knowledge.
  `(argPreserving largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, which `ask` reached while the fixpoint fired only
  on the claims that were written — so the conclusion it never drew had no `why`, no
  retraction path and no way to be an antecedent. The join contributes the handles the
  inherited claim was read from, so retracting any of them withdraws the conclusion. One
  asymmetry is left: a justification confers the weakest class it rests on, so a
  `:monotonic` claim declared preserved by a `:default` declaration draws a `:default`
  conclusion. `docs/inherit.md`.
- **A head-existential rule carrying an aggregate mints a ground witness.**
  `skolem/frontier-vars` subtracts a post-join literal's output, so the Skolem NAT no
  longer takes a variable into its argument list.
- **An open `disjoint` goal is enumerated from the declarations rather than from the
  vocabulary.** A separation convicts two subtrees, so the answers are the subtypes of
  what a *visible* declaration names and the cost is the answer's own size; 0.2.0 asked
  `taxonomy/disjoint?` once per type, and once per **pair** with both arguments open. On
  4,000 types carrying one separation that is 15.4 ms to 0.13 ms with an argument bound —
  flat where it grew linearly — and at 1,000 types the two-variable goal goes from 2.5 s
  to 4 ms. `lein perf`'s `disjoint-enumeration` check is the claim.
- **A definitional clash is arbitrated from a context that can see both halves.** The
  checks are scoped to the context they are asked in, so a pair whose halves sit either
  side of a `genlCx` edge was answerable from exactly one of the two, and only when
  that half was the one the settle moved. `settle/clash-askers` runs the check from the
  candidate's own context and from the maximal common descendant of it and each context
  holding a sentex it could pair with; nothing is widened.
- **A pair per opposing sentex, not per opposing type.** One sentence stated in a general
  context and again in one that sees it is two sentexes, of possibly different strength,
  and a claim that denies it denies both — where the checks named one handle each, so the
  content-first of the two was weighed and the other left believed beside content that
  contradicts it.

## 0.2.0 — 2026-08-03

**Not a drop-in upgrade from 0.1.0.** Several of the changes below refuse input
0.1.0 accepted or change an observable contract — each such entry is marked
**Breaking** — which is why this is 0.2.0 and not 0.1.1. Entries between here and
the 0.1.0 header are in it, newest first.

- **The argument roots are scoped by predicate** (`[:argument-root pred pos
  term]`), so a materialising join reads one literal's postings rather than
  wading through every functor's at a shared slot. An `[:argument-slot pos
  term]` roster, reference-counted off those postings, keeps the
  predicate-agnostic reads answerable as a union over the predicates present.
  The packed long has no room for a fourth key part, so the dense roots route
  the family to their boxed fallback. `index-layout-version` is **2**: an index
  written by 0.1.0 reads as `:layout-changed` and is rebuilt on first open —
  no action needed, but a large durable store pays a reindex for it.
- **Breaking: every handle-taking fn refuses a non-handle** (`:bad-handle`) —
  the vector `assert` returns for a conjunctive rule included, which 0.1.0's
  `retract!` silently answered with `{:removed-sentexes 0}`. `nil` stays a
  question with an answer (`in?` false, `why` `{:stored? false}`,
  `add-provenance` a no-op), and `check-edit` reports what `edit!` throws. `why`
  also takes `{:max-depth n}` (default 256), marks a capped branch
  `{:truncated? true}` instead of overflowing, and refuses bad opts
  (`:unknown-option`).
- **`close!` releases a durable KB's directory** without waiting for JVM exit,
  and `import!` is `export!`'s inverse. An unclean close still releases the
  lock and registry; the first component failure is rethrown after.
- **An `argIsa` / `interArgIsa` / `argGenl` refusal names its convicting
  declaration in content order**, not in whichever order retrieval enumerated.
- **The five sweeps run in CI** — dense TMS, incremental matcher, node query
  engine, its tacticians, reference retrieval — each failing-set-identical
  with the default it replaces. Nothing ran them before.
- **Breaking: `assert` refuses a non-map `opts`** (`:unknown-option`) —
  `(assert kb s ctx :monotonic)` stored a defeasible sentence in 0.1.0.
  `check` already reported the same request; the two agree now.
- **Breaking: `open-kb` recovers by default** (`:recover? :auto`). The old
  `:warn` default handed back a KB that answered wrongly from a reopened
  store. The cost moves to construction — O(records) on a populated store —
  and `{:recover? false}` defers it. `:warn` and `false` remain.
- **The public surface is six namespaces**, where it was one: `vaelii.core`
  plus thin shims `vaelii.client`, `vaelii.starter`, `vaelii.web`,
  `vaelii.serve` and `vaelii.cli` over the `impl` namespaces they front. The
  boundary is now what the docs said it was.
- **Breaking: `vaelii.client`'s `assert` and `assert-rule` are spelled bare**,
  without the `!` 0.1.0 gave them. A `!` marks a fn that destroys stored
  knowledge and neither does — both are additive, and `retract!` is what takes
  one back — so the client now spells them exactly as `vaelii.core` does. A call
  site writing `c/assert!` or `c/assert-rule!` no longer resolves.
- **A clash names the sentex that states the membership**, not one that merely
  entails it, under either retrieval strategy.
- **An auto-compaction queued for a closed store is dropped**, so the next
  open no longer replays it as a crash-interrupted compaction.
- **Breaking: error `:type` keywords are plain across the tree**
  (`:unknown-source`, not `:vaelii.impl.catalog/unknown-source`), and
  `open-kb`'s backend refusals carry one. Swept in the same pass: the settle
  re-check queue no longer drops entries queued by a concurrent thread, and
  `foreign/register` refuses with `ex-info` rather than an elidable `{:pre}`.
- **Leiningen 2.10 is the minimum**: `:preserve-eval-meta` needs it, and 2.9
  ignores the key silently.
- **Breaking: `POST /op` requires `Content-Type: application/edn`.** The type
  is not CORS-simple, so a browser must preflight and the daemon answers no
  CORS headers — which closes cross-site request forgery against a loopback
  daemon. A client that sent no content-type is refused; add the header.
- **Breaking: a request body over 16 MiB is refused** (413) before it reaches
  the heap; `VAELII_MAX_BODY_BYTES` adjusts the cap.
- **Breaking: DNS rebinding is closed on both servers.** Every route requires
  a `Host` naming the interface the server was started on. A request with no
  `Host` still passes (a non-browser client carries no ambient browser
  context); a reverse proxy or local alias sets `VAELII_ALLOWED_HOSTS`.
- **`+with-foreign` names a coordinate that exists**
  (`com.vaelii/vaelii-foreign`); the bare id it carried resolved nothing.

## 0.1.0 — 2026-07-31

The first release. What follows is the development log that produced it, newest
first; every entry below is in 0.1.0.

## 2026-07-30

- A declaration re-checks the exceptions it moves: `(symmetric P)`,
  `(transitive P)`, `(inverse P Q)` and the `argPreserving` forms change what
  may be concluded with no fact arriving; `(functional P)` sweeps the extent
  when it lands.
- An equality restates a fact for each reader rather than once for the KB, and
  is itself a re-check trigger for `exceptWhen`, `unknown` and census reads.
- A change feed: the region a settle already computes is handed to a listener
  instead of discarded.
- English in — a sentence read into candidates a person still has to accept.
- A qualitative relation two contexts entail together fires a forward
  rule; a believed negative reaches the wiring a positive does; "some context"
  means the union of what the readers answer.
- Three readers of one question agree over a cyclic hierarchy, and settle
  repairs the context ranking after reconciling belief as well as before it.

## 2026-07-29

- One front door for backward chaining: the four paths measured, then
  consolidated to two chainers behind one entry point with one dial. A proof
  of an ephemeral answer reads the way `why` does.
- The goal frontier's order is a policy measured on time-to-first-answer,
  `:ground-first` by default; the goal-stack chainer drives one solution at a
  time and level 7 streams its search.
- Foreign formats arrive as a classpath plugin, so a reader ships and retires
  without touching the engine.
- A constraint declaration may name a second sentex it must not weigh, and a
  depth bound has no default because there is no defensible one.

## 2026-07-28

- `lein gate`: lint, the suite, and the scaling claims, measured and failed on
  rather than asserted; five checks added for costs that grow with what they
  must not.
- The columnar index is written once and mapped back; backend names read
  `<records>-<index>`, all seven.
- A literal's matches are remembered and retired on a clock; converging
  branches share one rule expansion; a third backward chainer whose state is
  a frontier.
- The naming invariants belong to the knowledge base, and the bulk door counts
  what it skips.

## 2026-07-27

- Aggregation: a count is a query operator, and a firing that rests on one is
  maintained like any other — gated by a permutation test. A census counts
  distinctness through the representative the asking context elects.
- `argIsa` entails as well as constrains, behind a toggle, retroactively too.
- A definitional clash names a second sentex, making it a nogood, and the
  arbitrating sweep asks the taxonomy rather than a fixed functor set.
- The qualitative network lives on the knowledge base and warm-starts off its
  own previous answer; a violation ledger is a claim about one KB.
- The browser draws term shapes, composes English at three densities, and
  gained `lein browser`; OpenCyc loading went from 378s to 277s.

## 2026-07-26

- Contexts got a vantage: every taxonomy supporter records the context it
  asserts from, so disjointness, matching fan-out and settle all read only
  what the asking context can see.
- A firing names the `genl` edges it subsumed through — belief and strength
  run through them like any antecedent, checked against all 24 orderings.
- Records and index became two independent choices, plus an overlay backend:
  a private writable fork over a shared read-only base.
- A knowledge base is readable before it finishes loading, and the suite runs
  on every backend from one script.

## 2026-07-25

- OpenCyc, read and re-expressed: every constant given back its role, 1.1M
  sentexes in the engine's own format, on the machine that reads it. Nothing
  of Cycorp's is redistributed.
- An export format no rename can break, with `xz`, an importer, and an oracle
  comparing two knowledge bases; a dump lands every record at its handle.
- Qualitative spatial and temporal reasoning: RCC-8 and three more spatial
  algebras, Allen intervals, durations and instants, behind one glue.
- One gap written in two units is one constraint: both spellings snap to the
  tolerance grid, and a unit given two conversion factors is its own base.
- A knowledge-base catalog with a browser that switches between KBs;
  `inherit` declared rather than assumed; definitional checks reach every
  term; `argGenl` constrains one level up.

## 2026-07-24

- The scale program opened with measurement first: the truth-maintenance
  wall, a posting-encoding bake-off on a real corpus, and a rule audit.
- Three dense representations, each measured: `:memory-dense` integer
  postings, the `:memory-columnar` int-token trie with CSR compaction (3.18x
  whole-index), and a bitmapped TMS behind a protocol.
- The disk side got dense too: positional record reads with a hot-record LRU,
  a positional frame codec, tokenized bodies over a durable dictionary — all
  behind a backend parity gate.
- Recursive forward chaining went O(n³) → O(n log n); a term roster
  enumerates vocabulary in O(terms).
- The web browser was hardened — escape by default, guard the parse, bind
  loopback, refuse cross-origin writes — and a pluggable LLM proposes edits
  and never applies them.

## 2026-07-23

- A performance review, its findings fixed: the disk log records operations
  rather than grown values (killing an O(N²) write amplification), settle
  keeps a coincidence set, re-checks narrow to the moved cone, region
  fixpoints became semi-naive worklists, compaction is copy-on-write.
- Symbolic equational reasoning: pure oriented rewriting with full
  Knuth-Bendix orientation, order-independent normalization, and
  non-confluence surfaced; `rewriteOf` extended over predicates and types.
- An operational surface: an EDN-over-HTTP daemon, a command-line driver, a
  thin client, and a browser that attaches to a daemon — with the public API
  closing every hole the browser tracked.
- Existential rule heads with deterministic skolemization; an occurs check;
  closures answered on demand; the record split into atomic and rule shapes
  with interned symbols; a bulk-load fast path.

## 2026-07-22

- Negation as failure, at top level and in antecedents, with block, sweep and
  revive, and stratification to keep it sound.
- Resource-bounded anytime inference with qualitative cost tiers and a
  cost-ordered forward-chain join; `ask-within` normalizes its goal.
- Reification of non-atomic terms; structural subterm indexing,
  oracle-proven, then on by default.
- The storage seam: index logic onto one key-value protocol, an in-memory
  backend, then the on-disk substrate — files, lock, durability, record
  store, index store.
- The index benchmark harness, and a per-handle provenance side map.

## 2026-07-21

- `exceptWhen` canonicalized into the record, blocking excepted conclusions
  with only reachable firings re-checked; its query reified the way a fact
  is.
- Equality landed: the closure, the `different` prover, a specification
  suite, and wiring into assert; stratification is checked on edge change.
- The engine split out of one namespace into five, and the knowledge base
  restructured into a layered tree loaded on start.
- `assumptionRules` with persistent solve and labeling contexts, proven on a
  sudoku.
- Retrieval got sharper: argument roots, multi-column narrowing, predicate
  subsumption, set-algebra retrieval, an opt-in incremental matcher.
- Truth-maintenance mutations are atomic; lint arrived.

## 2026-07-20

- Canonical rule form — canonical variables with a varmap, literal order,
  comparison direction — so rules alike up to renaming share one handle.
- The eight-level lookup-to-query stack, lazy throughout, with a browser page
  showing which level answered.
- Order independence and locality pinned as invariants: region-local
  relabelling, belief-following closures, content-keyed tie-breaks.
- The answer-set layer wired to the edge-solver seam, with a labeling
  materialized as a context; the defeasible layer made sound, six bugs
  pinned as failing tests first; `exceptWhen` began as a failing suite.
- Everything but `core` moved under `vaelii.impl.*`; `!` reserved for
  irreversible operations; tests became net-neutral, and a second concurrent
  run fails fast rather than corrupting the first.

## 2026-07-19

The first day: a contextualized common-sense knowledge base with a trie
index, inference and truth maintenance.

- Sentexes — a sentence plus the context it holds in — stored as records
  behind protocols with nippy serialization; rules are sentexes too, with
  built-in transitivity for types and contexts.
- Forward chaining with dependency-directed retraction, and a backward
  chainer; a non-monotonic TMS with strengths, soft prioritized
  contradictions, and a solver seam.
- An inverted term index, directed rules, disjointness, well-formedness
  checks, and a pluggable prover query engine; structural connectives
  canonicalize into the record; evaluable arithmetic.
- A web browser over the whole thing, over a starter ontology with every
  term documented.
