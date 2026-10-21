# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.29.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking: inference

- **A rule's consequent is stored as written, and only its antecedents are read through
  `functionCorrespondingPredicate`.** A forward firing mints a constant for each
  application of a `reifiable_function` its consequent names, with or without a
  correspondence, and a recursive consequent such as `(num (SuccFn ?x))` mints up to the
  chain's `:max-depth` per write. A consequent application whose arguments an antecedent
  names takes that antecedent's variable. A backward rule whose consequent names an
  application answers no goal over it: `prove` of `(grownIn (FruitFn AppleTree) ?o)`
  through `(implies (bears ?t ?o) (grownIn (FruitFn ?t) ?o))` answers nothing.
  [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* state such a rule forward (`set/forwardRule`): its firing mints the
  application and stores the conclusion over the constant, which the goal reads.
  *Breaks:* `assert` of a rule whose consequent names an application, `prove`, `query`

### Additive: ASP

- **`VAELII_CLASP_BIN` (or `-Dvaelii.clasp.bin`) names the executable the subprocess
  backend runs**, and the `clingo` executable serves in clasp's place: a machine with
  `clingo` alone, or `pip install clingo` behind a wrapper script, gets the edge solver
  without `clasp` on `PATH`. The solver install steps are per platform.
  [asp.md](docs/asp.md#getting-a-solver)
  *Migration:* none.

### Additive: browser

- **The sentex page lists the meta-sentexes naming the sentex and shows its provenance
  map.** `sentexes-naming` answers every stored sentex nesting `(sentexHandle h)`, with
  `{:believed? true}` to filter, and the daemon serves it.
  [web.md](docs/web.md), [api.md](docs/api.md)
  *Migration:* none.
### Breaking

- **`kb-integrity`'s default sweep reports stranded declarations and live rule
  clashes.** Two new categories run without `:categories`: `:stranded-declaration`, each
  believed `arg`, `genlArg`, `interArg` or `interArgEqual` declaration the audit context
  sees that names a position its predicate does not have, and `:rule-clash`, each pair of
  rules the audit context sees whose conclusions would contradict if both fired, where
  both rules chain and no `exceptWhen` handles the clash. A KB holding either now sweeps
  `:gap` where it swept `:audited`. [integrity.md](docs/integrity.md#what-a-rule-clash-finding-means).

  *Migration:* fix the finding, or pass `:categories` naming the categories to run.
  *Breaks:* `kb-integrity`

### Additive

- **Taxonomy coverage, stranded declarations and rule clashes are `kb-integrity`
  categories, implemented once.** The three checks move out of `vaelii.impl.quality` into
  `vaelii.impl.integrity`, which reports them as `:stranded-declaration`, `:rule-clash`,
  and two review-only categories: `:taxonomy-island`, each edged type node the audit
  context sees that does not reach the found root, and `:rule-clash-review`, each clash
  pair with a `set/inertRule` (marked `:inert true`) or one a stated exception handles
  (`:excepted true`). `kb-quality`'s `:taxonomy`, `:declarations` and `:clashes` keys,
  `quality-report`, the `:kb-quality` and `:quality-report` daemon ops and `lein cli
  quality` answer as before, computed by the same code over the whole KB.
  [integrity.md](docs/integrity.md), [quality.md](docs/quality.md).

### Fix: answers

- **A forward rule concluding `equals` or `sameAs` over applications of a
  `reifiable_function` that have no constant yet mints them and stores the equality**, as
  `assert` of the ground sentence does. The firing dropped it as `:not-well-formed`, and
  `check` of the ground sentence reported the same problem `assert` does not raise.
  [nat.md](docs/nat.md#derivation-path)
  *Migration:* none.

- **`chain-report` counts a firing the forced-monotonic set holds void under `:void`, not
  under `:placed`**, and a rule whose every firing is void reads `:status :blocked`, where
  it read `:fires`. [exceptions.md](docs/exceptions.md)
  *Migration:* read `:void` beside `:placed` for the firings a rule made that support
  nothing.

- **A goal keeps a never-minted `Quote` or `Quasiquote` application as written** under a
  `(reifiable_function Quote)` declaration. `(different (Quote Bar) (Quote Baz))` holds for
  quotations stored only as a `modal_predicate`'s proposition, as the plugin's Cyc
  preamble stores them. [nat.md](docs/nat.md#read-path)
  *Migration:* none.

## 0.29.0 — 2026-10-23 — "Open applications read through `functionCorrespondingPredicate` and resolved under the reader's merges, `try-assert` refusing `:monotonic` complements and length clashes, query-only terms refused under `not`, closed-extent negatives re-checked in every arrival order"

| Area | Change |
|---|---|
| NATs | a rule's or goal's open application read through `functionCorrespondingPredicate`; an application resolved under the merges the reading or storing context sees; a corresponding fact reifies only where it is visible; a `modal_predicate`'s proposition keeps an application as written; `kb-integrity`'s `:uncorresponded-function`; a never-minted application answers by identity and congruence only; `natFormula` and `genlResult` teardown in any order |
| clashes | `try-assert` refuses a believed `:monotonic` complement (`:complement`), a fact or declaration breaking a length binding (`:arity`), an `irreflexive` or `anti_symmetric` tuple |
| well-formedness | `not` over a query-only term; `(not (or …))`; `set/monotonic` and `set/inert` inside a sentence (`:shape`); `:length-against-shape`, `:length-against-spelling`; misnamed literals inside `bravely`, `cautiously`, `forall`; an import skips a structurally ill-formed frame; `:not-stratified` over a closed-extent negative under `unknown`, `exceptWhen` or an aggregate body |
| vocabulary and reasoning | `prover`; `interArgEqual`; `exists-violations`; `argN` |
| order independence | closed-extent negatives re-checked under `unknown`, `exceptWhen` and an aggregate body; merges and restatements rest on their `genlCx` edges and equality paths; exceptions re-checked through `inverse`, `genlInverse` and `negates`; binder lists and nested NAF conjunctions canonical; argument-type mints and holds decided at the write that moves them |
| storage | `edit-records!`, `settle-record-edits!`; `lein cli upgrade --sync`; a sync adds a forward rule backward and turns it forward last; a rule whose direction changed survives a sync; a `VirtualMachineError` in a write's freeze propagates and marks the operation log |
| quality, koinii, browser | `kb-quality`'s rule-clash reading types applications and `genl` antecedents; `DisputeFn`; `/stats` reads `filed-violations` |
| performance | the settle's `genl`-end declaration refresh, stratification graph and reader state each read once; `violations` fetches held records in chunks |

Six entries are **Breaking** and nine are **Refusal**. Each carries its own `*Migration:*`
line, and the table indexes them by what a 0.28.0 caller changes.

| If your code… | Then |
|---|---|
| writes a rule or goal over an open application of a `reifiable_function` | declare `(functionCorrespondingPredicate F P)` for the function; read `kb-integrity`'s `:uncorresponded-function` |
| reads an application of a `reifiable_function` through a `sameAs` or `equals` its context does not see | state the merge where every reading context sees it |
| states a corresponding value in one context and reads the application in another | state the value where every reading context sees it |
| reads `believes` over an application through the asker's merges | state the identity in the agent's context |
| reads `kb-quality`'s rule-clash pairs | nothing: the dropped pairs are unreachable |
| names `(dispute …)` or reads its marks | name `DisputeFn`; expect one more notify and stale sweep per stored dispute |
| writes `(not (unknown S))`, `(not (thereExists …))`, `(not (forall …))` or `not` over another query-only term | write `S`, `(unknown (forall …))` or `(unknown (thereExists …))` |
| writes `(not (or A B))` as a fact | assert `(not A)` and `(not B)` |
| writes `set/monotonic` or `set/inert` inside a sentence | wrap the whole form or the `exceptWhen` query; call `assert-inert` for an inert sentence |
| binds an engine term's length, or a length against a term's spelling | drop the binding; rename the relation, or set `:naming :warn` |
| misnames a literal inside `bravely`, `cautiously` or a generated rule's `forall` | rename the functor the refusal names |
| imports a dump holding a structurally ill-formed frame | read `:refused` |
| calls `try-assert` to record a rebuttal of known-true content | call `assert` |
| calls `try-assert` with a fact or declaration that breaks a length binding or an `irreflexive` or `anti_symmetric` mark | call `assert` |
| concludes `P` from a rule reading a closed-extent `(not (P …))` | conclude off the cycle, or leave `P` open |

### Breaking: inference

- **A rule or a goal that names an open application of a `reifiable_function` is read
  through the function's `functionCorrespondingPredicate`.** `assert` stores `(implies
  (tagged (FruitFn ?t)) (ripe ?t))` as `(implies (and (fruitOf ?t ?f) (tagged ?f)) (ripe
  ?t))`, so both spellings are one handle and `why` shows the predicate form. `prove`
  asks `(grownIn (FruitFn ?t) ?o)` as `[(fruitOf ?t ?fruit) (grownIn ?fruit ?o)]` and
  binds the value variable in its answers, and `(equals ?x (FruitFn ?t))` reads as
  `(fruitOf ?t ?x)`. A function with several believed correspondences is read through
  each: the rule is stored once per correspondence, and the goal merges the answers.
  `(favoriteFood Pace (?fn AppleTree))` reads every declaration and binds `?fn`; a
  variable-functor compound in a `formula`-typed position stays a sentence pattern, and a
  rule holding a variable-functor application is stored inert. A rule naming a function
  with no believed correspondence is stored inert and goes live when one arrives; an
  open-application goal over such a function answers nothing. `query-status`, `abduce`,
  `search-tree`, `compare-tacticians` and `prove-within` refuse a goal whose declarations
  put the value at more than one position as `:shape`. A forward firing no longer mints a
  constant for an application its rule's head builds, and `kb-integrity` reports each
  function with no correspondence as `:uncorresponded-function`.
  [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* declare `(functionCorrespondingPredicate F P)` for each reifiable function
  a rule or goal applies; `(kb-integrity kb)` lists the functions whose rules are held.
  A goal that matched a stored compound through a variable functor names the function.
  *Breaks:* `assert` of a rule naming an application, `prove`, `query`, `kb-integrity`

- **An application of a `reifiable_function` resolves to its constant under the merges
  the reading or storing context sees.** With `(sameAs Apple Pomme)` in `CxUniverse`,
  `(likes Tom (FruitFn Pomme))` asked in a context that does not see `CxUniverse` is false
  where it was true; with the merge in the asking context, it is true where it was false.
  Two constants a merge joins are merged in each context that sees the merge, by an
  `equals` stated there, where only a merge in `CxUniverse` merged them.
  [nat.md](docs/nat.md#a-nat-resolves-under-the-readers-merges)
  *Migration:* state a merge where every context that should read the application under
  it sees it.
  *Breaks:* `ask` and every read entry point over an application of a
  `reifiable_function`, `assert` of one, `sameAs`, `equals`, `rewriteOf`

- **A corresponding fact reifies an application, and retires a placeholder, only where it
  is visible.** `(motherOf Muffet Mary)` stated in `CxStory` reifies `(MotherFn Muffet)`
  written in `CxStory` or below to `Mary`; a constant minted for it in `CxUniverse` is
  merged with `Mary` by a `(rewriteOf Mary K)` stated in `CxStory`, where it was stated in
  `CxUniverse`. A merge's restatement of a corresponding fact is no second value for a
  context that reads the two as one term, so the six sentences of a commutative
  correspondence merged in a child context mint 3 constants for every spelling, where 4
  of 8 spellings minted 4 and placed a repair equality in the parent.
  [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* state a value where every context that should read the application sees
  it; a value stated in `CxUniverse` reaches every context that sees `CxUniverse`.
  *Breaks:* `assert` of an application of a `reifiable_function`, `rewriteOf`

- **A `modal_predicate`'s proposition keeps an application of a `reifiable_function` as
  written.** `(believes Ann (likes Tom (FruitFn Apple)))` stores the application, where it
  stored the constant, and `believes` reifies it in the agent's context: the asker's
  `(sameAs Apple Pomme)` no longer answers `(believes Ann (likes Tom (FruitFn Pomme)))`, and
  an `equals` the agent holds does.
  [belief.md](docs/belief.md#where-the-barrier-sits-and-what-it-covers)
  *Migration:* state the identity in the agent's context when the belief should read
  through it.
  *Breaks:* `assert` of a `modal_predicate` sentence naming an application of a
  `reifiable_function`, `ask` of `believes` over one

### Breaking: quality

- **`kb-quality`'s rule-clash reading types an application by its function's `result` and
  the application's arguments by its function's `arg` declarations, at any depth, and
  types the first argument of a `(genl ?r P)` antecedent by `P`'s arity**, so it lists
  fewer unreachable `:disjoint` pairs. Four `TimeOfFn` rules added to the starter paired
  103 times, and pair 17 times with this reading; a rule over the specs of a binary
  predicate no longer pairs with every rule concluding a type no relation has, such as
  `person`. An application at a `quotedArg` position is read as a mention
  ([#169](https://github.com/vaelii/vaelii/issues/169),
  [#210](https://github.com/vaelii/vaelii/issues/210)).
  [quality.md](docs/quality.md#contradictions-in-waiting)
  *Migration:* none.
  *Breaks:* `kb-quality`

### Breaking: koinii

- **koinii's dispute lifecycle term is `DisputeFn`**, the spelling every other shipped
  function has. `dispute/dispute-term` returns `(DisputeFn (sentexHandle h) …)`, and the
  `disputeNotified` and `disputeStale` marks carry it
  ([#159](https://github.com/vaelii/vaelii/issues/159)).
  [koinii.md](docs/koinii.md)
  *Migration:* none for a new store. A store holding marks under `(dispute …)` reads
  those disputes as un-notified and not stale, so the notify and stale sweeps fire once
  more for each.
  *Breaks:* `dispute/dispute-term`, `(dispute …)`

### Refusal: naming and well-formedness

- **`assert`, `assert-inert`, `check` and `try-assert` refuse a `not` over a query-only
  term** (`unknown`, `thereExists`, `forall`, `bravely`, `cautiously`, the aggregates,
  `different`, `minCommonGenl`, `maxCommonSpec`, `totalDuration`, `overlapDuration`), at
  any depth of `not` and under `ist` or a rule wrapper, with the bare term's own
  `:not-well-formed` refusal; a rule antecedent or `exceptWhen` query holding `(not
  (unknown …))`, `(not (thereExists …))` or `(not (forall …))` at any depth is refused the
  same way, and an import skips it. Each was stored as a fact no prover reads, or as a
  condition that never held, so an exception written this way blocked nothing; an `or`
  inside it went unchecked, and a `(not (forall …))` threw an untyped
  `IndexOutOfBoundsException`. [naf.md](docs/naf.md)
  *Migration:* a stored `(not (unknown S))` states that S is derivable: ask S, or assert S
  if it is a fact. Write `(unknown (forall …))` or `(unknown (thereExists …))` for the
  closed-world reading.
  *Breaks:* `:not-well-formed`, `unknown`, `forall`

- **`assert`, `assert-inert` and `check` refuse a `(not (or …))` fact**, at any depth of
  `not` and under `ist` or a rule wrapper, as `:not-well-formed`. It was stored as one
  literal, so no goal over its disjuncts matched it and the literals inside it went
  unchecked. `import!` skips such a frame, and a bare `(or …)` frame, under `:refused`. A
  bare `(or …)`'s refusal message begins `not well-formed: `.
  [canonicalization.md](docs/canonicalization.md#where-or-cannot-go)
  *Migration:* a stored `(not (or A B))` means "neither A nor B": assert `(not A)` and
  `(not B)` instead. A dump holding one imports without it, counted in `:refused`.
  *Breaks:* `:not-well-formed`, `not well-formed: `, `:refused`

- **`assert`, `check` and `try-assert` refuse `(set/inert S)`, and refuse
  `(set/monotonic …)` anywhere but around the whole sentence or an `exceptWhen` query**
  (an antecedent, a consequent, a query, under `not`), as `:shape`. `assert-inert` refuses
  both wrappers, and a whole-form `(set/monotonic S)` beside `{:strength :default}` is
  refused. Each was stored at `:default` with the wrapper as its functor, which no query
  matches. [kbs.md](docs/kbs.md)
  *Migration:* write the wrapper around the whole form or the `exceptWhen` query, call
  `assert-inert` for an inert sentence, and state a strength once.
  *Breaks:* `set/inert`, `set/monotonic`, `:shape`

- **`assert`, `check` and `try-assert` refuse a length binding the sentence alone shows
  is wrong.** A binding of an engine term (`arity`, `arityMin`, an arity class,
  `variable_arity`) that admits no length the term's `:shape` takes, or fewer lengths
  than the shape takes, is refused as `:length-against-shape`: `(arity genl 3)`,
  `(arityMin partition 4)`. A binding that gives a type-spelled term a length other than
  1, or a camelCase term the length 1, is refused as `:length-against-spelling` under
  `:naming :strict`, logged under `:warn` and stored under `:off`: `(binary_predicate
  warm_blooded)`, `(arity parentOf 1)`. A bare lowercase word takes any length.
  [naming.md](docs/naming.md#a-length-binding-is-held-to-the-spelling)
  *Migration:* drop a binding of an engine term; rename a relation whose binding the
  spelling check refuses, or set `:naming :warn`.
  *Breaks:* `:length-against-shape`, `:length-against-spelling`, `arity`, `arityMin`

- **`assert` refuses a misnamed literal inside `(bravely S)`, `(cautiously S)` and a
  `forall` in a generated rule's antecedent**, as `:naming` under `:strict`. The naming
  check read each wrapper as one literal and stored the misnamed functor inside it, where
  no read written to the naming convention matches it.
  [naming.md](docs/naming.md#literals-wrappers-and-arguments)
  *Migration:* nothing for a caller whose content follows the naming convention; content
  that throws on re-assert renames the functor the refusal names.
  *Breaks:* `bravely`, `cautiously`, `:naming`

- **An import skips a frame `assert` refuses as `:not-well-formed` for its shape alone**
  (an individual or a self-loop in `genl`/`genlCx`/`disjoint`, a non-integer `arg`
  position, `unknown` as a fact, an inline `exceptWhen` over a fact, a non-finite measure
  magnitude) and counts it in `:refused`. Such a frame stored, and `(disjoint dog dog)`
  threw an untyped "Duplicate key" out of the import. The checks that read stored content
  still do not run on an import. [naming.md](docs/naming.md)
  *Migration:* a dump holding such a frame imports without it.
  *Breaks:* `import!`, `:not-well-formed`

### Refusal: clashes

- **`try-assert` refuses a sentence whose complement is believed `:monotonic`** from the
  context, stored or entailed through `:monotonic` `genl` edges, as `:definitional-clash`
  with `:violation :complement` and the complement in `:clashes-with`. It stored the
  sentence, the settle defeated it, and neither `conflicts` nor `contradictions` listed
  the pair, so the caller held a handle to a sentence the KB did not believe. A denial of
  a believed forced-monotonic literal is refused at either written strength; a
  forced-monotonic positive is not refused. A `:default` complement or edge refuses
  nothing, and `assert` stores every rebuttal as before.
  [api.md](docs/api.md#refusing-a-clash) ([#211](https://github.com/vaelii/vaelii/issues/211))
  *Migration:* a caller that records a rebuttal of known-true content calls `assert`.
  *Breaks:* `try-assert`, `:complement`

- **`try-assert` refuses a fact or a declaration that breaks a length binding or an
  `irreflexive` or `anti_symmetric` mark.** A fact whose length breaks its relation's
  length binding is refused as `:definitional-clash` with `:violation :arity`, the binding
  in `:detail` and its grounds in `:opposing-handles`; a self tuple of an `irreflexive`
  relation, or the converse of a believed tuple of an `anti_symmetric` one, as `:violation
  :irreflexive` / `:anti-symmetric`, where the relation is marked or below a marked one
  through `genl`. A converse whose two symbols merge under a `:monotonic` write is stored.
  A length binding, a `genl` edge, or a `:monotonic` metatype membership or edge whose
  length breaks the length of stored tuples is refused as `:violation :arity` with each
  length and its stored count in `:detail :shapes`; an `except` of a length binding as
  `:violation :arity`; and an `irreflexive` mark over believed self tuples of its
  predicate or one below it as `:violation :irreflexive`, with the tuples in
  `:clashes-with`. `assert` stores each as before: the tuples held inert, the self tuples
  placed, the length bound under the except. [api.md](docs/api.md#refusing-a-clash)
  *Migration:* a caller that records such a fact or declaration on purpose calls `assert`.
  *Breaks:* `try-assert`, `:arity`, `:irreflexive`, `:anti-symmetric`

### Refusal: stratification

- **A rule concluding `P` whose `unknown`, `exceptWhen` or aggregate census body reads a
  closed-extent `(not (P …))`, directly or through a cycle, is refused** with `:type
  :not-stratified`, in either arrival order: the grant can be the refused write. A
  negative nested in `unknown`, in `thereExists` under `unknown` or in an `exceptWhen`
  query was a negative edge on `not` only, so the rule stored while the same literal as an
  antecedent was refused.
  [naf.md](docs/naf.md#stratification-from-both-arrival-orders)
  *Migration:* conclude off the cycle, or leave `P` open.
  *Breaks:* a KB holding such a rule beside a `closed_extent_predicate` or
  `closedExtentForArg` grant on `P`

### Additive: vocabulary and reasoning

- **`prover` builds a prover from plain fns**, the value `add-prover` registers, so a
  caller needs nothing under `vaelii.impl`. A spec giving `:solve-with-support` with
  `:support-functors` and `:support-sources` names the handles each answer was read from:
  a forward rule fired on the answer is withdrawn when one of them is retracted, and a
  fact on a source re-joins the rule whichever arrived first. A malformed spec, or a
  reading or an answer outside its domain, is refused with `:unknown-option`.
  [inference.md](docs/inference.md#what-a-computed-answer-rests-on)
  *Migration:* none.

- **`(interArgEqual P n v m U)` types argument `m` of the `P` sentences whose argument `n`
  is the value `v`**, a number, string, keyword, boolean or character. It derives the type
  as `arg` does, convicts under the constraint-only reading, and `try-assert` refuses a
  separated argument from both arrival orders. CxUniverse types a `closedExtentForArg`
  grant's predicate by the grant's position, so `try-assert` refuses a grant past a stated
  arity, which closed nothing ([#175](https://github.com/vaelii/vaelii/issues/175)).
  [argtypes.md](docs/argtypes.md#a-type-conditioned-on-an-argument-value-interargequal)
  *Migration:* none; a stored grant past its predicate's arity is reported in `conflicts`.

- **`exists-violations` audits a `predAllExists`, `predExistsAll`, `predExistsInstance`
  or `predInstanceExists` declaration on demand**, returning the members of the universal
  collection, or the fixed term, with no believed filler. `all-specified-violations` and
  `kb-integrity` audit every visible one beside the *Specified* declarations. Served as
  the `:exists-violations` op. [predall.md](docs/predall.md)
  ([#149](https://github.com/vaelii/vaelii/issues/149))
  *Migration:* a caller of `all-specified-violations` sees a key per *Exists* declaration
  with a violation.

- **`argN` is answered from how its formula is written.** `(argN ?t ?n (parentOf Tom
  Bob))` binds `?t` and `?n` to each position, 0 being the operator, and a quoted formula
  answers the positions of the form it names. A forward rule with an `argN` antecedent
  fires, and a backward one proves, once another antecedent binds the formula.
  [inference.md](docs/inference.md) ([#149](https://github.com/vaelii/vaelii/issues/149))
  *Migration:* none.

### Additive: storage

- **A batch of premise removals and rule direction changes applies to the records of a
  KB without belief, and one rebuild settles any number of them.** `edit-records!`
  deletes the removed records with their postings and the justifications resting on
  them, and writes each rule's new direction, with no check, no dependency sweep and no
  settle; it refuses a KB with belief (`:belief-built`) and an `except`, `defeat` or
  `exceptWhen` removal (`:record-edit-unsupported`), and takes no additions.
  `settle-record-edits!` then runs `recover` (or `reindex`), sweeps what the batches left
  unsupported, chains the rules turned forward and draws the argument-type mints the
  removals released. `edit!` runs a dependency sweep and a settle per batch, so a large
  batch of removals costs one settle per removal's dependents; the record edit costs one
  rebuild for every batch. [storage.md](docs/storage.md#editing-the-records-of-a-kb-without-belief)
  *Migration:* none.
  Test `edit-records-then-settle-believes-what-edit-believes`.

- **`lein cli upgrade --sync` brings a store's shipped contexts to what this engine
  ships**, one change at a time with a progress line per change on stderr, and reports
  `:sync {:added :removed :forwarded :refused}`. Under `--verify` the comparison runs
  before the sync. Without the flag `upgrade` reads the records and writes none. A
  step-by-step sync asserts each rule shipped forward as `set/backwardRule` beside the
  rest of the content, then turns each forward as an `:op :forward` change of its own,
  after every other change has settled, so an addition that sets off forward rules over
  the whole taxonomy no longer runs as one change, and each forward rule's chaining is
  its own reported step. `sync-each!`'s result counts them as `:forwarded`.
  [operations.md](docs/operations.md)
  *Migration:* a caller reading `sync-each!`'s result sees the new key.
  Test `a-forward-rule-lands-backward-and-is-turned-forward-after-the-content`.

### Fix: answers

- **A goal over an application of a `reifiable_function` that was never minted answers
  nothing, except by identity and congruence.** `(equals (FooFn Xa Xb) (FooFn Xc Xd))`
  answered `{}` through `ask`, `prove` and `query`, and so did `(different (FooFn Xa Xb)
  Zed)`; `(equals ?x (FooFn Xa Xb))` and `(genl (FooFn Xa Xb) ?y)` bound the variable to
  `nat/no-match`. `(equals (FooFn Xa Xb) (FooFn Xa Xb))` still holds.
  [nat.md](docs/nat.md#read-path)
  *Migration:* none.

- **A rule naming an individual a merge retires is restated under the representative** and
  fires on the facts restated under it. It fired on neither spelling. `sentexes-matching`
  for such a rule below the merge returns the restated rule.
  [equality.md](docs/equality.md#interactions)
  *Migration:* a rule stored beside such a merge before this release stays unrestated until
  the merge is retracted and asserted again.

- **`ask` answers a denial from a reached or inverse denial.** `(not (P a b))` answers
  from a surviving denial reached along a `transitiveInArg` or `transitiveInArgInverse`
  position, as `(P a b)` answers from a reached claim, and an `exceptWhen` over such a
  denial holds whichever sentence arrives last; a membership separated across a
  `:default` `genl` edge answers no denial. `(not (P x y))` answers from `(not (Q y x))`
  under a `:monotonic` `(inverse P Q)`, and so does the denial of each spec of `P` over
  known-true `genl` edges. [inherit.md](docs/inherit.md#reading-it-back),
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* none.

- **`ask` of a stored sentence whose formula argument carries a variable answers instead of
  throwing `StackOverflowError`.** `(ask? kb '(defnNecessary negative_integer (and
  (integer ?x) (lessThan ?x 0))) 'CxAbstract)` threw at every context for each of the
  starter's eight `defnNecessary` and `defnSufficient` sentences, and so did any goal
  spelt with a variable name the stored formula also uses. A literal-cache read now
  answers what the uncached read answers.
  [inference.md](docs/inference.md#the-literal-cache-vaeliiimplliteral-cache)
  *Migration:* none.

- **The joint reading answers what each route gives.** `:post-hoc` answers a joint read
  through a `genl` edge stated in two contexts as `:fan` does, both when no reader sees
  the two together and when a reader excepts the more general one; it placed the answer
  by one route and dropped the others, or answered `[]`. A `CxInference` or
  variable-context read of a computed answer whose ingredients sit in a context no
  `genlCx` edge touches answers, witnessed by that context, for the provers the ingredient
  table names. It answered `[]`, or unscoped with no witness when no edge existed at all,
  so an unrelated edge changed the answer. A subgoal prover or `different` rests on no
  stored fact of its own and adds no reader.
  [contexts.md](docs/contexts.md#cxinference-the-joint-reading)
  *Migration:* none.

- **`handle-of`, `sentexes-matching` and `why-not` find a `forced_decontextualized_predicate`
  fact where `assert` stores it.** Given a `genlCx` edge, bare or as `(ist CxA S)`, at a
  named context other than CxUniverse, they read that context and answered nil or `[]`
  while the edge was stored in CxUniverse.
  [contexts.md](docs/contexts.md#forced_decontextualized_predicate-a-canonical-home-in-cxuniverse)
  *Migration:* a caller that read an empty `sentexes-matching` at the asserting context as
  "not stored here" reads the record's `:context`, or reads at `?ctx`.

- **A closed-extent negative answers in its conjunct order and under a hidden grant.** A
  `(not (P ?y))` conjunct under a closed-extent grant on `P` runs after the conjuncts that
  bind `?y`, in a `thereExists`, `unknown` or `forall` query, a `prove` or `query`
  conjunction and a backward rule's antecedents. Run first, it was asked open and
  declined: `(thereExists ?y (and (not (asleep ?y)) (childOf Bob ?y)))` answered false
  while Bob had a child not asleep. Under a defeated or excepted grant, an `unknown` or
  `exceptWhen` guard over a `(not (P …))` the grant answers follows `ask?` of its
  condition at each reader: the guard defeat rests on the grant, or on the stored
  negative, that answers the literal, and `why` lists that grant or negative in
  `:because`. [naf.md](docs/naf.md#under-the-grant-a-negative-antecedent-is-naf)
  *Migration:* a forward rule stored before this release keeps its firings until it is
  retracted and asserted again.

- **`assert`, `check` and `try-assert` read a whole-form `(set/monotonic S)` as `S` at
  `{:strength :monotonic}`**, as the text KB loader does, inside an `ist` too, and
  `handle-of` answers `S`'s handle for it. `assert` stored the wrapper as the sentence's
  functor at `:default`. [kbs.md](docs/kbs.md)
  *Migration:* a KB holding such a record keeps it;
  `(sentexes-matching kb '(set/monotonic ?s) '?c)` finds one to retract and assert again.

- **A rule whose literal carries an `or` in an argument slot is not refused.** `(implies
  (and (p ?x) (not (likes ?x (or A B)))) (r ?x))` was refused as "or cannot stand under
  not", as was the same argument under `unknown`, `thereExists` or an aggregate body, in a
  conclusion or in an `exceptWhen` query, while the same literal stored as a fact.
  [canonicalization.md](docs/canonicalization.md#where-or-cannot-go)
  *Migration:* none.

- **The naming check reads the wrappers it names.** `nm/problems` reads an `exceptWhen`
  query's literals inside its `(set/monotonic …)` wrapper and reports a misnamed one
  there, where `assert` refused it already. A generator whose generated rule is wrapped in
  `set/solveRule` is not refused as `:naming` for the wrapper's spelling. A quoted
  `(forAll …)` form is classified by its operands like any atomic sentence; `forall` is
  the quantifier. [naming.md](docs/naming.md#literals-wrappers-and-arguments)
  *Migration:* none.

- **The interval network answers for its reader.** A read under a rebound
  `provers/*quantity-tolerance*` answers that tolerance's network, where it answered the
  network last built under another tolerance until the next write. A forward rule on a
  calculus predicate fires in a context that holds only facts on a sub-predicate of one,
  or that meets the `genl` edge making it one; it fired nowhere while `ask` there held.
  [qcn.md](docs/qcn.md#a-network-can-have-a-second-reader)
  *Migration:* none.

- **`functional-at-instant-violations` reports a clash at an `(InstantFn …)` moment an
  `instantBefore` link names.** It read only `time_point` members, which a structural term
  never is. [time.md](docs/time.md#functionality-at-an-instant)
  *Migration:* none.

### Fix: order independence

- **A closed-extent negative is re-checked whenever what answers it moves.** A negative
  inside an `unknown` antecedent, an `exceptWhen` query or an aggregate's census body is
  re-checked when a member of its predicate, a `closed_extent_predicate` /
  `closedExtentForArg` grant on it, or a `negates` or separation declaration that denies
  it, or the denying fact, arrives or leaves after the rule; the rule kept the answer
  computed at its firing. A firing over a closed-extent negative antecedent is re-decided
  when the grant is defeated, excepted or suspended, not only when it is stored or
  retracted. Retracting a grant withdraws the firings that read its negative as negation
  as failure, unless a stored negative answers the literal, and no longer releases the
  firings it refused. [naf.md](docs/naf.md#under-the-grant-a-negative-antecedent-is-naf),
  [aggregate.md](docs/aggregate.md#maintenance-when-the-aggregate-is-a-rule-antecedent)
  *Migration:* a rule stored before this release is re-checked once the grant is
  retracted and asserted again.

- **A merge and a restatement rest on the edges and equalities they were drawn over.** A
  `functional` or `anti_symmetric` merge drawn through `genlCx` edges is withdrawn when
  one of those edges is retracted, and drawn again where another path survives; it stood
  in the orders where the merge arrived before the edge. A sentex a merge restates is
  withdrawn when an equality on the chain of merges it was restated over, or a `genlCx`
  edge its reader sees the original through, is retracted, and restated over a path that
  survives; it stood on any one merge touching the same term.
  [equality.md](docs/equality.md#a-late-genlcx-edge-is-a-third-arrival-order)
  *Migration:* a merge or restatement stored before this release keeps its justification
  until one of its facts, merges or declarations is retracted and asserted again.

- **A `different` antecedent reads the merges and indeterminacy declarations the
  conclusion's context sees.** A merge only an unrelated context sees no longer withdraws
  the firing, and a context below the placement that sees one reads a guard defeat of the
  conclusion. `chain-report` lists a firing refused at its placement as a `:naf` refusal.
  [predall.md](docs/predall.md#a-different-guard-is-re-checked-not-supported)
  *Migration:* none; `recover` re-fires every watched rule.

- **An exception is re-decided through every channel that answers it.** An exception
  answered through an `inverse` or `genlInverse` partner of its predicate is re-decided
  when a fact on the partner arrives or leaves, and a late `genlInverse`, `symmetric` or
  other declaration on the predicate re-decides a `(not (P …))` exception; the fan read
  `genl` edges only. A `(not (P …))` condition is re-decided when a tuple of a predicate a
  `negates` declaration says negates `P` arrives or leaves, and when the `negates`
  declaration or a `genl` edge under such a predicate arrives after the rule. A condition
  holding a `(not (forall …))` is re-decided when a `genl` edge moves a predicate inside
  the frame; the negated-frame set spelled the quantifier `forAll`.
  [exceptions.md](docs/exceptions.md#five-channels-a-declaration-or-a-fact-reaches-an-exception-through-sideways)
  *Migration:* none.

- **An argument-type mint or hold is decided at the write that moves it.** A length
  binding that arrives after a declaration minted in its type removes the mint at that
  write: `(binary_predicate t)` after `(arg rel 1 t)` and `(rel Rex Mary)` left `(t Rex)`
  stored, and believed until the next write's settle. The same holds for a `genlArg` edge
  mint and an `argArg` mint. A fact held inert under a declaration is released when a
  `genl` edge above its declared type releases it: `(vneeds 5)` under `(arg vneeds 1
  vdog)` stayed held after `(genl vmid vk)` placed `vdog` under `integer`, where the edge
  stored first left it believed.
  [argtypes.md](docs/argtypes.md#four-directions-or-belief-depends-on-arrival-order)
  *Migration:* none.

- **A rule over an open application, or holding a variable-functor application, keeps the
  firings the last arrival allows.** A rule held by an open application of a
  `reifiable_function` keeps no firing under `VAELII_ASSERTIVE_ARG_TYPES=0` when the
  declaration arrives after the rule fired. A `formula`-typed declaration arriving after a
  rule that holds a variable-functor application releases the rule, and the rule is held
  again, keeping no firing, when the declaration leaves: `(arg holdsIn 2 sentence)` stored
  after `(set/forwardRule (implies (holdsIn ?c (?p Rex)) (heardOf ?c ?p)))` left the rule
  firing nothing over the facts stored before it. A `genl` edge putting a declared type
  under `formula` moves the rule the same way.
  [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* none.

- **A reified NAT constant leaves the store in any retraction order.** A constant whose
  function declares `genlResult` is collected when its last use is retracted, whether the
  declaration arrives before or after the mint: the `(predicate K)` the argument-type
  entailment draws off the materialized `(genl K T)` edge counted as a use and kept it
  ([#225](https://github.com/vaelii/vaelii/issues/225)). Retracting a `natFormula` map
  before its `reifiable_function` mark no longer leaves the constant's uses spelled
  `nat/K`: under a believed mark the constant is minted again, and with the mark gone each
  use names the application ([#216](https://github.com/vaelii/vaelii/issues/216)).
  [nat.md](docs/nat.md#rename-and-remove--keeping-the-11-invariant)
  *Migration:* none.

- **A `thereExists` or `forall` binder list and the conjunctions inside a NAF query store
  in canonical order.** A binder list stores in canonical order, a one-variable list as
  the bare variable. Two spellings of a rule that differ only in the order of the
  conjuncts inside an `unknown` or `thereExists` query, at any depth, a `forall`'s head
  and body included, or only in those conjuncts' variables, store as one handle, and the
  conjunctions inside an `exceptWhen` exception's conjuncts are ordered the same way.
  Deferred literals keep their written order, which decides evaluation.
  [canonicalization.md](docs/canonicalization.md#a-naf-conjunctions-conjuncts-sorted)
  *Migration:* a stored rule keeps the form it was stored in, and asserting another
  spelling stores a second handle; `export-text!` then `load-text!` re-canonicalizes a
  store. No shipped rule changes form.

- **A conjunction joining `(t ?a)` on a type an argument declaration infers answers the
  same set in every conjunct order.** An open `(t ?x)` returns every individual a
  declaration types where no stored membership covers it: every declaration under
  `VAELII_ASSERTIVE_ARG_TYPES=0`, and `thing` and arity-bound types under the default
  reading. A usage spelled at a term the reader's merges retire types nothing, so `:fan`
  and `:post-hoc` return the same rows.
  [argtypes.md](docs/argtypes.md#the-open-membership-goal)
  *Migration:* none.

- **An `unknown` or `exceptWhen` guard is asked in the normal form of each reader below
  its placement.** With the rule `(tyc ?x) & (unknown (tya ?x)) => (tyb ?x)` and
  `(tyc IndC)` in CxA, and in CxB below it `(tya IndC)` and a functional pair that merges
  IndB with IndC, `(tyb IndB)` read true at CxB when the merge arrived after the rule and
  false when the rule came last. It now reads false at CxB and `(tyb IndC)` reads true at
  CxA in every order. The justifications still depend on the order: `(tyb IndB)` at CxB
  carries a `rewriteOf` justification from `(tyb IndC)` only when the merge arrives last.
  [naf.md](docs/naf.md#order-independence-and-the-re-check)
  *Migration:* none.

- **A forward rule whose `genl` or `genlCx` literal only its recursive literal binds stores
  one justification set in every arrival order.** In `(implies (and (genl ?a ?b) (reaches
  ?b ?c)) (reaches ?a ?c))`, the rule arriving after its facts, or an edge arriving last,
  joined the closure literal with both ends open over the stored edges alone, so the
  firing over a pair two edges apart was missing. The closure literal now runs after the
  recursive literal.
  [inference.md](docs/inference.md#a-genl--genlcx-antecedent-reads-the-closure)
  *Migration:* none.

- **A firing over a typed calculus predicate (`subintervalOf`) is re-decided when a
  membership or a `genl` edge moves what the predicate's declared argument types admit.**
  A firing whose typed antecedent the declared types no longer admit, and no believed fact
  states, is withdrawn. [qcn.md](docs/qcn.md#what-every-algebra-does-with-it)
  *Migration:* none.

### Fix: storage

- **A sync no longer loses a rule whose direction changed.** The plan compared rules by
  the form a file writes, direction wrapper included, so a rule held backward and shipped
  forward was an addition, which raised the one record to forward in place, and a
  retraction of that record after it: the rule was gone. One shipped backward over one
  held forward went the same way. A rule's direction is now read as a strength is: raised
  in place, or lowered by a retraction before the addition. A shipped `set/backwardRule`
  also compares equal to the unwrapped rule it stores as, so it no longer reappears in
  every plan.
  *Migration:* none. Test `a-rule-whose-direction-changed-is-one-record-raised-or-restated`.

- **An `OutOfMemoryError` or `StackOverflowError` while a write's frame is frozen
  propagates out of the write**, which does not run. The operation log takes no
  `[:unfreezable …]` mark, so the next open replays instead of rebuilding from the
  records. One thrown by a write after its frame was appended marks the log `[:vm-error op
  cls]`, so no replay re-runs the write the entry point rolled back.
  [storage.md](docs/storage.md#the-operation-log),
  [operations.md](docs/operations.md#after-a-crash).

### Fix: browser

- **A `/stats` load reads no held sentex and no convicted firing.** It counted and listed
  `violations`, which fetches every held fact and rule and every convicted firing from the
  record store, one round trip apiece on postgres. The card and the list are the filed
  ledger, read by the new `filed-violations`, and **Scan for held facts and rules** runs
  the `:inert-argument`, `:inert-rule` and `:forced-conclusion` entries as the `held`
  list's job. [web.md](docs/web.md#whole-kb-lists)
  *Migration:* none.

### Fix: performance

- **A settle builds each context's reader state once while nothing it reads moves.** A
  withheld-mint release rebuilt the state, scanning every forced-monotonic declaration's
  supporter contexts, for each belief read after each mint it wrote. The settle now keeps
  each frame across writes that move no defeat, except, conflict, declaration, stored
  rule, `genlCx` edge or except's or declaration's label: 40 mints beside 8,000
  declarations release in 71 ms against 5,815 ms. A frame's declaration check probes each
  declaration instead of building the set of every handle a stored defeat names, so a
  write beside n defeats on `memory-columnar` no longer costs O(n).
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion)
  *Migration:* none.

- **A settle reads the declarations below a moved `genl` end with many specializations in
  one pass.** For a moved type with more than 512 specializations, the argument-hold
  refresh tested every stored declaration by one reachability walk per declared type,
  again for each such type, and logged nothing. The refresh now reads every declaration
  once for all such types and walks the types above the declared types once, logs
  progress lines per moved type and per declaration, and a shutdown can stop an `assert`
  before each of them. A `genl` write's declaration presence checks read the per-kind
  declaration sets instead of building the union of every declaring predicate, which grew
  with the stored declarations. [argtypes.md](docs/argtypes.md)
  *Migration:* none.

- **The stratification checks of one write or one settle read each stored rule once.**
  Every `genl` mint's check read and sorted every rule its walk reached, one record read
  per rule, so on postgres a settle re-asking the mints of waiting declarations made one
  round trip per rule per mint. The rules' graph is now read once per write or settle and
  shared until a rule, a re-check posting, a closed-extent mark or an exception's belief
  moves. [exceptions.md](docs/exceptions.md#the-search)
  *Migration:* none.

- **A settle reads the separation and cover routes of a membership nogood without
  building a held type's supertype closure.** The routes read the second type's
  supertypes cut to the separable ones, where each placement of a queued membership built
  the whole closure. [taxonomy.md](docs/taxonomy.md#what-the-question-is-asked-of)
  *Migration:* none.

- **`violations` fetches the held sentexes' records in chunks and shares the conviction
  reads across one call.** Each call fetched every held fact and rule by one record read,
  one round trip apiece on postgres, and decided each conviction with reads of its own. The
  records are now hinted 1,000 at a time, and the reads no value or rule enters are made
  once per call: on the starter, 3,000 held value facts read in 92 ms against 533 ms, and
  3,000 held rules in 117 ms against 319 ms.
  [argtypes.md](docs/argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert)
  *Migration:* none.

### Internal

- **The shipped ontology states no exact-arity membership that a `:monotonic` metatype
  route entails.** The upper files drop 168 `(binary_predicate P)` and 5 `(unary_predicate
  T)` premises, and `CxTra.txt` drops 7 `(binary_predicate P)`. The engine stores each of
  the 180 in CxUniverse under an `arityClass` justification, so every relation's length,
  `describe`'s `:arity` and each exact-class answer in CxUniverse reads the same. `why`
  names the membership and the edges instead of a premise, and `sync!` over a store loaded
  from 0.28.0's files retracts the 180 premises.
  [taxonomy.md](docs/taxonomy.md#arity) ([#116](https://github.com/vaelii/vaelii/issues/116))

- **A declaration whose type an arity statement binds to another length records
  nothing.** The refusal record keeps no entry for it, and `recover` reads no
  declaration to rebuild one. When the type's own bindings move and its length admits
  one, the settle reads the stored declarations and facts naming the type and mints
  then. [argtypes.md](docs/argtypes.md)

- **`lein lint`'s `derived` check fails a `decide.arity` register row with no
  `:covered-by` perf check or probe**, and a `:covered-by` name no `lein perf` check or
  `perf-ab` probe carries. [caches.md](docs/caches.md)

## 0.28.0 — 2026-10-21 — "Ill-typed facts and rules stored inert, term kinds and arity policies forced-monotonic, a `:default` `genl` that does not contrapose, parthood and the example predicates restated, `:recover? :trust` by default"

**77 entries** — 28 Breaking, 0 Refusal, 25 Additive, 17 Fix, 7 Internal. A fact that
fails its argument type and a rule no term can fill are stored inert in every arrival
order, read back through `why-not`'s `:conviction` and `violations`' `:inert-argument`
and `:inert-rule`, and `try-assert` refuses them as `:definitional-clash`. Term kinds,
arity policies, comparators, `arg` and `exceptWhen` are forced-monotonic, a denial of a
forced-monotonic literal is believed until the literal is stored, and a `:default` `genl`
edge does not contrapose. `open-kb` defaults to `:recover? :trust`, the image format and
the index layout are 16, and a load syncs only with `:sync?`. The shipped ontology
restates parthood with `tangiblePartOf`, proper parthood and `subSituationOf`, renames
`termOfUnit` to `natFormula` and `metal` to `metal_stuff`, merges `CxComputing` and
`CxPerception` into `CxTra`, and writes examples as `(Quote S)`.

*Breaks:* `assert`, `check`, `try-assert`, `:arg-type`, `:arg-genl`, `:inter-arg-type`,
`:quoted-arg-type`, `:definitional-clash`, `violations`, `:arg-variable`, `handle-of`,
`watch`, `query`, `:arg-constraint-kind`, `bulk-assert-facts!`, `open-kb`, `recover`,
`lein cli upgrade`, `preview`, `ask`, `kb-quality`, `genl?`, `kb-integrity`, `why-not`,
`conflicts`, `contradictions`, `argue`, `exceptWhen`, `chain-report`, `ask?`, `prove`,
forward chaining over a preserved antecedent, `ask-within`, `prove-within`, `resume`,
`compare-tacticians`, `quoting_function`, `:quoting`, `state.nippy`, `index-entries`,
`:disk-log`, `:disk-snapshot`, `vaelii.browser.catalog/load-dir`,
`vaelii.browser.catalog/load-source`, `caches`, `set-cache-limit`, `:pinned-values`,
`publish!`, `:koinii/compression-pinned`, `:stale-index-records`,
`vaelii.impl.protocols/ImageStamping`, `index-stamp`, `belief-stamp`,
`:forced-conclusion`, `:off-roster`, recover step `:rosters`, derived-state event
`:roster`, `:unrostered-reader`, `:exempt-and-rostered`, `:unrostered-arm`,
`:family-roster`, `profile`, `termOfUnit`, `partOf`, `subintervalOf`,
`properSubintervalOf`, `partitionedByType`, `positiveExample`, `negativeExample`,
`borderlineExample`, `invokesTool`, `CxComputing`, `CxPerception`, `friendOf`,
`marriedTo`, `worksFor`, `parentOf`, `livesIn`, `metal`

## 0.27.0 — 2026-10-15 — "Arity clashes held inert and `:monotonic` class memberships stored, `predExistsAll` scoped universal-first, `:pg-snapshot` and `:recover? :trust`, `genlInverse` and `closedExtentForArg`"

**30 entries** — 3 Breaking, 0 Refusal, 9 Additive, 14 Fix, 4 Internal. A tuple that
breaks its functor's length is held inert at every context, and an arity clash reads from
`why-not`'s `:inert` and the `:arity` conflicts instead of a placed `defeat`; a
`:monotonic` metatype route stores the exact-arity class membership it binds under an
`arityClass` justification. `predExistsAll` puts the universal outside the existential,
and `PredExistsAllFn` and `predExistsAllPlaceholder` take the subject. `:pg-snapshot`
keeps the index and reasoning images over Postgres records, and `open-kb`'s `:recover?
:trust` installs an image written under other engine source. `genlInverse` reads through
`tax/signed-closure`, `closedExtentForArg` closes an argument's extent, and
`min-context-parents` and `max-context-children` read a context's nearest neighbours.

*Breaks:* `why-not`, `conflicts`, `believed?`, `sentexes-with-functor`, `why`,
`predExistsAll`, `PredExistsAllFn`, `predExistsAllPlaceholder`

## 0.26.0 — 2026-10-13 — "Upper ontology loaded into CxUniverse with a sync to the shipped files, one relation length read at every context, the `forced_monotonic_predicate` roster scoped to its readers, `time` and `situation` restructured"

**25 entries** — 6 Breaking, 0 Refusal, 4 Additive, 11 Fix, 4 Internal. Every file under
`resources/kb/upper/` loads into CxUniverse, the nine upper contexts CxCore through
CxTime are gone, and `vaelii.host.sync/sync!` locks CxUniverse's premises to the shipped
files. A relation's length reads the same at every context, a metatype membership binds
only at `:monotonic`, and a `forced_monotonic_predicate` declaration forces at the
contexts that see and believe it. `time` gains `uninterrupted_time` under a broad
`time`, `situation` is partitioned into `fluent` and `happening`, and `hollow` and
`spatial_event` are new. `violations` reads `:forced-conclusion` off the stored void
firings, a text KB spells an inert sentex `(set/inert S)`, and the index is at layout
14.

*Breaks:* `CxCore`, `CxAbstract`, `CxLife`, `CxMeasure`, `CxOrganism`, `CxReflection`,
`CxSociety`, `CxSpace`, `CxTime`, `vaelii.host.spindle`, `sync-spindle!`,
`spindle/shipped`, `seed/root-contexts`, `:spindle`, `CxCore.txt`, `CxUniverse.txt`,
`time`, `situation`, `fluent`, `initiates`, `terminates`, `causes`, `describe`,
`admitsArgnum`, `relation?`, `arity`, `arityMin`, `variable_arity`, `kb-integrity`,
`sentexes-with-functor`, `forced_monotonic_predicate`,
`forced_monotonic_between_predicates`, `has-prop?`, `violations`, `clear-violations!`,
`preview`, `index-entries`, `:disk-log`, `:disk-snapshot`

## 0.25.0 — 2026-10-11 — "Context NATs reified by position under `(result F context)`, the expression lattice in CxReflection, more placed contradictions and separations, `IndexStore` family methods and index layout 13"

**55 entries** — 14 Breaking, 4 Refusal, 11 Additive, 22 Fix, 4 Internal. Every ground
application in a context slot reifies to a `cx/` constant, and `(result F context)` in
CxUniverse replaces `context_denoting_function`. A `:monotonic` metatype membership binds
its member's arity, a membership beside a denial of a supertype is a `:supertype` nogood,
a firing a `:default` `exceptWhen` or `unknown` blocker blocks is stored with a guard
`defeat`, and `query-status` reads `:incomplete` over an open transitive goal.
CxReflection holds the expression lattice (`predication`, `closed_predication`,
`non_atomic_expression`), and `argArg`, `resultArg`, `try-assert`, `min-genls`,
`max-specs` and `sentex/closed?` are new. `IndexStore` reads and writes through seven
family methods at index layout 13, the reasoning image is at `format-version` 15, and a
request-named path over the wire is refused `:path-not-served` unless
`VAELII_REQUEST_PATHS=1`.

*Breaks:* `context_denoting_function`, `:context-denoting`, `assert`, `conflicts`,
`instance_relation_predicate`, `transitive`, `ask`, `ask?`, `sentexes-matching`,
`contradictions`, `exceptWhen`, `unknown`, `rule-firing-report`,
`transitiveInArgInverse`, `atomic_formula`, `atomic_sentence`, `relation_application`,
`at_least_binary_relation`, `at_least_ternary_relation`, `relation_type`, `:not-ground`,
`query-status`, `temporalDistance`, `qualitative-network`, `:export`,
`:path-not-served`, `VAELII_REQUEST_PATHS`, `:kb-diff`, `/kbs/load`, `/kbs/export`,
`IndexStore`, `p/index-rule`, `p/unindex-rule!`, `p/index-exception`,
`p/unindex-exception!`, `p/sentexes-in-context`, `p/count-in-context`,
`p/sentexes-with-term`, `p/terms`, `p/term-count`, `p/rules-by-antecedent`,
`p/rules-by-consequent`, `p/rules-with-exception-on`, `p/exception-rules`,
`p/exception-rule?`, `reads/stored-terms`, `reads/stored-term-count`,
`reads/as-stored-rules-by-antecedent`, `reads/as-stored-rules-by-consequent`,
`p/sentexes-with-arg`, `p/count-with-arg`, `p/unary-sentexes-with-arg`,
`reads/as-stored-with-arg`, `reads/stored-count-with-arg`,
`reads/as-stored-unary-with-arg`, `p/count-children`, `index-entries`, `:disk-log`,
`:disk-snapshot`, `disjointness-audit`, `vaelii-sandbox`, `/assert`, `abduce`, `genl`,
`disjoint`, `covering`, `partition`, `separating`, `disjoint_metatype`,
`sibling_disjoint`, `orthogonal`, `siblingDisjointException`, `arg`, `genlArg`,
`quotedArg`, `interArg`, `args`, `argsGenl`, `argAndRest`, `argAndRestGenl`,
`interArgs`, `interArgAndRest`, `is a value;`, `totalDuration`, `overlapDuration`

## 0.24.0 — 2026-10-07 — "Reified `contradicts` and `defeat` sentexes synced to KB, upper ontology improvements and more disjointness, indexing improvements"

**59 entries** — 8 Breaking, 1 Refusal, 11 Additive, 33 Fix, 6 Internal. A nogood is
stored as a `contradicts` sentex over `sentexHandle`s, with the `defeat` of its loser,
at the most general contexts that see its members and grounds, and an asserted `defeat`
is refused `:derived-only`. `arg`, `genlArg`, `interArg` and the covering and
homogeneity constraints derive the type they name and refuse no sentence on a
membership; `transitiveInArg` and `transitiveInArgInverse` swap names, a roster literal
keeps its written strength, and `orthogonal` states an overlap while
`siblingDisjointException` is the only separation-mark exemption. The upper ontology
divides `thing` by space, time and mass, renames `living_thing` to `organism` and gives
events a doer, inputs and outputs. The index is at layout 10, keyed by context with five
families added, the reasoning image is at `format-version` 11, and `open-kb :oplog?`,
`kb-integrity`, `relation?`, `direct-genls`, `direct-specs` and `separating-covers` are
new.

*Breaks:* `sentexes-matching`, `preview`, `why-not`, `belief-status`, `describe`,
`contradictions`, `conflicts`, `assert`, `genl?`, `isa?`, `genls`, `specs`, `disjoint?`,
`has-prop?`, `inverse-of`, `:disk-snapshot`, `transitiveInArg`, `transitiveInArgInverse`,
`check`, `check-edit`, `abduce`, `:arg-type`, `:arg-genl`, `:inter-arg-type`,
`defeat-class`, `props`, `ask`, `believed?`, `orthogonal`, `subsumption-status`,
`subsumption-statuses`, `disjointness-audit`, `caches`, `clear-caches`, `lookup`,
`sentexes-with-args`, `rules-by-consequent`, `index-rule`, `unindex-rule!`,
`index-entries`, `:disk-log`, `physical_object`, `spatial`, `abstract`, `artifact`,
`attribute`, `(disjoint substance artifact)`, `living_thing`, `(disjoint organism artifact)`,
`capability`, `(unary_predicate not)`, `(binary_predicate implies)`,
`(genl function relation)`, `(genl predicate relation)`, `(disjoint function predicate)`

## 0.23.0 — 2026-10-02 — "no definitional clash is refused, each reader decides a clash from its own view, and the definitional vocabulary is held known-true"

**78 entries** — 11 Breaking, 2 Refusal, 2 Additive, 63 Fix. `assert` refuses no
definitional clash (`disjoint`, `functional`, cover, `asymmetric`, `anti_transitive`,
`irreflexive`, `anti_symmetric`, arity); each reader below a vantage decides it. Relation
marks, definitional declarations and arity bindings are on a forced-monotonic roster; a
firing guarded by `unknown` or `exceptWhen` confers `:default`. The justification network
records no defeat, and a read naming no context answers at the handle's own context.
Refused: a durable fork remounted over a grown base (`:fork-base-overlap`), an
`exceptWhen` whose quantifier rebinds a rule variable (`:quantifier-not-local`).

*Breaks:* `defeat-class`, `why-not`, `violations`, `describe`, `retract!`, `edit!`,
`has-prop?`, `props`, `forced_monotonic_predicate`, `forced_monotonic_between_predicates`,
`relationTypeByArity`, `open-kb`, `fork`, `assert`, `check`, `:constraints`,
`VAELII_ARBITRATE_CONSTRAINTS`, `:disjoint`, `:functional`, `:cover`, `:asymmetric`,
`:anti-transitive`, `contradictions`, `supporting-justifications`, `exceptWhen`,
`unknown`, `believed?`, `conflicts`, `preview`, `:irreflexive`, `:anti-symmetric`,
`:unarbitrable-reach-truncated`, `ask?`, `belief-status`, `argue`, `:arity`,
`:arity-truncated`, `:arity-report-truncated`, `binary_predicate`, `variable_arity`,
`arityMin`, `same-class?`, `functional`, `functionalInArg`, `anti_symmetric`,
`injection`, `surjection`, `bijection`, `in?`, `believed`, `types-of`, `isa?`, `genl?`,
`disjoint?`, `:disk-snapshot`, `siblingDisjointException`, `exposed-clashes`

## 0.22.0 — 2026-09-29 — "prove answers what ask answers, a rule record names the engines that run it, and a clash is decided where its grounds come into view"

**57 entries** — 13 Breaking, 8 Refusal, 8 Additive, 28 Fix. `prove`, `ask` and `query`
answer the entailed goal where they answered the stored one, and a rule record holds
`:engines` and `:effect` in place of `:direction`, `:assumption` and `:constraint`. A
clash is decided where its grounds come into view, `violations` no longer files the
clashes the settle decides, and an argument-type mint gives way to a more specific
membership. An ASP solve stops at a conflict limit under a fixed seed, the LLM stack and
the taxonomy's scoped closure budget are gone, and a failed background rebuild ends
read-only. Malformed rules, an `except` naming no handle, a damaged log frame and unusable
server or browser input are refused; `set/solveRule`, the six named points of a temporal
thing, `rebuild-progress` and browser extensions are new.

*Breaks:* `prove`, `provable?`, `prove-within`, `resume`, `ask`, `query`, `query?`,
`query-status`, `search-tree`, `compare-tacticians`, `(:direction`, `(:assumption`,
`(:constraint`, `RuleSentex`, `violations`, `contradictions`, `assert`,
`:exposure-truncated`, `:not-defeasible`, `handle-of`, `sentexes-matching`, `why`,
`VAELII_PRUNE_SUBSUMED_MINTS`, `:disjoint`, `check`, `watch`, `VAELII_LLM_PROVIDER`,
`vaelii.llm.provider`, `VAELII_LLM_LIVE`, `VAELII_OLLAMA_HOST`, `VAELII_OLLAMA_MODEL`,
`VAELII_OLLAMA_GENERATION_MODEL`, `VAELII_OLLAMA_NUM_CTX`, `VAELII_OLLAMA_KEEP_ALIVE`,
`OLLAMA_HOST`, `ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN`, `ANTHROPIC_BASE_URL`,
`/propose`, `:llm`, `vaelii.host.llm`, `with-model`, `:taxonomy-scoped-closures`,
`*scoped-memo-budget*`, `vaelii.memo.budget`, `open-kb`, `:recover? :background`,
`rebuild-progress`, `lein cli`, `resolve-by-majority`, `admin-principal`,
`register-agent`, `set-trust!`, `ask?`, `ask-within`, `VAELII_ASP_SOLVE_LIMIT`, `settle`,
`do/label`, `do/labeling`, `do/classify`, `import!`, `thereExists`, `forall`,
`set/assumptionRule`, `set/hardConstraint`, `set/softConstraint`, `edit!`, `close!`,
`ClosedChannelException`, `Stream Closed`, `:overlay`, `:space`, `:dir`, `:base-stores`,
`set-cache-limit`, `--dir`, `vaelii.serve/start`, `vaelii.web/start`, `/levels`,
`/inference`, `/network`, `/term`, `/find`, `/assert`, `/edit`, `/edit/preview`,
`/retract`, `/sentex/:id`, `/why/:id`, `/justification/:id`, `/demo`, `/reasoning`,
`/jobs/cancel`, `/kbs/load`, `/kbs/unload`, `/kbs/activate`, `/kbs/export`,
`/caches/scale`, `POST /op`, `unload!`

## 0.21.0 — 2026-09-23 — "a definitional clash is decided at the context that sees it whole, and a relation can state that its arguments commute"

**61 entries** — 5 Breaking, 3 Refusal, 12 Additive, 41 Fix. A definitional clash whose
halves sit in two contexts is weighed under `:refuse` at the context that sees both, as
`:arbitrate` already did, and leaves `violations`; under `:arbitrate` a refusal reads the
derivation behind a clash as well as the fact it opposes, and `refuses-assert?` takes the
asserting context. A firing over an inherited claim is placed by the route that places it
highest, a context that disbelieves a `genl` or `genlCx` edge stops reaching over it, and a
firing whose route was defeated is re-derived over any second route its reader reaches.
`IndexStore` gains `unary-sentexes-with-arg` behind index layout 3, `KvBackend` names no
index family, and `ArgColumns` is gone. `commutative`, `commutativeInArgs`,
`commutativeInArgAndRest`, `covering`, `separating`, `partition`, `interArgs` and
`interArgAndRest` join the vocabulary; `watch` refuses an `(and …)` conjunction, one CLI
argument is one form, and `lein cli export --format` takes `text` or nothing.

*Breaks:* `violations`, `contradictions`, `assert`, `:constraints :arbitrate`, `:disjoint`,
`:functional`, `genl`, `check`, `refuses-assert?`, `sentexes-matching`,
`sentexes-in-context`, `IndexStore`, `unary-sentexes-with-arg`, `ArgColumns`,
`arg-scoped-members`, `arg-scoped-intersect`, `watch`, `lein cli`, `read-arg`, `--format`

## 0.20.0 — 2026-09-17 — "a defeated fact stays believed outside the context that decided the clash, and the belief record is renamed Reasoning"

**42 entries** — 6 Breaking, 1 Refusal, 15 Additive, 20 Fix. A clash's defeated member is
disbelieved only at the vantage that sees the clash and below it, a conclusion follows its
reader so an `except` subtracts what rests on what it hides, `contradictions` takes a
reader, and `do/labeling` commits inside its context so two labelings stand side by side.
The record holding a KB's network, taxonomy and derived atoms is renamed `Reasoning`, its
durable image moves to `<dir>/reasoning/`, and seven extension-point protocols move to
held namespaces the development reloader never re-evaluates. A rule is refused an
`(ist Ctx S)` consequent; `open-kb` takes `:recover? :background`, `belief-status` reports
`:withdrawn?` and `:scoped-vantages`, and `lein cli upgrade` brings a store's images up to
the running build. `store-backend` names the backend a directory was written by, the
daemon, the CLI and the browser open a store under it, and only
`scripts/start-vaelii-dev.sh` turns hot reload on.

*Breaks:* `in?`, `believed?`, `except`, `sentexHandle`, `do/labeling`, `contradictions`,
`belief-image`, `:belief-image`, `belief_image`, `types.belief`, `map->Belief`,
`derived-state`, `belief-fingerprint`, `register-belief-image!`, `:belief-fp`, `Prover`,
`SupportingProver`, `Solver`, `SnapshotSink`, `SnapshotSource`, `KvBackend`, `kv-get`,
`:reload?`, `assert`, `assert-rule`, `check`

## 0.19.1 — 2026-09-14 — "five readers repaired after rules lost their sentence field, and the source digest re-parses only files that changed"

**3 entries** — 3 Fix, each a regression 0.19.0 shipped. Five readers that still asked a
rule record for the `sentence` slot 0.19.0 dropped — the NAT teardown, the index
fingerprint, the retired-spelling filter, the vantage supporter check and the QCN
refuted-pair read — take the `implies` form from `sentence-of` instead, so an index dump's
fingerprint over rules is again the digest earlier releases wrote. The source identity
memoizes each engine namespace's parse and re-reads only a file whose stat and digest
moved, taking a call from 1.1 s to 9 ms. The shipped `CxBiology` stores no
`(hasCapability ?x travelling)` record: the capability hierarchy answers it at retrieval,
where a forward rule had stored a second record and justification per flyer.

## 0.19.0 — 2026-09-13 — "stores reopen from a saved belief image instead of recomputing it, and records drop the fields that repeated their own sentence"

**23 entries** — 5 Breaking, 4 Refusal, 4 Additive, 9 Fix, 1 neither label. A
`:disk-snapshot` KB installs a stored belief image at open in place of a full `recover`,
keyed on the records fingerprint, the source identity and the policies, and declines to an
ordinary recover when any of the three moved. The sentex records stop restating what the
store already holds: a rule map carries no `:sentence` and a literal no `:polarity`, a
justification names its rule once as `:informant` and carries no `:out`, and `sentence-of`
reconstructs each form. `bravely` and `cautiously` classify a labeling's dilemmas with no
ASP backend, a `genlCx` cycle is refused at assert as a `genl` cycle already was, and three
write paths that stored a record no belief-filtered read could find now refuse. Seven hot
paths drop work that changes no answer, an operation log and seal for a `:disk-snapshot`
KB's public writes are built with no entry point that attaches them, and a settle-phase
instrument splits a settle's wall clock
into four cost centres. The engine's `project.clj` names no `vaelii-foreign` coordinate,
so an engine release no longer forces a plugin release.

*Breaks:* `:refuse`, `violations`, `sentex`, `sentexes-matching`, `canonical-sentex`,
`:sentence`, `:polarity`, `bravely`, `cautiously`, `justification`,
`supporting-justifications`, `dependent-justifications`, `vaelii.belief.snapshot`,
`genlCx`, `assert-inert`, `cardAtMost`, `cardAtLeast`

## 0.18.1 — 2026-09-11 — "every entry point refuses an out-of-range value by name, and the upper ontology splits things into spatial and temporal"

**14 entries** — 2 Refusal, 4 Additive, 6 Fix. Every bounded entry point refuses a value
outside its domain by name, reading one shared domain table, and `assert-inert` refuses an
open sentence. The upper ontology divides `thing` by space and time, renames
`spatial_thing` and `temporal_thing` to `spatial` and `temporal`, and adds a `CxUniverse`
collector context. A process-wide cache profile scales every derived cache's bound, and a
memory-pressure guard the servers install shrinks the caches as the old generation fills
and grows them back as it drains. A reified NAT or context constant is named by the
SHA-256 of its expression, so the same expression reifies to the same constant across
processes, and the one-shot clingo solve injects its ground program through the backend
accessors rather than a temp file.

*Breaks:* `:counters?`, `:believed?`, `:max-cost`, `:max-depth`, `:max-term-growth`, `add-evaluatable`, `assert-inert`, `describe`, `why-not`, `spatial_thing`, `temporal_thing`

## 0.18.0 — 2026-09-09 — "argument-type declarations create the types they constrain, and rules forward-chain only when asked to"

**16 entries** — 3 Breaking, 1 Refusal, 9 Additive, 3 Fix. Assertive argument types become
the default reading: an `arg` / `genlArg` / `interArg` declaration mints the type it
constrains rather than only testing for it. A bare `implies` rule defaults to `:backward`
and materializes nothing, and `set/forwardRule` adds forward chaining to the backward use
rather than replacing it, so a rule forward-chains only where its author asks. The arity
vocabulary gains a runtime floor — a variable-arity application below its `arityMin` is
refused — and `admitsArgnum` answers a position query from the declared arity. New
declaration vocabulary types a whole variable-arity tail (`args`, `argsGenl`, `argAndRest`,
`argAndRestGenl`) and names an `intersection` kind that derives its taxonomy edges, and new
readers report the brave and cautious status of a labeling dilemma, a cardinality bound over
ASP choice heads, and the subsumption status of every type pair. A state-of-affairs and
causality cluster joins the upper ontology in CxAbstract.

*Breaks:* `VAELII_ASSERTIVE_ARG_TYPES`, `(implies` asserted bare, `set/forwardRule`,
`arityMin`, `(lessThan`, `(greaterThan`, `(termsRelated`, `(functionCorrespondingPredicate`,
`vaelii.impl.llm.protocol/Provider` (now `vaelii.host.llm.protocol/Provider`; the
entry was added after the release)

## 0.17.0 — 2026-09-06 — "arity becomes declared vocabulary on every relation, and declarations stop restating what they already imply"

**14 entries** — 1 Breaking, 4 Refusal, 4 Additive, 5 Fix. A declaration that restates
what the taxonomy already concludes turns that conclusion into a precondition, so the
arrival order of two assertions decides which facts a KB holds. Four entries retire such a
declaration — on `genl`, on fifteen unary marks, on six arity marks, and in the `predAll`
pair's third argument — and the arity vocabulary underneath is rebuilt so `relation` is
the common parent of `predicate` and `function` and every relation lands in exactly one
arity policy. `predAllSpecified` and `predSpecifiedAll` go binary and derive the filler
type from the predicate's own slot contract. Three composite function marks — `injection`,
`surjection` and `bijection` — arrive as one declaration each, a `genlCx` edge's merge
sweep stops growing with the KB, and a late `symmetric` declaration folds a mirrored pair
no earlier version could fold.

*Breaks:* `(predAllSpecified`, `(predSpecifiedAll`, `specified-violations`,
`all-specified-violations`, `(binary_predicate P)` beside `(variable_arity P)`,
`:arg-type`, `*assertive-arg-types?*`, `VAELII_ASSERTIVE_ARG_TYPES`,
`(genlArg genl 1 thing)`, `(arg symmetric 1 predicate)`, `(arg functional 1 predicate)`

## 0.16.0 — 2026-09-04 — "the predAll quantifier family, refusals that carry a type, and declarations that apply to facts already stored"

**18 entries** — 3 Breaking, 1 Refusal, 7 Additive, 7 Fix. The `predAll` quantifier
family lands in all eight cells. Three refusals stop answering with the wrong keyword:
an unpinned indeterminate term is not provably `different` from anything, a missing
adapter is not an unknown backend, and a wrong operand count is not an unknown option.
Declarations arriving after the facts now reach them — a `(symmetric P)` mark folds
records already stored, a computed `genlCx` edge runs the reconcilers a stated one runs,
and `quotedArg` is answered along the `genl` closure. Every refusal declares what its
`ex-data` carries, and a throw that drops a key fails the build.

*Breaks:* `(different`, `indeterminate_term`, `:unknown-backend`, `:sqlite`, `:pg`,
`:unknown-option`, `:not-stratified`

## 0.15.0 — 2026-09-01 — "definitions that compute their own answer, and two renames"

**7 entries** — 2 Breaking, 5 Additive. Definitional membership is answered at query
time rather than only by a forward rule. Two renames: the sentex polarity slot is
`:polarity`, and the `AtomicSentex` record is `LiteralSentex`. A unary predicate is
snake_case and `assert` enforces the spelling in both directions, which retired the
camelCase marks. CxCore names the expression kinds and gains a curation vocabulary.

*Breaks:* `unaryPredicate`, `reifiableFunction`, `abduciblePredicate`,
`closedExtentPredicate`, `disjointMetatype`, `siblingDisjoint`, `warmBlooded`, `:truth`

## 0.14.0 — 2026-08-29 — "the index image becomes a storage backend, and the heap it no longer needs"

**10 entries** — 1 Refusal, 1 Additive, 5 Fix. The mapped index image becomes a backend
of its own, `:disk-snapshot`, rather than a property of the disk store, and stops
carrying the argument roots into heap. The disk store's live-handle sets become
compressed bitmaps. The writer refreshes a drifted image mid-life and can be told not
to. A `functionalInArg` declaration arriving after the facts it convicts is reported
rather than silently late. Neither adapter shipped at this version; both stayed at
0.13.0.

*Breaks:* `vaelii.index.snapshot`, `:argument-family-ceiling`

## 0.13.0 — 2026-08-25 — "calendar time, joined queries, and entry points that refuse invalid input"

**95 entries** — 5 Breaking, 14 Refusal, 32 Additive, 22 Fix. The largest release:
calendar time, joined queries and a sweep through the entry points that refuse.
`CxChange` ships an event calculus, calendar constructors give a date its own endpoints
so it orders itself, and a metric constraint narrows an interval relation. `or` is
accepted in a rule antecedent, stored as one rule per alternative, and refused as a
goal. Every search entry point takes a bound and the daemon holds them to its ceiling.
Fourteen refusals close inputs whose acceptance stored junk, and the `:disk` and
`:pg-disk` pairings are renamed to say that both halves are out of core.

*Breaks:* `:disk`, `:pg-disk`, `VAELII_TEST_BACKEND=disk`, `edit!`,
`edit-with-consequences!`, `apply-proposal!`, `contexts`, `count-in-context`,
`contextDenotingFunction`, `lein cli load`, `prove`, `provable?`, `query`, `argue`,
`forward-chain`, `ask`, `ask?`, `query-plan`, `abduce`, `sentexes-matching`,
`handle-of`, `assert`, `load-text!`, `lein cli assert`, `unaryPredicate`,
`binaryPredicate`, `ternaryPredicate`, `/kbs`, `lein serve --listen <flag>`,
`vaelii.client/client`, `:timeout-ms`, `:token`, `dereference`, `resolve-by-locator`,
`set-trust!`, `trust-of`, `display-name-of`, `:reserved-family` (a dense index past its
`(predicate, position)` ceiling is `:argument-family-ceiling`), `do/label` over an
`assumptionRule` with a negated head (`:choice-head-not-positive`); these two entries
were added after the release

## 0.12.0 — 2026-08-23 — "query contexts, bulk loading, and types for literal values"

**99 entries** — 3 Breaking, 3 Refusal, 7 Additive, 5 Fix. Query contexts, bulk loading,
and a literal's type. `resultIsa` and `resultGenl` become `result` and `genlResult`; the
four function marks classify what they mark, and the reifiability criterion is written
down. A records read stays lazy, and a proof's witness is one of its bindings. Three
reads that could not answer the question stop answering empty. First release of the two
adapters, `com.vaelii/postgres` and `com.vaelii/sqlite`, each at this version.

*Breaks:* `resultIsa`, `resultGenl`, `reifiableFunction`, `unreifiableFunction`,
`quotingFunction`, `contextDenotingFunction`, `ist`, `:proof?`, `?ctx`,
`qualitative-network`, `possible-relations`, `:arg-type`, `:quoted-arg-type`, `result`,
`genlResult`, `:arg-genl`, `character_string`, `:pg-disk`, `:dir`,
`:stale-index-records`, `register-modal-predicate!`

## 0.11.0 — 2026-08-22 — "contradiction solving, arrival order, and the durable log"

**67 entries** — 2 Breaking, 4 Additive. Contradiction solving, arrival order, and the
durable log. `antiTransitive` convicts the chain it forbids rather than being declared
and deferred. Definitional collection relations tie membership to a defining condition,
and sibling disjointness lets a collection's specializations separate themselves, with
an escape hatch for a pair that must overlap. A computed predicate or function is
registered in one line.

## 0.10.0 — 2026-08-20 — "more than one agent over one knowledge base"

**9 entries** — 4 Additive. Koinii: several agents coordinate over one shared knowledge
base, with belief projection for what each agent holds true. A context can be a reified
function application whose `genlCx` edges compute themselves. Mention-opacity arrives —
a quoting function reads its argument by spelling — and `quotedArg` types an argument
against a syntactic type. The `argIsa`, `argGenl` and `interArgIsa` spellings become
`arg`, `genlArg` and `interArg`.

## 0.9.0 — 2026-08-17 — "the truth-maintenance network defaults to dense"

**15 entries** — 5 Breaking, 8 Additive. The dense truth-maintenance network becomes the
default and gives a concurrent reader a consistent view. Four relation properties are
enforced rather than documented. A subsumption rests on its strongest route rather than
its shortest. An algebraic property becomes one predicate instead of a mark and a twin,
which retired the `...Predicate` spellings.

*Breaks:* `defeat-class`

## 0.8.0 — 2026-08-14 — "predicates inherit down the hierarchy"

**50 entries** — 1 Breaking, 1 Additive. Predicates inherit down the hierarchy. A KB
whose declared hazards are unresolved refuses writes rather than accepting them
unchecked, and a derived record's teardown is refused where belief was never built.
`check` and `check-edit` answer for the entry point they mirror. Five refusals close
recovery paths that believed records the store did not hold.

*Breaks:* `:unrecovered-kb`, `write-hazards`, `note-hazards!`, `contradictions`,
`violations`, `:constraint-exposure`

## 0.7.0 — 2026-08-12 — "contexts get a single naming convention"

**2 entries.** Contexts get one spelling. A context name is `Cx`-prefixed rather than
`Context`-suffixed, and the context-transitivity predicate is `genlCx`.

## 0.6.0 — 2026-08-12 — "stored rules become first-class"

**22 entries** — 2 Breaking, 4 Refusal, 2 Additive. Stored rules become first-class: a
rule can conclude a rule, and a rule carries a handle, TMS support and retraction with
no rule-specific machinery. A capability claim about a kind is `capabilityType` and
about a member is `hasCapability`. A NAF guard written as a conjunction now guards, and
the strictest policy stops being the leakiest.

## 0.5.1 — 2026-08-11 — "faster writes, and more of the engine exposed to monitoring"

**15 entries.** Faster writes, more to watch. A settle pays for the region it moved
rather than for what the KB holds. The arbitrating half of a bounded pass says when its
budget stopped it. Four places where arrival order decided an answer are closed.

## 0.5.0 — 2026-08-07 — "operating the engine as a service"

**23 entries.** Operating the engine as a service. The daemon authenticates and refuses
to bind an address without a token. One space number names a KB's stores, `:space`,
replacing the separate record and index spellings. `context-size` becomes
`count-in-context`, `different` descends into compound arguments, and a name can carry a
sense and a lexeme.

*Breaks:* `:record-space`, `:index-space`, `docs/storage.md`

## 0.4.0 — 2026-08-05 — "correctness fixes against the invariants"

**33 entries.** Correctness fixes against the four invariants. A conjunctive query could
answer nothing while each of its conjuncts answered, and no longer does. `assert`
refuses a sentence that is not an s-expression, an `exceptWhen` query's literals are
held to the naming invariants, and an `edit!` batch key nothing reads is refused.

## 0.3.0 — 2026-08-04 — "a type on every refusal"

**29 entries.** A type on every refusal: every `ex-info` the engine throws carries a
`:type`, and the daemon's refusal keywords become plain. Both servers hold one
request-body ceiling, and the browser serializes its writes. An `ist` form must have
exactly three elements.

## 0.2.0 — 2026-08-03 — "the public API boundary is drawn"

**17 entries.** The public API boundary is drawn — six public namespaces, everything
else `vaelii.impl.*` and free to change. Every handle-taking function refuses a
non-handle. `close!` releases a durable KB's directory, an argument-constraint refusal
names its convicting declaration in content order, and the five sweeps start running in
CI.

## 0.1.0 — 2026-07-31 — "the first release"

The first public release.

## 2026-07-19 .. 2026-07-30 — the pre-release dailies

Twelve dated entries before versioning began, one per day of the initial build: the
whole stack on day one (2026-07-19), then order independence made an invariant, equality
and a sudoku solved, sound negation as failure, performance fixes and an operational
surface, denser storage measured first, OpenCyc in the engine's own format, reads scoped
to the asking context, aggregation over query results, the gate (lint, suite and
scaling), one entry point for backward chaining, and declarations that re-check what
they change (2026-07-30).
