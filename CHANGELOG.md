# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.33.0 are summarized rather than reproduced.** Each one
keeps its title and its class census, and each one from 0.14.0 on keeps every
`*Breaks:*` token, so an upgrade across those releases is still a grep for the name you
call; 0.8.0 through 0.13.0 keep a subset. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking: ontology

- **Kinship shares one generic hierarchy with blood and chosen readings.** `relativeOf`
  becomes `kinOf`; `BloodKinFn` qualifies eternal blood history and `ChosenKinFn`
  qualifies time-varying chosen ties. Generic kinship is time-agnostic. Gestational-only
  parenthood is blood kin without a genetic or shared-carrier sibling inference.
  Mothers are not unique; `MotherFn` does not choose between several known mothers.
  `originatorOf` admits organisms and no longer specializes kinship.
  *Migration:* rename `relativeOf` to `kinOf`; rewrite biological family/history facts
  with `BloodKinFn`. Generic facts no longer assert blood descent or eternity.
  `MotherFn` and `FatherFn` correspond to their blood-qualified predicates.
  *Breaks:* `relativeOf`, `parentOf`, `childOf`, `motherOf`, `fatherOf`, `siblingOf`,
  `grandparentOf`, `ancestorOf`, `birthDate`, `birthYearOf`, `olderThan`, `MotherFn`,
  `FatherFn`, `originatorOf`

### Additive: shipped ontology

- **A `comment` documents any closed expression.** `core.txt` declares
  `(quotedArg comment 1 closed_expression)`, so the commented position takes a closed
  term, a `(sentexHandle N)` or a closed sentence, each taken as written. A compound
  with a free variable there is an `open_expression`, which `reflection.txt` separates
  from `closed_expression`. `assert` refuses a comment on one, or on a bare variable,
  as `:not-ground` before any argument check reads it. `implementationNote` keeps
  `denotational_term`.
  [argtypes.md](docs/argtypes.md#the-quoted-twin)
- **`predAllQuotedSpecified` and `predSpecifiedAllQuoted` audit the terms of an
  expression kind as written.** The quoted twins of `predAllSpecified` and
  `predSpecifiedAll` take an expression kind where the pair takes a collection.
  `(predAllQuotedSpecified comment symbol)` requires a comment of every atomic name a
  stored sentex the reader sees writes, and a quotation is no name. The filler is audited
  as the pair audits one. A written term is audited only in readers under its ordinary
  defining homes, as the pair audits an instance, so an engine-made copy in CxUniverse
  adds no reader. `all-specified-violations` and `kb-integrity` sweep both twins,
  and `vaelii.impl.predall/quoted-specified-violations` audits one declaration. The
  population grows by one term per name the KB writes. No shipped declaration uses them.
  [predall.md](docs/predall.md#quoted-specified-the-population-as-written)

### Internal: CI

- **A CI shard runs its recurring failures first**
  ([#280](https://github.com/vaelii/vaelii/issues/280)). `scripts/ci-shard.sh` reads the
  checked-in `scripts/ci-test-history.tsv` and orders each shard's namespaces by
  recurring-failure count, then weight, then name. Which shard a namespace is in does not
  change, and every shard still runs every namespace it is given. A history that is
  missing, stale or malformed is ignored whole, for the lightest/heaviest order shards
  ran before.
- **The `weights` check skips each shard's first namespace.** A namespace that runs
  first in a JVM also pays the JVM's and the KB's start-up, about 70 s on CI, so
  `scripts/ci-weights.sh` judges every row but the first of each shard's timings. The
  rerun is skipped when rerunning the named namespaces is predicted to take longer
  than the whole shard, so a run where most namespaces regress fails on its first
  times instead of rerunning the shard.

## 0.33.0 — 2026-11-10 — "A separation undercutting a `:default` edge's reading, shipped type edges at `:monotonic`, relations classified by rigidity, a three-argument `functionCorrespondingPredicate`, daemon reads held to their ceilings, a time slice seeing the context it slices"

| Area | Change |
|---|---|
| inference | a separation or a cover undercuts a `:default` `genl` edge's reading of a membership; a cover nogood leaves a membership in no minimal nogood believed; a denial of a `decontextualized_predicate` lifted into CxUniverse; a write naming an application stores its constant, which a `:monotonic` value reaches through `rewriteOf`; an application whose corresponding predicate is not assertible takes the prover's value |
| shipped ontology | the shipped type `genl` edges `:monotonic`, except three; `genlMonad`, `monad_context`, `cxMonadOf`, `cxTimeOf` and `argN` answered by provers and refused at `assert`; pull request status kinds; `largerThan` renamed `typeLargerThan`; `person` under `spatial`; `sempiternal` disjoint from `tangible`; lists, multisets, finite sets and maps as structural terms |
| time | `TimeIntersectionFn` the meet over `subtimeOf`; a time slice sees the context it slices, and slices order through their times' points; an eternal predicate's fact in a slice copied into the context it slices; inertia stops at a terminator the KB does not place outside the span; calendar terms in the interval network; `holdsAt` off the calendar clock; `tightestStartBoundOf`; an exact start of the real world's present refused |
| rigidity | the rigidity kinds of relation, `eternal_predicate`, `stable_once_true` and `stable_once_false`, `temporalIndexArg`, `permanentPartOf` and `typeAllSpecified`; the shipped relations classified |
| NATs | `functionCorrespondingPredicate` takes three arguments; a reifiable application as a literal's predicate |
| storage | a quoted rule not found by its connectives; a `.` outside a rest marker refused; a durable fork reopens over a grown base and keeps its handles; `:fork-dirs`; `BulkDeleting` |
| serving | the daemon holds its clocked ops to `VAELII_MAX_QUERY_MS` and `:prove` to `VAELII_MAX_QUERY_DEPTH`; a handler built for an address refuses a request with no token; a grant writing an eternal predicate's fact into a slice names the context it slices |
| integrity | `kb-integrity` reads a rule's exceptions in the clash's context; `defining-contexts` classifies a derived support by its premises; the rule-macro sweep covers `arg` |
| performance | a write that owes the settle nothing runs no settle pass; a query resolves only its goal's variables; a forward join re-plans after a one-row step; a `genl` edge, a `genlCx` edge or an `except` re-chains only what it can move; a context-NAT read reads one argument position's `natFormula` maps; `edit-records!` reads and deletes a chunk at a time |
| browser | a literal search naming one term opens its page; `/` focuses the search box; the sandbox cookie carries `Secure` behind a proxy |

Nineteen entries are **Breaking** and nine are **Refusals**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.32.0 caller changes.

| If your code… | Then |
|---|---|
| reads a membership a `:default` `genl` path reaches beside a separation or a cover's denials as true | state the edge `:monotonic` where the membership must meet the separation or the cover |
| reads a membership a cover nogood convicted beside an unresolved two-member membership nogood as false | state a denial of that membership where it must not hold |
| reads a denial of a `decontextualized_predicate` only in the context that states it | declare the predicate `:monotonic` where a `:monotonic` statement must decide every context, and name CxUniverse in a serve grant that writes such a denial |
| reads the stored sentence of a write naming an application beside a `:monotonic` value | read the use through `ask`, `query` or `representative` |
| reads from a time slice's monad, or another slice of it, beside an eternal predicate's fact stated in a slice | state a fact that holds at one time only under a predicate that is not eternal |
| relies on a shipped type `genl` edge being `:default` | retract the membership or the denial that now meets a clash the ontology states |
| reads `holdsAt` across a terminating event whose moment is not ordered against the span | state the order of a terminating event outside the span, with `instantBefore` or the clock |
| writes `(timeIntersectionOf A B I)`, or reads a slice at an intersection by an unsorted spelling | write `(timeIntersectionOf I A B)`, and re-assert a slice's facts into its slot |
| asserts `genlMonad` | state `(genlCx A B)` |
| asserts `monad_context`, `cxMonadOf` or `cxTimeOf` | state `(context C)` for `monad_context`, and ask the other two |
| asserts `argN` | ask it |
| reads CxUniverse's premises for a CxTra type's `unary_predicate` mark | read the mark with `ask`, or find the premise in CxTra |
| names `prStatus`, `pull_request_status` or its four individuals | name the status kinds `draft_pr`, `ready_pr`, `merged_pr` and `closed_pr` |
| names `largerThan` | name `typeLargerThan`; `upgrade --sync` rewrites a stored premise |
| states or asks a two-argument `functionCorrespondingPredicate` | write `functionCorrespondingBinaryPredicate` for a binary predicate, and the ternary with the value position otherwise |
| calls `find-sentexes` of `implies`, `and` or `not` to find quoted rules | find a quoted rule by a predicate or constant inside it, and `reindex` a durable store |
| stores a reifiable application as a literal's head under `:naming :warn` or `:off` | retract each such fact and assert it again |
| builds `vaelii.serve/app` or `vaelii.web/handler` for an address with no token | pass `:token`, or set `VAELII_API_TOKEN` |
| serves an `:assert` of an eternal predicate's fact into a time slice or of a `natFormula` naming a slice, or an `:assert` or removal of an eternal membership, its denial or its `defeat`, under a token-table grant | name the context the slice slices in the grant, and write or remove an eternal membership under an admin grant |
| sends the daemon a `:lookup`, `:query`, `:query?`, `:query-status` or `:argue` that runs past `VAELII_MAX_QUERY_MS`, or a clocked op with no option map | name a `:max-ms` at or under the ceiling, or raise `VAELII_MAX_QUERY_MS` |
| sends `:prove`, `:provable?` or `:prove-within` deeper than `VAELII_MAX_QUERY_DEPTH` | name a `:max-depth` at or under the ceiling, or raise it (`0` lifts it) |
| sends `:escalate` with a `:max-ms` over the ceiling, or one that climbs past it | name a `:max-ms` at or under the ceiling |
| asserts an exact start of the real world's present, or a dated present-tense fact there | state a clock reading as `(instantNotBefore W T)` |
| stores a `defeat`, a `genl` self-loop, a dangling `except` or a `do/` form with `assert-inert` | retract such inert records before exporting |
| asserts a `TimeIntersectionFn` of disjoint calendar times | retract it |
| asserts a bare `(sentexHandle N)` | retract it |
| writes or reads a `.` outside a rest marker | write `(p ?x . ?rest)`, or drop the `.` |
| keeps a `reasoners.edn` holding no map or a malformed `:reasoners` | rewrite it as `{:reasoners [name …]}` |

### Breaking: inference

- **A separation or a cover undercuts a `:default` `genl` edge's reading of a membership.**
  With `(genl beast perishing)` at `:default` and `(beast Hydra)`, a membership
  `(immortal Hydra)` of either strength under `(disjoint perishing immortal)`, or denials
  of every part of a cover of `perishing`, makes `ask?`, `query` and `argue` answer
  `(perishing Hydra)` false, and a rule on `(perishing ?x)` does not fire for `Hydra`.
  `(beast Hydra)` stays believed beside them, and `conflicts` and `contradictions` report
  nothing, where a `:default` `(beast Hydra)` lost or the two memberships were a dilemma.
  Two memberships read over `:default` edges into the two sides of a separation are a
  dilemma between the two readings. A path whose edges hold only `:monotonic` supporters
  stores no reading.
  [inference.md](docs/inference.md#an-edges-reading)
  *Migration:* state the edge `:monotonic` where the membership must meet the separation
  or the cover.
  *Breaks:* `ask`, `query`, `argue`, `conflicts`, `contradictions` and forward firings
  over a membership a `:default` path climbs from to a separated type or a cover's whole;
  the stored handle set, which holds the reading
- **A membership in no minimal membership nogood stays believed beside a cover a smaller
  nogood refutes.** Where a `disjoint` or `supertype` nogood of two memberships of a term
  stays a hard clash or a dilemma, a cover nogood holding them and a third membership no
  longer defeats or undercuts the third through a part the two-member nogood's separation
  already denies. The cover places no route the two-member nogood places at or above, so
  a term asserted `animal` and then `fixed_arity_predicate` over the starter places 27,518
  routes against 832,010 and takes 6.5 s for the second write against 221 s, in one probe
  on a loaded box. [nmtms.md](docs/nmtms.md#the-nogood-families)
  *Migration:* state a denial of the third membership where it must not hold.
  *Breaks:* `ask`, `query` and `contradictions` for a membership a cover convicted beside
  an unresolved two-member membership nogood
- **A denial of a `decontextualized_predicate` is lifted into CxUniverse**
  ([#256](https://github.com/vaelii/vaelii/issues/256)). A `(not (P …))` stated or
  concluded in any context is copied into CxUniverse on the declaration about `P`, as
  `(P …)` is, so a sibling's denial is read from every context, and its clash with a lifted
  `(P …)` is reported or decided at CxUniverse. A copy holds at the weaker of its source's
  and the declaration's strengths, so under a `:default` declaration a `:monotonic`
  statement against its sibling's opposite is a dilemma at CxUniverse. A denial of a
  permuting mark is not lifted.
  [contexts.md](docs/contexts.md#a-denial-is-lifted-as-the-positive-is)
  *Migration:* declare `P` at `:monotonic` where a `:monotonic` statement about `P` must
  decide every context, and name CxUniverse in a serve grant that writes a denial of `P`.
  *Breaks:* `ask`, `query`, `contradictions` and `conflicts` beside a denial of a
  decontextualized predicate; a served `:assert` of such a denial under a grant without
  CxUniverse (`:forbidden-context`)
- **A write or a firing that names an application stores the application's constant, and a
  `:monotonic` value reaches it through `rewriteOf`.** Beside a `:monotonic` `(motherOf
  Muffet Mary)`, `(caresFor Bob (MotherFn Muffet))` stores `(caresFor Bob K)`, with `K` the
  constant minted for `(MotherFn Muffet)`, and `(rewriteOf Mary K)` restates it as
  `(caresFor Bob Mary)`. A retraction of the value's premise takes the restatement OUT and
  leaves `(caresFor Bob K)` believed, whichever of the value and the use arrived first.
  `handle-of`, `why-not`, `assert-inert`, `canonical-sentex` and `check` resolve an
  application as a write does. A `not_assertible` corresponding predicate's computed value
  still names the application.
  [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* read a use through `ask`, `query` or `representative`, which answer the
  value where its fact is visible; the stored sentence of the write's handle names `K`.
  *Breaks:* the stored sentence, `why` and the sentex count of a write or a firing naming
  an application beside a `:monotonic` corresponding value; what is believed after that
  value's premise is retracted
- **A fact of an `eternal_predicate` stated in a time slice is copied into the context the
  slice slices** ([#259](https://github.com/vaelii/vaelii/issues/259),
  [#272](https://github.com/vaelii/vaelii/issues/272)). A `(P …)` or `(not (P …))` stored
  in a slice is copied when the slice sees `(eternal_predicate P)`, or a membership of `P`
  in a type below it, in its own context or its `genlCx` ancestor set, so every slice of the
  monad reads it. A denial of the membership, an inherited one included, withdraws the
  copy. `time.txt` makes `happens`, `initiates`, `terminates` and `holdsAt` eternal: a
  fluent started in `(CxTimeFn CxRealWorld (YearFn 2000))` holds at a later moment asked
  from the present slice or the 2025 slice. A fact of a predicate no membership makes eternal stays in its
  slice. A context a hand-written `(natFormula K (CxTimeFn C T))` names is a slice of `C`
  and sees `C`, as a slice written in place does.
  [contexts.md](docs/contexts.md#eternal_predicate-a-fact-stated-in-a-time-slice-holds-in-what-it-slices)
  *Migration:* state a fact that holds at one time only under a predicate that is not
  eternal.
  *Breaks:* `ask`, `query` and `prove` from a slice's monad or another slice of it, beside
  an eternal predicate's fact stated in a slice, and from a context a hand-written
  `natFormula` names as a slice; the sentex count of such a fact

### Breaking: shipped ontology

- **The shipped type `genl` edges are `:monotonic`, except three.** 278 type edges in
  `upper/` and `middle/` move from `:default` to `:monotonic`. `(genl tangible
  uninterrupted)` and `(genl intermittent intangible)` stay `:default`, since a watch taken
  apart and rebuilt is tangible and intermittent, and so does `(genl warm_blooded
  vertebrate)`. The 21 `intersection`, 18 `typeGenl` and 3 `separating` declarations, and
  the `ip_address` partition, are `:monotonic` too. A firing through a shipped edge takes
  the class of its rule and fact, not `:default`. A `:default` membership beside a
  `:monotonic` denial of a shipped supertype loses to the denial, where the denial
  undercut the edge's reading.
  [oe-principles.md](docs/oe-principles.md#catbus-principle)
  *Migration:* a membership that now loses to a denial of its supertype meets a clash the
  ontology states; retract the membership or the denial.
  *Breaks:* a `:default` membership beside a denial of a shipped supertype; the class of a
  firing through a shipped edge
- **Inertia stops at a terminating event the KB does not place outside the span**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `CxChange`'s two `holdsAt` rules
  block on a terminator unless its moment is the start or the asked moment, or
  `instantBefore`, `instantNotAfter` or `instantNotBefore` places it at or before the
  start or at or after the asked moment. They blocked only on one stated strictly inside
  the span. A fluent ended at a moment the narrative leaves unordered against the reading
  no longer holds there.
  [time.md](docs/time.md#change-over-time-events-fluents-and-inertia)
  *Migration:* state the order of a terminating event that lies outside the span, with
  `instantBefore` or the clock.
  *Breaks:* `holdsAt` across a terminating event whose moment is not ordered against the
  span
- **`TimeIntersectionFn` is the meet over `subtimeOf`, of two or more times**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `time.txt` states
  `(meetFunctionOf TimeIntersectionFn subtimeOf)`, so an application is stored sorted and
  flattened, and an argument a calendar comparator places above another is dropped:
  `(TimeIntersectionFn (YearFn 2000) (MonthFn 2000 1))` is stored as `(MonthFn 2000 1)`.
  `timeIntersectionOf` takes the intersection first, `(timeIntersectionOf ?intersection .
  ?times)`. A context slot takes the same canonical form before it reifies, so a `cx/`
  constant minted before the upgrade for a slot holding an intersection is not reached
  by a read of that slot.
  [time.md](docs/time.md#a-slice-of-a-slice)
  *Migration:* write `(timeIntersectionOf I A B)` for each `(timeIntersectionOf A B I)`,
  and re-assert the facts of a slice at an intersection into its slot.
  *Breaks:* `timeIntersectionOf`, `(arity TimeIntersectionFn 2)`
- **`genlMonad` is not assertible: two monads are ordered by `genlCx`**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `time.txt` marks
  `(not_assertible genlMonad)`, so `assert` refuses `(genlMonad A B)` as
  `:not-well-formed`, and `provers/GenlMonadProver` answers it from the `genlCx` closure
  between the monads of `A` and `B`. A `genlMonad` fact a store holds is unbelieved after
  the upgrade.
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad)
  *Migration:* state `(genlCx A B)` in place of each `(genlMonad A B)`.
  *Breaks:* `assert` of `genlMonad`
- **`monad_context`, `cxMonadOf` and `cxTimeOf` are not assertible**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `time.txt` marks the three
  `not_assertible`, so `assert` refuses each as `:not-well-formed`, and
  `provers/ContextPartsProver` answers them at `ask` from the `natFormula` maps of the
  slices, in place of five backward rules. A context that is not a slice is its own monad
  and covers `Forever`. `CxMonadOfFn` and `CxTimeOfFn` are reifiable, and an application
  reads and writes as the prover's value: `(CxTimeOfFn CxStory)` is `Forever`. A fact of
  the three a store holds is unbelieved after the upgrade.
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad)
  *Migration:* state `(context C)` in place of each `(monad_context C)`.
  *Breaks:* `assert` of `monad_context`, `cxMonadOf` and `cxTimeOf`
- **`argN` is not assertible.** `core.txt` marks `(not_assertible argN)`, so `assert`
  refuses `(argN T N F)` as `:not-well-formed`, a false one included, and
  `provers/ArgPositionProver` answers every `argN` goal from the formula as written. An
  `argN` fact a store holds is unbelieved after the upgrade.
  [inference.md](docs/inference.md#the-pluggable-prover-engine-vaeliiimplprovers-ask)
  *Migration:* ask `argN` instead of storing it.
  *Breaks:* `assert` of `argN`
- **The starter states a type's `unary_predicate` mark in the context that defines it.**
  Each upper and middle file declares its types' marks beside their definitions, and the
  starter computes none. The starter's closing batch stated every mark in CxUniverse,
  including 20 for types only CxTra's edges reach, so CxUniverse held premises about a
  theory it does not see. CxTra states those 20 now, and the decontextualized lift stores
  a derived copy of each in CxUniverse, so `ask` answers as before at every context. A
  defining-context audit keeps those types' obligations in the readers of CxTra.
  [api.md](docs/api.md)
  *Migration:* read a mark with `ask`, which answers at every context; a caller reading
  the premises of CxUniverse finds the 20 in CxTra.
  *Breaks:* `premise?` and `why` of the 20 CxTra types' CxUniverse marks, the starter's
  sentex count (one more per moved mark)
- **A pull request's status is its membership in a status kind.** CxTra's `open_pr`,
  `merged_pr` and `closed_pr` partition `pull_request`, and `draft_pr` and `ready_pr`
  partition `open_pr`. Each is time-varying: a pull request changes status and stays the
  same request. `prStatus`, `pull_request_status` and its four individuals
  `PullRequestDraft`, `PullRequestReady`, `PullRequestMerged` and `PullRequestClosed` are
  retired.
  [catalog.md](docs/catalog.md#a-releases-renames)
  *Migration:* write `(prStatus ?pr PullRequestDraft)` as `(draft_pr ?pr)`,
  `PullRequestReady` as `ready_pr`, `PullRequestMerged` as `merged_pr` and
  `PullRequestClosed` as `closed_pr`; `upgrade --sync` reports each stored premise
  naming one of the six.
  *Breaks:* `prStatus`, `pull_request_status`, `PullRequestDraft`, `PullRequestReady`,
  `PullRequestMerged`, `PullRequestClosed`
- **`largerThan` is `typeLargerThan`.** The relation compares two kinds, as a
  `type_relation_predicate`, and the new name keeps it from reading as a sibling of
  `tallerThan` and `heavierThan`, which compare two individuals. Its declarations, its
  facts in CxSize and its comment are unchanged apart from the name.
  [catalog.md](docs/catalog.md#a-releases-renames)
  *Migration:* `upgrade --sync` rewrites a stored premise naming `largerThan`; write
  `typeLargerThan` in every rule and query.
  *Breaks:* `largerThan`

### Breaking: NATs

- **`functionCorrespondingPredicate` takes three arguments, and the third, the value
  position, is always stated.** `(functionCorrespondingPredicate F P N)` says `(F a…)` is
  the value `P` holds at argument `N` of those arguments. A two-argument form is refused
  `:not-well-formed`. `(functionCorrespondingBinaryPredicate F P)` states the common case,
  a binary `P` with the value second: a `core.txt` rule concludes
  `(functionCorrespondingPredicate F P 2)` from it, and the engine reads only the ternary.
  That ternary is derived, so a rule stored before the binary declaration is not
  respelled through it. This accepted limit is tracked in
  [#271](https://github.com/vaelii/vaelii/issues/271); the order regression remains `:red`.
  Two `functionalInArg` marks constrain the ternary. A function and predicate pair has one
  position, and a predicate and position have one function, so a second position for a
  pair, or a second function for a predicate and position, is a `:functional` nogood and
  `try-assert` refuses it. A function may still correspond to several predicates. The
  shipped correspondences use `functionCorrespondingBinaryPredicate` for a binary
  predicate whose value is second, and the explicit ternary otherwise. The declaration
  is no longer `variable_arity_predicate` or `bounded_arity`, and `core.txt` states no `arityMax`.
  [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* write `(functionCorrespondingPredicate F P)` as
  `(functionCorrespondingBinaryPredicate F P)` where `P` is binary, and as
  `(functionCorrespondingPredicate F P N)` with `N` the arity of `P` otherwise; a pattern
  `(functionCorrespondingPredicate ?f ?p)` becomes `(functionCorrespondingPredicate ?f ?p ?n)`.
  *Breaks:* `assert` of a two-argument `functionCorrespondingPredicate`, `ask` of one,
  `(variable_arity_predicate functionCorrespondingPredicate)`,
  `(arityMax functionCorrespondingPredicate 3)`

### Breaking: storage

- **A rule quoted in an argument is not found by its connectives.** `find-sentexes` of
  `implies`, `and` or `not` answered a generator, whose consequent quotes a rule, and a
  fact such as `(likes Tom (implies A B))`. Neither is answered now, and `terms` does not
  list the three; the predicates and constants inside the quoted rule still find it.
  *Migration:* a durable store indexed by an earlier release answers the three
  connectives until `(v/reindex kb)`.
  *Breaks:* `find-sentexes` and `find-sentexes-all` of `not`, `and` or `implies`, and
  `terms` and `term-count` over a KB holding a generator.
  [indexing.md](docs/indexing.md#5-the-inverted-term-index)
- **A ground application of a reifiable function can be a literal's predicate**
  ([#274](https://github.com/vaelii/vaelii/issues/274)). `((BloodKinFn siblingOf) Ann Bob)`
  stores its head as the constant `(genl (BloodKinFn siblingOf) siblingOf)` stores its
  argument as, so the fact reaches `siblingOf` through the edge, and an `arg` declared on
  the application or inherited through its edges types the fact's arguments. `assert`,
  `assert-inert` and `check` accept the head under `:naming :strict` and check its inputs
  as they check an argument application's; a compound head that does not reify is refused
  `:naming` as before. A query reifies the head too, so a head that a
  store holds as written from `:naming :warn` or `:off` is not reached by a read.
  [nat.md](docs/nat.md#an-application-as-a-sentences-predicate)
  *Migration:* retract each fact a store holds with a reifiable application as its head,
  and assert it again.
  *Breaks:* a read of a head application stored as written under `:naming :warn` or `:off`

### Breaking: serving

- **`vaelii.serve/app` and `vaelii.web/handler` refuse an address with no token as
  `:unauthorized`.** Built for a `:host` naming an address with no `:token`, no
  `VAELII_API_TOKEN` and, for the daemon, no token table, either handler served every
  route with no bearer check and no `Host` allowlist, which `start` and `-main` refuse.
  The browser's handler with a token checks it on every request.
  [operations.md](docs/operations.md#daemon--vaeliiserve)
  *Migration:* pass `:token`, or set `VAELII_API_TOKEN`, when building either handler for
  an address.
  *Breaks:* `vaelii.serve/app` and `vaelii.web/handler` built for an address with an
  explicit nil `:token`
- **A served write the store copies out of a time slice needs the sliced context in its
  grant** ([#259](https://github.com/vaelii/vaelii/issues/259),
  [#272](https://github.com/vaelii/vaelii/issues/272)). The token-table check names each
  context a slice slices beside the slice for an eternal predicate's fact or denial, a
  slice of a slice written in place included, and beside a `(natFormula K E)` naming a
  slice, with `K` when `contextArgGenlCx` places it. It admits a sentence changing whether
  a predicate is eternal (a membership in `eternal_predicate` or a type below it, a `genl`
  edge up to one, the denial or a `defeat` of either) under an admin grant alone, and a
  `:retract`, `:edit` removal or `:replace-facts` of a sentex only an admin grant writes
  likewise.
  [operations.md](docs/operations.md#daemon--vaeliiserve)
  *Migration:* name the sliced context in a grant that writes an eternal predicate's fact
  into a slice or a `natFormula` naming the slice, and write or remove an eternal
  membership under an admin grant.
  *Breaks:* a served `:assert` of an eternal predicate's fact into a time slice, or of a
  `natFormula` naming a slice, under a grant without the contexts it reaches; of an eternal
  membership or edge, its denial or its `defeat`, and a removal of a sentex only an admin
  grant writes, under a grant that is not an admin's (`:forbidden-context`)

### Refusal: serving

- **The daemon holds `:lookup`, `:query`, `:query?`, `:query-status` and `:argue` to
  `VAELII_MAX_QUERY_MS`, and fills the ceiling into every clocked op's short call.** A
  request naming a larger `:max-ms` is refused `:over-ceiling`, and one naming none runs
  under the ceiling's clock: a query or lookup that reaches it is refused
  `:budget-exhausted`, and `:query-status` reports `:status :timeout`. A `:why-not`,
  `:search-tree`, `:compare-tacticians`, `:ask-within` or `:prove-within` call that omits
  its option map or sends `nil` runs under the ceiling too.
  [operations.md](docs/operations.md#daemon--vaeliiserve)
  *Migration:* name a `:max-ms` at or under the ceiling, or raise `VAELII_MAX_QUERY_MS`.
  *Breaks:* a served `:lookup`, `:query`, `:query?` or `:argue` that ran past the ceiling,
  and a served call to the five ops above that omitted its option map and ran past it
- **The daemon holds `:prove`, `:provable?` and `:prove-within` to
  `VAELII_MAX_QUERY_DEPTH`.** A request naming a larger `:max-depth` is refused
  `:over-ceiling`, and one naming none runs under the ceiling: a `:prove` or `:provable?`
  that depth cut short is refused `:budget-exhausted` with `:status :depth-cut`, and
  `:prove-within` reports `:truncated? true`.
  [operations.md](docs/operations.md#daemon--vaeliiserve)
  *Migration:* name a `:max-depth` at or under the ceiling, or raise
  `VAELII_MAX_QUERY_DEPTH` (`0` lifts it).
  *Breaks:* a served `:prove`, `:provable?` or `:prove-within` naming `:max-depth` over the
  ceiling, and a served `:prove` or `:provable?` whose derivation is deeper than it
- **The daemon holds `:escalate` to `VAELII_MAX_QUERY_MS`.** A request naming a larger
  `:max-ms` is refused `:over-ceiling`, and one naming none, option map or not, runs under
  the ceiling's clock. A climb the clock stops before any level answers returns
  `{:level nil :status :timeout}`.
  [operations.md](docs/operations.md#daemon--vaeliiserve)
  *Migration:* name a `:max-ms` at or under the ceiling, or raise `VAELII_MAX_QUERY_MS`.
  *Breaks:* a served `:escalate` naming `:max-ms` over the ceiling, and one that climbed
  past the ceiling

### Refusal: assert

- **`assert` and `check` refuse an exact start of the real world's present and a dated
  present-tense fact as `:exact-present`** ([#259](https://github.com/vaelii/vaelii/issues/259)).
  In the slice `(CxTimeFn CxRealWorld (IntervalAfterFn W))` and every context below it,
  `(instantEqual W T)` and `(includesInstant X W)` for an X with an end are refused, and so
  is a `genlCx` edge placing a context that holds one under the present. Such a fact was
  stored, and the next clock reading `(instantNotBefore W T)` past it contradicted it.
  [time.md](docs/time.md#the-real-worlds-present)
  *Migration:* state a clock reading as `(instantNotBefore W T)`, and retract a stored
  `instantEqual` or `includesInstant` on the present's start below the present.
  *Breaks:* `assert` of an exact present or a dated present-tense fact in the real world's
  present or below it
- **`assert-inert` refuses a `defeat`, a structural well-formedness problem such as
  `(genl T T)`, an `except` naming no stored sentex and a `do/` form, as `assert` does.**
  Each was stored as an inert record no belief read reached, which `sentexes-in-context`
  listed, `export-text!` wrote as `(set/inert …)` and `load-text!` stored again. The
  refusals read the sentence alone, except the `except` target, which reads the store as
  at `assert`.
  [api.md](docs/api.md)
  *Migration:* retract a stored inert `defeat`, `genl` self-loop, dangling `except` or
  `do/` record before exporting.
  *Breaks:* `assert-inert` and `load-text!` of a `(set/inert …)` holding a `defeat`, a
  `genl` self-loop, an `except` naming no stored sentex or a `do/` form
- **`assert`, `assert-inert` and `check` refuse a `TimeIntersectionFn` of calendar times
  that share no time as `:not-well-formed`**, in the sentence or in the context slot, a
  slice of a slice included. `(TimeIntersectionFn (MonthFn 2000 1) (MonthFn 2000 2))`
  denotes no time, and a slice at it was a context no fact could hold in. Named times are
  not refused.
  [time.md](docs/time.md) ([#259](https://github.com/vaelii/vaelii/issues/259))
  *Migration:* retract a sentence or a slice at an intersection of disjoint calendar times.
  *Breaks:* `assert` of a `TimeIntersectionFn` of disjoint calendar times
- **`assert`, `assert-inert` and `check` refuse a bare `(sentexHandle N)` as `:shape`.**
  The sentence names a stored sentex and states nothing, and `assert` stored it as a
  believed premise that `sentexes-matching` and `handle-of` answered.
  [naming.md](docs/naming.md)
  *Migration:* retract a stored bare `(sentexHandle N)`.
  *Breaks:* `assert` of a bare `(sentexHandle N)`

### Refusal: shape

- **A `.` that is not the rest marker of its list is refused as `:shape`**
  ([#263](https://github.com/vaelii/vaelii/issues/263)). `assert`, `assert-inert`,
  `check`, an import and every read entry point refuse `(p ?x .)`, `(p . A)`, `(p . ?a
  ?b)` and `(p ?x (ListFn .))` in a fact, a rule or a goal, under every `:naming` policy.
  A rest pattern ends a list with `.` and one variable. A sentence holding such a `.` was
  a `:naming` violation of class `:dot-marker`, which `:warn` and `:off` stored.
  [inference.md](docs/inference.md#dotted-rest-patterns)
  *Migration:* write the literal as `(p ?x . ?rest)`, or drop the `.`. An import summary
  counts such a frame under `:refused`, not under `:naming`'s `:dot-marker`.
  *Breaks:* `assert`, `check`, an import or a read of a sentence holding a `.` outside a rest marker; the `:dot-marker` naming class

### Refusal: storage

- **A `reasoners.edn` holding no map, or whose `:reasoners` is not a list, vector or set,
  is refused as `:malformed-manifest`.** `open-kb` read such a file as an empty reasoner
  set, so `:reasoners :stored` registered no reasoner and a named set was refused as a
  `:reasoner-mismatch` against an empty one.
  [storage.md](docs/storage.md#a-directorys-sentinel)
  *Migration:* rewrite the file as `{:reasoners [name …]}`.
  *Breaks:* `open-kb` over a directory whose `reasoners.edn` holds such a value

### Additive: inference

- **An application whose corresponding predicate is not assertible takes the prover's
  value.** A ground application of a `reifiable_function` whose
  `functionCorrespondingPredicate` is `not_assertible` resolves on a read and on a write
  to the one value the prover registry binds, and nothing is minted for it.
  `ForeverProver` answers `(subintervalOf ?i Forever)` and `(includesInstant Forever ?p)`
  at `ask`, in place of two backward rules. An open interval position binds `Forever` too:
  `(includesInstant ?x P)` answers `Forever` beside the intervals the network names.
  [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* none.
- **A forward rule and a conjunction reach the calendar clock**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). The clock is a
  `SupportingProver`: its answer rests on the `(transitive instantBefore)` declaration and
  each stated bound it read, so a forward rule fires on it. An instant ordering or interval
  relation with a variable beside a calendar term, or an interval relation with one beside
  a named interval, waits for a generator to bind the variable, so `[(holiday ?m) (during
  ?m (YearFn 2000))]` answers each holiday month.
  [time.md](docs/time.md#the-calendar-clock)
  *Migration:* none.
- **A calendar term is a node of the interval network, and has a length**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). With `:allen` registered,
  `(MonthFn 2000 1)` or a `DatetimeRangeFn` range is related to every other calendar term
  of its frame by their fields, so a stated `(before Breakfast (MonthFn 2000 1))` answers
  `(before Breakfast (MonthFn 2000 3))`. The duration prover reads a calendar term's
  length as the seconds between its bounds, and `totalDuration` sums it.
  [time.md](docs/time.md#reading-the-kb-and-reading-an-answer-back)
  *Migration:* none.
- **A time slice is ordered under another through the times' points**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). The `subintervalOf` and
  `subtimeOf` orders on `CxTimeFn`'s time read every stated interval relation, instant
  order and bound as links between the two times' start and end points, so `(finishes Q
  H)`, a chain of two `subintervalOf` facts, or a moment linked to a calendar moment
  orders the slices with no `subintervalOf` stated between the two times.
  [time.md](docs/time.md#the-order-over-time-points-vaeliiimplpoint-order)
  *Migration:* none.
- **A slice of a slice is the slice at the intersection, one context**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `(contextArgFold CxTimeFn 1
  TimeIntersectionFn)` in `time.txt` folds `(CxTimeFn (CxTimeFn CxStory A) B)` into
  `(CxTimeFn CxStory (TimeIntersectionFn A B))` before the context slot reifies, so both
  spellings name one `cx/` constant, and the slice at an intersection is ordered under the
  slice at each argument.
  [context-nat.md](docs/context-nat.md#a-slice-of-a-slice-folds-by-declaration)
  *Migration:* none.
- **Two spellings of one calendar time name one time slice**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `(contextArgCalendarSpelling
  CxTimeFn 2)` in `time.txt` respells the slice's time from its extent before the slot
  reifies, so `(CxTimeFn CxStory (DatetimeFn "2000-01"))` and `(CxTimeFn CxStory (MonthFn
  2000 1))`, or a slice at `(InstantFn 2000 1 1 0 0 0)` and one at `(StartFn (MonthFn 2000
  1))`, name one `cx/` constant and see each other's facts in either arrival order.
  [context-nat.md](docs/context-nat.md#two-spellings-of-one-calendar-time-name-one-context)
  *Migration:* none.
- **A `genlCx` between two slices of one monad answers `subtimeOf` between their times**
  ([#259](https://github.com/vaelii/vaelii/issues/259)), and `subintervalOf` where both
  times are `time_interval`s, stated or computed edge alike, with either side open.
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad) *Migration:* none.
- **A slice at a named moment a stated `includesInstant` places inside a named time is
  ordered under that time's slice** ([#259](https://github.com/vaelii/vaelii/issues/259)):
  the order over time points reads `(includesInstant X m)` as `start(X) ≤ m < end(X)`.
  [time.md](docs/time.md#the-order-over-time-points-vaeliiimplpoint-order) *Migration:* none.
- **`tightestStartBoundOf` answers the tightest known lower bound on a start**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). With `:tightest-start-bound`
  registered, `(tightestStartBoundOf W ?t)` answers the stated lower bound on W that every
  other one lies at or before, so a later clock reading `(instantNotBefore W T)` replaces an
  earlier one as the answer, and two unordered bounds give none. `time.txt` declares it
  `not_assertible`; `earliestStartOf` still names the point `EarliestStartFn` names.
  [time.md](docs/time.md#the-tightest-known-lower-bound-on-a-start-tighteststartboundof)
  *Migration:* none.
- **`query`, `query?`, `query-status` and `argue` take `:max-ms`, and `lookup` takes an
  option map.** A clocked `query`, `query?`, `argue` or `lookup` returns its whole answer
  or refuses `:budget-exhausted`, and `query-status` reports `:status :timeout`.
  `query-opt-keys` and `argue-opt-keys` hold `:max-ms`, and `lookup-opt-keys` names
  `lookup`'s one key.
  [anytime.md](docs/anytime.md#the-partial-result-contract)
  *Migration:* none.
- **`prove` and `provable?` take `:refuse-depth-cut?`.** Under `true`, a run its
  `:max-depth` cut short is refused `:budget-exhausted` with `:status :depth-cut`, and the
  run takes the DFS whatever `*query-engine*` names. `prove-opt-keys` holds the key.
  [anytime.md](docs/anytime.md#the-partial-result-contract)
  *Migration:* none.
- **`prove-within` reports `:truncated? true` when `:max-depth` refused a rule.** A run the
  depth bound cut read `:complete` with nothing saying so, on either engine. The key is
  cumulative over `resume`, and the run still reads `:complete` for the depth it was given.
  [anytime.md](docs/anytime.md#the-partial-result-contract)

### Additive: shipped ontology

- **`person` is under `spatial` and disjoint from `situation`.** A person is disjoint from
  every aspatial type, a relation, a context and an organization among them.
  [oe-principles.md](docs/oe-principles.md#broad-under-thing)
  *Migration:* a KB stating one term a person and an organization, or a person and a
  situation, states two terms.
- **`sempiternal` is disjoint from `tangible`, and `syncategorematic` from truth-valued
  relations, contexts and propositions** ([#284](https://github.com/vaelii/vaelii/issues/284)).
  `sempiternal` is under `intangible`; `hollow` is under `causal` and orthogonal to
  `tangible` and `uninterrupted`; `type` is disjoint from `at_least_metatype`; and
  `idempotent` is under `function`, not `relation`. `arity_independent` is a kind of
  relation orthogonal to every `arity_type`, `truth_valued_relation` among its members,
  and no `time_indexed_relation` is one. The starter KB's disjointness audit reads 33,515
  of 39,903 pairs disjoint and 2,285 unknown.
  [oe-principles.md](docs/oe-principles.md#broad-under-thing)
- **A time slice sees the context it slices.** `(contextArgGenlCx F pos)` makes every
  `F`-context a subcontext of its argument at `pos`, and `time.txt` states
  `(contextArgGenlCx CxTimeFn 1)`, so `(CxTimeFn CxStory (YearFn 2000))` sees what
  `CxStory` states, and a slice along a monad under `CxWell` reads `CxChange`'s
  event-calculus rules.
  [context-nat.md](docs/context-nat.md#the-structural-genlcx-producer)
  ([#259](https://github.com/vaelii/vaelii/issues/259))
  *Migration:* a KB that states a fact in a monad and its denial in a slice of that monad
  has both visible in the slice.
- **`holdsAt` answers off the calendar clock's order**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `CxChange`'s inertia rule for a
  started fluent tests for a terminating event between the two moments when `holdsAt` is
  asked, in place of reading a stored `clipped`. A fluent started at `(InstantFn 2000 1 15
  15 0 0)` holds at four o'clock and not past an event the clock orders before six.
  `clipped` and `clippedBefore` are still derived forward.
  [time.md](docs/time.md#what-clipped-can-see)
  *Migration:* retract the started-fluent `holdsAt` rule a store loaded from an earlier
  `CxChange`; with the clock registered, that rule holds a fluent past an event the clock
  orders.
- **`not_assertible` marks a predicate that a prover answers and nothing stores.**
  `assert` refuses a literal or a denial of a predicate a believed `(not_assertible P)`
  marks as `:not-well-formed`. A mark arriving after facts of `P` are stored holds them
  in the `:out` forced set, across a recover, and retracting the mark releases them. The
  upper layer marks every operator the engine answers and never stores, and `unknown`,
  `bravely` and `cautiously` get a definitional block each. `core.txt` states
  `not_assertible` disjoint from the storage marks and the classifiers of stated content,
  and orthogonal to each arity, order and relation-property type.
  [naf.md](docs/naf.md)
  *Migration:* none.
- **structure.txt ships lists, multisets, finite sets and maps as structural terms.**
  `ListFn`, `MultisetFn`, `SetFn` and `MapFn` are unreifiable and variadic, `(SetFn)` is
  the empty set, and the term marks spell each kind canonically: `(SetFn b a a)` stores
  as `(SetFn a b)`, and `(ListFn b a)` stays apart from `(ListFn a b)`. `elementOf`,
  `cardinalityOf`, `multiplicityOf` and `valueAt` read a ground structure, with the
  structure last, and `listOf`, `multisetOf`, `setOf`, `mapOf` and `entryOf`, the
  constructors' corresponding predicates, build one or read one back, with the structure
  first. `provers/StructureProver` answers the nine, comparing elements in the asking
  context's normal form; each is deferred in a forward join and refused as a stored fact.
  A `MapFn` term giving one key two values is refused `:not-well-formed`, and one whose
  argument is not an `EntryFn` term, a `map_entry`, is refused `:arg-type`. Elements,
  entries and keys compare in the asking context's normal form: an open element binds one
  of each, and a map counts its entries, so a context that merges two of its keys reads
  both values and both entries. An open
  structure application in a rule's antecedent or a `prove` or `query` goal is read
  through its corresponding predicate, so `(holds ?k (SetFn 1 2 ?x))` binds `?x` to 1
  and 2 over a stored `(SetFn 1 2)`; `ask` matches it as written, and a deferred literal
  such as `elementOf` computes from the structure its bindings build. The four kinds
  are separated under `data_structure`, which is disjoint from `logical`, `linguistic`,
  `quantitative` and `syncategorematic`.
  So `(implies (and (intersection ?c . ?types) (elementOf ?t (SetFn . ?types))) (genl ?c
  ?t))` reaches every type of an intersection at any arity.
  [nat.md](docs/nat.md#a-data-structure-is-a-structural-term)
  *Migration:* none; every name structure.txt declares is new.
- **`arity_type` holds `quaternary`, `quinary`, `at_least_quaternary` and
  `at_least_quinary`.** `(typeOrthogonal arity_type not_assertible)` and
  `(typeOrthogonal type_type_by_order not_assertible)` derive `not_assertible`'s
  orthogonals to the arity types and to `type`, `metatype` and `meta_metatype`.
  [oe-principles.md](docs/oe-principles.md#classify-before-you-constrain)
  *Migration:* none.
- **`CxTra` ships Discord channel permissions and account-use vocabulary.**
  `communication_channel` names an aspatial, temporal, acausal logical route or shared
  venue for messages, and `discord_channel` specializes that kind.
  `DiscordChannelFn` names a channel by its decimal-string snowflake;
  `ChannelViewFn` names its `VIEW_CHANNEL` access kind. `discordChannelOf` and
  `channelViewOf` are the corresponding predicates. `discordChannelName` states
  renameable, non-unique labels, and `discordAccountId` states many-to-many account
  use. Permission grants take their time from the context and conclude no reading,
  sending, connector delivery or disclosure permission.
  [contexts.md](docs/contexts.md#the-context-topology)

### Additive: vocabulary and reasoning

- **`(functional P)` concludes `(functionalInArg P 2)`.** A core.txt forward rule states
  the definition: `functional` is `functionalInArg` read at position 2, its binary
  spelling. A functional predicate now answers `(functionalInArg P 2)`, and an injection,
  functional through its own rule, is functional in both arguments.
  [glossary.md](docs/glossary.md).
- **Every spec of `time` and every spec of `situation` is time-invariant.** Two
  core.txt forward rules classify `time`, `situation` and each type below either, a
  type stated later included.
- **The shipped relations' rigidity kinds.** The upper and starter vocabularies
  classify relations as time-invariant, time-agnostic or time-varying.
  Types over numbers, expressions, relations and types, every
  metatype, the folk kinds, the meta, logical and type-relation predicates, kinship,
  `madeOf`, `contains`, `length`, `totalDuration`, `overlapDuration`, the integrity
  requirements and the predall placeholders are time-invariant.
  `(genl folk_species time_invariant_relation)`,
  `(genl folk_biological_class time_invariant_relation)` and
  `(genl arity_type time_invariant_relation)` classify those families with one edge
  each. The social relations, `knows`, `livesIn`, `locatedIn`, `eats`,
  `hasCapability`, `asleep`, `awake`, `breathes_air`, `preysOn`, a quantity's sign,
  trend and derivative, `greaterInMagnitudeThan` and the qualitative arithmetic are
  time-varying, and `(genl stuff_type_by_state_of_matter time_varying_relation)` makes
  every phase of matter time-varying. The fifty spatial relations, the six predall
  world-statement cells, `contradicts` and `intangiblePartOf` are time-agnostic. CxSocial and CxTra
  classify their own relations, which CxUniverse does not see.
  `software_service` and `mcp_server` are invariant kinds: serving, and serving over
  MCP respectively, are constitutive rather than changeable roles. This adds no
  software-versioning vocabulary.
  `except`, `exceptWhen` and engine-derived `defeat` are time-varying: their effects
  may apply only within a temporal slice, so they are not eternal declarations.
- **The rigidity kinds of relation.** core.txt partitions `relation` into
  `time_varying_relation` and `possibly_time_invariant_relation`, and the second into
  `time_invariant_relation` and `time_agnostic_relation` (OntoClean's ~R, +R and -R, read
  modally), and core.txt states the three-way partition of `relation` beside the two. Possible invariance is preserved up
  `genl` and time variance down it, so a time-varying genl of a time-invariant type is an
  inherited clash `conflicts` reports. `rigidity_kind` names the three kinds.
- **`eternal_predicate` classifies time-independent truth within a theory.** It is
  below `predicate` and `time_invariant_relation`; `acknowledgedFinding` and
  `declined_rule_macro` are members. Assertions remain revisable, not an immutable
  review history or a temporal sequence of endorsements. The mark adds no engine
  restriction on assertion or retraction.
  A fact of an eternal predicate stated in a time slice is copied into the context the
  slice slices.
  `documentation_predicate` groups `comment`, `implementationNote` and all six
  example/`*ExampleComment` predicates under the eternal kind without making their
  documented sentences eternal. Definition, argument-contract, arity and functional
  declarations are eternal too, and ordinary as well as forced-decontextualized
  predicates inherit that classification.
  `means`, `denotes` and `expresses` are time-agnostic rather than invariant:
  interpretation includes both fixed reference and time-dependent indexicals.
  A one-way forward rule derives eternal unary predicates from invariant membership
  over atemporal things; its converse is not asserted. `sempiternal` is the common genl
  of `atemporal`, `time` and `situation`, and the bridge now reads
  `(genl ?predicate sempiternal)` in place of `(genl ?predicate atemporal)`.
  Fixed math, unit/measure, calendar, interval/instant, whole-extent and event-calculus
  predicates, including `initially`, are eternal. Taxonomy laws are time-agnostic and
  explicitly non-eternal.
  Closure, abducibility and audit-completeness requirements are time-varying and
  non-eternal, while modal classification is eternal. Whole-event actor specializations,
  provenance, biological genealogy and current fixed-region topology are eternal;
  chosen/current kinship and kind-level parts/capabilities are agnostic and non-eternal.
  Algebraic macros, the commutativity family included, are eternal and keep their
  decontextualization marks, so a mark stated in any context holds for every reader. Preservation macros are explicitly non-eternal;
  functional constraints and forced-strength/lifecycle engine contracts remain eternal.
  Equality `sameAs`/`equals`/`different` is eternal, as canonical `rewriteOf` is.
  The time-slice and monad vocabulary, the data structures and their element,
  cardinality, multiplicity and value relations, `properCounterpart`,
  `successorTypeOrder`, `rulePairOf`, `sentex_handle_term` and `syncategorematic` are
  eternal. `CxTimeFn`, `timezone`, `zonedDatetimeOf` and CxTra's computers, virtual
  machines, containers, clusters, networks, namespaces, file path references,
  repositories, pull requests, channels, messages and conceptual works are
  time-invariant. `maxCommonSpec`, `minCommonGenl`, `negates`, `typeLargerThan`,
  `adultFormOf` and `larvalFormOf` are time-agnostic, and `seat` and `construct` are
  time-varying. CxTra's resource-specific access kinds (`readAccessOf`, `writeAccessOf`,
  `shellAccessOf`, `adminAccessOf`, `deployAccessOf`, `mergeAccessOf`, `channelViewOf`,
  `fileLookupOf`) and stable-ID correspondences (`discordChannelOf`, `discordMessageOf`,
  `pullRequestOf`) are time-invariant, and their constructors take that kind through the
  correspondence. `alterOf` and `headmateOf` are time-varying and `carries` time-agnostic.
  `situation_predicate`, below `eternal_predicate`, holds predicates whose first argument
  is a situation that fixes their truth: `actor` and its binary specs, `subSituationOf`,
  `properSubSituationOf` and `toolInvocationArg`. Taking a situation first does not by
  itself make a predicate one.
  A `properCounterpart` pair passes rigidity only in its sound directions: a
  time-invariant or eternal relation has a time-invariant or eternal proper reading,
  and a time-agnostic proper reading has a time-agnostic relation. Time variance reaches
  the proper reading down the `genl` beside each pair, and no blanket two-way
  inheritance is stated.
  No complement type is introduced, and undecided cases are not closed-world negatives.
- **A function takes the rigidity kind of its corresponding predicate.** A generator over
  `rigidity_kind` generates one forward rule per kind, concluding `(?kind ?function)` from
  `(functionCorrespondingPredicate ?function ?predicate ?position)` and
  `(?kind ?predicate)`, a kind the predicate inherits down `genl` included. Each `Pred…Fn` takes its placeholder's
  kind this way. A function believed of a second kind is reported by
  `:rigidity-correspondence`. The rule-clash pairing pairs each two of the three rules,
  and core.txt acknowledges the three pairs with `acknowledgedFinding`, so they are
  `:rule-clash-review` findings.
- **A function and its corresponding predicate must share a rigidity kind.** A default
  `kb-integrity` pass, `:rigidity-correspondence`, reports each
  `functionCorrespondingPredicate` pair whose function and predicate are both classified
  and of different kinds. A pair with an unclassified side is left to
  `:type-specified-violations`.
  [integrity.md](docs/integrity.md#what-a-rigidity-correspondence-finding-means).
- **`temporalIndexArg` and `time_indexed_relation`.** `(temporalIndexArg ?relation
  ?position)` names the argument that carries the time a tuple holds at.
  `(arg temporalIndexArg 1 time_indexed_relation)` types the relation a
  `time_indexed_relation`, which is below `time_invariant_relation` and `at_least_binary`:
  the tuple carries its own time, so nothing can lose it, and a unary relation has no
  other argument for the time to index.
- **`permanentPartOf`, a time-invariant spec of `partOf`.** `partOfRegion` and
  `subSituationOf` are below it, and `tangiblePartOf` is not, since a wheel can come off
  a car. It is transitive and reflexive, and both its positions declare `thing`, as
  `partOf`'s do.
  [glossary.md](docs/glossary.md).
- **`stable_once_true` and `stable_once_false`, two kinds of time-varying relation.** A
  `stable_once_true` relation that holds at a time holds at every later time, and a
  `stable_once_false` relation that fails at a time fails at every later time. Both are
  below `time_varying_relation`, so no time-invariant relation is either. `dead` is
  `stable_once_true` and `alive` is `stable_once_false`. No rule states either
  definition, since the KB has no sentence for a relation holding at a time.
- **`typeAllSpecified`, a classification requirement `kb-integrity` audits.**
  `(typeAllSpecified ?classifier ?indep)` requires every instance of `?indep` to have a
  believed membership in some member of `?classifier` in each eligible defining reader;
  a partition does not satisfy it. Like Specified, the pass excludes proven skeletal-only
  bookkeeping, not native answers whose defining home is unknown, and reports incomplete
  defining support as a gap. The new default category is `:type-specified-violations`. core.txt
  states `(typeAllSpecified rigidity_kind relation)`, and not every shipped relation is
  classified yet, so a default sweep over CxUniverse now answers `:gap` with that one
  requirement.
  [integrity.md](docs/integrity.md#what-a-type-specified-finding-means).
- **A new OE principle, "consistent at each commit".** Assume the KB is consistent, and
  revise a theory in one atomic commit, so consistency and soundness hold at each commit.
  [oe-principles.md](docs/oe-principles.md).

### Additive: canonicalization

- **`distinctInArgAndRest` drops a repeated argument of a function's ground applications
  below the literal.** Under `(commutativeInArgAndRest F 1)` and `(distinctInArgAndRest F
  1)`, `(p (F B A A))` and `(p (F A B))` store as one sentex `(p (F A B))`, and `(p (F A
  A))` stores as `(p (F A))`: the application keeps its functor at any count and is never
  flattened. A declaration arriving after the facts merges their rows, and its retraction
  splits them back.
  [canonicalization.md](docs/canonicalization.md#a-functions-terms-reshaped-by-declaration)
  *Migration:* none.

### Additive: integrity

- **`kb-integrity`'s rule-macro sweep covers `(arg P i C)`.** A stored rule
  `(P ?o1 … ?on)` ⇒ `(C ?oi)`, the other arguments free, distinct variables, restates
  what `entail-arg-type` already derives from the declaration: every argument `i` of a
  true `P`-fact is typed `C`, materialized and retracted with the declaration.
  Reported when `P` has a fixed arity of two or more, `C` is not a term the engine
  interprets, and the rule is visible from CxUniverse.
  [integrity.md](docs/integrity.md#what-a-rule-macro-finding-means).

### Additive: storage

- **A durable fork reopens over a base that gained records since its last mount, and keeps
  its handles.** The reopen was refused as `:fork-base-overlap` once the fork had written
  anything. The fork's index takes in the base's new records and its rules fire over them.
  A base changed below the end the fork recorded, or one that gave a new record a handle
  the fork minted, is refused as before.
  [overlay.md](docs/overlay.md#a-base-that-grew-between-mounts)
- **`open-kb`'s `:fork-dirs` names the directories of a base's durable forks, and the
  base issues none of the handles those forks hold.** A base rebuilt in a later process
  gave the records it gained the handles a durable fork minted over the earlier one. A
  fork records the ranges it mints in; a fork from before this release records them at
  its next mount. `HandleReserving` is the record-store capability behind the option.
  [overlay.md](docs/overlay.md#the-merge-model--record-half)
- **A text export's `digests.edn` or the argument-type pass's owed record that does not
  parse is refused as `:malformed-manifest`.** Each read raised the EDN reader's exception
  with no `:type`. The engine writes its EDN manifests with `*print-length*` and
  `*print-level*` unbound, so a REPL binding either does not truncate one.
  [storage.md](docs/storage.md#a-directorys-sentinel)

### Additive: koinii

- **`:koinii/admin-off-registry` and `:koinii/foreign-context` join the frozen koinii
  surface.** `test/golden/koinii-surface.edn` held 21 of the 23 refusal `:type`s the koinii
  sources raise, so renaming either of the two passed the golden test.
  [troubleshooting.md](docs/troubleshooting.md)

### Additive: browser

- **A literal search naming exactly one term, ignoring case, opens its page**
  ([#264](https://github.com/vaelii/vaelii/issues/264)). `/find?q=muffet` listed `Muffet`
  and `MuffetBowl`, and opens `Muffet` now. Two whole-name matches that differ only in
  case, such as `foo` and `Foo`, keep the list.
  [web.md](docs/web.md)
- **`/` focuses the search box and selects its text**
  ([#281](https://github.com/vaelii/vaelii/issues/281)), outside an input, textarea,
  select or editable region. Ctrl, Cmd and Alt combinations and IME composition are left
  alone. [web.md](docs/web.md)

### Additive: tooling

- **`+with-agents` adds the released `com.vaelii/vaelii-agents` jar to any task**,
  `uberjar` included, as `+with-foreign` adds the plugin's.
  [operations.md](docs/operations.md#container--the-daemon-as-an-image)
  *Migration:* none.
- **One perf run at a time across every clone on the box.** `lein perf` and `lein perf-ab`
  hold `perf-lock` in `VAELII_BOX_STATE_DIR` (default `~/.local/state/vaelii`) instead of
  the clone's `.git/vaelii-matrix/`, so a perf run in a second clone waits for it, or
  exits 75 under `PERF_NO_WAIT=1`.
  [operations.md](docs/operations.md#configuration--every-switch-and-where-it-is-read)
- **`GATE_MAX_CONCURRENT` caps sharded suites across every clone on the box.** A `lein gate`
  test stage and a `lein test-parallel` run outside `lein gate` each hold a `gate-lock.<i>`
  in `VAELII_BOX_STATE_DIR` instead of the clone's `.git/vaelii-matrix/`, so a third suite
  anywhere on the box waits, or exits 75 under `GATE_NO_WAIT=1`. The wait names each
  holder's checkout.
  [operations.md](docs/operations.md#configuration--every-switch-and-where-it-is-read)

### Fix: answers

- **An open pattern over a commuted reifiable application answers in either argument
  order** ([#228](https://github.com/vaelii/vaelii/issues/228)). Under
  `(reifiable_function PairFn)`, `(commutative PairFn)` and a
  `functionCorrespondingPredicate` of `PairFn`, `(natFormula ?k (PairFn Bea ?x))` and the
  goal `(holds (PairFn Bea ?x))` missed the constant of `(PairFn Ada Bea)`, and a
  `rewriteOf` pattern missed a payload written in the other order. Each answers in every
  order the marks allow.
  [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* none.
- **Every name of one equivalence class answers `different` alike.** After a `sameAs`,
  `equals` or `rewriteOf` merge, one name of a class could be exempt from the unique-name
  assumption while the other was not, depending on the spelling the class elected. A
  stated `indeterminate_term` membership exempts every name of its class, and a merge
  naming a skolem lifts the skolem's exemption under every name, a merge of two skolems
  included. The `predAllSpecified` audit reads the same rule, and a context below a
  `different`-guarded firing that sees such a merge holds a guard defeat of its conclusion.
  [predall.md](docs/predall.md#the-identity-exemption)
  *Migration:* none.
- **`terms` and `term-count` leave out the `.` of a rest pattern**
  ([#263](https://github.com/vaelii/vaelii/issues/263)). `terms` lists predicate,
  individual, type and context names, and the argument-type rules in `core.txt` put `.`
  among them; the browser linked `.` to a term page and offered it in
  search.
  [indexing.md](docs/indexing.md#5-the-inverted-term-index)
  *Migration:* a durable store indexed by an earlier release lists `.` until
  `(v/reindex kb)`.

### Fix: order independence

- **A datum an `except` hides through its support that gains a route the `except` does not
  hide fires what rests on it at the excepting context.** A premise stating the hidden
  datum, or a second rule deriving it from an unexcepted fact, moved nothing the settle
  re-chains from, so a rule on the datum, or one a generator derived from it, stayed
  unfired over the facts stated before the route arrived and fired over those stated
  after it.
  [contexts.md](docs/contexts.md)
- **A defeat of a function's permuting mark below a context is read per reader**
  ([#228](https://github.com/vaelii/vaelii/issues/228)). Under `(commutative PairFn)` in
  CxUniverse and its known-true denial in a context below the facts, that context read
  `(holds (PairFn Bea Ada))` in the store's order, so its answers depended on which
  spelling arrived first. The denying context reads each application as written, and a
  context above the denial reads the sorted spelling.
  [canonicalization.md](docs/canonicalization.md#compounds-below-the-literal-sorted)
  *Migration:* none.
- **A defeat of a reifiable function's permuting mark below the facts is read per
  reader** ([#228](https://github.com/vaelii/vaelii/issues/228)). Under
  `(reifiable_function PairFn)` and `(commutative PairFn)` in CxUniverse, a context below a
  known-true denial of the mark read `(holds (PairFn Bea Ada))` under the constant of
  `(PairFn Ada Bea)`, and a denial in the facts' own context still sorted the application.
  The denying context reads the constant of the application as written, and a context
  above the denial reads the sorted constant. A rule firing that applies a reifiable
  function some reader does not believe a mark of was dropped for every reader; each
  reader reads it.
  [nat.md](docs/nat.md#a-reifiable-mark-moving)
  *Migration:* none.
- **A forward rule whose only antecedent is `(disjoint ?a ?b)` fires on the stated pairs
  in every arrival order.** A `genl` edge arriving after the rule fired it on the pair the
  edge specialized, and a stated `disjoint` arriving after the rule and the edge fired it
  on the reversed pair as well. A rule arriving last fired on neither.
  [inference.md](docs/inference.md#a-disjoint-antecedent-reads-the-separations)
- **A conjunction holding an open instant ordering or interval relation answers the same in
  every conjunct order with the point or interval prover registered.** The point prover
  enumerated its network's nodes for `(instantBefore T1 ?i)`, and a calendar moment only a
  `happens` fact names is no node, so `(thereExists (?e ?i) (and (instantBefore T1 ?i)
  (happens ?e ?i)))` failed where the `happens`-first order held. The interval prover did
  the same for `(during M ?m)` beside a calendar term no interval fact names.
  [time.md](docs/time.md#the-points-of-a-temporal-thing)
- **A unit-table row arriving or leaving re-decides an `(unknown S)` whose `S` compares
  two measures.** `(unknown (sameQuantity ?a ?b))` was decided against the unit table the
  rule fired under, so a `dimensionOf` or `conversionFactor` row stated after the firing
  left the conclusion believed while `S` held, and one retracted left it withdrawn.
  [exceptions.md](docs/exceptions.md#five-channels-a-declaration-or-a-fact-reaches-an-exception-through-sideways)
- **A refused firing of a lazy reader stays refused while the taxonomy holds the membership
  it concludes.** A firing that proves a lazy-forward rule's literal and concludes a
  membership `(C x)` the taxonomy holds from the fact `(T x)` it read is blocked, and the
  sweep records it as a refusal. A later re-join of the reader released that refusal
  without the lazy check and stored `(C x)` again. A text reload of the starter stored
  `(at_least_binary implies)` and three like it, which the authored load does not hold; no
  answer moved.
  [inference.md](docs/inference.md#a-lazy-forward-rule)

### Fix: inference

- **An `(unknown S)` that holds blocks each firing of a rule whose firings share one
  antecedent set.** Two firings naming the same facts and `genl` edges with their bindings
  swapped, such as `(inspace ?x) (intime ?y)` met by two individuals through one shared
  supertype, took one guard defeat between them, so the conclusion stayed believed while
  `S` held.
  [naf.md](docs/naf.md#evaluated-in-the-placement-context-not-the-join)
- **A negation-as-failure conjunction runs a conjunct its prover answers only bound after
  the conjunct's binders.** The join ran such a conjunct in canonical order, where an open
  argument answered nothing, so `(unknown (thereExists ?t (and (instantBefore T1 ?t)
  (rang Bell ?t))))` held with a ring stored after `T1`. A conjunct binding an output, a
  result-binding evaluatable or an `argN`, waits only for its inputs, so a conjunct reading
  that output runs after it.
  [naf.md](docs/naf.md#the-conjunction-is-joined-so-its-conjuncts-may-share-a-witness)
- **A dotted literal with a concrete functor matches stored facts of every length.** The
  trie and the argument roots read the `.` of `(p ?c . ?xs)` as an argument, so a goal or
  a rule arriving after its facts matched nothing. The match reads the functor's extent
  and `unify` binds the rest. [nat.md](docs/nat.md#a-data-structure-is-a-structural-term)
- **`overlapDuration` reads a `length` whose lower bound is negative as no length.** A
  stored `(length I (QuantityFn -5 Minute))` rendered `(QuantityIntervalFn 0 -300 Second)`
  for an overlap, an interval whose lower bound passes its upper one, and `totalDuration`
  summed it. [duration.md](docs/duration.md#bounds-not-points)
- **`kb-integrity` reports no `.` as a type `:not-under-thing`, and two rest patterns at
  the same point unify rest with rest** ([#263](https://github.com/vaelii/vaelii/issues/263)).
  `(p . ?a)` with `(p . ?b)` gives `?a=?b`.
  [inference.md](docs/inference.md#dotted-rest-patterns)
- **The constraint-only reading holds no fact whose symbol argument is separated from the
  declared type only over a `:default` `genl` edge.** With `(arg needs 1 dog)`,
  `(disjoint dog mineral)`, a `:default` `(genl rock mineral)` and `(rock Rex)`, `(needs Rex
  Tom)` was held inert under `VAELII_ASSERTIVE_ARG_TYPES=0` and believed under the entailing
  reading. Both readings believe it; a separation over `:monotonic` edges still holds it.
  [argtypes.md](docs/argtypes.md#an-argument-constraint-derives-try-assert-refuses-a-separated-argument)
- **`compare-tacticians` holds every row to one `:max-ms` deadline, and runs a tactician
  named twice once.** Each row took a fresh clock, so a call naming *n* tacticians ran up
  to *n* times its `:max-ms`. [api.md](docs/api.md)

### Fix: shipped ontology

- **`knows` follows from `relativeOf` by a default rule, not a `genl` edge.** Two
  relatives need not have met. A stated `(not (knows ?x ?y))` now overrides the default,
  where the edge made every relative an acquaintance.
  `(declined_rule_macro (genl relativeOf knows))` records the declined suggestion.
  *Migration:* none for a KB that only reads `knows`. A query for the `genl` edge from
  `relativeOf` to `knows` answers no.
- **CxNormalPhysicalConditions states each room-temperature phase as a default rule.** A
  phase is a state a portion of stuff is in, not a kind it is. Four default rules replace
  `(genl stone solid)`, `(genl wood solid)`, `(genl glass_stuff solid)` and
  `(genl mercury liquid)`, and each suggestion is recorded with `declined_rule_macro`.
  *Migration:* none for a KB that reads a portion's phase. A query for one of the four
  `genl` edges answers no.
- **A fluent that held at the outset stops at an event the calendar clock orders before
  the moment asked.** `CxChange`'s `initially` inertia rule read a forward
  `clippedBefore`, which holds no fact about a moment only a `holdsAt` question names. With
  `:calendar` registered, `(holdsAt F (InstantFn 2000 1 15 18 0 0))` held past an event at
  seventeen o'clock that `terminates` F. The rule tests for that event when the question
  is asked.
  [time.md](docs/time.md#what-clipped-can-see)
  *Migration:* retract the `initially` `holdsAt` rule a store loaded from an earlier
  `CxChange`.
- **The inert rule from `(commutativeInArgAndRest ?p 1)` to `(commutative ?p)` leaves a
  unary relation out.** `(commutativeInArgAndRest P 1)` holds vacuously of a unary `P`, and
  a commutative relation is `at_least_binary`. Two inert rules replace the one, requiring
  `(arity ?p ?n)` or `(arityMin ?p ?n)` with `(greaterThan ?n 1)`, as the
  `at_least_binary` floor rules do, so `kb-quality` no longer pairs the bridge with the
  arity-1 and `empty` rules. [canonicalization.md](docs/canonicalization.md)
  *Migration:* a query for the unguarded rule by `handle-of` answers nil.
- **The rule-clash pairing reads a functional slot off the KB's `functionalInArg` marks,
  for any predicate.** Two antecedents filling one marked slot for one tuple with
  two distinct numbers or other non-symbol atoms, with a number a `lessThan` or
  `greaterThan` bound on the other filler excludes, or with two variables whose bounds
  leave nothing between them, cannot both hold, and the pair is dropped. The arity table
  reaches the reading through `(functional arity)`, where the reading named `arity`
  before, and an upper bound now counts beside a lower one. A KB that does not mark
  `arity` functional now pairs `(arity ?p 1)` with `(arity ?p 2)`.
  [integrity.md](docs/integrity.md#what-a-rule-clash-finding-means).

### Fix: storage

- **A fork mints its handles from its base's counter.** A base written while a fork was
  mounted could give a base record and a fork record one handle, and a read in the fork
  then joined the base's index postings to the fork's record. The base's stored counter
  advances with each handle a fork mints. [overlay.md](docs/overlay.md#the-merge-model--record-half)
- **A dump written from the engine's jar names the jar's version as its writer.** With no
  `vaelii.build` or `VAELII_BUILD` set, `meta.edn`'s writer label read the working
  directory's git HEAD, so a dump from the image read `vaelii dev` and a dump from an
  application embedding the jar named that application's commit.
  [operations.md](docs/operations.md#configuration--every-switch-and-where-it-is-read)

### Fix: integrity

- **`kb-integrity` reads a rule's exceptions in the clash's context, through quantifiers**
  ([#262](https://github.com/vaelii/vaelii/issues/262)). A rule clash read as `:excepted`
  in a context that does not see the exception, and a clash whose exception is quantified,
  `(thereExists ?w (and (penguin ?x) …))`, stayed live. The audit reads the exceptions the
  clash's context sees, and the literals under each quantifier and conjunction, and no
  predicate inside quoted data.
  [integrity.md](docs/integrity.md#what-a-rule-clash-finding-means)
- **`defining-contexts` classifies a derived support by the premises it rests on**
  ([#260](https://github.com/vaelii/vaelii/issues/260)). A derivation whose antecedents
  mixed ordinary and skeletal support, or a firing whose literals were all computed, left
  its defining support unclassified, and `specified-violations` reported
  `:incomplete-defining-contexts` for it. The role comes from the asserted leaves the
  valid supports reach: ordinary when any leaf is ordinary, skeletal when every leaf is
  skeletal. A firing naming only computed literals is skeletal support, and a firing's rule
  is not a leaf.
  [predall.md](docs/predall.md#specified-an-integrity-audit-a-caller-runs)

### Fix: performance

- **A write that owes the settle nothing runs no settle pass, and a KB storing no sentence
  of a declaration kind skips that kind's work at each write and read.** A plain fact's
  assert or retract ran every arm of the settle's pass, and each arm found on its own that
  it owed nothing. The settle now asks the arms' conditions once, before the first pass,
  and closes at pass 1 when none holds. A write, a retraction and a read ask one stored
  count, or the taxonomy's mark sets, before reading for argument declarations,
  separations, inherited clashes, route edges, `rewriteOf`, entailing and forced-monotonic
  declarations, functional marks, length bindings, result declarations, `genlInverse` and
  arity classes, and a negated lookup in a store holding no negative fact answers empty
  off one count. Retracting and asserting again 1,000 of 19,998 facts of a transitive
  relation over 10,000 nodes takes 131 ms of CPU against 149 ms; loading 20,000 monotonic
  facts under three assumption rules takes 1.59 s against 1.79 s; a retraction loop over
  1,000 `genl` edges of a 10,000-node DAG takes 75 ms against 96 ms.
  [nmtms.md](docs/nmtms.md#a-settle-that-owes-nothing)
- **A query resolves only its goal's variables, and a forward join prices a `genl` literal
  from the taxonomy's closure and re-plans after a step that leaves one row.** An answer
  dereferenced every variable a derivation bound and kept the goal's; it dereferences the
  goal's alone, and an answer already resolved is its own projection. A negated `ask` over
  1,000 individuals with 100 denied takes 81.5 µs against 91 µs. The forward join priced a
  `genl` literal with one end open from the stored edges, so a leaf read 0 rows and the
  written order decided; it reads the cached closure's size, or one more than the
  relation's active edges, and a conjunction estimates only the conjuncts it reaches with
  a variable unbound. When a step leaves exactly one row and two or more literals remain,
  the join orders them again with the row's values substituted; each literal is still
  joined in its own spelling, and `VAELII_PLAN=0` re-plans nothing.
  [inference.md](docs/inference.md#conjunctive-query-planning-vaeliiimplplan)
- **A rule a preservation, a permuting mark or a transitive walk moves is re-joined once per
  chaining run.** Each datum that moved it owed a full join of its own. 1,024 claims of a
  predicate preserved along `genl`, each with a `genl` edge under it, load beside a rule on
  that predicate in 4.3 ms per pair against 238 ms (`lein perf`'s
  `preserved-reader-load`).
  [inference.md](docs/inference.md#full-re-joins-on-an-arriving-datum-chainrejoin-in-full)
- **A `genl` edge re-decides only the guarded firings whose `genl` pair it can move.** Every
  firing of a rule guarded by a `genl` literal was asked again on every `genl` edge in the
  KB. Beside 1,024 firings of such a rule, each binding a type of its own, a `genl` edge
  between two fresh types takes 4.0 ms against 163 ms (`lein perf`'s
  `genl-edge-beside-guarded-firings`).
  [exceptions.md](docs/exceptions.md#taxonomy-changes-are-keyed-on-what-the-closure-moved)
- **A `genl` edge re-joins a rule with a `genl` antecedent only over the pairs the edge
  adds.** Every `genl` edge re-joined each such rule over its extent. The join now starts
  from the types below the edge or above it, and a rule whose constant side the edge does
  not reach is not re-joined. Beside 1,024 types under a rule's `genl` antecedent, a `genl`
  edge between two fresh types takes 0.7 ms against 39 ms (`lein perf`'s
  `genl-edge-beside-a-closure-antecedent-extent`), and the starter loads in 23 s against
  34 s. [inference.md](docs/inference.md#a-genl--genlcx-antecedent-reads-the-closure)
- **A sufficient-definition walk asks each ground conjunct once, and its fast-fail reads only
  the types declaring a necessary.** Each condition the walk read asked its conjuncts
  again, so an ask at a type above `integer` asked `(integer a)` once per sign class, and
  each of those asks walked the sign classes again. Beside 128 sufficient definitions
  conditioned on one type, a membership ask above that type takes 2.0 ms against 216 ms
  (`lein perf`'s `membership-ask-above-shared-sufficient-conditions`). Below a chain of 512
  types declaring no necessary, an ask takes 0.16 ms against 7.7 ms
  (`membership-ask-below-a-chain-declaring-no-necessary`). The starter recovers in 0.7 s
  against 1.7 s. [defns.md](docs/defns.md#query-time-the-condition-is-evaluated-not-only-matched)
- **A settle pass checks each nogood and guard placement for a duplicate justification with
  one hash probe.** `chain/place-nogoods!` binds the justification dedup index for its
  pass, as `chain/chain` does for a run; each placement had scanned every support its
  conclusion already held. On a term asserted an `animal` and then a
  `fixed_arity_predicate` over the starter, the probe cut the second write from 228 s to
  83 s on a loaded box; with the cover routes the Breaking membership-nogood entry leaves
  out, the write takes 6.5 s. [inference.md](docs/inference.md#what-a-run-pays-per-witness-chainagenda-arrivals)
- **A `genl` edge added above many types places their membership nogoods in a quarter of
  the time.** Each link a descending placement climbs searched its source's whole
  up-closure and rebuilt each type's steps; the search now steps only toward its target,
  and a placement pass reads each type's steps once per reading. Over 300 types under a
  300-level ancestry the edit takes 3.4 s of CPU against 13.0 s.
  [nmtms.md](docs/nmtms.md#the-placement-pass)
- **A `genlCx` edge whose lower side stores nothing re-checks no guarded firing.** A new
  empty context under CxWell re-decided the guard defeats of every guarded firing above
  it. When no context below the edge stores a sentex, each context there sees the upper
  side's content and nothing more, so no guard reads differently and the edge queues no
  watched rule.
  [exceptions.md](docs/exceptions.md#taxonomy-changes-are-keyed-on-what-the-closure-moved)
- **A `genl` edge between types no claim names re-joins no rule on a transitive predicate
  preserved along `genl`.** A `(transitive P)` declaration made every edge move `P`'s
  readers whatever the edge's terms. Beside 1,024 claims of such a predicate and a rule on
  it, a `genl` edge between two fresh types takes 3.3 ms against 127 ms (`lein perf`'s
  `genl-edge-beside-transitive-claims`).
  [inherit.md](docs/inherit.md#forward-chaining-on-a-claim-nobody-stored)
- **An `except` re-chains none of the facts under an edge its target's firings name.** The
  facts outside the target's consequence closure that those firings name are re-chained
  alone; an edge among them had re-chained every fact under it. With 1,024 facts under such
  an edge, an `except` asserted and retracted takes 10.5 ms against 151 ms (`lein perf`'s
  `except-beside-facts-under-an-edge`).
  [contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree)
- **A link fact reaching a calendar moment pairs the slices a calendar comparison can order,
  not every slice of the context function.** The calendar index, an `IndexStore` family,
  files each fact naming a time under its functor and the month of each of its points, and
  the context-NAT producer reads the months between the arriving side's calendar bounds for
  the functors of context-NAT maps and link facts. Over 800 day slices a link from a named
  interval's end to a calendar moment takes 44.7 ms against 1,326 ms (`lein perf`'s
  `context-nat-calendar-link-append`). Facts of other functors naming a time in those
  months add no read (`context-nat-calendar-link-beside-timestamps`).
  [context-nat.md](docs/context-nat.md) ([#259](https://github.com/vaelii/vaelii/issues/259))
  *Migration:* none; a durable index at an earlier layout is rebuilt from its records at
  the first open.
- **A first read of a time slice nobody wrote into costs at most 1.21x as much beside 40x
  the monads.** A first ask in an unwritten month slice along one monad, beside 400 other
  monads holding contexts at the same twenty years, costs 1.01x-1.21x what it costs beside
  10, against 1.91x (`lein perf`'s `context-nat-read-unwritten-slice-beside-monads`). The
  index files each `natFormula` map by argument position at index layout 20.
  [context-nat.md](docs/context-nat.md), [indexing.md](docs/indexing.md#the-natformula-arguments)
  *Migration:* none; a durable index at an earlier layout is rebuilt from its records at
  the first open.
- **`edit-records!` reads and deletes the records it removes a chunk at a time, and the
  placed verdicts read only the `contradicts` records the nogood informant holds IN.**
  `record-edit/apply!` read each removed record and each seed with its own `get-sentex`,
  and deleted each removed record and each dead justification with its own write, a round
  trip apiece over a server. It hints the store a chunk at a time for the reads, and hands
  `capabilities/delete-sentexes` and `delete-justifications` 1,000 handles at a time
  through the new optional `BulkDeleting` protocol, which the postgres and sqlite adapters
  implement; a store without it deletes one at a time as before. The placed verdicts read
  every stored `contradicts` record before asking the TMS whether it was IN; they ask the
  TMS first and read the rest a hinted chunk at a time.
  [storage.md](docs/storage.md#bulkdeleting--the-deletes-a-record-surgery-makes)
- **`disjointness-audit` prepares taxonomy reads once per row**
  ([#279](https://github.com/vaelii/vaelii/issues/279)). Each row holds its
  first type's global ancestor and descendant sets and contextual disjointness predicate.
  Pair statuses, witnesses, ordering and facts-only queries retain their existing reading.
  The audit releases the prepared references after each row.

### Fix: browser

- **The sandbox cookie carries `Secure` behind a proxy that terminated HTTPS.** The flag
  read the connector's scheme, which is `http` behind the TLS-terminating proxy
  operations.md prescribes for a public bind, while the origin check beside it read
  `X-Forwarded-Proto`. Both now read the forwarded scheme.
  [web.md](docs/web.md#somewhere-safe-to-be-wrong)

### Internal

- **`VAELII_TEST_TMPDIR` sets the test JVM's `java.io.tmpdir`**, so every store a test
  builds is created there, not only the `^:fuzz` probes.
  [operations.md](docs/operations.md#developer--the-suite-and-the-scripts)
- **The image fetches the Leiningen launcher at tag 2.12.0 and checks its sha256.** The
  `LEIN_VERSION` and `LEIN_SHA256` build arguments name the tag and its digest, and a
  launcher with another digest fails the build. `lein lint`'s `versions` stage fails when
  `project.clj` names two `slf4j-nop` versions, and `lein gate`'s uberjar stage loads
  `vaelii.host.serve` and `vaelii.web` beside `vaelii.core`.
- **`lein lint`'s `drift` stage reads four more things.** E16 fails an allowlist entry
  whose definition calls no `reads/…-global` entry point, E9 reads the shipped KB's text
  files for `@todo`, E15 fails a `*Breaks:*` token split across two lines in any section,
  and W3 warns on a backticked name ending in `!` or `?`, or of three or more kebab
  segments, that no symbol or keyword under `src/`, `test/` or `bench/` spells.
- **The `args`→`argAndRest` forward rule moved from `core.txt` to the new
  `kb/upper/interface-rules.txt`**, loaded with the rest of the upper ontology by
  `core-context/load-into`. Test fixtures: `tu/fresh` loads it; the new `tu/empty-kb` is
  rule-free.
- **The run scripts count `resources/`, `bench/` and the project files as dirty; coverage
  runs in two passes over several JVMs; and CI fails a green run slower than develop's
  weights.** A result's revision line names its tree dirty when a file under those paths
  differs from HEAD (`REVISION_PATHS`), and the owed lists name the files under them.
  `scripts/coverage.sh` runs seven namespaces in one JVM, then the rest in `--jobs` JVMs
  with the forms the first pass hit left unprobed, under a probe that stops counting a
  form after its first hit, and merges the hits into one report. The weights job divides
  each namespace's time by its shard's median ratio. It fails a namespace at twice its
  weight and 60 s over it, which its shard first runs again and times at the smaller of
  the two runs, and fails the two legs when both reach 1.25 times the median. It is not a
  required check.

## 0.32.0 — 2026-11-03 — "Every context sees CxUniverse, a denial undercutting a `:default` edge's reading, a `genl` cycle refused where its context sees it, `CxTimeFn` slices at ranges and moments, time zones and calendar distances, `replace-facts!`, explanations in content form"

**76 entries** — 14 Breaking, 1 Refusal, 28 Additive, 31 Fix, 2 Internal. Every
context sees CxUniverse, and `(genlCx CxUniverse X)` is refused. A denial of a supertype
membership undercuts a `:default` `genl` edge's reading of it, a `genl` cycle is refused
only where the asserting context sees it, and `why`, `why-not` and `argue` answer in
content form. `CxTimeFn` slices are ordered at `DatetimeRangeFn` ranges, `InstantFn`
moments and named intervals with stated bounds, and the calendar prover reads UTC offsets,
named zones and `temporalDistance` over a calendar moment. A commuted reifiable application
has one constant, `replace-facts!` is new, `edit-records!` adds premises, and an `except`
naming a mint rule is refused `:mint-rule`. CxSocialExtension is merged into CxTra, and the
Allen and RCC-8 algebra facts are inert.

*Breaks:* `sees?`, `context-up`, `ask`, `query`, `assert`, `(genlCx CxUniverse X)`,
`argue`, `:default`, `CxTimeFn`, `DatetimeRangeFn`, `handle-of`, `meetFunctionOf`, `ask?`,
`includesInstant`, `startOf`, `endOf`, `temporalDistance`, `subintervalOf`,
`partOfRegion`, `reflexive`, `try-assert`, `genl`, `covering`, `genl?`, `genls`, `specs`,
`specified-violations`, `all-specified-violations`, `kb-integrity`, `sentexes-matching`,
`symmetric`, `reifiable_function`, `exceptWhen`, `quotedArg`, `quotedArgAndRest`,
`CxSocialExtension`, `(except (sentexHandle H))`, `:type`, `:not-indexable`,
`edit-records!`

## 0.31.0 — 2026-10-30 — "Separations that lose to a stronger denial, lazy-forward rules and a computed `nonempty`, forks that pull a newer base and merge peers' deltas, content digests across seats, `CxTimeFn` slices ordered across monads"

**69 entries** — 15 Breaking, 3 Refusal, 16 Additive, 33 Fix, 2 Internal. A separation
keeps the strength it was written at and loses to a stronger denial, and `argue` answers
`:false` for the loser of a placed nogood. `set/lazyForwardRule` stores a rule whose
conclusions a forward rule's join reads, and `(nonempty C)` is answered from a believed
member. A fork pulls a newer dump as its base with `import!`'s `:rebase?`, publishes its
own writes as a delta a peer merges, and names a sentex and a dispute by a content digest
equal across seats. `CxTimeFn` slices are ordered when they differ in both arguments and
along a `genlCx` path between monads, a store records its reasoner set, and a release
records its renames as data for `upgrade --sync`.

*Breaks:* belief, `conflicts` and `contradictions` under a denial of a separation, over a
`disjoint` between `genl`-related types, and through a `:default` `covering`'s part edges,
`argue`'s `:verdict` for the loser of a disjointness, functionality or other definitional
clash, `why` and `supporting-justifications` `:informant` of a minted type, sentex counts
of a KB that mints, `retract!` of one of the eleven rules, sentex counts of the starter
and of a KB whose forward rules read `arity`, `:engines` of the shipped arity converse,
`edit-records!` of a lazy-forward rule, `ask` and `query` of `(nonempty C)`, firings of a
rule reading `nonempty`, `sees?`, visibility and belief between `CxTimeFn` contexts that
differ in both arguments, and between slices of two monads a `genlCx` path orders,
`try-assert` of a calculus fact that contradicts the stored network, `ask`, `query`,
`conflicts`, `try-assert` of a unary predicate's membership over an argument outside the
removed declaration's type, `open-kb` over a store a KB called `add-reasoner` on, and
`import!` of such a KB's dump, without `:reasoners`, the files and the `:skipped` count
`export-text!` writes for a KB holding a sentence that names a handle, `assert` and
`assert-inert` of an `(except S)`, a koinii reply act holding a sentence at its target
position, or a function term holding an `(ist Cx S)` at its function's reference position,
which stored the sentence as written, `vaelii.koinii.dispute/dispute-id` at one argument,
`dispute-state`, `standing-rulings` and `who-ruled` over marks and rulings stored under
handle ids, `dispute-term`, `mark-notified`, `mark-stale`, `reopen!` and
`adjudication/rule` called with a handle seq, `adjudication/rule` upholding a sentence
that is neither a side nor a side's negation, which stored the ruling, `adjudication/rule`
by a party after another arbiter's ruling cleared the clash, a caller of
`vaelii.koinii.deref/->SentexRef`, `vaelii.koinii.deref/resolve-by-locator`,
`vaelii.koinii.deref/locator-index`, `watch` and the daemon's `watch` op on a calculus
predicate, either polarity, `add-reasoner` of a calculus answering a standing watch's
goal, `scripts/start-vaelii*.sh`, `scripts/upgrade-kb.sh` and `scripts/test-full-kb.sh`
under a `VAELII_HEAP` above physical memory, `assert` of a `target_following_predicate`
meta naming a sentence nothing stores, `:unresolved-reference`, `sentexes-matching` of the
`parentOf` conclusions `CxKinship`'s rules stored from `fatherOf` and `motherOf` facts

## 0.30.0 — 2026-10-27 — "Chaining writes rolled back at `:max-derivations` and a full heap, `why` as a justification graph, `functionCorrespondingPredicate` scoped to the reader, `kb-integrity`'s stranded declarations and rule clashes, `CxTimeFn` time slices"

**125 entries** — 19 Breaking, 1 Refusal, 31 Additive, 68 Fix, 6 Internal. Forward chaining
bounds term nesting with `:max-term-depth` and has no default derivation depth or derivation
cap, and a chaining write past `:max-derivations` or over a full heap is refused
`:interrupted` and rolled back. `functionCorrespondingPredicate` respells only where the
reader's ancestor set holds the declaration, and a `:default` corresponding fact resolves
nothing. `why` returns a justification graph as `{:root h :nodes {…}}`, and `kb-integrity`'s
default sweep adds `:stranded-declaration` and live rule clashes and reports `:work` and
`:elapsed-ms` on every answer. A wire write naming `:principal` is refused 403, and
`VAELII_MAX_QUERY_DEPTH` holds only the four clockless reads. `CxTimeFn` time slices,
`associative`, `idempotent`, `meetFunctionOf` and the `VAELII_TOKEN_TABLE` and
`VAELII_MAX_WRITE_MS` switches are new.

*Breaks:* `default-chain-opts`' keys, `assert`, `try-assert`, `assert-rule`, `assert-many`,
`edit!`, `edit-with-consequences!`, `forward-chain` and `preview` without `:max-depth` or
`:max-derivations`, `edit-with-consequences!` with `:max-derivations`, `forward-chain` and
the daemon's `:forward-chain` op with `:max-derivations` or a throwing `:on-progress`,
`:interrupted`, `edit-with-consequences!` that kept the conclusions placed before a full
heap stopped them, `forward-chain` that ran to its fixpoint over a full heap, `assert` of an
application beside a `:default` corresponding fact, `assert` of a `:default` corresponding
fact, `why` of a projection or a merge, `ask` of a corresponding predicate under two
declarations of one function, `assert` of a rule applying a function declared outside its
context's ancestor set, `prove`, `query` at `CxInference`, `CxEverything` or a variable
context, `assert` of a rule whose consequent names an application, `query`, `ask`,
`possible-relations`, `qualitative-network` `:unsatisfiable-sources`, forward firings over a
calculus antecedent in a context with a contradiction, `defeat-class` of a firing of a
minted rule, `intersection` membership class, `violations` `:arg-type` entries of a firing,
`args`, `check`, `why`, `why`'s `:max-depth`, `argue`'s `:for-why` and `:against-why`,
`vaelii.client/why`, the CLI's `why` output, `:principal`, `:add-provenance`,
`VAELII_MAX_QUERY_DEPTH` at `:prove`, `:provable?`, `:prove-within`, `:why-not`,
`:search-tree` and `:compare-tacticians`, `kb-integrity`, `kb-integrity`'s `:audited` and
`:gap` answers, `vaelii.client/kb-integrity`, `all-specified-violations`, `assert` of `arg`,
`genlArg`, `interArg`, `interArgEqual`, `argArg` and `arg1`…`arg5`, `ask?`, `handle-of` and
`sentexes-matching` over a ground compound below the literal whose functor is `symmetric` or
commuting, against a store written before; a goal or rule antecedent whose commuting
compound below the literal holds a variable and is written out of canonical order, the
corpus card's `:max-derivations` default of 100,000, `:not-well-formed`, `transitive`,
`inverse`, `genlInverse`, `closedExtentForArg`, `information_bearing_thing`

## 0.29.0 — 2026-10-23 — "Open applications read through `functionCorrespondingPredicate` and resolved under the reader's merges, `try-assert` refusing `:monotonic` complements and length clashes, query-only terms refused under `not`, closed-extent negatives re-checked in every arrival order"

**56 entries** — 6 Breaking, 9 Refusal, 6 Additive, 32 Fix, 3 Internal. A rule's or a
goal's open application of a `reifiable_function` is read through the function's
`functionCorrespondingPredicate`, and an application resolves under the merges the reading
or storing context sees. `try-assert` refuses a believed `:monotonic` complement, a fact or
declaration that breaks a length binding, and an `irreflexive` or `anti_symmetric` tuple.
`assert` refuses `not` over a query-only term, `(not (or …))`, `set/monotonic` and
`set/inert` inside a sentence, and a length binding against an engine term's shape or a
term's spelling. Closed-extent negatives are re-checked under `unknown`, `exceptWhen` and
an aggregate body, and `edit-records!`, `settle-record-edits!` and `lein cli upgrade
--sync` edit and sync a stored KB in place.

*Breaks:* `assert` of a rule naming an application, `prove`, `query`, `kb-integrity`,
`ask` and every read entry point over an application of a `reifiable_function`, `assert`
of one, `sameAs`, `equals`, `rewriteOf`, `assert` of a `modal_predicate` sentence naming
an application of a `reifiable_function`, `ask` of `believes` over one, `kb-quality`,
`dispute/dispute-term`, `(dispute …)`, `:not-well-formed`, `unknown`, `forall`,
`not well-formed: `, `:refused`, `set/inert`, `set/monotonic`, `:shape`,
`:length-against-shape`, `:length-against-spelling`, `arity`, `arityMin`, `bravely`,
`cautiously`, `:naming`, `import!`, `try-assert`, `:complement`, `:arity`, `:irreflexive`,
`:anti-symmetric`, a KB holding a rule that concludes `P` from a closed-extent
`(not (P …))` beside a `closed_extent_predicate` or `closedExtentForArg` grant on `P`

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
`arg-scoped-members`, `arg-scoped-intersect`, `arg-agnostic-members`,
`arg-agnostic-count`, `watch`, `lein cli`, `read-arg`, `--format`

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
