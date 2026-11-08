# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.32.0 are summarized rather than reproduced.** Each one
keeps its title and its class census, and each one from 0.14.0 on keeps every
`*Breaks:*` token, so an upgrade across those releases is still a grep for the name you
call; 0.8.0 through 0.13.0 keep a subset. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking: storage

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

### Fix: ontology names

- **`largerThan` is `typeLargerThan`.** The relation compares two kinds, as a
  `type_relation_predicate`, and the new name keeps it from reading as a sibling of
  `tallerThan` and `heavierThan`, which compare two individuals. Its declarations, its
  facts in CxSize and its comment are unchanged apart from the name.

  *Migration:* write `typeLargerThan` for `largerThan` in every fact, rule and query.

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

### Fix: contextual type definitions

- **The starter text declares each type's unary arity in its defining context.**
  Loading the starter no longer invents CxUniverse premises for types defined only in
  a middle theory. Defining-context audits therefore keep those types' obligations in
  readers of their actual theory. The computed closing type batch and its synthetic
  `:unary-predicates` load phase are removed; starter synchronization reads the authored
  layers directly.

### Additive: vocabulary and reasoning

- **The rigidity kinds of relation.** core.txt partitions `relation` into
  `time_invariant_relation`, `time_agnostic_relation` and `time_varying_relation`
  (OntoClean's +R, -R and ~R, read modally), with `possibly_time_invariant_relation` the
  first two together. Possible invariance is preserved up `genl` and time variance down
  it, so a time-varying genl of a time-invariant type is an inherited clash `conflicts`
  reports. `rigidity_kind` names the three kinds.

- **`eternal_predicate` classifies time-independent truth within a theory.** It is
  below `predicate` and `time_invariant_relation`; `acknowledgedFinding` and
  `declined_rule_macro` are members. Assertions remain revisable, not an immutable
  review history or a temporal sequence of endorsements. The mark adds no engine
  restriction on assertion or retraction.
  Cross-time propagation is not supplied by this declaration; engine support and
  temporal regressions are tracked in [#272](https://github.com/vaelii/vaelii/issues/272).
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
  time-varying.
  A `properCounterpart` pair passes rigidity only in its sound directions: a
  time-invariant or eternal relation has a time-invariant or eternal proper reading,
  and a time-agnostic proper reading has a time-agnostic relation. Time variance reaches
  the proper reading down the `genl` beside each pair, and no blanket two-way
  inheritance is stated.
  No complement type is introduced, and undecided cases are not closed-world negatives.


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


- **A function and its corresponding predicate must share a rigidity kind.** A default
  `kb-integrity` pass, `:rigidity-correspondence`, reports each
  `functionCorrespondingPredicate` pair whose function and predicate are both classified
  and of different kinds. A pair with an unclassified side is left to
  `:type-specified-violations`.
  [integrity.md](docs/integrity.md#what-a-rigidity-correspondence-finding-means).


- **Every spec of `time` and every spec of `situation` is time-invariant.** Two
  core.txt forward rules classify `time`, `situation` and each type below either, a
  type stated later included.


- **`temporalIndexArg` and `time_indexed_relation`.** `(temporalIndexArg ?relation
  ?position)` names the argument that carries the time a tuple holds at.
  `(arg temporalIndexArg 1 time_indexed_relation)` types the relation a
  `time_indexed_relation`, which is below `time_invariant_relation` and `at_least_binary`:
  the tuple carries its own time, so nothing can lose it, and a unary relation has no
  other argument for the time to index.


- **A function takes the rigidity kind of its corresponding predicate.** A generator over
  `rigidity_kind` generates one forward rule per kind, concluding `(?kind ?function)` from
  `(functionCorrespondingPredicate ?function ?predicate ?position)` and
  `(?kind ?predicate)`, a kind the predicate inherits down `genl` included. Each `Pred…Fn` takes its placeholder's
  kind this way. A function believed of a second kind is reported by
  `:rigidity-correspondence`. The rule-clash pairing pairs each two of the three rules,
  and core.txt acknowledges the three pairs with `acknowledgedFinding`, so they are
  `:rule-clash-review` findings.


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


- **A new OE principle, "consistent at each commit".** Assume the KB is consistent, and
  revise a theory in one atomic commit, so consistency and soundness hold at each commit.
  [oe-principles.md](docs/oe-principles.md).


- **`(functional P)` concludes `(functionalInArg P 2)`.** A core.txt forward rule states
  the definition: `functional` is `functionalInArg` read at position 2, its binary
  spelling. A functional predicate now answers `(functionalInArg P 2)`, and an injection,
  functional through its own rule, is functional in both arguments.
  [glossary.md](docs/glossary.md).


### Additive: integrity

- **`kb-integrity`'s rule-macro sweep covers `(arg P i C)`.** A stored rule
  `(P ?o1 … ?on)` ⇒ `(C ?oi)`, the other arguments free, distinct variables, restates
  what `entail-arg-type` already derives from the declaration: every argument `i` of a
  true `P`-fact is typed `C`, materialized and retracted with the declaration.
  Reported when `P` has a fixed arity of two or more, `C` is not a term the engine
  interprets, and the rule is visible from CxUniverse.
  [integrity.md](docs/integrity.md#what-a-rule-macro-finding-means).


### Fix: shipped ontology and rule clashes

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

- **The rule-clash pairing reads a functional slot off the KB's `functionalInArg` marks,
  for any predicate.** Two antecedents filling one marked slot for one tuple with
  two distinct numbers or other non-symbol atoms, with a number a `lessThan` or
  `greaterThan` bound on the other filler excludes, or with two variables whose bounds
  leave nothing between them, cannot both hold, and the pair is dropped. The arity table
  reaches the reading through `(functional arity)`, where the reading named `arity`
  before, and an upper bound now counts beside a lower one. A KB that does not mark
  `arity` functional now pairs `(arity ?p 1)` with `(arity ?p 2)`.
  [integrity.md](docs/integrity.md#what-a-rule-clash-finding-means).


- **The inert rule from `(commutativeInArgAndRest ?p 1)` to `(commutative ?p)` leaves a
  unary relation out.** `(commutativeInArgAndRest P 1)` holds vacuously of a unary `P`, and
  a commutative relation is `at_least_binary`. Two inert rules replace the one, requiring
  `(arity ?p ?n)` or `(arityMin ?p ?n)` with `(greaterThan ?n 1)`, as the
  `at_least_binary` floor rules do, so `kb-quality` no longer pairs the bridge with the
  arity-1 and `empty` rules. [canonicalization.md](docs/canonicalization.md)

  *Migration:* a query for the unguarded rule by `handle-of` answers nil.


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

### Refusal: serving

- **The daemon holds `:escalate` to `VAELII_MAX_QUERY_MS`.** A request naming a larger
  `:max-ms` is refused `:over-ceiling`, and one naming none, option map or not, runs under
  the ceiling's clock. A climb the clock stops before any level answers returns
  `{:level nil :status :timeout}`.
  [operations.md](docs/operations.md#daemon--vaeliiserve)
  *Migration:* name a `:max-ms` at or under the ceiling, or raise `VAELII_MAX_QUERY_MS`.
  *Breaks:* a served `:escalate` naming `:max-ms` over the ceiling, and one that climbed
  past the ceiling
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

### Additive: canonicalization

- **`distinctInArgAndRest` drops a repeated argument of a function's ground applications
  below the literal.** Under `(commutativeInArgAndRest F 1)` and `(distinctInArgAndRest F
  1)`, `(p (F B A A))` and `(p (F A B))` store as one sentex `(p (F A B))`, and `(p (F A
  A))` stores as `(p (F A))`: the application keeps its functor at any count and is never
  flattened. A declaration arriving after the facts merges their rows, and its retraction
  splits them back.
  [canonicalization.md](docs/canonicalization.md#a-functions-terms-reshaped-by-declaration)
  *Migration:* none.

### Additive: inference

- **`query`, `query?`, `query-status` and `argue` take `:max-ms`, and `lookup` takes an
  option map.** A clocked `query`, `query?`, `argue` or `lookup` returns its whole answer
  or refuses `:budget-exhausted`, and `query-status` reports `:status :timeout`.
  `query-opt-keys` and `argue-opt-keys` hold `:max-ms`, and `lookup-opt-keys` names
  `lookup`'s one key.
  [anytime.md](docs/anytime.md#the-partial-result-contract)
  *Migration:* none.

### Additive: shipped ontology

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

### Additive: tooling

- **`+with-agents` adds the released `com.vaelii/vaelii-agents` jar to any task**,
  `uberjar` included, as `+with-foreign` adds the plugin's.
  [operations.md](docs/operations.md#container--the-daemon-as-an-image)
  *Migration:* none.

### Fix: inference

- **`compare-tacticians` holds every row to one `:max-ms` deadline, and runs a tactician
  named twice once.** Each row took a fresh clock, so a call naming *n* tacticians ran up
  to *n* times its `:max-ms`. [api.md](docs/api.md)

- **A dotted literal with a concrete functor matches stored facts of every length.** The
  trie and the argument roots read the `.` of `(p ?c . ?xs)` as an argument, so a goal or
  a rule arriving after its facts matched nothing. The match reads the functor's extent
  and `unify` binds the rest. [nat.md](docs/nat.md#a-data-structure-is-a-structural-term)

- **`kb-integrity` reports no `.` as a type `:not-under-thing`, and two rest patterns at
  the same point unify rest with rest** ([#263](https://github.com/vaelii/vaelii/issues/263)).
  `(p . ?a)` with `(p . ?b)` gives `?a=?b`.
  [inference.md](docs/inference.md#dotted-rest-patterns)

### Fix: answers

- **`terms` and `term-count` leave out the `.` of a rest pattern**
  ([#263](https://github.com/vaelii/vaelii/issues/263)). `terms` lists predicate,
  individual, type and context names, and the argument-type rules in `core.txt` put `.`
  among them; the browser linked `.` to a term page and offered it in
  search.
  [indexing.md](docs/indexing.md#5-the-inverted-term-index)
  *Migration:* a durable store indexed by an earlier release lists `.` until
  `(v/reindex kb)`.

### Fix: shipped ontology

- **A fluent that held at the outset stops at an event the calendar clock orders before
  the moment asked.** `CxChange`'s `initially` inertia rule read a forward
  `clippedBefore`, which holds no fact about a moment only a `holdsAt` question names. With
  `:calendar` registered, `(holdsAt F (InstantFn 2000 1 15 18 0 0))` held past an event at
  seventeen o'clock that `terminates` F. The rule tests for that event when the question
  is asked.
  [time.md](docs/time.md#what-clipped-can-see)
  *Migration:* retract the `initially` `holdsAt` rule a store loaded from an earlier
  `CxChange`.

### Fix: storage

- **A fork mints its handles from its base's counter.** A base written while a fork was
  mounted could give a base record and a fork record one handle, and a read in the fork
  then joined the base's index postings to the fork's record. The base's stored counter
  advances with each handle a fork mints. [overlay.md](docs/overlay.md#the-merge-model--record-half)

### Internal

- **The `args`→`argAndRest` forward rule moved from `core.txt` to the new
  `kb/upper/interface-rules.txt`**, loaded with the rest of the upper ontology by
  `core-context/load-into`. Test fixtures: `tu/fresh` loads it; the new `tu/empty-kb` is
  rule-free.

## 0.32.0 — 2026-11-03 — "Every context sees CxUniverse, a denial undercutting a `:default` edge's reading, a `genl` cycle refused where its context sees it, `CxTimeFn` slices at ranges and moments, time zones and calendar distances, `replace-facts!`, explanations in content form"

| Area | Change |
|---|---|
| contexts | every context sees CxUniverse, and `(genlCx CxUniverse X)` is refused; `CxTimeFn` slices at a `DatetimeRangeFn` range, an `InstantFn` moment and a named interval with stated bounds; a read of an unwritten slice; `defining-contexts` |
| inference | a denial undercuts a `:default` `genl` edge's reading of a membership; a `genl` cycle refused only where the asserting context sees it; a forward rule over a declared-reflexive calculus predicate fires on the diagonal; `transitiveInArg` answers a goal open at another position; `why`, `why-not` and `argue` in content form |
| time | UTC offsets and named zones; a negated calendar relation decided; `temporalDistance` over a calendar moment; `includesInstant` from stated `startOf` and `endOf`; a stated Allen fact orders its things' points |
| integrity and rule checks | specified obligations audited in every eligible reader; an `except`, a direction change or an `edit-records!` removal of a mint rule refused `:mint-rule`; a constant held only at a `quotedArg` position not reported undeclared |
| storage | one constant for both spellings of a commuted reifiable application; one meta-sentex per `exceptWhen` exception; a compound at a `quotedArg` position keeps its order; `replace-facts!`; `edit-records!` adds premises; a starter restart loads only what changed; a crash losing the last record frame detected at the open |
| shipped ontology | CxSocialExtension merged into CxTra; CxTra's hosts, access grants, file paths, constructs, plurality terms, name strings, message claims and pull requests; the Allen and RCC-8 algebra facts inert; the upper partitions `set/monotonic` |
| performance | a batch of `genl` edges chains, places, sweeps and reads rule keys once; a belief read between two writes builds one reader frame per context; a bulk load re-joins a computed rule once; a record frozen whole decodes with its symbols pooled |
| browser | the running version in the header; every stored sentence drawn as a circle and formula; the whole-KB lists under `/stats`; the starter restored from a dump |

Fourteen entries are **Breaking** and one is a **Refusal**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.31.0 caller changes.

| If your code… | Then |
|---|---|
| relies on a context with no `genlCx` path not seeing CxUniverse, or states `(genlCx CxUniverse X)` | move a contingent fact out of CxUniverse into a context of its own; export and reload a store holding such an edge |
| reads a supertype membership a `:default` `genl` edge reaches beside a stored denial as true | state the membership where it must meet the denial, or state the edge `:monotonic` |
| reads `CxTimeFn` slices at ranges, moments or bounded named intervals as unordered, or an unwritten slice as empty | nothing: `sees?` and visibility answer the ordering; export and reload a store holding a `meetFunctionOf` application over a range or a moment |
| reads `argue`'s `:unknown` for a negated calendar relation the clock decides | read `:false` |
| reads `temporalDistance` over a calendar moment as unanswered | read the distance it answers |
| reads `includesInstant` of a thing with a stated `startOf` or `endOf` as `:unknown` | read the `:true` or `:false` the bound decides |
| reads the point predicates at a thing an Allen fact relates as unanswered | read the orderings and firings the fact entails |
| counts a forward rule's firings over `subintervalOf`, `partOfRegion` or a declared-reflexive calculus predicate | read the diagonal firings, and a calculus leaf's `:supports` |
| relies on `assert` refusing a `genl` edge whose cycle only another context sees | find the cycle with `subsumption-status`'s `:coextensional` |
| reads `all-specified-violations` or `kb-integrity` for a requirement a child reader inherits | repair the reader-local gap instead of restating the requirement |
| looks up a commuted reifiable application's constant by its unsorted spelling | nothing: `recover` moves the uses to the sorted spelling's constant |
| looks up a stored `exceptWhen` by an unfolded spelling | export and reload the store |
| relies on a `quotedArg` position's compound folding its commuted spellings | retract and restate the `quotedArg` declaration to respell the stored rows |
| names `CxSocialExtension` | name `CxTra` |
| stores an `except` naming a mint rule | retract it |

### Breaking: inference

- **Every context sees CxUniverse, and `(genlCx CxUniverse X)` is refused.** A context
  with no stored `genlCx` edge reads CxUniverse's facts, rules, taxonomy edges and
  declarations, and its `context-up` holds CxUniverse. A fact in CxUniverse reaches every
  context, belief contexts included. `assert` of `(genlCx CxUniverse X)` throws
  `:not-well-formed` for every `X`, and an explicit `(genlCx X CxUniverse)` adds nothing
  to `X`'s ancestor set.
  [contexts.md](docs/contexts.md#cxuniverse-is-the-implicit-root)
  *Migration:* move a contingent fact a context must not see out of CxUniverse into a
  context of its own (`CxWell` for the shipped examples); state the vocabulary of a context
  stored above CxUniverse in CxUniverse itself, and export and reload a store holding such
  an edge, since the reload refuses it.
  *Breaks:* `sees?`, `context-up`, `ask`, `query` and belief in a context with no path to
  CxUniverse; `assert` of `(genlCx CxUniverse X)`
- **A denial of a supertype membership undercuts a `:default` `genl` edge's reading of
  it.** With `(genl beast perishing)` at `:default`, `(beast Hydra)` and a stated
  `(not (perishing Hydra))` of either strength, `ask?`, `query` and `argue` answer
  `(perishing Hydra)` false where they answered it true beside the true denial, and a rule
  on `(perishing ?x)` no longer fires for `Hydra`. `(beast Hydra)` stays believed, and
  `conflicts` and `contradictions` report nothing. The reading is stored as a sentex under
  the informant `edgeReading` while the denial is stored. A stated or derived
  `(perishing Hydra)` still meets the denial as before.
  [inference.md](docs/inference.md#an-edges-reading)
  *Migration:* state `(perishing Hydra)` where the supertype membership must still meet the
  denial; at `:monotonic` the edge contraposes and the membership meets it instead.
  *Breaks:* `ask`, `query`, `argue` and forward firings on a supertype a `:default` path
  reaches beside a stored denial of it; the stored handle set, which holds the reading
- **A `CxTimeFn` slice at a `DatetimeRangeFn` range, at an `InstantFn` moment or at a named
  interval with stated bounds is ordered against the calendar slices, and a read of a slice
  nobody wrote into sees what the slices it is ordered below see
  ([#219](https://github.com/vaelii/vaelii/issues/219)).** `(CxTimeFn CxStory
  (DatetimeRangeFn "2000-01" "2000-06"))` sees the slice at `(YearFn 2000)` and is seen
  from the slice at `(MonthFn 2000 3)`. The slice at `(InstantFn 2000 6 1 12 0 0)` sees the
  year's under `time.txt`'s `(contextArgSubrelation CxTimeFn 2 subtimeOf)`. A named
  interval's believed `startOf` and `endOf` facts, each an `InstantFn` moment or a named
  moment a believed chain of `instantBefore` and `instantAfter` facts orders, order its
  slice the same way and justify the edge with the chain's facts. A slice at a named moment
  with no stated bound is ordered as that moment, and a slice at the moment a named
  interval's stated `startOf` names is ordered below the interval's, an end stated or not.
  A read naming an unwritten slice answered empty; it
  answers from a read copy holding the edges the producer would compute, held until the
  next write, and mints nothing. The calendar clock relates a range to a calendar term or
  to another range, `overlaps` included, and a named interval by its stated `InstantFn`
  bounds. The interval calculus reads an interval whose stated bounds are two named moments
  of the point network as the point network orders them, beside the interval's own
  `StartFn` and `EndFn` terms. An application of a function
  declared `(meetFunctionOf F subintervalOf)` or `(meetFunctionOf F subtimeOf)` drops an
  argument that holds a range or a moment among its other arguments, as it drops one that
  holds a calendar term.
  [context-nat.md](docs/context-nat.md#write-and-read-are-symmetric),
  [time.md](docs/time.md#naming-an-interval-the-calendar-constructors),
  [canonicalization.md](docs/canonicalization.md#a-functions-terms-reshaped-by-declaration)
  *Migration:* run `export-text!` and `load-text!` over a store holding such a
  `meetFunctionOf` application over a range or a moment; until then neither spelling finds
  it.
  *Breaks:* `sees?`, visibility and belief between `CxTimeFn` slices at ranges, moments and
  bounded named intervals; `ask` and `query` scoped to a `CxTimeFn` slice nobody wrote
  into; calendar-prover answers for a `DatetimeRangeFn` term; calendar-prover and Allen
  answers between named intervals with stated bounds; `handle-of` on a stored
  `meetFunctionOf` application over a range or a moment
- **The calendar clock reads a UTC offset and a named time zone, and answers the negation
  of a relation it decides ([#219](https://github.com/vaelii/vaelii/issues/219)).**
  `(DatetimeFn "2000-01-15T13:00-07:00")` is the minute that begins at 20:00 UTC. `time.txt`
  ships `(ZonedDatetimeFn ISO ZONE)` over a `timezone` identifier string, read through the
  zone's `java.time` rules. A term whose span lies inside an hour the zone skips or repeats
  names no interval, and one that starts or ends on a clock change spans the instants its
  clock reads. The calendar prover, the point network and the `CxTimeFn` slice ordering
  relate an absolute time to absolute times only. A `(not (R a b))` goal over two terms the
  clock reads holds when `(R a b)` fails, so `argue` answers `:false` where it answered
  `:unknown`, `ask?` of the negation answers true, and the `:calendar` shadowing channel
  reads the negated literal's arguments.
  [time.md](docs/time.md#absolute-time-utc-offsets-and-named-zones)
  *Migration:* read `:false` from `argue` of a calendar relation the clock decides fails,
  where a caller read `:unknown` as undecided.
  *Breaks:* `argue` and `ask?` of a negated calendar relation between two terms the clock
  reads
- **`includesInstant` reads a thing's believed `startOf` and `endOf` facts
  ([#219](https://github.com/vaelii/vaelii/issues/219)).** `(includesInstant Since2000
  (InstantFn 2000 1 1 0 0 0))` holds when `(startOf Since2000 (InstantFn 2000 1 1 0 0 0))`
  is believed and no end is stated, since a thing holds its start. A stated bound naming a
  node of the point network narrows the side it bounds, beside the thing's `StartFn` and
  `EndFn` terms, and the answer's support names the fact. An open thing ranges over the
  things a visible stated bound names too.
  [time.md](docs/time.md#the-points-of-a-temporal-thing)
  *Migration:* read `:true` or `:false` from `argue` of an `includesInstant` goal a stated
  bound decides, where it answered `:unknown`.
  *Breaks:* `argue`, `ask?` and `query` of `includesInstant` over a thing with a stated
  `startOf` or `endOf`, and a forward rule firing on such an answer
- **A stated Allen fact orders its two things' points.** `(before A B)` and
  `(instantBefore (StartFn B) (StartFn C))` entail `(instantBefore (EndFn A) (StartFn C))`.
  The start and end points of an Allen fact's two things answer the orderings its relation
  forces, each resting on the fact, and an arriving Allen fact re-joins the forward rules on
  the point predicates. An Allen relation the interval network composes does not reach the
  points.
  [time.md](docs/time.md#the-points-of-a-temporal-thing)
  *Migration:* read the point answers and firings a stated Allen fact entails, where the
  point predicates answered nothing.
  *Breaks:* `ask`, `query` and forward rules over the point predicates and `includesInstant`
  at a point of a thing an Allen fact relates; Allen answers the interval network reads off
  those points
- **`temporalDistance` places a calendar moment, and an instant a stated `includesInstant`
  puts inside a calendar term ([#219](https://github.com/vaelii/vaelii/issues/219)).**
  `(temporalDistance (StartFn (DatetimeFn "1990-05-17T14:32")) (StartFn (DatetimeFn
  "2026-10-21T09:15")) ?d)` answers `(QuantityFn 1149619380 Second)`, and two symbols an
  `includesInstant` fact places inside those two minutes answer a 120-second
  `QuantityIntervalFn`. A network placing moments of both frames holds a wall-clock moment
  within 18 hours of the same absolute reading. A `temporalDistance` fact naming an
  `InstantFn` moment or a point of a calendar term constrains the metric network, and the
  interval calculus's metric narrowing reads the bounds such an `includesInstant` fact
  gives.
  [stp.md](docs/stp.md#calendar-moments)
  *Migration:* read a `temporalDistance` answer over a calendar moment where the goal
  answered nothing.
  *Breaks:* `ask` and `query` of `temporalDistance` over a calendar moment or over an
  instant a calendar `includesInstant` places; Allen answers between intervals whose
  endpoints such a fact places
- **A forward rule over a declared-reflexive calculus predicate fires once per network
  node, and `argue` names what a calculus answer rests on
  ([#232](https://github.com/vaelii/vaelii/issues/232)).** With `(reflexive partOfRegion)`
  visible, a forward rule over `(partOfRegion ?x ?x)` or `(partOfRegion ?x ?y)` concludes
  for every region of the network, each firing resting on the declaration and a fact naming
  the region, and an arriving `(reflexive P)` re-joins the rules on `P`. An `argue` leaf a
  calculus answers carries `:supports`: the facts behind the pair, and on the diagonal the
  `(reflexive P)` statements the context sees.
  [qcn.md](docs/qcn.md#what-a-registered-prover-is-reachable-from)
  *Migration:* read the diagonal firings of a forward rule over `subintervalOf` or
  `partOfRegion`, and the `:supports` of a calculus leaf.
  *Breaks:* forward rules over `subintervalOf`, `partOfRegion` and any calculus predicate a
  KB declares `reflexive`; `argue`'s derivation leaves on a calculus goal
- **A `genl` edge is refused for a cycle only where its own context sees the path back
  ([#254](https://github.com/vaelii/vaelii/issues/254)).** `assert` of `(genl b a)` in one
  context beside a stored `(genl a b)` in a sibling context threw `:not-well-formed`, and
  so did a cover naming a part a sibling context places above its whole; both are stored.
  An edge whose reverse path the asserting context sees is refused at every strength, as
  before, and the refusal message names that context. A context below both siblings reads
  the two types as coextensive, and there a membership in one withholds no minted
  membership in the other.
  [taxonomy.md](docs/taxonomy.md#the-closure-is-not-materialized--it-is-answered-on-demand),
  [argtypes.md](docs/argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on)
  *Migration:* a caller that relied on the refusal to keep the edges of every context
  acyclic finds a cycle with `subsumption-status`'s `:coextensional`.
  *Breaks:* `assert` and `try-assert` of a `genl` edge or a `covering` whose cycle only
  another context sees; `genl?`, `genls`, `specs`, `ask` and the stored mints at a context
  below both edges

### Breaking: integrity

- **Specified obligations audit every known eligible reader.** `all-specified-violations`
  and `kb-integrity` validate each visible `predAllSpecified` / `predSpecifiedAll`
  requirement wherever a reader sees its GAF and an ordinary defining home of the term.
  Child-local instances and exceptions are checked in their own readers. Proved
  skeletal-only defining evidence is exempt; absent or native-only evidence is not.
  Unclassified support remains an explicit gap. Multiple readers combine under the
  existing key without consuming extra result-cap entries. Native-only registry
  declarations retain their querying-context audit.
  ([#250](https://github.com/vaelii/vaelii/issues/250))
  [predall.md](docs/predall.md)
  *Migration:* repair reader-local gaps instead of duplicating an inherited requirement.
  Direct `specified-violations` uses instance eligibility in its supplied reader.
  Exists audits and native-only registry declarations retain their existing behavior.
  *Breaks:* `specified-violations`, `all-specified-violations`, `kb-integrity`

### Breaking: storage

- **Both spellings of a commuted reifiable application name one constant.** Under
  `(reifiable_function PairFn)` and `(commutative PairFn)`, `(holds (PairFn Bob Ann))` and
  `(holds (PairFn Ann Bob))` reified to two constants, and in two arrival orders the row
  held the sorted one beside a map of the written one. They reify to one constant, named
  by the application sorted, and either spelling reads it. A `symmetric` or commuting mark
  arriving or leaving re-spells the uses stored before it, and its leaving hands each
  assertion and firing back the constant of its application as written. A `rewriteOf` of
  either spelling names the term both reify to.
  ([#228](https://github.com/vaelii/vaelii/issues/228))
  *Migration:* none; `recover` moves each use a store written earlier holds under the
  written order's constant to the sorted one's.
  *Breaks:* the constant `handle-of`, `ask?` and `sentexes-matching` read for an
  application of a `symmetric` or commuting `reifiable_function` written unsorted.
  [nat.md](docs/nat.md#write-path)
- **Two spellings of one `exceptWhen` exception are one meta-sentex.** `(exceptWhen
  (greaterThan ?y 3) R)` and `(exceptWhen (lessThan 3 ?y) R)`, or the two argument orders
  of a `symmetric` conjunct, stored two meta-sentexes, and retracting the handle `assert`
  returned for the first left the rule excepted by the second. Each conjunct is put in the
  store's literal form before it is aligned.
  *Migration:* run `export-text!` and `load-text!` over a store holding a meta-sentex under
  the unfolded spelling; until then neither spelling finds it.
  *Breaks:* `handle-of` on a stored `exceptWhen` under the unfolded spelling.
  [canonicalization.md](docs/canonicalization.md#comparison-siblings-folded),
  [exceptions.md](docs/exceptions.md#storage-and-identity)
- **A compound at a `quotedArg` position keeps its written argument order.** Under
  `(commutative PairFn)` and `(quotedArg noteOf 1 expression)`, `(noteOf (PairFn Ann Bob)
  "n")` and `(noteOf (PairFn Bob Ann) "n")` stored as one sentex, and they store as two. A
  `quotedArg` or `quotedArgAndRest` declaration arriving or leaving splits or folds the
  rows of its predicate stored before it. A reader that does not see or believe the
  declaration reads the compound under its functor's marks, through a sub-predicate's row
  too, and a read of a super-predicate finds a declaring sub-predicate's row in either
  order. A forward rule reads the compound as its placement context does, so it fires
  where `ask` there answers its antecedent. A `:rule-clash` acknowledgment's `RulePairFn`
  subject sits at such a position, and the integrity sweep reads it as a bag of rules.
  ([#228](https://github.com/vaelii/vaelii/issues/228))
  *Migration:* retract and restate a `quotedArg` or `quotedArgAndRest` declaration to
  respell the rows a store written earlier holds sorted under it; until then a lookup by
  the written order misses such a row.
  *Breaks:* `handle-of` and `sentexes-matching` over a compound at a `quotedArg` or
  `quotedArgAndRest` position whose functor is `symmetric` or commuting.
  [canonicalization.md](docs/canonicalization.md#compounds-below-the-literal-sorted)

### Breaking: shipped ontology

- **CxSocialExtension merges into CxTra, and CxTra sees CxSocial.**
  `kb/middle/CxTra.txt` states every form `CxSocialExtension.txt` stated
  (`nestingPartnerOf`, `chosenSiblingOf`, `founderOf` and the plurality terms) and
  `(genlCx CxTra CxSocial)` beside `(genlCx CxTra CxUniverse)`, since those relations
  specialize CxSocial's. `core.txt` no longer states `(context CxSocialExtension)`. A
  context is a unit of visibility, and both theories were opt-in, so one opt-in context
  holds both. A context placed under CxTra now also reads CxSocial's relations and
  rules. No relation, kind, rule or declaration changes.
  [contexts.md](docs/contexts.md)
  *Migration:* rename `CxSocialExtension` to `CxTra` in any `genlCx` edge, `ist` or
  context argument that names it; a context placed under both needs one edge to CxTra.
  *Breaks:* `CxSocialExtension`

### Refusal: rule checks

- **An `except` naming a mint rule, a direction change of one and an `edit-records!`
  removal of one are refused as `:mint-rule`.** The mints of an argument declaration kind
  rest on the kind's inert rule, whose `retract!` was refused already. `assert` stored an
  `(except (sentexHandle H))` naming the rule, and `edit-records!` removed it or moved its
  direction on a KB without belief. A restatement under another direction, refused
  `:not-indexable`, is refused `:mint-rule` with the rule's `:kind`.
  [argtypes.md](docs/argtypes.md#the-entailment-as-a-justified-datum)
  *Migration:* retract an `except` naming a mint rule that a store holds.
  *Breaks:* `assert` of `(except (sentexHandle H))` with H a mint rule; the `:type` of a
  mint rule restated under another direction, `:not-indexable`; `edit-records!` naming a
  mint rule

### Additive: inference

- **A `transitiveInArg` or `transitiveInArgInverse` declaration answers a goal open only
  at a position it does not name.** Under `(transitiveInArgInverse locatedIn 1
  tangiblePartOf)`, `query`, `prove` and `ask` on `(locatedIn U1 ?w)` return each `?w`
  that `ask?` confirms of the ground instance, where they returned the stored extent alone.
  A goal open at a preserved position still reads the stored extent.
  [inherit.md](docs/inherit.md#reading-it-back)
- **`why`, `why-not` and `argue` answer in content form on `{:content? true}`.** Every
  sentex in the reply is named `(ist Cx S)` with its `:digest`, and no handle or
  justification id appears, so two seats that believe the same knowledge compare their
  explanations with `=`. Two conflicts withdrawing one sentex at one vantage are ordered by
  their content. `why` takes the option in a new arity, `why-not` in its sentence
  arity's opts, and `argue` in `argue-opt-keys`, which is `query-opt-keys` and `:content?`.
  [overlay.md](docs/overlay.md#two-seats-explanations)
- **`mint-rule-kind` names the declaring kind of a stored mint rule**, and nil for any
  other sentex. [argtypes.md](docs/argtypes.md)

### Additive: shipped ontology

- **CxTra ships `toolEnablesCapability`, and reads `hasCapability` from it by
  default.** `(toolEnablesCapability ?tool ?kind)` says that whoever has `?tool` available
  can be the doer of a happening of kind `?kind`: position 1 takes a `temporal`, the
  nearest type software and a physical tool share, and position 2 is a `happening` kind
  (`genlArg`). `agentHasTool`'s position 2 takes a `temporal` where it took a
  `software_tool`. A default forward rule concludes `(hasCapability ?agent ?kind)` from
  `(agentHasTool ?agent ?tool)` and that fact, guarded by `(causal ?agent)`, since
  `agentHasTool` types its agent `thing` and `hasCapability` types it `causal`. A
  `:monotonic` `(not (hasCapability ?agent ?kind))` defeats it. [contexts.md](docs/contexts.md)
- **A penguin with something that enables flying can fly where CxTra is seen.** CxTra
  excepts CxBiology's rule concluding `(not (hasCapability ?x flying))` of a penguin,
  through `(exceptWhen … (ist CxBiology …))`, for a penguin that `agentHasTool` a thing
  `toolEnablesCapability` names for `flying`, and states `(genl computational_system
  temporal)`. A penguin without such a tool still cannot fly.
  [contexts.md](docs/contexts.md)
- **`core.txt` declares `successorTypeOrder`, the metatype-order ladder one step at a
  time.** `(successorTypeOrder ?lower ?higher)` says that `?higher` is the order of type
  directly above `?lower`. Both positions take a `type_type_by_order`, and `(genlInverse
  successorTypeOrder typeGenl)` reads each fact as the `typeGenl` fact with its arguments
  swapped. `core.txt` states `(successorTypeOrder type metatype)` and
  `(successorTypeOrder metatype meta_metatype)`, which answer `(typeGenl metatype type)`
  and `(typeGenl meta_metatype metatype)`; `core.txt` no longer states those two.
  `vocabulary/classification` calls it inert, as it does `typeGenl`.
  [glossary.md](docs/glossary.md)
- **CxTra ships hosts, what runs on them, and access to a resource.** `computer` is
  below `electronic_device` and `:monotonic`-disjoint from `person`: a person may run on
  a computer but is not one.
  `virtual_machine`, `software_container` and `software_service` are separated under
  `computational_system`, and `mcp_server` is below `software_service`. `(runsOn
  ?system ?host)` is transitive, and no rule carries any other fact across it.
  `kubernetes_cluster` is a `computational_system`, and `network` and
  `kubernetes_namespace` are `intangible`; `clusterNode` with its specs
  `controlPlaneNode` and `workerNode`, whose node is a `computational_system` (the
  operating system install that runs on a computer or a hypervisor), `onNetwork` and the
  functional `kubernetesNamespaceOf` relate them. `(hostnameOf ?thing ?name)` takes a string and
  states `(not (functional hostnameOf))` and `(not (functionalInArg hostnameOf 1))`, so
  two systems that share a name are not equated. A grant of access is stated as
  `(hasCapability ?principal (ShellAccessFn ?resource))`: `ReadAccessFn`,
  `WriteAccessFn`, `ShellAccessFn`, `AdminAccessFn` and `DeployAccessFn` are reifiable,
  their `genlResult` is one of five happening kinds below `resource_access`, and each
  has a functional corresponding predicate, `readAccessOf` through `deployAccessOf`.
  Two default forward rules conclude write access from admin access and from deploy
  access over the same resource. `(custodianOf ?person ?thing)` says who keeps a thing
  working. [contexts.md](docs/contexts.md)
- **CxTra ships file-path references and lookup access.** A `file_path_reference`
  (below `linguistic`) is an absolute path taken with the `filesystem_namespace` (below
  `intangible`) it is resolved in: `(FilePathRefFn ?namespace ?path)` builds one, with
  `filePathRefOf` its corresponding predicate, and a forward rule reads `pathNamespace`
  and `pathText`, each functional, from `filePathRefOf`. `file_lookup`, resolving paths
  in a namespace, is below `resource_access`, and `(hasCapability ?principal
  (FileLookupFn ?namespace))` states a grant of it, with `fileLookupOf` its functional
  corresponding predicate. Lookup entails no read access. [contexts.md](docs/contexts.md)
- **CxTra ships `construct`, `seat`, `hasSeat`, `founderOf` and the plurality terms.** A `construct` is a
  person whose mind runs on a computational substrate: below `person`, and
  `:monotonic`-disjoint from `organism`, so `(disjoint human construct)` follows. A
  `seat` is the `computational_system` a construct runs in, and `(hasSeat ?construct
  ?seat)` relates the two; it states `(not (functional hasSeat))`, since a construct can
  run in several seats.
  `(founderOf ?founder ?construct)` is a spec of `originatorOf` naming the person who
  founded a construct; position 2 takes a `construct`. `singlet`, `plural_system` and `alter` are separated
  under `person`, with no coverage claimed. `(alterOf ?alter ?system)` is functional and
  asymmetric, and a forward rule reads the symmetric `headmateOf` of two different alters
  of one system. `(not (genl headmateOf knows))` states that sharing a body does not
  entail knowing each other. [contexts.md](docs/contexts.md)
- **CxTra ships `nameString`, a thing's name as a string.** `(nameString ?thing ?name)`
  takes a thing of any kind in position 1 and a string (`quotedArg`) in position 2. It
  carries no functional mark, so a thing can have more than one name string.
  [contexts.md](docs/contexts.md)
- **CxTra ships `discordMessageClaims`, the Discord message a claim came from.**
  `(discordMessageClaims ?message (sentexHandle H))` says that the message asserts what
  sentex H states. Position 1 takes a `discord_message`, below `digital_artifact`, which
  the reifiable `(DiscordMessageFn ?snowflake)` names by its snowflake id as a string
  (`quotedArg`), with `discordMessageOf` its corresponding predicate, value last;
  position 2 takes `thing`, as `agentClaims`'s does. It is
  `target_following_predicate`, so retracting H retracts the receipt.
  [contexts.md](docs/contexts.md)
- **CxTra ships pull requests, their status, the ready latch and merge access.** A
  `pull_request` of a `forge_repository`, both below `digital_artifact`, is named by the
  reifiable `(PullRequestFn ?repository ?number)`, with `pullRequestOf` its
  corresponding predicate, value last. `(prStatus ?pullRequest ?status)` takes a
  `pull_request_status`, below `nowhere_never`: `PullRequestDraft`, `PullRequestReady`,
  `PullRequestMerged` or `PullRequestClosed`. `(holdsReadyLatch ?person ?repository)`
  says whose call it is that a repository's drafts are ready, and grants nothing.
  `merge_access` is below `write_access`, `(hasCapability ?principal (MergeAccessFn
  ?repository))` states a grant of it, with `mergeAccessOf` its functional
  corresponding predicate, and a default forward rule concludes write access over the
  same repository. [contexts.md](docs/contexts.md)
- **`time.txt` and `space.txt` state the Allen and RCC-8 base relations' converse,
  asymmetry and disjointness inert.** CxUniverse holds `(set/inert (inverse P Q))` per
  Allen converse pair, `(set/inert (asymmetric P))` per base relation other than its own
  converse, and `(set/inert (negates P Q))` per pair of base relations: 128 stored
  sentences that form no nogood and change no belief. [qcn.md](docs/qcn.md)
- **Every shipped inert rule states why it is inert.** Ten new `implementationNote`s and an
  added sentence in `birthDate`'s hold the reasons, which `core.txt` and `life.txt` kept in
  source comments. [glossary.md](docs/glossary.md)

### Additive: storage

- **A restart over a store the starter and its text KBs built loads nothing again.**
  `vaelii.starter/load-into` takes `{:layers [path …]}`, text KBs it loads after the
  starter, and over a durable store nothing has written to since the last call it skips
  the sources before the first whose files changed. A fact a changed or dropped layer no
  longer states is retracted, and a restated strength is the stated one. A premise no
  layer stated, such as a caller's own write into a layer's context, stays. The daemon's and
  the CLI's `--starter` take the same path. ([#247](https://github.com/vaelii/vaelii/issues/247))
  [operations.md](docs/operations.md#restarting-over-a-built-store)
- **`replace-facts!` writes a context's new snapshot as its difference.**
  `(replace-facts! kb context facts opts?)` reads the ground literal premises stored in
  `context`, adds each fact it does not hold and retracts each premise no fact names, in one
  `edit!`, so a conclusion both snapshots support stays believed throughout. A premise
  naming a sentex, such as an `exceptWhen`, is never retracted, a held fact requested at a
  stronger strength is raised to it, `:added` counts rows, and a rule, a fact holding a
  variable, a fact stored outside `context` and a fact naming a sentex are refused
  `:shape`. The daemon serves it as `:replace-facts`, and `vaelii.client` carries it.
  [storage.md](docs/storage.md#writing-the-difference-between-two-snapshots),
  [api.md](docs/api.md)
- **`edit-records!` adds `genl`, `sense` and `comment` premises to a KB without belief.**
  `{:add [[sentence context] …]}` writes each new ground fact as a premise record with
  the index postings `assert` gives it, a `genl` edge's taxonomy-supporter postings among
  them, before the batch's removals. A sentence stored as a premise counts under
  `:present` and is left alone; one stored as a derived record gains the premise mark.
  Every refusal comes before the first write: the belief-free checks of the write path
  (`:shape`, `:not-ground`, `:naming`, `:not-well-formed`), `:record-edit-unsupported`
  for another functor, a compound argument, a `genl` between predicates, a predicate the
  store marks symmetric, commutative or forced-decontextualized, or a context the index
  does not name, and `:unrecovered-kb` on a store whose index was never built. A batch
  adding a `genl` edge owes the argument-type pass. `settle-record-edits!` then brings each
  seed that is a stored premise fact in as `assert` does after storing it: its migrations,
  lift, argument-type mints, companion rules and arity classes, one chain from all of
  them and from the facts their edges make newly matchable, and a settle; it returns
  `:arrived n`. A `genl` cycle, a negation cycle and a disjointness or argument clash go
  unchecked, so a caller screens additions with `check` while belief is built. Four tests
  in `edit_test` (84 assertions) compare the records, premise marks, belief,
  justifications and mints per context against `edit!` under both pruning readings, with
  and without the argument-type pass, and cover the refusals, the duplicates and a batch
  run with the KB's reasoning state unreadable.
  [storage.md](docs/storage.md#editing-the-records-of-a-kb-without-belief)

### Additive: contexts

- **`defining-contexts` reads the maximal ordinary defining contexts of a term.**
  Literal Quote and nested-sentence mentions, lift-only copies, generated arity-class
  copies and NAT bookkeeping do not create a defining home. Independent ordinary
  support still counts. Unclassified live support raises `:incomplete-defining-contexts`.
  The daemon serves it as `:defining-contexts`, and `vaelii.client` carries it.
  [api.md](docs/api.md)

### Additive: browser

- **The page header names the running version.** The label sits beside the wordmark, and
  its tooltip gives the git revision. [web.md](docs/web.md)
- **Every stored sentence on a page draws as a circle and formula.** Browsed literals and
  rules and Core predicates are one-line sentex rows, and justifications, `/why`, the
  search tree and the reports name a rule or conclusion by its row, not its handle. The
  circle-to-formula gap is one width on every row, and `/history/literals` is
  `/history/sentexes`. [web.md](docs/web.md)
- **A sentex's page explains its circle.** It states the kind, origin and belief the circle
  draws, says why an inert rule is inert, and names the cause of every OUT state, withdrawn
  and forced conclusions among them. [web.md](docs/web.md)
- **Choice, constraint and solve rules have their own circle colours**, teal, pink and sky,
  and black means an inert rule alone. [web.md](docs/web.md)
- **The term legend reads `unary_predicate`, predicate, ternary+ predicate, connective,
  context, individual, literal, variable.** [web.md](docs/web.md)
- **The whole-KB lists are a section of `/stats`.** Defeats and Contradictions show their
  stored counts on every load, a list a stored zero proves empty offers no button, and an
  empty run stays on `/stats`. The Lists menu item is gone and `/lists` answers with the
  `/stats` page. [web.md](docs/web.md#whole-kb-lists)
- **`/network` says what a KB holds for it.** The calculi table counts each calculus's
  stored facts, and a KB holding none says so. [web.md](docs/web.md)
- **The header adapts to the viewport and stays on screen.** The logo sits upper left,
  search lower left, the KB link and colour dots lower right, and the menubar runs from
  the left along the top row or between the corners. A viewport of 57rem or wider gets a two-line header
  that stays in view while the page scrolls. The header and every menu link hold their
  position across a click. [web.md](docs/web.md)
- **A page's HTML source breaks lines at block elements**, so the source reads one
  element per line. [web.md](docs/web.md)
- **`lein browser` restores the starter from a dump under `target/` when one matches the
  engine and the shipped files.** A start that finds one reaches the prompt without
  asserting the starter; any other start loads it in full and writes the dump.
  `lein run -m vaelii.web` and `/kbs` load it in full.
  `vaelii.starter.dump` names the directory, and the `:browser` profile sets it.
  [web.md](docs/web.md#the-starter-dump)

### Fix: answers

- **A pattern holding a variable inside a permuted compound below the literal reads the
  compound in every order its mark allows.** Under `(commutative PairFn)`, `(holds (PairFn
  Bob ?x))` missed a stored `(holds (PairFn Ann Bob))`, and a forward rule reading that
  pattern did not fire over it. A query, a backward goal and a forward join or trigger fan
  each such compound over its arrangements; a firing made over one names the mark, and
  leaves with it. ([#228](https://github.com/vaelii/vaelii/issues/228))
  [canonicalization.md](docs/canonicalization.md#compounds-below-the-literal-sorted)
- **Two placed conflicts against one member at one reader defeat the member there, as one
  conflict does.** With `(cat Rex)` lowered to `:default` at CxW, and `(disjoint dog cat)`
  and `(disjoint fish cat)` each placing a `(contradicts …)`, CxW believed `(cat Rex)`:
  each conflict's justification read `(cat Rex)` as hidden by the other conflict.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion)

### Fix: order independence

- **A forward rule with a closed-extent negative antecedent and an `unknown` antecedent or
  an `exceptWhen` is re-decided when a member of the extent arrives.** The re-check kept
  the firings an `unknown`, `exceptWhen` or aggregate literal names and dropped the one an
  arriving `(asleep K)` refutes, so the rule written before `(asleep K)` kept concluding
  `(conc K)` and the rule written after it did not.
  [naf.md](docs/naf.md#under-the-grant-a-negative-antecedent-is-naf)
- **A rule firing's stored `:bindings` are the same in every arrival order, and a refused
  firing is one refusal entry.** A firing a rule's own join found carried the join's `?ctx`
  beside the rule's variables, and the same firing reached from an arriving fact did not,
  so `justification`, a clash report's `:justifications` and the order
  `supporting-justifications` sorts on differed by arrival. A refused firing kept an entry
  per join, per run `:max-depth` and once more swept, so `chain-report`'s `:refused` count
  differed too.
  [nmtms.md](docs/nmtms.md#two-representations-of-the-same-network)
- **A forward rule's computed antecedent runs after its binders however many variables
  it shares with the literals before it.** An antecedent a `SupportingProver` answers only
  when ground, sharing four variables with a stored literal, was ranked ahead of the
  literal binding its fifth, asked open, and answered nothing: the rule asserted after its
  facts concluded nothing, and asserted before them concluded every firing.
  [inference.md](docs/inference.md#conjunctive-query-planning-vaeliiimplplan)
- **A preservation along `genlCx` reads the context topology with no `except` holes.**
  `inherit/witness-terms` read `genlCx` through the except-aware walk from the preserved
  term's own context, so an `except` one context stated on a `genlCx` edge withdrew the
  preserved claim from `CxUniverse` and from a sibling that could not see the except. The
  read is the unscoped one inherit.md states.
  [inherit.md](docs/inherit.md#from-whose-vantage)
- **A derived `genl` edge that a relabel brings back IN chains the facts below it, as its
  arrival does.** A relabel restored the edge's belief without seeding the facts below
  its lower end, so a forward rule over the upper end missed them in the arrival orders
  that took the edge OUT and back.
  [nmtms.md](docs/nmtms.md)
- **A rule derived from an excepted handle fires over the facts beside it once the
  `except` leaves.** Retracting `(except (sentexHandle H))` re-joined from `H`'s
  consequence closure and skipped the rules in it, so a rule a generator derived from `H`
  stayed unfired at the excepting context over a fact stated there, though the same
  fact stated after the retraction fired it.
  [contexts.md](docs/contexts.md)

### Fix: inference

- **A forward rule concluding a `genl` edge stops when it derives the edge again.** Each
  firing seeded the facts below the edge, a re-derivation included, and the firing's own
  trigger is one of them, so a rule concluding `(genl ?t dog)` from `(poodle ?x)` fired on
  `(poodle Rex)` without end once a rule read `dog`'s members. A firing seeds the facts
  below its edge only when it adds a justification.
  [taxonomy.md](docs/taxonomy.md#what-a-batch-of-edges-costs-the-passes-that-read-it)
- **A forward rule's closed-extent negative antecedent is decided at each reader below the
  firing's placement.** With `(not (asleep ?y))` under `(closed_extent_predicate asleep)`
  in CxA, an `(asleep K)` or a `:monotonic` denial of the grant in a context below CxA
  places a guard defeat there, so the conclusion is not believed where `ask?` of the
  literal fails, as the same rule written backward is not provable. A stored `(not (asleep
  K))` visible below CxA answers the literal there, and the conclusion stays believed.
  [naf.md](docs/naf.md#under-the-grant-a-negative-antecedent-is-naf)
- **`violations` lists no `:inert-rule` for a rule only a generator's firings conclude.**
  A generator fired over a predicate whose argument types are separated mints a rule no
  term can fill. The rule is held as before, and is listed once an author asserts it too.
  [argtypes.md](docs/argtypes.md#a-rule-whose-variable-no-term-can-fill-is-held-inert)
- **A constant held only at a `quotedArg` position is not an undeclared-term finding.**
  `kb-integrity`'s `:undeclared-term` pass read every argument outside a `Quote` as a use,
  so a symbol a `(quotedArg P n …)` declaration types as a mention was reported. The pass
  reads past those positions, as the argument checks do.
  [integrity.md](docs/integrity.md#what-an-undeclared-term-finding-means)

### Fix: shipped ontology

- **The upper files state their definitional partitions and `syncategorematic`'s two
  disjoints `set/monotonic`.** Every context sees CxUniverse, so a `:default` partition
  stated there was defeasible against every context's facts. The partitions over
  `relation`, `unrepresented_term`, `expression`, `atomic_expression`,
  `denotational_term`, `atomic_term`, `formula`, `sentence`, `predication` and `literal`
  and the disjoints of `syncategorematic` from `linguistic` and `quantitative` are
  `:monotonic`, so a `:default` denial does not defeat one.
  [contexts.md](docs/contexts.md#cxuniverse-is-the-implicit-root)

### Fix: storage

- **A crash that loses the last record frame while a prefix of its index batch survives
  is detected at the open.** The coverage check read the batch-seal counter alone when it
  was non-zero, and that shape leaves the seal and the record count agreeing with the
  root count one ahead; the trie kept a posting no record backed, `handle-of` named it,
  and `assert` of the same sentence returned the handle, stored nothing and marked a
  premise `ask?` could not read. The open compares the root count beside the seal and
  rebuilds, and `assert` over a posting with no record takes the posting out and stores
  the sentence anew.
  [storage.md](docs/storage.md#the-on-disk-backend-disk)
- **A crash inside a pull's import of the dump keeps the writes the next open cannot
  assert, and the next pull asserts them.** The open over the partly imported base
  deleted the rebase marker whatever the replay returned, dropping each form naming a
  record not yet imported, each form refused, and each retraction of a sentence the
  partial base holds no premise of, a sentence a fork rule derived again during the
  replay included. The marker keeps them, the open names them in its `::pending-replayed`
  line, and the next rebase adds them to its capture.
  [overlay.md](docs/overlay.md#replacing-the-base),
  [operations.md](docs/operations.md#after-a-crash)
- **`export-text!` writes an exception on a rule another context stores as `(exceptWhen
  Q (ist Cx R))`, and the rule on its own line in its own context.** It paired every
  `exceptWhen` meta-sentex with its rule as one `(exceptWhen Q R)` form in the exception's
  context, so `load-text!` stored a second, unexcepted copy of the rule there and none in
  the rule's own context. An exception and its rule share one form only when one context
  stores both.
  [exceptions.md](docs/exceptions.md#storage-and-identity)
- **A second disk open naming neither `:dir` nor `:space` logs the default-space
  warning.** The warning fired for in-RAM records only; two such disk opens share
  `space-0` under the default directory the same way.
  [storage.md](docs/storage.md#opening-a-kb)

### Fix: performance

- **A belief read between two writes builds one reader frame per context.** `in?`,
  `believed?` and a scoped `genl?` over a KB with a placed defeat or a stored except rebuilt
  the frame per read, at a cost growing with the forced-monotonic declarations.
  [nmtms.md](docs/nmtms.md)
- **A starter load spends a third less CPU.** `CxBiology` states its declined `rule-macro`
  suggestion as an `acknowledgedFinding` with its reason, so `kb-integrity` reads the same
  decision and a load solves a fifth of the computed goals.
  [integrity.md](docs/integrity.md)
- **A bulk load re-joins a computed rule once.** Inside a `with-deferred-settle` batch, each
  datum a prover reads re-joined every rule with an antecedent that prover answers, so a
  shuffled load of the shipped starter spent a third of its time on re-joins that placed
  nothing. The batch re-joins each such rule once, at its settle.
  [inference.md](docs/inference.md#what-a-computed-answer-rests-on)
- **A definitional-block tally takes half the time.** `describe`, `subsumption-statuses` and
  `disjointness-audit` between two writes ask each ground goal once.
  [integrity.md](docs/integrity.md)
- **An `edit!` chains the facts under its `genl` edges once for the batch.** Each added
  edge chained its lower end's whole believed subtree at its own assert, so a batch of
  edges over one subtree chained it once per edge. The batch chains the union after its
  adds, and belief and justifications are unchanged. Ten edges over one 2,000-fact subtree
  seed 2,010 handles, not 20,010.
  [taxonomy.md](docs/taxonomy.md#what-a-batch-of-edges-costs-the-passes-that-read-it)
- **A batch of `genl` edges reads the stored rule keys once.** On a KB declaring a
  `genlInverse` edge, each edge an `edit!` or an `edit-records!` batch seeds decoded every
  antecedent key the stored rules take to ask whether a rule reads a negation under its
  lower end, so the batch's chaining seeds cost its edges times the keys. The batch reads
  the keys, the re-join families and each predicate's negative facts once, and each edge
  meets the negated keys from the smaller side. The seeds are unchanged. A batch of 2,048
  edges beside 2,048 keys costs 0.065 ms per 64 edges, where it cost 19.6 ms; 1 test.
  [indexing.md](docs/indexing.md#3-the-rule-index)
- **A `genl` edge places again only the membership nogoods with a type at or below its
  lower end.** Each term holding a type under a moved edge's lower end had every one of its
  nogoods placed again, its routes read and its placed member sets read for stale ones,
  though a nogood whose member types and cover parts are not under the lower end reads no
  closure the edge moved. Such a term now places those nogoods alone, unless another
  source queued it. Placements, verdicts and belief are unchanged. An edge over a hub type
  whose terms hold one unrelated nogood each reads the routes of 2 nogoods at 8 and at 16
  terms, where it read 10 and 18; 2 tests.
  [nmtms.md](docs/nmtms.md#the-nogood-families)
- **A `genl` edge asks again only the inherited clashes whose reach it crosses.** The
  inherited-clash discovery re-asked, for each moved `genl` edge, the facts of a predicate
  preserved along `genl` at every term below the lower end or above the upper end, and
  every separated membership's clash in the KB. A claim against the arrow crosses the edge
  only from above the upper end to below the lower end, and one along it the other way, so
  the facts re-asked are those at the receiving side's terms, while a stored claim holds a
  term of the other side; the separated memberships re-asked are those of a type, or of a
  preserved predicate, at or below the lower end. A membership's denial reading reads the
  separation's witnesses only when a claim reads it, and the exception re-check reads a
  `genl` edge's reach only for a goal its separation arms leave open. Clashes, placements
  and belief are unchanged. An edge beside 8 and beside 32 separated-membership clashes
  and claims above its upper end asks 3 questions at both, where it asked 19 and 67; 2
  tests.
  [nmtms.md](docs/nmtms.md#the-inherited-clash-memo)
- **A `genl` edge's argument-type sweep reads each lower end's closure once.** Every
  entailment the sweep under an arriving edge drew, a duplicate included, moved the change
  clock through `ensure-node` and retired the scoped closure and visibility caches, and
  each fact asked a fresh scoped `genl?` walk per declaration to place its mint. A node
  already present at a depth no higher now moves neither the network nor the clock, and the
  placement reads membership in the fact's scoped closure, which the declarations were read
  through. Records, justifications, placements and violations are unchanged against the
  reference paths over a 7-step mixed scenario. An edge over 4 and over 16 facts whose
  declarations mint nothing new walks up from its lower end equally often at both, where it
  walked 22 and 82 times; 2 tests.
  [argtypes.md](docs/argtypes.md#where-a-mint-is-placed)
- **A placement reads no `:default` edge's record for a strict link, and a reader's void
  check reads no premise's record.** The witness of a contrapositive link (a `supertype`
  nogood's, a cover part's denial, a separation's denial) keeps only paths every edge of
  which `res/holding-class` reads `:monotonic`, but its walk, its route search and the
  `:monotonic` check of each placement walked every edge above the held type at
  `:default` as well, reading each edge supporter's record. They now walk the
  `:monotonic` edges alone. `exc/forced-void` read a handle's record before learning that
  only a firing can be void; it now reads none for a premise. Placements, verdicts and
  belief are unchanged. Over a 16-level ladder of `:default` edges a strict link reads the
  class of 9 supporters where it read 231; 2 tests.
  [nmtms.md](docs/nmtms.md#the-placement-pass)
- **A progress reporter no longer copies the caller's thread bindings.** Under a Trove
  backend other than `set-log-level`'s, each reporter a settle opened copied every binding
  in force for its timer, about 5 µs at the 54 bindings a write holds; it now shares the
  binding frame. Over 179,000 single-sentence writes the copy took 1.1% of the CPU.
  [operations.md](docs/operations.md#progress-lines)
- **A check for an optional capability a value lacks reads one class.** A record store
  without `Prefetching`, `Tallying`, `BulkLoading` or `BulkAnnotating`, and a prover
  without `SupportingProver`, cost about 5 µs a check, read by walking the value's
  supertypes; the check now takes about 25 ns. Over 179,000 single-sentence writes the
  walks took 3.1% of the CPU. [storage.md](docs/storage.md#protocols)

- **A record stored nippy-frozen whole decodes with its symbols pooled.** The Postgres and
  SQLite adapters store each record frozen whole, and decoding one kept the private copy
  of every symbol the thaw made, where a positional frame's symbols were pooled. A
  literal's sentence and context, a rule's context, antecedent, consequent and varmap,
  and a justification's informant and bindings now share one symbol per name with the
  in-memory store, so a record the fetch cache holds, or a read keeps, carries no copy of
  its names. `decoding-interns-the-vocabulary` asserts it for both frame shapes (20
  assertions).
  [storage.md](docs/storage.md#the-on-disk-backend-disk)

### Fix: browser

- **The Postgres backup page reads a snapshot store's `records.edn` with `clojure.edn`.**
  It read the file with `clojure.core/read-string`, the one reader of a store file not
  held to the EDN reader.
  [web.md](docs/web.md#backing-up-a-store-kept-in-postgres)

### Internal

- **`lein test-parallel` shards a durable backend and `:all`.** Each shard of a durable
  backend opens its own `vaelii.disk.dir`, and at `:all` the shards are packed from
  `scripts/ci-test-weights-all.tsv`, which weighs the `^:slow` tests. Each leg of
  `deep.yml` runs it at `:all` across three shards.
- **`lein lint`'s drift stage resolves the backticked var references in `.clj` comments.**
  A backticked `alias/fn` in a comment or docstring under `src/`, `test/` or `bench/` fails
  when its namespace defines no such var. E23 fails a tracked top-level entry the stage
  does not list and a tracked `.md` outside the listed directories, and E7 fails an issue
  number told as an event.

## 0.31.0 — 2026-10-30 — "Separations that lose to a stronger denial, lazy-forward rules and a computed `nonempty`, forks that pull a newer base and merge peers' deltas, content digests across seats, `CxTimeFn` slices ordered across monads"

**69 entries** — 14 Breaking, 3 Refusal, 16 Additive, 34 Fix, 2 Internal. A separation
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
meta naming a sentence nothing stores, `:unresolved-reference`

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
`dispute/dispute-term`, `(dispute …)`, `:not-well-formed`, `unknown`, `forall`, `not
well-formed: `, `:refused`, `set/inert`, `set/monotonic`, `:shape`,
`:length-against-shape`, `:length-against-spelling`, `arity`, `arityMin`, `bravely`,
`cautiously`, `:naming`, `import!`, `try-assert`, `:complement`, `:arity`, `:irreflexive`,
`:anti-symmetric`, a KB holding a rule that concludes `P` from a closed-extent `(not (P
…))` beside a `closed_extent_predicate` or `closedExtentForArg` grant on `P`

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
