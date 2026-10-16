# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.26.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Additions

- **`genlInverse` infers: binary `genl` with arguments 1 and 2 swapped.**
  `(genlInverse P Q)` makes a stored `(P a b)` answer a `(Q b a)` goal, satisfy a
  `(Q ?x ?y)` rule antecedent, and answer a `Q` goal through a rule concluding `P`. A
  firing's justification names the `genlInverse` edges it crossed, a default edge caps the
  conclusion at `:default`, and an `except` on the edge hides the swapped reading. The
  matching fan walks `genl` and `genlInverse` edges together with a parity bit
  (`tax/signed-closure`), so a chain swaps exactly when it holds an odd number of
  `genlInverse` edges and two in a row answer what `genl` answers. The converse is not
  licensed. docs/inference.md, "`genlInverse`: the fan with the arguments swapped",
  records the five readers that take less than the full swap.

  *Class:* **Additive** (the predicate was declared with no inference path; core.txt
  states no `genlInverse` fact, so the shipped ontology answers as before).
  *Migration:* none. A KB that states `(genlInverse P Q)` now reads `P` facts as swapped
  `Q` facts.

- **CxUniverse separates `animal` from four made kinds.** `(disjoint animal building)`,
  `(disjoint animal clothing)`, `(disjoint animal furniture)` and `(disjoint animal
  machine)`, each `:monotonic`, join the made-kind separations in `abstract.txt`.
  `organization` and `animal` are separated by the tangible/intangible partition
  instead and needed no new fact.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none. A term below `animal` and a term below one of the four made kinds
  were already `:unknown` or `:orthogonal` to each other; a KB stating an overlap
  between them now holds a disjointness nogood.

- **CxRealWorld ships as a middle context under CxWell, and `animal`/`vehicle`
  separate there monotonic.** CxUniverse states `(disjoint animal vehicle)` at the default strength,
  so a fiction below CxWell may except it and hold a term that is both — the shipped
  ontology still has to be able to represent fiction. CxRealWorld, which sees CxWell,
  restates the same separation `:monotonic`, so the real world itself can never hold
  the overlap; a fiction is a sibling of CxRealWorld under CxWell, never a context
  under it, so a fiction's exception never reaches what holds of the real world.
  CxNormalPhysicalConditions now sees CxRealWorld instead of CxUniverse directly, so a
  room's temperature theory reaches the real world and never a fiction.
  `catbus_test` pins a term that is both a cat and a bus as a represented dilemma in a
  fiction context, the same pair losing a monotonic clash in CxRealWorld, and an
  ordinary animal not a vehicle in CxWell with no overlap asserted.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none. A context below CxWell reads `animal`/`vehicle` as separated by
  default, as before; a context placed under CxRealWorld reads the separation
  monotonic, and a context placed under CxNormalPhysicalConditions now also sees
  CxRealWorld's and CxWell's content.

- **`why-not` of an inert denial names the literal it denies and what puts it on the
  roster.** `:denies` carries the literal, its handle in the same context, whether that
  context believes it, and the roster predicate, kind and declarations. The browser's
  sentex page renders it. [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Class:* **Additive**.

### Fixes: answers

- **A membership in a type separated from `T` answers `(not (T x))`, and the cover family
  reads the same denial.** With `(pc Xy)` believed and `pc` separated from `pb` by a
  visible `disjoint`, disjoint metatype, `sibling_disjoint` parent or `partition`, `query`
  of `(not (pb Xy))` answers and `argue` of `(pb Xy)` answers `:false` where both answered
  nothing (`provers/DisjointnessNegationProver`, `res/separation-denials`). The denial
  climbs only `:monotonic` `genl` edges on both sides, since a default does not
  contrapose: with `(genl pa pb)` at `:default`, `argue (pa Xy)` stays `:unknown`, and at
  `:monotonic` it answers `:false`. A cover every part of which such a denial rules out is
  a `:cover` nogood over the whole's membership and the denying memberships, placed by the
  settle in every arrival order, so `contradictions` lists what `argue` reads as refuted;
  the write that completes one is stored, never refused. A rule's `(unknown (not (T …)))`
  antecedent and an `exceptWhen` on `(not (T …))` are re-checked when such a membership
  or separation arrives or leaves.
  [taxonomy.md](docs/taxonomy.md#disjointness)
  ([#183](https://github.com/vaelii/vaelii/issues/183)).

  *Class:* **Fix**.
  *Migration:* none. A KB holding a membership under a cover whose every part another of
  the term's memberships is separated from now holds a `:cover` nogood over them.

- **`tool` is retired.** The ontology classifies by what a thing is, and `tool` named
  an artifact by what it is for. `abstract.txt` drops the type, its comment, its `genl`
  edge to `made` and `(disjoint building tool)`, and CxSocial drops `(disjoint dwelling
  tool)`. CxComputing's comment on `software_tool` no longer sets it against `tool`.
  `ontology_test` and `starter_test` drop it from the rosters that named the made kinds
  and the documented vocabulary, `social_test` from dwelling's disjoints, and
  `computing_test` its check that `software_tool` is not a `tool`.

  *Class:* **Fix** (shipped ontology content, which takes no Breaking label however far
  it moves an answer).
  *Migration:* a KB that typed a term `tool` reads no membership for it; the type and
  every sentence naming it are gone.

- **`core.txt` drops `(genl person tangible)`.** A person is not necessarily a massed
  body: a non-biological agent can be a person with no commitment either way on
  `tangible` or `intangible`. `person` roots to `thing` directly instead.
  `arity_vocabulary_test`'s clash witness read `person` for an ordinary non-relation
  type and relied on it being tangible; `animal`, already disjoint from `relation`
  through `tangible`, takes its place.

  *Class:* **Fix** (shipped ontology content, which takes no Breaking label however far
  it moves an answer).
  *Migration:* a context that derived a term's `tangible` or `intangible` membership
  from a `person` membership alone derives neither now; state the one that holds
  directly.

- **koinii's registry mark renames from `agent` to `registered_agent`.** The name ties
  the mark to koinii's own registration rather than reading as a general-purpose agent
  classification. `CxRegistry.txt`, the two `vaelii.koinii.identity` functions reading
  and writing the mark, and `docs/koinii.md` move to the new name; `register-agent`,
  `registered-agents` and the rest of the identity API keep their names.
  `CxSpeechActs.txt` types its 12 actor positions `registered_agent`: argument 1 of the
  11 speech acts and argument 2 of `agentContext`.

  *Class:* **Fix** (shipped ontology content, which takes no Breaking label however far
  it moves an answer).
  *Migration:* a caller reading or writing `(agent ?a)` in `CxRegistry` reads or writes
  `(registered_agent ?a)` instead.

### Fixes: performance

- **The node engine builds no child whose residual asks its own goal again.** A rewrite
  through an `intersection` rule, or any rule whose antecedent is the goal or a spec of
  it, no longer re-asks the goal one level down. On the starter, `(acausal ?x)` with one
  recursive rule expands 37 nodes at depth 4, where it did not finish depth 3, and
  `(intangible Foo1)` expands 9 at every depth. The `:stats` node counts of
  `query-status` and `search-tree` drop; the answers do not change.
  [inference.md](docs/inference.md#the-node-engine-vaeliiimplinference)
  ([#101](https://github.com/vaelii/vaelii/issues/101),
  [#182](https://github.com/vaelii/vaelii/issues/182)).

  *Class:* **Fix**.

- **`argue` stops a ground side's search at its first answer, and an interrupt stops a
  node-engine search.** `argue` at a `:max-depth` returns once each ground side has an
  answer or has exhausted the bound. A `future-cancel` or `Thread.interrupt` on a running
  `query`, `query-status` or `argue` throws `InterruptedException` at the next node
  expansion. [inference.md](docs/inference.md#the-node-engine-vaeliiimplinference)
  ([#182](https://github.com/vaelii/vaelii/issues/182)).

  *Class:* **Fix**.

### Internal

- **`disjointness-coverage-ratchet` requires at least 21456 disjoint pairs, 82.91%
  disjoint and at most 7.07% unknown in the starter KB.** The bounds were 14211,
  70.70% and 19.87%. Retiring `tool` drops a type from the CxWell vantage sweep, and
  dropping `(genl person tangible)` removes pairs that edge separated; `animal`'s four
  new made-kind disjoints and `animal`/`vehicle` add pairs back. The starter KB now
  measures 21456 disjoint and 1829 unknown over 25878 pairs of 228 types.

  *Class:* **Internal**.

## Unreleased

### Additions

- **`closedExtentForArg` closes a predicate's extent for one argument value.**
  `(closedExtentForArg P n v)` grants that `P`'s believed extent is complete for the
  goals whose argument `n` is `v`, so `(not (P …))` holds there while the positive finds
  nothing. `(closedExtentForArg accountOn 2 HostA)` answers `(not (accountOn Carol HostA))`
  and leaves `(accountOn Carol HostB)` open-world. The grant is scoped to the asking
  context and belief-following, reads a closed negative rule antecedent as negation as
  failure, and is refused where it would close a cycle through negation, as
  `closed_extent_predicate` is. `closedExtentForArg1`, `closedExtentForArg2` and
  `closedExtentForArg3` are binary spellings that derive the ternary; an inert rule
  states each reverse direction. Inert rules also state that a whole-predicate grant
  entails every per-argument grant, and state `admitsArgnum`'s definition, which its
  prover answers.
  [naf.md](docs/naf.md#a-closed-extent-for-one-argument-value).

  *Class:* **Additive**.

## Unreleased

### Additions

- **`min-context-parents` and `max-context-children` read a context's nearest neighbours
  in the context lattice, and a context page's concept graph draws them.**
  `(min-context-parents kb c)` answers the contexts `c` reaches over one `genlCx` edge
  with no other such context strictly below them, and `max-context-children` the contexts
  that reach `c` over one `genlCx` edge with no other such context strictly above them.
  Both read an `except` on a `genlCx` edge as `context-up` and `context-down` read one:
  `min-context-parents` walks the edges effective for `c`, and while an `except` reaches a
  `genlCx` edge `max-context-children` holds each direct child whose own
  `min-context-parents` hold `c`. The daemon and `vaelii.client` serve both. The concept
  graph's `genlCx` rows draw these sets at every expanded node, where they drew every
  stored one-step neighbour: with `CxLeaf → CxMid → CxTop` believed and
  `(genlCx CxLeaf CxTop)` stated, the page for `CxLeaf` draws `CxTop` above `CxMid` and
  no arrow from `CxLeaf` to `CxTop`. The `genl` rows are unchanged.
  [api.md](docs/api.md), [web.md](docs/web.md#a-terms-shape-drawn).

  *Class:* **Additive**.

## Unreleased

### Breaking

- **`predExistsAll` puts the universal outside the existential, and `PredExistsAllFn`
  takes the subject.** `(predExistsAll worksFor person company)` means that every company
  has at least one person who works for it: `predAllExists` with the predicate's argument
  positions swapped. The universal outscopes the existential in every cell of the family
  that quantifies both positions. `PredExistsAllFn` takes a fourth argument, the `?indep`
  member the filler bears the predicate to, as `PredAllExistsFn` does, so it is a
  `fixed_arity_function` of arity 4 with `(argArg PredExistsAllFn 4 3)`.
  `predExistsAllPlaceholder` takes that subject before the placeholder and has arity 5.
  [predall.md](docs/predall.md#exists-the-declaration-is-a-record-and-nothing-else).

  *Class:* **Breaking** (a `predExistsAll` declaration states a different requirement, and
  the three-argument `PredExistsAllFn` and four-argument `predExistsAllPlaceholder`
  spellings break their arity).
  *Migration:* read each `predExistsAll` declaration as "every `?indep` member has some
  `?dep` member bearing the predicate to it", and restate one that meant a single filler
  for every member with a named individual and `predInstanceAll`. Add the `?indep` member
  as the fourth argument of each `PredExistsAllFn` application and as the fourth argument
  of each `predExistsAllPlaceholder` fact.
  *Breaks:* `predExistsAll`, `PredExistsAllFn`, `predExistsAllPlaceholder`

## Unreleased

- **Stopping the daemon interrupts no KB write.** An op ran on the Jetty worker that read
  the request, and a server stop interrupts a busy worker, so a stop during a disk write
  latched the store `:store-unusable`. Each op now runs on a thread the server does not
  own. Stopping a daemon `serve/start` returned waits for the op in progress, answers
  parked long polls at once, and refuses the ops still queued with 503 `:stopping`.
  [operations.md](docs/operations.md#daemon--vaeliiserve).

  *Class:* **Fix**.

## 0.26.0 — 2026-10-13 — "Upper ontology loaded into CxUniverse with a sync to the shipped files, one relation length read at every context, the `forced_monotonic_predicate` roster scoped to its readers, `time` and `situation` restructured"

| Area | Change |
|---|---|
| contexts | CxCore, CxAbstract, CxLife, CxMeasure, CxOrganism, CxReflection, CxSociety, CxSpace and CxTime removed; every file under `resources/kb/upper/` loads into CxUniverse; `vaelii.host.spindle` → `vaelii.host.sync`; `sync!` retracts a CxUniverse premise no shipped file states |
| arity | `arity/relation-length` read the same at every context; the fourteen binding functors `decontextualized_predicate`; `describe`'s `:arity-via`; `admitsArgnum`, `relation?` and `kb-integrity` read an inherited length; a metatype membership binds only at `:monotonic` |
| roster and defeat | `forced_monotonic_predicate` forces at the contexts that see and believe it; `violations`' `:forced-conclusion` read off the stored void firings; a defeat-dependency cycle read to a fixed point and, up to eight defeats, in one reading from every entry |
| KB | `time` → `uninterrupted_time` under a broad `time`; `situation` partitioned into `fluent` and `happening`; `causal` below `temporal`; `TimeOfFn`, `timeOf`, `spatial_event`, `hollow`; situations and events located or not |
| text and browser | `(set/inert S)` in a text KB; `export-text!` writes inert sentexes and refuses `:unrecovered-kb`; the dev browser syncs the shipped files and the loaded KBs both ways |
| storage | index layout 14 (`:tax-named`); a recover from the records writes the index image once |
| answers | `Quote` forms are constants to unification; `bravely`/`cautiously` read the asking context; `handle-of` on an `exceptWhen` answers the exception; the uberjar builds under a 255-byte file name limit |

Six entries are **Breaking** and none is a **Refusal**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.25.0 caller changes.

| If your code… | Then |
|---|---|
| names CxCore, CxAbstract, CxLife, CxMeasure, CxOrganism, CxReflection, CxSociety, CxSpace or CxTime, requires `vaelii.host.spindle`, or states author premises in CxUniverse | rebuild the store from the shipped files; require `vaelii.host.sync`; state author content in a context of its own |
| relies on `time` being a moment or a stretch, on a `situation` being static or an event, or states an `initiates` or `terminates` subject only `event` or `temporal` | write `uninterrupted_time` or `uninterrupted_situation`; state the subject `causal_event` |
| binds a relation's length in one context only, or through a `:default` metatype membership | make it a relation of its own per theory; state the membership and its edges `:monotonic`; read `describe`'s `:arity-via` |
| relies on a `forced_monotonic_predicate` declaration at a context that does not see or believe it | state the declaration in a context every reader of the predicate sees |
| reads `:forced-conclusion` entries from `preview`'s `:violations`, or clears them with `clear-violations!` | read `why-not` on the conclusion, or `violations` after the write |
| opens a durable index or a `:disk-snapshot` image written by 0.25.0 | nothing: the first open rebuilds the index from the records |

### Breaking

- **CxUniverse holds the whole upper ontology, and a sync locks its premises to the
  shipped files.** `core.txt` and every other file under `resources/kb/upper/` load into
  CxUniverse, and CxCore, CxAbstract, CxLife, CxMeasure, CxOrganism, CxReflection,
  CxSociety, CxSpace and CxTime are no longer contexts. A vocabulary KB loads the whole
  upper layer. `vaelii.host.sync/sync!` retracts a CxUniverse premise no shipped file
  states and restates one whose strength differs; it leaves every `genlCx` edge and every
  lifted copy alone. A binding an upper file states is a CxUniverse premise and has no
  copy. The starter stores 3,497 sentexes and 1,954 justifications, where with one
  context per upper file and the length-binding copies below it stored 4,177 and 2,631;
  its load takes a median 5.2 s where it took 12.6 s, and its recover 0.33 s where it
  took 2.6 s. The ontology adds `(type organism)`, `(typeGenl folk_species organism)` and
  `(typeGenl folk_biological_class organism)`, which the `predAllSpecified typeGenl` audit
  read missing once one context held both files.
  [contexts.md](docs/contexts.md#the-context-topology),
  [catalog.md](docs/catalog.md#a-loaded-kb-states-this-engines-shipped-contexts).

  *Class:* **Breaking** (the nine upper contexts are gone; an author premise stated in CxUniverse is retracted at the next sync; `vaelii.host.spindle` is `vaelii.host.sync`).
  *Migration:* rebuild the store from the shipped files; state author content in a context of its own, below CxUniverse or wired above it with `(genlCx CxUniverse CxYours)`.
  *Breaks:* `CxCore`, `CxAbstract`, `CxLife`, `CxMeasure`, `CxOrganism`, `CxReflection`, `CxSociety`, `CxSpace`, `CxTime`, `vaelii.host.spindle`, `sync-spindle!`, `spindle/shipped`, `seed/root-contexts`, `:spindle`, `CxCore.txt`, `CxUniverse.txt`

- **`time` and `situation` each gain a broad parent, and causation is tied to time.**
  `(partition temporal uninterrupted intermittent)` divides what is in time by whether it
  has a gap. The old `time` is renamed `uninterrupted_time`, and `time_point` and
  `time_interval` partition it. A new `time` is partitioned into `uninterrupted_time` and
  `intermittent_time`, each the intersection of `time` with one side. The old
  `situation`'s partition into `static_situation` and `event` moves to
  `uninterrupted_situation`, the intersection of `uninterrupted` and `situation`. The
  broad `situation` is partitioned into `fluent` and the new `happening`;
  `static_situation` is the intersection of `uninterrupted` and `fluent`, and `event` the
  intersection of `uninterrupted` and `happening`. `causes`' effect, `(disjoint time
  situation)` and `(orthogonal situation spatial)` name the broad `situation`;
  `(orthogonal uninterrupted_situation spatial)`, `(orthogonal situation spatiotemporal)` and
  `(orthogonal happening spatial)` are stated too, and `(disjoint tangible situation)`
  holds: a situation is located in its region, not made of the matter in it. A tangible
  is `uninterrupted` by default. `(partition thing causal
  acausal)` and `(genl causal temporal)` move to core.txt, beside `(genl atemporal acausal)`.
  `initiates` and `terminates` take a `causal` first argument. A rule in CxUniverse
  concludes `(instantNotAfter (StartFn ?cause) (StartFn ?effect))` from `(causes ?cause
  ?effect)`. `(genl fluent aspatial)` is dropped, since a held state can have a place.
  `quantity` is below `temporal` and `acausal` and disjoint from `situation`. time.txt adds
  `TimeOfFn`, the time a temporal thing occupies, with its corresponding predicate
  `timeOf`, and a rule making every time its own time.
  [taxonomy.md](docs/taxonomy.md#the-three-partitions-of-thing),
  [time.md](docs/time.md#the-time-a-thing-occupies).

  *Class:* **Breaking** (`time_point` and `time_interval` no longer cover `time`, a
  `situation` denied being an `event` is no longer concluded a `static_situation`, and an
  `initiates` or `terminates` subject must be `causal`).
  *Migration:* write `uninterrupted_time` where a KB relied on `time` being a moment or a
  stretch, and `uninterrupted_situation` where it relied on a `situation` being static or
  an event. A KB that states `(fluent X)` beside `(spatial X)` stores both. An effect
  stated to start before its cause is a qualitative inconsistency once the point
  reasoner is registered. State the subject of an `initiates` or `terminates` fact
  `causal_event` where the KB states it only `event` or `temporal`: under
  `VAELII_ASSERTIVE_ARG_TYPES=0` the fact is refused `:arg-type`.
  *Breaks:* `time`, `situation`, `fluent`, `initiates`, `terminates`, `causes`

- **A relation's length is one function, read the same at every context, and a length
  binding stated in one context binds at every context that sees CxUniverse.** core.txt
  declares the fourteen binding functors (`arity`, `arityMin`, the nine exact-arity
  classes and the three `variable_arity` classes) `decontextualized_predicate` at
  `:monotonic`, so a binding stated outside CxUniverse has a copy there. A tuple stated
  in CxUniverse that breaks a binding stated in a context below it was believed at
  CxUniverse; it is now OUT there, and at every reader that sees CxUniverse.
  `arity/relation-length` answers what binds a relation's length for the
  argument-position check, the arity nogood, `describe`'s `:arity`, `admitsArgnum` and
  `kb-integrity`'s undeclared-arity: a relation bound to no length of its own takes the one
  exact length the bound predicates above it agree on in each of them, `describe` names
  the predicate it is bound on as `:arity-via`, and `relation?` answers true for an
  inherited length of two or more where no visible declaration answers. Each reader
  now reads a binding, a `variable_arity` membership and a `genl` edge stated in any
  context, so a binding or an edge another context states binds the length at a reader
  that does not see it. An engine grammar term's length is its `:shape` whatever the KB
  binds (`(arity genl 3)` leaves `genl` binary). `thereExists`'s shape takes two
  arguments, and the shapes of `intersection`, `covering`, `separating`, `partition`,
  `commutativeInArgs`, `different`, `lessThan`, `greaterThan`, `partitionedByType` and
  `termsRelated` carry the floor core.txt's `arityMin` states. A metatype membership binds
  only at `:monotonic` with `:monotonic` edges to its exact-arity class, at every reader;
  core.txt states the memberships and the eight `genl` edges its own metatypes bind through
  at `:monotonic`. Two own lengths leave the relation unbound in `describe` and
  `admitsArgnum` where the `(arity P n)` table answered, `variable_arity` releases a
  stated exact length there, `admitsArgnum` no longer picks the class first by name, and
  the argument-position check reads a relation under two lengths above it, or carrying
  `variable_arity` under a bound one, as unbound. [taxonomy.md](docs/taxonomy.md#arity),
  [contexts.md](docs/contexts.md#what-the-shipped-ontology-declares-it-of).

  *Class:* **Breaking** (a tuple that breaks a binding stated in another context goes OUT at every context that sees CxUniverse; `sentexes-with-functor` and the counts of the fourteen functors include the CxUniverse copies; `describe`'s `:arity`, `admitsArgnum` and the argument-position check read bindings and `genl` edges in every context and no `:default` metatype route; `describe`'s `:arity`, `admitsArgnum`, `relation?` and `kb-integrity`'s undeclared-arity read a length inherited through `genl`; an engine term's KB binding is ignored).
  *Migration:* a relation meant to take a length in one theory only, or two lengths in two contexts, is a relation of its own per theory; state a metatype membership that should bind a length, and its edges to the exact-arity class, `:monotonic`, or state the exact-arity class membership; read `describe`'s `:arity-via` to tell an inherited length from an own one; filter a read of a binding functor on `:context` where the copies are unwanted.
  *Breaks:* `describe`, `admitsArgnum`, `relation?`, `arity`, `arityMin`, `variable_arity`, `kb-integrity`, `sentexes-with-functor`

- **A `forced_monotonic_predicate` declaration forces its predicate at the contexts that
  see and believe it.** A declaration stated in one context put the predicate on the
  roster in every context, so a reader that does not see the declaration read a
  membership of it as never the loser, a denial of one as inert, a rule from it as a
  roster rule, and a firing concluding one from antecedents off the roster as void. Those
  four now follow the reader, and only the baseline's declarations stay global. A
  declaration in CxUniverse reads as one stated in any other context. A declaration a
  `:monotonic` denial defeats no longer forces its predicate at the contexts below the
  denial, and a declaration a placed `defeat` names at a context makes no denial inert
  there. A declaration whose `defeat` an `except` hides keeps forcing its predicate where
  the `except` is seen, and an `except` of a placed `defeat` releases its loser beside a
  declaration another context states. A conclusion whose valid firings are all void at
  its context is read as hidden there. A declaration arriving after a `:default` dilemma
  defeats the rival, as one arriving first does. Writing or retracting `(genlCx C D)`,
  where `D` holds a declaration, reports to `watch`, `preview` and
  `edit-with-consequences!` the denials the edge makes inert or releases. A declaration's
  reach walks the contexts below the declaring one at most once
  ([#129](https://github.com/vaelii/vaelii/issues/129)).
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster),
  [nmtms.md](docs/nmtms.md#the-published-window).

  *Class:* **Breaking** (belief at a context that does not see, or does not believe, a declaration stated below it, beside it or in CxUniverse).
  *Migration:* state the declaration in a context every reader of the predicate sees; a context with no `genlCx` path to CxUniverse needs one.
  *Breaks:* `forced_monotonic_predicate`, `forced_monotonic_between_predicates`, `has-prop?`

- **`violations` reads its `:forced-conclusion` entries off the stored void firings.**
  An entry stands exactly while its firing is stored and void at some reader: one per rule and
  conclusion, gone with the firing, back when the firing is derived again, and the same
  in every arrival order and after `recover`. `:sentence` is the conclusion's stored spelling, the entry
  carries no `:run`, the entries follow the ledger's in content order, and
  `clear-violations!` and the 1000-entry cap do not remove one. `preview`'s `:violations`
  does not list them. The chainer logs a convicted firing at `:warn` once, as its
  justification is added ([#129](https://github.com/vaelii/vaelii/issues/129)).
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Class:* **Breaking** (a `:forced-conclusion` entry is read off the stored firings, not filed in the ledger).
  *Migration:* read `why-not` on the conclusion, or `violations` after the write, in place of `preview`'s `:violations`; match the entry against the stored spelling.
  *Breaks:* `violations`, `clear-violations!`, `preview`

- **The index is at layout 14: the stored `except` and `defeat` facts naming a taxonomy
  supporter join the index.** The count trie `[:tax-named rel f ctx]` files each positive
  `except` or `defeat` whose target installs a `genl`, `genlCx` or flat-cache key. A
  scoped taxonomy read after a write reads one count where it built the set of every
  stored `except` and `defeat` target on `memory-columnar`. A stored index, a
  `:disk-snapshot` image or a dump of layout 13 is rebuilt from the records at its first
  open or import, and answers are unchanged.
  [indexing.md](docs/indexing.md#9-the-taxonomys-supporter-families).

  *Class:* **Breaking** (a stored index or a `:disk-snapshot` image of layout 13 is rebuilt from the records at its first open, and a dump of layout 13 reindexes on import).
  *Migration:* none; the first open rebuilds a durable index.
  *Breaks:* `index-entries`, `:disk-log`, `:disk-snapshot`

### Additions

- **Situations, held states and events are each located or not, and `spatial_event` names
  an event located in some space.** core.txt states `(orthogonal situation aspatial)`,
  `(orthogonal static_situation spatial)`, `(orthogonal static_situation aspatial)`,
  `(orthogonal event spatial)` and `(orthogonal event aspatial)`, beside `(orthogonal
  situation spatial)`, and states `event` and `static_situation` each orthogonal to
  `spatiotemporal`, beside `(orthogonal situation spatiotemporal)`. A debt owed, a treaty
  in force and a contract expiring at midnight are located nowhere; a cat on a mat and the
  battle of Waterloo have a place. An `orthogonal` is not inherited along `genl`, so each
  kind's pair is stated. abstract.txt defines `(intersection spatial_event event
  spatial)` and states `(genl spatial_event spatiotemporal)`, so a battle stated an event
  and spatial reads `spatial_event` and `spatiotemporal`. `ontology_test` pins each pair
  with a witness, the derived edge from `event` to `temporal`, and the `spatial_event`
  edges and membership.

  *Class:* **Additive** (shipped ontology content).

- **`hollow` names a shape, and `container` is placed under `made` and `hollow`.**
  abstract.txt mints `hollow`: a thing that has, at that time, an interior space other
  things can occupy, such as a cup, a building, a cave, a pitcher plant or a cupped hand.
  `hollow` is below `spatiotemporal`, orthogonal to `made`, `organism`, `body_part`,
  `biological` and `food`, and disjoint from `substance`. abstract.txt states `(genl
  container hollow)` beside `(genl container made)`, so `container`, `building` and
  `dwelling` reach `hollow`. `container` keeps its disjoints from `organism`, `person` and
  `substance`. A made hollow thing is not concluded a container, so a potted pitcher plant
  is no clash. A pitcher plant and a lab-grown bladder are biological and hollow, and
  `subsumption-status` reads `biological` and `hollow` `:orthogonal`. `ontology_test` pins
  the placement, the orthogonals, the edges, and a made hollow organism and a hollow body
  part as no clash.

  *Class:* **Additive** (shipped ontology content).

- **A text KB spells an inert sentex `(set/inert S)`.** `load-text!` and the shipped
  ontology's loader store `S` through `assert-inert`: stored, indexed and durable, never
  believed, chained or named in a clash. A rule under the wrapper is refused
  `:not-indexable`, as `assert-inert` refuses one, and `(set/inertRule R)` stays the form
  for a believed rule that fires in neither direction. `(set/inert …)` and
  `(set/monotonic …)` nested in either order are refused `:shape`. `export-text!` writes
  every inert sentex, a solve's labeling and classification contexts among them, under the
  wrapper, and refuses `:unrecovered-kb` over a KB whose belief is not built when the store
  holds a sentex that is neither a premise nor a TMS node
  ([#178](https://github.com/vaelii/vaelii/issues/178)).
  [kbs.md](docs/kbs.md#text-you-exported-yourself).

  *Class:* **Additive**.

- **The dev browser syncs the shipped KB files and the loaded KBs both ways.** Under
  `VAELII_DEV`, the first request after a file under `resources/kb/upper/` or
  `resources/kb/middle/` is saved, added or removed submits one `:sync` job that runs
  `sync/sync!` on every in-process KB that accepts writes and files each report on its
  entry. After each non-GET request, what the starter KB gained or lost in CxUniverse and
  the middle contexts is written into those files as line edits (`sync/write-back!`),
  each premise beside its term's `comment`. [web.md](docs/web.md#working-on-it-lein-browser),
  [catalog.md](docs/catalog.md#a-loaded-kb-states-this-engines-shipped-contexts).

  *Class:* **Additive**.

### Fixes: answers

- **A query naming a stored quoted form's variable answers instead of overflowing the
  stack.** Asking `(awesome_rule (Quote (implies (poodle ?x) (dog ?x))))` with the stored
  spelling threw `StackOverflowError`, and the `?y` spelling answered true by binding `?y`
  to the quoted `?x`. A `(Quote …)` form is now a constant to matching: the stored
  spelling answers true, another spelling or a ground instance answers false, and a query
  variable named like a quoted one is not bound by it
  ([#167](https://github.com/vaelii/vaelii/issues/167)).
  [inference.md](docs/inference.md#quoted-forms-in-unification).

  *Class:* **Fix**.

- **`(bravely S)` and `(cautiously S)` read the sentexes of `S` and the dilemmas the asking
  context sees.** `S` stored in a context the asker inherits answered false to both, and the
  classification read every dilemma of the KB, so a context that reads no dilemma answered
  `(cautiously S)` false for a sentence it believes. The prover now reads the sentexes of
  `S` in the asker's `genlCx` ancestor set that it believes and sees, and classifies them
  against the dilemmas `contradictions` reports to that context
  ([#154](https://github.com/vaelii/vaelii/issues/154)).
  [labeling.md](docs/labeling.md#reading-bravecautious-without-committing-bravely-s--cautiously-s).

  *Class:* **Fix**.

- **`handle-of` on an `(exceptWhen Q R)` sentence answers the exception's handle.** It
  answered the rule's handle whatever `Q` was, so `retract!` on that handle removed the
  rule. It now answers the handle `assert` returns for the exception, nil when no such
  exception is stored, and nil for a rule stored as several.
  [exceptions.md](docs/exceptions.md#storage-and-identity).

  *Class:* **Fix**.

- **A defeat-dependency cycle is read again until no value changes, and a cycle of at most
  eight defeats reads the same from every defeat it is entered at.** The walk broke every
  cycle it met by putting the first loser's defeats in force and holding the others out of
  force without reading them again, so a `:default` membership that loses to a
  `:monotonic` firing stayed believed beside a guard defeat of a second, guarded copy of
  the firing's rule. It also kept the values of a cycle it closed even when a member's
  re-read had met an outer open defeat read as out of force, so the answer depended on
  which defeat of the cycle was asked first
  ([#129](https://github.com/vaelii/vaelii/issues/129)). Each member is now read again
  with the others held, a cycle the answer does not move reads as it stands, and a cycle
  of at most eight defeats takes its first consistent reading in content order, in force
  first. A cycle of more than eight defeats takes the values of at most 2m + 1 passes,
  and the walk does not hold it to one reading across entries. A cycle closed inside a
  member's read and resting on no member is closed once per read, not once per assignment
  of the cycle around it. [nmtms.md](docs/nmtms.md#a-defeat-dependency-cycle).

  *Class:* **Fix**.

- **A nogood's loser that a guarded firing's antecedents include is hidden beside the
  firing's guard defeat.** A guard defeat's force read the firing's own antecedents, so a
  `:default` conclusion beside a `:monotonic` denial, from which a guarded rule fired that
  its blocker blocks, read the guard defeat and the nogood's defeat as a cycle, and the
  content order could leave the conclusion believed. A guard defeat's force now reads its
  blockers alone. [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

  *Class:* **Fix**.

- **A mint is not drawn again from an inert sentex.** After a retraction released an
  argument-type mint, the mint was justified again on an inert sentex (`assert-inert`,
  `(set/inert S)`) that would draw it, which is no TMS datum. Under the reference TMS the
  next retraction beneath that mint threw `ClassCastException`.
  [argtypes.md](docs/argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on).

  *Class:* **Fix**.

### Fixes: order independence

- **A late `symmetric` mark, and a record a rule concludes beside a withheld mint, leave
  the argument-type justifications of the other arrival order.** A mark arriving after
  its facts kept the mints drawn over each row's former spelling, so a mint named the
  declaration of the other position, and folding two rule-concluded spellings left
  justifications naming a handle with no record. A record a rule concluded, onto which a
  firing of the same write had minted, did not take the mints withheld before it arrived.
  A text export reloaded in content order then held other justifications than the KB
  loaded in authored order ([#173](https://github.com/vaelii/vaelii/issues/173)).
  [canonicalization.md](docs/canonicalization.md#a-mark-arriving-after-the-facts-migrates-them),
  [argtypes.md](docs/argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on).

  *Class:* **Fix**.

- **Which of two equally good routes a route search keeps no longer depends on edges off
  every route.** Two partial routes tied on the search queue's key were popped in an order
  set by whatever else was queued, so an unrelated edge could change the witness a
  placement or an inherited conclusion names, and with it a justification's antecedents.
  Ties are now ordered by the routes' printed terms and supporters from the source on.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

  *Class:* **Fix**.

### Fixes: build

- **`lein uberjar` builds on a filesystem with a 255-byte file name limit.** AOT
  compilation of `vaelii.impl.taxonomy` threw `File name too long` on ext4, btrfs and
  APFS, so the uberjar and the container image did not build. The longest class file
  name the build writes is now 191 bytes, and `lein release-gate` builds the uberjar and
  loads `vaelii.core` from it ([#179](https://github.com/vaelii/vaelii/issues/179)).
  [operations.md](docs/operations.md#container--the-daemon-as-an-image).

  *Class:* **Fix**.

### Fixes: performance

- **A declaration or `genl` edge asserted under `*bulk-load?*` draws no argument types
  over the stored facts.** A bulk load skipped only the fact's own derivations; a
  declaration or a predicate edge still swept the stored facts and minted, and each minted
  edge walked the stored rule graph, so a bulk load's cost grew with the stored rules
  once per declaration. `v/record-arg-types` records the derivations
  after the load. [argtypes.md](docs/argtypes.md#where-it-does-not-mint).

  *Class:* **Fix**.

- **The settle that places what a rebuilt index queued writes the arity family's
  placements a batch at a time, and places a nogood over one edge without a walk.** A
  placement pass read the routes of every nogood of a family before it wrote the first,
  so a family of millions held a plan for each in the heap. Past 4,096 nogoods it now
  reads and writes them a batch at a time in the same order. A witness from a predicate
  with an edge straight to its target, and a route search whose source's only edge ends
  at the target, answer without walking. Which nogoods are placed, where, and on which
  antecedents is unchanged. [nmtms.md](docs/nmtms.md#the-placement-pass).

  *Class:* **Fix**.

### Internal

- **A recover from the records writes the index image once, after its settles.** The
  first open of a store with no index image wrote the image again after each settle,
  and each later settle made the previous image stale. A process
  killed during the recover reopens from the records.
  [storage.md](docs/storage.md#the-cadence-and-whose-thread-it-runs-on).

  *Class:* **Internal**.

- **An index write allocates 1.3x to 1.5x fewer bytes per sentex.** The non-trie families
  of a write (`flat-family-adds`) conj their ops onto the store's one batch, where each
  built a vector that was concatenated into another. A reindex of a synthetic corpus
  allocates 37.0 KB per sentex on `memory` and 27.5 KB on `memory-columnar` before, and
  27.5 KB and 18.7 KB after; the index is entry-for-entry identical.
  [indexing.md](docs/indexing.md).

  *Class:* **Internal**.

- **A settle's inherited-clash discovery reads only the carried entries a move names.** It
  tested every carried entry against each settle's moves, so the settle's cost grew with
  the stored claims holding an entry. The entries are now filed under what each reads, and
  `lein perf`'s `inherited-entry-except` reads 0.92x where it read 1.56x. Answers are
  unchanged. [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).

  *Class:* **Internal**.

- **`lein perf-ab` times the arity paths and the starter load and recover in absolute
  milliseconds.** Four probes, `arity-assert`, `arity-edge-move`, `arity-read` and
  `arity-recover`, run a write over bound predicates, a `genl` edge move under arity
  conflicts, `describe` and `admitsArgnum` reads, and a disk open with its first write.
  `starter-load` and `starter-recover` time `vaelii.starter/load-into` over an empty
  in-memory KB and `recover` over a loaded one. `lein gate` prints `perf-ab owed` with
  the command when a pending diff changes `decide/arity.clj` or an arity function of
  `checks`, `kb` or `provers`, and names the starter probes when a shipped KB file or its
  loader is about to land.

  *Class:* **Internal**.

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
