# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.25.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

- **A mint is not drawn again from an inert sentex.** After a retraction released an
  argument-type mint, the mint was justified again on an inert sentex (`assert-inert`,
  `(set/inert S)`) that would draw it, which is no TMS datum. Under the reference TMS the
  next retraction beneath that mint threw `ClassCastException`.
  [argtypes.md](docs/argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on).

  *Class:* **Fix**.

- **`lein uberjar` builds on a filesystem with a 255-byte file name limit.** AOT
  compilation of `vaelii.impl.taxonomy` threw `File name too long` on ext4, btrfs and
  APFS, so the uberjar and the container image did not build. The longest class file
  name the build writes is now 191 bytes
  ([#179](https://github.com/vaelii/vaelii/issues/179)).
  [operations.md](docs/operations.md#container--the-daemon-as-an-image).

  *Class:* **Fix**.

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

### Breaking

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
  acausal)` and `(genl causal temporal)` move to CxCore, beside `(genl atemporal acausal)`.
  `initiates` and `terminates` take a `causal` first argument. A rule in CxUniverse
  concludes `(instantNotAfter (StartFn ?cause) (StartFn ?effect))` from `(causes ?cause
  ?effect)`. `(genl fluent aspatial)` is dropped, since a held state can have a place.
  `quantity` is below `temporal` and `acausal` and disjoint from `situation`. CxTime adds
  `TimeOfFn`, the time a temporal thing occupies, with its corresponding predicate
  `timeOf`, and a rule making every time its own time.
  [taxonomy.md](docs/taxonomy.md#the-three-partitions-of-thing),
  [time.md](docs/time.md#the-time-a-thing-occupies).

  *Class:* **Breaking** (`time_point` and `time_interval` no longer cover `time`, and a
  `situation` denied being an `event` is no longer concluded a `static_situation`).
  *Migration:* write `uninterrupted_time` where a KB relied on `time` being a moment or a
  stretch, and `uninterrupted_situation` where it relied on a `situation` being static or
  an event. A KB that states `(fluent X)` beside `(spatial X)` stores both. An effect
  stated to start before its cause is a qualitative inconsistency once the point
  reasoner is registered.
  *Breaks:* `time`, `situation`, `fluent`, `initiates`, `terminates`, `causes`

### Additions

- **A situation or a held state may be located nowhere.** CxCore states
  `(orthogonal situation aspatial)`, `(orthogonal static_situation spatial)` and
  `(orthogonal static_situation aspatial)`, beside `(orthogonal situation spatial)`: a debt
  owed and a treaty in force are located nowhere, and a cat on a mat is a held state with
  a place. An `orthogonal` is not inherited along `genl`, so each pair is stated.
  `ontology_test` pins each pair with a witness.

  *Class:* **Additive** (shipped ontology content).

- **An event may be located or not.** CxCore states `(orthogonal event spatial)` and
  `(orthogonal event aspatial)`: the battle of Waterloo is located, and a contract
  expiring at midnight is not. `ontology_test` pins both pairs with a witness and the
  derived, unstated edge from `event` to `temporal`.

  *Class:* **Additive** (shipped ontology content).

- **`spatial_event` is an event located in some space.** CxAbstract defines
  `(intersection spatial_event event spatial)` and states
  `(genl spatial_event spatiotemporal)`, so a battle or a smelting stated an event and
  spatial reads `spatial_event` and `spatiotemporal`, and a contract expiring at midnight
  stays an event that is no spatial event. `ontology_test` pins the edges and the
  membership.

  *Class:* **Additive**.

- **An event and a static situation are spatiotemporal or not.** CxCore states `event`
  and `static_situation` each orthogonal to `spatiotemporal`, beside
  `(orthogonal situation spatiotemporal)`. An `orthogonal` is not inherited along `genl`,
  so each kind's pair is stated. A battle and a cat on a mat are spatiotemporal; a
  contract expiring and a treaty in force are not. `ontology_test` pins both pairs with a
  witness.

  *Class:* **Additive** (shipped ontology content).

- **`hollow` names a shape, and `container` is placed under `made` and `hollow`.**
  CxAbstract mints `hollow`: a thing that has, at that time, an interior space other
  things can occupy, such as a cup, a building, a cave, a pitcher plant or a cupped hand.
  `hollow` is below `spatiotemporal`, orthogonal to `made`, `organism`, `body_part` and
  `food`, and disjoint from `substance`. CxAbstract states `(genl container hollow)`
  beside `(genl container made)`, so `container`, `building` and `dwelling` reach
  `hollow`. `container` keeps its disjoints from `organism`, `person` and `substance`. A
  made hollow thing is not concluded a container, so a potted pitcher plant is no clash.
  `ontology_test` pins the placement, the orthogonals, the edges and a made hollow
  organism as no clash.

  *Class:* **Additive** (shipped ontology content).

- **`biological` and `hollow` are orthogonal.** A pitcher plant and a lab-grown bladder
  are biological and hollow, a cup is hollow and not biological, and a leaf is
  biological and not hollow. CxAbstract states `(orthogonal biological hollow)` beside
  `hollow`'s orthogonals to `organism` and `body_part`, since an `orthogonal` is not
  inherited along `genl`. `subsumption-status` reads the pair `:orthogonal`.
  `ontology_test` pins the declaration and a hollow body part as no clash.

  *Class:* **Additive** (shipped ontology content).

## 0.25.0 — 2026-10-11 — "Context NATs reified by position under `(result F context)`, the expression lattice in CxReflection, more placed contradictions and separations, `IndexStore` family methods and index layout 13"

| Area | Change |
|---|---|
| context NATs | every ground application in a context slot reifies to a `cx/` constant; `(result F context)` in CxUniverse replaces `context_denoting_function`; `check` reads the slot as `assert` stores it |
| nogoods | a `:monotonic` metatype membership binds its member's arity; a membership beside a denial of a supertype is a `:supertype` nogood; a separated membership argument preservation reaches is an `:inherited` nogood and undercuts `ask`; `empty`/`nonempty` preservation is known-true |
| rules | a firing a `:default` `exceptWhen`/`unknown` blocker blocks is stored with a guard `defeat`; a forward `(disjoint ?a ?b)` antecedent matches every separation; `query-status` reads `:incomplete` over an open transitive goal |
| KB | CxReflection holds the expression lattice; `atomic_formula` → `predication`, `atomic_sentence` → `closed_predication`, `relation_application` → `non_atomic_expression`; `at_least_*_relation` → `at_least_binary`/`at_least_ternary`; `relation_type` removed; CxComputing, CxPerception, CxSocialExtension and CxNormalPhysicalConditions opt-in theories; `causes` in CxAbstract |
| argument types | `argArg`, `resultArg`; a mint is placed at each maximal context that sees the fact and the declaration |
| storage | `IndexStore` reads and writes through seven family methods and has 20; index layout 13; columnar snapshot format 5; reasoning image `format-version` 15 |
| wire and browser | a request-named path is refused `:path-not-served` unless `VAELII_REQUEST_PATHS=1`; sandboxes capped and server-minted; catalog capped at 16 KBs |
| new API | `try-assert`, `min-genls`, `max-specs`, `types` with a context, `sentex/closed?` |

Fourteen entries are **Breaking** and four are **Refusals**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.24.0 caller changes.

| If your code… | Then |
|---|---|
| states `(context_denoting_function F)` | state `(result F context)` in CxUniverse |
| relies on a wrong-length tuple of a predicate bound through a `:monotonic` metatype membership | state the membership `:default` |
| reads `ask`, `conflicts` or `contradictions` beside a separated membership argument preservation reaches | nothing: a reading meant to hold is stated known-true |
| dispatches on a `conflicts` or `contradictions` report's `:kind` | handle `:supertype` |
| reads a rule firing's presence with `handle-of` beside an `exceptWhen` or `unknown` blocker | read belief with `believed?`, `in?` or `sentexes-matching` |
| writes `atomic_formula`, `atomic_sentence`, `relation_application`, `at_least_binary_relation`, `at_least_ternary_relation` or `relation_type` | write `predication`, `closed_predication`, `non_atomic_expression`, `at_least_binary`, `at_least_ternary`; `relation_type` has no replacement |
| matches `:not-ground` on a quantified fact | match `:not-well-formed` |
| dispatches on `query-status`'s `:status` | handle `:incomplete` |
| states `temporalDistance` facts in two dimensions in one context | state them in units of one dimension |
| exports, diffs, loads or writes a path over the wire or the browser | start the server with `VAELII_REQUEST_PATHS=1`, or work in the process that owns the KB |
| implements `IndexStore` out of tree, or calls a retired index read or write | implement the seven family methods; call the `rules/` or `reads/` entry point |
| opens a durable index or imports a dump written by 0.24.0 | nothing: the first open or import rebuilds the index from the records |
| opens a `:disk-snapshot` reasoning image written by 0.24.0 | nothing: the first open recovers in full once and writes a new image |
| calls `disjointness-audit` with no context | pass `CxUniverse` to keep the upper ontology's vantage |
| keeps abductions with `{:keep? true}` | `abduce-discard!` one before keeping a 65th |
| opens a browser sandbox or loads a 17th KB | set `VAELII_SANDBOX_KEY` to keep sessions; unload a KB first |
| states a value where a type is named | retract it |
| asserts `totalDuration` or `overlapDuration` | state the `length` facts instead |

### Breaking

- **A ground application in a context slot is stored whatever is declared about its
  head, and `(result F context)` replaces `context_denoting_function`.** `assert` refused a
  fact whose context slot `(F a…)` arrived before `(context_denoting_function F)` or after
  its retraction, and stored it otherwise, so the stored set depended on arrival order.
  Every ground application in a context slot now reifies to a `cx/` constant, whichever
  of the fact and a hiding `except` or `defeat` arrives first. A read names that context
  through the application while CxUniverse believes `(result F context)`, stated in
  CxUniverse or a context CxUniverse sees, and otherwise refuses it for `:shape` with a
  message naming the declaration. The same expression in argument position mints its own
  `nat/` constant when `F` is a `reifiable_function`. `check`, `check-edit` and the wire
  `:check` op resolve the slot to its stored `cx/` constant, or to the one the
  expression's content names, without minting, so they report what `assert` refuses. The
  disjointness audit no longer sweeps `context_denoting_function`.
  [context-nat.md](docs/context-nat.md#the-representation-reify-the-outer-function-keep-the-argument-structural).

  *Class:* **Breaking** (`context_denoting_function` is no longer vocabulary, and an undeclared ground application in a context slot is stored instead of refused).
  *Migration:* replace each `(context_denoting_function F)` with `(result F context)`.
  *Breaks:* `context_denoting_function`, `:context-denoting`, `assert`

- **A `:monotonic` metatype membership binds its member's arity.** With
  `(instance_relation_predicate P)` and no `(binary_predicate P)`, a three-place `P` fact
  was believed, although every other arity reader answered two. The arity nogood now
  reads a `:monotonic` membership `(T P)` as a binding when `T` reaches an exact-arity
  class through `:monotonic` `genl` edges the reader sees, and places the wrong-length
  tuple as a nogood grounded on the membership and those edges, in every arrival order and
  after a recover. A `:default` membership or edge binds nothing. CxCore states its
  metatypes' edges into the exact-arity classes `:monotonic`, the shipped predicate
  memberships of those metatypes are `:monotonic`, and 13 `(binary_predicate P)` lines
  that `(instance_relation_predicate P)` now binds are gone. The starter's disjointness
  audit, `conflicts` and `contradictions` read the same before and after.
  [taxonomy.md](docs/taxonomy.md#arity).

  *Class:* **Breaking** (a tuple of a predicate bound through a `:monotonic` metatype membership is placed as an arity nogood, and a `:monotonic` one is reported in `conflicts`).
  *Migration:* a KB that relies on a wrong-length tuple of such a predicate states the
  membership `:default`.
  *Breaks:* `conflicts`, `instance_relation_predicate`, `transitive`

- **A membership of a separated type that argument preservation reaches is placed against
  the stored membership it clashes with, and `ask` reads the stored one as a claim
  against it.** Given `(partition whole_kind down_kind up_kind)` or `(disjoint down_kind
  plain_kind)`, `(transitiveInArgInverse down_kind 1 genl)`, `(genl lower upper)` and
  `(down_kind upper)`, a stored `(up_kind lower)` or `(plain_kind lower)` left `lower` in
  both types: `ask` answered `(down_kind lower)` true, a forward rule over it fired, and
  neither `conflicts` nor `contradictions` reported it.
  - The settle places a known-true reached membership beside the stored one as an
    `:inherited` nogood in every arrival order: a `:default` stored side loses, and a
    known-true pair is a conflict. A reading with a `:default` reason forms no nogood.
  - `ask` reads the stored membership as a claim against the reached one where the
    separation is seen, and answers the reached membership only where the stored one is
    not believed. A forward firing beside a `:default` membership is stored with a defeat
    resting on it, and one beside a `:monotonic` membership is blocked. A membership, a
    separation or a `genl` edge arriving or leaving re-joins the rules and re-checks the
    exceptions over the predicates it moves.
  - CxCore states `(transitiveInArgInverse empty 1 genl)` and `(transitiveInArg nonempty
    1 genl)` known-true, since each holds by the definition of `genl`, so `(empty outer)`
    and `(genl inner outer)` stated `{:strength :monotonic}` beside `(nonempty inner)` is
    an `:inherited` nogood on each side.

  A separation's supports are read once per pair under the question memo.
  [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).

  *Class:* **Breaking** (`ask` answers no reached unary membership a believed membership of a separated type denies, forward firings over one are defeated or blocked, and `conflicts` and `contradictions` report the new clashes).
  *Migration:* none; a reading meant to hold over the membership is stated known-true, and
  the inherited nogood then decides the pair.
  *Breaks:* `ask`, `ask?`, `sentexes-matching`, `conflicts`, `contradictions`

- **A membership beside a denial of a supertype of its type is a nogood.** `(dog Rex)`,
  `(genl dog animal)` and `(not (animal Rex))` were all believed and nothing was reported,
  unless a cover was stored over `dog`. The settle places the membership and the denial as
  a nogood of kind `:supertype`, grounded on the `genl` edges between the two types, in
  every arrival order: a `:default` side loses, and a known-true pair is a conflict. A
  denial's write reads the denied type's specializations, or each held type's closure
  where those are fewer, so its cost does not grow with the term's memberships.
  [nmtms.md](docs/nmtms.md#the-nogood-families).

  *Class:* **Breaking** (a `:default` membership beside a known-true denial of a supertype is not believed, and `conflicts` and `contradictions` report a new `:kind`).
  *Migration:* a caller that dispatches on a report's `:kind` handles `:supertype`.
  *Breaks:* `conflicts`, `contradictions`

- **A rule firing a `:default` blocker blocks at its own placement is stored, with a
  guard `defeat` of its conclusion resting on the blocker.** The blocker is an
  `exceptWhen` or `unknown` query's matched facts, or a `:default` contrary claim of an
  inherited antecedent. The firing was refused or swept, so a reader where a defeat hid
  the blocker lacked the conclusion, and the stored set depended on arrival order. A
  blocker resting on `:monotonic` facts alone still refuses the firing, and the refusal
  record keeps it. `rule-firing-report` counts such a firing as placed. A guard
  justification belongs to the firing with the largest antecedent set it names, so the
  conclusion stays OUT when a second firing rests on a subset of another's antecedents.
  A read of a firing a reader sees n guard defeats of costs linear in n; `perf`'s
  `guard-defeats-at-a-reader` holds it.
  [naf.md](docs/naf.md#evaluated-in-the-placement-context-not-the-join),
  [inherit.md](docs/inherit.md#forward-chaining-on-a-claim-nobody-stored),
  [exceptions.md](docs/exceptions.md#garbage-collection-not-defeat).

  *Class:* **Breaking** (the store holds a firing and a `defeat` where it held neither, and a reader that does not believe the blocker believes the conclusion).
  *Migration:* read belief with `believed?`, `in?` or `sentexes-matching`, not with
  `handle-of`; assert a blocker `:monotonic` to keep the firing out of the store.
  *Breaks:* `exceptWhen`, `unknown`, `rule-firing-report`, `transitiveInArgInverse`

- **The expression lattice and the use/mention vocabulary move to a new upper member,
  CxReflection; `atomic_formula`, `atomic_sentence`, `relation_application`,
  `at_least_binary_relation` and `at_least_ternary_relation` are renamed; and
  `relation_type` is removed.**
  - `expression` is a written form in this KB's own language, the thing `(Quote …)`
    names, so it is disjoint from `relation`, `context` and `language`. A natural-language
    sentence is `linguistic` but not an `expression`. CxReflection
    (`resources/kb/upper/CxReflection.txt`) holds 22 expression kinds: `expression` is
    partitioned into `atomic_expression` and `non_atomic_expression`, which replaces
    `relation_application`; `atomic_expression` into `atomic_term` and `variable`; and
    `expression` again into `open_expression` and `closed_expression` and into
    `wff_expression` and `ill_formed_expression`. `atomic_formula` is `predication` and
    `atomic_sentence` is `closed_predication`, with `open_predication`,
    `negated_predication`, `open_literal`, `closed_literal`, `open_formula`, `wff`,
    `ill_formed`, `wff_sentence` and `ill_formed_sentence` beside them. `proposition`,
    `means`, `denotes` and `expresses` relate an expression to what it says or names.
  - CxCore keeps `symbol`, the value kinds, `unrepresented_term`, `formula`, `sentence`,
    `non_atomic_term` and the new `linguistic`, which `language` and every expression sit
    under, so `symbol` and the value kinds are disjoint from `relation` from every
    context. `forall`, `thereExists` and `exists` are declared binary quantifiers, and
    `quantifier`, `logical_connective`, `logical_constant` and `sign_value` have closed
    extents.
  - `at_least_binary` and `at_least_ternary` hold of fixed-arity relations too: `binary`
    is below `at_least_binary` and `ternary` below `at_least_ternary`, and rules over
    `arity` conclude both beside the `arityMin` rules, so they reach the 5 shipped
    relations of arity 4 to 7. `fixed_arity` and `variable_arity` partition `relation`,
    and so do `bounded_arity` and `unbounded_arity`; the 14 relations that take any number
    of arguments are `unbounded_arity`, `(orthogonal at_least_binary fixed_arity)` is
    stated, and `arityMax` bounds `functionCorrespondingPredicate` at 3.
  - The disjointness-audit rulings state `situation` and `spatial`, `animal` and `made`,
    `made` and `plant`, and `food` and `organism` orthogonal; `linguistic`,
    `proposition`, `measure`, `unit_of_measure` and `physical_dimension` each disjoint
    from `relation`; and place `indeterminate_term` under `denotational_term`,
    `sign_value` under `nowhere_never`, `alive` and `dead` under `organism`, and
    `quantity` under `acausal`.

  [contexts.md](docs/contexts.md), [naming.md](docs/naming.md#reserved-words),
  [taxonomy.md](docs/taxonomy.md#relations-and-arity-policy).

  *Class:* **Breaking** (KB vocabulary renamed, moved and removed).
  *Migration:* write `predication` for `atomic_formula`, `closed_predication` for
  `atomic_sentence`, `non_atomic_expression` for `relation_application`, `at_least_binary`
  for `at_least_binary_relation` and `at_least_ternary` for `at_least_ternary_relation`;
  a query for one of the last two also answers fixed-arity relations, e.g. `parentOf`.
  `relation_type` has no replacement. A context that names an expression kind other than
  CxCore's sees CxReflection, as every context below CxUniverse does.
  *Breaks:* `atomic_formula`, `atomic_sentence`, `relation_application`
  *Breaks:* `at_least_binary_relation`, `at_least_ternary_relation`, `relation_type`

- **A variable inside `(Quote …)` or bound by a quantifier is not free, so a fact about a
  quoted rule stores.** `(awesome_rule (Quote (implies (poodle ?x) (dog ?x))))` was
  refused as `:not-ground`. `sentex/closed?` is new beside `sentex/ground?`: it is true
  when every variable occurrence is bound by `forall`, `thereExists` or `exists`, or sits
  inside a `(Quote …)`, and `check-ground` reads it. A written `(forall ?y (implies …))`
  asserted as a fact is refused by the query-operator check rather than as
  `:not-ground`. [glossary.md](docs/glossary.md#g).

  *Class:* **Breaking** (a refusal changes type).
  *Migration:* a caller matching `:not-ground` on a quantified fact matches
  `:not-well-formed`.
  *Breaks:* `:not-ground`

- **`query-status` reads `:incomplete` when a transitive goal answered its extent.** A
  goal `(P ?x ?y)` over a `transitive` `P`, solved with both arguments open, answers the
  stored pairs and not the closure, and `query-status` reported `:complete` over it.
  `query-status` and `search-tree` return `:unenumerated`, the predicates a search
  answered that way, and `query-status`'s `:status` is `:incomplete` when it is non-empty
  and the depth bound cut nothing. The inference debugger page names them above its
  answers. [inference.md](docs/inference.md#truncation-is-observable-corequery-status),
  [taxonomy.md](docs/taxonomy.md#predicate-metadata).

  *Class:* **Breaking** (a new `:status` value).
  *Migration:* a caller that dispatches on `query-status`'s `:status` handles
  `:incomplete`; to enumerate the closure, bind one argument per source term.
  *Breaks:* `query-status`

- **A metric problem refused for mixed dimensions makes the interval network reading it
  unsatisfiable.** When the `temporalDistance` facts a context sees span two dimensions,
  the interval network widened, so an Allen relation the measures had entailed stopped
  being answered while a forward rule that fired on it kept its conclusion, and the
  arrival order decided whether that conclusion was believed. The context now answers no
  Allen goal, the firing is withdrawn in every order, and it revives when the refusal
  ends. `qualitative-network` over `:allen` names the refusal as a `:metric` source with
  its `:dimensions`. [stp.md](docs/stp.md#constraints-are-measures),
  [qcn.md](docs/qcn.md).

  *Class:* **Breaking** (a context whose `temporalDistance` facts span two dimensions answered Allen goals from its stored interval facts and points, and answers none).
  *Migration:* state every `temporalDistance` a context sees in units of one dimension.
  *Breaks:* `temporalDistance`, `qualitative-network`

- **A path a wire or browser request names is refused with `:path-not-served` (403)
  unless the server starts under `VAELII_REQUEST_PATHS=1`.** The daemon's and the
  browser's `POST /op` `:export` wrote a dump to whatever directory the request named on
  the server's host, a `:kb-diff` side read any path, and the browser's `/kbs/load` and
  `/kbs/export` created a store or a dump wherever the process could write. Each now
  refuses before anything is read or written. A `:kb-diff` side names a KB the server
  serves: in the browser, the catalog key of another loaded entry, diffed against the
  active one; a daemon serves one KB, so its `:kb-diff` refuses every string. A browser
  durable load (the card's new `:durable?` flag) and every browser export go in a new
  directory under the first `VAELII_KB_PATH` entry that is not itself a KB, named after
  the entry key and the time. The in-process `export!`, `kb-diff`, `load-source`,
  `load-dir` and `export-entry!`, and `lein cli export` and `lein cli diff`, still take
  paths. [operations.md](docs/operations.md#daemon--vaeliiserve),
  [catalog.md](docs/catalog.md#where-the-server-writes).

  *Class:* **Breaking** (a wire export, diff, load or browser export naming a path on the server's host is refused, and the browser forms no longer offer the field).
  *Migration:* start the server with `VAELII_REQUEST_PATHS=1`, or export and diff in the
  process that owns the KB (`export!`, `lein cli export`, `lein cli diff`), and take a
  browser dump from under `VAELII_KB_PATH`.
  *Breaks:* `:export`, `:path-not-served`, `VAELII_REQUEST_PATHS`, `:kb-diff`
  *Breaks:* `/kbs/load`, `/kbs/export`

- **`IndexStore` reads and writes every index family through seven family methods.**
  `family-count`, `family-children`, `family-child-count`, `family-leaf`,
  `family-member?`, `family-handles` and `family-apply!` take a family tag and a path, so
  a store implementing the protocol answers the taxonomy's supporters, the mints, the
  rule extent and the other families `kv/index-families` names. A family read given nil
  for its contexts throws `:bad-args`; `p/every-context` reads every context, and
  `family-children` answers a set under it and a vector under a context set, alike on
  every backend. A count-trie retire may name `p/any-context`; a flat set's throws
  `:bad-args`. A taxonomy probe forks the index's `KvBackend` past the methods, and over
  an index keeping none it refuses with `:unforkable-index`: a `genl` assert while a
  stored rule carries a negative edge runs one. The rule and exception writes leave the
  protocol for `rules/index-rule`, `rules/unindex-rule!`, `rules/index-exception` and
  `rules/unindex-exception!`, each one `family-apply!` batch. The context, term, rule,
  exception and predicate-agnostic argument reads and the trie's child count leave it for
  `vaelii.impl.reads` entry points over the family methods, which the profiler tallies,
  so the protocol has 20 methods; a read over every context is named `…-global`
  (`reads/stored-terms-global`, `reads/as-stored-rules-by-antecedent-global`).
  [storage.md](docs/storage.md#the-family-methods).

  *Class:* **Breaking** (an out-of-tree `IndexStore` implements seven new methods, and a caller of a retired method calls the `rules` or `reads` function in its place).
  *Migration:* an out-of-tree `IndexStore` implements the seven family methods, or embeds
  a `KvIndexStore` as `ColumnarIndexStore` does and delegates them to it, and drops the
  retired methods. A store that embeds no `KvIndexStore` keeps no `KvBackend` for a
  taxonomy probe to fork, so its `genl` asserts beside a rule with a negative edge throw
  `:unforkable-index`. A caller of `p/index-rule` calls `rules/index-rule` with the same
  arguments, and likewise for the other three writes. A caller of a retired read calls
  its `reads` entry point: `reads/as-stored-in-context`, `reads/stored-count-in-context`,
  `reads/as-stored-with-term`, `reads/stored-terms-global`,
  `reads/stored-term-count-global`, `reads/as-stored-rules-by-antecedent-global`,
  `reads/as-stored-rules-by-consequent-in` or `-global`, `reads/watched-rules-on`,
  `reads/watched-rules`, `reads/watched-rule?`, `reads/as-stored-with-arg-global`,
  `reads/stored-count-with-arg-global` and `reads/as-stored-unary-with-arg-global`. A
  caller of `p/count-children` calls `reads/stored-count-children`, or `family-child-count`
  with the tag `:trie`.
  *Breaks:* `IndexStore`, `p/index-rule`, `p/unindex-rule!`, `p/index-exception`
  *Breaks:* `p/unindex-exception!`, `p/sentexes-in-context`, `p/count-in-context`
  *Breaks:* `p/sentexes-with-term`, `p/terms`, `p/term-count`, `p/rules-by-antecedent`
  *Breaks:* `p/rules-by-consequent`, `p/rules-with-exception-on`, `p/exception-rules`
  *Breaks:* `p/exception-rule?`, `reads/stored-terms`, `reads/stored-term-count`
  *Breaks:* `reads/as-stored-rules-by-antecedent`, `reads/as-stored-rules-by-consequent`
  *Breaks:* `p/sentexes-with-arg`, `p/count-with-arg`, `p/unary-sentexes-with-arg`
  *Breaks:* `reads/as-stored-with-arg`, `reads/stored-count-with-arg`
  *Breaks:* `reads/as-stored-unary-with-arg`, `p/count-children`

- **The index is at layout 13, and the columnar snapshot at format 5.** The terms of two
  unary predicates (`[:unary-kept pred]`, `[:unary-kept-types]`), the terms a stored
  denial names (`[:unary-denied pred]`, `[:unary-denied-types]`), the stored length
  bindings (the count trie `[:arity-binding pred kind value ctx]` with
  `[:arity-binding-kinds pred]` and `[:arity-bound]`) and the positive facts by functor
  and length (the count trie `[:shape-tuple f n ctx]` in place of the counter
  `[:shape-count f n]`) join the index; the index write posts them from the sentence in
  hand. A binding arriving over a functor reads the tuples of the shape it breaks off the
  shape trie, not every tuple of the functor. The columnar index's roots pack the
  taxonomy's supporters, the length bindings and every name set, so a `:disk-snapshot`
  index image's fallback blob holds the vocabulary's counters alone and holds no entry
  per fact; a roots batch hands the fallback its ops as one batch. A stored index, a
  `:disk-snapshot` image or a dump of an earlier layout or format is rebuilt from the
  records at its first open or import, and answers are unchanged.
  [indexing.md](docs/indexing.md#the-unary-roster-and-why-position-1-was-not-narrow-enough),
  [indexing.md](docs/indexing.md#the-arity-bindings),
  [indexing.md](docs/indexing.md#the-shape-roster),
  [indexing.md](docs/indexing.md#8-the-index-as-bytes-the-mapped-snapshot).

  *Class:* **Breaking** (a stored index, a `:disk-snapshot` image of layout 10, 11 or 12 or of snapshot format 4, and a dump of layout 10, 11 or 12 are rebuilt from the records at their first open or import).
  *Migration:* none; the first open rebuilds a durable index, and the next close writes an
  image of the new layout and format.
  *Breaks:* `index-entries`, `:disk-log`, `:disk-snapshot`

- **A reasoning image is at `format-version` 15 and network layout 5.** Its state
  section no longer carries the membership candidates' terms by type and by denial, the
  cover pairs, the arity bindings and the lengths above each type, or the
  supporter-visibility generation; its taxonomy section no longer carries a
  `:context-denoting` prop; and its network section carries the justifications'
  subsumptions. The dropped rows are read from the index, and the lengths from a bounded
  cache. A `:disk-snapshot` image an earlier build wrote is declined at open, the KB
  recovers in full once, and the next close writes an image of the new layout.
  [storage.md](docs/storage.md#the-reasoning-image).

  *Class:* **Breaking** (a `:disk-snapshot` image of an earlier build is recovered in full once, at its first open).
  *Migration:* none; the first open after the upgrade recovers the store and writes a new
  image.
  *Breaks:* `:disk-snapshot`

- **`disjointness-audit` sweeps the types its vantage sees, and its default vantage is
  CxWell.** It read `relation?`, `disjoint?` and the `:orthogonal` witnesses from its
  `context` argument, but swept every node of the global `genl` hierarchy, so an opt-in
  theory's type raised the swept count and could never be covered. `types` takes an
  optional `context`, reading only the nodes touched by an edge visible from it, and
  `disjointness-audit` sweeps `(types kb context)`. The default vantage moves from
  CxUniverse to CxWell, the starter spindle's collector, which sees every middle member
  and the upper ontology and no opt-in theory. The audit reads each type's members and
  each instance test once per call. On the starter it sweeps 201 types over 20,100 pairs,
  14,211 of them disjoint (70.70%) and 3,992 unknown (19.86%), and
  `disjointness-coverage-ratchet` requires at least 14,211 disjoint pairs, 70.70%
  disjoint and at most 19.87% unknown, where 0.24.0 required 13,762, 69.85% and 20.66%.
  [taxonomy.md](docs/taxonomy.md).

  *Class:* **Breaking** (a documented default moves: a call with no `context` reads the starter spindle's coverage instead of the upper ontology's).
  *Migration:* pass `CxUniverse` as the `context` to keep the upper ontology's vantage; a
  caller already passing a `context` is unaffected.
  *Breaks:* `disjointness-audit`

### Refusals

- **The browser bounds the sandboxes, jobs and KBs it holds.** A cookie of any 32 hex
  digits named a sandbox, so each fresh cookie's first write added a `CxSandbox…` context
  with a `genlCx` edge that nothing collected; a no-op `/chain` left one job record per
  request for an hour; and each generated load filed a new `generated#N` with no bound.
  - The cookie carries a server-minted token and its HMAC tag under `VAELII_SANDBOX_KEY`,
    and a cookie whose tag does not check is replaced. Opening a sandbox past
    `VAELII_SANDBOX_MAX` (256 per KB) resets the one an aged priority ranks lowest, and
    one idle past `VAELII_SANDBOX_IDLE_MINUTES` first. An `/assert` form that would take
    its sandbox past 2,000 sentexes is refused with `:over-ceiling`; its lines written
    into another context count toward no ceiling. The cookie carries `Secure` over HTTPS.
  - The job registry holds the newest 100 settled reports, and a listing read sweeps as a
    submit does; a running job is never dropped.
  - A `/kbs/load` past 16 loaded KBs is refused with `:too-many-kbs`, which names the
    loaded keys.

  [web.md](docs/web.md#how-many-sandboxes-a-kb-holds),
  [web.md](docs/web.md#long-work-as-jobs), [catalog.md](docs/catalog.md#loading).

  *Class:* **Refusal** (a sandbox past the cap or the ceiling, and a 17th KB, were stored).
  *Migration:* none for a reader: a browser holding an old cookie is given a new one and
  a new sandbox, and the old sandbox is reset when the roster needs room. Set
  `VAELII_SANDBOX_KEY` to keep sessions across a restart, and unload a KB before loading
  a 17th.
  *Breaks:* `vaelii-sandbox`, `/assert`, `/kbs/load`

- **`abduce` refuses a `{:keep? true}` call while the KB holds 64 kept abduction
  contexts, with `:too-many-kept`.** Each kept call left a `CxAbduction…` context with its
  hypotheses and their consequences until `abduce-discard!`, so a caller that never
  discarded grew the store by one context per call with no bound. The refusal comes before
  the search and names the standing contexts under `:contexts`; nothing is evicted. The
  daemon answers it 400. [abduction.md](docs/abduction.md#isolation).

  *Class:* **Refusal** (a 65th kept context was stored).
  *Migration:* `abduce-discard!` a kept result before keeping another.
  *Breaks:* `abduce`

- **A value in a position that names a type is refused `:not-well-formed`.** A string,
  number, keyword, boolean, character, `nil` or tagged literal on either side of `genl` or
  `disjoint`, in a cover, in `disjoint_metatype`, `sibling_disjoint`, `orthogonal` or
  `siblingDisjointException`, or as an argument constraint's type is refused by `assert`
  and reported by `check`; a rule concluding one drops the firing. A stored one recovers
  with no taxonomy entry. [taxonomy.md](docs/taxonomy.md#well-formedness-vaeliiimplwff).

  *Class:* **Refusal** (`(genl "Bob" thing)` was stored, and `"Bob"` answered `genl?` as a type).
  *Migration:* retract each such declaration before upgrading; a store that keeps one
  holds the sentex, installs no `genl`, `disjoint`, metatype, sibling or cover entry from
  it, and constrains no argument by it, and `check` of its sentence reports the refusal.
  *Breaks:* `genl`, `disjoint`, `covering`, `partition`, `separating`, `disjoint_metatype`, `sibling_disjoint`, `orthogonal`, `siblingDisjointException`
  *Breaks:* `arg`, `genlArg`, `quotedArg`, `interArg`, `args`, `argsGenl`, `argAndRest`, `argAndRestGenl`, `interArgs`, `interArgAndRest`, `is a value;`

- **`totalDuration` and `overlapDuration` are refused `:not-well-formed` as stored
  facts.** `assert` refuses either one and `check` predicts the refusal; asking either
  one is unchanged. [duration.md](docs/duration.md).

  *Class:* **Refusal** (a stored one was a fact no `ask` returned, since the `:duration` prover answers both and reads no stored one).
  *Migration:* retract a stored `totalDuration` or `overlapDuration` before upgrading;
  state the `length` facts it was computed from instead.
  *Breaks:* `totalDuration`, `overlapDuration`

### Additions

- **`argArg` and `resultArg` type a position by the type another argument names.**
  `(argArg P n m)`: argument `n` of `P` is an instance of the type its argument `m` names,
  derived under assertive argument types and convicted under the constraint-only reading,
  as `arg` is. `(resultArg F n)`: an application of `F` denotes an instance of the type its
  argument `n` names, read where `result` is. A minted constant's membership is derived
  from its `termOfUnit` fact and the declaration through the argument entailment: it
  waits until the name is a type, and it leaves with the declaration. Under
  `VAELII_ASSERTIVE_ARG_TYPES=0` a `resultArg` types no minted constant; state `(result F
  T)` for a function whose constants that reading must type.
  [argtypes.md](docs/argtypes.md#a-type-another-argument-names-argarg),
  [nat.md](docs/nat.md#typing-an-application-that-is-never-minted).

  *Class:* **Additive**.

- **`try-assert` refuses a write that would open a definitional clash.** It is `assert`
  plus a refusal, `:definitional-clash`, for a sentence whose own clash or whose
  argument-type mints' clash with believed content `assert` would store and settle.
  Whether it refuses depends on arrival order. The daemon's `POST /op {:op :try-assert}`
  answers the refusal 400. [api.md](docs/api.md#refusing-a-clash),
  [operations.md](docs/operations.md#daemon--vaeliiserve).

  *Class:* **Additive**.

- **A query asks what kind of expression a quoted form is, and what kind of value a
  literal argument is.** `(symbol (Quote dog))`, `(variable (Quote ?x))`, `(open_formula
  (Quote (implies (poodle ?x) (dog ?x))))` and the other kinds of CxReflection's lattice
  that the form's spelling decides are answered by `ExpressionKindProver`, through a
  reified constant's `termOfUnit` as well, and a forward rule over one fires with the
  `quoting_function` statement in its support. A `genl`, cover or separation sentence
  re-joins only the rules over the kinds at or above the edge's upper end. `string`,
  `number`, `boolean`, `keyword` and `character` are computed for a literal argument by
  the evaluable prover that answers `integer`: `(string "foo")` and `(keyword :a)` hold,
  and `(not (number "foo"))` is proved. A symbol argument is left to the other provers,
  since a constant can denote a number.
  [argtypes.md](docs/argtypes.md#what-a-quoted-form-is), [inference.md](docs/inference.md).

  *Class:* **Additive**.

- **`min-genls` and `max-specs` read a type's nearest neighbours in the subsumption
  order, and the term page's concept graph draws them.** `(min-genls kb t [context])`
  answers the direct parents of `t` with no other direct parent of `t` strictly below
  them, and `max-specs` the direct children with no other direct child strictly above
  them. Both read every believed edge of the closure, whatever installed the edge: a
  stated `genl`, a derived one such as an `intersection`'s, or a cover roster's; the
  short arity reads the KB-wide edge set, as `direct-genls` does. The daemon and
  `vaelii.client` serve both. The concept graph's `genl` rows draw these sets at every
  expanded node, where they drew `direct-genls` and `direct-specs`: with `dog ⊂ mammal ⊂
  animal` believed and `(genl dog animal)` stated, the page for `dog` draws `animal` above
  `mammal` and no arrow from `dog` to `animal`.
  [api.md](docs/api.md), [web.md](docs/web.md#a-terms-shape-drawn).

  *Class:* **Additive**.

- **Every function CxCore and the upper ontology ship declares a corresponding
  predicate.** `StartFn` and `EndFn` correspond to `startOf` and `endOf`; CxTime adds
  `earliestStartOf`, `latestStartOf`, `earliestEndOf`, `latestEndOf`, `datetimeOf`,
  `calendarYear`, `calendarMonth`, `calendarDay` and `calendarInstant`, whose month and
  day fields take `positive_integer` and clock fields `non_negative_integer`; CxMeasure
  adds `measureInUnit` and `measureRangeInUnit`; CxCore adds `predAllExistsPlaceholder`,
  `predExistsAllPlaceholder`, `predExistsInstancePlaceholder` and
  `predInstanceExistsPlaceholder`. `PredAllExistsFn` takes the subject as a fourth
  argument, and each Exists placeholder is typed by the collection its cell names
  (`resultArg`). [predall.md](docs/predall.md#exists-the-declaration-is-a-record-and-nothing-else),
  [nat.md](docs/nat.md#the-corresponding-predicate).

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however far it moves an answer).
  *Migration:* write a `PredAllExistsFn` application with the member of the cell's second
  argument it names as a fourth argument: `(PredAllExistsFn owns person dog Muffet)`.

- **CxCore states `(predAllSpecified typeGenl at_least_metatype)` and
  `(predAllSpecified genl unary_predicate)`.** Every `at_least_metatype` is required to
  name, through `typeGenl`, a type its instances specialize, and every `unary_predicate`
  to name a `genl`. `all-specified-violations` and `kb-integrity` audit both. CxCore
  states `(typeGenl sibling_disjoint thing)`, `(typeGenl empty thing)` and `(typeGenl
  nonempty thing)`. Over the starter, the `genl` audit is clean and the `typeGenl` audit
  reports `folk_species` and `folk_biological_class`.

  *Class:* **Additive**.

- **CxSocial states the general relationship and dwelling vocabulary over two persons,
  and CxSocialExtension, a new opt-in theory below it, states `nestingPartnerOf` and
  `chosenSiblingOf`.** `relativeOf`, `coworkerOf` and `roommateOf` specialize `knows`, and
  `romanticPartnerOf` specializes `friendOf`. `originatorOf` is read by a rule from
  `parentOf`, guarded to two persons, since the shipped `parentOf` relates any two
  organisms. `relationshipLabel` is a perspectival, ternary label. `dwelling` is a
  residential unit below `container`, disjoint from `clothing`, `furniture` and `tool`
  and orthogonal to `building` and `vehicle`, and `dwellsIn`, a spec of `livesIn`,
  derives `roommateOf` for two different people who dwell in the same one. CxAbstract
  states `container` disjoint from `organism`, `person` and `substance`. No edge relates
  `marriedTo` to `romanticPartnerOf`. In CxSocialExtension, `nestingPartnerOf`
  specializes `romanticPartnerOf` and `roommateOf`, and a rule reads it from the two
  together; `chosenSiblingOf` specializes `relativeOf` and is unrelated to `siblingOf`. A
  `<Theory>Extension` names a theory that extends a starter theory with vocabulary only
  the contexts placed under it see. [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however far it moves an answer).
  *Migration:* none. Every context below CxWell reads the CxSocial additions; only a
  context placed under CxSocialExtension reads `nestingPartnerOf` and `chosenSiblingOf`.

- **CxPerception, a new opt-in theory in `kb/middle/`, states the perception relations
  and `image_viewing`.** `perceives` relates an entity to a located thing it takes in
  through some sense, and `sees`, a spec of it, does so through sight. `seeImage` and
  `watchVideo` take in a static image and a video, and conclude `sees` by a rule guarded
  by a `spatial` second argument, since an image or a video need not be located. Arg 1 of
  each is typed `thing`. `image_viewing` is an event kind below `acausal_event`, read
  through `hasCapability`: `(hasCapability ?x image_viewing)` means `?x` can be the doer
  of one. [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however far it moves an answer).
  *Migration:* none. A context below CxWell reads no perception relation; a context placed
  under CxPerception reads them as declared there.

- **`causes` ships in CxAbstract.** `(causes ?cause ?effect)` is a `binary_predicate` and
  an `instance_relation_predicate`, declared `transitive`. Its cause slot is typed
  `causal` and its effect slot `situation`, so a causal event, a tangible or an
  organization can be a cause, and an `acausal` thing in the cause slot draws a `causal`
  membership that clashes with it under `(disjoint causal acausal)`.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however far it moves an answer).
  *Migration:* a KB below CxAbstract that states `causes` with an `acausal` first
  argument, such as an `acausal_event`, holds a disjointness nogood there; type the cause
  as a `causal_event`, a tangible or an organization.

- **CxNormalPhysicalConditions, a new opt-in theory in `kb/middle/`, states the states of
  matter of stuff at ordinary room temperature and pressure.** It places `stone`, `wood`
  and `glass_stuff` under `solid` and `mercury` under `liquid`, and concludes a metal
  solid at `:default` by `(exceptWhen (mercury ?x) (set/defaultRule (set/forwardRule
  (implies (and (metal ?x)) (solid ?x)))))`. CxAbstract declares `mercury`, a first-order
  `type` below `metal`. The upper ontology states no state of matter for any substance.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however far it moves an answer).
  *Migration:* none. A context below CxWell reads no state of matter. A context placed
  under CxNormalPhysicalConditions reads its stone, wood, glass and metal solid and its
  mercury liquid, and a state it states otherwise for one of them is a disjointness nogood
  under `stuff_type_by_state_of_matter`.

- **CxComputing, a new opt-in theory in `kb/middle/`, states ten relations over software
  tools, their invocations and receipts, media resources and DNS names, and the sixteen
  kinds they are typed over.** It declares seven binary predicates (`toolName`,
  `invokesTool`, `resourceUrl`, `receipt`, `probesPredicate`, `dnsResolvesTo`,
  `agentHasTool`) and three ternary predicates (`toolInvocationArg`, `toolArgType`,
  `toolArgComment`), each with its `arg` and `quotedArg` declarations, and `(functional
  toolName)`, and states no rule. The kinds are `computational_system` below
  `intangible`, with `software_tool`, `command_line_tool`, `mcp_tool`,
  `read_only_software_tool` (also below `acausal`) and `write_capable_software_tool` (also
  below `causal`) under it; `information_bearing_thing` below `intangible` and `acausal`,
  with `digital_artifact`, `media_resource`, `image` and `video` under it;
  `tool_invocation` below `event`; `tool_receipt` below `acausal_event`; and `ip_address`
  below `string`, partitioned into `ipv4_address` and `ipv6_address`. Four `disjoint`
  sentences separate `computational_system` from `event` and from `expression`, `image`
  from `video`, and `tool_receipt` from `tool_invocation`. `software_tool` has no edge to
  `tool`. [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however far it moves an answer).
  *Migration:* none. A context below CxWell reads no computing relation and no computing
  kind. `(functional toolName)` is a decontextualized mark, so every context that sees
  CxUniverse reads that mark.

### Fixes: answers

- **With the join planner's ranking off (`VAELII_PLAN=0`), a computed antecedent waits for
  its binders.** An unranked join ran a registered evaluatable, or a literal a
  `SupportingProver` cannot enumerate open, in written order ahead of the antecedent
  binding it, and answered empty. A literal an `:est-override` costs at
  `provers/deferred-est` now runs after the generators binding its variables in both
  configurations. [inference.md](docs/inference.md#where-the-ranking-is-required).

  *Class:* **Fix**.

- **A forward rule's `(disjoint ?a ?b)` antecedent matches every separation a query
  answers.** A pair separated only by a `partition`, a `separating` roster, a
  `disjoint_metatype`, a `sibling_disjoint` parent, or a `disjoint` stated over supertypes
  matched no rule, although `disjoint?` and a query for the pair answered true. CxCore's
  "a type below two disjoint types is empty" rule, written over `(disjoint ?type ?type)`,
  concludes `empty` for a type below two parts of a partition. A
  `siblingDisjointException` the conclusion's context sees blocks the firing. A write that
  moves a separation re-joins such rules over the types it moved, not over every type;
  `perf`'s `separation-rule-under-moving-edge` holds it.
  [inference.md](docs/inference.md#a-disjoint-antecedent-reads-the-separations).

  *Class:* **Fix**.

- **`why-not` on the conclusion of a firing the forced-monotonic roster holds void
  answers `:forced-conclusion`, and the `:forced-conclusion` report names the
  antecedents off the roster.** `why-not` answered `:unsupported` with an empty
  `:missing`, and the report named only the conclusion's predicate. Both name the rule's
  antecedent predicates off the roster under `:off-roster`, which a
  `forced_monotonic_predicate` declaration puts on the roster.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Class:* **Fix**.

- **A new member of a closed part of a cover is admitted.** With every part of a
  `covering` declared `closed_extent_predicate`, the cover check read `(not (quantifier
  forall))` off the closure's negation as failure before the membership that withdraws
  it was stored, and refused the membership as a coverage violation. A part the
  membership puts its term in is denied only by a stored negation, so the starter loads
  the same KB whether the closures arrive before or after the memberships.

  *Class:* **Fix**.

- **A rule firing whose conclusion is one of the facts it matched stores no
  justification.** A rule concluding a type its own antecedents read through `genl`
  stored a justification holding its conclusion among its antecedents, which supported
  nothing. The starter and the test-world store 73 fewer justifications with the same
  sentexes and belief. [inference.md](docs/inference.md#a-firing-that-restates-its-antecedent).

  *Class:* **Fix**.

- **Two rule firings that pair the same facts with different literals are both stored.** A
  justification records the `[sub super]` predicate pairs its firing matched a fact to a
  literal through, as `:subsumptions`, and a route arriving later replaces only the
  firing with the same ones. `(kind Xa)` and `(sort Xa)`, each reaching both literals of
  `(inspace ?x) ∧ (intime ?x)`, stored only the swapped firing that arrived last. A
  justification written by an earlier build has none, and is compared on its edges.
  [nmtms.md](docs/nmtms.md#where-the-layer-stops).

  *Class:* **Fix**.

### Fixes: order independence

- **A `genlCx` edge re-checks what it moves alike in every arrival order, at every reader
  below it, and when it is concluded by a rule, computed or relabelled.** An except stated
  in a context the edge's `sub` reaches only past an excepted edge was not re-checked when
  the edge arrived or left, so a firing it hides stayed stored in some orders. A reader
  below `sub` whose own except hid an edge `sub` sees gained no firing over the facts a new
  edge showed it. An edge a rule concluded, the structural producer computed or a relabel
  moved re-checked the excepts and seeded the rules it shows only in part. A `genlCx` edge
  resting on a `genlCx` edge an `except` hides leaves the excepting context's ancestor set
  for reads as for firings, and `context-down` holds its answer per reading.
  [contexts.md](docs/contexts.md#one-context-move),
  [contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree).

  *Class:* **Fix**.

- **An argument-type mint is stored at each maximal context that sees the fact and the
  declaration.** A declaration stated in a context the fact's context does not see stored
  no mint, and neither did a `genl` route, an `interArg` trigger membership or a
  restoring `except` below the fact and the declaration, or a `genlCx` edge leaving that
  gives a placement back. The mint is placed in every arrival order of the fact, the
  declaration, the routes and the `genlCx` edges, and a placement below a more general one
  a later route, trigger or `except` leaving gives is dropped. A `genlCx` edge draws no
  declaration over the facts its `sub` already saw, a departing edge redraws only the
  mint pairs and released facts a context under its `sub` sees, and a fact fetches no
  declaration of its predicate stated where no descendant of its context sees it; `lein
  perf`'s `genlcx-edge-beside-seen-declared-facts`, `fact-beside-distant-declarations`
  and `context-edge-retraction-beside-its-own-mint` hold them.
  [argtypes.md](docs/argtypes.md#where-a-mint-is-placed).

  *Class:* **Fix**.

- **A forward rule over a computed bound believes the same conclusions in every arrival
  order and after a retraction.** A rule joining on `overlapDuration` or
  `temporalDistance` that fired before a narrowing source arrived kept its wider
  conclusion beside the narrowed one, and retracting the narrowing source left neither
  believed. A source of a `SupportingProver` arriving or leaving re-checks the rule's
  firings at the next settle, withdraws a firing whose answer the prover no longer gives,
  and re-joins the rule. A source datum re-checks and re-joins only the rules whose
  computed antecedents a prover reading that predicate answers, and an installed edge's
  answers are cut by a walk down from the answers, not by the edge's upper end's
  closure; `perf`'s `source-datum-beside-computed-firings` and `taxonomy-depth` hold
  them. [inference.md](docs/inference.md#what-a-computed-answer-rests-on).

  *Class:* **Fix**.

- **A permuting mark moves no class, and a late one clashes with a stored negation.**
  The sorted spelling stored beside a fact whose readers disagree on its mark took the
  weaker of the fact's class and the mark's, so a known-true `(swRel Bea Ada)` under a
  default `(symmetric swRel)` read `:default` above a denial of the mark; the spelling now
  holds at the fact's class, and so does a firing over it. A `(symmetric swRel)` asserted
  after `(swRel Bea Ada)` and `(not (swRel Ada Bea))` re-spelled the fact in place and
  placed no nogood; it now places the clash the other arrival orders place.
  [canonicalization.md](docs/canonicalization.md#a-mark-a-reader-does-not-believe),
  [nmtms.md](docs/nmtms.md#why-a-read-runs-no-rounds).

  *Class:* **Fix**.

- **The arity candidates convict every tuple a length binding breaks.** A tuple stored
  while a `rewriteOf` superseded a `genl` edge stayed believed when retracting the
  `rewriteOf` returned the edge; the candidates now read the `genl` relation's moves and
  recompute the functors below each moved edge. A length binding stored while a reader
  computed the first candidates after a recover was never read; a write while the
  candidates are owed moves the index, and the reader computes them again. That first
  read computes the candidates for the functors of stored facts and the lower ends of
  `genl` edges only, so its time does not grow with bindings that convict nothing.
  [nmtms.md](docs/nmtms.md#the-nogood-families).

  *Class:* **Fix**.

### Fixes: storage

- **A close or a seal that fails writing the reasoning image keeps the image it had, and
  an installed image holds one object per symbol and handle it repeats.** The sections
  are written beside the image and renamed over it once both are complete, where a close
  that ran out of heap left no image and the next open recovered in full. An install
  takes each symbol from the symbol pool and one `Long` per handle: 1,024 contexts' worth
  of facts install with 6,150 symbols for 6,150 names, where they installed with 105,507,
  and hold 0.74x the heap of the same store recovered, where they held 0.91x.
  [storage.md](docs/storage.md#the-reasoning-image).

  *Class:* **Fix**.

- **A token dictionary sizes the symbol pool before it interns.** The record store's
  `tokens.log` and the index snapshot's dictionary raise `*symbol-pool-limit*` to twice
  their token count at open, and never lower it, so a store whose vocabulary passes the
  default limit does not rotate the pool on every name. [caches.md](docs/caches.md).

  *Class:* **Fix**.

- **`kb-diff` drops the in-RAM KB it reads from a path once the diff is built, and
  `close!` of an ephemeral `fork` drops the fork's own space.** Each string side opened a
  memory space that stayed in the process registry for the life of the JVM, one per call.
  Both open on an engine space no caller can name, which `close!` drops; a space the
  caller named stays. [storage.md](docs/storage.md), [overlay.md](docs/overlay.md).

  *Class:* **Fix**.

- **A bulk premise mark on the `:disk` store reads no record for a mark its idx slot
  already records, and reads the slots in handle order.** An import's premise pass paged
  every premise's record in hash order to find that no mark changed one: 1M premises read
  1M records, now 0. [storage.md](docs/storage.md#bulkannotating--the-two-writes-that-follow-a-record).

  *Class:* **Fix**.

### Fixes: performance

- **A `genlCx` edge's write, retraction and settle cost what the edge moves.**
  - A retraction re-seeds the antecedents of the swept firings that named the edge, not
    every fact of `super`'s ancestor set: on the starter, 14 seeds and 14 ms where it
    re-chained 1,629 facts in 1.8 s. A firing whose conclusion a second justification
    kept is re-placed too. `perf`'s `context-edge-retraction-beside-sighted-facts` holds
    it.
  - A move seeds the facts the gaining readers see, a fresh `genl` edge seeds only the
    facts under it, and each seed is re-chained once per pass. A `with-deferred-settle`
    batch's drain reads only what was stored before each edge arrived, and draws each
    stored fact's argument-type entailments once. The starter load takes 27 s where it
    took 43 s on the same machine.
  - A move's seen contexts are one walk up from the contexts under its lower end, and its
    reach is computed only when a placement family past its gate reads it: a chain of
    1024 edges in one batch beside a held nogood costs 1.9 ms per edge, where it cost
    42.7 ms.
  - An edge re-checks only the `except`s stated where its lower end did not see before,
    or no longer sees after, each over its target's consequence closure, and a reader
    class or the filter gate walks forward from the stored `except`s' targets when that
    side is smaller. An edge written under a listener reads the defeats and nogood
    candidates in the contexts it moves.
  - An edge re-places a membership, related-types, tuple or arity nogood comparing only
    the placements under its lower end.

  `perf`'s `genlcx-edge-beside-seen-excepts`, `genlcx-edge-revealing-one-except`,
  `genlcx-edge-beside-unreached-defeats`,
  `genlcx-edge-beside-seen-excepts-under-a-genlcx-except`,
  `context-edge-beside-membership-placements`, `-related-`, `-tuple-` and
  `-arity-placements` hold them. [contexts.md](docs/contexts.md#one-context-move),
  [nmtms.md](docs/nmtms.md#where-the-scaling-arguments-hold).

  *Class:* **Fix**.

- **The settle that places what a rebuilt candidate index queued walks each subsumption,
  route and `genlCx` reach once per scope, and reads no closure per `genl` lower end.**
  Each membership, related-types, tuple or arity nogood walked its routes' subsumptions
  and its placements' `genlCx` reaches on its own, so a store upgraded from an older index
  layout or written without belief did not finish its first open. A placement pass reads
  every route of a family before it writes, and holds the witnesses, neighbours, edge
  supporters, supporter classes and each descended subsumption's routes while the change
  clock does not move. A witness walk past its first 64 expansions reads only the types
  between its two ends, for that walk alone. The tuple marks are read against the lower
  ends of the relabelled `genl` edges through the subtypes of the marked predicates or
  one walk up per end, whichever reads fewer: 1,698 lower ends under four marked
  predicates take 15 ms and four closures, where they took 3,694 ms and 6,720. The arity,
  membership and related-types reads of the types under a set of ends take the same walk
  with one memo per read. Which nogoods are placed, where, and on which antecedents is
  unchanged. `lein perf`'s `recover-placement-walk` and
  `witness-walk-beside-side-ancestors` hold it.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

  *Class:* **Fix**.

- **A belief read walks support only where a placement or defeat it can be moved by is
  seen.** A KB holding one `siblingDisjointException`, equality edge or arity candidate
  beside any placed `(contradicts …)` sent every read through the walk over the asked
  handle's support; the read asks first whether a `(contradicts …)` and an exemption
  source, or a `defeat`, are stated in a context the reader sees, and reads the defeat
  extent before any support. The first `:monotonic` handle a read met walked the support
  of every `symmetric`, commuting and `reifiable_function` statement: 16x the marks cost
  14.6x per read, now 0.8x. `perf`'s `default-chain-beside-unseen-contradicts` and
  `default-chain-beside-many-unseen-defeats` hold it.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

  *Class:* **Fix**.

- **A scoped taxonomy read is flat in the stored `except`s and `defeat`s.** The filter
  gates built the set of every stored except's and defeat's target on each scoped read;
  they read whether one is stored, and build the sets only when the `genl` filter reads
  them after a write. The supporter reach counts the roster's facts by functor and reads
  the smaller of the defeat targets and the supporters' support. A read's census of the
  supporting contexts is held per reader until the change clock moves, and the
  declaration and rule gates over a `genl` edge walk up to the first rostered ancestor.
  `lein perf`'s `genlcx-edge-beside-seen-excepts-columnar` and `vantage-unrelated-write`
  hold it. [taxonomy.md](docs/taxonomy.md#the-global-readers-and-who-may-use-one).

  *Class:* **Fix**.

- **Retracting a fact from a determinant re-places only its own tuple nogoods.** In
  0.24.0 each `(contradicts …)` placement leaving with the fact queued its surviving
  partner, so retracting one `:default` filler beside n clashing fillers of a
  `functional` subject re-placed all n(n-1)/2 nogoods of the group: 3.2 s at n=200. It
  reads 22–24 ms at n=100 and n=200, and `lein perf`'s `filler-beside-clashing-fillers`
  holds it. [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

  *Class:* **Fix**.

- **A read of a firing over a second route through a long `genl` chain is flat in the
  chain's length after the first read.** The second-route search reads the claim type's
  scoped ancestor set from the closure cache, where it walked the chain on every read. A
  scoped closure, neighbour set or literal's matches computed inside the search while a
  route question is open is not held, so `in?` and `ask?` answer the same in every read
  order. `perf`'s `second-route-over-a-deep-chain` holds it.
  [nmtms.md](docs/nmtms.md#where-the-scaling-arguments-hold).

  *Class:* **Fix**.

- **A `recover` beside stored `defeat`s fetches a record per defeat, not per stored
  sentex.** A recover of 105,757 sentexes beside 400 defeats fetches 8,408 sentex records
  instead of 113,765, and its first settle's glue reads 63 ms on `disk-log` instead of
  416–690 ms. A carried inherited-clash entry is tested against the except reach from the
  smaller set. [nmtms.md](docs/nmtms.md#the-runtime-view).

  *Class:* **Fix**.

### Internal

- **The nogood candidates read the index, and recover rebuilds none of their rows.** The
  arity candidates keep no binding (register row N3) and read the bindings off
  `[:arity-binding …]`; the exact lengths stored at or above each type are a weighted
  LRU, `:arity-lengths` in `caches` (N8). The membership candidates keep no term by type
  and no term by denial (N5), and read `[:unary-kept t]` and `[:unary-denied t]`; the
  related candidates keep no cover pair (N6), and read a declaration's cover pairs off the
  argument trie (`related/nogoods-holding`); `decide/registry`'s `:holds?` and `:handles`
  take the KB. A recover owes the candidates whole, and the first read after it computes
  them. `perf`'s `arity-binding-under-deep-chain` and `arity-rebuild-beside-bindings`
  hold the binding and the rebuild flat per binding.
  [indexing.md](docs/indexing.md#the-arity-bindings),
  [nmtms.md](docs/nmtms.md#the-nogood-families).

  *Class:* **Internal**.

- **A scoped taxonomy read that reads supporter belief is held for one stretch of the
  change clock under its reading, and no write evicts one.** The scoped closures, the
  supporter-filter gate and `context-down`'s filtered answer are keyed on the change clock
  and the reading; the supporter-visibility generation (register row T9) and the
  evictions are deleted. A reader under a settle's hold shares no entry with the writer.
  A transitive predicate's cached reach is keyed on the reading too, and a reach read
  under an open route question is not held.
  [taxonomy.md](docs/taxonomy.md#reads-are-scoped-by-the-asking-context).

  *Class:* **Internal**.

- **`lein lint` fails a derived-state row that holds KB content outside the KB or a
  belief-free index outside the IndexStore, and the index families are a registry of
  data.** Every register row declares `:holds-content?`, and the `derived` check fails a
  row declaring true that its `HOLDS_CONTENT` list does not name (S5, the refusal
  record), or a belief-free row kept at the write outside an `IndexStore` namespace that
  its `OUTSIDE_INDEX` list does not name (R9, the rete matcher's alpha memories); the
  register table gains a `content` column, and the README states the rule as a fifth
  property, separated state. `kv/index-families` holds one row per key tag with the class
  of answer a KB without the family loses; the dense index's handle-posting test, the
  columnar roots' routing table and the records-only import read it. E16 covers
  `p/unary-sentexes-with-arg`, and E17 holds the mark-census reads and every context-free
  flat-cache read to its roster, each rostered caller stating why it reads unscoped.
  [nmtms.md](docs/nmtms.md#3-separated-state),
  [caches.md](docs/caches.md#the-derived-state-register),
  [indexing.md](docs/indexing.md#the-index-family-registry).

  *Class:* **Internal**.

- **One perf run and a bounded number of gates run at a time on the box, and an owed
  matrix yields to a queued one.** `lein perf` and `lein perf-ab` hold `perf-lock` beside
  the matrix lock (`PERF_NO_WAIT=1` exits 75); a gate's test stage waits for one of
  `GATE_MAX_CONCURRENT` slots; a running `--owed` matrix ends at its first verdict when a
  request is queued behind it (`MATRIX_YIELD=0` keeps it running), a yield never stops
  the same configuration twice, and a stale lock is broken by an atomic rename. Each perf
  check names its subsystem group, `--only` and the owed line take groups, a check warms
  once at its large size, and seven checks another check covers are gone. The `:test`
  profile gives a test JVM a 4g heap ceiling (`VAELII_TEST_HEAP`), G1 returns freed heap,
  and three collector threads. The public CI's memory leg runs across four runner VMs.
  [operations.md](docs/operations.md#developer--the-suite-and-the-scripts).

  *Class:* **Internal**.

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
