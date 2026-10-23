# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.28.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking: quality

- **`kb-quality`'s rule-clash reading types the first argument of a `(genl ?r P)`
  antecedent by `P`'s arity.** A rule over the specs of a binary predicate paired as
  `:disjoint` with every rule concluding a type no relation has, such as `person`; the
  pair is now dropped as unreachable
  ([#210](https://github.com/vaelii/vaelii/issues/210)).
  [quality.md](docs/quality.md#contradictions-in-waiting)
  *Migration:* none.
  *Breaks:* `kb-quality`

- **`kb-quality`'s rule-clash reading types an application by its function's `result` and
  the application's arguments by its function's `arg` declarations**, at any depth, so it
  lists fewer unreachable `:disjoint` pairs: four `TimeOfFn` rules added to the starter
  pair 103 times, and 17 times with this reading
  ([#169](https://github.com/vaelii/vaelii/issues/169)).
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

### Breaking: vocabulary

- **`information_bearing_thing` renames to `information`.** CxTra declares
  `information` with the same comment, examples and `genl` edges to `intangible` and
  `acausal`, and `digital_artifact` sits below it. The name says what the type holds: the
  content, apart from the medium that carries it.

  *Class:* **Breaking** (shipped ontology content).
  *Migration:* rename `information_bearing_thing` to `information` in any KB text that
  names it.
  *Breaks:* `information_bearing_thing`


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

### Additive: vocabulary and reasoning

- **The upper ontology ships `intangiblePartOf`, `tangiblePartOf`'s twin for things without
  mass.** It is transitive, reflexive and below `partOf`, and types both positions
  `intangible`. `partOf` is not partitioned into the two specs: a mixed pair, e.g. a mind
  as part of a person, stays plain `partOf`.

  *Class:* **Additive** (shipped ontology content).
  *Migration:* none.

- **CxTra ships conceptual works, carriers, `encodes`, `subInformationOf`, `agentClaims`, `dataContent` and `propositionalContent`.**
  `conceptual_work` is below `information`. `(carries ?carrier ?info)` types position 1
  `temporal` and position 2 `information`, so a tangible paper copy and an intangible
  event, e.g. a bird's chirp, are both accepted; not functional in position 2, so one
  carrier holds more than one piece of information. `(encodes ?info1 ?info2)` relates
  one piece of information to another that reading it under its code gives, e.g. a
  ciphertext to its plaintext. `subInformationOf` specializes `intangiblePartOf` for a chapter in a book or
  a frame in a video. `(agentClaims ?agent (sentexHandle H))` says that `?agent`
  presents sentex H as true; it is typed and marked exactly as the earlier design's
  `claims` was (position 1 `thing`, position 2 a sentex handle left untyped,
  `target_following_predicate`), and no rule concludes it from `carries`.
  `(dataContent ?info ?string)` is functional over the exact symbol sequence `?info`
  holds, independent of any byte encoding that stores it. `(propositionalContent ?info
  ?proposition)` is not functional over the existing `proposition` type. Neither
  content relation is derived from an information's author, encoding or context; both
  are stated directly. [contexts.md](docs/contexts.md).

  *Class:* **Additive** (shipped ontology content).
  *Migration:* an earlier unreleased build of this change shipped
  `information_carrier`, `information_or_carrier` and `claims`; none of the three ever
  released, and none of the three is in this KB. A KB text naming any of them states
  `carries` and `agentClaims` instead.


- **`argN` is answered from how its formula is written.** `(argN ?t ?n (parentOf Tom
  Bob))` binds `?t` and `?n` to each position, 0 being the operator, and a quoted formula
  answers the positions of the form it names. A forward rule with an `argN` antecedent
  fires, and a backward one proves, once another antecedent binds the formula.
  [inference.md](docs/inference.md) ([#149](https://github.com/vaelii/vaelii/issues/149))
  *Migration:* none.

- **`exists-violations` audits a `predAllExists`, `predExistsAll`, `predExistsInstance`
  or `predInstanceExists` declaration on demand**, returning the members of the universal
  collection, or the fixed term, with no believed filler. `all-specified-violations` and
  `kb-integrity` audit every visible one beside the *Specified* declarations. Served as
  the `:exists-violations` op. [predall.md](docs/predall.md)
  ([#149](https://github.com/vaelii/vaelii/issues/149))
  *Migration:* a caller of `all-specified-violations` sees a key per *Exists* declaration
  with a violation.

- **`(interArgEqual P n v m U)` types argument `m` of the `P` sentences whose argument `n`
  is the value `v`**, a number, string, keyword, boolean or character. It derives the type
  as `arg` does, convicts under the constraint-only reading, and `try-assert` refuses a
  separated argument from both arrival orders. CxUniverse types a `closedExtentForArg`
  grant's predicate by the grant's position, so `try-assert` refuses a grant past a stated
  arity, which closed nothing ([#175](https://github.com/vaelii/vaelii/issues/175)).
  [argtypes.md](docs/argtypes.md#a-type-conditioned-on-an-argument-value-interargequal)
  *Migration:* none; a stored grant past its predicate's arity is reported in `conflicts`.

### Fix: order independence

- **A reified NAT constant whose function declares `genlResult` is collected when its
  last use is retracted**, whether the declaration arrives before or after the mint. The
  `(predicate K)` the argument-type entailment draws off the materialized `(genl K T)`
  edge counted as a use and kept the constant. Belief after the retract matches a fresh
  load of the remaining knowledge
  ([#225](https://github.com/vaelii/vaelii/issues/225)).
  [nat.md](docs/nat.md#rename-and-remove--keeping-the-11-invariant)
  *Migration:* none.

- **Retracting a `natFormula` map before its `reifiable_function` mark no longer leaves
  the constant's uses spelled `nat/K`** ([#216](https://github.com/vaelii/vaelii/issues/216)).
  The uses a departing map leaves are re-spelled in the same teardown: under a believed
  mark the constant is minted again, and with the mark gone each use names the
  application. The mark and its maps leave the same store in any retraction order.
  [nat.md](docs/nat.md#a-reifiable-mark-moving)
  *Migration:* none.

### Internal

- **The shipped ontology states no exact-arity membership that a `:monotonic` metatype
  route entails.** The upper files drop 169 `(binary_predicate P)` and 5 `(unary_predicate
  T)` premises, and `CxTra.txt` drops 7 `(binary_predicate P)`. The engine stores each of
  the 181 in CxUniverse under an `arityClass` justification, so every relation's length,
  `describe`'s `:arity` and each exact-class answer in CxUniverse reads the same. `why`
  names the membership and the edges instead of a premise, and `sync!` over a store loaded
  from 0.28.0's files retracts the 181 premises.
  [taxonomy.md](docs/taxonomy.md#arity) ([#116](https://github.com/vaelii/vaelii/issues/116))

## 0.28.0 — 2026-10-21 — "Ill-typed facts and rules stored inert, term kinds and arity policies forced-monotonic, a `:default` `genl` that does not contrapose, parthood and the example predicates restated, `:recover? :trust` by default"

| Area | Change |
|---|---|
| argument types | a fact failing its argument type and a rule no term can fill stored inert in every order; `why-not`'s `:conviction`; `violations`' `:inert-argument` and `:inert-rule`; `try-assert` refuses as `:definitional-clash`; a constraint convicts only by a separated type; a value-kind antecedent fires; a type-level relation's arguments are predicates; a declared type mints by its arity, and a declaration typed `thing` mints nothing; owed withheld-mint releases and `owed-releases` |
| arity | `(arity R n)` proved from an exact-arity membership; `predicateTypeByArity` and `functionTypeByArity` inert and `termsRelated`; `kb-integrity`'s `:implicit-arity-class`; quaternary and quinary classes; `arg4`, `arg5`; `relation-arity`; `admitsArgnum` by backward rule |
| forced-monotonic set | a denial believed until its literal is stored; term kinds, arity policies, comparators, `arg` and `exceptWhen` forced; `genlInverse` forced between predicates |
| inference | a `:default` `genl` does not contrapose; the intersection rule confers `:monotonic`; a guard defeat for every blocked firing and `why-not`'s `:excepted`; declarations at one position compose; `:incomplete` over an open transitive goal; `quoting_function` removed; `negates`; `minCommonGenl`, `maxCommonSpec`, `common-genls`; `escalate`'s `:max-ms`; `justification-verdicts` |
| storage | `:recover? :trust` by default, with `:oplog?` too; image format 16; index layout 16; a load syncs only with `:sync?`, one reported change at a time; `:pg-snapshot` operation log; `unsupported`, `remove-unsupported!`, `mark-inert!`; the shutdown hook waits for a write; progress lines; `+with-postgres`, `+with-sqlite`, `+with-foreign` |
| renamed identifiers | `:held-values`, `:koinii/compression-fixed`, `:recorded`, `ImageFingerprinting`, `:not-forced-monotonic`, `:derived-sets`, `:forced-monotonic`, the `:bad-table-entry` list mismatches, `:term-names` |
| shipped ontology | `natFormula` for `termOfUnit`; `partOf` of any kind and `tangiblePartOf`; proper parthood and `subSituationOf`; `partitionedByType` binary; `logical`, `quantitative`, `typeOrthogonal`, `orthogonalMetatypes`, `implementationNote`; quoted-sentence and string examples; happening roles and `toolInvoked`; CxTra; `metal_stuff`; `genl` edges in place of one-antecedent rules; `mechanism`, `electronic_device`; 51 `thing` argument declarations |
| browser | edits and term operations as jobs; `/removed`; whole-KB lists and `/closure`; a long read answered with a waiting page; `:pg-snapshot` backup; `POST /op` `:kbs` and `:jobs`; part-list frames in the taxonomy diagram; extension menus and term actions |

Twenty-eight entries are **Breaking** and none is a **Refusal**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.27.0 caller changes.

| If your code… | Then |
|---|---|
| catches `:arg-type`, `:arg-genl`, `:inter-arg-type` or `:quoted-arg-type` from `assert` | read `why-not`'s `:conviction` or `violations`' `:inert-argument`; call `try-assert` where the write must be refused |
| catches `:arg-variable` from `assert` or reads it off a dropped mint | read `why-not`'s `:conviction` or `violations`' `:inert-rule`; call `try-assert` |
| writes a rule whose value-kind antecedent no other antecedent binds | bind the value-kind argument with a stored literal in the same rule |
| relies on a declared type with no path to `thing` minting nothing, or on a declaration typed `thing` minting `(thing X)` | state the type's other arity; narrow the declaration to the type `kb-quality`'s `:typed-thing` names |
| relates non-predicates through a `type_relation_predicate`, or relied on `:arg-constraint-kind` for `arg` on one | drop the mark; check `type_relation_predicate` yourself |
| reads `isa?`, matching or a preview after a bulk load, an open or a membership removal | call `release-withheld!`, or pass `{:release-withheld? true}` to `preview` |
| classifies relations of an arity with `predicateTypeByArity` or `functionTypeByArity` | state `relationTypeByArity`; state the class `kb-integrity` reports |
| writes a denial of a forced-monotonic literal to be ignored, or reads `:inert` with `:denies` | retract the denial; read `:defeated` and `:contradicted-by` |
| relies on a defeat picking between two term kinds or two arity policies | retract one of the two |
| denies a `genl` edge's upper end to deny its lower end | assert the edge `:monotonic` |
| wants a combined intersection membership to stay defeasible | state a conjunct at `:default` |
| takes a missing handle as "excepted", or reads `:excepts` off `chain-report` | read the guard defeat and `why-not`'s `:excepted`; run `lein cli upgrade` |
| states two declarations at one argument position meaning their union | drop one |
| dispatches on `:status` from `ask-within`, `prove-within`, `resume` or `compare-tacticians` | handle `:incomplete` |
| asserts `quoting_function`, or passes `:quoting` to `has-prop?` | delete the assertion; quote through `Quote` |
| needs an open to re-derive belief under the running build | pass `{:recover? :auto}`, or run `lein cli upgrade` |
| opens a durable store | budget one index rebuild and one recover on the first open; read `[:term-names]` from `index-entries` |
| loads a store or dump in the browser and expects a sync | pass `:sync? true` to `load-dir` or `load-source` |
| names `:pinned-values`, `:koinii/compression-pinned`, `:stamped`, `ImageStamping`, `:off-roster`, `:rosters`, the event `:roster`, an `:unrostered-…` mismatch or `:term-roster` | use the new spelling the entry lists |
| names `termOfUnit`, or opens a store a mint wrote under 0.27.0 | name `natFormula`; `export-text!`, rewrite `termOfUnit` to `natFormula`, and `load-text!` into an empty store |
| writes `partOf` between two tangibles, or `subintervalOf` between situations | write `tangiblePartOf`; relate situations by `during`, `starts` or `finishes` |
| writes `partitionedByType` with a cell list | write `(partitionedByType W C)` and state each `(C A)` |
| writes an example as `(sentexHandle H)` | write `(Quote S)` |
| names `invokesTool`, or expects `event` in a role's first position | write `toolInvoked`; state `event` where uninterrupted occurrence is needed |
| names `CxComputing` or `CxPerception` | name `CxTra` |
| reads the forward rules on `friendOf`, `marriedTo`, `worksFor`, `parentOf` or `livesIn` | read the `genl` edge `why` cites |
| names `metal` | name `metal_stuff` |
| reads `kb-quality`'s rule-clash pairs | nothing: the dropped pairs are unreachable |


### Breaking: argument types

- **A fact whose argument fails its declared argument type is stored and held inert, in
  every arrival order.** `assert` stores a value argument under `arg` (`(needs 5)` under
  `(arg needs 1 dog)`), an application whose declared result misses, an individual in a
  `genlArg` position, a symbol the constraint-only reading convicts, and a kind outside a
  `quotedArg` type. Each threw `:arg-type`, `:arg-genl`, `:inter-arg-type` or
  `:quoted-arg-type` when the declaration arrived first, and was stored and believed when
  the declaration arrived after it. The fact is never believed: `why-not` answers `:inert`
  with the violation under `:conviction`, and `violations` lists it as `:inert-argument`.
  A value is tested from its fact's context, so a `(needs 5)` stated below the
  declaration's context is held in every order of the declaration, the fact and a `genl`
  edge only that context sees. The settle decides the stored facts again when a
  declaration, a membership, a `genl` edge or a separation moves, and a move decides
  again only the holds at or below its ends. `check` reports none of them. Refs #145.

  An argument constraint convicts a symbol only by a type the taxonomy separates from the
  declared one: under `VAELII_ASSERTIVE_ARG_TYPES=0`, an `action` argument under `(arg
  causes 1 causal)` is admitted when nothing separates `action` from `causal`, and the
  same reading holds for `genlArg`, `interArg`, the covering and homogeneity forms, a
  nested input and an application's declared result. A value under a type that refines
  its kind, a string under `(arg P n ip_address)` or an integer under a subtype of
  `integer`, is believed unless the taxonomy separates the declared type from one of the
  value's kinds. A compound in a `quotedArg` position is judged by the expression kinds
  `provers/shape-kinds` reads off its spelling: `(P (MsrFn 5))` under `(quotedArg P 1
  string)` is held inert, and a kind that only fails to reach the type convicts nothing.

  `try-assert` refuses each of these writes as `:definitional-clash` with `:violation`
  `:arg-type`, `:arg-genl`, `:inter-arg-type` or `:quoted-arg-type`, including against a
  declaration stated below the sentence's context, and refuses an `arg`, `genlArg`,
  `interArg` or `quotedArg` declaration a stored tuple of its predicate or a
  sub-predicate breaks, a tuple holding a value at the position included. A firing
  dropped on a conviction is re-asked when the separation or the argument's membership is
  retracted. Perf checks `genl-write-beside-held-facts` and
  `holds-pass-over-declared-predicates` bound the growth of deciding the holds again.
  [argtypes.md](docs/argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert),
  [argtypes.md](docs/argtypes.md#what-a-quoted-form-is),
  [api.md](docs/api.md#refusing-a-clash).

  *Migration:* read `why-not`'s `:conviction` or the `:inert-argument` entries of
  `violations` where a caller caught one of the four types from `assert`; call
  `try-assert` where the write must be refused; state the `disjoint`, `partition` or
  `disjoint_metatype` that separates two types where a refusal under the constraint-only
  reading depended on a missing `genl` path.
  *Breaks:* `assert`, `check`, `try-assert`, `:arg-type`, `:arg-genl`, `:inter-arg-type`, `:quoted-arg-type`
  *Breaks:* `:definitional-clash`

- **A rule whose variable no term can fill is stored and held inert, in every arrival
  order.** `assert` stores a rule one of whose variables two argument constraints hold to
  separated types, `(implies (comment ?x ?string) (genl ?x ?string))` among them, and a
  generator fill or a `defn*` companion rule convicted the same way. Each threw or was
  dropped as `:arg-variable` when the declarations arrived first, and was stored and
  believed when they arrived after it. The rule is never believed and fires nothing:
  `why-not` answers `:inert` with the `:arg-variable` conviction, and `violations` lists
  it as `:inert-rule`. A declaration arriving later takes a believed rule and its
  conclusions OUT. A `quotedArg` demand at `string`, `number` or a type below one
  convicts against a separated instance demand. `try-assert` refuses the rule, and a
  declaration that would convict a stored rule, as `:definitional-clash` with
  `:violation :arg-variable`. `check` reports none of them. 15,000 rules in 200 contexts
  decide their holds in 0.2 to 0.4 s.
  [argtypes.md](docs/argtypes.md#a-rule-whose-variable-no-term-can-fill-is-held-inert).

  *Migration:* read `why-not`'s `:conviction` or the `:inert-rule` entries of
  `violations` where a caller caught `:arg-variable` from `assert` or read it off a
  dropped mint; call `try-assert` where the rule must be refused.
  *Breaks:* `assert`, `check`, `try-assert`, `violations`, `:arg-variable`

- **A forward rule with a value-kind or `sentence` antecedent fires on the value another
  antecedent binds.** `(implies (and (valueOf ?a ?x) (string ?x)) (hasKinded ?a))`
  concluded nothing from `(valueOf Ann "rex")`, and neither did the same rule over
  `number`, `boolean`, `keyword`, `character` or `sentence`; `integer` and `formula`
  fired. Each such rule now fires in either arrival order, and beliefs change where one is
  stored; `(implies (sentence (Quote …)) …)` alone still concludes nothing. A forward rule
  reading `(temporalDistance ?e ?e ?d)` beside a stored antecedent concludes zero seconds,
  the answer `ask` gives. A rule whose value-kind argument no other antecedent binds is
  refused `:naf-not-closed` by `assert`, `check` and import, a `defnSufficient` on a value
  kind alone expands to no companion rule, a backward rule concluding a value
  kind is not expanded, and `watch` refuses a value-kind goal
  ([#191](https://github.com/vaelii/vaelii/issues/191)).
  [argtypes.md](docs/argtypes.md#what-a-quoted-form-is).

  *Migration:* bind a value-kind argument with a stored literal in the same rule. A disk
  store written before this change holds a rule with a value-kind antecedent under its old
  canonical sentence, so the stored rule and its re-assert are two handles until the store
  is reloaded from text.
  *Breaks:* `assert`, `check`, `handle-of`, `watch`

- **A type-level relation's arguments are predicates, and the instance constraints are
  admitted on it.** `core.txt` concludes `(args R predicate)` forward from
  `(type_relation_predicate R)`: `predicate` and not `unary_predicate`, since `genl`
  relates predicate specializations of any arity. `query (args disjoint ?t)` answers
  `[{?t predicate}]`, a symbol argument of `genl`, `disjoint` or another type-level
  relation is derived a `predicate` under assertive argument types, and one whose types
  place it outside `predicate` is refused `:arg-type`. `arg`, `arg1`, `arg2`, `arg3`,
  `interArg` and `argArg` on a `type_relation_predicate` are stored, where `assert` and
  `check` refused each `:arg-constraint-kind`: `(arg disjoint 1 unary_predicate)` is a
  true instance claim. `genlArg` on an `instance_relation_predicate` is still refused
  `:arg-constraint-kind`. [taxonomy.md](docs/taxonomy.md), [api.md](docs/api.md).

  *Migration:* a KB relating terms that are not predicates through a
  `type_relation_predicate` drops the mark from that relation; a caller that relied on the
  refusal to keep instance constraints off a type-level relation checks
  `type_relation_predicate` itself.
  *Breaks:* `assert`, `check`, `query`, `:arg-constraint-kind`

- **A withheld argument-type mint that a departed membership releases stays owed after a
  bulk load, an open, a recover, the first settle after a trusted image install, and a
  preview.** Under pruning, retracting `(dog Fred)` in one of these settles stores no
  `(animal Fred)` for `(parentOf Fred Mary)` until `release-withheld!` runs. `owed-releases`
  counts the owed departures and arrivals, the image carries them across a close, and the
  browser's store card shows the count. Until `release-withheld!` runs, `isa?` and
  matching miss the owed membership. A preview of a batch that removes a withholding
  membership answers without the mint and the contradiction it would enter, carries
  `:owed-releases n` and `:release-path :deferred`, and its rollback leaves
  `owed-releases` as it found it; `{:release-withheld? true}` runs the release sweep in
  the preview (`:release-path :swept`). Refs #145.
  [argtypes.md](docs/argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on),
  [preview.md](docs/preview.md#what-a-preview-omits).

  *Migration:* call `release-withheld!` after a bulk load or an open where `isa?`, matching
  or `why` must find the minted memberships; pass `{:release-withheld? true}` where a
  preview must report every mint and contradiction the apply draws.
  *Breaks:* `bulk-assert-facts!`, `open-kb`, `recover`, `lein cli upgrade`, `preview`

- **An argument declaration mints in a type that does not reach `thing`, and mints
  nothing in `thing`.** Under the entailing reading, `(arg P n T)` and the rest of the
  family mint memberships in `T` whenever no arity statement binds `T` to a length other
  than one, whatever `T`'s `genl` path; the declaration also entails `(unary_predicate T)`.
  A type bound to another length, or to one length and another, mints nothing, and its
  declaration waits until the binding leaves; a binding arriving after the declaration
  withdraws the entailed `(unary_predicate T)` and holds the minted memberships inert, so
  both orders reach the same belief. A declaration typed `thing` mints no `(thing X)`, and
  `kb-quality` names it under `:typed-thing` with the number of facts it would have
  typed. The starter asserts `(unary_predicate T)` only of the subtypes of `thing` no
  declaration names. [argtypes.md](docs/argtypes.md#where-it-does-not-mint).

  *Migration:* a KB that relied on a declared type with no path to `thing` minting
  nothing states the type's other arity, or reads the memberships the declaration now
  mints; narrow a declaration typed `thing` to the type `kb-quality` reports it would
  have typed.
  *Breaks:* `assert`, `ask`, `query`, `recover`, `kb-quality`

### Breaking: arity

- **The exact-arity class memberships and `arity` prove each other one way each, and
  `kb-integrity` reports a relation missing its class.** A `set/backwardRule` proves
  `(arity R n)` from a membership of an exact-arity class: `query (arity R ?n)` of a
  relation stated only `(binary R)`, `(binary_predicate R)` or `(binary_function R)`
  answers `[{?n 2}]` at depth 3, where it answered nothing, and no arity is stored. The
  `relationTypeByArity` rule the other way, `(arity ?r n) → (T ?r)`, is
  `set/forwardOnlyRule`, so the two form no backward cycle. `core.txt` ships
  `(predicateTypeByArity unary_predicate 1)` through `(predicateTypeByArity
  quinary_predicate 5)` and the five `functionTypeByArity` peers; each generates
  `(predicate ?r) ∧ (arity ?r n) → (T ?r)` (or the same over `(function ?r)`) as a
  `set/inertRule`, believed and browsable, run on no write and no query.
  `predicateTypeByArity` and `functionTypeByArity` are `termsRelated` to
  `relationTypeByArity`, not its `genl` specializations, so a `(predicateTypeByArity T
  n)` fact classifies no function of arity `n` under `T`, and `genl?` of either mapping
  and `relationTypeByArity` answers false. `kb-integrity`'s default
  `:implicit-arity-class` category applies the inert rules: it reports `{:term R :kind
  predicate :arity 2 :class binary_predicate :mapping (predicateTypeByArity
  binary_predicate 2)}` for a relation with an exact length outside the mapped class, and
  a sweep over such a candidate answers `:status :gap` where it answered `:audited`. Every
  predicate and function the starter ships states its class.
  [taxonomy.md](docs/taxonomy.md#relations-and-arity-policy),
  [integrity.md](docs/integrity.md#what-an-implicit-arity-class-finding-means).

  *Migration:* a KB that maps an arity with `predicateTypeByArity` or
  `functionTypeByArity` to classify every relation of that arity states
  `relationTypeByArity` instead; state the class `kb-integrity` reports, or name the
  categories to run in `:categories`.
  *Breaks:* `ask`, `query`, `genl?`, `kb-integrity`

### Breaking: the forced-monotonic set

- **A denial of a forced-monotonic literal is believed until the literal is, and then
  loses to it.** `(not (irreflexive likesP))` was stored and never believed; it is now
  believed, and a rule reading it fires, while no `(irreflexive likesP)` is stored where
  the denial's context sees it. Once the literal is stored, the denial is OUT at either
  strength and in either arrival order, and so is what it supported; retracting the
  literal restores both. A declaration `(forced_monotonic_predicate P)` makes a denial
  lose only where a reader sees the declaration. `why-not` of such a denial answers
  `:defeated` with the literal under `:contradicted-by`, in place of `:inert` with
  `:denies`, and the browser's sentex page names the literal. A denial of a literal that
  a closure or an equation answers without storing it stays believed
  ([#208](https://github.com/vaelii/vaelii/issues/208)).
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-set).

  *Migration:* retract a denial that was written to be ignored; read `why-not`'s
  `:defeated` and `:contradicted-by` where a caller read `:inert` with `:denies`.
  *Breaks:* `ask`, `query`, `why-not`, `recover`

- **The term kinds, the arity policies, the numeric comparators and `exceptWhen` are
  forced-monotonic.** Each of these goes OUT only by retraction: `relation`, `predicate`,
  `function`, `truth_valued_relation`, `logical_constant`, `logical_connective`,
  `quantifier`, `symbol`, `context`, `unrepresented_term` and its value kinds (`boolean`,
  `character`, `keyword`, `number`, `integer` and its four sign classes, `string`, and
  CxTra's `ip_address`, `ipv4_address` and `ipv6_address`); `fixed_arity`,
  `fixed_arity_predicate`, `fixed_arity_function`, `bounded_arity`, `unbounded_arity`,
  `at_least_binary`, `at_least_ternary`, `arityMax` and `admitsArgnum`; `greaterThan`,
  `lessThan` and the quantity comparators (`quantityGreaterThan`,
  `quantityGreaterThanOrEqual`, `quantityLessThan`, `quantityLessThanOrEqual`,
  `sameQuantity`); the argument declarations `arg`, `arg1`, `arg2` and `arg3`; and
  `exceptWhen`, whose `retract!` of the declaration is refused with `:type
  :uncleared-forcing` and `:missing :unforced-exception`. `genlInverse` is
  `forced_monotonic_between_predicates`, as `genl` is. Two term kinds or two arity
  policies stated of one term are an irreducible conflict: a `:default` `(predicate X)`
  beside a `:default` `(string X)`, or `(fixed_arity R)` beside `(variable_arity R)`,
  leaves both believed and `conflicts` reports the pair, where one was the loser.
  `(animal X)` beside `(fixed_arity_predicate X)` takes `animal` OUT, where `relation` was
  the one held in the clash. A stored denial of a term kind or an `arg` declaration loses
  to it once it is stored. [nmtms.md](docs/nmtms.md#the-forced-monotonic-set).

  *Migration:* retract one of two clashing term kinds or arity policies, since a defeat
  no longer picks one.
  *Breaks:* `ask`, `query`, `conflicts`, `contradictions`

### Breaking: inference

- **A `:default` `genl` edge no longer contraposes.** With `(genl pa pb)` at `:default` and
  `(not (pb Zz))` stored or derived, `query (not (pa Zz))` answers nothing and `argue (pa
  Zz)` answers `:unknown`, where they answered `[{}]` and `:false`. In a context that
  holds the edge at `:default` only, a forward rule on `(not (pa ?x))` does not fire on
  `(not (pb A))`, an `exceptWhen` query `(not (pa ?x))` blocks nothing for `A`, `(pa Rex)`
  beside `(not (pb Rex))` is no `:supertype` nogood, and `(not (pb X))` does not deny the
  part `pa` of a cover. An edge the reader holds at `:monotonic`, or one a cover
  declaration installs, contraposes as before, the rule a separation's denial already
  follows. The two time intersections in `core.txt` are `:monotonic`. Closes #188.
  [inference.md](docs/inference.md#predicate-subsumption-in-matching).

  *Migration:* assert a `genl` or `genlInverse` edge with `{:strength :monotonic}` where a
  denial of its upper end should deny its lower end.
  *Breaks:* `query`, `argue`, `conflicts`, `contradictions`, `exceptWhen`

- **The intersection membership rule confers `:monotonic`.** Each `(intersection C A B)`
  fact generates a bare `(implies (and (A ?x) (B ?x)) (C ?x))` rather than a
  `set/defaultRule`, so a thing stated of each type at `:monotonic` is a `:monotonic`
  member of `C`, and wins a clash with a `:default` membership where the two were a
  dilemma. A `:default` conjunct still makes a `:default` member. A forced-monotonic `C`
  is concluded from forced-monotonic conjuncts, where every firing was void.

  *Migration:* state a conjunct at `:default` where the combined membership should stay
  defeasible.
  *Breaks:* `ask`, `query`, `contradictions`, `violations`

- **A firing an `exceptWhen` or an `unknown` blocks is stored with a guard defeat, for a
  `:monotonic` blocker as for a `:default` one, and `why-not` names the exception.** With
  `(exceptWhen (rskip ?x) …)` over `(rmark ?x) => (rseen ?x)` and `(rskip RM1)`
  `:monotonic`, `(rseen RM1)` is stored with `(defeat (sentexHandle F))` resting on
  `(rskip RM1)`, where no conclusion was stored. A blocker arriving after the firing
  places the defeat and sweeps nothing. `ask`, `query` and `sentexes-matching` answer as
  before; `handle-of`, levels 0 and 1, `CxEverything`, `why` and export see the stored
  conclusion and its defeat. The refusal record keeps closed-extent and separation
  refusals only, and `chain-report` drops `:excepts`. `why-not` of such a conclusion's
  handle answers `:excepted` with `:rule`, `:exception` and `:via`, where it answered
  `:unsupported`, and the browser's belief pill reads it so. A guard defeat whose
  `exceptWhen` is OUT no longer covers its firing, so a `preview` of removing an
  exception reports the conclusion the edit believes again.
  [naf.md](docs/naf.md#evaluated-in-the-placement-context-not-the-join),
  [exceptions.md](docs/exceptions.md#semantics).

  *Migration:* run `lein cli upgrade` or open with `{:recover? :auto}`: a recover re-fires
  every guarded rule (`rerecord-refusals!`) and stores the firings with their defeats. A
  trusted image install keeps an earlier build's refused firings until a settle queues
  their rule. Read the guard defeat where a caller took a missing handle as "excepted",
  and `:excepted` where it read `:unsupported`.
  *Breaks:* `handle-of`, `chain-report`, `recover`, `why-not`

- **Declarations at one argument position compose, and a preserved transitive predicate
  composes with its own transitivity.** A position's reach is the closure of the goal's
  term under every relation its declarations name, where it was the union of each
  relation's reach. `(transitiveInArgInverse needsCheck 1 partOf)` beside
  `(transitiveInArgInverse needsCheck 1 heldIn)` carries `(needsCheck Crate Monday)` to a
  part of a thing held in `Crate`, and a position declared along `genl` in both directions
  reaches every kind connected to the claim's: `(flagged mammal)` answers `(flagged
  reptile)`. Specificity compares claims along the same closure. With `(transitive
  locatedIn)` and `(transitiveInArgInverse locatedIn 1 partOf)`, `ask`, `prove` and a
  forward antecedent answer `(locatedIn Piston1 House1)` from `(partOf Piston1 Car1)`,
  `(locatedIn Car1 Garage1)` and `(locatedIn Garage1 House1)`, where `ask` answered false;
  a denial of `locatedIn` is not carried along `locatedIn`. Fixes #207.
  [inherit.md](docs/inherit.md#declarations-at-one-position-compose-with-each-other-and-with-p).

  *Migration:* drop one of two declarations at a position where the union was the meaning.
  *Breaks:* `ask`, `ask?`, `prove`, forward chaining over a preserved antecedent

- **`ask-within`, `prove-within`, `resume` and `compare-tacticians` read `:incomplete` over
  an open transitive goal.** A goal `(P ?x ?y)` over a `transitive` `P`, solved with both
  arguments open, answers `P`'s stored pairs and not its closure, and these reads reported
  `:complete` over it. A run whose source ran dry after one now reads `:status
  :incomplete` with no continuation, and every partial result and row carries
  `:unenumerated [P …]`, cumulative across a `resume`. An `explain-levels` row and an
  `escalate` result name `P` the same way. Each of these reads, `query-status` and
  `search-tree` included, also reports `:unenumerated-in-guards`: the predicates recorded
  inside an `unknown` or `exceptWhen` evaluation, where a missed pair can admit an answer
  the closure would refuse. Follows
  [#134](https://github.com/vaelii/vaelii/issues/134).
  [anytime.md](docs/anytime.md#where-the-collector-lives).

  *Migration:* a caller dispatching on `:status` from `ask-within`, `prove-within`,
  `resume` or a `compare-tacticians` row handles `:incomplete`; to enumerate a closure,
  bind one argument per source term.
  *Breaks:* `ask-within`, `prove-within`, `resume`, `compare-tacticians`

- **`quoting_function` is removed; `Quote` and `Quasiquote` are the quoting functions,
  fixed by the engine.** Which functions quote is `sx/quoting-functors`, not a KB
  declaration. A `Quote` or `Quasiquote` argument is a mention in every KB from the first
  assert: held opaque to a `sameAs` or `equals` merge, followed by a `rewriteOf` rename,
  not reified on its own, and not typed by what it denotes, so a merge processed before a
  declaration can no longer fold a mention onto its referent. The `:quoting` prop kind
  goes with the predicate. `ensure-quasiquote-functions` asserts `(reifiable_function
  Quote)` and `(unreifiable_function Quasiquote)` only, and `(unreifiable_function
  Quasiquote)` turns the quasiquote reducer on. `ExpressionKindProver`'s support cites no
  quoting statement, so a forward firing reads a quoted form's kind only when a `genl`
  edge or a `natFormula` statement supports it.

  *Migration:* delete any `(quoting_function X)` assertions. A KB that declared another
  function quoting must quote through `Quote` instead. `has-prop?` and `props` no longer
  take `:quoting`.
  *Breaks:* `quoting_function`, `:quoting`

### Breaking: storage

- **`open-kb` keeps a reasoning image an earlier engine build wrote, with or without
  `:oplog?` (`:recover? :trust` is the default).** A `:disk-snapshot` store whose image was
  written under other engine source installs it, is writable at once, and moves belief
  under this build only where a settle reaches, where the open recovered from the
  records: under `:auto`, every commit to belief-deriving code made the next open of
  every store a full recover. `:oplog?` takes `:recover? :trust` too, and its
  seals record the source belief was last derived under. The browser, the daemon and
  `lein cli` take the default; the browser opens a `:disk-snapshot` or `:pg-snapshot`
  store it recovers with `:oplog? true`. `lein cli upgrade` still opens with `:auto`, and
  `lein cli upgrade --trust` (`scripts/upgrade-kb.sh --trust`) keeps an image and recovers
  belief only when the records moved behind the images. An edit to the import code no
  longer moves the source identity: `vaelii.core`'s `write-ops` names its entries by
  keyword, and the `:replay` writes are digest roots by name.
  [storage.md](docs/storage.md#the-reasoning-image),
  [storage.md](docs/storage.md#the-operation-log),
  [operations.md](docs/operations.md#cli--vaeliicli).

  *Migration:* pass `{:recover? :auto}` where an open must hold belief this build derived
  in full, or run `lein cli upgrade` on the store.
  *Breaks:* `open-kb`

- **A durable store rebuilds its index and recovers belief once on its first open: the
  reasoning image is at `format-version` 16 and the index at layout 16.** The image's
  state section holds the membership candidates' separation inputs under `::sep-inputs`
  and the argument family's taxonomy generations under `::read-under`; under every
  `:recover?` setting, `:trust` included, the first open of a `:disk-snapshot` or
  `:pg-snapshot` store after the upgrade recovers from the records and writes a
  format-16 image at close. The index keys the term-name set, the flat set of every
  symbol the term index is keyed by, under `[:term-names]`, and adds `[:opposed-functor
  f]` and `[:opposed-between f]`, the bodies stored in both polarities filed by functor;
  a stored index, a
  `:disk-snapshot` image or a dump of layout 14 is rebuilt from the records at its first
  open or import, and answers are unchanged. A fork whose base holds layout 14 is refused
  as `:stale-index-layout` until the base is opened writable once.
  [storage.md](docs/storage.md#the-reasoning-image),
  [indexing.md](docs/indexing.md#6-the-term-name-set).

  *Migration:* budget one recover per store on the first open, or run `lein cli upgrade`
  on each store beforehand. Read `[:term-names]` where a caller of `index-entries` read
  `[:term-roster]`.
  *Breaks:* `state.nippy`, `index-entries`, `:disk-log`, `:disk-snapshot`

- **A loaded store or dump is synced to the shipped contexts only when its load asks
  (`:sync?`), and a sync job reports each change.** A sync was one `edit!` and one settle
  over the whole KB: on a large `:pg-snapshot` store loaded by the development browser,
  a settle stopped part-way left the records it had written ahead of the index and
  reasoning images, so every later open rebuilt both. A store or dump now loads as
  it was written, the development browser's file-edit sync passes it by, and
  `catalog/sync-entry!` syncs one entry as a `:sync` job on purpose.
  `vaelii.host.sync/sync-each!` makes the plan one `edit!` per change, calling a report
  with `{:done i :total n :op {:op :context :form}}` before each; the browser's sync jobs
  run it, the jobs page shows each change, and a refused addition no longer rolls back the
  rest. The plan renders only the premises naming the shipped vocabulary.
  [catalog.md](docs/catalog.md#a-loaded-kb-states-this-engines-shipped-contexts).

  *Migration:* pass `:sync? true` to `load-dir` or `load-source`, or tick the load's
  "Sync the shipped contexts" option, for a load that syncs.
  *Breaks:* `vaelii.browser.catalog/load-dir`, `vaelii.browser.catalog/load-source`

### Breaking: renamed identifiers

- **Nine identifiers that said `roster`, `pin` or `stamp` are renamed for what they
  name.** Each old spelling is gone:
  `caches` reports the held-values row as `:held-values` ("Held values"), and
  `set-cache-limit` takes `:held-values`; `:pinned-values` names no cache, and
  `set-cache-limit` warns on it ([caches.md](docs/caches.md)).
  koinii's `publish!` refuses a compression other than `:none` as
  `:koinii/compression-fixed`, "publish! requires :compression :none"
  ([koinii.md](docs/koinii.md)).
  The `:stale-index-records` refusal names the store an index was built against under
  `:recorded`, beside `:records`
  ([storage.md](docs/storage.md#pg-snapshot-the-two-images-over-records-on-a-server)).
  The optional record-store protocol an image is checked against is
  `vaelii.impl.protocols/ImageFingerprinting`, with methods `index-fingerprint` and
  `belief-fingerprint`; a record store extending the old name no longer satisfies it, so
  `open-kb` refuses the `:snapshot` index over it with `:missing-adapter`
  ([storage.md](docs/storage.md#the-image-disk-snapshot)).
  A `:forced-conclusion` violation's `:detail` and each `why-not` `:convicted` entry name
  the rule's antecedent predicates that are not forced-monotonic under
  `:not-forced-monotonic`, and the `:message` reads "is forced-monotonic"
  ([nmtms.md](docs/nmtms.md#the-forced-monotonic-set)).
  The recover step is `:derived-sets` ("rebuilding the derived sets") in
  `:last-recover`'s `:steps`, the image's recorded recover and the progress line; an
  older image still opens
  ([storage.md](docs/storage.md#what-a-recover-spends-its-time-and-heap-on)).
  The derived-state event `checks/force-reach!` raises is `:forced-monotonic`, and the
  descriptor check refuses a `:retired-by` naming the old key
  ([caches.md](docs/caches.md)).
  A `:bad-table-entry` refusal carries `:mismatch` `:unlisted-reader`,
  `:exempt-and-listed`, `:unlisted-arm` or `:family-list`, the last naming the list
  under `:list` and its members under `:list-holds`, and `predicates/check-facets` takes
  `:family-lists` ([predicates.md](docs/predicates.md)).
  `profile`'s per-functor `:writes` and `:retracts` carry `:term-names n`, and the
  vocabulary reads tally under the family `:term-names` ([profile.md](docs/profile.md)).

  *Migration:* `:pinned-values` → `:held-values`; `:koinii/compression-pinned` →
  `:koinii/compression-fixed`; `:stamped` → `:recorded`; `ImageStamping` →
  `ImageFingerprinting`, `index-stamp` → `index-fingerprint`, `belief-stamp` →
  `belief-fingerprint` (the values returned stay as they are); `:off-roster` →
  `:not-forced-monotonic`; `:rosters` → `:derived-sets`; the event `:roster` →
  `:forced-monotonic`; `:unrostered-reader` → `:unlisted-reader`, `:exempt-and-rostered`
  → `:exempt-and-listed`, `:unrostered-arm` → `:unlisted-arm`, `:family-roster` →
  `:family-list`; `:roster` and `:term-roster` in a `profile` report → `:term-names`.
  *Breaks:* `caches`, `set-cache-limit`, `:pinned-values`, `publish!`, `:koinii/compression-pinned`, `:stale-index-records`
  *Breaks:* `vaelii.impl.protocols/ImageStamping`, `index-stamp`, `belief-stamp`, `:forced-conclusion` `:off-roster`, recover step `:rosters`, derived-state event `:roster`
  *Breaks:* `:unrostered-reader`, `:exempt-and-rostered`, `:unrostered-arm`, `:family-roster`, `profile`

### Breaking: shipped ontology

- **`termOfUnit` is renamed `natFormula`.** The reified-term map, `(natFormula K E)`
  in CxUniverse, is what a mint writes and what the engine reads to take a reified
  constant back to its expression. `core.txt` declares and comments `natFormula`, and
  every engine read, the browser and the docs name it. Nothing reads `termOfUnit` any
  more: no alias maps the old name onto the new one. The `natFormula` comment in
  `core.txt` is rewritten. [nat.md](docs/nat.md).

  *Migration:* a store written before this change must be migrated, and cannot be
  re-derived. Its `(termOfUnit K E)` maps are stored records that the engine reads by
  predicate name, so after the upgrade no constant reads back to its expression, and a
  re-asserted application mints a second constant beside the first. `sync!` does not
  repair this: it asserts the `natFormula` declarations but leaves every premise naming
  `termOfUnit` in place, since `termOfUnit` is no longer a term the engine ships. A map
  cannot be re-derived from the store's other facts either, because those facts name the
  minted constant `K`, not the application. To migrate, `export-text!` the store, rewrite
  every `termOfUnit` token in the export to `natFormula`, and `load-text!` the result
  into an empty store. A frame dump (`export!`/`import!`) keeps the old spelling, so it
  is no route around the text export. A text KB, rule or query that names `termOfUnit`
  names `natFormula` instead.
  *Breaks:* `termOfUnit`

- **Parthood is reflexive or proper, `partOf` is parthood of any kind, and `partOf`
  between two tangibles is `tangiblePartOf`.** `tangiblePartOf` keeps both arguments
  `tangible`, its transitivity and partType's `typeToInstancePred`. The new `partOf` is
  transitive and declares `thing` in both positions, and `tangiblePartOf`,
  `partOfRegion`, `subSituationOf` and `subintervalOf` are below it by `genl`. A
  `tangiblePartOf` fact answers `partOf`, and a `partOf` fact answers no
  `tangiblePartOf`. CxMereology's two rules read `tangiblePartOf`. Each of the five
  carries its own `reflexive` mark. `properPartOf` is irreflexive, transitive and below
  `partOf`, defined as `(partOf x y)` with `(partOf y x)` denied; antisymmetry is declined
  and stated so, `(not (anti_symmetric partOf))`. `properTangiblePartOf`,
  `properSubSituationOf`, `properPartOfRegion` and `properSubintervalOf` are below
  `properPartOf`, `(properCounterpart ?predicate ?properPredicate)` records each pair, a
  core.txt generator generates its definition, and one rule at the root, `(properPartOf
  x y)` to `(not (partOf y x))`, denies the reverse for every proper relation below it.
  `subSituationOf` relates two situations and is transitive; no rule concludes the time
  containment. `subintervalOf` and `properSubintervalOf` take two `time_interval`s, not
  two `temporal`s. space.txt states the 15 converse pairs of the RCC-8, cardinal and
  relative-direction calculi and four RCC-8 parthood edges under `set/inert`, so each
  calculus prover still answers its goals alone, and a dump holding those inert records
  still writes a reasoning image. [glossary.md](docs/glossary.md),
  [time.md](docs/time.md).

  *Migration:* write `tangiblePartOf` for a `partOf` fact, rule or declaration between
  two tangibles; a query for any parthood keeps `partOf`. Relate two events by `during`,
  `starts` or `finishes`, or relate their times: a `subintervalOf` between two situations
  now types each as a `time_interval`, which `(disjoint time situation)` refuses.
  *Breaks:* `partOf`, `subintervalOf`, `properSubintervalOf`

- **`partitionedByType` is binary and draws inference, and the upper ontology states
  `logical`, `quantitative`, `typeOrthogonal`, `orthogonalMetatypes` and
  `implementationNote`.** `(partitionedByType ?whole ?classifier)`: the members of
  `?classifier` partition `?whole`. A core.txt generator places each member under
  `?whole`, and a rule concludes `(disjoint_metatype ?classifier)`. No rule draws the
  coverage half (vaelii/vaelii#171), so the `partition` sentence stays beside each of the
  4 shipped facts: `fixed_order_type` by `type_type_by_order`, `tangible` by
  `origin_type`, and `thing` by `spatiality_type` and by `temporality_type`.
  `(separating nowhere_never logical linguistic quantitative)` separates three kinds:
  `relation`, `proposition` and `context` are `logical`, and `measure`,
  `unit_of_measure`, `physical_dimension` and `sign_value` are `quantitative`.
  `(typeOrthogonal ?classifier ?type)` makes every member of a classifier orthogonal to
  `?type`, and `(orthogonalMetatypes ?m1 ?m2 …)` makes every member of each metatype
  orthogonal to every member of the others (vaelii/vaelii#170). The classifiers
  `arity_type`, `origin_type`, `spatiality_type` and `temporality_type` are new and
  forced-monotonic. 10 `typeOrthogonal` facts and one `orthogonalMetatypes` fact derive
  33 orthogonal pairs, 22 of them stated before; the upper ontology derives 43 `genl`,
  `disjoint` and `orthogonal` sentences it stated and no longer states 40 of them. 9 more
  orthogonal pairs are stated, among them `made` and `vertebrate`. `physical`, a location
  in the physical space of our universe, is below `spatial`, and `spatiotemporal` is below
  `physical` and `temporal`. `implementationNote` is a sibling of `comment` for how a term
  is implemented, and 16 terms in `core.txt` and `abstract.txt` carry one. The read walk
  of an `except` stays off where the declarations behind a rule are visible to every
  reader of that rule, so the classifier rules leave an upper-ontology load at 7.4 s.
  (#172)
  [taxonomy.md](docs/taxonomy.md), [glossary.md](docs/glossary.md).

  *Migration:* drop the cell list: write `(partitionedByType W C)` for
  `(partitionedByType W C A B …)`, and state each cell's membership `(C A)`.
  *Breaks:* `partitionedByType`

- **The example predicates quote their example sentence, and string siblings carry an
  example as text.** The second argument of `positiveExample`, `negativeExample` and
  `borderlineExample` is a quoted sentence, `(positiveExample ip_address (Quote
  (ip_address "192.0.2.1")))`, and no longer a `(sentexHandle H)`, and the three are no
  longer `target_following_predicate`. `curation_test` asks the quoted sentence in the
  example's context: a `positiveExample`'s sentence must be provable there, a
  `negativeExample`'s must not be, and unknown is enough. `positiveExampleComment`,
  `negativeExampleComment` and `borderlineExampleComment` are binary, the second argument
  a `string`, and carry no provability obligation. The shipped files state 34
  `positiveExample` and 7 `negativeExample` facts, each one the starter proves or does not
  prove, and 204 `positiveExampleComment` and 21 `negativeExampleComment` facts in place
  of the examples 101 comments named inline. Examples that could be misread are reworded,
  and `machine`'s comment defines it by its moving parts and energy source and names no
  use.

  *Migration:* rewrite `(positiveExample T (sentexHandle H))` as `(positiveExample T
  (Quote S))`, S being the sentence H holds, and the same for the other two. An example
  is no longer torn down with the sentence it named. A `negativeExample` whose sentence
  the KB proves now fails the check. A reader of a comment's examples reads the example
  facts.
  *Breaks:* `positiveExample`, `negativeExample`, `borderlineExample`

- **General happening roles and capabilities admit interrupted occurrences, and
  `invokesTool` is renamed `toolInvoked`.** `actor` relates a happening to a meaningful
  participant, and `thingPerceived` relates it to what is perceptually taken in. `doneBy`,
  `performedBy`, `input`, `destroyedInput`, `preservedInput`, `output`, `tangibleOutput`
  and `intangibleOutput` declare `happening` rather than `event` in position 1.
  Participation alone concludes neither intentional doing nor perception. The tool
  relation keeps its invocation-first argument order and `tool_invocation` /
  `software_tool` bounds. `capabilityType` and `hasCapability` take a happening kind as
  argument 2, and `hasCapability` takes any `causal` doer as argument 1, so a `machine` or
  an `organization` has capabilities and a `time` is still convicted.
  [inherit.md](docs/inherit.md).

  *Migration:* update stored tool facts, rules, queries and writers to `toolInvoked`;
  this change does not migrate a live store. Callers inspecting the eight role domains
  must expect `happening`; state `event` separately when uninterrupted occurrence is
  required.
  *Breaks:* `invokesTool`

- **CxComputing and CxPerception merge into one opt-in context, CxTra.**
  `kb/middle/CxTra.txt` states every form the two files stated, with `(genlCx CxTra
  CxUniverse)`, so CxTra sees what each of the two saw and CxWell does not see CxTra.
  `core.txt` states `(context CxTra)` in place of the two `context` memberships. No
  relation, kind, rule or declaration changes.

  *Migration:* rename `CxComputing` and `CxPerception` to `CxTra` in any `genlCx` edge,
  `ist` or context argument that names them; a context placed under both needs one edge
  to CxTra.
  *Breaks:* `CxComputing`, `CxPerception`

- **The middle theories state `genl` edges where they stated one-antecedent rules, and
  the upper files state the `genl` edges their covers imply.** CxSocial states `(genl
  friendOf knows)`, `(genl marriedTo knows)` and `(genl worksFor memberOf)`, CxKinship
  `(genl parentOf ancestorOf)`, and CxBiology `(genl livesIn locatedIn)`, `(genl bird
  warm_blooded)` and `(genl mammal warm_blooded)`, each in place of a forward rule. A
  `genl` between predicates is forced-monotonic, so a `:monotonic` `livesIn` fact
  concludes a `:monotonic` `locatedIn` where the rule concluded a default, and a denial of
  the upper predicate denies the lower one. `core.txt`, `abstract.txt` and
  `reflection.txt` state the edges their covers imply, among them `(genl acausal
  intangible)` and `(genl closed_literal sentence)`, and place seven predicate-kind marks
  and metatypes under `thing`; `except` is a `unary_predicate`. `life.txt` drops `(arg P 1
  T)` for `alive`, `dead`, `mortal`, `asleep`, `awake`, `breathes_air` and `warm_blooded`,
  since each property's `genl` entails it, so a membership under one of their specs is not
  held inert by the property's argument type. `kb-integrity` over the starter in CxWell
  reports no `implicit-genl` or `not-under-thing` finding
  ([#209](https://github.com/vaelii/vaelii/issues/209)). [taxonomy.md](docs/taxonomy.md).

  *Migration:* none for a query; `why` of such a conclusion cites the edge.
  *Breaks:* `friendOf`, `marriedTo`, `worksFor`, `parentOf`, `livesIn`

- **`metal` renames to `metal_stuff`.** A stuff type's name is a mass noun, as
  `glass_stuff` is. `abstract.txt` declares `metal_stuff` with the same comment, `genl`
  edges and `stuff_type_by_substance` membership, `mercury` sits below it, and
  CxNormalPhysicalConditions' solid-by-default rule reads `(metal_stuff ?x)`. No pair's
  disjointness changes.

  *Migration:* rename `metal` to `metal_stuff` in any KB text that names it.
  *Breaks:* `metal`

### Breaking: quality

- **`kb-quality`'s rule-clash reading drops three kinds of unreachable pair.** It reads
  `args` and `argAndRest` as it reads `arg`, so a pair whose shared term a covering
  declaration types disjoint from what the other rule places it in is not reported: over
  the starter, `(function ?r) (arity ?r 1) → (unary_function ?r)` against `(unary ?type)
  (disjoint ?type ?type) → (empty ?type)` is dropped. A pair whose antecedents put a
  literal beside a denial of a predicate it is a spec of, `(properPartOf a b)` and `(not
  (partOf a b))`, is dropped. A pair in which one term is bounded above the exact arity
  it is claimed to have is dropped, so the shipped KB reads four excepted `:negation`
  pairs where it would read 86. [quality.md](docs/quality.md).

  *Migration:* none.
  *Breaks:* `kb-quality`

### Additive: vocabulary and reasoning

- **`(negates P Q)` states that two relations hold of no argument list together.** A
  believed `(scorns Eve Fay)` beside a believed `(admires Eve Fay)` under `(negates scorns
  admires)` is one placed nogood, read down `genl` on both sides, whichever arrives first.
  `ask? (not (scorns Gus Hal))` is true while `(admires Gus Hal)` is believed, and no
  denial is stored per fact. `(negates P P)` makes each `P` tuple a one-member nogood. A
  declaration whose sides are bound to lengths no argument list fits, or to one argument,
  is stored and reported in `conflicts` as `:negates-arity` or `:negates-unary`. The
  declaration is forced-monotonic and context-scoped. The from-Cyc guide translates a
  binary `negationPreds` as `negates`, where its two implication rules convicted nothing
  when both tuples were stored ([#106](https://github.com/vaelii/vaelii/issues/106)).
  [taxonomy.md](docs/taxonomy.md#predicate-metadata),
  [from-cyc.md](docs/from-cyc.md#negation-and-mutual-exclusion).

  *Migration:* none. A KB storing `negates` facts of its own reads them as declarations;
  replace the from-Cyc guide's two rules with one `(negates P Q)`.

- **Relations of four and five arguments have exact arity classes, and a function's
  result types the value position of its corresponding predicate.** `quaternary` and
  `quinary` are relation-wide exact classes, and `quaternary_predicate`,
  `quinary_predicate`, `quaternary_function` and `quinary_function` specialize them.
  `(arity R 4)` concludes `(quaternary R)`, and `(arity R 5)` concludes `(quinary R)`.
  One `(separating fixed_arity unary binary ternary quaternary quinary)` declaration
  separates the five classes. `at_least_quaternary` and `at_least_quinary` extend the
  arity floors, each disjoint from the exact class one below it. `arg4` and `arg5`
  project `arg` at positions 4 and 5, and `closedExtentForArg4` and `closedExtentForArg5`
  spell `closedExtentForArg` at those positions; the four are forced-monotonic.
  `calendarDay`, `measureRangeInUnit`, `predExistsInstancePlaceholder` and
  `predInstanceExistsPlaceholder` are `quaternary_predicate`, `interArg`,
  `predAllExistsPlaceholder` and `predExistsAllPlaceholder` are `quinary_predicate`, and
  `PredAllExistsFn` and `PredExistsAllFn` are `quaternary_function`. Forward rules
  conclude `(arg P n T)` from `(result F T)` and `(functionCorrespondingPredicate F P)`:
  `n` is the last position of a binary through quinary `P`, or the position the
  correspondence states; `functionCorrespondingPredicate` and `result` are
  forced-monotonic. A test holds every shipped predicate in an exact arity class or
  `variable_arity`; a `fixed_arity` relation above five arguments, such as
  `calendarInstant`, has no named class. [taxonomy.md](docs/taxonomy.md#arity).

- **`relation-arity` answers a relation's exact arity, `admitsArgnum` answers with a
  proof, and `(args R T)` proves `(argAndRest R 1 T)`.** `(relation-arity kb 'arg)` is
  `3`; a `variable_arity` relation, or a term no length binds, answers nil, and
  `vaelii.client` and the daemon serve it. `admitsArgnum`'s eight definition rules are
  `set/backwardRule`: `query (admitsArgnum calendarDay ?n)` answers `1` through `4`,
  `(admitsArgnum ?r 7)` answers each `unbounded_arity` relation, and each answer's
  `{:proof? true}` tree cites its rule; no `admitsArgnum` fact is stored. A
  `set/backwardRule` states the entailment from `args` to `argAndRest`, so `query
  (argAndRest R ?n ?t)` at depth 3 answers `[{?n 1 ?t T}]` of a relation declared only
  through `args`. [api.md](docs/api.md), [inference.md](docs/inference.md),
  [argtypes.md](docs/argtypes.md).

- **`common-genls`, `common-specs`, `min-common-genls` and `max-common-specs` read the
  types a collection of types shares, and `minCommonGenl` and `maxCommonSpec` answer them
  in a query.** `(common-genls kb [a b])` is the intersection of `(genls kb a)` and
  `(genls kb b)`, reflexive as `genls` is, and `common-specs` intersects `specs` the same
  way. `min-common-genls` keeps the members strictly above every input with no other such
  member below them: with `dog ⊂ mammal ⊂ animal`, `(min-common-genls kb [dog mammal])`
  is `#{animal}`. `max-common-specs` is the same read downward. Each takes a context, and
  `vaelii.client` and the daemon serve all four. `CommonGenlProver` answers
  `(minCommonGenl ?x dog cat)` with each member of `(min-common-genls kb [dog cat])`, and a
  ground first argument outside the set proves false, so `argue` answers `:false`.
  `core.txt` declares both variable-arity with `arityMin` 2, and asserting one is refused
  as `:not-well-formed`. [api.md](docs/api.md), [inference.md](docs/inference.md).

- **`escalate` takes `{:max-ms n}`.** The deadline is checked between levels and inside
  level 7's search. A climb it stops before any level answered returns `{:level nil
  :status :timeout}`, and `escalate-opt-keys` lists the option. The browser's
  `/reasoning` gallery renders at once and then asks each card's verdict, 10 s per card.
  [levels.md](docs/levels.md#operators).

- **A quoted application is classified by what the KB states of its head.** Under a
  symbol head R, `(predication (Quote (R a)))` holds when R is a member of `predicate` or
  a type below it, `(non_atomic_term (Quote (R a)))` when R is a function and the form is
  closed, and `ill_formed_expression` (`ill_formed` for a predicate) when R's length rules
  out the argument count. R's spelling is never read. The answer cites the membership,
  the bindings and the `genl` edges it rests on, and a forward rule over one of these kinds
  fires whether the head's kind arrives before or after the rule and the quoted fact. A
  head membership stated outside CxUniverse classifies the form for the readers that see
  it ([#145](https://github.com/vaelii/vaelii/issues/145)).
  [argtypes.md](docs/argtypes.md#what-a-quoted-form-is).

- **A `:monotonic` definition decides a value at the argument check.** Under `(arg P n
  T)` or `(quotedArg P n T)`, a `:monotonic` `defnIff`, `defnSufficient` or
  `defnNecessary` over the value-kind predicates or any evaluable condition decides a
  literal value before its kind does. With `(defnIff character_string (string ?x))`,
  `(nameString X "Foo")` is believed where `character_string` has no `genl` edge to
  `string`, and `(nameString X 5)` is held inert. A sufficient condition of `T` or of a
  subtype admits a value it is true on, and a necessary condition of `T` or of a
  supertype convicts a value it is false on. A `:default` definition decides nothing.
  [defns.md](docs/defns.md#a-definition-decides-a-literal-value-at-the-argument-check).

- **`justification-verdicts` names why a justification does or does not carry its
  conclusion at a context.** `(justification-verdicts kb handle context)` answers `{jid
  reason}`, each reason one of `:supports`, `:antecedent-out`, `:blocked`, `:void`,
  `:guard` and `:exempt`, read by the walk that decides belief there. `why` carries the
  verdict at each node's context on its `:support` entries and `why-not` on its
  `:support`, so a justification a guard defeat covers reads `:guard` where it read as
  supporting. The browser's proof and justification pages draw the verdict, also over
  `--attach`, and count a covered justification as not supporting.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

- **The clash reports can leave their grounds off, and `stored-first-args` reads a type's
  members off the index.** `(conflicts kb {:grounds? false})` and `(contradictions kb
  context {:grounds? false})` answer every entry without `:grounds`, which costs a
  taxonomy walk per definitional clash. A nil context is the KB-wide reading, and any other key is
  refused as `:unknown-option`. `(stored-first-args kb pred)` is the set of terms stored
  at argument 1 under `pred`, one read with no record fetched and belief unread. [api.md](docs/api.md).

### Additive: shipped ontology

- **A shipped argument position that holds a term of any kind declares `thing`.** `(arg P
  n thing)` states that position `n` of `P` holds a term of any kind and that no narrower
  type is right for it. `core.txt`, `abstract.txt`, `reflection.txt`, `society.txt`,
  `CxTra.txt` and `CxSpeechActs.txt` state 51 such `arg` declarations, among them `(arg
  equals 1 thing)`, `(arg doneBy 2 thing)` and `(arg believes 1 thing)`, and `(args
  different thing)` types every position of `different`. `(genlArg toolArgType 3 thing)`
  types the third position of `toolArgType` a type. `comment`, `seeAlso`, the example
  predicates and their string siblings declare `(quotedArg P 1 denotational_term)`,
  `seeAlso` declares its second position the same way, and `argN` declares `(quotedArg
  argN 1 expression)`. A fixed-arity predicate's position of arity 2 and up is declared,
  or `ontology_test`'s `undeclared-positions` names it with its reason.
  [argtypes.md](docs/argtypes.md#constraint-and-entailment-readings).

  *Migration:* none. Under the entailing reading, a symbol at one of these positions with
  no narrower membership derives `(thing X)`.

- **`mechanism` is the common `genl` of `machine` and the new `electronic_device`, and
  `wing` and `fur` are disjoint.** `abstract.txt` declares `mechanism`, a physical object
  whose parts, in their arrangement, set up a characteristic causal operation, below
  `tangible` and not below `made`: a juvenile Issus planthopper's hind-leg gears are a
  mechanism. `electronic_device`, a mechanism built around an electronic circuit, is
  below `made` and `mechanism`, and `(orthogonal electronic_device machine)` is
  `:monotonic`, with a `comment` naming a witness for each claim. `(disjoint mechanism
  organism)` and `(disjoint mechanism substance)` are stated once on the parent, and
  `(disjoint animal machine)` is derived through them, no longer stated. `(disjoint wing
  fur)` is `:monotonic`. With this release's separations, the disjointness coverage
  ratchet rises to 25,373 disjoint pairs (83.51%) and at most 6.82% unknown.

  *Migration:* a KB that asserts one term as both an `organism` (or a `substance`) and a
  `machine` or `electronic_device`, or as both a `wing` and `fur`, now records a clash. A
  KB that reads the stated `(disjoint animal machine)` sentence finds the derived
  disjointness instead.

- **A new OE principle, "bank the decision".** A modelling question weighed and answered
  no is stated in the KB as an explicit negation, and a `(not …)` is asserted only for a
  decision actually made. [oe-principles.md](docs/oe-principles.md).

### Additive: storage

- **A `:pg-snapshot` KB takes an operation log, and a `:pg-disk-log` or `:pg-snapshot`
  directory reopens with no `:pg`.** `(open-kb {:backend :pg-snapshot :dir dir :oplog?
  true})` keeps the log, the seal and both images under `dir`. An open after the writer
  was killed (SIGKILL, which no shutdown hook sees) restores the images and replays the
  operations logged since the seal, in place of the full reindex and recover. A write to
  a sealed directory by a KB opened without `:oplog?` retires the seal, under any disk
  backend: `:disk-dense`, `:disk-columnar` and `:disk-log` over the same records as
  well. `open-kb` over such a directory with no `:pg` connects to the server
  `index/records.edn` names, as `PGUSER` (else the OS user) with `PGPASSWORD` when set,
  so `{:backend (v/store-backend dir) :dir dir}` opens it as it opens a `:disk` store,
  and `VAELII_KB_DIR` and `/kbs` load it. An explicit `:pg` is used as given.
  [storage.md](docs/storage.md#the-operation-log),
  [storage.md](docs/storage.md#pg-snapshot-the-two-images-over-records-on-a-server).

  *Migration:* none; a seal written before this release is not restored, and the next
  logged open seals again.

- **An open reports a record that no premise mark and no justification supports.** A
  write cut short between a record and its justification leaves such a record. The open
  logs its handles and changes nothing; `unsupported` answers `{:n n :handles [...]}`, the
  browser's store card shows the count, and no write refuses over it.
  `remove-unsupported!` removes the reported records among the handles the caller names
  (`:force? true` removes every reported one), and `mark-inert!` marks an earlier
  build's `assert-inert` records, which carry no `:inert` provenance mark and are
  reported until marked. `assert-inert` marks each new record.
  [storage.md](docs/storage.md#a-record-no-premise-and-no-justification-supports).

- **The shutdown hook waits for a running write.** A JVM shutdown waits up to 10 s for
  the public writes in flight, then stops an `assert` or an `edit!` batch's adds at the
  next rule firing or settle pass with `:shutdown-abort`, rolled back as a unit. A write
  past its rollback point runs to its end. The hook then waits up to
  `vaelii.disk.shutdown-unwind-ms` (default 10000) before it closes the stores under the
  writes still running.
  [storage.md](docs/storage.md#a-shutdown-under-a-running-write).

- **A long loop logs its progress, and the console backend prints one short line per
  call.** The loops of a recover and a settle, a dump import and export, a reindex, a
  disk store's open and compaction, an operation log replay, the token log read, the
  index snapshot's token load and write, the reasoning image's read and write, a text
  load and export, the quality census, the integrity sweep, the disjointness audit,
  `bulk-assert-facts!`, the starter load, sync and the corpus generator log a line at
  `:info` once a loop has run 15 s, again at 30 s, 1, 2 and 4 minutes and then every 5
  minutes, each naming its count, total, share and time left, and a closing line. A line
  also logs when the projected total time halves or doubles, and a timer logs the line
  when the loop has not ticked. The dump import's `loaded N sentexes…` line is gone. A
  recover records the settle that places the queued nogoods as its own `:placement` step,
  logged as step 7 of 7, and `rebuild-progress` counts nine steps. An `:info` line is
  `HH:mm:ss message`; a louder one adds its level and namespace, and `:debug` adds the id
  and the `:data` map. The browser and `lein cli` install it at `:info` when no level is
  set.
  [operations.md](docs/operations.md#progress-lines),
  [operations.md](docs/operations.md#logging--a-dial-and-what-is-behind-it),
  [storage.md](docs/storage.md#what-a-recover-spends-its-time-and-heap-on).

  *Migration:* a caller reading `rebuild-progress`'s `:of` as 8 reads 9.

- **`+with-postgres`, `+with-sqlite` and `+with-foreign` add the published siblings to any
  lein task, the uberjar included.** `lein with-profile +with-postgres browser` opens a
  `:pg-*` KB from this checkout, `lein with-profile +with-postgres,+with-sqlite uberjar`
  builds a standalone jar that opens both, and the `Dockerfile`'s `PROFILES` build
  argument builds the image that way. The default uberjar and the published pom carry no
  adapter. `scripts/link-checkouts.sh` links all three siblings' live source, and
  `scripts/upgrade-kb.sh` and the start scripts run a KB over postgres records under
  `+with-postgres`. An adapter that loads without its dependencies refuses with
  `:missing-adapter`, naming the namespace that failed, instead of a `CompilerException`.
  [storage.md](docs/storage.md#backend-selection-two-independent-axes),
  [foreign.md](docs/foreign.md#exercising-one-from-here).

  *Migration:* `scripts/with-foreign.sh <task>` is gone; run `lein with-profile
  +with-foreign <task>`.

### Additive: browser

- **A browser edit runs as a job, a term page carries a term bar, and `/removed` lists
  what the browser removed.** An assert, an editor save, a retraction and a put-back each
  run as an `:edit` job on `/jobs`. A badge's right-click menu and the sentex page offer
  Copy, Edit and Remove, and `/assert` seeds from `?copy=<handle>` or `?text=`, `?ctx=`
  and `?strength=`. The term bar's Rename, Copy and Remove confirm with the count of
  asserted sentexes naming the term and an estimated run time, and one estimated past a
  minute must be acknowledged; a rename into an existing term merges the two, and
  `/term-op/name` says whether they merge cleanly. A term job settles 500 sentexes at a
  time and can be cancelled between settles. `/removed` lists the last 50 removals per
  KB, with Put back, kept under `vaelii.removed.dir` (default `~/.vaelii/removed`).
  [web.md](docs/web.md#editing-sentexes).

- **The browser lists the whole KB's defeats, dilemmas, conflicts and types without a
  `genl`, and draws a type's whole closure.** `/lists` runs each list as a read job from
  its button. `/closure` draws every supertype or every subtype of a type in rows by
  longest path, and the term page links both.
  [web.md](docs/web.md#whole-kb-lists), [web.md](docs/web.md#a-types-whole-closure).

- **A page load that reads past `vaelii.browser.detach-ms` (default 5 s) is answered with
  a "Still reading" page.** The page reloads once the read is done. A second load of the
  same address in one session joins the running read, and `/jobs` lists the reads still
  running. [web.md](docs/web.md#page-loads-that-read-long).

- **A `:pg-snapshot` store can be backed up from its `/kbs` card.** The **Back up** button
  seals the KB, clones its directory and dumps its Postgres schema with `pg_dump`, beside
  the store, as a `:backup` job that holds off writes until the dump is done; `backup.edn`
  in the backup lists the restore commands. `vaelii.browser.backup`.
  [web.md](docs/web.md#backing-up-a-store-kept-in-postgres).

- **A browser store load shows what the open is doing, and `POST /op` answers `:kbs` and
  `:jobs`.** Each `:info`-or-louder line the engine logs during the open (the recover
  steps, the image install) becomes the load card's note, and still reaches the installed
  log backend. A cancel asked during the open is honoured at the next progress report.
  The reasoning-image install logs `::reasoning-image-installing` at its start as well as
  its outcome. `:kbs` is the catalog as EDN: the active key, the heap, and each entry's
  status, progress, error and live stored sentex count. `:jobs` is the job registry. Both
  answer while a job writes the active KB and every other op is refused with
  `:still-loading`. [web.md](docs/web.md).

- **The term page's taxonomy diagram frames a type's subtypes by the part lists over it,
  and `covers-of` answers them.** Below a type, the subtypes one `partition`, `covering`
  or `separating` declaration names sit in a frame labelled with the kind and its claims
  (`partition 1: covers, disjoint`); a subtype no part list names sits outside every
  frame. A subsumption arrow is blue and a `disjoint` edge amber, a pair that separates
  under protanopia and deuteranopia. A predicate of three or more places is red-orange
  and a `logical_connective` green. `vaelii.core/covers-of` answers the believed cover
  declarations over one whole as `[kind parts]`
  ([#158](https://github.com/vaelii/vaelii/issues/158)).
  [web.md](docs/web.md#a-terms-shape-drawn), [api.md](docs/api.md).

- **An extension adds menubar items and term actions.** `register-extension` takes
  `:menu`, `[[label href] …]` with each `href` under the extension's `/ext/<name>/`, drawn
  after the browser's own menubar items, and `:term-actions`, `(fn [env term] hiccup)`,
  drawn beside the heading of every term page. A menu item outside the prefix, or not a
  `[label href]` pair, is refused at registration (`:unknown-option`).
  [web.md](docs/web.md#extensions).

- **The browser's history lists only what the active KB holds.** `/history/known`
  answers which of a history's terms and handles the active KB holds, and vaelii.js
  forgets the rest each time it draws the Browsed panel. A KB whose load is running or
  stopped part-way is not judged. Switching back does not restore what was forgotten.
  [web.md](docs/web.md).

### Fix: answers

- **A containment or region part a calculus entails answers `partOf` and
  `properPartOf`, and the interval prover answers `subintervalOf` only within its
  domain.** A calculus prover lifts a positive goal on a super-predicate of one of its
  predicates to that predicate, and answers it beside the stored tuples: time intervals A
  and B with `(during A B)` answered `subintervalOf` and not `partOf`, since the `genl`
  edge reached only stored tuples, and `partOfRegion` and `properPartOfRegion` lift the
  same way. `subintervalOf` and `properSubintervalOf` answer only where each argument
  holds no type disjoint from `time_interval`, so two situations `(during S1 S2)` relates
  answer `during` and the reverse `hasSubinterval` and neither containment. An argument
  with no type is admitted. [glossary.md](docs/glossary.md), [time.md](docs/time.md).

- **A commutative binary function is not concluded `symmetric`.** `core.txt`'s rule
  `(commutative ?p) ∧ (arity ?p 2) → (symmetric ?p)` reads `(predicate ?p)` beside the
  arity. A `(function F)` stated `commutative` with `(arity F 2)` concluded `(symmetric
  F)`, which clashed with `(function F)` and was stored defeated.
  [canonicalization.md](docs/canonicalization.md#a-bridge-between-two-marks-is-a-cycle-backward)

  *Migration:* none.

- **A recovered store written before 0.24.0 withdraws its firings over superseded
  spellings.** Such a store kept a firing made over a spelling a later merge supersedes,
  and `recover` restored it, so the recovered KB believed a conclusion that a fresh KB
  given the same sentences does not hold. The rebuild now withdraws those firings, and
  the recovered store equals the fresh one.
  *Migration:* none. [nmtms.md](docs/nmtms.md#the-other-half-a-spelling-an-un-merge-gives-back)

### Fix: order independence

- **An argument-type mint reaches one belief in every arrival order beside a rule it
  supports and beside an equality merge.** A mint that a more specific membership
  subsumes is withdrawn when some subsumer does not rest on it, where a subsumer derived
  from the mint (`(awake Muffet)` from `(animal Muffet)`) could keep it. A mint drawn over
  a fact an equality merge already retired is restated at the elected name, where
  `(person Kipper)` stayed believed beside `(person Kip)` in the orders that merged first.
  [argtypes.md](docs/argtypes.md), [equality.md](docs/equality.md)

  *Migration:* none.

- **A membership that reaches `:monotonic` after it is stored stores its exact-arity
  class membership.** With a `:monotonic` route to `binary_predicate`, a `(rel_kind P)`
  derived first from a `:default` premise and then from a `:monotonic` one stored no
  `(binary_predicate P)` until a recover, so a ternary `(P a b c)` stayed believed. Both
  arrival orders now store the class membership and hold the tuple inert.
  [reference.md](docs/reference.md)

  *Migration:* none; a recover stores the missing class memberships.

- **A forward rule over a `genl` or `genlCx` literal stores one justification set in
  every arrival order.** With `(genl part_a whole)` and `(partition whole part_a part_b)`
  both stated, a rule over `(genl ?type whole)` stored one or two justifications of
  `(noted part_a)` by arrival order, and named the stated edge in some orders and the
  `partition` in others. Every order stores the one justification over
  `(genl part_a whole)`. Belief does not change.
  ([#192](https://github.com/vaelii/vaelii/issues/192),
  [#205](https://github.com/vaelii/vaelii/issues/205))
  [inference.md](docs/inference.md#a-genl--genlcx-antecedent-reads-the-closure),
  [taxonomy.md](docs/taxonomy.md)

  *Migration:* a store written before this release keeps its second justification over a
  stated edge; export and reload it as text to store one.

- **A `covering`, `separating` or `partition` on a route draws the argument-type mints a
  `genl` edge there draws, and an edge such a declaration installs subsumes a minted
  `genl` edge.** A cover arriving after a fact and a declaration it routes between mints
  the type, where it minted nothing; a mint over a cover's route is replaced by one over
  a shorter route arriving later; and retracting a cover or a trigger membership on a
  mint's route draws the mint again over a route or trigger that survives. A type whose
  only parent edge came from such a declaration kept every edge `genlArg` minted to an
  ancestor, such as `(genl context thing)`; the mint is now withheld when the declaration
  is there first, withdrawn when it arrives second, and drawn again when it leaves. With
  `VAELII_PRUNE_SUBSUMED_MINTS=0`, the upper layer and the starter hold the same
  justifications (`why`) in authored and content order.
  [argtypes.md](docs/argtypes.md#four-directions-or-belief-depends-on-arrival-order).

  *Migration:* none.

- **An inert fact draws no argument type on any sweep.** An inert fact asserted after
  an `arg` declaration got no type, and a declaration arriving after it, a forward chain,
  or a `genlCx` edge minted one anyway. `deduce-placed` and `retroactive-mints` skip an
  inert sentex, so every arrival order draws the same types.
  [argtypes.md](docs/argtypes.md).

- **A `genl` edge that places a preserved type under a separated one reports the clash
  it makes.** With `ic_dn` preserved and below `ic_dsup`, `(genl ic_dsup ic_hard)`
  written after `(disjoint ic_hard ic_plain)`, `(ic_dn ic_top)` and `(ic_plain ic_mid)`
  reported no inherited clash, where the same sentences with the edge written first
  reported one. The discovery re-opens each preserved predicate at or below the types an
  edge moves separations below.
  *Migration:* none. [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).

### Fix: performance

Each entry gives the same answers sooner. *Migration:* none for every entry here. A
perf check named in an entry bounds the growth `lein perf` measures.

- **A `genl` or `genlCx` edge's settle reads what the edge can move.** The nogood
  placement walks a moved edge's ancestor set only when the membership, negation,
  related-types or tuple family has work, so a chain of 4,096 `genlCx` edges asserted in
  one pass takes 3.1 s and its `recover` 0.2 s, where they took 15.3 s and 18.3 s
  (`recover-over-a-context-chain`). A `genlCx` edge's placement pass reads the `genl`
  edges and declarations stated below it off the postings of their functors, not every
  fact there: 3.4 to 9.0 ms beside 65,536 facts, where it took 80 to 103 ms. A `genlCx`
  edge to a context that stores nothing draws no argument types: a koinii agent joining a
  channel whose agents speak `CxSpeechActs` takes under 20 ms, where it took 1.8 s
  (`genlcx-edge-showing-an-empty-context`), and an edge from a context holding fewer postings
  than there are rule keys tests each fact's functor instead of building the rule-key fan
  (`genlcx-edge-to-an-empty-context-under-a-rule-fan`). A `genl` hierarchy loaded child first in one
  `with-deferred-settle` batch settles in time linear in its edges: 4,096 edges take 1.5
  s, where they took 46 s and grew 4x per doubling (`genl-chain-child-first-in-one-batch`).
  A `genl` edge whose lower end no rule concludes skips the stratification walk
  (`edge-stratification-unconcluded`), and re-asks the inherited clashes only of the
  facts below its lower end or at the terms of its closure, where it re-asked every
  membership below a separated end (`genl-edge-under-separated-type`,
  `genl-edge-past-the-crossing-cap`). A `forced_decontextualized_predicate` declaration
  arriving after its facts moves them into CxUniverse in one `edit!` batch, so a shuffled
  starter load takes 13.1 s of CPU, where it took 25.8 s.
  [nmtms.md](docs/nmtms.md#the-nogood-families),
  [nmtms.md](docs/nmtms.md#the-inherited-clash-memo),
  [exceptions.md](docs/exceptions.md#a-taxonomy-edge-closes-a-cycle-too),
  [contexts.md](docs/contexts.md#forced_decontextualized_predicate-a-canonical-home-in-cxuniverse).

- **The placement passes walk each type once.** A placement pass's witness walks to one
  target over one router test the depth potential alone and share the route lengths of
  the types above their sources, where each walk tested each type it entered by its whole
  upward closure. Walks up a braid of 128 levels cost 0.042 ms per level, where they cost
  2.47 ms (`routed-walks-up-a-braid`); over 3,200 leaves under a nine-level graph, a
  nogood costs 0.38 ms at 160 types per level, where it cost 6.9 ms. A settle beside
  standing inherited clashes hands the candidate index only the member sets it read
  again. A relabel evaluates a node's class once per rise that reaches it, where a node
  concluded by n justifications cost n² reads: a region of 28,642 nodes relabels in 12.9
  s, where it took 210 s. The witnesses, and so the placements, are unchanged.
  [taxonomy.md](docs/taxonomy.md#strength-of-a-subsumption-path),
  [nmtms.md](docs/nmtms.md).

- **An argument-type mint reads the term's own types and each type's watched rules
  once.** A mint the term already holds more specifically runs no admission check, so a
  fact beside 256 covers of its minted type takes 1.1 ms, where it took 12.1 ms, and a
  warm load of the upper ontology takes 3.4 s against 4.8 s
  (`withheld-mint-beside-covers`). The subsumption check reads the term's unary predicate
  set, where it ran one `genl` test per predicate holding the term at argument 1: a
  release of one term named by 5,000 facts over 300 declared predicates takes 468 ms,
  where it took 3,525 ms (`mint-beside-binary-predicates`). A release asks the
  watched-rule set's count and reads the rules for one type once: 0.30 ms per mint beside
  12,800 `exceptWhen` rules on a mapped index, where it cost 1.30 ms
  (`release-beside-watched-rules`). A departed membership reads its type's closure once
  per released term, where it walked from the type once per mint drawn. [argtypes.md](docs/argtypes.md), [indexing.md](docs/indexing.md).

- **A write and a preview read what the write moved, not every standing nogood.** A
  forward-rule trigger, a literal of an interpreted functor, a write beside a stored
  equality edge and a `with-deferred-settle` batch read the KB before the write off the
  values the write replaced, where their reports read every standing defeat's target and
  every placed `contradicts`' members. A `comment` and an inert term (`seeAlso`,
  `termsRelated`, the example annotations) read as a domain predicate's literal. An empty
  preview reads no stored `contradicts`, and a preview reads each nogood's placements
  once, where a member shared by k nogoods cost k² record reads. A write after a rolled-back preview re-asks no
  refused mint, constraint or lift the preview found settled, and a write beside
  declarations waiting on an unmintable type reads none of them while no generation
  moves: 0.2 to 0.4 ms beside 4,096 waiting declarations, where it took 2 to 3 ms
  (`write-after-rolled-back-preview`). The operation log replays a preview's writes and
  rollback alone. A retraction reads the handle term's own index key for the
  target-following metas naming each removed handle: retracting two root `genl` edges
  on the same store takes 7.2 s, where it took 208.3 s.
  [nmtms.md](docs/nmtms.md#the-published-set), [preview.md](docs/preview.md#cost),
  [preview.md](docs/preview.md#what-the-rollback-restores-and-what-it-does-not),
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings),
  [koinii.md](docs/koinii.md#speech-acts-reply-is-an-assertion).

- **A recover reads the store a chunk at a time and asks each question once.** A
  recover's settle fetches only the records of the forced-monotonic declarations, where
  it fetched every handle's record, one round trip a handle over Postgres. A recover hands the forced
  predicates' sentexes, the membership candidates' entries, the argument holds decided
  again, the argument declarations above a rule's predicates and the lower ends of `genl`
  edges to `Prefetching` a chunk ahead, and a reindex does the same for the
  declarations `post-taxonomy-supporters!` reads, logging its progress. A recover over a store holding an unsupported or inert record asks the whole store's
  inherited-clash questions off the index, where its settle read every region handle for
  what it re-opens. A denial probe of a preserved claim reads the stored denials once a pass,
  where it probed each tuple of a claim's product, and the first membership sync reads
  the cover wholes above a type through one memo, where it walked each type's ancestor
  set. An import of one of our dumps marks each premise once, at its own frame's
  strength, where the premise pass rewrote every premise row it had just copied. The taxonomy's closure cache
  holds one term per 256 bytes of maximum heap, and at least 50,000,000;
  `caches/set-limit :taxonomy-closures` still overrides it.
  [storage.md](docs/storage.md), [nmtms.md](docs/nmtms.md#the-inherited-clash-memo),
  [inherit.md](docs/inherit.md#what-one-question-costs),
  [nmtms.md](docs/nmtms.md#how-a-settle-finds-the-clashes),
  [taxonomy.md](docs/taxonomy.md).

- **A goal on a predicate with many sub-predicates reads only the members that can answer
  it.** The fan is cut to the members whose argument-slot key sets hold every ground
  argument of the goal, so a ground `(different A B)` under thousands of sub-predicates and
  `genlInverse` ones reads a few of them, and a forward join over a wide fan tests only
  those members per row (`ground-goal-under-a-wide-fan`). `tax/signed-closure` holds its walk of a fan with
  a `genlInverse` edge for the change clock's stretch, `provers/shadowing-channels` stops
  at the first concluding rule bucket, and a read that matches nothing builds no
  visibility state. [contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree).

- **An assert beside placed defeats checks disjointness at a cost that stays flat as
  facts accumulate.** The check walked every stored defeat's target once per supporter
  per assert; its answer is now held per ancestor set while the change clock stands. One
  fact per predicate over a braided hierarchy of 1,000 predicates loads in 43.1 s, where
  it took 224.7 s. A recover's tuple placement reads the `irreflexive` marks over its
  predicates once per call, where each predicate's marks were read through its own `genl`
  closure. [nmtms.md](docs/nmtms.md#the-nogood-families).

- **A `/stats` load reads no belief.** The Contradictions and Conflicts cards are the
  stored `contradicts` count, one index read, and the dilemma and conflict lists wait
  behind `/stats?nogoods=1`, as the standing disjointness question waits behind
  `?clashes=1`, where a load read each placed `contradicts` at its context.
  [web.md](docs/web.md).

### Internal

- **`prof/*handle-sink*` receives each handle a record fetch or a posting read answers,
  and `padding_blindness_test` lists every step that reads standing content a write does
  not name.** A read of the padding no row of `known-padding-reads` names fails the test.
  [profile.md](docs/profile.md), [nmtms.md](docs/nmtms.md#where-the-scaling-arguments-hold).

- **The nippy release check reads `thaw/expected-nippy-version`.** A nippy upgrade moves
  `vaelii.impl.io.thaw/expected-nippy-version`, and the `:nippy-version-moved` and
  `:nippy-version-unreadable` refusals carry the expected release under `:expected`.
  [defenses.md](docs/defenses.md), [troubleshooting.md](docs/troubleshooting.md).

- **A fork writes its base digests under `::base-digested`.** A mount reads the
  digested-handle set under `::base-digested` and the old key both, so a durable fork
  whose bookkeeping holds the set under either key reopens and is checked against its
  base. [overlay.md](docs/overlay.md).

- **`lein lint` fails the five words that each name several mechanisms (P5), the word
  for a context's visible set used in another sense (P6), and a top-level install into another namespace's slot
  (E20).** [prose rules in CONTRIBUTING.md §3.10](CONTRIBUTING.md).
  `lein lint-links` passes `--public-docs`. `handles` prints its result as
  `#vaelii/handle-set{n handles}`.

- **`lein perf` re-runs every check still over its bound once after the rest, and marks
  it.** Three checks are renamed: `verdict-published-set-write`,
  `negation-opposed-check-denials` and `constraint-genl-edge-unmarked`, and the
  `exceptWhen` rule-membership check is `watched-rule-membership`.

- **`project.clj` loads its helper definitions from `project-env.clj`, and RoaringBitmap
  is at 1.6.24.** A Docker build context or a copied checkout carries the file.

- **The development browser reloads no source while a job runs.** Edits made during a
  load, export or chain reload at the first request after the last job settles.
  [web.md](docs/web.md).

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
