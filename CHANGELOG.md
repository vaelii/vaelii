# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.27.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking

- **`termOfUnit` is renamed `natFormula`.** The reified-term map, `(natFormula K E)`
  in CxUniverse, is what a mint writes and what the engine reads to take a reified
  constant back to its expression. `core.txt` declares and comments `natFormula`, and
  every engine read, the browser and the docs name it. Nothing reads `termOfUnit` any
  more: no alias maps the old name onto the new one. The `natFormula` comment in
  `core.txt` is rewritten. [nat.md](docs/nat.md).

  *Class:* **Breaking** (KB vocabulary renamed).
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

- **A backward rule proves `(arity R n)` from a membership of an exact-arity class.**
  `query (arity R ?n)` of a relation stated only `(binary R)`, `(binary_predicate R)` or
  `(binary_function R)` answers `[{?n 2}]` at depth 3, where it answered nothing. No
  arity is stored, so the membership keeps the strength it was written at rather than an
  arity on the forced-monotonic roster being stored beside it. A depth-3 `query (arity ?p
  ?n)` over the starter answers one binding per relation with an exact-arity membership.
  The rule the `relationTypeByArity` generator stamps the other way, `(arity ?r n) → (T
  ?r)`, is `set/forwardOnlyRule`, so the two form no backward cycle.
  [taxonomy.md](docs/taxonomy.md#arity).

  *Migration:* none.
  *Breaks:* `query`

- **`kb-integrity` gains a default `:implicit-arity-class` category.** For each candidate
  with an exact length that is a predicate (resp. function) and is not an instance of the
  class `predicateTypeByArity` (resp. `functionTypeByArity`) maps that length to, the sweep
  reports `{:term R :kind predicate :arity 2 :class binary_predicate :mapping
  (predicateTypeByArity binary_predicate 2)}`. A default sweep over such a candidate
  answers `:status :gap` where it answered `:audited`. The pass applies the rule the two
  mappings stamp inert (below), and the shipped starter has no finding.
  [integrity.md](docs/integrity.md#what-an-implicit-arity-class-finding-means).

  *Migration:* state the reported class, or name the categories to run in `:categories`.
  *Breaks:* `kb-integrity`

- **`predicateTypeByArity` and `functionTypeByArity` are `termsRelated` to
  `relationTypeByArity`, not its `genl` specializations.** A `(predicateTypeByArity T n)`
  fact is no longer a `(relationTypeByArity T n)` fact, so the relation-wide generator
  stamps no rule for it and classifies no function of arity `n` under `T`. `genl?` of
  either mapping and `relationTypeByArity` answers false.
  [taxonomy.md](docs/taxonomy.md#relations-and-arity-policy).

  *Migration:* a KB that maps an arity with `predicateTypeByArity` or
  `functionTypeByArity` to classify every relation of that arity states
  `relationTypeByArity` instead.
  *Breaks:* `ask`, `query`, `genl?`

- **A `type_relation_predicate`'s arguments are predicates.** `core.txt` concludes `(args
  R predicate)` forward from `(type_relation_predicate R)`: `predicate` and not
  `unary_predicate`, since `genl` relates predicate specializations of any arity. `query
  (args disjoint ?t)` answers `[{?t predicate}]`, a symbol argument of `genl`, `disjoint`
  or another type-level relation is derived a `predicate` under assertive argument types,
  and one whose types place it outside `predicate` is refused `:arg-type`.
  [taxonomy.md](docs/taxonomy.md).

  *Migration:* a KB relating terms that are not predicates through a
  `type_relation_predicate` drops the mark from that relation.
  *Breaks:* `assert`, `query`

- **`arg`, `arg1`, `arg2`, `arg3`, `interArg` and `argArg` are admitted on a
  `type_relation_predicate`.** `assert` and `check` refused each `:arg-constraint-kind`.
  The kinds such a relation relates are instances of a type as well as subtypes of one, so
  `(arg disjoint 1 unary_predicate)` is a true instance claim and is stored. `genlArg` on
  an `instance_relation_predicate` is still refused `:arg-constraint-kind`.
  [api.md](docs/api.md).

  *Migration:* a caller that relied on the refusal to keep instance constraints off a
  type-level relation checks `type_relation_predicate` itself.
  *Breaks:* `assert`, `check`, `:arg-constraint-kind`

- **`kb-quality`'s rule-clash reading reads `args` and `argAndRest` as it reads `arg`.** A
  pair whose shared term a covering declaration types disjoint from what the other rule
  places it in is unreachable and no longer reported. Over the starter, `(function ?r)
  (arity ?r 1) → (unary_function ?r)` against `(unary ?type) (disjoint ?type ?type) →
  (empty ?type)` is dropped, `disjoint`'s arguments being predicates.
  [quality.md](docs/quality.md).

  *Migration:* none.
  *Breaks:* `kb-quality`

- **The term kinds are on the forced-monotonic roster.** `relation`, `predicate`,
  `function`, `truth_valued_relation`, `logical_constant`, `logical_connective`,
  `quantifier`, `symbol`, `context`, `unrepresented_term` and its value kinds (`boolean`,
  `character`, `keyword`, `number`, `integer` and its four sign classes, `string`, and
  CxTra's `ip_address`, `ipv4_address` and `ipv6_address`) go OUT only by retraction. Two
  term kinds stated of one term are an irreducible conflict: a `:default` `(predicate X)`
  beside a `:default` `(string X)` or `(unary_function X)` leaves both believed and
  `conflicts` reports the pair, where one of them was the loser. A stored denial of a
  term kind is never believed, so `(not (truth_valued_relation X))` beside `(relation X)`
  no longer concludes `(function X)` through the cover of `relation`; state `(function X)`.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Migration:* retract one of two clashing term kinds, since a defeat no longer picks one,
  and state a term's kind outright rather than denying the others.
  *Breaks:* `ask`, `query`, `conflicts`, `contradictions`

- **The intersection membership rule confers `:monotonic`.** Each `(intersection C A B)`
  fact stamps a bare `(implies (and (A ?x) (B ?x)) (C ?x))` rather than a
  `set/defaultRule`, so a thing stated of each type at `:monotonic` is a `:monotonic`
  member of `C`, and wins a clash with a `:default` membership where the two were a
  dilemma. A `:default` conjunct still makes a `:default` member. A `C` on the
  forced-monotonic roster is concluded from roster conjuncts, where every firing was void.

  *Migration:* state a conjunct at `:default` where the combined membership should stay
  defeasible.
  *Breaks:* `ask`, `query`, `contradictions`, `violations`

- **The arity policies and the numeric comparators are on the forced-monotonic roster.**
  `fixed_arity`, `fixed_arity_predicate`, `fixed_arity_function`, `bounded_arity`,
  `unbounded_arity`, `at_least_binary`, `arityMax`, `admitsArgnum`, `greaterThan` and
  `lessThan` go OUT only by retraction, as the arity bindings do. A `:default`
  `(fixed_arity R)` beside a `:default` `(variable_arity R)` is an irreducible conflict:
  both stay believed and `conflicts` reports the pair, where `fixed_arity` was the loser.
  `(animal X)` beside `(fixed_arity_predicate X)`, whose argument position derives
  `(relation X)`, now takes `animal` OUT, where `relation` was the one held in the clash.
  `greaterThan` is on the roster so that the `core.txt` rules concluding `at_least_binary`
  and `at_least_ternary` from `arity` and `arityMin` read roster antecedents only.
  `at_least_ternary`, the quantity comparators (`quantityGreaterThan`,
  `quantityGreaterThanOrEqual`, `quantityLessThan`, `quantityLessThanOrEqual`,
  `sameQuantity`) and the argument declarations (`arg`, `arg1`, `arg2`, `arg3`) are on the
  roster too, and `forced_monotonic_between_predicates` is declared of `genlInverse`, so a
  `genlInverse` between two predicates is forced as a `genl` between them is, and a
  denial of an `arg` declaration is never believed.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Migration:* retract one of two clashing arity policies; a defeat no longer picks one.
  *Breaks:* `ask`, `query`, `conflicts`

- **A `:default` `genl` edge no longer contraposes.** With `(genl pa pb)` at `:default` and
  `(not (pb Zz))` stored or derived, `query (not (pa Zz))` answers nothing and `argue (pa
  Zz)` answers `:unknown`, where they answered `[{}]` and `:false`. In a context that
  holds the edge at `:default` only, a forward rule on `(not (pa ?x))` does not fire on
  `(not (pb A))`, an `exceptWhen` query `(not (pa ?x))` blocks nothing for `A`, `(pa Rex)`
  beside `(not (pb Rex))` is no `:supertype` nogood, and `(not (pb X))` does not deny the
  part `pa` of a cover. An edge the reader holds at `:monotonic`, or one a roster
  installs, contraposes as before, the rule a separation's denial already follows. The
  two time intersections in `core.txt` are `:monotonic`. Closes #188.
  [inference.md](docs/inference.md#predicate-subsumption-in-matching).

  *Migration:* assert a `genl` or `genlInverse` edge with `{:strength :monotonic}` where a
  denial of its upper end should deny its lower end.
  *Breaks:* `query`, `argue`, `conflicts`, `contradictions`, `exceptWhen`

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

- **`partOf` between two tangibles is `tangiblePartOf`, and `partOf` is parthood of any
  kind.** `tangiblePartOf` keeps both arguments `tangible`, its transitivity and partType's
  `typeToInstancePred`. The new `partOf` is transitive and declares `thing` in both
  positions, and `tangiblePartOf`, `partOfRegion` and `subSituationOf` are below it by
  `genl`. A `tangiblePartOf` fact answers `partOf`, and a `partOf` fact answers no
  `tangiblePartOf`. CxMereology's two rules read `tangiblePartOf`. [glossary.md](docs/glossary.md).

  *Class:* **Breaking** (KB vocabulary renamed).
  *Migration:* write `tangiblePartOf` for a `partOf` fact, rule or declaration between
  two tangibles; a query for any parthood keeps `partOf`.
  *Breaks:* `partOf`

- **`subintervalOf` and `properSubintervalOf` take two `time_interval`s, not two
  `temporal`s.** Both comments say "?interval1 falls within ?interval2". No KB file
  states a tuple of either, and every calendar term already yields a `time_interval`.
  Once tightened they are parthood of times: `subintervalOf` is reflexive and below
  `partOf`, and `properSubintervalOf` is irreflexive, transitive and below `properPartOf`.
  [time.md](docs/time.md).

  *Class:* **Breaking** (argument type narrowed).
  *Migration:* relate two events by `during`, `starts` or `finishes`, or relate their
  times; a `subintervalOf` between two situations now types each as a `time_interval`,
  which `(disjoint time situation)` refuses.
  *Breaks:* `subintervalOf`, `properSubintervalOf`

- **`partitionedByType` is binary, `(partitionedByType ?whole ?classifier)`, and draws
  inference.** The members of `?classifier` partition `?whole`. A core.txt generator places
  each member under `?whole`, and a rule concludes `(disjoint_metatype ?classifier)`. No
  rule draws the coverage half (vaelii/vaelii#171), so the `partition` sentence stays
  beside each of the 4 shipped facts: `fixed_order_type` by `type_type_by_order`,
  `tangible` by `origin_type`, and `thing` by `spatiality_type` and by
  `temporality_type`. The three `genl` edges to `fixed_order_type` stay stated at
  `:monotonic` beside the derived ones. [glossary.md](docs/glossary.md).

  *Class:* **Breaking** (KB vocabulary arity changed).
  *Migration:* drop the cell list: write `(partitionedByType W C)` for
  `(partitionedByType W C A B …)`, and state each cell's membership `(C A)`.
  *Breaks:* `partitionedByType`

- **`(args R T)` derives `(argAndRest R 1 T)`.** A `set/forwardRule` in `core.txt` states
  the entailment the two spellings' comments describe and stores the `argAndRest` twin, so
  `query (argAndRest R ?n ?t)` answers `[{?n 1 ?t T}]` of a relation declared only
  through `args`, and the readers of what a position holds (`res/arg-constraints`) look up
  `arg` and `argAndRest` alone. So do the assert-time checks: an `args` declaration is
  refused, and derives memberships, through the twin, whose handle an entailment rests on
  and whose `argAndRest from 1, position N` a refusal names. Retracting the `args`
  declaration retracts the twin. [argtypes.md](docs/argtypes.md).

  *Migration:* a KB that loads `core.txt` needs none. A KB that does not has no forward
  rule, so its `args` declarations type nothing: state `(argAndRest R 1 T)` instead, or
  assert the rule.
  *Breaks:* `args`, `assert`, `check`

### Additive

- **A quoted application is classified by what the KB states of its head.** Under a
  symbol head R, `(predication (Quote (R a)))` holds when R is a member of `predicate` or
  a type below it, `(non_atomic_term (Quote (R a)))` when R is a function and the form is
  closed, and `ill_formed_expression` (`ill_formed` for a predicate) when R's length rules
  out the argument count. R's spelling is never read. The answer cites the membership,
  the bindings and the `genl` edges it rests on, and a forward rule over one of these kinds
  fires whether the head's kind arrives before or after the rule and the quoted fact
  ([#145](https://github.com/vaelii/vaelii/issues/145)).
  [argtypes.md](docs/argtypes.md#what-a-quoted-form-is).

- **`core.txt` ships the predicate and function exact-arity mappings, whose stamped rules
  are inert.** `(predicateTypeByArity unary_predicate 1)` through `(predicateTypeByArity
  quinary_predicate 5)`, one fact per exact-arity predicate class, and the five
  `functionTypeByArity` peers over `unary_function` through `quinary_function`.
  `(predicateTypeByArity T n)` stamps `(predicate ?r) ∧ (arity ?r n) →
  (T ?r)` as a `set/inertRule`, and `(functionTypeByArity T n)` the same rule over
  `(function ?r)`: believed and browsable, run on no write and no query. Run backward, the
  rule reached `(binary ?r)` through `binary_predicate`'s `genl` edge while the converse
  proves `(arity ?r 2)` from `(binary ?r)`; `kb-integrity`'s `:implicit-arity-class` pass
  applies it instead, and every predicate and function the starter ships states its class.
  [taxonomy.md](docs/taxonomy.md#relations-and-arity-policy).

  *Class:* **Additive** (shipped ontology content).
  *Migration:* none.

- **`minCommonGenl` and `maxCommonSpec` answer the minimal common supertypes and maximal
  common subtypes of their later arguments.** `CommonGenlProver` computes both from the
  `genl` closure through the edges the asking context sees. `(minCommonGenl ?x dog
  cat)` binds `?x` to each member of `(min-common-genls kb [dog cat])`. A
  ground first argument proves true when it is a member and proves false when it is not,
  so `argue` answers `:false` for a type outside the set rather than `:unknown`.
  `maxCommonSpec` answers `max-common-specs` the same way. `core.txt` declares both
  variable-arity with `arityMin` 2, and both are query operators: asserting one is
  refused as `:not-well-formed`. [inference.md](docs/inference.md).

- **`common-genls`, `common-specs`, `min-common-genls` and `max-common-specs` read the
  supertypes and subtypes a collection of types shares.** `(common-genls kb [a b])` is the
  intersection of `(genls kb a)` and `(genls kb b)`, reflexive as `genls` is, and
  `common-specs` intersects `specs` the same way. `min-common-genls` keeps the members of
  that intersection that are strictly above every input and have no other such member
  below them: with `a` and `b` each under both `left` and `right`, it is `#{left right}`,
  and with `dog ⊂ mammal ⊂ animal`, `(min-common-genls kb [dog mammal])` is `#{animal}`.
  One input type gives `min-genls` of it. `max-common-specs` is the same read downward.
  Each takes a context, and `vaelii.client` and the daemon serve all four.
  [api.md](docs/api.md).

- **A shipped argument position that holds a term of any kind declares `thing`.** `(arg P
  n thing)` states that position `n` of `P` holds a term of any kind and that no narrower
  type is right for it. `core.txt`, `abstract.txt`, `reflection.txt`, `society.txt`,
  `CxPerception.txt`, `CxComputing.txt` and `CxSpeechActs.txt` state 51 such `arg`
  declarations, among them `(arg equals 1 thing)`, `(arg doneBy 2 thing)` and `(arg
  believes 1 thing)`, and `(args different thing)` types every position of `different`.
  `(genlArg toolArgType 3 thing)` types the third position of `toolArgType` a type. A
  documentation position holds the term it documents taken as written, so `comment`,
  `seeAlso`, the three example predicates and their three string siblings declare
  `(quotedArg P 1 denotational_term)`. `seeAlso` declares its second position the same
  way, and `argN` declares `(quotedArg argN 1 expression)`. A fixed-arity predicate's
  position of arity 2 and up is declared, or `ontology_test`'s `undeclared-positions`
  names it with its reason. The two `genl` positions, the example predicates' quoted
  sentence and the aggregation operators' slots are the positions it names. [argtypes.md](docs/argtypes.md#constraint-and-entailment-readings).

  *Class:* **Additive** (shipped ontology content).
  *Migration:* none. Under the entailing reading, a symbol at one of these positions with
  no narrower membership derives `(thing X)`.

- **The browser's history lists only what the active KB holds.** The front page's
  Browsed panel is kept in the browser's localStorage, so a switch to another KB left it
  listing terms and sentexes the new one does not hold, each a link to an empty page.
  `/history/known` answers which of a history's terms and handles the active KB holds,
  and vaelii.js forgets the rest each time it draws the panel. A KB whose load is running
  or stopped part-way is not judged, so nothing is forgotten until its load is `:done`.
  Switching back does not restore what was forgotten. [web.md](docs/web.md).

- **`hasCapability` takes any causal doer as its first argument, not only an animal.**
  `(arg hasCapability 1 causal)` replaces `(arg hasCapability 1 animal)` in `life.txt`,
  so `(hasCapability Pump travelling)` of a `machine` or `(hasCapability Acme event)` of
  an `organization` passes `check`, and an acausal first argument, such as a `time`, is
  still convicted, now against `causal`. An instrument is not thereby a doer, so being
  usable in a kind of event is not a capability. [inherit.md](docs/inherit.md).

- **`relation-arity` answers a predicate's exact arity, and the browser colours a
  predicate of three or more places red-orange and a logical connective green.** A
  connective is a `logical_connective` member: `and`, `or`, `not`, `implies`.
  `(relation-arity kb 'arg)` is `3`; a `variable_arity` relation, or a term no length
  binds, answers nil. `vaelii.client` and the daemon serve it. [api.md](docs/api.md),
  [web.md](docs/web.md).

- **General happening roles admit interrupted occurrences; `invokesTool` is renamed
  `toolInvoked`.** `actor` relates a happening to a meaningful participant, and
  `thingPerceived` relates it to what is perceptually taken in. `doneBy`, `performedBy`,
  `input`, `destroyedInput`, `preservedInput`, `output`, `tangibleOutput` and
  `intangibleOutput` now declare `happening` rather than `event` in position 1. Participation
  alone concludes neither intentional doing nor perception. The tool relation retains
  its invocation-first argument order and `tool_invocation`/`software_tool` bounds.

  *Migration:* update stored tool facts, rules, queries and writers to `toolInvoked`;
  this change does not migrate a live store. Callers inspecting the eight role domains
  must expect `happening`; state `event` separately when uninterrupted occurrence is
  required. Existing participant subtype bounds remain in force.

- **`+with-postgres`, `+with-sqlite` and `+with-foreign` add the published siblings to any
  lein task, the uberjar included.** `lein with-profile +with-postgres browser` opens a
  `:pg-*` KB from this checkout, `lein with-profile +with-postgres,+with-sqlite uberjar`
  builds a standalone jar that opens both, and the `Dockerfile`'s `PROFILES` build
  argument builds the image that way. The default uberjar and the published pom carry no
  adapter. `scripts/link-checkouts.sh` links all three siblings' live source. An adapter
  that loads without its dependencies refuses with `:missing-adapter`, naming the
  namespace that failed, instead of a `CompilerException`.
  [storage.md](docs/storage.md#backend-selection-two-independent-axes),
  [foreign.md](docs/foreign.md#exercising-one-from-here).

  *Migration:* `scripts/with-foreign.sh <task>` is gone; run `lein with-profile
  +with-foreign <task>`.

- **Relations of four and five arguments have exact arity classes, and a function's
  result types the value position of its corresponding predicate.** `quaternary` and
  `quinary` are relation-wide exact classes, and `quaternary_predicate`,
  `quinary_predicate`, `quaternary_function` and `quinary_function` specialize them.
  `(arity R 4)` concludes `(quaternary R)`, and `(arity R 5)` concludes `(quinary R)`.
  One `(separating fixed_arity unary binary ternary quaternary quinary)` roster separates
  the five classes, so a further class adds one part and no `disjoint` pair.
  `at_least_quaternary` and `at_least_quinary` extend the arity floors. Each floor is
  disjoint from the exact class one below it, and so from every exact class below it
  through `genl`. `kb-quality`'s rule-clash reading drops a pair in which one term is
  bounded above the exact arity it is claimed to have, so a floor rule and an
  exact-class rule are no clash in waiting: the shipped KB reads four excepted
  `:negation` pairs, where it would read 86. `arg4` and `arg5` project `arg` at positions
  4 and 5, and `closedExtentForArg4` and `closedExtentForArg5` spell `closedExtentForArg`
  at those positions. `at_least_quaternary`, `at_least_quinary`, `arg4` and `arg5` are on
  the forced-monotonic roster beside the floors and projections below them. `calendarDay`,
  `measureRangeInUnit`, `predExistsInstancePlaceholder` and `predInstanceExistsPlaceholder` are
  `quaternary_predicate`. `interArg`, `predAllExistsPlaceholder` and
  `predExistsAllPlaceholder` are `quinary_predicate`. `PredAllExistsFn` and
  `PredExistsAllFn` are `quaternary_function`. Forward rules conclude `(arg P n T)` from
  `(result F T)` and `(functionCorrespondingPredicate F P)`: `n` is the last position of a
  binary through quinary `P`, or the position the correspondence states. `functionCorrespondingPredicate`
  and `result` are on the forced-monotonic roster with `arg`, so those firings are not void. A test holds
  every shipped predicate in an exact arity class or `variable_arity`; a `fixed_arity`
  relation above five arguments, such as `calendarInstant`, has no named class.
  [taxonomy.md](docs/taxonomy.md#arity).

- **`admitsArgnum`'s eight definition rules are `set/backwardRule`, so an answer has a
  proof in the logic.** `query (admitsArgnum doneBy ?n)` answers `1` and `2`,
  `(admitsArgnum calendarDay ?n)` answers `1` through `4`, and `(admitsArgnum ?r 7)`
  answers each `unbounded_arity` relation. Each answer's `{:proof? true}` tree cites the
  rule that derives it. `AdmitsArgnumProver` answers a ground goal beside the rules. The
  rules store no `admitsArgnum` fact. [inference.md](docs/inference.md).

- **`exceptWhen` is on the forced-monotonic roster, as `except` is.** `decide/held-members`
  names it, since taking an `exceptWhen` meta-sentex OUT unblocks the firings of the rule it
  names. `core.txt` states `(forced_monotonic_predicate exceptWhen)`, `(binary_predicate
  exceptWhen)` for the two arguments of the stored meta-sentex, and a `comment` of
  `exceptWhen`, and `retract!` refuses the declaration with `:type :uncleared-forcing` and
  `:missing :unforced-exception`. [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

- **`(negates P Q)` states that two relations hold of no argument list together.** A
  believed `(scorns Eve Fay)` beside a believed `(admires Eve Fay)` under `(negates scorns
  admires)` is one placed nogood, read down `genl` on both sides, whichever arrives first.
  `ask? (not (scorns Gus Hal))` is true while `(admires Gus Hal)` is believed, and no
  denial is stored per fact. `(negates P P)` makes each `P` tuple a one-member nogood. A
  declaration whose sides are bound to lengths no argument list fits, or to one argument,
  is stored and reported in `conflicts` as `:negates-arity` or `:negates-unary`. The
  declaration is forced-monotonic and context-scoped
  ([#106](https://github.com/vaelii/vaelii/issues/106)).
  [taxonomy.md](docs/taxonomy.md#predicate-metadata).

  *Migration:* none. A KB storing `negates` facts of its own reads them as declarations.

- **The upper ontology states `logical`, `quantitative`, `typeOrthogonal`,
  `orthogonalMetatypes` and `implementationNote`, and derives 43 genl, disjoint and
  orthogonal sentences it stated, and no longer states 40 of them.** `(separating nowhere_never logical linguistic
  quantitative)` separates three kinds: `relation`, `proposition` and `context` are
  `logical`, and `measure`, `unit_of_measure`, `physical_dimension` and `sign_value` are
  `quantitative`. `(typeOrthogonal ?classifier ?type)` makes every member of a classifier
  orthogonal to `?type`, and `(orthogonalMetatypes ?m1 ?m2 …)` makes every member of each
  metatype orthogonal to every member of the others, for two and three metatypes
  (vaelii/vaelii#170). Each is a core.txt rule generator. The classifiers `arity_type`,
  `origin_type`, `spatiality_type` and `temporality_type` are new, and each classifier a
  rule reads is on the forced-monotonic roster. 10 `typeOrthogonal` facts and one
  `orthogonalMetatypes` fact derive 33 orthogonal pairs, 22 of them stated before, and
  every arity type is orthogonal to `abducible_predicate`. 9 more orthogonal pairs are
  stated, e.g. `made` and `vertebrate`, `animal` and `food`. `warm_blooded` is below
  `vertebrate` by default. `physical` is new: a location in the physical space of our
  universe, below `spatial`. `spatiotemporal` is below `physical` and `temporal`, and
  reaches `spatial` through `physical`. `implementationNote` is a
  sibling of `comment` for how a term is implemented, and 14 core.txt terms carry one.
  [taxonomy.md](docs/taxonomy.md), [glossary.md](docs/glossary.md).

  *Class:* **Additive**.

- **The upper ontology states `subSituationOf` and the 15 converse pairs of the spatial
  calculi.** `(subSituationOf ?part ?whole)` relates two situations, is transitive, and is
  below `partOf`. A part's time is within its whole's time, and the converse does not
  hold; no rule concludes the containment yet, since no upper relation states one time
  within another that covers an intermittent time. space.txt states each converse pair of
  the RCC-8, cardinal and relative-direction calculi as `(set/inert (inverse P Q))`, so
  each calculus prover still answers its goals alone. `space_test` pins the pairs against
  each algebra's converse. space.txt also states `(genl spatiallyEqual partOfRegion)` and
  `(genlInverse P partOf)` for `hasRegionPart`, `tangentialProperPartInverse` and
  `nonTangentialProperPartInverse` under `set/inert`. RCC-8 entails each of the four
  edges, and `space_test` pins that entailment.

  *Class:* **Additive**.

- **Parthood is reflexive or proper, and each parthood relation has its proper reading.**
  `partOf`, `tangiblePartOf`, `partOfRegion`, `subSituationOf` and `subintervalOf` each
  carry their own `reflexive` mark. `properPartOf` is irreflexive, transitive and below
  `partOf`. Its definition is `(partOf x y)` with `(partOf y x)` denied, and antisymmetry
  is declined and stated so: `(not (anti_symmetric partOf))`. `properTangiblePartOf` and
  `properSubSituationOf` are new, and `properPartOfRegion` and `properSubintervalOf` join
  them below `properPartOf`. `(properCounterpart ?predicate ?properPredicate)` records each
  pair, and a core.txt generator stamps its definition. The proper tuple needs a believed
  denial of the reverse, never the reverse being unknown. One rule at the root,
  `(properPartOf x y)` to `(not (partOf y x))`, denies the reverse for every proper
  relation below it. The two calculus-owned pairs
  state their counterpart and their inner `genl` edges inert, so each calculus still
  answers alone. `ontology_test` holds two invariants. Every spec of `partOf` is reflexive
  or below `properPartOf`. A spec both symmetric and irreflexive is flagged for review.
  [glossary.md](docs/glossary.md).

  *Class:* **Additive**.

- **A new OE principle, "bank the decision".** A modelling question weighed and answered
  no is stated in the KB as an explicit negation, and a `(not …)` is asserted only for a
  decision actually made. [oe-principles.md](docs/oe-principles.md).

  *Class:* **Additive**.

- **`capabilityType` and `hasCapability` take a happening kind as argument 2, not only an
  event kind.** `(genlArg … 2 happening)` replaces `(genlArg … 2 event)` in life.txt, so an
  ability whose exercise has gaps, such as a happening kind under `intermittent`, is
  accepted. Each event kind is still accepted, being a happening kind.
  `ontology_test`'s `all-dogs-have-shell-access` pins both predicates over such a kind, with
  no `genl` to `event` drawn. [inherit.md](docs/inherit.md).

  *Class:* **Additive**.

### Fix: answers

- **`ArgTypeProver` types a term at a position an `argAndRest` declaration types.** A
  believed `(P … x …)` with `x` at position `n` or later beside `(argAndRest P n T)`
  answers `(T x)`, as `(arg P n T)` at `x`'s position does; `(args P T)` answers through
  the `argAndRest` twin its rule stores. The exception re-check that follows the inference
  reads the same declarations, in both arrival orders. The prover reads a predicate's
  declarations through `res/arg-constraints-at`, held for one stretch of the change clock.
  [argtypes.md](docs/argtypes.md)

  *Migration:* none. Under the constraint-only reading, `ask` answers such a membership
  where it answered nothing.

- **A `predAllSpecified` or `predSpecifiedAll` slot typed by a tail declaration is
  audited.** A slot typed only by `argAndRest`, `args`, `argAndRestGenl` or `argsGenl`
  reported `{:status :gap :gap :missing-slot-typing}`; the audit now derives its contract
  from those declarations as from `arg` and `genlArg`. [predall.md](docs/predall.md)

  *Migration:* none. A declaration that reported the gap reports `:audited`.

- **A commutative binary function is not concluded `symmetric`.** `core.txt`'s rule
  `(commutative ?p) ∧ (arity ?p 2) → (symmetric ?p)` reads `(predicate ?p)` beside the
  arity. A `(function F)` stated `commutative` with `(arity F 2)` concluded `(symmetric
  F)`, which clashed with `(function F)` and was stored defeated, since `symmetric`
  classifies binary predicates only. It now concludes nothing.
  [canonicalization.md](docs/canonicalization.md#a-bridge-between-two-marks-is-a-cycle-backward)

  *Migration:* none.

- **`why-not` of a handle answers `:excepted` for a conclusion stored with a guard
  defeat.** A conclusion whose `exceptWhen` holds through a `:default` blocker is stored
  OUT with a guard defeat. `why-not` of its handle answered `:unsupported` with no missing
  antecedent, and the browser's belief pill read "unsupported". It now answers
  `:excepted` with `:rule`, `:exception` and `:via`, as the sentence arity does.
  [exceptions.md](docs/exceptions.md#semantics)

  *Migration:* none. A caller reading `:unsupported` off such a handle reads `:excepted`.

- **The from-Cyc guide translates a binary `negationPreds` as `negates`.** The two
  implication rules it gave for mutual exclusion above arity 1 convicted nothing when
  both tuples were stored ([#106](https://github.com/vaelii/vaelii/issues/106)).
  [from-cyc.md](docs/from-cyc.md#negation-and-mutual-exclusion).

  *Migration:* replace the two rules with one `(negates P Q)`.

- **`kb-quality`'s clash reading drops a pair whose antecedents put a literal beside a
  denial of a predicate it is a spec of.** A tuple of a spec is a tuple of the predicate
  above it, so `(properPartOf a b)` and `(not (partOf a b))` cannot both hold, and the
  pair is no clash in waiting. [quality.md](docs/quality.md).

  *Class:* **Fix**.

- **The interval prover answers `subintervalOf` and `properSubintervalOf` only within
  their declared domain.** Each argument must hold no type disjoint from `time_interval`.
  Two situations `(during S1 S2)` relates answered both, though `situation` and
  `time_interval` are disjoint. The pair now answers `during` and the reverse
  `hasSubinterval`, which take any temporal thing, and neither containment. An argument
  with no type is admitted.
  [time.md](docs/time.md).

  *Class:* **Fix**.

- **A containment or region part a calculus entails answers `partOf` and
  `properPartOf`.** A calculus prover lifts a positive goal on a super-predicate of one
  of its predicates to that predicate, and answers it beside the stored tuples. Time
  intervals A and B with `(during A B)` answered `subintervalOf` and not `partOf`, since
  the `genl` edge reached only stored tuples. `partOfRegion` and `properPartOfRegion`
  lift the same way. [glossary.md](docs/glossary.md).

  *Class:* **Fix**.

### Fix: performance

- **A `genl` hierarchy loaded child first in one batch settles in time linear in its
  edges.** A chain of 4,096 `genl` edges asserted in one `with-deferred-settle` batch took
  46 s and grew 4x per doubling; it now takes 1.5 s. The settle repairs the depth
  potential before its passes read `genl?`, and an edge reads its lower end's spec closure
  for the negated-antecedent seeds only when a stored rule reads a negated antecedent.
  *Migration:* none.
  [taxonomy.md](docs/taxonomy.md#what-a-batch-does-to-the-depth-potential). Perf check
  `genl-chain-child-first-in-one-batch` measures the growth.

- **A fact whose argument type mints a membership the term already holds more
  specifically runs no admission check on the mint.** The mint is withheld and stores
  nothing, but the assert entry point and the materializer each asked its admission, whose
  cover arm asks the provers once per cover over the type. A fact beside 256 covers of its
  minted type took 12.1 ms and now takes 1.1 ms, and a warm load of the upper ontology
  takes 3.4 s against 4.8 s. *Migration:* none.
  [argtypes.md](docs/argtypes.md). Perf check `withheld-mint-beside-covers` measures the
  growth.

- **A settle that owes only the arity refresh does not read what its `genlCx` moves
  reach.** The nogood placement walked the ancestor set of every context a moved edge
  sits under whenever any nogood family had work, though only the membership, negation,
  related-types and tuple families read the walk. A chain of 4,096 `genlCx` edges
  asserted in one pass took 15.3 s and its `recover` 18.3 s; they now take 3.1 s and
  0.2 s. *Migration:* none.
  [nmtms.md](docs/nmtms.md#the-nogood-families). Perf check
  `recover-over-a-context-chain` measures the growth.

- **A `genlCx` edge to a context that stores nothing draws no argument types.** The
  edge's argument-type sweep drew every declared fact in the contexts its lower end
  already saw again, though a context storing nothing gives no fact a new declaration or
  route. A koinii agent joining a channel whose agents speak `CxSpeechActs` took 1.8 s,
  rereading the upper ontology in CxUniverse, and now takes under 20 ms.
  *Migration:* none. [argtypes.md](docs/argtypes.md#where-a-mint-is-placed).
  Perf check `genlcx-edge-showing-an-empty-context` measures the growth.

- **A goal on a predicate with many sub-predicates reads only the members that can answer
  it.** A literal's matches are read once per member of its functor's fan, so a ground
  `(different A B)` under 3,054 sub-predicates and 3,050 `genlInverse` ones cost 76 ms,
  and a forward join tests one per row: re-recording the refusals of a recover fired four
  rules joining `(different ?b ?a)` over 108,571 `genl` rows, and the recover took 14 hours. The fan is
  now cut to the members whose slot rosters hold every ground argument of the goal, and
  each member left is read as before. `tax/signed-closure` holds its walk of a fan with
  a `genlInverse` edge for the change clock's stretch. `provers/shadowing-channels` asks
  `res/concludes?`, which stops at the first rule bucket it finds, where it built the
  whole `concluding-rule-handles` set. `res/without-unbelieved-spellings` reads the
  `reifiable_function` marks only when a match reaches it. The same goal costs 0.5 ms.
  Perf check `ground-goal-under-a-wide-fan` pins the growth.

  *Class:* **Fix** (the same answers, sooner).

- **An edge a `covering`, `separating` or `partition` roster installs subsumes a minted
  `genl` edge, as a stated edge does.** A type whose only parent edge came from a roster
  kept every edge `genlArg` minted to an ancestor, such as `(genl context thing)`. Each
  new justification of that record moved a `genl` edge into `thing`, and the inherited-clash
  memo then asked every membership again. The mint is now withheld when the roster is
  there first, withdrawn when it arrives second, and drawn again when it leaves.
  [argtypes.md](docs/argtypes.md).

  *Class:* **Fix**.

- **`recover` skips the store-wide inherited-clash sweep in a store holding inert
  facts.** The skip asked for a region at least the store's size, and an inert sentex
  is never in a settle's region, so the 15 inert `inverse` facts in `space.txt` turned
  each `recover` into a sweep over every membership. A region missing only inert
  sentexes now counts as the whole store.

  *Class:* **Fix**.

### Fix: order independence

- **An inert fact draws no argument type on any sweep.** An inert fact asserted after
  an `arg` declaration got no type. A declaration arriving after it, a forward chain, or
  a `genlCx` edge minted one anyway. `deduce-placed` and `retroactive-mints` now skip an
  inert sentex, so every arrival order draws the same types.
  [argtypes.md](docs/argtypes.md).

  *Class:* **Fix**.

### Breaking

- **`quoting_function` removed; Quote and Quasiquote are the quoting functions,
  hard-coded.** Which functions quote is fixed by the engine (`sx/quoting-functors`), not
  declared in the KB. A `Quote` or `Quasiquote` argument is a mention in every KB from the
  first assert: held opaque to a `sameAs` or `equals` merge, followed by a `rewriteOf`
  rename, not reified on its own, and not typed by what it denotes. No statement turns
  that on or off, so a merge processed before a declaration can no longer fold a mention
  onto its referent. The `:quoting` prop kind goes with the predicate.
  `ensure-quasiquote-functions` asserts `(reifiable_function Quote)` and
  `(unreifiable_function Quasiquote)` only, and `(unreifiable_function Quasiquote)` is the
  gate that turns the quasiquote reducer on. `ExpressionKindProver`'s support no longer
  cites a quoting statement, so a forward firing reads a quoted form's kind only when a
  `genl` edge or a `natFormula` statement supports it.

  *Class:* **Breaking** (shipped vocabulary).
  *Migration:* delete any `(quoting_function X)` assertions. A KB that declared another
  function quoting must quote through `Quote` instead. `has-prop?` and `props` no longer
  take `:quoting`.
  *Breaks:* `quoting_function`, `:quoting`

- **`metal` renames to `metal_stuff`.** A stuff type's name is a mass noun, as
  `glass_stuff` is. "A metal" is a count noun, so a sentence such as `(disjoint metal
  mechanism)` seemed to be about kinds of metal. `abstract.txt` declares `metal_stuff`
  with the same comment, `genl` edges and `stuff_type_by_substance` membership,
  `mercury` sits below it, and CxNormalPhysicalConditions' solid-by-default rule reads
  `(metal_stuff ?x)`. No pair's disjointness changes.

  *Class:* **Breaking** (shipped ontology content).
  *Migration:* rename `metal` to `metal_stuff` in any KB text that names it.
  *Breaks:* `metal`

- **CxComputing and CxPerception merge into one opt-in context, CxTra.**
  `kb/middle/CxTra.txt` states every form the two files stated, with `(genlCx CxTra
  CxUniverse)`, so CxTra sees what each of the two saw and CxWell does not see CxTra.
  `core.txt` states `(context CxTra)` in place of the two `context` memberships, and
  `CxTra.txt` states a `comment` on CxTra. A context is a unit of visibility. Both theories were opt-in
  and CxWell saw neither, so one opt-in context holds both vocabularies. No relation,
  kind, rule or declaration changes.

  *Class:* **Breaking** (shipped ontology content).
  *Migration:* rename `CxComputing` and `CxPerception` to `CxTra` in any `genlCx` edge,
  `ist` or context argument that names them; a context placed under both needs one edge
  to CxTra.
  *Breaks:* `CxComputing`, `CxPerception`

- **The example predicates quote their example sentence.** The second argument of
  `positiveExample`, `negativeExample` and `borderlineExample` is a quoted sentence,
  `(positiveExample ip_address (Quote (ip_address "192.0.2.1")))`, and no longer a
  `(sentexHandle H)`. A KB text file can now state an example. The three are no longer
  `target_following_predicate`, since an example names no sentex. `curation_test` asks
  the quoted sentence in the example's own context. A `positiveExample`'s sentence must
  be provable there. A `negativeExample`'s must not be provable, and unknown is enough,
  where the KB used to have to prove its negation. A `borderlineExample` is not checked.

  *Class:* **Breaking** (shipped vocabulary).
  *Migration:* rewrite `(positiveExample T (sentexHandle H))` as `(positiveExample T
  (Quote S))`, S being the sentence H holds, and the same for the other two. An example
  is no longer torn down with the sentence it named. A `negativeExample` whose sentence
  the KB proves now fails the check.
  *Breaks:* `positiveExample`, `negativeExample`, `borderlineExample`

### Additions

- **38 shipped string examples become quoted-sentence examples that a test checks.**
  `core.txt`, `organism.txt`, `measure.txt` and `CxTra.txt` state 31
  `positiveExample` and 7 `negativeExample` facts in place of the
  `positiveExampleComment` and `negativeExampleComment` facts they replace, among them
  `(positiveExample folk_species (Quote (folk_species cat)))`, `(positiveExample
  sameQuantity (Quote (sameQuantity (QuantityFn 1000 Gram) (QuantityFn 1 Kilogram))))`
  and `(negativeExample character (Quote (character "a")))`. An example was converted
  only where the starter KB proves its sentence (a positive one) or does not prove it (a
  negative one) in the example's context; `curation_test` now checks every one. The
  reasons the five `relation_kind` negative examples gave move to a file comment above
  them.

  *Class:* **Additive** (shipped documentation; no sentence's truth changes).
  *Migration:* a reader that lists a term's examples by `positiveExampleComment` or
  `negativeExampleComment` reads `positiveExample` and `negativeExample` as well.

- **String examples that could be misread are reworded.** `CxTra.txt`'s tool
  examples name tools, not acts (`"a text-search tool"`, not `"a text search"`), and its
  MCP tool examples say MCP. A computational system's example is a running database
  server process, not the hardware. The `time_interval`, `uninterrupted`, `acausal` and
  `intangible` examples name particular intervals and times (`"the year 2024"`, `"the
  time 3 PM on 14 October 2024"`), not durations. `acausal_event`'s examples name acts
  (`"the receiving of a message"`), and `mechanism`'s says desktop computer.
  `reflection.txt` and `core.txt` mention their expressions as expressions: `"the symbol
  Muffet"`, `"the term (MotherFn Muffet)"`, `"a KB symbol"`.

  *Class:* **Additive** (shipped documentation; no sentence's truth changes).
  *Migration:* none.

- **`electronic_device` joins the made kinds, orthogonal to `machine`.**
  `abstract.txt` declares `electronic_device`, a mechanism built around an electronic
  circuit, with `(genl electronic_device made)` and `(genl electronic_device
  mechanism)`. The circuit and the parts that carry it make up the whole object, so an
  organism with an implanted circuit is not an electronic device. The type is rigid:
  what defines it is how a thing is built and not what the thing does. `(orthogonal
  electronic_device machine)`, `:monotonic`, states that the two types overlap and that
  neither is a genl of the other. A `comment` on that sentence names a witness for each
  of the three claims.

  *Class:* **Additive** (shipped ontology content).
  *Migration:* none. A KB that declares its own `electronic_device` term meets the
  shipped one.

- **`mechanism` is the common genl of `machine` and `electronic_device`.**
  `abstract.txt` declares `mechanism`, a physical object whose parts, in their
  arrangement, set up a characteristic causal operation, with `(genl mechanism
  tangible)`, `(genl machine mechanism)` and `(genl electronic_device mechanism)`. Most
  mechanisms are made but not all, so `mechanism` is not a genl of `made`: a juvenile
  Issus planthopper's hind-leg gears are a mechanism. The type is rigid: a stopped clock
  or an unplugged board is still one. The two kinds' shared separations
  are stated once on the parent: `(disjoint mechanism organism)` and `(disjoint
  mechanism substance)`, both `:monotonic`. `(disjoint animal machine)` is no longer
  stated; `animal` and `machine` stay disjoint through `mechanism` and `organism`.
  The disjointness coverage ratchet rises to 21,875 disjoint pairs (83.06%) and at most
  7.02% unknown.

  *Class:* **Additive** (shipped ontology content).
  *Migration:* a KB that asserts one term as both an `organism` (or a `substance`) and a
  `machine` or `electronic_device` now records a clash. A KB that reads the stated
  `(disjoint animal machine)` sentence finds the derived disjointness instead.

- **`wing` and `fur` are disjoint.** `abstract.txt` states `(disjoint wing fur)`,
  `:monotonic`. A bat's wing has fur on it, but the fur is part of the wing, and nothing
  is both. `wing`'s comment now names bats along with birds and insects.

  *Class:* **Additive** (shipped ontology content).
  *Migration:* a KB that asserts one term as both a `wing` and `fur` now records a clash.

- **The shipped comments state their examples as example facts.** 101 comments
  across `core.txt`, `abstract.txt`, `reflection.txt`, `life.txt`, `measure.txt`,
  `organism.txt`, `time.txt`, `CxTra.txt` and `CxSocial.txt` named examples of
  their own term. Each keeps its definition, and its examples are 227
  `positiveExampleComment` and 25 `negativeExampleComment` facts beside it, in the
  comment's own context. Nine comments keep an example that explains the definition and
  state it as a fact as well. The witness that a region of space is intangible and
  spatiotemporal is a `comment` on `(orthogonal intangible spatiotemporal)`.

  *Class:* **Additive** (shipped documentation; no sentence's truth changes).
  *Migration:* none. A reader of a comment's examples reads the example facts.

- **`machine`'s comment defines it by its parts.** A machine is a made thing with
  parts that move relative to each other, driven by an energy source. The comment names
  no use, so a stopped clock is still a machine. Its
  examples are `positiveExampleComment` facts.

  *Class:* **Additive** (shipped documentation; no sentence's truth changes).
  *Migration:* none.

- **The example predicates gain string siblings.** `core.txt` declares
  `positiveExampleComment`, `negativeExampleComment` and `borderlineExampleComment`:
  binary, the first argument the exemplified term and the second a `string` carrying
  the example as text. They name no sentex, so none is
  `target_following_predicate` and none carries a provability obligation. A KB text
  file has no spelling for a sentex handle, so a shipped file states its examples with
  these. Four `termsRelated` facts relate each sentex predicate to its sibling and the
  three siblings to each other. The vocabulary roster classifies the three `:inert`.

  *Class:* **Additive** (shipped ontology content).
  *Migration:* none.

## 0.27.0 — 2026-10-15 — "Arity clashes held inert and `:monotonic` class memberships stored, `predExistsAll` scoped universal-first, `:pg-snapshot` and `:recover? :trust`, `genlInverse` and `closedExtentForArg`"

| Area | Change |
|---|---|
| arity | a tuple breaking its functor's length inert at every context; `why-not`'s `:inert` with `:binding`; one `:arity` conflict per inert tuple; one CxUniverse `contradicts` per pair of exact-length bindings, with no `defeat`; a `:monotonic` metatype route stores `(C P)` under an `arityClass` justification |
| predall | `predExistsAll` puts the universal outside the existential; `PredExistsAllFn` at arity 4; `predExistsAllPlaceholder` at arity 5 |
| storage | `:pg-snapshot` over Postgres records; `p/ImageStamping`; `open-kb`'s `:recover? :trust`; `import!` installs a dump image written under other engine source; a dump's index replays in bounded heap; a remapped import merges collapsed meta-sentexes |
| inference | `genlInverse` through `tax/signed-closure`; `closedExtentForArg` and its binary spellings; a separated membership answers `(not (T x))`, and a fully denied cover is a `:cover` nogood; the node engine re-asks no goal; `argue` stops at a ground side's first answer; an interrupt stops a search |
| contexts and KB | `min-context-parents`, `max-context-children`; CxRealWorld under CxWell; `animal` disjoint from `building`, `clothing`, `furniture` and `machine`, and `:monotonic` from `vehicle` in CxRealWorld; `tool` retired; `(genl person tangible)` dropped; `registered_agent`; the shipped-context sync retracts only premises about shipped vocabulary |
| settle and daemon | a `{:chain? false}` batch chains nothing; a recover's mint re-draw, arity pairs, separations, trigger keys and stratification read once per sync; a daemon stop interrupts no write |
| browser | role colours; Clojure layout for meta-sentexes; comment markup; browsing history; `why-not`'s `:denies` rendered |

Three entries are **Breaking** and none is a **Refusal**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.26.0 caller changes.

| If your code… | Then |
|---|---|
| reads an arity clash from a placed `defeat` or a per-context `contradicts`, or relies on a `:monotonic` tuple that breaks its functor's length being believed | read `why-not`'s `:inert` or the `:arity` conflicts; restate the tuple at the bound length |
| counts an exact-arity class's members with `sentexes-with-functor`, or reads `why` of a class membership | keep the `premise?` handles where only the asserted memberships are wanted |
| states `predExistsAll`, or applies `PredExistsAllFn` or `predExistsAllPlaceholder` | read each declaration as "every `?indep` member has some `?dep` member bearing the predicate to it"; add the `?indep` member as the fourth argument of each application and placeholder fact |

### Breaking

- **A tuple that breaks its functor's length is inert, and an arity clash is no longer
  placed.** The settle holds such a tuple in the `:out` forced set at every context, at
  `:default` and `:monotonic` alike: it is stored, never believed and fires no rule. The
  length is read off the bindings and `genl` edges of every context, and an `except` of a
  binding or of an edge leaves it bound. `why-not` answers `:inert` with `:binding`, the
  length and the bindings stating it, and `conflicts` reports one `:arity` conflict per
  inert tuple. Two exact lengths of one relation, or of two relations a `genl` edge
  relates, are one `contradicts` stored in CxUniverse per pair of binding copies, with no
  `defeat` and no route. [taxonomy.md](docs/taxonomy.md#arity).

  *Migration:* read an arity clash from `why-not`'s `:inert` or from the `:arity` conflicts, not from a placed `defeat`.
  *Breaks:* `why-not`, `conflicts`, `believed?`

- **A `:monotonic` metatype route stores the exact-arity class membership it binds.** A
  membership `(T P)` stored at `:monotonic`, whose type reaches an exact-arity class `C`
  through `genl` edges IN at `:monotonic`, stores `(C P)` in CxUniverse under an
  `arityClass` justification whose antecedents are the membership and one path's edges.
  `why` of `(C P)` names them, and `(C P)` goes OUT when the membership or an edge leaves.
  `sentexes-with-functor` and the counts of the nine exact-arity classes include the
  derived memberships. Every moved `genl` edge syncs the memberships at or below its lower
  end, including an edge a `partition`, `covering` or `separating` declaration installs.
  The starter derives 208 such justifications, 31 of them on a class membership nothing
  asserts. [taxonomy.md](docs/taxonomy.md#arity).

  *Migration:* keep `premise?` handles where a read of an exact-arity class wants the asserted memberships only.
  *Breaks:* `sentexes-with-functor`, `why`

- **`predExistsAll` puts the universal outside the existential, and `PredExistsAllFn`
  takes the subject.** `(predExistsAll worksFor person company)` means that every company
  has at least one person who works for it: `predAllExists` with the predicate's argument
  positions swapped. The universal outscopes the existential in every cell of the family
  that quantifies both positions. `PredExistsAllFn` takes a fourth argument, the `?indep`
  member the filler bears the predicate to, as `PredAllExistsFn` does, so it is a
  `fixed_arity_function` of arity 4 with `(argArg PredExistsAllFn 4 3)`.
  `predExistsAllPlaceholder` takes that subject before the placeholder and has arity 5.
  [predall.md](docs/predall.md#exists-the-declaration-is-a-record-and-nothing-else).

  *Migration:* read each `predExistsAll` declaration as "every `?indep` member has some
  `?dep` member bearing the predicate to it", and restate one that meant a single filler
  for every member with a named individual and `predInstanceAll`. Add the `?indep` member
  as the fourth argument of each `PredExistsAllFn` application and as the fourth argument
  of each `predExistsAllPlaceholder` fact.
  *Breaks:* `predExistsAll`, `PredExistsAllFn`, `predExistsAllPlaceholder`

### Additive

- **`:pg-snapshot` keeps the index image and the reasoning image over Postgres records.**
  A record store stamps the images it may sit under through a new optional protocol,
  `p/ImageStamping` (`index-stamp`, `belief-stamp`); the `:disk` store answers off its slot
  files as before, and the `com.vaelii/postgres` adapter off one row a trigger moves with
  every write. `{:backend :pg-snapshot :pg … :dir …}` opens as `:disk-snapshot` does,
  installing both images from `:dir` instead of reindexing and recovering, and takes the
  directory's single-writer lock. An adapter without the protocol is refused at open with
  `:missing-adapter`. [storage.md](docs/storage.md#pg-snapshot-the-two-images-over-records-on-a-server).

- **`open-kb` takes `:recover? :trust`, and an import trusts a dump image written under
  other engine source.** `:trust` installs a reasoning image declined only for its engine
  source and keeps it: no rebuild runs, writes are accepted at once, and belief moves under
  the running build wherever a settle reaches. The close writes the session's writes into
  the image and keeps its source stamp, so the next `:trust` open installs it again, an
  `:auto` open still recovers it, and `recover` re-derives all of it on demand.
  `import!` with `{:belief? true}` now installs such a dump image instead of recovering,
  and its summary's `:reasoning-image` reads `{:reasoning :installed :trusted <source>}`.
  The browser opens with `:trust` under `VAELII_DEV`, in place of `:background`.
  [storage.md](docs/storage.md#the-reasoning-image).

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

  *Migration:* none. A KB that states `(genlInverse P Q)` now reads `P` facts as swapped
  `Q` facts.

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

- **`why-not` of an inert denial names the literal it denies and what puts it on the
  roster.** `:denies` carries the literal, its handle in the same context, whether that
  context believes it, and the roster predicate, kind and declarations. The browser's
  sentex page renders it. [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

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

  *Migration:* none. A context below CxWell reads `animal`/`vehicle` as separated by
  default, as before; a context placed under CxRealWorld reads the separation
  monotonic, and a context placed under CxNormalPhysicalConditions now also sees
  CxRealWorld's and CxWell's content.

- **CxUniverse separates `animal` from four made kinds.** `(disjoint animal building)`,
  `(disjoint animal clothing)`, `(disjoint animal furniture)` and `(disjoint animal
  machine)`, each `:monotonic`, join the made-kind separations in `abstract.txt`.
  `organization` and `animal` are separated by the tangible/intangible partition
  instead and needed no new fact.

  *Migration:* none. A term below `animal` and a term below one of the four made kinds
  were already `:unknown` or `:orthogonal` to each other; a KB stating an overlap
  between them now holds a disjointness nogood.

- **The browser colours terms by role, lays out meta-sentexes as Clojure does, marks up
  comments and keeps a browsing history.** Contexts draw blue, types pale amber,
  predicates yellow-orange, individuals violet and literals white, and ` in ` replaces
  ` @ ` before a context. A meta-sentex holding a rule aligns its arguments by column, as
  the editor's `pretty-sentence` does. A comment's text links formulas, variables, stored
  terms and `docs/` pages. A string argument sets in Atkinson Hyperlegible Next between
  Hasklig quotes, an OUT sentex dims its sentence and keeps its role colours, and a
  nested sentence dims by its own belief. The front page lists the last 50 terms,
  literals and rules opened, from `localStorage`. The core and starter cards drop the
  forward-chain option, which derived no new sentex over either. [web.md](docs/web.md).

### Fix: answers

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

  *Migration:* none. A KB holding a membership under a cover whose every part another of
  the term's memberships is separated from now holds a `:cover` nogood over them.

- **The shipped-context sync retracts only premises about the engine's own vocabulary.**
  A premise in CxUniverse or a `kb/middle/` context that the engine does not ship is
  retracted only when every term it names is one a shipped premise names
  (`sync/vocabulary`); a premise naming any other term is an author's, and stays. A KB
  whose corpus states its own declarations in CxUniverse lost them to the first writable
  load's sync. [contexts.md](docs/contexts.md#the-context-topology).

- **A `{:chain? false}` write chains nothing, alone or in a `with-deferred-settle` batch.**
  A rule's or exception's settle reads the write's own `:chain?`, as a fact's does. A
  batch's closing settle seeded chaining from every `genlCx` move the batch made, which a
  settle per write does not, so stored rules fired during a load that asked for none and
  each conclusion drew argument types. `bulk-assert-facts!` already suppressed this; every
  batch now does. [api.md](docs/api.md).

- **`core.txt` drops `(genl person tangible)`.** A person is not necessarily a massed
  body: a non-biological agent can be a person with no commitment either way on
  `tangible` or `intangible`. `person` roots to `thing` directly instead.
  `arity_vocabulary_test`'s clash witness read `person` for an ordinary non-relation
  type and relied on it being tangible; `animal`, already disjoint from `relation`
  through `tangible`, takes its place.

  *Migration:* a context that derived a term's `tangible` or `intangible` membership
  from a `person` membership alone derives neither now; state the one that holds
  directly.

- **`tool` is retired.** The ontology classifies by what a thing is, and `tool` named
  an artifact by what it is for. `abstract.txt` drops the type, its comment, its `genl`
  edge to `made` and `(disjoint building tool)`, and CxSocial drops `(disjoint dwelling
  tool)`. CxComputing's comment on `software_tool` no longer sets it against `tool`.
  `ontology_test` and `starter_test` drop it from the rosters that named the made kinds
  and the documented vocabulary, `social_test` from dwelling's disjoints, and
  `computing_test` its check that `software_tool` is not a `tool`.

  *Migration:* a KB that typed a term `tool` reads no membership for it; the type and
  every sentence naming it are gone.

- **koinii's registry mark renames from `agent` to `registered_agent`.** The name ties
  the mark to koinii's own registration rather than reading as a general-purpose agent
  classification. `CxRegistry.txt`, the two `vaelii.koinii.identity` functions reading
  and writing the mark, and `docs/koinii.md` move to the new name; `register-agent`,
  `registered-agents` and the rest of the identity API keep their names.
  `CxSpeechActs.txt` types its 12 actor positions `registered_agent`: argument 1 of the
  11 speech acts and argument 2 of `agentContext`.

  *Migration:* a caller reading or writing `(agent ?a)` in `CxRegistry` reads or writes
  `(registered_agent ?a)` instead.

### Fix: performance

- **Re-drawing a released term's mints checks only the mints that can change.** When a
  subsuming record leaves belief, the settle draws again the mints of every fact naming
  each term it released. A term's turn runs only while a record that released it is out:
  it reads its departures again and skips the term when all are stored as they were and
  believed. A departed `(T x)` can have withheld a mint `(t x)` only for `t` at or above
  `T`, so only those mints are re-drawn. A mint whose justification already holds, or that
  a believed record still withholds, skips the admissibility checks, and `rederive-mints`
  holds the checks' answers until a mint is created or brought IN. The settle after a
  recover's pair sync asked a released term's checks once per fact naming the term, where
  it now asks each distinct mint's checks once.

- **A recover's settles read the arity pairs, separations, trigger keys and
  stratification once per sync.** `arity/pair-sets` reads no closure for a predicate with
  one exact length at or above it, and shares one memo across a sync while no `genl` edge
  moves, in place of the bounded length entries. The pair sync's placed sets hold only a
  CxUniverse nogood whose antecedents are exactly its two members. The membership sync
  builds each type's separation frame once per sync and tests each pair once.
  `rules/trigger-keys` probes per closure term or passes over the rule roster, whichever
  side is smaller. `checks/edge-negation-cycle` stops at one reachability test for a
  `genl` edge the closure already holds. A recover asks each stored mint the withdrawal
  question instead of decoding every stored sentex, and asks a separated type's
  memberships only where a stored claim on the preserved predicate exists. Perf checks
  `arity-refresh-under-bound-chain`, `arity-pairs-below-a-queued-binding`,
  `recover-membership-sync`, `trigger-keys-beside-rules` and
  `edge-stratification-subsumed` pin the growth.

- **A `genlCx` edge settled under `*bulk-load?*` draws no argument types over the stored
  facts.** The settle that closes a bulk batch drained the batch's `genlCx` moves and drew
  what each move's declarations say about the facts below it, and each minted edge walked
  the stored rule graph, once per edge.
  `v/record-arg-types` records the derivations after the load.
  [argtypes.md](docs/argtypes.md#where-it-does-not-mint).

- **The node engine builds no child whose residual asks its own goal again.** A rewrite
  through an `intersection` rule, or any rule whose antecedent is the goal or a spec of
  it, no longer re-asks the goal one level down. On the starter, `(acausal ?x)` with one
  recursive rule expands 37 nodes at depth 4, where it did not finish depth 3, and
  `(intangible Foo1)` expands 9 at every depth. The `:stats` node counts of
  `query-status` and `search-tree` drop; the answers do not change.
  [inference.md](docs/inference.md#the-node-engine-vaeliiimplinference)
  ([#101](https://github.com/vaelii/vaelii/issues/101),
  [#182](https://github.com/vaelii/vaelii/issues/182)).

- **`argue` stops a ground side's search at its first answer, and an interrupt stops a
  node-engine search.** `argue` at a `:max-depth` returns once each ground side has an
  answer or has exhausted the bound. A `future-cancel` or `Thread.interrupt` on a running
  `query`, `query-status` or `argue` throws `InterruptedException` at the next node
  expansion. [inference.md](docs/inference.md#the-node-engine-vaeliiimplinference)
  ([#182](https://github.com/vaelii/vaelii/issues/182)).

### Fix: storage

- **A dump's index replays in bounded heap.** Replaying a `:records+index` dump held the
  head of the entry stream so its `finally` could close the file, so every installed
  entry stayed reachable and the replay's heap grew with the index, past the peak of
  rebuilding the same index. The replay, the snapshot index load, the
  provenance pass and the justification pre-scan now close through `frames/closer`, which
  holds the file and not the frames.

- **Stopping the daemon interrupts no KB write.** An op ran on the Jetty worker that read
  the request, and a server stop interrupts a busy worker, so a stop during a disk write
  latched the store `:store-unusable`. Each op now runs on a thread the server does not
  own. Stopping a daemon `serve/start` returned waits for the op in progress, answers
  parked long polls at once, and refuses the ops still queued with 503 `:stopping`.
  [operations.md](docs/operations.md#daemon--vaeliiserve).

- **A remapped import stores a meta-sentex once when two rules it names collapse.** The
  sentex pass collapses by the sentence as the dump spells it, so two dump rules that
  canonicalize to one left a copy of each meta-sentex naming each rule's dump id, and
  the handle rewrite turned the copies into one content stored twice. The rewrite now
  merges a record whose rewritten form an earlier record already holds, counts it in
  `:collapsed`, and points the merged record's dump ids at the survivor, so a
  justification or provenance entry naming it still resolves. Re-importing such a
  KB's export collapsed those copies and failed the equal-count check.

### Internal

- **`disjointness-coverage-ratchet` requires at least 21456 disjoint pairs, 82.91%
  disjoint and at most 7.07% unknown in the starter KB.** The bounds were 14211,
  70.70% and 19.87%. Retiring `tool` drops a type from the CxWell vantage sweep, and
  dropping `(genl person tangible)` removes pairs that edge separated; `animal`'s four
  new made-kind disjoints and `animal`/`vehicle` add pairs back. The starter KB now
  measures 21456 disjoint and 1829 unknown over 25878 pairs of 228 types.

- **CI shards the memory and disk legs eight ways each, from weights each green run
  refreshes, and `/rerun` reruns a pull request's failed jobs.** Each leg packs from its
  own column of `scripts/ci-test-weights-{memory,disk}.tsv`; every shard records its
  namespace times through `scripts/lib/ns-timings.sh`, and the weights job saves a green
  leg's times to the Actions cache. A comment reading exactly `/rerun`, from the pull
  request's author or a maintainer, reruns the failed jobs at its head commit
  (`rerun.yml`).

- **Gate, backend, sweep and shuffle logs live under `logs/`, and `lein test-matrix`
  re-reads its slot count while running.** The gate's run directories move to
  `logs/gate/`, the other runners' logs to `logs/`, and `test-full-kb`'s clone to
  `testbench/full-kb`, so a `lein clean` during a gate no longer deletes them.
  `runlog_prune` rotates the gate's and `test-backends`' run directories
  (`GATE_KEEP_RUNS` 40, `BACKENDS_KEEP_RUNS` 20). A matrix started without `--jobs` or
  `MATRIX_JOBS` re-reads the slot rule as each configuration ends and every
  `MATRIX_SLOTS_EVERY` seconds, counting only JVMs outside its own configurations.
  [operations.md](docs/operations.md).

- **`scripts/ontology-graph.py` draws the `genl` graph from the believed taxonomy.**
  `scripts/ontology-edges.clj` loads the upper ontology or the starter into an in-memory
  KB and prints `direct-genls` and `min-genls` for every spec of `thing`, so the drawing
  includes the edges a `partition`, `covering`, `separating` or `intersection` installs.
  The script keeps the dot layout that fills the most of a `--ratio`-shaped sheet.

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
