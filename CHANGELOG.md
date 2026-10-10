# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.24.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking

- **The expression lattice and the use/mention vocabulary move to a new upper member,
  CxReflection, and `atomic_formula`, `atomic_sentence` and `relation_application` are
  renamed.** `expression` is a written form in this KB's own language, the thing
  `(Quote …)` names, so it is disjoint from `relation`, `context` and `language`, which
  sit directly below `nowhere_never`. A natural-language sentence is `linguistic` but not
  an `expression`. CxReflection (`resources/kb/upper/CxReflection.txt`) holds 22
  expression kinds: `expression` is partitioned into `atomic_expression` and
  `non_atomic_expression`, which replaces `relation_application`; `atomic_expression`
  into `atomic_term` and `variable`; and `expression` again into `open_expression` and
  `closed_expression` and into `wff_expression` and `ill_formed_expression`.
  `atomic_formula` is `predication` and `atomic_sentence` is `closed_predication`, with
  `open_predication`, `negated_predication`, `open_literal`, `closed_literal`,
  `open_formula`, `wff`, `ill_formed`, `wff_sentence` and `ill_formed_sentence` beside
  them. `proposition`, `means`, `denotes` and `expresses` relate an expression to what it
  says or names. CxCore keeps `symbol`, the value kinds, `unrepresented_term`, `formula`,
  `sentence`, `non_atomic_term` and the new `linguistic`, which `language` and every
  expression sit under, so `symbol` and the value kinds are disjoint from `relation` from
  every context. `forall`, `thereExists` and `exists` are declared binary quantifiers, and
  `quantifier`, `logical_connective`, `logical_constant` and `sign_value` have closed
  extents. `bounded_arity` and `unbounded_arity` partition `relation`, the 14 relations
  that take any number of arguments are stated `unbounded_arity`, and `arityMax` bounds
  `functionCorrespondingPredicate` at 3. [contexts.md](docs/contexts.md),
  [naming.md](docs/naming.md#reserved-words), [taxonomy.md](docs/taxonomy.md).

  *Class:* **Breaking** (KB vocabulary renamed and moved).
  *Migration:* write `predication` for `atomic_formula`, `closed_predication` for
  `atomic_sentence` and `non_atomic_expression` for `relation_application`. A context that
  names an expression kind other than CxCore's sees CxReflection, as every context below
  CxUniverse does.
  *Breaks:* `atomic_formula`, `atomic_sentence`, `relation_application`

- **`at_least_binary_relation` and `at_least_ternary_relation` are renamed
  `at_least_binary` and `at_least_ternary`, and hold of fixed-arity relations too.**
  `binary` is below `at_least_binary` and `ternary` below `at_least_ternary`. Rules over
  `arity` conclude both beside the `arityMin` rules, and so reach the 5 shipped relations
  of arity 4 to 7, which no exact-arity class names. `(orthogonal at_least_binary fixed_arity)` is stated.
  `fixed_arity` and `variable_arity` partition `relation`, and `relation_type` is removed
  from CxAbstract. [taxonomy.md](docs/taxonomy.md#relations-and-arity-policy).

  *Class:* **Breaking** (KB vocabulary renamed and removed).
  *Migration:* write `at_least_binary` for `at_least_binary_relation` and
  `at_least_ternary` for `at_least_ternary_relation`; a query for one now also answers
  fixed-arity relations, e.g. `parentOf`. `relation_type` has no replacement.
  *Breaks:* `at_least_binary_relation`, `at_least_ternary_relation`, `relation_type`

- **`partitionedByType` is binary, `(partitionedByType ?whole ?classifier)`, and draws
  inference.** The members of `?classifier` partition `?whole`. A CxCore generator places
  each member under `?whole`, and a rule concludes `(disjoint_metatype ?classifier)`. No
  rule draws the coverage half (vaelii/vaelii#171), so the `partition` sentence stays
  beside each of the 4 shipped facts: `fixed_order_type` by `type_type_by_order`,
  `tangible` by `origin_type`, and `thing` by `spatiality_type` and by
  `temporality_type`. [glossary.md](docs/glossary.md).

  *Class:* **Breaking** (KB vocabulary arity changed).
  *Migration:* drop the cell list: write `(partitionedByType W C)` for
  `(partitionedByType W C A B …)`, and state each cell's membership `(C A)`.
  *Breaks:* `partitionedByType`

- **A variable inside `(Quote …)` or bound by a quantifier is not free, so a fact about a
  quoted rule stores.** `(awesome_rule (Quote (implies (poodle ?x) (dog ?x))))` was
  refused as `:not-ground`. `sentex/closed?` is new beside `sentex/ground?`: it is true
  when every variable occurrence is bound by `forall`, `thereExists` or `exists`, or sits
  inside a `(Quote …)`, and `check-ground` reads it. A written `(forall ?y (implies …))`
  asserted as a fact is now refused by the query-operator check rather than as
  `:not-ground`. [glossary.md](docs/glossary.md#g).

  *Class:* **Breaking** (a refusal changes type).
  *Migration:* a caller matching `:not-ground` on a quantified fact matches
  `:not-well-formed`.
  *Breaks:* `:not-ground`

- **`query-status` reads `:incomplete` when a transitive goal answered its extent.** A
  goal `(P ?x ?y)` over a `transitive` `P`, solved with both arguments open, answers the
  stored pairs and not the closure, and `query-status` reported `:complete` over it.
  `query-status` and `search-tree` now return `:unenumerated`, the predicates a search
  answered that way, and `query-status`'s `:status` is `:incomplete` when it is non-empty
  and the depth bound cut nothing. The inference debugger page names them above its
  answers. [inference.md](docs/inference.md#truncation-is-observable-corequery-status),
  [taxonomy.md](docs/taxonomy.md#predicate-metadata).

  *Class:* **Breaking** (a new `:status` value).
  *Migration:* a caller that dispatches on `query-status`'s `:status` handles
  `:incomplete`; to enumerate the closure, bind one argument per source term.
  *Breaks:* `query-status`

### Fixes

- **A new member of a closed part of a cover is admitted.** With every part of a
  `covering` declared `closed_extent_predicate`, the cover check asked of `(quantifier
  forall)` read `(not (quantifier forall))` off the closure's negation as failure, before
  the membership that withdraws it was stored, and refused the membership as a coverage
  violation. A part the membership puts its term in is now denied only by a stored
  negation. The starter then loads the same KB whether the closures arrive before or
  after the memberships.

  *Class:* **Fix**.

- **Two rule firings that pair the same facts with different literals are both stored.** A
  justification records the `[sub super]` predicate pairs its firing matched a fact to a
  literal through, as `:subsumptions`, and a route arriving later replaces only the
  firing with the same ones. Before, `(kind Xa)` and `(sort Xa)`, each reaching both
  literals of `(inspace ?x) ∧ (intime ?x)`, stored one of the two swapped firings, the
  one that arrived last, and a `genlCx` edge's round trip re-created it under a new id. A
  justification written by an earlier build has none, and is compared on its edges. The
  reasoning image's network section is at layout 5 and carries the subsumptions, so an
  image an earlier build wrote is declined once.
  [nmtms.md](docs/nmtms.md#where-the-layer-stops).

  *Class:* **Fix**.

- **`disjointness-audit` sweeps the types its vantage sees, not every type stored
  anywhere.** It read `relation?`, `disjoint?` and the `:orthogonal` witnesses from its
  `context` argument already, but swept `types kb` unscoped: every node of the global
  `genl` hierarchy, whatever context declared it. An opt-in theory's type raised the
  swept count — and, with no `disjoint` declaration reachable from the audit's vantage,
  could never be covered — so the coverage ratchet measured a KB no vantage actually
  sees as one. `types` takes an optional `context` now, reading only the nodes touched
  by an edge visible from it, the same visibility `genl?` and `disjoint?` already read
  with one; `disjointness-audit` sweeps `(types kb context)` instead of `(types kb)`,
  so the swept set and the coverage read over it are finally one vantage, not two.
  `disjointness-audit`'s default vantage moves from `CxUniverse` to `CxWell`, the
  starter spindle's collector: `CxUniverse` sees the upper ontology but not a starter
  middle member's own declarations (a middle member sees `CxUniverse`, not the reverse),
  so a type or a separation a middle theory states directly, never hoisted to
  `CxUniverse`, was invisible to the audit either way. `CxWell` sees every middle member
  below it and, through them, the whole upper ontology, and sees no opt-in theory — the
  exact boundary the ratchet means to hold. On the starter KB the swept set stays 200
  types over 19,900 pairs at both vantages; disjoint coverage is unchanged at 13,928
  pairs (69.99%) and unknown coverage improves from 4,089 to 4,085 pairs (20.53%), reading
  shared-instance and shared-subtype witnesses a starter middle member states that
  `CxUniverse`'s vantage could not see. `disjointness_audit_test` pins a type an opt-in
  context alone declares as outside the sweep at the default vantage and inside it at
  that context's own. [taxonomy.md](docs/taxonomy.md)

  *Class:* **Fix**.
  *Migration:* a caller reading `disjointness-audit kb` with no `context` reads the
  starter spindle's coverage instead of the upper ontology's; a caller already passing
  an explicit `context` is unaffected.

### Additions

- **`min-genls` and `max-specs` read a type's nearest neighbours in the subsumption
  order, and the term page's concept graph draws them.** `(min-genls kb t [context])`
  answers the direct parents of `t` with no other direct parent of `t` strictly below
  them, and `max-specs` the direct children with no other direct child strictly above
  them. Both read every believed edge of the closure, whatever installed the edge: a
  stated `genl`, a derived one such as an `intersection`'s, or a cover roster's. The
  daemon and `vaelii.client` serve both. The concept graph's `genl` rows draw these sets
  at every expanded node, where they drew `direct-genls` and `direct-specs`: with
  `dog ⊂ mammal ⊂ animal` believed and `(genl dog animal)` stated, the page for `dog`
  draws `animal` above `mammal` and no arrow from `dog` to `animal`. An expansion costs
  at most two facade reads, and a page makes at most twelve expansions.
  [api.md](docs/api.md), [web.md](docs/web.md#a-terms-shape-drawn).

  *Class:* **Additive**.

- **The upper ontology states `logical`, `quantitative`, `typeOrthogonal`,
  `orthogonalMetatypes` and `implementationNote`, and derives 43 genl, disjoint and
  orthogonal sentences it stated.** `(separating nowhere_never logical linguistic
  quantitative)` separates three kinds: `relation`, `proposition` and `context` are
  `logical`, and `measure`, `unit_of_measure`, `physical_dimension` and `sign_value` are
  `quantitative`. `(typeOrthogonal ?classifier ?type)` makes every member of a classifier
  orthogonal to `?type`, and `(orthogonalMetatypes ?m1 ?m2 …)` makes every member of each
  metatype orthogonal to every member of the others, for two and three metatypes
  (vaelii/vaelii#170). Each is a CxCore rule generator. The classifiers `arity_type`,
  `origin_type`, `spatiality_type` and `temporality_type` are new, and each classifier a
  rule reads is on the forced-monotonic roster. 10 `typeOrthogonal` facts and one
  `orthogonalMetatypes` fact derive 33 orthogonal pairs, 22 of them stated before, and
  every arity type is orthogonal to `abducible_predicate`. 9 more orthogonal pairs are
  stated, e.g. `made` and `vertebrate`, `animal` and `food`. `warm_blooded` is below
  `vertebrate` by default. `implementationNote` is a
  sibling of `comment` for how a term is implemented, and 14 CxCore terms carry one.
  [taxonomy.md](docs/taxonomy.md), [glossary.md](docs/glossary.md).

  *Class:* **Additive**.

- **`string`, `number`, `boolean`, `keyword` and `character` are computed for a literal
  argument.** `(string "foo")` and `(keyword :a)` hold, and `(not (number "foo"))` and
  `(not (string 7))` are proved, by the evaluable prover that answers `integer`. A symbol
  argument is left to the other provers, since a constant can denote a number.
  [inference.md](docs/inference.md).

  *Class:* **Additive**.

- **`try-assert` refuses a write that would open a definitional clash.** It is `assert`
  plus a refusal, `:definitional-clash`, for a sentence whose own clash or whose
  argument-type mints' clash with believed content `assert` would store and settle.
  Whether it refuses depends on arrival order. [api.md](docs/api.md#refusing-a-clash).

  *Class:* **Additive**.

- **CxSocial states the general relationship and dwelling vocabulary over two
  persons.** `relativeOf`, `coworkerOf` and `roommateOf` each specialize `knows`, the
  way `friendOf` and `marriedTo` already do; `romanticPartnerOf` specializes
  `friendOf`. `originatorOf` is read by a rule from `parentOf`, guarded to two
  persons, since the shipped `parentOf` relates any two organisms. `relationshipLabel`
  is a perspectival, ternary label. `dwelling` is a residential unit, genl `building`,
  and `dwellsIn`, a spec of `livesIn` restricted to a human and a dwelling, derives
  `roommateOf` by a rule for two different people who dwell in the same one. No edge
  relates `marriedTo` to `romanticPartnerOf`: this theory already reaches `knows`
  from `friendOf` and `marriedTo` by separate rules because it does not claim every
  marriage is a friendship, and the edge would carry `marriedTo`'s rule under
  `friendOf`'s and leave it covered. CxSocial states `dwelling` disjoint from
  `organism`, `substance` and `person` — a dwelling is a building, never alive,
  never a raw substance and never a person — which the disjointness audit, reading
  from CxWell, requires to hold its coverage ratchet. `social_test` pins the
  specialization edges, `dwelling`'s placement under `building` and its three
  disjointness facts, and both red-before-green derivations, `originatorOf` from
  `parentOf` and `roommateOf` from co-dwelling. [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none. CxSocial is a starter theory: every context below CxWell reads
  the new relations as declared here, as it already reads `knows`/`friendOf`/`marriedTo`.

- **CxSocialExtension states nestingPartnerOf and chosenSiblingOf, as a new
  opt-in theory below CxSocial.** `nestingPartnerOf` is read by a rule from
  CxSocial's `romanticPartnerOf` and `roommateOf` together; `chosenSiblingOf` is a
  sibling relation by choice rather than by birth, unrelated to the shipped
  `siblingOf` in either direction. Neither carries a `genl` edge to the CxSocial term
  its rule reads from: `romanticPartnerOf`, `roommateOf` and `relativeOf` are
  CxSocial's own middle-spindle terms, and a term two middle members touch must sit at
  or above the spindle's head
  (`starter_test`/`a-term-two-spindle-members-touch-is-defined-in-the-head`). The
  theory sees CxSocial, and through it CxUniverse, and CxWell does not see it: a
  context opts in by placing itself under CxSocialExtension. **`<Theory>Extension`
  names a theory that extends an existing starter theory with vocabulary most
  contexts under the base theory have no occasion to see**: the base theory ships
  to every context below CxWell, and the extension only to a context placed under
  it. `social_extension_test` pins the theory's visibility, both red-before-green
  derivations, and the absence of the carried `genl` edges.
  [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none. A context below CxWell reads none of this theory, as before. A
  context placed under CxSocialExtension reads `nestingPartnerOf` and
  `chosenSiblingOf` as declared there.

- **CxPerception states the perception relations, as an opt-in theory in
  `kb/middle/`.** `perceives` is the general relation an entity taking in a located
  thing through some sense; `sees`, a spec of it, is the same through sight; `seeImage`
  and `watchVideo`, each a spec of `sees`, take in a static image and a video. Arg 1 of
  each is typed `thing`: the upper ontology ships no general type for an entity with
  agency, and vaelii's `agent` names a registered koinii participant, not that. The new
  theory sees CxUniverse, and CxWell does not see it: a context opts in by placing
  itself under CxPerception. `perception_test` pins the specialization chain and the
  absence of every perception relation in a context that does not see the theory.
  [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none. A context below CxWell reads no perception relation, as before. A
  context placed under CxPerception reads `perceives`, `sees`, `seeImage` and
  `watchVideo` as declared there.

- **CxPerception states `image_viewing`, the ability to view a static image, as an
  event kind.** `hasCapability` takes an event kind as its second argument (#126), so
  the ability is read through it rather than through the retired `capability`:
  `(hasCapability ?x image_viewing)` means `?x` can be the doer of one.
  `(genl image_viewing acausal_event)` pairs it with `seeImage`, the relation stating
  who is looking: taking in an image changes nothing about what it depicts, so the
  event is a kind of `acausal_event`, CxAbstract's intersection of `acausal` and
  `event`. Stated in the theory itself, as every other perception relation is, so a
  context that does not see CxPerception derives no such capability class.
  `perception_test` pins the placement at the theory's own vantage, its absence at
  CxUniverse and CxAbstract, and the derivation of the ability's causal class under a
  context placed under the theory.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none.

- **`causes` ships in CxAbstract.** `(causes ?cause ?effect)` is a `binary_predicate` and
  an `instance_relation_predicate`, declared `transitive`. Its cause slot is typed
  `causal` and its effect slot `situation`, so a causal event, a tangible or an
  organization can be a cause, and an `acausal` thing in the cause slot draws a
  `causal` membership that clashes with it under `(disjoint causal acausal)`. The test
  world's Fox and Crow story types its three stated causes `Flatter1`, `CrowSings` and
  `CheeseFalls` as `causal_event`, and keeps its own `(arg causes 1 event)` and `(arg
  causes 2 event)` in CxStories. `causality_cluster_test` pins the declaration, a chain of
  causes, and the clash an acausal cause places.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB below CxAbstract that states `causes` with an `acausal` first
  argument, such as an `acausal_event`, holds a disjointness nogood there; type the cause
  as a `causal_event`, a tangible or an organization.

- **CxNormalPhysicalConditions states the states of matter of stuff at ordinary room
  temperature and pressure.** The new theory in `kb/middle/` sees CxUniverse, and CxWell
  does not see it: a context opts in by placing itself under CxNormalPhysicalConditions, so
  the everyday contexts below CxWell assume no temperature. It places `stone`, `wood` and `glass_stuff` under `solid` and
  `mercury` under `liquid` with four `genl` edges. A metal is solid there by default:
  `(exceptWhen (mercury ?x) (set/defaultRule (set/forwardRule (implies (and (metal ?x))
  (solid ?x)))))`, so a metal the KB says nothing more about is concluded solid at
  `:default`, and the rule concludes nothing for a portion of mercury. CxAbstract declares
  `mercury`, a first-order `type` below `metal`, with its comment. The upper ontology states
  no state of matter for any substance, so a context that does not see the theory concludes
  none. `normal_physical_conditions_test` pins the solids, the default, the mercury
  exception with no clash in a user context placed under the theory, and the absence of
  every state in CxWell and in every other context that does not see the theory;
  `seed_test` pins the eight files in `kb/middle/`.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none. A context below CxWell reads no state of matter, as before. A
  context placed under CxNormalPhysicalConditions reads its stone, wood, glass and metal
  solid and its mercury liquid, and a state it states otherwise for one of them is a
  disjointness nogood under `stuff_type_by_state_of_matter`.

- **CxComputing states ten relations over software tools, their invocations and receipts,
  media resources and DNS names, and the sixteen kinds they are typed over.** The new
  theory in `kb/middle/` sees CxUniverse, and CxWell does not see it: a context opts in
  by placing itself under CxComputing. It declares seven binary predicates (`toolName`,
  `invokesTool`, `resourceUrl`, `receipt`, `probesPredicate`, `dnsResolvesTo`,
  `agentHasTool`) and three ternary predicates (`toolInvocationArg`, `toolArgType`,
  `toolArgComment`), each with its comment and its `arg` and `quotedArg` declarations,
  and `(functional toolName)`. CxComputing states no rule. It states the sixteen kinds
  itself, each with its comment: `computational_system` below `intangible`, with
  `software_tool`, `command_line_tool`, `mcp_tool`, `read_only_software_tool` (also below
  `acausal`) and `write_capable_software_tool` (also below `causal`) under it;
  `information_bearing_thing` below `intangible` and `acausal`, with `digital_artifact`,
  `media_resource`, `image` and `video` under it; `tool_invocation` below `event`;
  `tool_receipt` below `acausal_event`; and `ip_address` below `string`, partitioned into
  `ipv4_address` and `ipv6_address`. It states four `disjoint` sentences at default
  strength: `computational_system` against `event` and against `expression`, `image`
  against `video`, and `tool_receipt` against `tool_invocation`. `software_tool` has no
  edge to `tool`, which is a tangible made thing. CxUniverse states
  `(context CxComputing)` beside the other shipped contexts and states no relation and
  no kind of the theory, so `disjointness-audit` at its default vantage, CxWell, sweeps
  none of the sixteen kinds.
  Position 1 of `agentHasTool` and position 3 of `toolArgType` declare no type and are
  rows of `ontology_test`'s untyped-positions roster. `computing_test` pins the wiring,
  the placements and separations of the kinds as a context under the theory reads them,
  the type each `arg` declaration derives there, the absence of every relation
  declaration and every kind's placement in a context that does not see the theory, and
  the `check` convictions under the constraint-only reading; `seed_test` lists the theory
  among the files in `kb/middle/`. [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none. A context below CxWell reads no computing relation and no computing
  kind. A context placed under CxComputing reads the ten relations and the sixteen kinds
  as declared there. `(functional toolName)` is a decontextualized mark, so every context
  that sees CxUniverse reads that mark.

- **CxCore states `(predAllSpecified typeGenl at_least_metatype)` and
  `(predAllSpecified genl unary_predicate)`.** Every `at_least_metatype` is required to
  name, through `typeGenl`, a type its instances specialize, and every `unary_predicate`
  to name a `genl`. `all-specified-violations` and `kb-integrity` audit both requirements.
  CxCore states `(typeGenl sibling_disjoint thing)`, matching
  `(genlArg sibling_disjoint 1 thing)`. `empty` and `nonempty` are `at_least_metatype`
  with no other type to specialize, so CxCore states `(typeGenl empty thing)` and
  `(typeGenl nonempty thing)` beside their declaration; both facts are vacuous, since
  `thing` is already a `genl` of every type, and inert, since `typeGenl` has no
  inference path. Over the starter, the `genl` audit is clean and the `typeGenl` audit
  reports `folk_species` and `folk_biological_class`, the two metatypes that state no
  `typeGenl`.

  *Class:* **Additive**.

### Fixes: order independence

- **A defeat of a permuting mark below a fact's context moves no class at that context.**
  The sorted spelling stored beside a fact whose readers disagree on its mark took the
  weaker of the fact's class and the mark's, so a known-true `(swRel Bea Ada)` under a
  default `(symmetric swRel)` read `:default` above a denial of the mark, and tied a
  default `(not (swRel Ada Bea))` there. The spelling now holds at the fact's class, as
  with no denial, and so does a firing over it. A reader below the denial decides its
  nogoods with that spelling out of belief.
  [canonicalization.md](docs/canonicalization.md#a-mark-a-reader-does-not-believe),
  [nmtms.md](docs/nmtms.md#why-a-read-runs-no-rounds).

  *Class:* **Fix**.

- **A fact a late permuting mark moves onto the spelling of a stored negation clashes
  with it.** A `(symmetric swRel)` asserted after `(swRel Bea Ada)` and `(not (swRel Ada
  Bea))` re-spelled the fact in place and placed no nogood, so both stayed believed where
  the other arrival orders placed the clash.
  [canonicalization.md](docs/canonicalization.md).

  *Class:* **Fix**.

### Fixes: performance

- **Retracting a fact from a determinant re-places only its own tuple nogoods.** In
  0.24.0 each `(contradicts …)` placement leaving with the fact queued its surviving
  partner, so retracting one `:default` filler beside n clashing fillers of a
  `functional` subject re-placed all n(n-1)/2 nogoods of the group: 632 ms at n=100,
  3.2 s at n=200. It now reads 22–24 ms at both sizes, and `lein perf`'s
  `filler-beside-clashing-fillers` holds it.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

  *Class:* **Fix**.

### Internal

- **`disjointness-coverage-ratchet` requires at least 13928 disjoint pairs, 69.98%
  disjoint and at most 20.55% unknown in the starter KB.** The bounds were 13762, 69.85%
  and 20.66%. The starter KB that ships `causes` and CxNormalPhysicalConditions measures
  13928 disjoint and 4089 unknown over 19900 pairs of 200 types.

  *Class:* **Internal**.

- **A test pins the defeat-dependency cycle whose first defeat is out of force at a
  reader.** With the first defeat's ground excepted at a reader below the cycle, that
  reader reads the second defeat in force, and a reader that sees no except reads the
  content-order answer, in all 120 arrival orders.
  [nmtms.md](docs/nmtms.md#a-defeat-dependency-cycle).

  *Class:* **Internal**.

## 0.24.0 — 2026-10-07 — "Reified `contradicts` and `defeat` sentexes synced to KB, upper ontology improvements and more disjointness, indexing improvements"

| Area | Change |
|---|---|
| nogoods | new meta-sentexes `contradicts` (a nogood over `sentexHandle`s) and `defeat` (removes the named handle from belief), placed at the most general contexts that see the members and grounds; a belief read walks the stored `except`s and `defeat`s; an asserted `defeat` is refused `:derived-only` |
| argument types | `arg`, `genlArg`, `interArg` and the covering and homogeneity constraints derive the type they name and refuse no sentence on a membership |
| taxonomy | `orthogonal`: two types overlap and neither is a `genl` of the other; `siblingDisjointException` is the only separation-mark exemption |
| inheritance | `transitiveInArg` and `transitiveInArgInverse` swap names to match Cyc's `transitiveViaArg` / `transitiveViaArgInverse` |
| strength | a roster literal keeps its written strength; a reading inherited over a `:default` reason is `:default` |
| storage | index layout 10: argument roots, predicate extent and rule indexes keyed by context, five families added; reasoning image `format-version` 11 holds nothing the index holds |
| KB | `thing` divided by space, time and mass; `living_thing` renamed `organism`; events take doer, inputs and outputs |
| new API | `open-kb :oplog?`, `kb-integrity`, `relation?`, `direct-genls`, `direct-specs`, `separating-covers` |

Eight entries are **Breaking** and one is a **Refusal**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.23.0 caller changes.

| If your code… | Then |
|---|---|
| reads `sentexes-matching` or `preview` and expects stated content only | filter out `contradicts` and `defeat` |
| reads `belief-status`'s `:scoped-vantages` | read the vantages off `why-not`'s `:defeats` |
| calls `genl?`, `isa?`, `genls`, `specs` or `disjoint?` with no context for a context's belief | pass that context |
| states `transitiveInArg` or `transitiveInArgInverse` | swap the two names |
| catches `:arg-type`, `:arg-genl` or `:inter-arg-type` on a symbol argument | read `contradictions` and `conflicts`, or set `VAELII_ASSERTIVE_ARG_TYPES=0`; run `record-arg-types` once on an older store |
| writes a roster literal, a `transitiveInArg` declaration or a `genl` edge `:default` and needs its derivations known-true | write it `{:strength :monotonic}` |
| writes `(orthogonal a b)` to exempt a pair from a separation mark | write `(siblingDisjointException a b)` |
| sums `caches`' `:literal-matches` hits as a process total | sum the row over every KB |
| implements `IndexStore` out of tree | implement the context arities of `lookup`, `sentexes-with-args` and `rules-by-consequent`, and the context argument of `index-rule` and `unindex-rule!` |
| opens a durable index or imports a dump written by 0.23.0 | nothing: the first open or import rebuilds the index from the records |
| opens a `:disk-snapshot` image written by 0.23.0 | nothing: the first open recovers in full once and writes a new image |
| asserts a `(defeat …)` sentence | retract it before upgrading, and rewrite a rule over one on a predicate of its own |

### Breaking

- **A nogood is stored as a `contradicts` sentex, with the `defeat` of its loser, where
  its members and grounds are seen whole, and no reader decides a clash at read time.**
  CxCore declares `contradicts` a variable-arity predicate over sentex handles,
  `(contradicts (sentexHandle ?h1) (sentexHandle ?h2) …)`, with no argument type, and
  `defeat`, a meta-sentex the engine derives that removes the handle it names, and what
  rests only on that handle, from belief at every context that sees it. The settle stores
  a nogood's `contradicts`, and the `defeat` of a unique weakest member, at the most
  general contexts that see the members and the grounds where no `except` hides one,
  justified by them. It places the nogood again when a member, a ground or a `genlCx`
  edge moves the placement, and removes a placement whose nogood no longer holds; a
  `genlCx` edge places again only the nogoods whose placement it can move. A
  nogood whose members are all `:monotonic` stores no `defeat`. `recover` places the
  standing nogoods of a store written with no belief, a records-only import among them,
  in its closing settle, before the first write. Every family places its nogoods this
  way:

  - **negation:** a `P` and a `(not P)`, at the maximal common descendants of their
    contexts;
  - **membership and related types:** two memberships under a separation, a membership
    under a cover beside a denial of each part, a `disjoint` over two related types, a
    cover beside a `disjoint` separating a part from its whole, and a contradicted
    `orthogonal`, grounded on the separating or covering declarations and the `genl`
    edges they climb. A reader whose `siblingDisjointException` exempts every separation
    that convicts the nogood does not believe the placement;
  - **tuples:** a self tuple, a converse pair, a chain and two tuples agreeing on a
    determinant under `irreflexive`, `anti_symmetric`, `asymmetric`, `anti_transitive`,
    `functional` or `functionalInArg`, grounded on the mark and the predicate `genl`
    edges up to it. A reader reads only the marks it believes, and two symbol fillers it
    reads as one equality class convict nothing;
  - **arity:** a tuple whose length breaks a binding of its functor or of a predicate
    above it, grounded on the binding, and two related predicates bound to different
    lengths. A reader reads only the bindings it believes. An arity clash placed through
    a `genl` edge an argument declaration minted names that declaration under
    `:grounds`;
  - **inherited:** a stored denial of a known-true claim reached by argument
    preservation, at the most general contexts that read the clash whole;
  - **guards:** a firing whose `exceptWhen` or `unknown` guard holds below its placement
    and not at it stores `(defeat (sentexHandle F))` of its conclusion at the common
    descendants of the placement and the blocker, justified by the blocker, the rule,
    the firing's antecedents, F and the `genl` edges the guard climbed. A reader that
    sees it believes F only through a premise or a justification no guard blocks there,
    and retracting the blocker takes the defeat OUT. The blocker is found by the forward
    join over the guard's conjuncts, so a prover answer names the facts it read. Where an
    `except`, or a placed defeat of a `:default` ground, takes the blocker's own defeat
    out of force below the placement, the guard defeat is placed there and rests on it.
    A guard defeat removes no answer a backward rule expansion produces.

  A belief read is the read walk over the asked handle's support, reading the stored
  `except`s and `defeat`s, and no state is kept per reader. A `defeat` two nogoods share
  stays in force through either one. A firing's placement and its witness search read the
  network and the `except` roster and no `defeat`, so a placed defeat of a `genl` edge
  moves no firing, and a reader that reaches a firing's path ends over edges it does not
  hide reads the firing with nothing stored for it. `genl?`, `isa?`, `genls`, `specs` and
  `disjoint?` given a context do not cross an edge a `defeat` or `except` they see hides,
  or an edge whose support rests on such a handle; given no context, they, `has-prop?`
  and `inverse-of` read an edge or a declaration at its network label, and an equality
  no context believes still decides the merge. `conflicts` and `contradictions` read the stored `contradicts`:
  `:vantages` names the placement contexts that defeated different members, and
  `(contradictions kb context)` reads only the `contradicts` stated where `context`
  sees. A nogood whose member an equality merge supersedes keeps its placement in every
  arrival order of the merge; neither read reports a `contradicts` naming the superseded
  spelling, and the restated spellings' `contradicts` reports that clash. Of two placed
  defeats that rest on each other, the one whose loser is first in content order is in
  force, in every arrival order and every read
  ([nmtms.md](docs/nmtms.md#a-defeat-dependency-cycle)). `belief-status` drops
  `:scoped-vantages`. `why-not` names a defeat under
  `:defeats` or `:withdrawn-by`, the pair's other member under `:contradicted-by` and the
  nogood's grounds under `:grounds`. `sentexes-matching` answers the placed sentexes,
  and `preview` and `edit-with-consequences` count them as belief added. Each of these
  holds in every arrival order.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion),
  [naf.md](docs/naf.md#evaluated-in-the-placement-context-not-the-join).

  *Class:* **Breaking**.
  *Migration:* filter `contradicts` and `defeat` out of a `sentexes-matching` or
  `preview` read that expects stated content only; read the vantages off `why-not`'s
  `:defeats`, each a `defeat` handle whose `sentex`'s `:context` is the vantage; pass the
  context whose belief a `genl` closure read is about. A KB that states `contradicts`
  names the members by `(sentexHandle h)`. The first open after the upgrade recovers the
  store and writes a new image.
  *Breaks:* `sentexes-matching`, `preview`, `why-not`, `belief-status`, `describe`
  *Breaks:* `contradictions`, `conflicts`, `assert`
  *Breaks:* `genl?`, `isa?`, `genls`, `specs`, `disjoint?`, `has-prop?`, `inverse-of`,
  `:disk-snapshot`

- **`transitiveInArg` and `transitiveInArgInverse` swap names, so `transitiveInArg` takes
  the direction of Cyc's `transitiveViaArg`.** `(transitiveInArg P n R)` now carries a
  stored `(P … W …)` along `R`'s arrow: `(R W A)` gives `(P … A …)`, which with `genl`
  is upward, to a supertype. `(transitiveInArgInverse P n R)` carries it against the
  arrow: `(R A W)` gives `(P … A …)`, which with `genl` is downward, to a subtype. Before
  this change each name carried the other direction. The argument order stays `(P n R)`
  (Cyc writes `(P R n)`). The engine implements the same two walks it did; only the
  functor naming each walk changed, and every declaration the shipped KB and the test
  suite state was rewritten to the other name, so each one still licenses what it did:
  `(transitiveInArg largerThan 1 genl)` is now `(transitiveInArgInverse largerThan 1
  genl)`. [inherit.md](docs/inherit.md), [from-cyc.md](docs/from-cyc.md).

  *Class:* **Breaking** (a stored declaration under either name now licenses the
  opposite direction).
  *Migration:* swap every `transitiveInArg` and `transitiveInArgInverse` in your KB: the
  names now carry the directions Cyc's `transitiveViaArg` / `transitiveViaArgInverse`
  do.
  *Breaks:* `transitiveInArg`, `transitiveInArgInverse`

- **An argument constraint derives the type it names and refuses no sentence on a
  membership.** Under the default entailing reading, `arg`, `genlArg`, `interArg`, the
  covering `args` / `argAndRest` / `argsGenl` / `argAndRestGenl` and the homogeneity
  `interArgs` / `interArgAndRest` derive their type over every symbol argument, from a
  declaration written in the asserting context or inherited by it, and a `genlCx` edge
  arriving last derives over the facts it makes the declaration visible to. A membership
  the declared type does not reach is not evidence against the sentence, and a derived
  type disjoint from one the term holds is a placed clash. Two facts that derive one
  membership are both stored in either order, and re-asserting a stored membership
  stores it. A value or an application whose function's `result` misses is still
  refused, and `VAELII_ASSERTIVE_ARG_TYPES=0` keeps the constraint-only reading. A
  premise retracted while a derivation still holds it up is withdrawn when a believed
  membership says it more specifically, as a derivation is. `record-arg-types` records
  the derivations of a store loaded without them (a dump import, a `*bulk-load?*` load,
  `bulk-assert-facts!`), so the store holds what loading the same facts one by one holds;
  a second run records nothing, an operation log records it as a write, and the daemon
  does not serve it. [argtypes.md](docs/argtypes.md#an-argument-constraint-only-adds-support),
  [operations.md](docs/operations.md).

  *Class:* **Breaking** (`assert` and `check` admit what they refused, and a KB stores
  memberships an inherited declaration derives).
  *Migration:* where a caller caught `:arg-type`, `:arg-genl` or `:inter-arg-type` for a
  symbol argument, read `(contradictions kb)` and `(conflicts kb)` for the clash a derived
  type forms, or run under `VAELII_ASSERTIVE_ARG_TYPES=0` for the constraint reading. A
  store written before holds no derivation an inherited declaration draws: run
  `record-arg-types` once on it.
  *Breaks:* `assert`, `check`, `check-edit`, `abduce`, `:arg-type`, `:arg-genl`,
  `:inter-arg-type`

- **A literal keeps the strength it was written at, and an inherited reading over a
  `:default` reason is `:default` and opposes nothing.** A forced-monotonic roster
  literal (a relation mark, a definitional declaration, an arity binding, a predicate
  `genl`, an `except`, an equation) written `:default` reads `:default` and confers it on
  what is derived from it: a fact preserved through a `:default` predicate `genl`, a fact
  moved under a `:default` `rewriteOf` and a firing of CxCore's `injection` rules from a
  `:default` declaration are `:default`. A roster member is never the loser of a nogood,
  so a nogood with no defeasible member off the roster is a hard clash. The roster is
  every literal a nogood family reads among its grounds, beside `genlCx`, `except`,
  `rewriteOf`, `sameAs`, `equals`, `injection`, `surjection` and `bijection`, on every KB
  whether or not it loads CxCore. A `genlCx` edge alone is still read `:monotonic`, so
  it caps no firing's class. `transitiveInArg` leaves the roster: a declaration is
  weighed as a member of an inherited nogood, and a denial of one is believed. A claim
  reached by argument preservation is `:monotonic` only when the general claim and every
  reason it rests on are, the `transitiveInArg` declaration and the `genl` edges
  included; a reading over a `:default` reason is undercut as a `:default` claim is, so
  no inherited clash forms and the stored denial is believed. The shipped `transitiveInArg`
  declarations of `largerThan`, `partType` and `capabilityType` are written `:monotonic`.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster),
  [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).

  *Class:* **Breaking** (`defeat-class` of a roster literal written `:default`, and of
  what is derived from it, reads `:default`; `has-prop?` and `props` answer the new
  roster for `:forced-monotonic`).
  *Migration:* write `{:strength :monotonic}` on a roster literal, a `transitiveInArg`
  declaration or a `genl` edge whose derivations must stay known-true.
  *Breaks:* `defeat-class`, `has-prop?`, `props`, `ask`, `believed?`
  *Breaks:* `conflicts`, `contradictions`

- **`orthogonal` states that two types are not disjoint and neither is a `genl` of the
  other, and only `siblingDisjointException` exempts a pair from the separation marks.**
  CxCore declares `(orthogonal A B)` a symmetric binary `type_relation_predicate` on the
  forced-monotonic roster beside `disjoint`. It derives nothing, mints no shared instance
  and exempts nothing. A `disjoint` over the pair or over a supertype of each, a
  `sibling_disjoint` parent, a `disjoint_metatype`, a `partition` or `separating` roster
  that separates the pair at a reader, a `genl` edge between the two, or one type named
  twice is a one-member clash of the declaration, `:kind :orthogonal`, in every arrival
  order. `conflicts` lists it with the separating declarations under `:grounds`, and its
  retraction from the roster is refused with `:unforced-definitional-declaration`.
  `(siblingDisjointException a b)` exempts the pair from the marks (a `sibling_disjoint`
  parent, a `disjoint_metatype`, a `partition` or `separating` roster), pair-local and
  read at the reader; a stated `disjoint` of the pair beside the exception is a clash of
  the exception. CxCore states `(genl siblingDisjointException orthogonal)`, so a stored
  exception answers `(orthogonal a b)` to `ask` and `match` and is read as the orthogonal
  it entails. `subsumption-statuses` reads a stated `orthogonal` as `:orthogonal` with no
  shared instance, reads `disjoint?` at its vantage `context` (default `CxUniverse`), and
  reports a pair that is also separated or `genl`-related `:inconsistent`.
  `disjointness-audit` sweeps types only: it leaves out a node of arity two or more or
  declared `variable_arity`, and `:types` counts the nodes swept. A `genl` edge or a
  separation declaration reads again only the `orthogonal`s it can contradict.
  [taxonomy.md](docs/taxonomy.md#disjointness),
  [nmtms.md](docs/nmtms.md#declarations-over-related-types).

  *Class:* **Breaking** (an `orthogonal` over a pair a separation holds apart is a clash
  of the declaration; a pair separated only in a context below the vantage reads
  `:unknown` at the vantage).
  *Migration:* write `(siblingDisjointException a b)` where `(orthogonal a b)` was written
  to exempt the pair from a mark; where a `disjoint` and an `orthogonal` of one pair are
  both stated, drop whichever is wrong; pass the context that states a separation as
  `subsumption-statuses`' `context`.
  *Breaks:* `orthogonal`, `disjoint?`, `subsumption-status`, `subsumption-statuses`
  *Breaks:* `disjointness-audit`, `conflicts`

- **`caches` counts the literal cache per KB, counts the closure answers in members, and
  reports each counted row's recompute time and retirements.** The `:literal-matches`
  row reads `:counters :kb`, and its hits are this KB's alone. The rows of the taxonomy
  closures, the visibility sets, the closure answers and the resident values gain
  `:hits`, `:misses`, `:recompute-ns`, `:retired`, `:compared`, `:spurious` and
  `:evicted`, and the closure row `:builds` and `:fallbacks`. The `:closure-answers` row
  counts members, the unit its bound counts, and a clear reports the members it dropped.
  `clear-caches` with `{:counters? true}` zeroes this KB's tallies and lists them under
  `:tallies-reset`. The source-parse cache offers a clear and the visibility sets a trim,
  so `clear-caches` and the memory guard reach them.
  [caches.md](docs/caches.md#counting-the-register).

  *Class:* **Breaking** (the `:literal-matches` row's `:counters` reads `:kb`, and its
  `:hits` and `:misses` count one KB).
  *Migration:* sum the `:literal-matches` rows of every KB for the process total.
  *Breaks:* `caches`, `clear-caches`

- **The index is at layout 10: the argument roots, the predicate extent and the rule
  indexes end in the context, so a scoped read reads only the contexts its reader sees,
  and five families join the index.** The argument roots are a count trie over
  `[pred pos term ctx]`, the predicate extent replaces the functor root as a count trie
  over `[pred ctx]`, and the two rule indexes are count tries over `[key ctx]`.
  `sentexes-with-args` and `rules-by-consequent` take the reader's contexts, `lookup`
  takes a set of contexts and keeps its path's last level to it, and `index-rule` /
  `unindex-rule!` take the rule's context. A context-scoped read, a read led by two
  ground arguments at a ground or a variable context, a match in a ground context, a
  backward rule candidate and the check for a defeat a reader sees fetch no record
  stated where the reader cannot see. A read whose matches sit mostly where the reader
  cannot see reads the argument roots instead of walking the stored values under the
  prefix. The families that join the index:

  - the rule extent `[:rule-extent :count|:children|:handles …]`, a count trie over
    `[kind ctx]`, and the antecedent trie's root level `[:rule-antecedent-keys]`
    ([indexing.md](docs/indexing.md#3-the-rule-index));
  - the bodies stored in both polarities, a count trie `[:opposed …]` over `[body ctx]`
    with its root level `[:opposed-bodies]` and the members by context `[:opposed-in ctx]`
    ([indexing.md](docs/indexing.md#the-bodies-stored-in-both-polarities));
  - the taxonomy's supporters, a count trie `[:tax-support …]` over `[k ctx]` keyed by the
    edge or declaration each one installs, and `[:tax-installs h]`; a cover is listed under
    each `genl` edge it installs
    ([indexing.md](docs/indexing.md#9-the-taxonomys-supporter-families));
  - the mints, a count trie `[:mint …]` over `[term ctx]` with its root level
    `[:mint-terms]`, and `[:mint-in …]` over `[ctx]`
    ([indexing.md](docs/indexing.md#10-the-mint-family));
  - the shape roster `[:shape-count f n]` and `[:shape-lengths f]`, the terms of two unary
    predicates `[:unary-multi]`, and the ground binary self tuples, a count trie
    `[:self-tuple …]` over `[pred ctx]`
    ([indexing.md](docs/indexing.md#the-shape-roster)).

  A count trie's leaf key cites its context's scope, and a `:disk-snapshot` index image
  is written at snapshot format 4. A stored index, a `:disk-snapshot` image or a dump of
  an earlier layout is rebuilt from the records at its first open or import, and
  `reindex` posts every family from the stored records and justifications. Answers are
  unchanged. [indexing.md](docs/indexing.md#by-context-reads).

  *Class:* **Breaking** (a stored index or a `:disk-snapshot` image of layout 3 is rebuilt
  from the records at its first open, a dump of layout 3 reindexes on import, and an
  out-of-tree `IndexStore` implements the new `lookup`, `sentexes-with-args` and
  `rules-by-consequent` arities and the context argument of `index-rule` and
  `unindex-rule!`).
  *Migration:* reindex: the first open rebuilds a durable index; implement the read
  arities with a context set, or nil for every context, and post a rule under its context.
  *Breaks:* `lookup`, `sentexes-with-args`, `rules-by-consequent`, `index-rule`,
  `unindex-rule!`, `index-entries`, `:disk-log`, `:disk-snapshot`

- **A reasoning image is at `format-version` 11 and carries nothing the index holds; an
  image an earlier build wrote is declined once.** The image no longer carries the
  except, defeat and rule rosters, the mint roster, the opposed bodies, the
  argument-preservation roster, the nogood candidates (the negation candidates, and the
  stored declarations, self tuples and tuple shapes the other families read), the
  taxonomy's context census or its supporter maps: each is read from the index. A
  `:disk-snapshot` image an earlier build wrote is declined at open, the KB recovers in
  full once, and the next close writes an image of the new layout.
  [storage.md](docs/storage.md#the-reasoning-image).

  *Class:* **Breaking** (a `:disk-snapshot` image of an earlier build is recovered in full
  once, at its first open).
  *Migration:* none; the first open after the upgrade recovers the store and writes a new
  image.
  *Breaks:* `:disk-snapshot`

### Refusals

- **A `defeat` literal is refused `:derived-only` in every asserted sentence.** `(defeat
  (sentexHandle H))`, its negation, a rule reading or concluding one and an `exceptWhen`
  query naming one are refused by `assert` and predicted by `check`, a bulk load included.
  Matching and asking `(defeat ?h)` are reads and stay allowed.
  [glossary.md](docs/glossary.md#d), [troubleshooting.md](docs/troubleshooting.md#i-have-a-type-and-do-not-know-what-it-means).

  *Class:* **Refusal** (a `(defeat …)` sentence was stored as an ordinary fact).
  *Migration:* retract an asserted `(defeat …)` fact before upgrading; a rule over one
  is rewritten over a predicate of its own.
  *Breaks:* `assert`, `check`

### Additions

- **`open-kb` attaches an operation log with `:oplog?`, and an open after a crash
  restores from the last seal.** `{:backend :disk-snapshot :oplog? true}` logs every
  outermost public write, fsyncing its frame before the write runs (`:tick` leaves the
  frame to the durability daemon's tick). An open of a directory holding a seal installs
  the seal's two images and replays the operations logged after it, and rebuilds from the
  records only when the restore declines, logging which path ran and why. `seal` takes a
  seal on the caller's cadence and returns the generation, the watermark and the time
  taken. A log whose append or fsync fails refuses that write and every later one with
  `:store-unusable`. Any other backend, and a `:recover?` other than `:auto`, is refused
  with `:unknown-option`. [storage.md](docs/storage.md#the-operation-log),
  [operations.md](docs/operations.md#after-a-crash).

  *Class:* **Additive**.

- **`kb-integrity` runs a bounded, read-only integrity sweep in a context, and the daemon
  serves it.** Over a finite set of ground candidate terms the sweep reports, by
  default, eight categories:

  - `:definition-inconsistencies`: a passing `defnSufficient` beside a failing own
    `defnNecessary`;
  - the visible `predAllSpecified` / `predSpecifiedAll` declarations
    `all-specified-violations` reports;
  - `:genl-arg-widening`: a predicate `genl` edge whose spec declares an argument type no
    type the genl's constraint demands there subsumes;
  - `:not-under-thing`: a candidate `unary_predicate` with no `genl` path to `thing`;
  - `:implicit-genl`: a `genl` edge a `covering` or `partition` forces and the closure
    misses;
  - `:orthogonal-over-separation`: an `orthogonal` or `siblingDisjointException` over a
    pair a separation divides, both sides named by handle;
  - `:rule-macro`: a believed premise rule that states what a declaration the engine
    implements states (`transitiveInArg`, `transitiveInArgInverse`, `symmetric`,
    `transitive`, `commutativeInArgs`, `inverse`, `genl`, `predAllInstance`,
    `predInstanceAll`), as `{:rule h :sentence S :context C :macro M :declaration D}`, with
    `:stated true` when the rule's context already sees the declaration. A
    `set/defaultRule` of a monotonic declaration's shape is reported with
    `:default-shaped true` unless the KB holds a claim the default yields to, and CxCore's
    `(declined_rule_macro D)` records a reviewed suggestion the pass then leaves out;
  - `:undeclared-arity`: a node of a visible `genl` edge for which the audit context sees
    no arity and no `variable_arity` membership.

  Four review-only passes run only when `:categories` names them, so a review finding
  never turns an otherwise clean sweep into `:gap`: `:twin-genls` (two or more visible
  types sharing one direct `genl` set besides `thing`), `:derivable-stated-edge` (a stated
  `genl` or `disjoint` that derives without itself), `:disjoint-could-be-partition` (a
  stated `disjoint` a known cover or a parent's sole two specs exhausts) and
  `:missing-arg` (a declared argument position no `arg`, `genlArg`, `quotedArg`, rest or
  `args` form types). A clean sweep answers `{:status :audited :candidate-count n}`, a
  sweep with findings `:status :gap` with only the non-empty categories, and a sweep that
  runs out of `:max-work`, `:max-ms` or `:max-results` `:status :truncated` with its
  `:reason` and the findings kept, the same ones in every arrival order. A candidate set
  that is not a set of ground terms is refused with `:op kb-integrity`. The sweep stores
  nothing and files no violation: it binds `vaelii.impl.violations/*report-sink*`, so the
  ledger does not move. The daemon serves it as `:kb-integrity` under its three ceilings
  (`:max-work` 10,000, `:max-results` 1,000 and the query clock), refuses a bound over a
  ceiling `:over-ceiling` and a call that sends only the candidate set `:bad-args`, and
  `vaelii.client` gains `kb-integrity`. [integrity.md](docs/integrity.md),
  [operations.md](docs/operations.md).

  *Class:* **Additive**.

- **`relation?`, `direct-genls`, `direct-specs` and `separating-covers` read the
  hierarchy's structure, and the daemon and `vaelii.client` serve all four.**
  `(relation? kb term [context])` answers whether a term is a relation of two or more
  places by its stored arity or a `variable_arity` membership; `describe`,
  `disjointness-audit`, `kb-quality` and the browser read a `genl` node's kind through it.
  `(direct-genls kb t [context])` answers the types `t` is a subtype of by one edge, and
  `direct-specs` the types one edge below `t`; an edge counts whatever installed it, so a
  part a `covering`, `separating` or `partition` roster names is a direct subtype of the
  roster's whole. `(separating-covers kb)` answers the believed `separating` and
  `partition` rosters as `[whole parts kind]`, the table `disjoint?` reads. The browser's
  taxonomy view and hierarchy tree draw from `direct-genls` and `direct-specs`, and its
  front-page disjointness list from `separating-covers`.
  [api.md](docs/api.md), [taxonomy.md](docs/taxonomy.md#disjointness), [web.md](docs/web.md).

  *Class:* **Additive**.

- **`subsumption-statuses` and `disjointness-audit` read a shared subtype as an overlap
  witness.** A pair neither subsuming the other nor disjoint, with a type below both
  that is not separated from itself, reads `:orthogonal` with no shared instance stated.
  A type below two separated types, or one with a known `(empty c)`, is no witness, so a
  pair whose only shared subtypes are empty stays `:unknown`. `disjointness-audit` marks
  each `:orthogonal` entry with `:witness` (`:declared`, `:shared-instance`,
  `:shared-spec`, or `:unwitnessed-spec` for a shared subtype with no known
  `(nonempty c)`) and, for the last three, `:via`, the instance or subtype found: a
  nonempty subtype first, then the content-least, in every assertion order. On the
  starter KB this moves pairs such as `animal` and `person` (through `human`) and
  `injection` and `surjection` (through `bijection`) from `:unknown` to `:orthogonal`.
  [taxonomy.md](docs/taxonomy.md#auditing-the-hierarchy-for-missing-disjointness).

  *Class:* **Additive** (an `:unknown` pair gains a status, and audit entries gain two
  keys).

- **`qualitative-network` names the unsatisfiable metric or point network behind an
  unsatisfiable interval network, and no longer blames the interval pair it empties.**
  `:unsatisfiable-sources` holds one map per source,
  `{:source :metric :pairs [[P Q] …] :cycle [P Q …] :support [handle …]}` (`:point`
  carries no `:cycle`): the source's pairs unsatisfiable as written, the instants on a
  negative cycle, and the handles of the facts behind them. The
  `:qualitative-inconsistency` ledger entry carries the same maps as `:sources`, and the
  browser's network view lists them. `:unsatisfiable` and the entry's `:pairs` leave out
  the interval pair such a source empties, which they named as unsatisfiable as written
  though no interval fact contradicts it. [qcn.md](docs/qcn.md), [stp.md](docs/stp.md).

  *Class:* **Additive** (and a Fix to `:unsatisfiable` and `:pairs`).

- **The upper ontology divides `thing` by location in space, by time and by mass, and
  `tangible` by whether a living thing's action shaped it; `physical_object` is renamed
  `tangible`, `abstract` `nowhere_never`, `artifact` `made`, and the old `spatial`
  `spatiotemporal`.**

  - **Three partitions of `thing`.** `(partition thing spatial aspatial)`,
    `(partition thing temporal atemporal)` and `(partition thing tangible intangible)`
    state separation and coverage both, so a thing denied one part is concluded the
    other. `spatial` is a location in any space, mathematical spaces included (the line
    y=x, a square of an abstract chessboard), and `spatiotemporal`, below `spatial` and
    `temporal`, is a location in space and time. Every CxSpace argument is declared at
    `spatial`, so RCC-8, direction and distance relate regions of the Cartesian plane as
    readily as fields. `tangible` is something with mass, below `spatiotemporal`;
    `intangible` is something with no mass, and `(disjoint intangible spatial)` is dropped
    so that a region can be spatiotemporal and intangible at once. `nowhere_never` (an
    expression, a language) is below `aspatial` and `atemporal`, both below `intangible`.
    `fluent`, `organization`, `quantity` and `relation_type` are below `aspatial`, and
    CxCore places `context` and `language` below `nowhere_never`. CxCore states seven
    `set/monotonic` `orthogonal`s across the three axes, each with a witness (a rock, the
    line y=x, a fluent, a region of space).
  - **`made` and `natural` partition `tangible`.** `made` is a tangible shaped by an
    agent's action or by something made (a chair, steel, sawdust, a footprint, a beaver's
    dam, a cloned sheep), and `building`'s parent `container`, `clothing`, `furniture`,
    `machine`, `tool` and `vehicle` are kinds of it. `natural` is a tangible whose form no
    living thing's action gave it (a wild sheep, a coral reef, a river). `formation`, a
    natural tangible neither grown nor made (a rock, a crystal, a dune), is kept from
    `biological` by `(separating tangible formation biological)`. An `orthogonal` is not
    inherited along `genl`, so CxAbstract states `biological` orthogonal to `made` and to
    `natural`, and eleven more pairs across the two: `organism` and `body_part` each with
    `made` and `natural`, `substance` with `made`, `natural` and `formation`, and `food`
    with `made`, `natural`, `biological` and `formation`. The monotonic `(disjoint
    substance artifact)` is removed, since steel is a made substance.
  - **Causality.** `(genl tangible causal)` and `(genl organization causal)` make a rock
    and a company causal, and the monotonic `(disjoint causal acausal)` then separates
    every tangible kind from `acausal` and `acausal_event`. `acausal`'s comment names a
    time, a property line, an attribute and the information a record carries, not the
    record, which is tangible.
  - **Time.** CxAbstract declares `time`, a moment or a stretch of time as such, with
    `(genl time acausal)`, and CxCore states `(genl time temporal)`, `(genl time
    aspatial)`, `(partition time time_point time_interval)` and `(disjoint time
    situation)`, so CxTime reads its calendar results and moments as times. `YearFn`,
    `MonthFn` and `DayFn` declare `(result … time_interval)` where they declared
    `temporal`. CxTime declares `DatetimeFn`, the ISO-string spelling of a calendar
    interval, places `functional_at_instant` under `function` and `initially` under
    `fluent`, and CxUniverse states `(termsRelated time_interval Duration)`.
  - **Situations and expressions.** `(partition situation static_situation event)` adds
    coverage, so a situation denied being an event is a `static_situation`. CxCore holds
    the partition and `(genl situation temporal)`, so CxLife's `genlArg` of `event` on
    `capabilityType` and `hasCapability` reads `event` below `thing`. CxCore also holds
    `expression` and `unrepresented_term`, moved from CxAbstract with the edges that place
    `context`, `relation`, `formula`, `relation_application`, `denotational_term` and the
    value kinds below them, so CxCore and every band context read each of these kinds
    below `thing` and each value kind as disjoint from `predicate`.
  - **Removed.** CxAbstract does not declare `attribute`; no shipped type replaces it.
    Every stated `genl` or `disjoint` that a partition, a `genl` chain, a
    `disjoint_metatype` or another disjointness already derives in the same context is
    removed across CxCore, CxAbstract, CxMeasure, CxTime and CxUniverse, among them the
    eight `genl` edges to `thing` and `nowhere_never` the `expression` chain derives;
    `ontology_test`'s `derivable-and-unstated` table lists each.

  On the starter KB at the close of this release, `disjointness-audit` sweeps 199 types
  and 19,701 pairs: 13,762 `:disjoint`, 170 `:orthogonal` and 4,069 `:unknown`.
  `ontology_test`, `causality_cluster_test` and `starter_test` pin each change.
  [taxonomy.md](docs/taxonomy.md#the-three-partitions-of-thing), [space.md](docs/space.md),
  [time.md](docs/time.md), [glossary.md](docs/glossary.md).

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* rename `physical_object` to `tangible`, `abstract` to `nowhere_never` and
  `artifact` to `made`; each old spelling stores clean but attaches to nothing in the
  taxonomy, so its instance reaches nothing above it. A KB that wrote `spatial` for
  "located in the world" renames to `spatiotemporal`; the old spelling places the thing in
  the broader collection, where nothing concludes it has a location in the world. A KB
  that wrote `(attribute X)` declares its own type, such as `(genl attribute aspatial)`,
  in a context that sees CxAbstract. A KB that stated an instance of a tangible kind
  `acausal` now holds a clash. A KB that read `(result YearFn temporal)` or its two twins
  as stated reads `time_interval`. A KB that relied on a substance and a made thing
  clashing states that separation over narrower kinds of its own. A KB that relied on a
  removed sentence being stated, rather than derived, reads it from `disjoint?` or `genl?`.
  *Breaks:* `physical_object`, `spatial`, `abstract`, `artifact`, `attribute`,
  `(disjoint substance artifact)`

- **`living_thing` is renamed `organism`, kinship and age relate organisms, `biological`
  is an organism or a part of one, and the organisms carry a folk taxonomy.**

  - **Organisms.** `organism` names something alive in its own right, and every shipped
    use is renamed, with no `rewriteOf` alias. `parentOf`, `childOf`, `siblingOf`,
    `ancestorOf`, `grandparentOf`, `birthYearOf` and `olderThan` declare `organism` where
    they declared `animal`, so the kinship and age rules read on a tree's parent as on a
    dog's; `fatherOf`, `motherOf`, `FatherFn`, `MotherFn` and the behaviour predicates stay
    `animal`. `biological`, held in CxCore, is a tangible that is an organism or part of
    one, and `(separating biological organism body_part)` keeps an organism and a part it
    grew apart. `(disjoint biological substance)` replaces `(disjoint organism substance)`
    and `(disjoint substance body_part)`. `(orthogonal food body_part)` replaces the
    monotonic `(disjoint food body_part)`, since a chicken wing is both, and `(orthogonal
    biological made)` replaces `(disjoint organism artifact)`. `animal` and `plant` are
    separated by one `(separating organism animal plant)` roster in CxOrganism.
  - **The biology properties.** CxLife places `alive` and `dead` under `biological`, with
    a `biological` argument, so a dead leaf is no organism; `mortal` under `organism`; and
    `asleep`, `awake`, `breathes_air` and `warm_blooded` under `animal`.
  - **Folk taxonomy.** CxOrganism states `(partition animal vertebrate invertebrate)` and
    places the five vertebrate classes, `insect` and `arachnid` below the two parts.
    `invertebrate_class` and `plant_class` are `disjoint_metatype`s beside
    `vertebrate_class`, and `(separating folk_biological_class vertebrate_class
    invertebrate_class plant_class)` keeps the three apart. `folk_species` is a
    `disjoint_metatype` over the 27 shipped species, disjoint from
    `folk_biological_class`, and on the forced-monotonic roster with each membership
    written `:monotonic`, so a denial of one is held OUT. The disjointness audit leaves no
    unknown pair among the kinds below `organism`.

  `ontology_test` and `common_sense_test` pin each change.
  [contexts.md](docs/contexts.md), [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* rename `living_thing` to `organism`; the old spelling stores clean but
  attaches to nothing in the taxonomy. A KB that relied on a kinship or age fact refusing
  a plant states that narrower type of its own. A KB that needs `food` and `body_part`, or
  an organism and a made thing, kept apart states the separation over narrower kinds of
  its own, such as `(disjoint animal tool)`. A KB that stated one organism of two shipped
  species, or an insect that is a mammal, now reads a clash.
  *Breaks:* `living_thing`, `(disjoint organism artifact)`

- **Events name their doer, their inputs and their outputs, and an ability is an event
  kind.** CxAbstract declares binary `instance_relation_predicate`s that take the event
  first: `doneBy` (the doer brought the event about) and its spec `performedBy` (it did so
  intentionally), with no type on the doer, since a machine can bring an event about;
  `input`, with the specs `destroyedInput` and `preservedInput`; and `output`, with the
  specs `tangibleOutput` and `intangibleOutput`. A tangible output of an event something
  `performedBy`, or that a made thing `doneBy`, is concluded `made`; a calf its mother grew
  is not. In CxChange and below, each relation places the thing's start or end against
  its event's on the point network, so an order that contradicts one is a
  `:qualitative-inconsistency` under `:point`. `capability` is retired:
  `(hasCapability ?animal ?eventKind)` and `capabilityType` take an event kind, with
  `(genlArg … 2 event)`. `travelling` and `flying` move from CxLife to CxUniverse, below
  `causal_event`; bird flight, the penguin exception and `(hasCapability ?x travelling)`
  answer as before. `causality_cluster_test`, `input_output_timing_test` and
  `ontology_test` pin each of these. [time.md](docs/time.md), [inherit.md](docs/inherit.md).

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* type ability arguments as event kinds. A KB that placed its own ability
  under `capability`, as `(genl swimming capability)`, writes `(genl swimming event)` in a
  context that sees CxAbstract, such as CxUniverse. A KB that relied on an ability kind
  being `aspatial` states that placement itself.
  *Breaks:* `capability`

- **CxCore divides the relations and the unary predicates, and declares and types the
  vocabulary the engine reads by name.**

  - **Relations.** `(partition relation function truth_valued_relation)`,
    `(partition truth_valued_relation logical_constant predicate)` and
    `(partition logical_constant quantifier logical_connective)`, after Cyc's
    `TruthFunction`, so `function`, `predicate`, `quantifier` and `logical_connective` are
    pairwise disjoint. `and`, `or`, `not` and `implies` are `logical_connective`s, with
    `(unary not)`, `(binary implies)` and `(variable_arity …)` for `and` and `or`, where
    `(unary_predicate not)` and `(binary_predicate implies)` were stated; the arity readers
    read 1 for `not` and 2 for `implies` as before. `(genl function relation)`, `(genl
    predicate relation)` and `(disjoint function predicate)` are derived, no longer
    stated. `(partition function reifiable_function unreifiable_function)` separates the
    two minting marks, and `(intersection equivalence_relation reflexive symmetric
    transitive)` concludes `equivalence_relation` of a predicate carrying all three marks.
  - **Unary predicates and metatypes.** `(partition unary_predicate fixed_order_type
    variable_order_type)`, so a metatype is never of variable order; `at_least_metatype`
    is a `variable_order_type` member, not a subtype, with `(genl at_least_metatype
    unary_predicate)`. `empty` and `nonempty` partition `unary_predicate`: `(empty t)` says
    `t` has no instance in the context the sentence is stated in.
    `(transitiveInArgInverse empty 1 genl)` carries `empty` down to subtypes and
    `(transitiveInArg nonempty 1 genl)` carries `nonempty` up, read at query time, and a
    forward rule concludes `empty` of a `unary` type below two types a stated or inherited
    `disjoint` separates. CxCore declares an arity for each of the 52 types it places under
    `thing` (`unary_predicate`, `type` or `variable_order_type`), places five predicate
    marks under `predicate` and `sibling_disjoint` under `unary_predicate`, and states
    `(genl partition covering)` and `(genl partition separating)`, so a stated partition
    answers a `covering` or `separating` query.
  - **Integers.** `(partition integer positive_integer non_positive_integer)` and
    `(partition integer negative_integer non_negative_integer)` replace the four
    `(genl … integer)` edges; zero is in both `non_` types.
  - **Vocabulary the engine reads by name.** CxCore declares `argN`, a `ternary_predicate`
    that nothing in the engine derives or reads; `different`, a `variable_arity_predicate`
    with `(arityMin different 2)` and `(commutative different)`, whose assert is still
    refused; comments and `binary_predicate` for `sameAs` and `equals`, which type neither
    position, as `rewriteOf` does not; and comments for `set/forwardOnlyRule`,
    `set/solveRule`, `set/assumptionRule`, `set/hardConstraint`, `set/softConstraint` and
    `set/monotonic`. `forced_monotonic_between_predicates` types its position `predicate`,
    `intersection` types its third and later positions with `(argAndRestGenl intersection 3
    thing)`, and `functionCorrespondingPredicate` its optional third with `(argAndRest …
    3 positive_integer)`. The query operators `unknown`, `thereExists`, `forall`,
    `bravely` and `cautiously` stay undeclared.

  `ontology_test`, `engine_vocabulary_test` and `arity_vocabulary_test` pin each change.
  [argtypes.md](docs/argtypes.md), [equality.md](docs/equality.md),
  [taxonomy.md](docs/taxonomy.md).

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a query that found `not` among the `unary_predicate`s or `predicate`s, or
  `implies` among the `binary_predicate`s, asks `logical_connective` instead, or `unary` /
  `binary` for the arity; a KB that states `(predicate not)` now contradicts the
  partition. Code that unasserts `(genl function relation)`, `(genl predicate relation)`,
  `(disjoint function predicate)` or a `(genl … integer)` edge, or reads one as a stated
  sentence, finds it derived instead. A KB that declared one function both
  `reifiable_function` and `unreifiable_function` now reads a clash.
  *Breaks:* `(unary_predicate not)`, `(binary_predicate implies)`,
  `(genl function relation)`, `(genl predicate relation)`, `(disjoint function predicate)`

- **No shipped argument declaration names `thing`, and the starter proves the same
  sentences under the constraint-only reading as under the entailing one.** 53
  declarations that named `thing` name a type, and four types are added for them:
  `unit_of_measure`, `physical_dimension` and `quantity` in CxMeasure, and `measure` in
  CxCore, which `QuantityFn` and `QuantityIntervalFn` declare as their result.
  `(dimensionOf Kilogram Mass)` derives `(unit_of_measure Kilogram)` and
  `(physical_dimension Mass)` and no `(thing Kilogram)`. A number position
  (`birthYearOf`, `trustLevel`, `conversionFactor`, `lessThan`, `greaterThan`,
  `evaluate`'s result) refuses a value of another kind with `:arg-type`, as a measure
  position refuses a number. The 18 slots that hold a term of any kind, `comment`'s first
  argument among them, declare no type, so the entailing reading derives no `(thing X)`
  from one; `ontology_test` holds that roster. CxUniverse states each shipped context's
  `context` membership, CxCore holds the `genl` edge of the seven band types a second band
  context declares an argument over, CxTime defines `fluent`, `and` and `or` have
  variable arity, and `partitionedByType` has variable arity of at least
  3. [quantity.md](docs/quantity.md), [sign.md](docs/sign.md),
  [argtypes.md](docs/argtypes.md#constraint-and-entailment-readings).

  *Class:* **Additive** (shipped ontology content).

- **`lein lint` and the script aliases run on Windows, under Git for Windows' bash, and
  `VAELII_BASH` picks the bash.** The aliases find Git's bash beside `git.exe` on `PATH`
  and in per-user and Scoop installs, the tree scans compare paths spelled with `/`, and a
  test over a `:disk-snapshot` KB prints SKIP there. `VAELII_BASH` names the bash every
  script alias runs, and the `:test` profile hands it on as `vaelii.test.bash`.
  [operations.md](docs/operations.md).

  *Class:* **Additive** (developer tooling and two configuration names).

### Fixes: answers

- **`check` reads a reifiable application in a quoting predicate's payload as a mention.**
  `check` reads a ground application of a reifiable function as the constant `assert`
  mints, and in `(termOfUnit K (AwakeFn Whiskers))` it typed the payload by the function's
  `result`, so a stored `termOfUnit` read `:disjoint` once that result was separated from
  `non_atomic_term`. `assert` never typed the payload, and `check` now agrees with it.
  [nat.md](docs/nat.md).

  *Class:* **Fix**.

- **A `greaterThan` goal matches the stored `lessThan` fact it folds onto, and so does a
  goal on a predicate `greaterThan` is a spec of.** `(ask? kb '(greaterThan A B) ctx)`
  answered false beside a stored `(lessThan B A)`: the default set-algebra retrieval read
  the goal's functor and argument order, where the reference fan-out folds the goal
  first. Such a literal takes the reference fan-out.
  [indexing.md](docs/indexing.md#retrieval-from-the-roots-resmatch-one).

  *Class:* **Fix**.

- **A fact of another functor shaped like a cover no longer pairs with a `disjoint` as a
  `:cover` conflict.** The related-types candidates read any stored fact of three or more
  symbols as a cover, so `(liesAmong alpha beta gamma)` beside `(disjoint alpha beta)` was
  placed as a `contradicts` of the two. Only a `covering`, `separating` or `partition`
  fact is a cover. [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion).

  *Class:* **Fix**.

- **A scoped `genls`, `specs`, `genl?`, `isa?` or ancestor-set read follows what hides an
  edge at the reader.** A derived `genl` edge resting on a fact a `defeat` or `except` the
  reader sees hides is not crossed: the closures tested only whether an edge's own
  supporter was a target, so the edge stayed crossed where `believed?` of it answered
  false, and they now read whether a supporter rests on a target, through its forward
  consequence closure or its support, whichever is smaller. A justification added to or
  dropped from a `genl` or `genlCx` edge a defeat or except hides retires the scoped
  closures that cross the edge, under the belief reading and the network reading; the
  edge stayed network IN, so a closure read before such a write answered after it.
  `taxonomy_belief_test` holds the derived edge in every fifth of 24 arrival orders, with
  and without `recover`. [nmtms.md](docs/nmtms.md#a-read-with-no-reader).

  *Class:* **Fix**.

- **`describe` describes a relation that a `genl` edge makes a node of the hierarchy as a
  predicate, and the browser colours it as one.** `orthogonal`,
  `siblingDisjointException`, `relationTypeByArity`, `predicateTypeByArity` and
  `functionTypeByArity` answered `:role :type`, without `:arity`, `:props`, `:inverse` or
  the grants, and the term page coloured them as types. The role is read from the stored
  arity at the asking context, never from the spelling; a unary or undeclared node stays
  a type. `disjointness-audit` reads the relation's arity at its vantage `context` rather
  than from every context. [api.md](docs/api.md),
  [taxonomy.md](docs/taxonomy.md#disjointness).

  *Class:* **Fix**.

- **An inherited clash is placed in the context that reads it whole when an `except`
  hides one of its readings higher up, in every arrival order.** A reading stated below
  the stored claim was dropped as covered by a more general one, so where an except hid
  the general reading, the context reading the covered one was never asked and believed
  the denial. A clash whose reason an except hides at the stored claim's context, and a
  meta-except shows again below, was not placed either, and the lower context believed
  the claim, the reason and the denial together. Both are placed, and retracting the
  except takes the clash OUT.
  [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).

  *Class:* **Fix**.

- **A write's report names a consequence of a conflict member that a reader's excepts
  decide, and a `with-deferred-settle` batch reports against the belief before its first
  write.** Storing or retracting an except that lowers a member of a placed `contradicts`
  with no `defeat`, or retracting the other member, moved the belief of what rests on
  the lowered member at a context below, and no event, `preview` or
  `edit-with-consequences` report named it. An except asserted inside a
  `with-deferred-settle` batch moved belief when it was stored, and the batch's settle
  read the belief before it after that move, so the event left out what the except
  revived. [nmtms.md](docs/nmtms.md#the-published-window).

  *Class:* **Fix**.

- **A `symmetric`, commutative or `reifiable_function` mark a context does not believe
  spells nothing that context reads.** A context that sees a `defeat` or an `except` of
  every statement of the mark reads a fact on its predicate as written: the mirror and the
  sorted spelling answer false there, and a reified use, its constant and the constant's
  result types are not read. A context the defeat does not reach reads the fold and the
  constant as before. Where the readers of one fact disagree, the store holds the written
  spelling beside the sorted or reified one, which rests on the mark, and each is read
  where its reader's belief admits it. `has-prop?` of `:symmetric` or `:commutative` with
  a context answers whether that context believes a statement. `perf`'s
  `permuting-mark-defeat-flip` holds a defeat's cost flat in the facts under other marks.
  [canonicalization.md](docs/canonicalization.md#a-mark-a-reader-does-not-believe),
  [nat.md](docs/nat.md#a-reifiable-mark-moving).

  *Class:* **Fix**.

- **A `reifiable_function` declaration reaches the applications stored before it, and its
  leaving reaches the constants minted under it** (vaelii#100). A ground `(F a)` asserted
  before `(reifiable_function F)` stayed a raw compound that no read reached; it is now
  reified when the mark arrives (asserted, derived or revived), in place or folded into
  the row its constant spells, nested applications re-keyed. The mark retracted or
  defeated spells each use as written again and collects the constants. A `result` or
  `genlResult` asserted after a mint materializes onto the constants already minted.
  [nat.md](docs/nat.md#a-reifiable-mark-moving).

  *Class:* **Fix**.
  *Migration:* `recover` re-spells nothing: a store holding raw applications beside a
  believed declaration keeps them until the declaration is retracted and asserted again.

- **`query {:proof? true}` and `argue` return a proof when a rewrite's residual repeats
  a conjunct the goal already holds.** Where the repeat folded onto a literal left of the
  rewritten one they threw `IndexOutOfBoundsException`; where it folded onto one right of
  it the proof showed a derived literal as a `:leaf`. A proof's leaves are now exactly the
  answering node's literals. [inference.md](docs/inference.md#the-two-side-by-side).

  *Class:* **Fix**.

- **A refused mint, lift or argument conviction is asked again after a `recover`.**
  `recover` restarts the `genl` and `genlCx` generations at 0, and replaying the stored
  edges brings them back to the numbers a KB that only added edges held already, so an
  entry stamped before the recover compared equal after it and was not asked again under
  the rebuilt hierarchy. The stamp carries a rebuild epoch the recover moves.
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings).

  *Class:* **Fix**.

- **An `exceptWhen` exception carrying a `forall`, or an `unknown` or aggregate under a
  quantifier, answers as its arrivals move it.** A `forall` conjunct was registered for
  re-check under `forall`, which no fact arrives on, so `(exceptWhen (forall ?c (implies
  (childOf ?b ?c) (sick ?c))) …)` kept the answer it gave when the rule first fired; it
  is now stored as the nested NAF it is, as a `forall` antecedent is, and a malformed one
  is refused `:not-well-formed`. And a block one arrival imposed was not lifted by the
  arrival that ended it — a sick child's exception swept by `(childOf Opus Kid)` stayed
  after `(vaccinated Kid)` ended it, as did a count exception after the next child —
  because only a rule whose own antecedents can be released was re-joined; a rule whose
  exception an arrival can move both ways — an aggregate, or literals under both an odd
  and an even number of `unknown`s — is re-joined too.
  [exceptions.md](docs/exceptions.md#re-chaining-what-was-released-not-what-was-touched).

  *Class:* **Fix**.

### Fixes: order independence

- **A rule firing made over a spelling before a merge superseded it is withdrawn at the
  merge.** With `(pp Zz)`, `(not (pp Aa))` known-true, the forward rule
  `(pp ?x) => (rr ?x)` and `(rewriteOf Aa Zz)`, the KB believed `(rr Aa)` in the 8 arrival
  orders where the merge came last: the firing over `(pp Zz)` stood, and its conclusion's
  restatement under `Aa` carried belief that no defeat named. A merge-first order makes no
  such firing, since a superseded spelling fires nothing. The settle now drops each rule
  firing that names a spelling superseded since the last settle, as an antecedent or as
  its rule, so `(rr Aa)` is not believed in any of the 24 orders, in the negation and the
  inherited families alike. An `except` of the merge that later leaves withdraws the
  firings its spelling made while the merge was hidden. A withdrawn firing that climbed a
  merged type's `genl` edge is drawn again over the restated edge, and a restated edge
  fires the rules it connects in every arrival order: `(dog Rex)`, `(genl dog mammal)`,
  `(genl mammal animal)`, `(animal ?x) => (alive ?x)` and `(rewriteOf mammalia mammal)`
  believe `(alive Rex)` in all 120 orders, where the KB lost it when an edge arrived after
  the merge. `recover` and `preview` withdraw nothing, so a store written before this
  release keeps such a firing.
  [nmtms.md](docs/nmtms.md#the-other-half-a-spelling-an-un-merge-gives-back),
  [equality.md](docs/equality.md#merging-predicates-and-types).

  *Class:* **Fix**.

- **Argument-type derivations are the same in every arrival order and every spelling.**
  An `interArg`, `interArgs` or `interArgAndRest` derivation names the membership that
  makes its trigger hold, so it is drawn when the trigger's type arrives last and goes
  when the trigger is retracted. An `except` of a derivation's trigger membership
  or declaration drops the derivations it held in a context that sees it, and leaving draws
  them again, whichever arrived first. A symmetric or commuting fact's derivations read
  its stored spelling on every path (assert, derivation, a declaration arriving later, a
  text export reloaded), so `(orthogonal food body_part)` and `(orthogonal body_part
  food)` store the same justifications. `perf`'s `trigger-membership-beside-declared-facts`
  holds the late trigger flat in the declared facts that do not name it.
  [argtypes.md](docs/argtypes.md#an-except-of-an-ingredient),
  [canonicalization.md](docs/canonicalization.md#symmetric-arguments-sorted--ground-literals-only).

  *Class:* **Fix**.

- **An `except` sweeps every firing and placed nogood that rests on its target through
  any chain, in every arrival order, and retracting it restores them.** A firing or a
  nogood whose antecedent or member was derived from the excepted fact, placed at or below
  the except's context, stayed stored when it was placed before the except arrived. The
  sweep and the re-check read the except's target's consequence closure, which also bounds
  an except's cost by that closure where it was the extent of every rule the target's
  firings used. [contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree).

  *Class:* **Fix**.

- **Rule firings are the same in every arrival order of the `genl` and `genlCx` edges
  they read.** A `genlCx` edge arriving last fires a rule over a fact when the `genl` edge
  the match reads is stated on the other side of it from the rule and the fact, as a
  cover's edges do; the seeding costs the smaller of the `genl` edges the lower context
  already sees and the new parent's rule-relevant facts (`perf`'s
  `genlcx-edge-under-a-seen-taxonomy`). A stated `genl` route that makes a minted edge
  redundant re-joins the facts and rules the withdrawn mint carried, as an edge that lost
  belief does, so a firing that named the mint as its witness is drawn again over the
  surviving route. [contexts.md](docs/contexts.md#the-consumers-and-what-each-of-them-may-reach),
  [nmtms.md](docs/nmtms.md).

  *Class:* **Fix**.

- **A second route is found through a claim that itself stands on a second route, and a
  belief read counts a route an `except` hides.** The backward search for a firing whose
  witness edge a reader hides read every claim and derived edge with second routes
  switched off, so a goal reached only through a claim that stands on its own second route
  was hidden in every arrival order. A read inside the search now reads its own second
  routes the way a read outside it does. `in?` and `res/believed-at?` counted only routes
  the reader also sees; they now count a claim or an edge an `except` hides, while `ask?`
  and `believed?` still do not. [nmtms.md](docs/nmtms.md#where-the-layer-stops).

  *Class:* **Fix**.

### Fixes: storage

- **A closed KB's records and index are collectable, and a heap failure reading an image
  fails the open.** After `close!` the records and index of the last KB that wrote
  stayed reachable until another KB wrote, so a process opening a large store after
  closing one ran out of heap. An `OutOfMemoryError` while an open read the reasoning
  image, one of its caches or the index image was logged as an unreadable image and
  started a recover or a reindex; it is now rethrown, and an open that throws writes no
  image over the ones it found. [storage.md](docs/storage.md#the-reasoning-image).

  *Class:* **Fix**.

- **A bulk load into the in-memory backend leaves the same nogood candidates and placed
  nogoods as loading the same facts one by one.** A read inside a `*bulk-load?*` load did
  not see the load's own writes. The backend's reads answer from the open load.
  [storage.md](docs/storage.md).

  *Class:* **Fix**.

- **`VAELII_KB_PATH` and `vaelii.kb.path` split on the platform's path separator.** The
  search path was split on `:`, which on Windows cut every absolute path at its drive
  letter. It splits as `PATH` does: on `:`, and on `;` on Windows. Nothing changes off
  Windows. [operations.md](docs/operations.md).

  *Class:* **Fix**.

### Fixes: performance

- **A cold `genls` read costs at most the asked type's closure.** 0.23.0 built an
  up-closure from its parents' closures, building every ancestor not held first, so one
  cold `genls` under a type with two parents paid the sum of its ancestors' closures: a
  100k-type braided hierarchy's read went from 75 ms to 96.7 s. A type with two parents is
  walked, and a one-parent chain still shares structure. `perf`'s `genl-closure-read`
  reads 6.59x against its 16x bound, where 0.23.0 read 59.5x.
  [taxonomy.md](docs/taxonomy.md).

  *Class:* **Fix**.

- **A departing `genlCx` edge re-joins each rule with a `genl` antecedent in full once per
  chaining run.** The retraction re-chains every fact its upper context's ancestor set
  holds, and each `genl` fact among them re-joined every such rule over its whole extent.
  A chaining run re-joins a closure rule in full only when the taxonomy generation has
  moved since its last full join, and otherwise fires it at the fact's trigger position.
  `perf`'s `closure-rule-under-departing-context-edge` reads 6.54x against its 16x
  bound, where the chaining before this change read 30x.
  [inference.md](docs/inference.md#a-genl--genlcx-antecedent-reads-the-closure).

  *Class:* **Fix**.

- **A `:default` fact under a `functional` or `functionalInArg` mark reads no clash for a
  merge.** Only a pair of two `:monotonic` members merges, so a `:default` arrival skips
  `functional-clashes`, and a `:monotonic` one drops the pairs that cannot merge before the
  content sort. `assert_cost_test`'s `functional-in-arg-arity-2` budget reads 800 fewer
  `:predicate-extent` and 1,200 fewer `:trie-counts` per 100 asserts.
  [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing).

  *Class:* **Fix**.

- **A conjunction's plain stored-fact literal no longer probes the consequent index for
  provers.** In 0.23.0 every literal of a `prove` conjunction ran the prover registry's
  shadowing check, which probes the consequent index once per spec of the goal's
  predicate, before the claimants were filtered. The probe runs only for a goal some
  prover claims. [inference.md](docs/inference.md).

  *Class:* **Fix**.

- **An argument declaration over stored facts asks whether its type reaches `thing`
  once.** A declaration arriving over a predicate's stored facts asked every declaration
  on the predicate whether its type reaches `thing` once per fact, so a declaration over
  35,841 facts beside types with large ancestor sets ran for over 54 minutes. The sweep
  reads the arriving declaration alone, asks its type once per `genl` generation, and
  reads no fact when the type does not reach `thing`. `perf`'s
  `arg-declaration-over-facts` holds the cost per fact flat.
  [argtypes.md](docs/argtypes.md#four-directions-or-belief-depends-on-arrival-order).

  *Class:* **Fix**.

- **A membership's cost no longer grows with its type's ancestors or its term's other
  types.** An arriving fact probes the rule index only for the supertypes some stored
  rule reads, where it probed once per supertype. A membership reads the declarations
  above its type from the smaller of the ancestor set and the roster of declaring
  predicates, where it sorted the whole ancestor set. A membership tests its type against
  the term's other types only when a separation reaches it, where n memberships of one
  term cost n³, and the candidate index holds the kept terms by type and each term's
  separated pairs, so a separation declaration tests only the pairs under the types it
  moves. `perf`'s `membership-under-deep-type` (flat from 64 to 4,096 ancestors),
  `membership-beside-held-types`, `separated-membership-beside-held-types` and
  `separation-beside-kept-terms` hold the four costs.
  [indexing.md](docs/indexing.md#3-the-rule-index),
  [nmtms.md](docs/nmtms.md#the-nogood-families).

  *Class:* **Fix**.

- **A write reads the nogood candidates and inherited-clash entries it moves, and no
  other.** Each family names the handles a write moves in the candidate journal, and the
  candidate index keeps every candidate by the context it is stated in, so a write adding
  a candidate reads those handles and the candidates the affected contexts see, where it
  recomputed every candidate's consequence closure. A `genl` edge walks only to the
  functors under an arity conflict below its lower end. A binary tuple reads its
  converses only under a converse mark over its own functor, where every tuple of a KB
  declaring any `anti_symmetric` mark paid one trie read. A declaration the taxonomy
  caches flat, an `except` and a `genlCx` edge ask again only the inherited-clash entries
  that read them, where any `except` or `genlCx` write asked every standing inherited
  clash again, and a settle journals only the inherited-clash members that entered or
  left. `perf`'s `candidate-write`, `reached-reader-family-read`,
  `genl-edge-beside-arity-conflicts`, `inherited-entry-declaration`,
  `inherited-entry-except` and `inherited-clash-arbitration` hold these.
  [nmtms.md](docs/nmtms.md#the-candidate-journal),
  [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).

  *Class:* **Fix**.

- **A write that makes a nogood whole, or retracts its winner, costs the same however
  many firings rest on its loser.** The retract re-chained the loser, refiring every rule
  over it, and placing a membership nogood scanned every justification resting on each
  member. A target a removed `defeat` gives back is re-chained only when the taxonomy
  derives from it, since the network kept it IN, and the placed nogoods over a member are
  read off the term index. `lein perf`'s `whole-beside-loser-consequences`,
  `dissolving-beside-loser-consequences` and their unary twins hold both writes flat.
  [nmtms.md](docs/nmtms.md#a-revived-datum-is-a-datum-the-agenda-has-not-seen).

  *Class:* **Fix**.

- **An `except` costs what its target reaches, not what its context or the guarded rule
  holds.** The except roster is kept by target beside the roster by context, so
  `exception-status`, the read and derivation filters and a meta-except's removal cost
  the excepts naming one handle. An except of a guard's blocker, the blocker's
  retraction, and a defeat that hides the blocker release the swept firing from the
  refusal record instead of re-chaining the guarded rule over its whole extent
  (`except-of-a-guard-blocker`). A `genlCx` edge re-checks only the `except`s stated in a
  context its upper end sees, for the contexts under its lower end
  (`genlcx-edge-beside-excepted-declarations`).
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings),
  [contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree).

  *Class:* **Fix**.

- **A write under a change-feed listener, `preview` or `edit-with-consequences` reads the
  belief before it of what its sentences can move, not of every standing defeat's
  consequences.** A fact naming no nogood member beside 1,024 standing decided nogoods
  took 267 ms under one listener, against 27 ms beside 64. A retraction, or an assertion
  of a stored sentence, reads its handle and what rests on it; a new literal the engine
  does not interpret reads nothing, or, asserted `:monotonic`, the handles a nogood over it
  could defeat. A write that fires a rule, queues a watched rule, names an interpreted
  functor or arrives while an equality edge is stored reads every standing defeat's
  consequences, as every write did. `perf`'s `listener-write-beside-defeats` holds the
  cost flat, and `verdict-window-write` passes, where it read 4.33x.
  [nmtms.md](docs/nmtms.md#the-published-window).

  *Class:* **Fix**.

- **`contradictions` at a context and `preview` read only the nogoods they can see or
  move.** `contradictions` at a context reads the smaller of the extents of the contexts
  it sees and the `contradicts` extent, where it filtered the KB-wide reading, and
  `preview` reads the nogoods of the contexts its batch can move before and after, where
  it read every standing dilemma twice. `perf`'s `reader-dilemmas-beside-unseen-ones` and
  `preview-beside-standing-dilemmas` hold both flat.
  [nmtms.md](docs/nmtms.md#what-a-reading-reads), [preview.md](docs/preview.md#cost).

  *Class:* **Fix**.

- **A defeat of a `genl` edge retires only the scoped closures that can cross the edge,
  and walks no consequence closure while no scoped read rests on a defeated target.** A
  defeat stored, removed or relabelled, and a `genl` supporter a settle relabels, moved
  one visibility generation, so every reader recomputed every scoped `genl` closure and
  its visible-context set. They now evict the scoped closures of the nodes at or below
  the edge's lower end or at or above its upper end, read at the readers that see the
  defeat, and a defeat move reads the `genl` gate's memo instead of walking its target's
  consequences. `perf`'s `defeat-beside-unreached-readers` holds a closure read at a
  reader the defeat does not reach flat in the readers, and
  `whole-beside-loser-consequences` reads 1.31x against its 2.0 bound.
  [nmtms.md](docs/nmtms.md#a-read-with-no-reader).

  *Class:* **Fix**.

### Fixes: the browser

- **The browser's taxonomy views draw the edges a roster installs and draw the same
  neighbours on every KB holding the same edges, and the mouse wheel scrolls the page
  over the concept graph.** The taxonomy view and hierarchy tree draw from `direct-genls`
  and `direct-specs`, so a type whose parent edge comes from a `covering`, `separating` or
  `partition` roster is drawn with its parent, and every level of the tree is sorted. The
  front page's disjointness list holds the pairs a `separating` or `partition` roster
  separates, which store no `disjoint` sentence. The concept graph draws at most eight
  neighbours of a node: it reads up to 501 direct supertypes or subtypes, sorts them, and
  draws the first eight with an exact count in the caption, where it drew the first eight
  the index returned; a node with more than 500 draws none, and the caption says so. The
  graph's box leaves `overscroll-behavior` at its default, so a wheel turn the box cannot
  use scrolls the page. [web.md](docs/web.md).

  *Class:* **Fix**.

### Internal

- **`recover` and a fork rebuild no roster the index holds.** The except and defeat
  rosters by context and by target, the meta-except count, the rule rosters by antecedent
  key, by context and by kind, the mint roster, the bodies stored in both polarities and
  the negation candidates over them, the argument-preservation roster, and the taxonomy's
  supporters and context census are read from the index families (`reads/as-stored-*`,
  `reads/stores-*?`, `inherit/preserved-pairs`). The nogood candidates keep no stored
  `disjoint`, cover, `orthogonal`, self tuple or tuple of a shape (register rows N1, N3,
  N6): a write reads them off the argument trie, the extents, the shape roster and the
  self-tuple trie, and `:related-dj`, `:related-orth` and the cover pairs stay as a cache
  bounded by the stored declarations. The taxonomy's relation context counts, the flat
  caches' context census, the interned visibility sets (row T6) and the supporter maps
  are deleted; a scoped `genl` read intersects the reader's ancestor set with the
  children of the `genl`, `covering`, `separating` and `partition` extents, and a bounded
  cache (`:taxonomy-supporters`, row T11) holds what the belief reconcile reads. A KB
  storing no except, defeat or preservation pays up to thirteen count reads per assert
  for these, one more rule-index read per assert and five per `genl` edge, and one more
  index read per settle pass. [indexing.md](docs/indexing.md),
  [taxonomy.md](docs/taxonomy.md#the-supporters-are-index-families-and-a-cache-holds-what-the-reconcile-reads),
  [nmtms.md](docs/nmtms.md#the-nogood-families).

  *Class:* **Internal**.

- **The per-reader decision machinery is deleted, and every belief read is the read
  walk.** `vaelii.impl.reroute`, the per-reader decision code in `vaelii.impl.resolution`,
  the `:withdrawn` and `:own-readings` fields, `decide/losers`, `redecide` and their
  rounds, the re-read under a reader's withdrawal, `special/reconcile-own-withdrawals!`
  and `jtms/grounded-forcing-out` go, with the cache rows they held. `hidden-fn`,
  `belief-hidden-fn`, `own-hidden-fn`, `believed-own?` and `without-excepted` live in
  `vaelii.impl.except` and read the `except` and `defeat` rosters over the asked handle's
  support. A reporting write reads what its defeats moved against a reading it takes at
  its entry point (`settle/reading-before`). The inherited family asks its clashes from
  the except-aware placement, which moves to `vaelii.impl.resolution`;
  `inherit/denial-contexts` is `inherit/denial-readings` and names each reading's handles.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion),
  [reference.md](docs/reference.md#decisions).

  *Class:* **Internal**.

- **Every derived structure is registered with its key, its reads and the write events
  that retire it, and an instrument counts what each event retires.**
  `caches/derived-state` returns the register; `derived_state_test` fires each event on a
  small KB and fails when a row moves under an event it does not declare or a map key
  belongs to no row. `lein lint`'s `derived` check fails a stateful `def` or a
  `Reasoning` field with no row (the `lint-derived` alias is gone), and `docs/caches.md`'s
  register table is generated
  (`lein derived-state`, rewritten by `lein regen-goldens`). `caches/start-tally!` counts
  each event's firings and retirements per row and compares a miss's recompute with the
  value it replaced; `caches/tally-ranking` orders the rows by recompute time times
  spurious fraction. It keeps a retired value's hash, not the value, which on the full
  store took a 40 GB heap. `lein derived-state -- --edn <path>` exports the register,
  and `scripts/derived-state-graph.py` draws its dependency graph.
  [caches.md](docs/caches.md#the-derived-state-register).

  *Class:* **Internal**.

- **`lein perf --only` takes a comma-separated list and runs in a linked worktree, a check
  can be marked `:unmet`, and `lein perf-ab` times a fixed cost against a base
  revision.** The named checks run in one JVM in roster order, and an unknown name exits
  2; a full `lein perf` still runs only in the primary checkout. An `:unmet` check is
  judged against its bound and reports UNMET without failing the run. `lein perf-ab
  <base-rev>` runs fixed probes through the public API on the base and the working tree
  in alternating fresh JVMs and fails a probe whose median paired ratio passes 1.25x, so
  it catches a cost added to every operation, which moves both of `lein perf`'s sizes.
  Checks added this release cover the cost of a write, a read and a `belief-status`
  beside standing nogoods, the second-route search, and a cold `genls` read.

  *Class:* **Internal**.

- **The disjointness coverage ratchet reads the starter KB's values.** It fails when the
  disjoint pair count falls below 13,762, disjoint coverage below 69.85% or unknown pairs
  rise above 20.66%. The pair count floor fails a removed separation that a new type's
  pairs hide in the percentages.

  *Class:* **Internal**.

- **A change no caller observes takes the fifth class, Internal, and gets an entry only
  when a maintainer needs to know about it.** CONTRIBUTING §3.8 defines the class and
  says which Internal changes get an entry, and `scripts/check-breaking-siblings.sh`
  accepts it. An Internal entry alone raises no version. Entries for one subsystem merge
  into one, and each heading runs from most to least impact.
  [CONTRIBUTING.md](CONTRIBUTING.md).

  *Class:* **Internal**.

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
