# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.34.0 are summarized rather than reproduced.** Each one
keeps its title and its class census, and each one from 0.14.0 on keeps every
`*Breaks:*` token, so an upgrade across those releases is still a grep for the name you
call; 0.8.0 through 0.13.0 keep a subset. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking: shipped ontology

- **Blood kinship is genetic kinship, and generic kinship is unqualified.** The 0.34.0
  spellings are renamed with their arity and argument order: `BloodKinFn` is
  `GeneticKinFn`, `blood_kinship_predicate` is `genetic_kinship_predicate`,
  `generic_kinship_predicate` is `unqualified_kinship_predicate`, `bloodRelativeOf` is
  `geneticRelativeOf`, `bloodKinPredicateOf` is `geneticVersionOf` and
  `chosenKinPredicateOf` is `chosenVersionOf`. `resources/renames/unreleased.edn` records
  the six, so `upgrade --sync` rewrites a stored premise that names an old spelling.
  Gestational-only parenthood and surrogacy are not genetic kin and specialize no parent
  or mother predicate. A child can have more than one mother or father, so `life.txt`
  states `(not (functional motherOf))` and `(not (functional fatherOf))`, and
  `kinship.txt` states the same of `(GeneticKinFn motherOf)` and
  `(GeneticKinFn fatherOf)`, each with a `comment` giving a case. `MotherFn` and
  `FatherFn` are retired, and `resources/renames/unreleased.edn` records both, so
  `upgrade --sync` reports a stored premise that names either. `birthDate`,
  `birthYearOf` and `olderThan` are eternal predicates again and no kinship predicates, so
  no qualified reading of them ships.
  *Migration:* run `upgrade --sync`, or rename the six spellings in KB text, rules and
  queries. State gestational-only parenthood or surrogacy with `gestationalOnlyParentOf`
  or `surrogateMotherOf`. State `motherOf` or `fatherOf` facts directly where a KB wrote
  `(MotherFn ?x)` or `(FatherFn ?x)`. Write a `((BloodKinFn birthDate) ?x ?t)`,
  `birthYearOf` or `olderThan` fact as the unqualified fact. `upgrade --sync` rewrites a
  stored one to a `GeneticKinFn` application and refuses none: the three are eternal
  predicates, which no `unqualified_kinship_predicate` is, so the rewritten premise is
  ill-typed. Restate each one as the unqualified fact or retract it.
  *Breaks:* `BloodKinFn`, `blood_kinship_predicate`, `generic_kinship_predicate`,
  `bloodRelativeOf`, `bloodKinPredicateOf`, `chosenKinPredicateOf`, `parentOf`,
  `motherOf`, `fatherOf`, `MotherFn`, `FatherFn`, `birthDate`, `birthYearOf`, `olderThan`
- **CxTra drops `chosenSiblingOf` for `(ChosenKinFn siblingOf)`.** `chosenSiblingOf`, a
  spec of `(ChosenKinFn siblingOf)`, is retired. `(ChosenKinFn siblingOf)` names the same
  relation and is symmetric, time-varying, typed `person` at both positions, and below
  `chosenKinOf` and `siblingOf`.
  `resources/renames/unreleased.edn` records the term as retired, so `upgrade --sync`
  reports a stored premise that names it.
  *Migration:* write `((ChosenKinFn siblingOf) ?x ?y)` for `(chosenSiblingOf ?x ?y)`.
  *Breaks:* `chosenSiblingOf`
- **`injection` is `injective_predicate`, `surjection` is `surjective_predicate` and
  `bijection` is `bijective_predicate`.** The three predicate types keep their meanings,
  declarations, comments and rules under the new names in `core.txt`, and `kinship.txt`'s
  acknowledgments quote the rules by the new names. The names say that each is a type of
  predicate. `resources/renames/unreleased.edn` records the three renames, so
  `upgrade --sync` rewrites a stored premise that names an old spelling.
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* rename `injection` to `injective_predicate`, `surjection` to
  `surjective_predicate` and `bijection` to `bijective_predicate` in KB text, rules and
  queries.
  *Breaks:* `injection`, `surjection`, `bijection`
- **A `computational_system` is `causal`, read-only software tools included.** CxTra
  states `(genl computational_system causal)` and drops
  `(genl read_only_software_tool acausal)`. It also drops
  `(genl write_capable_software_tool causal)`, which the new edge derives. A running computational system is the doer of
  what runs in it and of what its tools do. A read-only tool's invocation changes what
  its caller knows, so a read-only tool can be a cause. `read_only_software_tool`'s
  comment now says that its invocation changes none of the state it reads. CxTra's
  default reading `able` from `agentHasTool` and `toolEnablesAbility` concludes `able`
  only of a causal holder, so a `seat` or any other computational system that has a tool
  enabling a kind is now `able` of that kind. Through `(partition thing causal acausal)`,
  every computational system is now disjoint from every acausal kind, `information`,
  `time` and `communication_channel` among them. `read_only_software_tool` and
  `write_capable_software_tool` are no longer disjoint. Nor are a read-only tool and
  `person`, `organization`, `alter`, `singlet`, `plural_system` or `hollow`.
  [contexts.md](docs/contexts.md)
  *Migration:* a KB that states a computational system, a read-only tool among them,
  `acausal` or a member of an acausal kind now clashes. Retract that statement.
  *Breaks:* `read_only_software_tool`
- **A tool in `agentHasTool` and `toolEnablesAbility` is `causal`, and `image_viewing` is
  not `acausal`.** Position 2 of `agentHasTool` and position 1 of `toolEnablesAbility`
  declare `causal`, not `temporal`. A software tool is causal through
  `computational_system`, and a hammer or a jetpack is causal through `tangible`. CxTra
  drops `(genl computational_system temporal)`, which `(genl causal temporal)` derives.
  CxTra states `(genl image_viewing event)` for `(genl image_viewing acausal_event)`.
  Taking in an image can change what the viewer knows, so `image_viewing` is not placed
  acausal. `image_viewing` is no longer disjoint from `causal`, `causal_event`, `flying`,
  `travelling`, `organization` or `hollow`.
  [contexts.md](docs/contexts.md)
  *Migration:* an acausal thing stated in either tool position is now concluded
  `causal`, and the conclusion clashes. A `tool_receipt` or a `communication_channel`
  stated as a tool is one such case. Retract that statement. A query for
  `(able ?x acausal_event)` no longer reads `image_viewing`; ask `(able ?x event)`.
  *Breaks:* `agentHasTool`, `toolEnablesAbility`, `image_viewing`

### Breaking: inference

- **A functional collision reads three levels of determinateness.** A `functional` or
  `functionalInArg` collision between two symbols merged only when both facts were
  `:monotonic`. core.txt now declares `proxy_term` and `placeholder_term`, reflection.txt
  states `(partition proxy_term placeholder_term indeterminate_term)`, and
  `provers/determinateness` reads each filler's level off the symbol as written. A `nat/`
  or `cx/` reified constant that is no skolem is a `placeholder_term`, and the
  unique-name assumption holds for it. A skolem constant is an `indeterminate_term`. A
  proxy filler merges whatever the facts' strength with a determinate constant that is
  the one candidate of its slot. So a `:default` `(bestFriendOf Ann Mary)` merges a
  placeholder in Ann's slot with Mary, and a `:default` `(bestFriendOf Ann Jane)` beside
  it withdraws the merge, so Mary and Jane never merge on `:default` evidence. The merge
  comes back when the rival leaves, in every arrival order. A collision with a proxy
  filler that does not merge places no nogood in a context that reads the filler as a
  proxy, and keeps its nogood in a context that does not. A placeholder against a
  `:default` value of its own correspondence is no collision, and the value's copies
  carry it. The `different` prover and the `predAllSpecified` audit read a placeholder
  term as determinate and an indeterminate term as indeterminate. A late membership of
  either part reaches a collision stored before it.
  [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing)
  *Breaks:* `equals`, `contradictions`
- **An equality class prefers a constant over a reified constant.** Its representative
  was the smallest member by name, so `(<VerFn basePred>)` stood for a class holding
  `namedPred`. A `nat/` or `cx/` constant now stands for a class only when every
  candidate is one. The spelling a quoted position reads breaks a tie among `rewriteOf`
  heads the same way. [equality.md](docs/equality.md#choosing-the-representative)
  *Breaks:* `representative`, `ask`

### Breaking: describe and the term page

- **The definitional block reads the KB's classification.** A sentence about the term is in
  `describe`'s `:definitional-block` when its predicate is a `definitional_predicate`,
  read with the vocabulary audit's reader (`vocabulary/members`). `:kind` lists every
  unary predicate holding of the term, less the kinds knowing its arity implies: an
  `arity_type`, a class `predicateTypeByArity` or `functionTypeByArity` maps, and an
  `arity_type`'s `intersection` with `predicate`, `function` or `relation`. A kind below
  one of them by `genl` alone stays, so `arachnid` lists `invertebrate_class`.
  `:arg-declarations` is every `wff_predicate` sentence, `argsGenl` and `result` among them.
  The block's `:props` part is every `algebraic_predicate_property` sentence as a
  `{:kind :sentence :context}` row, so `irreflexive` and the per-position
  `functionalInArg` show. A new `:links` part lists `seeAlso` and each `termsRelated`
  cluster naming the term. A `predicateDisplayOrder` fact in core.txt orders the block's
  parts and rows. The comment and the examples lead, then the arity, the arity class and
  the kinds. The parents, the separations, the argument declarations, the relation
  properties and the links follow.
  The term page heads the block **Definition** and draws it as a summary of the index
  groups below it, which list each assertion about the term exactly once.
  A unary sentence such as `(irreflexive P)` shows as its predicate, the links line lists
  the related terms, and each numbered position an `arg`, `argN` or `quotedArg` declaration
  types has a line of its own listing its types. The siblings line shows 12 siblings and
  opens the rest in place behind **+ N more**. A new `:other` part holds the definitional
  sentences no other part shows, ranked by their predicates, so an unnamed one is last.
  A `variable_arity` predicate's block has no `:arity` part. `genl`'s comment says what `genl` means, and
  an `implementationNote` on `genl` records that the engine caches its closure.
  `seeAlso` and `termsRelated` are classified enforced, since the block reads them.
  *Migration:* read the block's `:props` rows' `:sentence` in place of a keyword set; the
  top-level `:props` keyword set is unchanged.
  *Breaks:* `describe`'s `:definitional-block`
  [web.md](docs/web.md#a-term-page-lists-its-definitional-block)

### Refusal: inference

- **A generator whose conclusion arrives as a predicate it reads by `genl` or a swap edge
  feeds itself.** The generator-cycle check matched a conclusion only to reads of its own
  predicate. A conclusion `(sub (F a))` under `(genl sub marker)` also arrives as a
  `(marker (F a))` read, so a generator reading `(marker ?y)` and concluding
  `(sub (F ?y))` generated forever. Under `genlInverse` or `inverse` a binary conclusion
  arrives as a binary read with its arguments exchanged, and the check reads it so. A
  read of each predicate the conclusion arrives as is now fed.
  [generators.md](docs/generators.md#what-is-refused)
  *Migration:* break the cycle, or state the read on the conclusion's own predicate where
  the generator meant to read only its own kind.
  *Breaks:* a generator, or a loop of generators, feeding a read above its conclusion's
  predicate by `genl`, `genlInverse` or `inverse`

### Additive: inference

- **A firing whose ground antecedents are forced-monotonic concludes a forced-monotonic
  literal.** The forced-monotonic check reads each antecedent as stored and as the ground
  instance the firing's bindings make of it, at the chainer, the `:void` forced set, the
  read walk and `why-not`. A rule `(implies (and (k ?p) (genl ?p ?g)) (k ?g))` with `k`
  forced-monotonic places its firing over `(genl p g)` between two predicates, and holds
  void its firing over `(genl t u)` between two types. `:not-forced-monotonic` names the
  antecedents not forced-monotonic at the firing.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-set)
  *Migration:* none; a firing this admits was held void, and a firing held void before
  over an unforced instance is still held void.
- **A generator whose conclusion's application cannot be one of its typed reads closes no
  generator cycle.** The generator-cycle check cuts a feed at an argument `(F …)` where the
  reader types the variable `(T ?v)`. The cut needs a `(result F R)` visible at CxUniverse,
  and a separation of `R` from `T` that every reader reads. That separation is read at
  CxUniverse, at `:monotonic`, and spared by no stored `siblingDisjointException`. A type
  read of the conclusion's predicate or of a `genl` of it cuts nothing. A generator
  lifting `genl` edges between unqualified inputs to edges between their readings is
  accepted where such a separation holds the readings' result type apart from the inputs'
  type.
  [generators.md](docs/generators.md#what-is-refused)
  *Migration:* none; a generator this admits was refused `:not-stratified`.

### Additive: shipped ontology

- **A function's corresponding predicate is functional at the value position.** A
  `core.txt` rule concludes `(functionalInArg ?predicate ?position)` from each
  `(functionCorrespondingPredicate ?function ?predicate ?position)`, since a function has
  one value for each argument tuple. Each shipped correspondence's predicate, `startOf`,
  `calendarYear` and `listOf` among them, takes the mark, and two `:monotonic` symbol
  values at the position merge.
  [nat.md](docs/nat.md#the-corresponding-predicate)
- **`injective_function`, `surjective_function` and `bijective_function` are types of
  function.** `core.txt` declares each below `function`, decontextualized, time-invariant
  and forced-monotonic, as its predicate twin is. `bijective_function` is below the other
  two. An `injective_function`'s applications to different arguments denote different
  things. An inert rule states that definition for a unary function, since an argument
  tuple of any length is no term.
- **`geneticVersionOf` and `chosenVersionOf` relate an unqualified kinship predicate to
  its genetic and chosen versions.** `kinship.txt` declares each the binary predicate
  corresponding to `GeneticKinFn` or `ChosenKinFn`, taking an
  `unqualified_kinship_predicate` first and a `genetic_kinship_predicate` or
  `chosen_kinship_predicate` second, functional, eternal and forced-monotonic, so a rule
  reading one may conclude a forced-monotonic declaration of the version.
  The kinship copy rules read each reading through them rather than through a
  `GeneticKinFn` or `ChosenKinFn` application, so a reading named by a plain symbol takes
  its input's class, arity, argument types and symmetry too.
  `(geneticVersionOf siblingOf (GeneticKinFn siblingOf))` holds.
- **An `eagerly_reifiable_function`'s applications are reified as soon as their arguments
  meet its argument constraints.** `core.txt` declares three terms.
  `eagerly_reifiable_function` is a type of function, a spec of `reifiable_function`.
  `meetsArgConstraints` holds of a function and arguments that meet its `arg` and
  `argGenl` declarations. `reify` holds of a term of the KB. One general rule concludes
  `(reify (?f . ?args))` from `(eagerly_reifiable_function ?f)` and
  `(meetsArgConstraints ?f . ?args)`, and its firing mints the application.
  `kinship.txt` declares `(eagerly_reifiable_function GeneticKinFn)` and
  `(eagerly_reifiable_function ChosenKinFn)`, so every unqualified kinship predicate,
  one declared later included, has both readings reified.
  *@hack:* `reify` has no engine support yet, so a rule comments each reified term as a
  temporary implementation. `meetsArgConstraints` is concluded only for a unary
  `eagerly_reifiable_function`, from each `arg` declaration alone and without `argGenl`.
  `eager_reify_test`'s `^:red` tests state the general reading.
- **An `injective_predicate` that is a `surjective_predicate` is a `bijective_predicate`,
  and `folk_biological_class` is forced-monotonic.** A forward-only `core.txt` rule
  concludes `(bijective_predicate P)` from `(injective_predicate P)` and
  `(surjective_predicate P)`, and retracting either withdraws it. `organism.txt`
  declares `(forced_monotonic_predicate folk_biological_class)`, as `folk_species` already
  is, so a class membership is never the loser of a nogood.
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* none.
- **Kinship hierarchy lifting reads each `genl` edge between unqualified inputs once.**
  kinship.txt's two lift rules conclude `(genl ?v ?gv)` from `(geneticVersionOf ?p ?v)`,
  `(geneticVersionOf ?g ?gv)` and `(genl ?p ?g)`, and the `chosenVersionOf` twin, in place
  of two generators of one ground rule per ordered pair of unqualified predicates. The
  starter stores no generated lift rule (128 before), its forward firings fall from 3,147
  to 3,019, and the lifted `genl` set is unchanged.
  *Migration:* none; the lifted edges are the same.

### Fix: describe

- **A type's disjoint line is sorted whenever the union of its partners' closures fits
  the sort budget.** The choice used the sum of the closure sizes, which counts an overlap
  twice, so a line whose union fit could come out unsorted and inexact, and a sorted
  member such as `cat` under `dog` could fall off it. Past the budget the line stays
  unsorted, with the sum as its `:total` and `:exact?` false.

### Fix: order independence

- **A mint's `natFormula` map, stated, gets its constant's result types.** A mint
  types its constant from each `(result F T)` and `(genlResult F T)` stated before it,
  and a declaration stated after the mint types every constant minted for `F`. A
  `(natFormula K E)` map stated after the declaration typed nothing, and a text KB's
  reload states each map after the declarations, so the reloaded upper layer lost 14
  `result` justifications of its kinship constants. A stated map whose `K` is the
  constant `E` names now gets the `(T K)` and `(genl K T)` a mint writes, with the
  same justification.
  [nat.md](docs/nat.md)
  *Migration:* none.

### Internal: tooling

- **`lein perf-ab` fails a run whose JVM stops at a probe that throws.** `assert` refused
  `arity-edge-move`'s setup, and a full run timed the nine probes before it and passed.
  The probe runs again, and the seven probes from it on report.
  [CONTRIBUTING.md §1.1](CONTRIBUTING.md#11-static-analysis-lein-lint-setup)

### Internal: CI

- **A pull request runs the perf-ab probes its change reaches, under one `perf` check.**
  Each of three reps runs on its own runners, `starter-load` apart from the other probes.
  A change under `resources/kb/` runs the `starter-load` and `starter-recover` probes, and
  a change under `src/vaelii/impl/` or to `src/vaelii/core.clj` runs all 16.
  `scripts/perf-owed.py` reads a file whose namespace its reach map holds no key for, and
  every file when there is no map, through its per-file rules. `lein perf-ab --first-rep
  K` numbers a run's reps from K, and `lein perf-ab --judge <rows.tsv>…` judges the rows
  of several runs as one. [CONTRIBUTING.md §7](CONTRIBUTING.md#7-commits--pull-requests)

## 0.34.0 — 2026-11-18 — "Kinship qualified by blood and choice, forward `(k ?x)` antecedents over declared result types, context NATs ordered both ways, term rename, merge, copy and remove, bounded removals"

| Area | Change |
|---|---|
| shipped ontology | kinship under one generic hierarchy, qualified by `BloodKinFn` and `ChosenKinFn`; `partOf` between two times derives `subtimeOf`; `hasCapability` is `able`; `may`, `can`, `intersection`, `comment` and the quoted audits `predAllQuotedSpecified` and `predSpecifiedAllQuoted` |
| inference | a forward `(k ?x)` antecedent holds for an application a `result` or `resultArg` declaration types; a `:monotonic` inclusion rewrites a stored meet; a positive `rewriteOf` goal answers through representatives; `orthogonal` is not forced-monotonic and its clash is read by strength; a mint in a type bound to another length is held OUT; `set/oneJustificationRule`; order-independence fixes for guards, grants, respelled rules and swap edges |
| time | `(IntervalBeforeFn W)` and `(IntervalAfterFn W)` hold their moments; a ground Allen goal reads stated bounds; `DatetimeFn` names an interval under a second |
| contexts | two context NATs ordered each below the other are one class on `:monotonic` evidence and `contextsOrderedBothWays` on `:default`; a moment's slice lies inside a named time's slice only while the time has no gap; a slice's eternal or decontextualized fact is copied only where the sliced context sees it eternal; an equality between two contexts joins their extents |
| NATs | a minted constant's role read off its length bindings; its result types derived from its map and their declaration; a write through a merged argument names its own spelling's constant; a `rewriteOf` target takes the application's `natFormula` and result types |
| writes | `assert` refuses an upper bound on the present's start as `:exact-present`; `rename-terms!`, `merge-terms!`, `copy-terms` and `remove-terms!`; `retract!`, `edit!` and `settle-record-edits!` bound the re-chain a removal releases |
| integrity | `vocabulary-audit` reads `definitional_predicate`; the arity sweep reports a `genl` node whose only length is inherited; `kb-integrity` reports a conjunction rule's `intersection` and a `genl` edge whose spec admits a length its genl does not |
| serving | a token-table grant removes only where it would write, under the write's bound; a `cx/` constant's `natFormula` names each context its pairs order below it |
| performance | a chain beside an unrelated `except` is linear; a justification reads none of its conclusion's other supports; a backward goal reads only the rules its argument heads admit (index layout 23); a write or settle reads each rule, declaration and owing datum once; `recover` over block conditions; a `genlCx` edge reads only the `natFormula` rows it joins |
| browser | `vaelii.web/page` draws an extension's route as a page; a reified NAT's parens are coloured apart from a structural NAT's |

Twenty entries are **Breaking** and two are **Refusals**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.33.0 caller changes.

| If your code… | Then |
|---|---|
| names `relativeOf`, or reads blood descent or eternity off `parentOf`, `childOf`, `motherOf`, `fatherOf` or `siblingOf` | rename `relativeOf` to `kinOf`, and rewrite biological family and history facts with `BloodKinFn` |
| asserts `partOf` between two times where the part does not lie inside the whole | state `partOf` between two times only where the part lies inside the whole |
| names `hasCapability`, `capabilityType` or `toolEnablesCapability` | name `able`, `abilityType` and `toolEnablesAbility`; `upgrade --sync` rewrites a stored premise |
| has a forward rule with a `(k ?x)` antecedent that is to read stored members only | give the rule a type antecedent no `result` or `resultArg` declaration reaches |
| reads a stored meet application whose arguments a `:monotonic` fact orders | state the inclusion at `:default` to keep the application in answers |
| reads the answers to a positive `rewriteOf` goal as stored spellings | read a stored edge's own spelling with `sentexes-matching` |
| concludes `orthogonal` from a `:default` membership, or relies on a `:default` `orthogonal` winning its clash | write a definitional `orthogonal` at `:monotonic`, and state a separation or edge `:monotonic` where it is to defeat a `:default` `orthogonal` |
| reads a mint in a type an arity statement binds to another length through its handle | read whether the membership holds through `ask` or `in?` |
| bounds an `edit!` with `:max-ms` or `:stop?` over a removal that releases a long re-chain | raise the bound |
| reads a slice ordered around two context NATs a `:monotonic` order places each below the other | state at `:default` the evidence of a pair that is to stay ordered one way, and read the pair's identity off `equals` |
| reads a slice ordered around two context NATs a `:default` order places each below the other | retract or defeat the direction that is not to hold, or state both at `:monotonic`; rename a relation spelled `contextsOrderedBothWays` |
| reads a moment's slice inside a named time's slice where the time's gaps are not ruled out | state the time's type in CxUniverse, such as `(time_interval T)` |
| reads at a sliced context an eternal predicate's fact stated in a slice | state the membership making the predicate eternal in the sliced context, a context it sees, or the slice |
| reads the sliced context's copy of a decontextualized fact stated in a slice | read the fact at the sliced context, or state `(eternal_predicate P)` beside `(decontextualized_predicate P)` |
| reads a `nat/` constant's role with `term-role`, or the class of a `genl` between minted constants off their names | read the role with `relation?` or `describe` |
| reads a minted constant's result type as a premise, or as `:monotonic` under a `:default` declaration | state the `result` or `genlResult` declaration `:monotonic` |
| reads the constant in a stored sentence written through a merged argument, or the `cx/` context a merged slot write is stored in | read the use through `ask` or `query`; the stored sentence names the constant of the spelling written |
| asserts an upper bound on the start of the real world's present | state a clock reading as `(instantNotBefore W T)` |
| reads `vocabulary-audit` over a grammar term outside `definitional_predicate` | ask `interpreted` of the term, or mark the block predicate `definitional_predicate` |
| runs `kb-integrity` over a `genl` node whose only length is inherited | state an arity of each `genl` node |
| removes through a token-table grant a sentex in a context the grant cannot write, or one whose removal withdraws a conclusion outside `:writes` | add the context the 403 names to the grant, or remove under an admin grant |
| writes or removes a `natFormula` for a `cx/` constant through a grant that does not name each context its pairs order below it | name those contexts in the grant, or write the `natFormula` under an admin grant |

### Breaking: shipped ontology

- **Kinship shares one generic hierarchy with blood and chosen readings.** `relativeOf`
  becomes `kinOf`; `BloodKinFn` qualifies eternal blood history and `ChosenKinFn`
  qualifies time-varying chosen ties. Generic kinship is time-agnostic. Gestational-only
  parenthood is blood kin without a genetic or shared-carrier sibling inference.
  Mothers are not unique; `MotherFn` does not choose between several known mothers.
  Named blood/chosen predicates keep separately justified constructor results and
  correspondences; removing a use removes only the proofs that depend on it.
  `originatorOf` admits organisms and no longer specializes kinship.
  [commonsense.md](docs/commonsense.md#what-the-schema-carries-for-these-questions)
  *Migration:* rename `relativeOf` to `kinOf`; rewrite biological family/history facts
  with `BloodKinFn`. Generic facts no longer assert blood descent or eternity.
  `MotherFn` and `FatherFn` correspond to their blood-qualified predicates.
  *Breaks:* `relativeOf`, `parentOf`, `childOf`, `motherOf`, `fatherOf`, `siblingOf`,
  `grandparentOf`, `ancestorOf`, `birthDate`, `birthYearOf`, `olderThan`, `MotherFn`,
  `FatherFn`, `originatorOf`
- **A time that is part of a time is a subtime of it**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). `time.txt` states the forward
  rule from `(partOf P T)`, `(time P)` and `(time T)` to `(subtimeOf P T)`, so a stated
  piece of an intermittent time places a moment's slice under the whole's. `kb-integrity`
  reports the rule's pair with the root `properPartOf` denial as an acknowledged
  `:rule-clash-review` finding.
  [time.md](docs/time.md#a-slice-of-a-slice)
  *Migration:* none to keep the new conclusions. State `partOf` between two times only
  where the part lies inside the whole.
  *Breaks:* `assert` of a `partOf` between two times, which stores the `subtimeOf`; `ask`
  and `query` of that `subtimeOf`; reads at a moment's slice inside the part; `kb-integrity`
- **`hasCapability` is `able`, `capabilityType` is `abilityType` and
  `toolEnablesCapability` is `toolEnablesAbility`.** The three relations keep their
  declarations, comments and rules under the new names, in `life.txt`, `CxBiology` and
  `CxTra`. `able` names dynamic ability, the reading `may` and `can` sit beside.
  `resources/renames/unreleased.edn` records the three renames, so `upgrade --sync`
  rewrites a stored premise that names an old spelling.
  [inherit.md](docs/inherit.md#six-predicates-ship-with-one)
  *Migration:* rename `hasCapability` to `able`, `capabilityType` to `abilityType` and
  `toolEnablesCapability` to `toolEnablesAbility` in KB text, rules and queries.
  *Breaks:* `hasCapability`, `capabilityType`, `toolEnablesCapability`

### Breaking: inference

- **A forward rule's `(k ?x)` antecedent holds for each application a stored fact mentions
  whose function's `result` or `resultArg` declaration types it at or below `k`**
  ([#226](https://github.com/vaelii/vaelii/issues/226),
  [#259](https://github.com/vaelii/vaelii/issues/259)). The rule fires whichever
  antecedent binds `?x`, and whichever of the mention, the declaration, a `genl` edge and
  the rule arrives last. The firing rests on a fact mentioning the application and goes
  with the last one. CxUniverse's `(time ?t) → (timeOf ?t ?t)` stores `(timeOf T T)` for
  each mentioned calendar term `T`, and `(partOf P T)` between two calendar terms stores
  `(subtimeOf P T)`. A fact naming a fresh calendar term stores three sentexes: the fact,
  `(timeOf T T)` and `(uninterrupted_time T)`. Each further fact naming `T` adds one
  justification to each conclusion the rules over its type place.
  [inference.md](docs/inference.md#a-type-an-applications-function-declares)
  *Migration:* none to keep the new conclusions. A rule that reads stored members only
  takes a type antecedent no `result` or `resultArg` declaration reaches.
  *Breaks:* `assert` over a forward rule with a `(k ?x)` antecedent and a declaration
  typing an application at or below `k`, which stores the new conclusions
- **A `:monotonic` fact placing one argument of a stored meet application below the other
  rewrites the application to that argument** ([#259](https://github.com/vaelii/vaelii/issues/259)).
  With `(subtimeOf a b)`, `(subintervalOf a b)` or `(includesInstant b a)` stored
  `:monotonic`, every literal naming `(TimeIntersectionFn a b)` answers under `a`, a
  slice's `natFormula` map included, so `cxTimeOf` of the slice at a moment of a year
  slice answers the moment. A stored literal keeps the application's spelling, a written
  `(CxTimeOfFn K)` stores the same term whichever arrives first, and retracting the fact
  restores the application in answers. A compound `(rewriteOf T E)` rewrites a ground
  application `E` a stored literal names to `T` when `T` is one of `E`'s arguments.
  [canonicalization.md](docs/canonicalization.md#a-meet-a-stated-inclusion-absorbs)
  *Migration:* state the inclusion at `:default` to keep the application in answers.
  *Breaks:* `query`, `ask` and `cxTimeOf` over a meet application whose arguments a
  `:monotonic` fact orders, and over an application a compound `rewriteOf` rewrites to
  one of its arguments
- **A positive `rewriteOf` goal is answered through the reader's representatives**
  ([#277](https://github.com/vaelii/vaelii/pull/277)). The goal's endpoints and each
  visible stored edge's endpoints are read as their representatives before they match, and
  a backward rule's `rewriteOf` head is matched the same way once its body binds. Over
  `(rewriteOf A B)` and `(sameAs B C)`, `ask`, `query` and `prove` answer `(rewriteOf A
  A)`, `(rewriteOf B A)` and `(rewriteOf A C)`. `(rewriteOf A ?x)` binds `?x` to `A`, not
  `B`. The stored edge and what a write admits are unchanged.
  [equality.md](docs/equality.md#answering-an-equation)
  *Migration:* read a stored edge's own spelling with `sentexes-matching`.
  *Breaks:* `ask`, `query` and `prove` of a positive `rewriteOf` goal whose endpoint a
  visible merge renames
- **`orthogonal` is not forced-monotonic, and its clash is read by strength**
  ([#129](https://github.com/vaelii/vaelii/issues/129)). CxUniverse states
  `(not (forced_monotonic_predicate orthogonal))`. A forward rule concluding an
  `orthogonal` from a `:default` membership fires, and `violations` reads no
  `:forced-conclusion` entry for the firing. A `:default` `orthogonal` and a `:default`
  separation or `genl` edge of its pair are a dilemma, which `contradictions` lists and
  `kb-integrity` reports. A `:monotonic` separation or edge defeats a `:default`
  `orthogonal`, and a `:monotonic` `orthogonal` stays a hard clash. A
  `siblingDisjointException` over a separated or `genl`-related pair is read the same
  way. A denial of an `orthogonal` is weighed against it by class.
  [nmtms.md](docs/nmtms.md#declarations-over-related-types)
  *Migration:* write a definitional `orthogonal` at `:monotonic`, and state a separation
  or edge `:monotonic` where it is to defeat a `:default` `orthogonal`.
  *Breaks:* `assert` of a forward rule concluding `orthogonal` from a `:default` membership
  *Breaks:* `ask`, `conflicts`, `contradictions`, `subsumption-status`, `kb-integrity` and
  `violations` over a `:default` `orthogonal` or `siblingDisjointException`
- **A mint in a type an arity statement binds to another length is stored and held OUT**
  ([#283](https://github.com/vaelii/vaelii/issues/283)). Under the entailing reading, the
  membership `(T x)`, the edge `(genl x T)` and the `(unary_predicate T)` an argument
  declaration draws are stored in every arrival order of the binding, the declaration and
  the fact, and the binding leaving brings them IN. A record with no other support is OUT
  while the binding stands. `why-not` answers `:inert` for it with its `:support`, and
  `justification-verdicts` and `why` read `:inert` on the held justification.
  [argtypes.md](docs/argtypes.md#where-it-does-not-mint)
  *Migration:* read whether such a membership holds through `ask` or `in?`, not through a
  stored handle.
  *Breaks:* `handle-of`, `why-not`, `justification-verdicts` and `why` over a mint in a type
  bound to another length
- **`edit!`'s `:max-ms` and `:stop?` bound the re-chain its removals release.** A stop
  there refuses the batch (`:interrupted`, `:in :remove`) and rolls it back. The daemon
  holds that re-chain, and `:retract`'s, to `VAELII_MAX_WRITE_MS` once an operator sets it.
  [inference.md](docs/inference.md#stopping-a-run)
  *Migration:* a bounded batch whose removal releases a long re-chain raises its bound.
  *Breaks:* `edit!` with `:max-ms` or `:stop?` over a removal whose release outlasts the
  bound, and a served `:edit` or `:retract` whose release outlasts the write ceiling

### Breaking: contexts

- **Two context NATs a declared order places each below the other through `:monotonic`
  evidence are one class** ([#259](https://github.com/vaelii/vaelii/issues/259)). CxUniverse
  holds their `equals` and no `genlCx` edge between them, so each reads the other's facts
  in either arrival order. Two names stated `intervalEqual` and `subintervalOf` both ways,
  and a range and a calendar term or two ranges with the same `:monotonic` bounds, are such
  pairs. At either strength, retracting one direction's evidence leaves the edge the other
  direction holds.
  [context-nat.md](docs/context-nat.md#two-contexts-ordered-both-ways)
  *Migration:* state at `:default` the evidence of a pair that is to stay ordered one way.
  Read the pair's identity off `equals`.
  *Breaks:* `ask`, `query` and every read at the slice the first order placed above the
  other, which sees the other's facts; `genlCx` between the two, which holds no edge
- **Two context NATs a declared order places each below the other through `:default`
  evidence see neither of each other's facts** ([#259](https://github.com/vaelii/vaelii/issues/259)).
  CxUniverse holds `(contextsOrderedBothWays Ka Kb)`, a new CxUniverse predicate, and no
  `genlCx` edge between the two, in either arrival order. Retracting or defeating one
  direction's evidence leaves the edge the other direction holds. Restating it or
  retracting the defeat takes that edge out again.
  [context-nat.md](docs/context-nat.md#two-contexts-ordered-both-ways)
  *Migration:* retract or defeat the evidence of the direction that is not to hold, or
  state both directions at `:monotonic` for a pair that names one context. Rename a
  relation of your own spelled `contextsOrderedBothWays`.
  *Breaks:* `ask`, `query` and every read at the slice the first order placed below the
  other, which no longer sees the other's facts; `genlCx` between the two, which holds no
  edge; `contextsOrderedBothWays`, which CxUniverse declares
- **A moment's slice is ordered inside a named time's slice by the time's bounds only while
  the time is believed to have no gap** ([#259](https://github.com/vaelii/vaelii/issues/259)).
  The time has none when CxUniverse believes it a `time_interval`, `uninterrupted_time` or
  `time_point`, or a member of a type below one, stated or through its function's
  `(result F t)`. A membership stated in another context orders nothing. A time of no
  stated type, or an `intermittent_time`, holds no moment between its `startOf` and
  `endOf`. A moment inside a believed `(subtimeOf P T)` piece lies inside the slice at `T`
  through the piece.
  [context-nat.md](docs/context-nat.md#the-bounded-r-oracle--no-proof-inside-the-relabel-loop)
  *Migration:* state the time's type in CxUniverse, such as `(time_interval T)`, where its
  bounds hold the moments between them.
  *Breaks:* `ask`, `query` and every read of a moment's slice that saw a named time's
  slice through that time's bounds alone, or through a membership stated outside
  CxUniverse
- **An eternal predicate's fact stated in a time slice is copied into the context the slice
  slices only when that context sees a membership making the predicate eternal.** A
  membership in a context the slice sees and the sliced context does not makes no copy. A
  membership stated in the slice itself still makes one. The upper ontology concludes
  `(eternal_predicate eternal_predicate)`, so the membership is itself copied into the
  sliced context.
  [contexts.md](docs/contexts.md#eternal_predicate-a-fact-stated-in-a-time-slice-holds-in-what-it-slices)
  *Migration:* state the membership in the sliced context, a context it sees, or the
  slice. A durable store written earlier keeps the copies such a membership made; load its
  source into an empty store to drop them.
  *Breaks:* `ask`, `query` and every read at the sliced context of a fact whose eternal
  membership is in a context only the slice sees; `handle-of`, `sentexes-matching` and
  `explain` of its copy
- **A decontextualized fact stated in a slice is copied into the context the slice slices
  only when another membership makes its predicate eternal.** Its CxUniverse copy holds it
  for every context, and a token-table grant storing it no longer names the sliced context.
  [contexts.md](docs/contexts.md#eternal_predicate-a-fact-stated-in-a-time-slice-holds-in-what-it-slices)
  *Migration:* read the fact at the sliced context, or state `(eternal_predicate P)` beside
  `(decontextualized_predicate P)` to keep the copy. A durable store written earlier keeps
  the copy; load its source into an empty store to drop it.
  *Breaks:* `handle-of`, `sentexes-matching` and `explain` of the sliced context's copy

### Breaking: NATs

- **A minted constant's role is read off its length bindings, not its minted name.** A
  `genl` or `genlInverse` between two constants is forced-monotonic when each takes two or
  more places, as under a `(result F binary_predicate)` function, and defeasible under a
  `unary_predicate` one. A name with a capital after its first character read as a
  predicate before, so the class depended on the name. A length stated after the `genl`
  moves it at the next settle. `term-role` answers nil for a `nat/` constant.
  [naming.md](docs/naming.md#a-length-binding-is-held-to-the-spelling)
  *Migration:* read a minted constant's role with `relation?` or `describe`.
  *Breaks:* `term-role` of a `nat/` constant, and the class of a `genl` or `genlInverse`
  between minted constants
- **A minted constant's result types rest on its map and their declaration.** The mint's
  `(T K)` per `(result F T)` and `(genl K T)` per `(genlResult F T)` are derived from `K`'s
  `natFormula` map and the declaration, not stored as premises. Retracting the declaration
  takes them out, and a `:default` declaration gives a `:default` type. A type a caller
  states as well stays a premise. [nat.md](docs/nat.md#write-path)
  *Migration:* state a `result` or `genlResult` declaration `:monotonic` where a minted
  type must be `:monotonic`.
  *Breaks:* `premise?`, `supporting-justifications` and the class of a minted type;
  `retract!` of a `result` or `genlResult` declaration
- **A write through a merged argument or context slot names the constant of its own
  spelling** ([#259](https://github.com/vaelii/vaelii/issues/259)). With `(equals JanA
  JanB)` in CxUniverse, `(likes Ann (FruitFn JanA))` written after a write naming
  `(FruitFn JanB)` was stored with `(FruitFn JanB)`'s constant. It kept that constant after
  the equality was retracted, so it answered for `(FruitFn JanB)` and not for `(FruitFn
  JanA)`, unlike a KB that never stated the equality. A write through `(CxTimeFn CxM
  JanA)` was stored in JanB's slice in the same arrival orders. The write now stores the
  constant of the application or slot as written, minted where none is stated. While the
  equality holds the two constants are one class, and each spelling answers the other's
  facts. A slice at a meet that a stated inclusion absorbs and the slice at the absorbing
  time read apart once the inclusion is retracted, in either arrival order.
  [nat.md](docs/nat.md#a-nat-resolves-under-the-readers-merges)
  *Migration:* none for a query. Code reading the constant in a stored sentence, or the
  `cx/` context a slot write is stored in, gets the constant of the spelling written.
  *Breaks:* `sentex` and `sentexes-matching` of a sentence written through a merged
  argument; the context `assert` stores a write through a merged slot in; the `natFormula`
  rows, one constant per spelling written

### Breaking: assert

- **`assert` and `check` refuse an upper bound on the start of the real world's present as
  `:exact-present`** ([#259](https://github.com/vaelii/vaelii/issues/259)). In the slice
  `(CxTimeFn CxRealWorld (IntervalAfterFn W))` and every context below it,
  `(instantBefore W T)`, `(instantNotAfter W T)`, `(instantAfter T W)` and
  `(instantNotBefore T W)` with T other than W are refused, and so is a `genlCx` edge
  placing a context that holds one under the present. Each was stored, and a later clock
  reading past T contradicts it.
  [time.md](docs/time.md#the-real-worlds-present)
  *Migration:* state a clock reading as `(instantNotBefore W T)`, and retract a stored upper
  bound on the present's start below the present.
  *Breaks:* `assert` of `instantBefore`, `instantNotAfter`, `instantAfter` or
  `instantNotBefore` bounding the real world's present's start from above, in the present
  or below it

### Breaking: integrity

- **`vocabulary-audit` reads its population from the KB.** core.txt declares
  `definitional_predicate`. Its members are the predicates a term's definitional block is
  written in. They are `comment` and the example annotations, `genl`, the separations,
  the orders, the relation and rigidity kinds, `eternal_predicate`, `arity` and the arity
  classes, and the argument declarations. The
  algebraic relation properties, `termsRelated` and `seeAlso` are members too. The audit
  classifies those members and the `syncategorematic` constants
  (`Quote` and the `set/*` wrappers), answered in CxUniverse, where it classified every
  term core.txt comments. A membership a `genl` edge or a rule derives counts as a stated
  one: `(genl type_type_by_order definitional_predicate)` makes `type`, `metatype` and
  `meta_metatype` members. New collections below `definitional_predicate` hold most of
  the rest: `ontology_predicate` holds `genl`, `genlCx`, `inverse` and the separations,
  `wff_predicate` the well-formedness declarations, and `algebraic_predicate_property` the
  relation properties, including the per-position ones such as `functionalInArg`.
  `wff_predicate` is partitioned into `wff_constraint`, the argument declarations, and
  `wff_satisfaction_predicate`, the result declarations. A
  forward rule over each of `relationTypeByArity`, `predicateTypeByArity` and
  `functionTypeByArity` makes the fifteen exact-arity classes members. The `at_least`
  classes are not members. `definitional_predicate`, the five collections below it and
  `decontextualized_predicate` are each a `closed_extent_predicate`, so a predicate the KB
  does not make a member is refuted as one: `(not (decontextualized_predicate P))` now
  answers true of an undeclared `P`. `decontextualized_predicate` is now a `genl` of
  `forced_decontextualized_predicate`. A grammar term in neither, such as `except` or `equals`, is no
  longer listed under `:enforced` or `:inert`; `interpreted` still answers for it.
  `:retired` names a classification entry for a term no believed `comment` in the KB names,
  so a term commented in any upper file, such as time.txt's `functional_at_instant`, can be
  classified.
  `diachronicallyDisjoint` is declared in time.txt, which loads into CxUniverse beside core.txt.
  *Migration:* ask `interpreted` of a grammar term outside the population, or mark a
  block predicate a KB adds `definitional_predicate` so the audit asks it to be answered for.
  *Breaks:* `vocabulary-audit`
  [predicates.md](docs/predicates.md#reading-the-answer-back)
- **The undeclared-arity sweep reports a `genl` node whose only length is inherited.** A
  node passes when the node itself is known to have an exact length, or when a
  `variable_arity` membership releases it. The node's own exact length comes from an
  engine `:shape`, an `(arity P n)`, an exact-arity class membership such as
  `unary_predicate`, or a `:monotonic` membership reaching one. Under `(unary_predicate placed_kind)` and `(genl below_kind placed_kind)`,
  `below_kind` is an `:undeclared-arity` finding, and a default `kb-integrity` sweep of
  such a KB answers `:gap`. The upper and middle files declare `(unary_predicate X)` beside
  each type's definition, so neither the upper ontology alone nor the starter has a
  finding. The new `arity/own-length` reads the node's own length with no
  `genl` closure read; `arity/relation-length` and its callers keep the inherited length.
  [integrity.md](docs/integrity.md#what-an-undeclared-arity-finding-means)
  *Migration:* state an arity of each `genl` node, such as `(unary_predicate below_kind)`.
  *Breaks:* `kb-integrity`

### Refusal: serving

- **A token-table grant removes a sentex only where storing it would write, and withdraws
  no conclusion outside `:writes`.** `:retract`, an `:edit`'s `:remove` and the premises
  `:replace-facts` retracts are held to the contexts storing the sentence writes. Each
  sentex the removal takes out of belief is held as a rule's conclusion is after a write.
  Accepting such a removal withdraws content from a context the grant cannot write. The
  check runs under the write's bound, so a removal whose re-chain the bound ends is
  refused `:interrupted` before it writes.
  [operations.md](docs/operations.md#the-token-table)
  *Migration:* add the context the 403 names to the grant, or remove under an admin grant.
  *Breaks:* a served removal of a slice's eternal-predicate fact, a `natFormula`, a
  `genlCx` edge, or a premise a rule's out-of-grant conclusion rests on, under a grant
  not naming those contexts
- **A token-table grant writing or removing a `natFormula` for a `cx/` constant names each
  context its `contextArgSubrelation` pairs order below the constant.**
  [operations.md](docs/operations.md#the-token-table)
  *Migration:* name those contexts in the grant, or write the `natFormula` under an admin
  grant.
  *Breaks:* a served `natFormula` for a `cx/` constant that orders a context the grant does
  not name below it

### Additive: inference

- **A forward rule reads the type a function's `result` declaration gives an
  application** ([#226](https://github.com/vaelii/vaelii/issues/226),
  [#259](https://github.com/vaelii/vaelii/issues/259)). An antecedent the rule writes as
  `(k (F a…))` holds, once its application is ground, when a stored `(result F t)` or
  `(resultArg F n)` gives the application a type at or below `k`, as `ResultTypeProver`
  answers the goal. A rule with a `(time (YearFn ?y))` antecedent fires for each year
  another antecedent binds. The firing rests on the declaration and the `genl` edges it
  climbs, and a declaration or an edge arriving last re-joins the rule.
  [inference.md](docs/inference.md#a-type-an-applications-function-declares)
- **A moment before W is inside `(IntervalBeforeFn W)` with no bound stated**
  ([#258](https://github.com/vaelii/vaelii/issues/258)). The point network and the order
  over time points read `(IntervalBeforeFn W)` as ending at W with no start, and
  `(IntervalAfterFn W)` as starting at W with no end. So the slice at an `InstantFn`
  moment before W is ordered below the slice at `(IntervalBeforeFn W)` and sees a
  `closed_extent_predicate` grant stated there, and `includesInstant` answers true for a
  moment before W. A read of a slice nobody wrote into finds both kinds of slice above it.
  [time.md](docs/time.md#naming-an-interval-the-calendar-constructors)
  *Migration:* none.
- **A ground Allen goal reads its two intervals' stated bounds**
  ([#258](https://github.com/vaelii/vaelii/issues/258)). With `:allen` registered,
  `(meets (IntervalBeforeFn W) (IntervalAfterFn W))`, and `(during I J)` over two intervals
  whose `startOf` and `endOf` name `InstantFn` moments, answered `:unknown`. A ground goal
  the interval network leaves undecided now reads the order over the two intervals' points
  and stated bounds, and answers the relation that order entails. A forward rule on an
  Allen literal fires on the interval network alone. An `overlapDuration` answer the
  reading narrows rests on the stated bounds it read, and `why` names them.
  [time.md](docs/time.md#the-points-of-a-temporal-thing)
  *Migration:* none.
- **`DatetimeFn` names an interval shorter than a second**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). A fractional second of one to
  nine digits behind a zero-padded date and time names an interval of that many decimal
  places of a second, so `(DatetimeFn "2000-01-15T13:00:00.123")` is one millisecond. It
  nests inside its second and each fraction of fewer digits, `meets` `.124`, and its
  `StartFn` and `EndFn` are ordered against every calendar moment in no zone. A meet of
  two such terms that share no time is refused as `:not-well-formed`, as a meet of two
  disjoint days is. The clock answers no `startOf` or `endOf` for a sub-second term, and
  the metric network places no moment between two seconds.
  [time.md](docs/time.md#the-calendar-clock)
  *Migration:* none.
- **`set/oneJustificationRule` keeps one stored justification per conclusion of a
  forward rule.** A firing that a stored justification of the same rule outranks at
  every reader stores nothing, and a reader believes what it believes under the
  unwrapped rule, at the same class. CxUniverse's intersection generator wraps the
  membership rule it generates, so `why` of a membership lists one firing where it
  listed one per pair of subtypes.
  [inference.md](docs/inference.md#a-rule-that-stores-one-justification-per-conclusion)
- **`retract!` and `vaelii.client/retract!` take `:max-ms`, `:stop?` and
  `:max-derivations`** (`retract-opt-keys`).
  The bound holds until the first deletion and covers the re-chain the removal releases:
  a stop refuses the call (`:interrupted`) and leaves the KB as the call found it, the
  retracted premise still stored and believed.
  [inference.md](docs/inference.md#stopping-a-run)
  *Migration:* none.
- **`settle-record-edits!` takes `:max-ms`, `:stop?` and `:max-derivations`.** The bound
  covers the chain and the re-chain of its sweep. A stop removes what those steps created
  and throws `:interrupted`, and a second call over the same `:seeds` runs them again.
  [storage.md](docs/storage.md#editing-the-records-of-a-kb-without-belief)
  *Migration:* none.

### Additive: shipped ontology

- **life.txt ships `may` and `can` beside `able`.** `(may ?doer ?kind)` is deontic
  permission to be the doer of a happening of kind `?kind`, and `(can ?doer ?kind)` is
  ability and permission together. Both take `able`'s positions: `(arg … 1 causal)`,
  `(genlArg … 2 happening)` and `transitiveInArg` along `genl` on the second. Both are
  `time_varying_relation`, since an ability or a permission can be gained and lost. life.txt
  states `(intersection can able may)`, so `able` and `may` together conclude `can`, and
  `can` is `genl` each half. Ability without permission, or permission without ability,
  concludes no `can`.
  [inherit.md](docs/inherit.md#six-predicates-ship-with-one)
  *Migration:* none; `may` and `can` are new.
- **`intersection` relates binary predicates as well as kinds.** `(intersection P A B)`
  and `(intersection P A B C)` over binary predicates derive `(genl P A)` and the other
  edges as over kinds, and a generated membership rule concludes `(P x y)` from `(A x y)`,
  `(B x y)` and, for three, `(C x y)`. The binary rule is generated where `P` has arity 2.
  The unary rule is generated where `P` is a member of a class `relationTypeByArity` maps
  to 1: `unary`, which holds a kind declared `unary_predicate` or given `(arity P 1)`, or a
  KB's own class. A binary predicate generates no unary rule. The membership is strict,
  and a `genl` edge between predicates is forced-monotonic, so a binary intersection is
  stated `set/monotonic`.
  [integrity.md](docs/integrity.md#what-a-rule-macro-finding-means)
  *Migration:* none.
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

### Additive: contexts

- **An equality between two contexts stated in CxUniverse joins their extents**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). Each sentex stored in a context
  the equality retires is restated in the class's representative, and a read at either
  name reads there. A context below either name sees both extents, and retracting the
  equality splits them again. Two monads stated equal read each other's slices' facts in
  either arrival order, and so do two named times stated equal. A token-table grant
  writes or removes such an equality, or writes a fact the engine derives one from, only
  when it names every context of the classes it joins.
  [equality.md](docs/equality.md#two-names-of-one-context)
  *Migration:* none.

### Additive: NATs

- **A constant `(rewriteOf Root (F a))` names takes the application's `natFormula` and
  result types** ([#277](https://github.com/vaelii/vaelii/pull/277)).
  `F` is a `reifiable_function`, and a fact names `Root` or `(F a)`. The KB derives
  `(natFormula Root (F a))` and the types `F`'s `result` and `resultArg` declarations give
  `Root`, at a context that sees both facts, in either arrival order. It mints no
  constant. Retracting the `rewriteOf` or the last such fact withdraws them, and so does a
  second `rewriteOf` naming another constant for `(F a)`.
  A write naming `Root` beside 1,600 other uses reads 57 sentexes and 2 justifications.
  [nat.md](docs/nat.md#an-application-as-a-sentences-predicate)
  *Migration:* none.

### Additive: integrity

- **The rule-macro sweep reports a conjunction rule as the `intersection` it spells.** A
  rule `(A ?x)`, `(B ?x)` ⇒ `(P ?x)`, or the same over two arguments or with a third
  component, is a `:rule-macro` finding suggesting `(intersection P A B)`, where `P` and the
  components are distinct, uninterpreted and of the rule's arity. CxTra's
  `nestingPartnerOf` rule is one, and CxTra acknowledges it. The unary membership rule an
  intersection generates would spell its camelCase relations with one argument, which the
  naming check refuses. [integrity.md](docs/integrity.md#what-a-rule-macro-finding-means)
  *Migration:* acknowledge or replace a conjunction rule the sweep now reports.
- **`kb-integrity` reports a `genl` edge whose spec admits a length its genl does not.**
  The default sweep adds `:genl-arity-mismatch`, one `{:spec a :genl b :spec-arity …
  :genl-arity …}` per visible `(genl a b)` whose ends each have an arity of their own
  (`arity/own-length`) and where `a` admits a length `b` does not
  (`arity/admits-length?`). An exact length admits itself alone, and a `variable_arity`
  release every length at or above its `arityMin`. `(genl <unary> <variable_arity>)` is
  not a finding, and `(genl <variable_arity> <unary>)` is one; a floor of 2 under a floor
  of 3 is one, and a floor of 3 under a floor of 2 is not. An end with no arity of its
  own is an `:undeclared-arity` finding instead. The shipped starter has no finding.
  [integrity.md](docs/integrity.md#what-a-genl-arity-mismatch-finding-means)
  *Migration:* state agreeing arities at both ends of a reported edge, or drop the edge.

### Additive: API

- **`rename-terms!`, `merge-terms!`, `copy-terms` and `remove-terms!` change a term in
  every premise that uses it, as one `edit!`.** A rule, a context's extent, a reified NAT
  built from the term and a meta naming a restated premise are restated with it, and a
  quotation keeps its spelling. A constant a `natFormula` premise in CxUniverse maps under
  a name other than its content name keeps that name, and its map is restated as written.
  An operation reaching a `natFormula` premise stored outside CxUniverse is refused as
  `:nat-map-outside-universe`. `:stop?` and `:max-ms` bound an operation until its first
  deletion, and a stop rolls it back. A rename, merge or copy that would take a belief its
  substitution does not carry is refused as `:lost-belief` and rolled back.
  `check-term-edit` answers the refusals before the write, among them `:shipped-term` for a
  term the shipped ontology names, and `term-edit-plan` the batch.
  The daemon serves those two reads. Each operation has a one-term form.
  *Migration:* none. [api.md](docs/api.md#contract-notes-term-operations)

### Additive: browser

- **`vaelii.web/page` draws an extension's route as a page of the browser**: the header,
  the menubar and the stylesheets on a plain request, the `#main` region when htmx asks.
  A route answering hiccup is still sent as a fragment, which a menubar link swapped in
  as nothing. [web.md](docs/web.md#extensions)
  *Migration:* none.
- **A reified NAT's parens are violet and a structural NAT's are white.** The arguments of
  a `Quote` or `Quasiquote` dim as an OUT sentence does, and an `Unquote` hole inside a
  `Quasiquote` returns to the sentence's colour.
  [web.md](docs/web.md#a-reified-term-is-never-shown-as-its-constant)
  *Migration:* none.

### Fix: answers

- **A context that excepts an equality reads each use of a merged application under the
  name it was written with** ([#259](https://github.com/vaelii/vaelii/issues/259)). With
  `(likes Ann (FruitFn JanA))`, `(likes Bob (FruitFn JanB))` and `(equals JanA JanB)` in
  `CxP`, and an `except` of the equality in `CxR` below it, `CxR` answered `(likes Bob
  (FruitFn JanA))` true. In the arrival orders ending with the `except`, it answered the
  use whose constant the collision repair did not keep false under its own name.
  [equational.md](docs/equational.md#an-except-of-an-equation)
  *Migration:* none.
- **`contradictions` at a context application reads the context it names**
  ([#258](https://github.com/vaelii/vaelii/issues/258)). `(contradictions kb (CxTimeFn
  CxGitHub T))` answered `[]` while `(contradictions kb K)`, with `K` the `cx/` constant the
  application names, reported the clash placed there. Both now report it.
  [context-nat.md](docs/context-nat.md#write-and-read-are-symmetric)
  *Migration:* none.
- **`term-expression` answers a retired constant's expression through its representative.**
  A constant an equality retired answered nil, since the read kept only the `natFormula`
  rows naming the constant itself, and the match answers the representative's rows.
  [nat.md](docs/nat.md#display--export)
  *Migration:* none.

### Fix: order independence

- **A guard defeat lands at a reader that hides a `reifiable_function` mark**
  ([#289](https://github.com/vaelii/vaelii/issues/289)). CxA states
  `(reifiable_function Quote)` and `(exceptWhen (blocked ?q) R)`, and `R` fires over
  `(said Tom (Quote Muffet))`. CxB, below CxA, hides the mark and states
  `(blocked (Quote Muffet))`. CxB believed R's conclusion in some arrival orders when it
  denies the mark, and in all when an `except` hides the mark. CxB now reads the
  conclusion defeated, as when no context states the mark.
  [nat.md](docs/nat.md#a-reifiable-mark-moving)
  *Migration:* none.
- **A guard defeat lands at a reader that hides a `sameAs` merge**
  ([#289](https://github.com/vaelii/vaelii/issues/289)). CxA states `(sameAs Robert Bob)`
  and `(exceptWhen (blocked ?q) R)`, and `R` fires over `(said Tom Robert)`. CxB, below
  CxA, hides the merge and states `(blocked Robert)`. CxB believed R's conclusion in the
  orders where the `except` arrived after the fact. CxB now reads the conclusion
  defeated, as when no context states the merge.
  [nmtms.md](docs/nmtms.md#the-other-half-a-spelling-an-un-merge-gives-back)
  *Migration:* none.
- **A derived closed-extent grant that would close a cycle through negation is dropped**
  ([#275](https://github.com/vaelii/vaelii/issues/275)). The grant is a
  `closed_extent_predicate`, `closedExtentForArg` or binary-spelling grant that a forward
  rule concludes or an argument-type mint entails. When it would close a cycle with a
  stored rule, it is dropped and reported in `violations` as `:not-stratified`, as a
  derived `genl` edge is, and closes no extent. `assert` refuses a stated grant in the
  same case.
  [naf.md](docs/naf.md#stratification-from-both-arrival-orders)
  *Migration:* none.
- **A grant or `genl` edge dropped for a cycle through negation is stored once the cycle
  opens** ([#275](https://github.com/vaelii/vaelii/issues/275)). Retracting the rule that
  closed the cycle left the derived grant or edge dropped, where a KB built without that
  rule stores it. The twin an equality restatement stores of a grant or edge took no
  stratification check, so `(rewriteOf P Q)` beside `(closed_extent_predicate Q)` stored
  `(closed_extent_predicate P)` beside a rule its grant closes a cycle with. A dropped
  conclusion now stays listed in `violations` after `clear-violations!`, while the cycle
  holds.
  [naf.md](docs/naf.md#stratification-from-both-arrival-orders)
  *Migration:* none.
- **A rule stored before a derived correspondence is respelled through it**
  ([#271](https://github.com/vaelii/vaelii/issues/271)). With `(implies (tagged (FruitFn
  ?t)) (ripe ?t))` stored before `(functionCorrespondingBinaryPredicate FruitFn fruitOf)`,
  the rule stayed held and `(ripe ?t)` answered nothing. It now answers `AppleTree` from
  `(fruitOf AppleTree Gala)` and `(tagged Gala)` in every arrival order, and the
  respelling goes when the declaration does. A `preview` adding a correspondence no longer
  leaves a held rule respelled after its rollback.
  [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* none.
- **A rule is respelled when a declaration a firing concludes turns valid or void**
  ([#271](https://github.com/vaelii/vaelii/issues/271)). A forward rule concluding
  `(functionCorrespondingPredicate FruitFn fruitOf 2)` from `(source FruitFn fruitOf)` fires
  void until `source` is `forced_monotonic_predicate`. With the rule over `(FruitFn ?t)`
  stored before the forcing, it stayed held and `(ripe ?t)` answered nothing; with the
  forcing retracted, it stayed respelled and answered `AppleTree`. The rule now follows the
  declaration's belief in every arrival order.
  [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* none.
- **A correspondence an `except` hides is not read below the except**
  ([#271](https://github.com/vaelii/vaelii/issues/271)). With
  `(functionCorrespondingPredicate FruitFn fruitOf 2)` in CxUniverse and an `except` of it
  in CxHid, a rule `(implies (tagged (FruitFn ?t)) (ripe ?t))` in CxHid was respelled
  through the declaration, and `(ripe ?t)` and `(tagged (FruitFn ?t))` answered
  `AppleTree` there. CxHid now reads both as a KB without the declaration: the rule stays
  held and neither answers. The except arriving or leaving, or a `genlCx` edge that shows
  or hides it, respells the rules below it in every arrival order.
  [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* none.
- **Retracting a rename splits the reified constants its collision merged**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). The collision repair's merge is
  derived under the informant `natFormula` from the two `natFormula` rows and the `genlCx`
  edges its context sees them over. After the rename is retracted, the two constants are
  two classes, as in a KB that never stated the rename. Retracting one `genlCx` edge the
  merge was drawn over keeps the merge, and each merge it restates, while another route to
  the two rows remains, as in a KB that never stated that edge.
  [nat.md](docs/nat.md#rename-and-remove--keeping-the-11-invariant)
  *Migration:* none.
- **A firing held by a separation comes IN when a defeat of the separation arrives**
  ([#283](https://github.com/vaelii/vaelii/issues/283)). Under the constraint-only
  reading, with `(disjoint poodleKind animal)` at `:default` and `(arg ownsPet 2 animal)`,
  a rule's `(ownsPet Ann Rex)` from `(poodleKind Rex)` stayed held after a `:monotonic`
  `(genl poodleKind animal)` defeated the separation. The same edge arriving first let the
  firing through. The conclusion is now IN in both arrival orders.
  [argtypes.md](docs/argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert)
  *Migration:* none.
- **A refusal recorded before a `reifiable_function` mark stays one refusal after it**
  ([#289](https://github.com/vaelii/vaelii/issues/289)). A closed-extent refusal recorded
  with `(Quote RM1)` bound counted twice in `rule-firing-report` once the mark arrived. It
  now reads as one refusal, as when the mark arrives first.
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings)
  *Migration:* none.
- **A rule storing one justification per conclusion stores one where some arrival orders
  left two** ([#259](https://github.com/vaelii/vaelii/issues/259)). A firing placed in a
  context below one holding the same conclusion stored a justification in one arrival
  order and none in the other. A conclusion kept a justification resting on a second
  conclusion after a premise gave the second conclusion support. Belief was the same in
  every arrival order.
  [inference.md](docs/inference.md#a-rule-that-stores-one-justification-per-conclusion)
  *Migration:* none.
- **A rule storing one justification per conclusion places no re-asked firing that rests
  on provers alone, and drops no justification its conclusion rests on**
  ([#259](https://github.com/vaelii/vaelii/issues/259)). Retracting
  `(declined_rule_macro (Quote S))` in one of two contexts placed
  `(closed_predication (Quote S))` in CxUniverse, which sees no statement of the quoted
  sentence. The test world loaded back through `load-text!` held 15 such sentexes that
  the exported world did not. Two such rules whose conclusions satisfy each other's
  antecedents lost both conclusions.
  [inference.md](docs/inference.md#a-rule-that-stores-one-justification-per-conclusion)
  *Migration:* none.

### Fix: inference

- **A conviction reaching a `:default` edge's head over `:monotonic` edges undercuts the
  reading there.** With `(genl beast mortal)` at `:default`, `(genl mortal perishing)` at
  `:monotonic`, `(beast Hydra)` and a denial of `(perishing Hydra)` or a separated
  `(immortal Hydra)`, `(mortal Hydra)` and `(not (mortal Hydra))` both answered true, a
  forward rule on `mortal` fired, and nothing was reported. `(mortal Hydra)` now answers
  false.
  [inference.md](docs/inference.md#an-edges-reading)
- **An `exceptWhen` or `unknown` guard reads an undercut edge reading as not holding.**
  With `(genl beast mortal)` at `:default`, `(beast Hydra)` and `(not (mortal Hydra))`,
  `ask?` answered `(mortal Hydra)` false while an `(exceptWhen (mortal ?x) R)` guard read
  it true and blocked `R`. The guard now reads what `ask?` reads. A guard whose blocker is
  a reading the guarded conclusion undercuts takes the content order of a
  defeat-dependency cycle.
  [inference.md](docs/inference.md#an-edges-reading)
- **A backward rule's head answers every argument order its permuting marks allow.**
  Under `(symmetric bordersOn)` and `(implies (listed ?y) (bordersOn ?y Bob))` with
  `(listed Ann)`, `(bordersOn Ann Bob)` was provable and `(bordersOn Bob Ann)` was not.
  The same held for a commuting predicate and for a `commutative` function applied in the
  head. A goal now gets the answers its stored-fact twin gives, in every spelling.
  [canonicalization.md](docs/canonicalization.md#a-rule-head-matched-in-every-order)
- **A forward rule's antecedent joins an `inverse` partner's facts.** Under `(inverse
  childOf parentOf)` with `(childOf C0 P0)`, `ask?` answered `(parentOf P0 C0)` and a
  forward rule on `(parentOf ?p ?c)` fired on nothing, in every arrival order. The rule
  now fires, and its justification names the `inverse` declaration and the fact. A
  backward rule concluding `parentOf` answers a `childOf` goal too.
  [inference.md](docs/inference.md#genlinverse-the-fan-with-the-arguments-swapped)
- **A firing over a swapped reading names the swap edges it crossed, and a retracted swap
  edge re-fires over a second route.** Under `(genlInverse P P)`, or a predicate the fan
  reaches both by `genl` and across a `genlInverse` edge, the swapped reading's conclusion
  named no swap edge and stayed believed after the edge was retracted. Retracting one of
  two swap routes left a conclusion OUT that the other route still licensed.
  [inference.md](docs/inference.md#genlinverse-the-fan-with-the-arguments-swapped)
- **A defeated or excepted swap edge leaves a firing a second swap route licenses.** A
  forward conclusion over a `genlInverse` edge a denial defeats, or over a `genlInverse`
  edge or an `inverse` declaration an `except` hides, stayed OUT where a second swap route
  still licensed it. Under a defeat it stayed IN only where the edge arrived after the
  second route.
  [inference.md](docs/inference.md#genlinverse-the-fan-with-the-arguments-swapped)
- **A retracted merge of two reified constants leaves with the facts spelled through it.**
  With `(functionCorrespondingPredicate LeaderFn leaderOf 2)`, `(functional leaderOf)` and
  a premise from which `(leaderOf Blues (LeaderFn Reds))` follows, the two constants merge.
  In some arrival orders `(leaderOf Reds (LeaderFn Reds))` answered false, and after the
  premise was retracted `(admires Ann (LeaderFn Blues))` still answered true for a stated
  `(admires Ann (LeaderFn Reds))`. A firing naming `(LeaderFn Blues)` after the merge kept
  the other constant after the retraction. Each now answers from the map or premise it was
  written from.
  [nat.md](docs/nat.md#a-nat-resolves-under-the-readers-merges)
- **A rule over two open expression kinds of one variable joins once per kind.** Each
  kind antecedent leads a join of its own and the rows are unioned, so a member that
  holds a kind only by its spelling is joined whichever kind a plan runs first. The
  unary intersection rule over `predication` and `closed_expression` holds the same
  firings over a quoted member in every arrival order.
  [inference.md](docs/inference.md#what-a-computed-answer-rests-on)
- **A `genl` edge no block literal reaches no longer throws over a refused firing.** With
  a firing of `(implies (and (tag ?k T) (not (member ?k)) (unknown (genl ?k base))) …)`
  refused under a `closed_extent_predicate` grant on `member`, asserting a `genl` edge
  between two other types threw a `NullPointerException` from the settle. The edge now
  keeps the refusal, and the release still places the firing.
  [exceptions.md](docs/exceptions.md#narrowing-the-re-check-to-the-firings-a-trigger-can-reach)
- **A forward rule's `(k ?x)` antecedent with `?x` open runs after the antecedent that
  binds `?x`, with the planner on or off** ([#259](https://github.com/vaelii/vaelii/issues/259)).
  Under time.txt's `(implies (and (time ?a) (time ?b) (partOf ?a ?b)) (subtimeOf ?a ?b))`,
  `VAELII_PLAN=0` joined `(time ?b)` ahead of `(partOf … ?b)`, so a write naming one time
  read every stored fact mentioning a calendar term. The literal now waits for a binder
  that is neither such a literal nor costed at `plan/unbounded`.
  [inference.md](docs/inference.md#a-type-an-applications-function-declares)

### Fix: contextual type definitions

- **A forced arity-class store in CxUniverse does not move a type's defining context.**
  `arity`, `arityMin` and the arity classes are `forced_decontextualized_predicate`s, so a
  middle theory's `(unary_predicate T)` is stored in CxUniverse. `defining-contexts` reads
  such a record as a home only when no other leaf gives the term one. A type or relation
  a middle theory defines therefore keeps that theory as its home. Its rigidity class
  stated there satisfies `(typeAllSpecified rigidity_kind relation)`.
  [api.md](docs/api.md)
  *Migration:* to define a relation in CxUniverse, state something other than its arity
  there, such as its `comment`.

### Fix: performance

- **A chain beside an `except` of an unrelated fact costs time linear in its length.**
  While any `except` was stored, each firing walked its antecedents' whole supports twice.
  An assert chaining 2,000 links beside one unrelated `except` took 10,956 ms against
  305 ms without it, and a `retract!` releasing the chain took 11,703 ms against 401 ms.
  A chaining run now holds, per handle, whether a stored `except` names a handle of its
  support. The same assert takes 446 ms and the release 515 ms. A `preview` removing the
  `except` that hid the chain's first link takes 19 s at 2,000 links against 45 s, since
  an `except` it suspends names nothing for that check.
  [contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree)
  *Migration:* none.
- **A justification added to a conclusion holding n supports no longer reads the n.** The
  dedup check, the replaced-route drop and the defeat walk each read every support of the
  conclusion. The nth fact naming one calendar moment read about 4n supports and 2n
  justifications, at n = 100, 1000 and 2000; it now reads one support, three dependents
  and six justifications at each. `lein perf`'s `calendar-re-mention` holds the 4000th
  fact within 1.3x of the 100th, which read 1.84x before
  ([#259](https://github.com/vaelii/vaelii/issues/259)).
  [inference.md](docs/inference.md#what-a-run-pays-per-witness-chainagenda-arrivals)
  *Migration:* none.
- **A backward goal no longer reads the rules whose conclusion its arguments cannot
  match.** A goal `(p A B)` read the record of every rule concluding `p` or a spec of it,
  including a rule concluding `(p (F K) B)`. Beside 100 such rules the goal read 104
  records, and 14 beside 10; it now reads 14 beside either. A disk store's index is
  rebuilt once on open (index layout 23).
  [indexing.md](docs/indexing.md#3-the-rule-index)
  *Migration:* none.
- **A write or a settle reads each rule, declaration and owing datum it needs once.** Ten
  writes and queries beside 100 rules reading a forced-monotonic predicate read 40
  records, 1,040 before. Ten writes naming an application beside 100
  `functionCorrespondingPredicate` declarations read 280 records, 3,310 before. Ten
  `genl` edges beside 100 rules reading `genl` read 1,030 records, 2,030 before. A
  lazy-forward rule's re-join reads each owing datum once per settle, not once per join
  state and lazy rule, and each rule reading its conclusion once per run, not once per
  owing datum.
  [inference.md](docs/inference.md#a-lazy-forward-rule)
  *Migration:* none.
- **A `recover` over rules carrying a block condition takes less time.** With a
  few hundred rules carrying a block condition, a recover takes 45.3 s against 82.6 s.
  [exceptions.md](docs/exceptions.md#re-chaining-what-was-released-not-what-was-touched)
  *Migration:* none.
- **A `recover` rebuilds the refusals of a rule whose only condition is `different` in
  less time.** On 4,850 sentexes with one such rule over 4,000 placed firings, the
  rebuild takes 0.007 s against 0.239 s, and records the same refusals.
  [exceptions.md](docs/exceptions.md#a-recover-re-fires-a-different-rule-from-seeds)
  *Migration:* none.
- **A `genlCx` edge reads only the `natFormula` rows it can join into a collision.**
  While any equality was stored, the collision repair after an edge read every
  `natFormula` row below the edge's lower context. An edge joining one collision over
  1,024 rows below it took 6.16 ms against 2.89 ms over 64; it now takes 1.55 ms against
  1.08 ms. The repair leaves a collision between rows below the lower context that the
  edge does not join, as it leaves an imported one.
  [nat.md](docs/nat.md#rename-and-remove--keeping-the-11-invariant)
  *Migration:* none.

### Internal: CI

- **A CI shard runs its recurring failures first**
  ([#280](https://github.com/vaelii/vaelii/issues/280)). `scripts/ci-shard.sh` reads the
  checked-in `scripts/ci-test-history.tsv` and orders each shard's namespaces by
  recurring-failure count, then weight, then name. Which shard a namespace is in does not
  change, and every shard still runs every namespace it is given. A history that is
  missing, stale or malformed is ignored whole, for the lightest/heaviest order shards
  ran before.
- **Every CI shard builds the shared test dumps first, in a namespace of its own.** A
  test JVM builds the starter dump once, about 70 s on CI, and the upper-ontology dump
  once, each inside whichever namespace loads it first. The `weights` check then read
  that namespace as slow: `vaelii.orthogonal-test` took 139 s against 46 s on the
  disk-log leg in [#265](https://github.com/vaelii/vaelii/pull/265).
  `scripts/ci-shard.sh` now prints the new `vaelii.shared-dumps-test` first in every
  shard, outside the packing, so its row takes both builds. The check judges no
  shard's first row, so it does not judge this one.
- **`weights` is a required check on `develop`, and judges each namespace's smallest time
  over three runs, past each shard's first row.** A namespace that runs first in a JVM
  also pays the JVM's and the KB's start-up, about 70 s on CI, so `scripts/ci-weights.sh`
  judges every row but the first of each shard's timings. A namespace over its weight is
  run three times in one JVM (`VAELII_TEST_NS_REPEAT`) and judged by its smallest time;
  the rerun is skipped when it is predicted not to finish 2 minutes before the shard
  job's 45-minute timeout. A check with no cached baseline reads the committed
  `scripts/ci-test-weights-<leg>.tsv`, and the steps that write and save the next run's
  weights do not decide the verdict. A row a change sets in that file, differing from the
  file at the change's base revision, raises the namespace's figure in the check and in
  the weights the run saves; `scripts/ci-weights.sh <run-id>` rewrites both files from a
  run. [CONTRIBUTING.md §7](CONTRIBUTING.md#7-commits--pull-requests)

## 0.33.0 — 2026-11-10 — "A separation undercutting a `:default` edge's reading, shipped type edges at `:monotonic`, relations classified by rigidity, a three-argument `functionCorrespondingPredicate`, daemon reads held to their ceilings, a time slice seeing the context it slices"

**118 entries** — 19 Breaking, 9 Refusal, 43 Additive, 42 Fix, 5 Internal. A separation,
or denials of every part of a cover, undercuts a `:default` `genl` edge's reading of a
membership, and the shipped type `genl` edges are `:monotonic`, except three. `core.txt`
partitions `relation` into rigidity kinds, `functionCorrespondingPredicate` takes three
arguments, and a write naming an application stores the application's constant. The
daemon holds its clocked reads to `VAELII_MAX_QUERY_MS` and its proofs to
`VAELII_MAX_QUERY_DEPTH`. A time slice sees the context it slices, a fact of an eternal
predicate stated in a slice holds in the context the slice slices, and slices are ordered
through their times' points.

*Breaks:* `ask`, `query`, `argue`, `conflicts`, `contradictions`, `:default`, `:assert`,
`:forbidden-context`, `why`, `:monotonic`, `prove`, `natFormula`, `holdsAt`,
`timeIntersectionOf`, `(arity TimeIntersectionFn 2)`, `assert`, `genlMonad`,
`monad_context`, `cxMonadOf`, `cxTimeOf`, `argN`, `premise?`, `prStatus`,
`pull_request_status`, `PullRequestDraft`, `PullRequestReady`, `PullRequestMerged`,
`PullRequestClosed`, `largerThan`, `functionCorrespondingPredicate`,
`(variable_arity_predicate functionCorrespondingPredicate)`,
`(arityMax functionCorrespondingPredicate 3)`, `find-sentexes`, `find-sentexes-all`,
`not`, `and`, `implies`, `terms`, `term-count`, `:naming :warn`, `:off`,
`vaelii.serve/app`, `vaelii.web/handler`, `:token`, `defeat`, `:lookup`, `:query`,
`:query?`, `:argue`, `:prove`, `:provable?`, `:prove-within`, `:max-depth`, `:escalate`,
`:max-ms`, `assert-inert`, `load-text!`, `(set/inert …)`, `genl`, `except`, `do/`,
`TimeIntersectionFn`, `(sentexHandle N)`, `check`, `.`, `:dot-marker`, `open-kb`,
`reasoners.edn`

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
