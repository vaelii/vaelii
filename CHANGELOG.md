# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.35.0 are summarized rather than reproduced.** Each one
keeps its title and its class census, and each one from 0.14.0 on keeps every
`*Breaks:*` token, so an upgrade across those releases is still a grep for the name you
call; 0.8.0 through 0.13.0 keep a subset. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## 0.35.0 — 2026-11-23 — "Belief at a context read through the excepts it sees, taxonomy reads at each edge's own context, inherited firings kept beside a contrary, functional collisions by determinateness, genetic and unqualified kinship, `answer-sets` and run files"

| Area | Change |
|---|---|
| inference | belief at a context reads the `except`s it sees and its `genlCx` ancestor set; a taxonomy read naming no context reads each edge and declaration at its own context; `in?` leaves the API for `(believed? kb handle)`; an inherited firing beside a contrary is stored with a guard `defeat` and confers `:default`; a functional collision reads three levels of determinateness; an equality class prefers a constant; an unsatisfiable temporal, qualitative or sign network stores one `contradicts` per region; a generator fed through `genl` or a swap edge is a cycle |
| shipped ontology | `BloodKinFn` is `GeneticKinFn` and generic kinship is unqualified; `chosenSiblingOf` is retired; `injection`, `surjection` and `bijection` are `injective_predicate`, `surjective_predicate` and `bijective_predicate`; a computational system and a tool are `causal`; a function's corresponding predicate is functional at the value position; `eagerly_reifiable_function` |
| storage | `open-kb` refuses a `:base-stores` without the base KB's `:clock`; a durable fork reopens over a base changed below the end it recorded |
| integrity | the not-under-thing sweep reads each type from its defining contexts; `:undeclared-term`, `covers-of` and `exposed-clashes` read belief |
| describe and the term page | the definitional block reads the KB's classification |
| caches | `:preservation-crossing` is held per KB with no limit; a write or settle on one KB leaves another KB's cache entries, reader frames and readers in place |
| API and tooling | `answer-sets`, `sign-reading`, `stored-lengths`, `calculi`'s `:allen` `:endpoints`; `lein cli run <file.vae>` |
| contexts | a rule over two contexts concludes at a context application minted below both; a row re-spelled onto its rewritten twin is believed; slice and `natFormula` orderings in every arrival order |
| performance | a functional slot's settle is linear in its members; a type arriving at a term reads the term's separated types; a metric constraint relaxes only the rows and columns it shortens; rule re-joins scoped to what a declaration or separation moves |
| browser | `/why` draws the proof; `/network` draws a calculus's network as a graph; `/signs`; `/vantage`; `/term` and `/closure` take `ctx` |

Twenty-two entries are **Breaking** and one is a **Refusal**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.34.0 caller changes.

| If your code… | Then |
|---|---|
| reads `in?` or `believed?` as the IN label, or `believed?` at a context that does not see the record's context | read the support label off `belief-status`'s `:in?`; republish a koinii seat holding a `disregard` |
| calls `genl?`, `genls`, `specs`, `isa?`, `disjoint?`, `has-prop?` or `inverse-of` with no context | pass the context to read at |
| relies on an inherited firing being refused beside a `:monotonic` contrary, or on its conclusion defeating a `:monotonic` member | run `lein cli upgrade --dir <path>`, or open once with `{:recover? :auto}`; read belief with `ask?` or `believed?` |
| states an except or defeat only in a context above an excepted `genlCx` edge | state it in a context the reader sees |
| excepts a record a placed `defeat` names, below the defeat's context, to restore it | except the defeat there |
| reads a `functional` slot holding a `nat/` or `cx/` constant beside one `:default` value as unmerged | read the merge off `equals`; a second `:default` value withdraws it |
| reads the `representative` of a class holding a `nat/` or `cx/` constant and a named constant | read the named constant as the representative |
| relies on `try-assert` refusing a declaration over a record a placed `defeat` takes from belief | read the record's `belief-status` before the write |
| reads `:qualitative-inconsistency`, `:metric-temporal-inconsistency`, `:sign-inconsistency` or `:unsatisfiable-network`, or stores a metric or sign clash through `try-assert` | read the clash off the entry's `:sentence` or the stored `contradicts`, count one entry per region, and pass `{:refuse-unsatisfiable? false}` to store a clash |
| relies on a `label-context` copy tying with its rival | retract the copy to reopen the tie |
| reads `belief-status`'s `:withdrawn?` as true for an excepted record | read `:excepted?` beside `:withdrawn?` |
| reads `belief-status`'s `:visible?` | read `:believed?` |
| calls `in?`, `vaelii.client/in?`, the daemon's `:in?` op or `lein cli in` | call `(believed? kb handle)`, the daemon's `:believed?` op with the handle alone, or `lein cli believed` |
| names `BloodKinFn`, `blood_kinship_predicate`, `generic_kinship_predicate`, `bloodRelativeOf`, `bloodKinPredicateOf`, `chosenKinPredicateOf`, `MotherFn` or `FatherFn`, or reads `motherOf` or `fatherOf` as functional | run `upgrade --sync` or rename the six spellings; state `motherOf` and `fatherOf` facts for `MotherFn` and `FatherFn`; restate a qualified `birthDate`, `birthYearOf` or `olderThan` fact as the unqualified fact |
| states a computational system or a read-only tool `acausal`, or a member of an acausal kind | retract that statement |
| states an acausal thing in a tool position of `agentHasTool` or `toolEnablesAbility`, or asks `(able ?x acausal_event)` for `image_viewing` | retract that statement; ask `(able ?x event)` |
| names `chosenSiblingOf` | write `((ChosenKinFn siblingOf) ?x ?y)` |
| names `injection`, `surjection` or `bijection` | name `injective_predicate`, `surjective_predicate` and `bijective_predicate`; `upgrade --sync` rewrites a stored premise |
| opens a KB with `:base-stores` and no `:clock` | call `fork`, or add `:clock (:clock base-kb)` |
| relies on a `:not-under-thing` finding for a type its defining context places under `thing` | read that context's taxonomy |
| reads `describe`'s `:definitional-block` `:props` as a keyword set | read each `:props` row's `:sentence` |
| calls `set-cache-limit` on `:preservation-crossing` | drop the call |
| has a generator, or a loop of generators, feeding a read above its conclusion's predicate by `genl`, `genlInverse` or `inverse` | break the cycle, or read the conclusion's own predicate |

### Breaking: inference

- **Belief at a context reads the `except`s it sees and its `genlCx` ancestor set.** A
  record is believed at `C` when it is IN, no defeat in force at `C` removes it, no except
  `C` sees hides it, and `C` sees its context through `genlCx`. A read that names no
  context answers at the record's own context. `believed?` answered true at a context that
  does not see the record's context, and `in?` answered true for a record an except hides
  at its own context. `in?`, `believed`, the extent fns' `{:believed? true}`, `why`,
  `why-not`, `preview`, `edit-with-consequences!` and `kb-diff` read the definition.
  `belief-status`'s `:believed?` answers it. `why-not` answers `:excepted` with
  `:exceptions` for a stored record an except hides at its own context. A koinii seat's
  commit leaves out a statement its agent disregards, so `commit-id`, `state-root` and
  `inclusion-proof` change for a seat holding a `disregard`.
  [nmtms.md](docs/nmtms.md#a-read-with-no-reader)
  *Migration:* read the support label off `belief-status`'s `:in?`; republish a seat
  holding a `disregard`.
  *Breaks:* `in?`, `believed?`, `belief-status`, `commit-id`, `state-root`.

- **A taxonomy read that names no context reads each edge and declaration at the context
  it is stated in.** The reads are `genl?`, `genls`, `specs`, `direct-genls`,
  `direct-specs`, `min-genls`, `max-specs`, the `common-` reads, `isa?`, `disjoint?`,
  `has-prop?` and `inverse-of`. Each leaves out an edge or a declaration a defeat or an
  except hides at its own context, as `believed?` with no context leaves out a handle.
  [nmtms.md](docs/nmtms.md#a-read-with-no-reader)
  *Migration:* pass the context to read at.
  *Breaks:* `genl?`, `genls`, `specs`, `isa?`, `disjoint?`, `has-prop?`, `inverse-of`.

- **An inherited firing beside a contrary of either strength is stored with a guard
  `defeat`, and confers `:default`.** The firing was refused or blocked beside a
  `:monotonic` contrary, so a reader that did not believe or see the contrary lost the
  conclusion while it answered the inherited antecedent. Each reader now believes the
  conclusion by the contraries, `except`s and `siblingDisjointException`s it believes. A
  firing that joined on an inherited claim records `:default` whatever its rule and its
  antecedents confer, so its conclusion no longer defeats a `:monotonic` member. A
  suppressed firing stores its conclusion and one `defeat` per context the contrary places
  one at, and the defeat's justification records a separated pair under `:separated`. A
  suppressed firing that concludes a forced-monotonic literal (`sameAs`) logs the
  `:forced-conclusion` violation it logs with no contrary. `recover` re-fires every rule on
  a preserved predicate. [inherit.md](docs/inherit.md#forward-chaining-on-a-claim-nobody-stored)
  *Migration:* run `lein cli upgrade --dir <path>`, or open once with `{:recover? :auto}`.
  An open that installs an existing reasoning image keeps the earlier belief. Read belief
  with `ask?` or `believed?`, since the stored conclusion is present under a contrary.
  *Breaks:* `transitiveInArg`, `transitiveInArgInverse`.

- **An except or defeat stated in a context a reader no longer sees removes nothing at that
  reader.** An except of a `genlCx` edge stops the reader seeing the contexts above the
  edge, and the excepts and defeats stated only there no longer apply at the reader. An
  except of a `genlCx` edge is read over the reader's whole ancestor set, as before.
  [contexts.md](docs/contexts.md#except-removing-belief-down-a-context-subtree)
  *Migration:* none; state the except, or the denial, in a context the reader sees.
  *Breaks:* `believed?`, `belief-status`, `ask?`.

- **An `except` of a record a placed `defeat` names, stated below the defeat's context,
  leaves the record unbelieved there.** The except took the defeat out of force at the
  except's context and below, so `belief-status`, `preview`, `why` and `try-assert`'s
  declaration checks read the record as believed there. An except of the defeat's
  winner, of one of its grounds or of the defeat itself still takes the defeat out of
  force.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion)
  *Migration:* to restore the record below a context, except its defeat there.
  *Breaks:* `belief-status`, `preview`, `why`, `try-assert`

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
  *Migration:* none.
  *Breaks:* `equals`, `contradictions`

- **An equality class prefers a constant over a reified constant.** Its representative
  was the smallest member by name, so `(<VerFn basePred>)` stood for a class holding
  `namedPred`. A `nat/` or `cx/` constant now stands for a class only when every
  candidate is one. The spelling a quoted position reads breaks a tie among `rewriteOf`
  heads the same way. [equality.md](docs/equality.md#choosing-the-representative)
  *Migration:* none.
  *Breaks:* `representative`, `ask`

- **`try-assert` of a declaration counts a record only where a context it covers believes
  it.** An `irreflexive` mark, an argument declaration against the tuples and rules it
  constrains, a `genlArg` and `instance_relation_predicate` pair, and a length binding
  that strands a declaration each refused the write over every stored record the network
  labels IN. A record a placed `defeat` takes from belief at the context the check reads
  it from, and at every context below that one, no longer refuses the write. A record an
  `except` below that context restores still refuses it.
  [api.md](docs/api.md#refusing-a-clash)
  *Migration:* where a caller relied on the refusal over a defeated record, read the
  record's `belief-status` before the write.
  *Breaks:* `try-assert`, `:irreflexive`, `:arg-type`, `:arg-genl`, `:arg-variable`,
  `:arg-constraint-kind`, `:arg-position`

- **A write that makes a temporal, qualitative or sign network unsatisfiable stores one
  `(contradicts …)` per conflicted region, and the region's ledger entry names it.** The
  metric and sign networks file their entry at the write, as the calculi do, and a read
  files none. A calculus files one entry per region, at the context the contradiction is
  placed in, where it filed one per network and governing context. Two networks whose
  regions rest on the same facts file one entry. `try-assert` refuses a write that is a
  member of a region, a metric or sign region included. It refuses a write that joins a
  region standing before it.
  [qcn.md](docs/qcn.md#support-what-an-entailed-relation-rests-on)
  *Migration:* read the clash off the entry's `:sentence` or the stored `contradicts`.
  Count one entry per region. Pass `{:refuse-unsatisfiable? false}` to `try-assert` to
  store a metric or sign clash.
  *Breaks:* `:qualitative-inconsistency`, `:metric-temporal-inconsistency`,
  `:sign-inconsistency`, `:unsatisfiable-network`.

- **`label/label-context` writes each copy at `:monotonic`.** A copy at `:default` tied
  with the rival the base still believes, so the labeling context reported a second
  dilemma. The labeling context now reads the recorded side alone, as a `do/labeling`
  context does. A rival restated at `:monotonic` is then a hard clash in the labeling
  context: both sides stay believed there, and `conflicts` reports it.
  [labeling.md](docs/labeling.md#ctx-inherits-and-the-labeling-is-recorded-by-strengthening)
  *Migration:* none; retract a copy to reopen the tie in the labeling context.
  *Breaks:* `label-context`.

- **`belief-status`'s `:withdrawn?` is false for a record an except alone hides.** It
  reports the placed defeats in force at the context (`exc/withdrawn-fn`), and
  `:excepted?` reports the except. [nmtms.md](docs/nmtms.md)
  *Migration:* read `:excepted?` beside `:withdrawn?`.
  *Breaks:* `:withdrawn?`.

- **`belief-status` no longer returns `:visible?`.** Under the belief definition
  `:visible?` answered what `:believed?` answers.
  [api.md](docs/api.md)
  *Migration:* read `:believed?`.
  *Breaks:* `:visible?`.

- **`in?` leaves the API: `(believed? kb handle)` answers belief at the context a record
  is stored in.** The daemon's `:in?` op, `vaelii.client/in?` and `lein cli in` go with
  it. `lein cli believed <handle> [<CxName>]` answers at the record's own context or at
  the named one. [api.md](docs/api.md)
  *Migration:* call `(believed? kb handle)` where `(in? kb handle)` was called, and the
  daemon's `:believed?` op with the handle alone.
  *Breaks:* `in?`, `:in?`, `lein cli in`.

### Breaking: shipped ontology

- **Blood kinship is genetic kinship, and generic kinship is unqualified.** The 0.34.0
  spellings are renamed with their arity and argument order: `BloodKinFn` is
  `GeneticKinFn`, `blood_kinship_predicate` is `genetic_kinship_predicate`,
  `generic_kinship_predicate` is `unqualified_kinship_predicate`, `bloodRelativeOf` is
  `geneticRelativeOf`, `bloodKinPredicateOf` is `geneticVersionOf` and
  `chosenKinPredicateOf` is `chosenVersionOf`. `resources/renames/0.35.0.edn` records
  the six, so `upgrade --sync` rewrites a stored premise that names an old spelling.
  Gestational-only parenthood and surrogacy are not genetic kin and specialize no parent
  or mother predicate. A child can have more than one mother or father, so `life.txt`
  states `(not (functional motherOf))` and `(not (functional fatherOf))`, and
  `kinship.txt` states the same of `(GeneticKinFn motherOf)` and
  `(GeneticKinFn fatherOf)`, each with a `comment` giving a case. `MotherFn` and
  `FatherFn` are retired, and `resources/renames/0.35.0.edn` records both, so
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

- **CxTra drops `chosenSiblingOf` for `(ChosenKinFn siblingOf)`.** `chosenSiblingOf`, a
  spec of `(ChosenKinFn siblingOf)`, is retired. `(ChosenKinFn siblingOf)` names the same
  relation and is symmetric, time-varying, typed `person` at both positions, and below
  `chosenKinOf` and `siblingOf`.
  `resources/renames/0.35.0.edn` records the term as retired, so `upgrade --sync`
  reports a stored premise that names it.
  *Migration:* write `((ChosenKinFn siblingOf) ?x ?y)` for `(chosenSiblingOf ?x ?y)`.
  *Breaks:* `chosenSiblingOf`

- **`injection` is `injective_predicate`, `surjection` is `surjective_predicate` and
  `bijection` is `bijective_predicate`.** The three predicate types keep their meanings,
  declarations, comments and rules under the new names in `core.txt`, and `kinship.txt`'s
  acknowledgments quote the rules by the new names. The names say that each is a type of
  predicate. `resources/renames/0.35.0.edn` records the three renames, so
  `upgrade --sync` rewrites a stored premise that names an old spelling.
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* rename `injection` to `injective_predicate`, `surjection` to
  `surjective_predicate` and `bijection` to `bijective_predicate` in KB text, rules and
  queries.
  *Breaks:* `injection`, `surjection`, `bijection`

### Breaking: storage

- **`open-kb` refuses a `:base-stores` without the base KB's `:clock`.** A fork reads its
  base's change count beside its own, so a write through the base KB retires the fork's
  cached answers. A pair of stores names no clock. The refusal is `:unknown-option` with
  `:mismatch :bad-value` and `:option :base-stores`.
  [storage.md](docs/storage.md#two-stores)
  *Migration:* call `fork`, or add `:clock (:clock base-kb)` to the `:base-stores` map.
  *Breaks:* `:base-stores`

### Breaking: integrity

- **The not-under-thing sweep reads each type from its defining contexts.** A candidate
  type is rooted when the audit context or one of the type's defining contexts
  (`defining-contexts`) reaches `thing` by `genl`. `core.txt` states
  `(decontextualized_predicate unary_predicate)`, so every reader sees a type declaration
  made in a middle theory, while the type's `genl` edges stay in that theory. The sweep
  read the edges from the audit context alone, so it reported such a type from a reader
  that does not see the theory. Over the 353 terms the starter declares
  `unary_predicate`, the sweep from CxNormalPhysicalConditions reported 52 CxTra types.
  It now reports none, from CxNormalPhysicalConditions or from CxTra. A type whose
  defining support is incomplete is read from the audit context alone.
  *Migration:* a caller that relied on a `:not-under-thing` finding for a type whose
  defining context places it under `thing` reads that context's taxonomy instead.
  *Breaks:* `:not-under-thing`
  [integrity.md](docs/integrity.md#what-a-not-under-thing-finding-means)

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

### Breaking: caches

- **The `:preservation-crossing` cache is held per KB and has no limit.** Its `caches`
  row reads `:scope :kb`, and its `:entries` count the values one KB holds. Another KB's
  open, read or close leaves a KB's entry in place, and no process-wide map holds a
  closed KB's entry. `set-cache-limit` refuses `:preservation-crossing`, as it refuses
  every cache with a nil limit. [caches.md](docs/caches.md#the-register)
  *Migration:* drop the `set-cache-limit` call on `:preservation-crossing`.
  *Breaks:* `set-cache-limit :preservation-crossing`

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

- **An `injective_predicate` that is a `surjective_predicate` is a `bijective_predicate`,
  and `folk_biological_class` is forced-monotonic.** A forward-only `core.txt` rule
  concludes `(bijective_predicate P)` from `(injective_predicate P)` and
  `(surjective_predicate P)`, and retracting either withdraws it. `organism.txt`
  declares `(forced_monotonic_predicate folk_biological_class)`, as `folk_species` already
  is, so a class membership is never the loser of a nogood.
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* none.

- **An `eagerly_reifiable_function`'s applications are reified as soon as their arguments
  meet its argument constraints.** `core.txt` declares three terms.
  `eagerly_reifiable_function` is a type of function, a spec of `reifiable_function`.
  `meetsArgConstraints` holds of a function and arguments that meet its `arg` and
  `argGenl` declarations. `reify` holds of a term of the KB, and is a spec of `thing`
  orthogonal to `not_assertible`.
  One general rule concludes `(reify (?f . ?args))` from
  `(eagerly_reifiable_function ?f)` and `(meetsArgConstraints ?f . ?args)`, and its
  firing mints the application.
  `kinship.txt` declares `(eagerly_reifiable_function GeneticKinFn)` and
  `(eagerly_reifiable_function ChosenKinFn)`, so every unqualified kinship predicate,
  one declared later included, has both readings reified.
  *@hack:* `reify` has no engine support yet, so a rule comments each reified term as a
  temporary implementation. `meetsArgConstraints` is concluded only for a unary
  `eagerly_reifiable_function`, from each `arg` declaration alone and without `argGenl`.
  `eager_reify_test`'s `^:red` tests state the general reading.

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

- **`injective_function`, `surjective_function` and `bijective_function` are types of
  function.** `core.txt` declares each below `function`, decontextualized, time-invariant
  and forced-monotonic, as its predicate twin is. `bijective_function` is below the other
  two. An `injective_function`'s applications to different arguments denote different
  things. An inert rule states that definition for a unary function, since an argument
  tuple of any length is no term.

- **Kinship hierarchy lifting reads each `genl` edge between unqualified inputs once.**
  kinship.txt's two lift rules conclude `(genl ?v ?gv)` from `(geneticVersionOf ?p ?v)`,
  `(geneticVersionOf ?g ?gv)` and `(genl ?p ?g)`, and the `chosenVersionOf` twin, in place
  of two generators of one ground rule per ordered pair of unqualified predicates. The
  starter stores no generated lift rule (128 before), its forward firings fall from 3,147
  to 3,019, and the lifted `genl` set is unchanged.
  *Migration:* none; the lifted edges are the same.

### Additive: storage

- **A durable fork reopens over a base changed below the end it recorded, and keeps every
  handle it minted.** A base loaded in another order, grown in the middle of its load
  order, edited in place, or missing records the fork named is followed by content. The
  fork's removals, overrides, released marks, `except`s and justifications apply to the
  records they named, and what named a record the base no longer holds is dropped.
  `:fork-base-overlap` remains for a fork whose index half `reindex` rebuilt, and for a
  fork whose bookkeeping holds digests until a mount over its own base accepts it.
  [overlay.md](docs/overlay.md#a-base-changed-below-its-end)
  *Migration:* none.

### Additive: API

- **`believed?` takes no context: `(believed? kb handle)` answers at the context the
  record is stored in.** The daemon and `vaelii.client` serve the same arity.
  [api.md](docs/api.md)

- **`answer-sets` solves the program a context sees as clingo reads it, and writes
  nothing.** `:reading` picks every optimal answer set, one, or the brave or cautious
  consequences. `:among`, `:limit` and `:project` admit non-optimal answer sets, cap them and
  project them, and three options set the search. The daemon serves it, holding
  `:time-limit` under its clock ceiling.
  [solving.md](docs/solving.md#the-asp-reading-of-a-program)
  *Migration:* none.

- **`sign-reading` returns a context's sign reading: each quantity's possible signs and
  trends, and `:consistent?`.** An inconsistent reading keeps the sets the clash left, an
  emptied set as `#{}`. The read answers whether or not the `:sign` prover is registered,
  and takes a context name or a ground context application. The daemon serves it.
  [sign.md](docs/sign.md#reading-out)
  *Migration:* none.

- **`stored-lengths` maps each functor in a collection to the argument counts its positive
  facts are stored at**, in one index read per functor, with belief unread. The daemon
  serves it. [api.md](docs/api.md)
  *Migration:* none.

- **`calculi`'s `:allen` map carries `:endpoints`**, each base relation's order on the four
  endpoint comparisons. [web.md](docs/web.md#the-timeline)
  *Migration:* none.

### Additive: tooling

- **`lein cli run <file.vae>` runs a run file**: it restores the base `#base` names, asserts
  the file's forms, and prints each `#show` read's instances and each `#truth` read's
  verdict. A refused form prints `<file>:<line>: error: [<:type>] …` and exits 1, and a
  refused directive is `:bad-directive`. A `#show` cut at `--depth` exits 3. `#models`,
  `#model`, `#brave` and `#cautious` solve the context's program as clingo reads it and print
  its optimal answer sets or the instances true in some or in every one. A `#solve` map
  sets the `answer-sets` options of the solve reads after it. Eleven sample programs under
  `test/programs/asp/` sit beside their clingo twins
  ([from-asp.md](docs/from-asp.md#sample-programs)).
  [operations.md](docs/operations.md#run-files)
  *Migration:* none.

### Additive: browser

- **`/why` draws the proof above its tree.** The conclusion sits on the top row, each
  justification under the sentence it concludes, and each antecedent under its
  justification. An unbelieved conclusion is drawn with its stored justifications dashed,
  and the caption names what holds it out. [web.md](docs/web.md#the-proof-tree)
  *Migration:* none.

- **`/network` draws a calculus's network over a context as a labelled graph above the
  matrix.** The interval and point calculi add a timeline of each part whose every pair
  the network narrows to one base relation. An emptied pair is dashed, and an
  inconsistent network is drawn inside a dashed frame.
  [web.md](docs/web.md#the-network-drawing)
  *Migration:* none.

- **`/signs?ctx=<context>` draws a context's sign network** above a table of each
  quantity's possible signs and trends. [web.md](docs/web.md#the-sign-drawing)
  *Migration:* none.

- **`/vantage?ctx=<context>&q=<pattern or term>` draws one card per context**: `ctx`, the
  contexts it sees that store a match, and the contexts that see it. Each card lists the
  matches its context sees and how that context reads each one.
  [web.md](docs/web.md#a-sentence-across-contexts)
  *Migration:* none.

- **`/term` and `/closure` take `ctx`.** With one, the picture draws only what the
  context's `genlCx` ancestor set states. [web.md](docs/web.md#a-terms-shape-drawn)
  *Migration:* none.

### Fix: inference

- **A ground membership or denial of a part answers when two parts of its cover have closed
  extents** ([#310](https://github.com/vaelii/vaelii/issues/310),
  [#304](https://github.com/vaelii/vaelii/issues/304)). A goal about a member of
  the whole stated in no part could throw `StackOverflowError`.
  [taxonomy.md](docs/taxonomy.md#the-coverage-inference-is-conditional-on-explicit-negation)
  *Migration:* none.

- **A retracted mark an eager reification reads leaves with the constants it minted**
  ([#303](https://github.com/vaelii/vaelii/issues/303)). Retracting
  `(unqualified_kinship_predicate p)` left the mark believed, with the `(GeneticKinFn p)` and
  `(ChosenKinFn p)` constants and what they derive, because each map's projection derived
  the mark again. [nat.md](docs/nat.md#rename-and-remove--keeping-the-11-invariant)
  *Migration:* none.

- **A `symmetric` or `commutative` mark arriving after two void firings of one
  proposition leaves the proposition unbelieved until a firing is valid, whichever
  arrives last.** The late mark believed the folded proposition. A fold of two such rows
  that conclude themselves through a third row threw a `NullPointerException` on the
  `memory-columnar`, `memory-dense` and `disk-snapshot` backends.
  [canonicalization.md](docs/canonicalization.md#a-mark-arriving-after-the-facts-migrates-them)
  *Migration:* none.

- **`qualitative-network` at a variable context reads each fact as its own context believes
  it.** A fact a placed `defeat` removed in its own context entered the diagnostic network
  and could make it unsatisfiable.
  [qcn.md](docs/qcn.md#which-networks-it-joins-against)
  *Migration:* none.

- **`covers-of` no longer counts a defeated record, and `kb-integrity`'s
  `:undeclared-term` no longer reads a term as declared by a defeated membership.**
  `covers-of` returned a `covering`, `separating` or `partition` defeated in the context
  it is stored in. The sweep read a term as declared by a membership the audit context
  defeats or excepts. The sweep still counts a defeated use of the term.
  [integrity.md](docs/integrity.md#what-an-undeclared-term-finding-means)
  *Migration:* none.

- **`kb-integrity`'s `:undeclared-term` reads a membership a rule concludes as a
  declaration only where the audit context believes and sees the rule's antecedents.**
  A firing from a defeated or excepted antecedent declared the term.
  [integrity.md](docs/integrity.md#what-an-undeclared-term-finding-means)
  *Migration:* none.

- **`exposed-clashes` no longer reports a clash at a context where an `except`, or a
  `defeat` of another nogood, hides one of its memberships.** Such a membership was
  reported. A pair is reported whether or not a defeat between its two memberships
  decides it.
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* none.

- **`chain-report`'s `:believed?` is false for a derived rule resting on a defeated
  fact.** The row answered true where `in?` of the rule answered false.
  [api.md](docs/api.md)
  *Migration:* none.

- **A preview hands the named-application facts back at their handles.** A preview that
  re-chained a rule guarded on `rewriteOf` dropped them, and the rollback placed them again
  at new handles. [nat.md](docs/nat.md#the-corresponding-predicate) *Migration:* none.

- **`label-context` copies the assumptions `label-dilemmas` kept, and only those their own
  context believes.** It copied every assumption of the recorded `Program` the network held
  IN, both sides of a dilemma included.
  [asp.md](docs/asp.md#labeling-contexts)
  *Migration:* none.

- **`classify-local` classifies no datum its read context does not believe.** A datum a
  placed `defeat` removed was classified `:true` or `:supportable`.
  [labeling.md](docs/labeling.md#the-solve-free-bracket)
  *Migration:* none.

### Fix: order independence

- **A forward firing over a `transitive` walk, a `reflexive` diagonal or a calendar answer
  rests on each believed declaration apart, whichever arrives last.** A defeated declaration
  took the firing from belief, and retracting or excepting one of two declarations withdrew
  the firing.
  [inference.md](docs/inference.md)
  *Migration:* none.

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

### Fix: contexts

- **A forward rule whose antecedents sit in two contexts concludes at a context
  application minted below both after they arrive.** The `genlCx` edges the mint built
  seeded no chaining, so the conclusion appeared only when the context was minted first.
  [context-nat.md](docs/context-nat.md#the-structural-genlcx-producer)
  *Migration:* none.

- **A row re-spelled onto its own rewritten twin's spelling is believed.** A rule that
  concludes a sentence over a reifiable application before that application's
  `rewriteOf` takes effect stores the row, and the merge stores its rewritten twin and
  supersedes the row. A settle that re-spells the function's uses folds the twin into the
  row, which takes the twin's spelling. The row kept its supersession entry and read OUT
  as superseded by its own spelling. The fold now reconciles the row's entry at its new
  spelling. In the starter loaded in shuffled order, the `genl` edges from the genetic
  readings to `geneticRelativeOf` read IN.
  [nat.md](docs/nat.md#a-reifiable-mark-moving)
  *Migration:* none.

- **A `natFormula` map or a `contextArgGenlCx` declaration a placed `defeat` removes
  orders no context under its argument, whichever arrives last.** The producer read the
  network label, so a defeated map or declaration built the edge, and a defeat arriving
  after the edge left it.
  [context-nat.md](docs/context-nat.md#the-structural-genlcx-producer)
  *Migration:* none.

- **A slice is ordered under another when its time starts inside the other's through local
  moments and ends inside it through UTC ones, whichever arrives last**
  ([#259](https://github.com/vaelii/vaelii/issues/259)).
  A link fact arriving after both slices read the calendar months between two bounds of
  one frame, and the pair stayed unordered when the two bounds lay in different frames.
  [context-nat.md](docs/context-nat.md#the-structural-genlcx-producer)
  *Migration:* none.

### Fix: describe

- **`describe` leaves out a comment, link or argument declaration an except or defeat at
  the read context hides.** It showed one stated above the context that excepts it.

- **A type's disjoint line is sorted whenever the union of its partners' closures fits
  the sort budget.** The choice used the sum of the closure sizes, which counts an overlap
  twice, so a line whose union fit could come out unsorted and inexact, and a sorted
  member such as `cat` under `dog` could fall off it. Past the budget the line stays
  unsorted, with the sum as its `:total` and `:exact?` false.

### Fix: performance

- **A write to one KB no longer retires the clocked cache entries of a KB over another
  store, or declines its reasoning-image save.** Each store has its own change clock. A
  write through any KB value open over the store moves it, and a fork's clock adds its
  base's. A reader of KB A beside a writer on KB B over another store keeps A's
  literal-match, closure and network entries. A's image save or export commits while B is
  written, so A's next open installs the image instead of running a recover. Each KB holds its own
  reader-frame and yield write counts and its own sync memo. A write to KB B retires none
  of A's reader frames or held yield answers, a read on B evicts nothing A synced, and a
  KB dropped without `close!` is not held reachable.
  [caches.md](docs/caches.md#the-register)
  *Migration:* none.

- **A settle on one KB no longer makes another KB's readers held.** Each KB keeps its own
  registry of open holds. A reader of KB A beside a settle on KB B reads A's clock and keeps
  A's cache entries. A thread inside A's settle reads B's settle as the belief it began from.
  [storage.md](docs/storage.md#the-single-writer-contract)
  *Migration:* none.

- **A settle re-asks only the live members of a functional slot it moved.** An arrival
  into a slot of n members read each member, and read the slot's fillers again per member,
  so it cost O(n²): `functional-in-arg-empty-determinant-sweep` read 12.3 ms/op at n=250
  and 457 ms/op at n=2000. It now reads 1.85 and 1.43 ms/op.
  [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing)
  *Migration:* none.

- **A type arriving at a term is tested against the term's types a separation reaches.**
  It was tested against every type the term holds. The
  `separated-membership-beside-held-types` check's growth reads 0.83x to 1.13x, where it
  read 3.00x and 3.40x. A routed witness walk sorts each type's neighbours once per
  router, and allocates 33 KB per level where it allocated 80 KB.
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* none.

- **An arriving metric constraint relaxes only the rows and columns it shortens.** A
  warm-started closure keeps the earlier instants' order and places new instants after
  them, so the earlier matrix is copied as one block. `metric-closure-warm-start` reads
  1.06 ms per arrival at 400 instants, where it read 1.72.
  [stp.md](docs/stp.md#cost)
  *Migration:* none.

- **A separated membership, a negated claim or an `asymmetric` mark re-joins no rule on a
  preserved predicate.** Each re-joined such a rule over the claims it reads and could
  license no firing. Each still re-checks the firings already stored.
  [inherit.md](docs/inherit.md#forward-chaining-on-a-claim-nobody-stored)
  *Migration:* none.

- **A believed argument-type mint takes no admission check from a source that already
  justifies it.** A declaration or fact stated or derived again draws the same mints
  without re-checking them. The starter KB's load asks 1,609 admission checks against
  2,548. A violation that content stored after the mint makes is no longer reported by
  such a repeat draw, as `record-arg-types` already reports none.
  [argtypes.md](docs/argtypes.md#the-entailment-as-a-justified-datum)
  *Migration:* none.

- **A `partition`, `covering` or `separating` declaration re-joins a rule with a `genl`
  antecedent only over the pairs its parts add.** Each such declaration re-joined every
  rule reading `genl` over the rule's extent. The join now starts from the types below each
  part or above the whole, as a `genl` edge's join does, and a rule no part reaches is not
  re-joined. Beside 1,024 types under a rule's `genl` antecedent, a partition of three
  fresh types takes 2.5 ms against 47.6 ms (`lein perf`'s
  `partition-beside-a-closure-antecedent-extent`). The starter KB's load runs 14,193 rule
  firings against 33,319.
  [inference.md](docs/inference.md#full-re-joins-on-an-arriving-datum-chainrejoin-in-full)
  *Migration:* none.

- **A cover check reads a part's denials only under the predicates stored of the term.**
  The check read `(not (q x))` for every supertype `q` of each part of a cover over the
  membership's type. It now reads only the supertypes holding a stored fact about `x`
  (`res/*cut-every-fan?*`). The starter KB's load asks 189,704 goals against 546,075, and
  spends 5.9% of its profile samples in that read against 12.5%.
  [taxonomy.md](docs/taxonomy.md#the-coverage-inference-is-conditional-on-explicit-negation)
  *Migration:* none.

- **A forward rule's computed antecedent asks only the provers whose answers it can join.**
  The join asked every applicable prover and dropped each answer from a prover that does
  not implement `SupportingProver`. `DefnSufficientProver` and `CoveringProver` solved
  every expression-kind antecedent, and the join dropped their answers. The starter KB's
  load asks 546,075 goals against 591,699, and the computed antecedents take 3.3% of its
  profile samples against 11.7%.
  [inference.md](docs/inference.md#what-a-computed-answer-rests-on)
  *Migration:* none.

- **A slice mint and a `tightestStartBoundOf` question read the links along a chain once,
  not once per sibling or per pair of bounds** ([#259](https://github.com/vaelii/vaelii/issues/259)).
  Along a chain of story events, a mint in its middle read 26.3x for 8x the slices and
  now reads 4.5x (`lein perf`'s `context-nat-mint-along-a-chain`). A question of its last
  event read 23.5x for 4x the events and now reads 4.1x
  (`tightest-start-bound-along-a-chain`).
  [time.md](docs/time.md#the-order-over-time-points-vaeliiimplpoint-order)
  *Migration:* none.

- **A batch that stores a `formula`-position declaration settles once, at its close.**
  Inside `with-deferred-settle` or `assert-many`, an `arg`, `quotedArg` or `argN`
  declaration typed `formula`, or a `genl` edge that moves one, settled belief at the
  write, and the batch's closing settle then repeated that work. The starter KB's load
  settled three extra times. [api.md](docs/api.md#batched-assertion)
  *Migration:* none.

- **The typeAllSpecified pass reads eligibility first and one open ask per member.** It
  asked each instance `(K x)` of every classifier member and only then read whether the
  reader was its defining home, so an exempt instance paid every failing ask. It now
  reads eligibility first, then one `(K ?x)` per member. An eligible instance those
  answers name is classified, and every other one asks `(K x)` of each member as before.
  When a member's open read throws something other than a budget or deadline signal, the
  pass asks every instance bound. Its findings are unchanged. On the starter, the default
  `kb-integrity` sweep from CxNormalPhysicalConditions takes 6.2 s against 28.0 s, and its
  pass 0.84 s against 22.7 s. From CxTra the sweep takes 5.9 s against 28.2 s, and its
  pass 0.84 s against 23.2 s. Each is a median of five runs.
  [integrity.md](docs/integrity.md#what-a-type-specified-finding-means)
  *Migration:* none.

### Fix: browser

- **A term page's picture draws every edge it read between two drawn nodes.** An edge
  spanning rows bends around the boxes in the rows between instead of crossing them. A
  label wraps over three lines before it is cut, and the caption counts the part of the
  closure the picture holds. [web.md](docs/web.md#a-terms-shape-drawn)
  *Migration:* none.

- **A taxonomy node stored with two or more arguments is coloured as a relation.** With no
  declarations, `dislikes` under `(dislikes Ann Bob)` was coloured as a type.
  [web.md](docs/web.md#a-terms-shape-drawn)
  *Migration:* none.

- **`/closure` on a context draws its `genlCx` ancestor or descendant set.** `/closure` on
  `CxWell` drew nothing. [web.md](docs/web.md#a-types-whole-closure)
  *Migration:* none.

### Internal: tooling

- **`lein lint` fails a read of the IN label outside `E24_ALLOW`, which gives the reason
  for each reader and the number of its reads.** `jtms/in-datums`, `reads/in-with-functor`,
  `reads/in-with-args` and `res/rule-believed?` count as reads, under any alias or fully
  qualified.
  [nmtms.md](docs/nmtms.md#belief-filtering-is-a-namespace-boundary)

- **`lein perf --owed` runs the perf checks a change reaches, and `lein perf-ab <base>
  --owed` the perf-ab probes.** `lein perf --reach` records, under the JaCoCo agent, the
  engine fns and the lines of src/ each check and probe executes, and `lein gate`'s "perf
  owed" and "perf-ab owed" lines read that map. A change inside a fn selects the checks
  that executed the call or branch around it. With no map, they keep the per-file rules.
  `lein perf --jobs <n>` runs the checks on n worker JVMs, by default one per 8
  processors up to 4.
  [CONTRIBUTING.md §1.1](CONTRIBUTING.md#11-static-analysis-lein-lint-setup)

- **`lein perf-ab` fails a run whose JVM stops at a probe that throws.** `assert` refused
  `arity-edge-move`'s setup, and a full run timed the nine probes before it and passed.
  The probe runs again, and the seven probes from it on report.
  [CONTRIBUTING.md §1.1](CONTRIBUTING.md#11-static-analysis-lein-lint-setup)

- **The settle-phase instrument (`lein bench-settlephases`) keeps a span stack per
  thread.** Two KBs settling on two threads under it each file their own settle records.
  [docs/nmtms.md](docs/nmtms.md#where-the-time-goes-measured)

- **The test slot count takes in every core tier but Efficiency.** On a chip with 12 Super
  and 24 Performance cores the base is 27 slots, three quarters of the 36 cores, and on
  8P + 2E it is 6. A sharded suite starts on the free slots, at most 18. Its floor,
  `TEST_MIN_JOBS`, defaults to a third of the base, or to 3 when that is more. A matrix
  starts as many configurations as there are free slots.
  [operations.md](docs/operations.md#configuration--every-switch-and-where-it-is-read)

- **Every JVM lein starts has a heap cap, and the build moves to Clojure 1.12.7, ring
  1.15.6, cheshire 6.2.1 and RoaringBitmap 1.6.30.** `.leinrc` caps leiningen's own JVM
  at 1 GB unless `LEIN_JVM_OPTS` names `-Xmx`. `project.clj` caps every project JVM at
  8 GB unless `JVM_OPTS` names `-Xmx`, and a profile's `-Xmx` still wins.
  [operations.md](docs/operations.md)

### Internal: CI

- **A pull request runs the perf-ab probes its change reaches, under one `perf` check.**
  Each of three reps runs on its own runners, `starter-load` apart from the other probes.
  A change under `resources/kb/` runs the `starter-load` and `starter-recover` probes, and
  a change under `src/vaelii/impl/` or to `src/vaelii/core.clj` runs all 16.
  `scripts/perf-owed.py` reads a file whose namespace its reach map holds no key for, and
  every file when there is no map, through its per-file rules. `lein perf-ab --first-rep
  K` numbers a run's reps from K, and `lein perf-ab --judge <rows.tsv>…` judges the rows
  of several runs as one. [CONTRIBUTING.md §7](CONTRIBUTING.md#7-commits--pull-requests)

- **The `weights` check accepts the rows a release sets on the first push to `develop`
  after the release resets it.** On a push that replaces the branch's history, the tip
  before the push is not an ancestor of the pushed commit, so the check reads the weights
  files at the merge base of the two. The 0.34.0 reset's first run accepted no row and
  failed on `vaelii.intersection-test`.
  [CONTRIBUTING.md §7](CONTRIBUTING.md#7-commits--pull-requests)

- **A failing test is a GitHub annotation while its shard still runs.** The `memory` and
  `disk` suite steps pipe `lein test` through `annotate_failed_selectors`
  (`scripts/lib/failed-selectors.sh`), which writes one `::error` per failing
  `<namespace>/<test>` as its `lein test :only` line arrives. Each names the leg, the
  shard, the log and its failure-log artifact. A shard annotates at most 10 tests, then
  writes one warning that counts the rest. A marker that does not match suite-marks.sh's
  patterns whole is counted and not annotated, and no annotation quotes a failure's
  report. The log, the shards and the step's exit status are as they were.

## 0.34.0 — 2026-11-18 — "Kinship qualified by blood and choice, forward `(k ?x)` antecedents over declared result types, context NATs ordered both ways, term rename, merge, copy and remove, bounded removals"

**76 entries** — 20 Breaking, 2 Refusal, 18 Additive, 33 Fix, 3 Internal. Kinship shares
one generic hierarchy with blood and chosen readings, a time that is part of a time is a
subtime of it, and `hasCapability`, `capabilityType` and `toolEnablesCapability` are
`able`, `abilityType` and `toolEnablesAbility`. A forward rule's `(k ?x)` antecedent holds
for each application a `result` or `resultArg` declaration types at or below `k`, and an
`orthogonal` clash is read by strength. Two context NATs a declared order places each
below the other through `:monotonic` evidence are one class, and a minted constant's role
and result types rest on its length bindings and its map. `rename-terms!`, `merge-terms!`,
`copy-terms` and `remove-terms!` change a term in every premise as one `edit!`, and
`edit!`, `retract!` and a served removal bound the re-chain a removal releases.

*Breaks:* `relativeOf`, `parentOf`, `childOf`, `motherOf`, `fatherOf`, `siblingOf`,
`grandparentOf`, `ancestorOf`, `birthDate`, `birthYearOf`, `olderThan`, `MotherFn`,
`FatherFn`, `originatorOf`, `assert`, `partOf`, `subtimeOf`, `ask`, `query`,
`kb-integrity`, `hasCapability`, `capabilityType`, `toolEnablesCapability`, `(k ?x)`,
`cxTimeOf`, `:monotonic`, `rewriteOf`, `prove`, `orthogonal`, `:default`, `conflicts`,
`contradictions`, `subsumption-status`, `violations`, `siblingDisjointException`,
`handle-of`, `why-not`, `justification-verdicts`, `why`, `edit!`, `:max-ms`, `:stop?`,
`:edit`, `:retract`, `genlCx`, `contextsOrderedBothWays`, `sentexes-matching`, `explain`,
`term-role`, `nat/`, `genl`, `genlInverse`, `premise?`, `supporting-justifications`,
`retract!`, `result`, `genlResult`, `sentex`, `natFormula`, `instantBefore`,
`instantNotAfter`, `instantAfter`, `instantNotBefore`, `vocabulary-audit`, `cx/`

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
