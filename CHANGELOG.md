# Changelog

## Unreleased

- **`predAllSpecified` and `predSpecifiedAll` go binary: the filler type derives from
  the predicate's own slot contract.** The ternary forms restated in a third argument
  what `(arg P 2 R)` / `(genlArg P 2 R)` already say, and a restated type can disagree
  with the contract it copies — a second type system inside one declaration. The
  declarations are now `(predAllSpecified P D)` and `(predSpecifiedAll P R)`; the audit
  derives the filler constraints from the visible slot typing of the predicate **and
  every super-predicate whose declarations bind its tuples** — the same
  `constraining-predicates` union the assert-time checker reads — with `arg` →
  membership, `genlArg` → subtype through the reflexive `genl` closure, and a
  `type_relation_predicate` membership requiring the filler to be visibly a type at
  every position, composed conjunctively as the checker composes them. A declaration
  over a predicate with **no** visible denotation typing is reported as an explicit
  `{:status :gap :gap :missing-slot-typing}` declaration-contract diagnostic, never
  silently audited unconstrained, and a stored pre-migration ternary sentex — which
  the bulk import path can carry past the assert-time refusal — surfaces from the
  sweep as `{:gap :legacy-ternary-declaration}` rather than silently vanishing.
  `specified-violations` accordingly returns `{:status :audited :violations #{…}}` or
  `{:status :gap …}` — discriminate on `:status`, not key presence — drops its `dep`
  parameter, and refuses a non-`:second`/`:first` `arg-pos` with a typed `:bad-args`
  naming the removed-dep migration (the shape an unmigrated caller's context symbol
  lands in); `all-specified-violations` keys by `[functor pred indep]` and always
  carries gaps, so an empty map remains a clean sweep a gap cannot fake. The
  function-mark rules thin to one antecedent each — totality reads only `(arg P 1 D)`,
  ontoness only `(arg P 2 R)`. New vocabulary `arg1` / `arg2` / `arg3` — binary
  projections of `arg`, bridged by rules in both directions and held to `arg`'s own
  declaration checks at the projected position, so neither spelling launders a
  declaration the other refuses — lets a positional constraint stand in a binary
  declaration's subject position, `(predAllSpecified arg1 predicate)` being the
  founding use; the projections relate stored declarations only, generalized and
  inherited readings staying `arg`'s. *Class:* **Breaking** (declaration arity and
  audit return shape). *Migration:* rewrite `(predAllSpecified P D R)` to
  `(predAllSpecified P D)` and `(predSpecifiedAll P D R)` to `(predSpecifiedAll P R)`,
  ensure the audited slot carries its `arg`/`genlArg` typing, and read
  `(:violations result)` under a `:status` check where a bare set was read before.
  [docs/predall.md](docs/predall.md), [docs/taxonomy.md](docs/taxonomy.md)

  *Breaks:* `(predAllSpecified`, `(predSpecifiedAll`, `specified-violations`,
  `all-specified-violations`

- **`injection`, `surjection` and `bijection` name what a relation is as a function, and
  the engine reads each half where it can.** Saying a relation was a one-to-one function
  took four separate declarations — `(functional P)`, `(functionalInArg P 1)`,
  `(predAllSpecified P D)` and `(predSpecifiedAll P R)` — and an author who wrote some
  of them got partial enforcement with no report of the gap. The three composite marks are
  one declaration each, and eight CxCore forward rules derive the parts, so nothing is
  keyed on the new names. `injection` is single-valued, one-to-one and total; `surjection`
  is single-valued, total and onto; `bijection` derives the other two. The **domain and
  range are not arguments of the mark**: totality and ontoness are claims about two
  collections rather than about `P`, and `(arg P 1 D)` and `(arg P 2 R)` already state
  them, so the rules read them from there. A predicate declaring no `arg` pair gets the
  enforced marks and no audit. The two halves divide on what an open world can refuse: a
  second filler is refused or merged at the assert entry point, while totality and
  ontoness become `predAllSpecified` and `predSpecifiedAll` requirements that
  `all-specified-violations` reports when a caller asks. No new API function, and
  retracting the mark or either `arg` declaration withdraws what rested on it. The
  glossary gains `injection` and `surjection` and rewrites `bijection`, 173 to 176.
  *Class:* **Additive**. *Migration:* none — `bijection` shipped in no release, and the
  reading it had on `develop` (single-valued and one-to-one, with no totality or
  ontoness) is now `(functional P)` beside `(functionalInArg P 1)`, written directly.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/predall.md](docs/predall.md)

## 0.16.0 — 2026-09-04 — "the predAll quantifier family, refusals that name their kind, and declarations that reach back"

- **An unpinned indeterminate term is not provably different from anything.** The
  unique-name assumption made `(different X Y)` provable for any two symbols no equality
  sentex had merged, and a skolem constant is a symbol the engine minted for an object it
  has not identified. `different` now answers false where either argument is an unpinned
  member of the extensible `indeterminate_term` category — the skolem constant is its
  built-in first member, read off the `SkolemFn` expression the constant was minted from,
  and a further kind joins with `(genl NewKind indeterminate_term)`. A `rewriteOf`,
  `sameAs` or `equals` that pins the term moves its representative off the term itself and
  restores the assumption. `same-class?` reads false of such a term as it always has, so
  the two are no longer complements: a caller wanting *provably different* asks
  `different` and reads that answer. *Class:* **Breaking** for a caller reading a
  difference against a skolem constant or a declared indeterminate kind. *Migration:* pin
  the term with `rewriteOf` before asking, or ask `same-class?` where the question is
  shared membership rather than provable difference. [docs/equality.md](docs/equality.md),
  [docs/predall.md](docs/predall.md)

  *Breaks:* `(different`, `indeterminate_term`

- **A missing adapter is not an unknown backend.** Selecting `:sqlite` or `:pg` records
  without the Apache-2.0 sibling on the classpath refused as `:unknown-backend`, so a
  caller catching that keyword to fall back on `:memory` acted on two wrong readings at
  once: the axis name is legal, and the remedy is a coordinate in the project rather than
  a different backend. The refusal is `:missing-adapter`, carrying `:records` and the
  `:coordinate` to add, read off `kb/record-axes`' own `:adapter` column so it cannot
  drift from the table that declares it. *Class:* **Breaking** for a caller branching on
  `:unknown-backend` for either axis. *Migration:* catch `:missing-adapter` where the
  remedy is a dependency; `:unknown-backend` still answers a name the engine does not
  have. [docs/storage.md](docs/storage.md),
  [docs/troubleshooting.md](docs/troubleshooting.md)

  *Breaks:* `:unknown-backend` for a `:sqlite` or `:pg` records axis with no adapter on
  the classpath

- **A wrong operand count is not an unknown option.** `cli/check-arity!` refused
  `assert takes 2 arguments, given 1` as `:unknown-option`, so a caller branching on that
  keyword reported a bad flag when every flag on the line may be one the command reads.
  The refusal is `:bad-args` — the keyword `serve` already refuses a wire call's argument
  count under — carrying `:op`, `:given` and `:takes`. *Class:* **Breaking** for a caller
  branching on `:unknown-option` for a CLI operand count. *Migration:* catch `:bad-args`.
  [docs/api.md](docs/api.md)

  *Breaks:* `:unknown-option` for a CLI operand count

- **A rule concluding an indeterminacy from a `different` antecedent is refused.**
  `different` is negation as failure over two inputs now — the equality closure and the
  `indeterminate_term` category — so a rule concluding into either from a `different`
  antecedent closes a cycle through negation. Such a rule was stored and settled to a
  belief its own support contradicts, the conclusion believed off a difference the
  conclusion then made false. `checks/negative-predicates` ran its negative edge to the
  three merge relations alone; the edge covers `indeterminate_term` and `genl` as well,
  and `assert` refuses the rule as `:not-stratified`. The `genl` entry
  over-approximates, because only a `genl` into the category's closure withdraws a
  difference and the consequent's second argument is a variable when the check runs.
  `edge-negation-cycle` starts at a `different` rule directly, so a cycle closed by a
  later taxonomy edge is refused rather than missed. *Class:* **Refusal**. *Migration:*
  none for a KB the bundled ontology builds, where no rule reads `different`; a rule that
  did conclude `indeterminate_term` or a `genl` from a difference has to be rewritten to
  read a stored mark instead. [docs/exceptions.md](docs/exceptions.md),
  [docs/equality.md](docs/equality.md)

  *Breaks:* `:not-stratified`, `indeterminate_term`

- **The `predAll` quantifier family, all eight cells.** A quantifier-family declaration
  says how each argument position of a binary predicate is filled: one position ranges
  over a collection's members and the other holds a fixed term, or both range over
  collections. Each relation names its two positions in order, and the eight divide into
  three classes by what the engine does with a declaration. `predAllInstance` and
  `predInstanceAll` are rule generators — asserting
  `(predAllInstance sign negative_integer "negative")` stamps the concrete forward rule
  `(implies (negative_integer ?x) (sign ?x "negative"))`, so descent to the members is
  ordinary chain inference, with a justification on the conclusion and a retraction that
  follows the membership. The four cells with `exist` in the name are inert: each
  declaration is a stored, queryable record the engine derives nothing from, and each
  sanctions a placeholder functor — `PredAllExistsFn`, `PredExistsAllFn`,
  `PredExistsInstanceFn`, `PredInstanceExistsFn` — an author may use to name the required
  filler. `predAllSpecified` and `predSpecifiedAll` state a requirement audited on
  demand: `specified-violations` reports the instances of one declaration with no
  determinate filler, `all-specified-violations` audits every declaration visible in a
  context and omits the ones that hold, and both read the KB and store nothing. A filler
  is determinate unless it is an `indeterminate_term`, which is what makes the *Specified*
  class the antagonist of the *Exists* class: a placeholder an author wrote down satisfies
  the requirement and a witness the engine skolemized does not. Thirteen grammar terms
  join the predicate registry, CxCore carries the declarations and the two generators, and
  the two audit entry points reach `vaelii.core` through `wiring`, which the layering
  inventory now names four entries. The glossary gains `indeterminate_term` and the
  `predAll` family, 171 to 173. *Class:* **Additive**. *Migration:* none.
  [docs/predall.md](docs/predall.md)

- **A `different`-guarded firing is withdrawn when a later merge makes the guard false.**
  A rule guarded by `(different ?x ?y)` fired, stored a conclusion, and kept it when a
  later `sameAs` merged the two arguments, while asserting the merge first derived
  nothing. The same three sentences settled to two beliefs depending on which arrived
  last, which order independence forbids. `SupportingProver` cannot carry this one: its
  contract is a prover naming the stored facts its answer was read from, and `different`
  holds by the absence of a merge, is not assertible, and has no handle anywhere in the KB
  for a justification to name. The re-check index answers it instead — the index
  `unknown`, `exceptWhen`, aggregates and closed-extent negatives already use.
  `rules/rechecked?` admits a `different` antecedent and posts the rule under
  `rules/different-flip-predicates` (the three equality relations, `indeterminate_term`
  and `genl`), and `chain/different-blocks?` re-evaluates each guard against the firing's
  settled bindings from `rule-firing-blocked?`, the one place both re-decision paths run
  through. A merge, an indeterminacy declaration and their retractions all reach the
  firing. *Class:* **Fix**, with one thing to know: the registration is written when a
  rule is indexed, so a store written before this release needs `recover` to rebuild the
  posting before its `different`-guarded rules are re-checked. *Migration:* none.
  [docs/equality.md](docs/equality.md), [docs/predall.md](docs/predall.md)

- **A `(symmetric P)` declaration arriving after the facts reaches the facts already
  stored.** The write entry point sorts a ground symmetric literal's arguments, so a mark
  that arrives late left the store holding spellings no later assertion produces and, where
  both spellings had been written, two records for one proposition, each retractable
  without the other. Same declarations, same facts, one retraction, and the beliefs
  differed by the order the mark arrived in. `integrate/symmetrize-existing` re-spells a
  row with no mirror in place and folds a mirrored pair into one record, which restores
  order independence on the one mark whose effect is canonicalization rather than
  conviction. *Class:* **Fix**, with one thing to know: the migration is a write, so
  retracting the mark does not undo it. *Migration:* none.
  [docs/canonicalization.md](docs/canonicalization.md)

- **A computed `genlCx` edge runs the equality reconcilers a stated one runs.** A `genlCx`
  edge reaches the store three ways — asserted, concluded by a rule, or computed by the
  structural producer off a `contextArgSubrelation` declaration. The first two ran the
  three reconcilers a context edge owes; the third ran none, so a calendar month-to-year
  edge reached the taxonomy and the exception re-checks and stopped there, leaving two
  fillers of one functional slot unmerged and unreported where the same two facts under a
  stated edge merged. `special/reconcile-context-edge` is that list once, and all three
  paths call it. *Class:* **Fix**. *Migration:* none.
  [docs/context-nat.md](docs/context-nat.md), [docs/equality.md](docs/equality.md)

- **A close waits for the compaction it started before it hands the directory over.**
  `close-dir!` released the directory's OS lock without joining the compaction executor,
  and the record store's rewrite phase runs outside the kind lock by design, so this JVM
  could still be writing the temp files of a directory a second process already owned:
  two rewrites appending to one temp log, one commit marker, and a replay installing
  frames from both. `vaelii.disk.auto-compact` is on by default, so this was the default
  configuration. The order is now the contract — deregister, abort, join, write the image,
  close the components, release the lock — and `stop!` no longer returns having stopped
  nothing. *Class:* **Fix**. *Migration:* none. [docs/storage.md](docs/storage.md)

- **`quotedArg` is answered along the `genl` closure, like its three siblings.** The write
  entry point has always asked the whole `:argument-constraint` family whose declarations
  speak for a tuple, so `(genl pInfantAgeOf pAgeOf)` with `(quotedArg pAgeOf 2 string)`
  refuses `(pInfantAgeOf Bob 5)`; the query surface answered only what was literally
  stored, so one declaration meant one thing to `assert` and another to `ask`.
  `provers/meta-constraint-shape` gains the row it was missing, with the variance its
  three siblings already state. *Class:* **Fix**. *Migration:* none.
  [docs/argtypes.md](docs/argtypes.md)

- **Every refusal declares what its `ex-data` carries, and a throw that drops a key
  fails.** `carried` pins, for each `:type` raised in more than one place, the keys all of
  its throws agree on, scanned out of the sources; `carries-nothing` records the
  twenty-five where they agree on none, with the reason. The fifty-one remaining
  `:unknown-option` throws now carry `:mismatch` (`:unknown-key`, `:bad-value`,
  `:missing-value`, `:not-a-map`, `:missing-companion`, `:conflict`) and the eleven
  `:unknown-backend` ones carry `:axis`, `:kind` and `:mismatch` (`:unknown-name`,
  `:reserved-name`, `:illegal-pair`, `:illegal-position`). Which key held the offending
  backend used to be the axis's own name, so a caller wrote
  `(or (:backend d) (:records d) (:index d) (:tms d))`; `:axis` answers it. Every
  existing key stays. *Class:* **Additive**. *Migration:* none.
  [docs/troubleshooting.md](docs/troubleshooting.md)

- **The facet contract is data, and a half-wired declaration fails the build.**
  `predicates/facet-contract` gives every facet a row — the facets carrying it implies,
  and whether a mark family has to agree about it — and `check-facets` refuses seven rules
  at `settle`'s namespace load under `:bad-table-entry`, ten `:mismatch` values between
  them. Two rules are stated rather than derived: `:opposing-read` says what an
  arbitrable term's opposing side is read through, and `:stops-short` records an
  implication an entry does not satisfy, checked in both directions so it can neither be
  missing nor go stale. *Class:* **Additive**. *Migration:* none.
  [docs/predicates.md](docs/predicates.md)

- **Four more tables become rosters checked at load.** `config/switches` declares the
  twenty-three durability switches with their readers and where each is read, and a reader
  with no row fails the namespace — eight of them were first read inside `fsync-all`'s
  `catch Throwable`, where a missing one logged a class name every three seconds with the
  feature silently dead. `kb/record-axes` and `kb/index-axes` replace five private
  literals and three `case` dispatches, with nine rules joining them to the arms that open
  a store. `quality/readings` replaces the two hand-written lists behind `census` and
  `report`, where a reading in one and not the other rendered as an absent section.
  `settle/facet-check-inputs` is the one value both the live check and its test read, so
  deleting the check no longer compiles. *Class:* **Additive** — same behaviour, same
  order, same values refused at the same entry points. *Migration:* none.
  [docs/predicates.md](docs/predicates.md), [docs/storage.md](docs/storage.md),
  [docs/quality.md](docs/quality.md)

- **The class-name check states which nippy release it was written against.** The gate on
  a durable frame that names a class reaches into three of nippy's internals, and a bump
  that keeps their names while no longer routing a class name through them would wrap
  cleanly and cover less than it did. `thaw/pinned-nippy-version` states the release, and
  `check-nippy-pin!` refuses at namespace load against any other, reading the resolved
  version off nippy's own Maven descriptor: `:nippy-version-unreadable` when nothing can
  be read, `:nippy-version-moved` when another release is named. *Class:* **Additive** —
  two new refusals at load, and no call moves. *Migration:* a nippy upgrade re-reads the
  three attachment points and then moves the pin. [docs/defenses.md](docs/defenses.md)

- **The content-key guards read an ordering key as a form, not as the rest of its line.**
  `sort_by_content_key_test`'s scans cut the line after the ordering call, so a key
  written one line below its `sort-by` was invisible to them; nine sites had been written
  under a guard watching for exactly that. The scan now reads the key paren-balanced to
  its own close, and a fourth scan refuses a `sort-by` whose key fn reads the KB, which
  re-reads a taxonomy closure about `2·n·log2(n)` times where `nm/sort-by-content-key`
  reads it `n` times. *Class:* **Fix** — two of the nine collapsed a context under an
  ambient `*print-length*`, so the tie they broke fell back to arrival order.
  *Migration:* none. [docs/nmtms.md](docs/nmtms.md)

- **The CI disk leg runs as two runner-sharded jobs, and a namespace outside the split
  fails the leg.** The disk-log leg had grown into its own 30-minute timeout. Two shard
  jobs each run half the test namespaces — whole namespaces, split alphabetically, the
  same `:default` selector — on separate runner VMs, which share no directory, no registry
  and no single-writer lock, and they report through a gate job named `disk` so the
  required check keeps its name. The shards selected files by glob while `lein test`
  selects by namespace, and nothing kept the two in step, so a file defining a top-level
  `deftest` outside the glob was skipped by both shards and stayed green. The leg fails on
  such a file now. *Class:* **Fix** — CI configuration and a test-selection check.
  *Migration:* none.

- **The prose is reworded to say what the code does.** Comments, docstrings, doc pages,
  changelog entries and test names now state the mechanism in literal technical language,
  and `scripts/check-prose.py` runs as `lein lint`'s `prose` row against
  `scripts/prose-baseline.txt`, a per-file budget that only shrinks. Five metaphors are
  replaced by what each one stood for: an entry point or a check, the named protocol or
  extension point, the public API, a layering boundary, a call site, and the ancestor set.
  Six private fns rename with them — `members-in-ancestors` and its five siblings — along
  with three test-local bindings and nineteen `deftest` names;
  `entry_point_and_report_test.clj` is the renamed test file, and `bench/index.clj`'s
  index-store flag is `:kv-index-store?`. The glossary's entry for the API sense is
  **Entry point**, and four words the other entries leaned on and never defined — arm,
  lane, refusal, roster — now have entries of their own, 167 to 171. *Class:* **Additive**:
  no public var, protocol or option key carried any of the renamed words, so the API
  surface is unchanged and the three goldens are untouched. *Migration:* none.
  [docs/glossary.md](docs/glossary.md), [docs/naming.md](docs/naming.md)

- **CONTRIBUTING gains §3.9 and §3.10.** §3.9 states what compacting a released changelog
  section keeps and what it drops, and that every argument in a dropped paragraph needs a
  home first — mechanism in the subsystem page, a rejected alternative in
  [docs/defenses.md](docs/defenses.md). §3.10 is the prose rule and its eight clauses.
  Both released sections in this file are compacted to the shape the older ones use.
  *Class:* **Additive**. *Migration:* none.

## 0.15.0 — 2026-09-01 — "definitions that compute, and two renames"

- **A unary predicate is snake_case, and `assert` now enforces it in both directions.**
  *Class:* **Breaking** for any KB, corpus or caller holding a camelCase unary predicate.
  *Migration:* rename every camelCase functor used at arity 1 to snake_case —
  `warmBlooded` → `warm_blooded`, `unaryPredicate` → `unary_predicate`,
  `abduciblePredicate` → `abducible_predicate`. `nm/snake-case` is the conversion the
  rejection message applies, and every shipped context, test-world file and doc here has
  been rewritten. A corpus that cannot be rewritten opens under `{:naming :warn}` or
  `{:naming :off}`; the bulk import path never consulted the entry point, and its `nm/tally`
  summary now counts `functor-unary` beside the rest. [docs/naming.md](docs/naming.md)

  *Breaks:* every camelCase unary predicate spelling — `unaryPredicate`,
  `reifiableFunction`, `abduciblePredicate`, `closedExtentPredicate`, `disjointMetatype`,
  `siblingDisjoint`, `warmBlooded`

- **The sentex polarity slot is `:polarity`, not `:truth`.** *Class:* **Breaking** for any
  reader of a sentex map. *Migration:* `(:truth sx)` → `(:polarity sx)`, `(= :true …)` →
  `(= :positive …)`, `(= :false …)` → `(= :negative …)`. On-disk record stores are
  unaffected — the durable frame is positional behind a numeric tag and never held the
  keyword — and an export dump written either side of this loads correctly, since `import`
  re-derives the polarity from the sentence's own `not` and never reads the key.
  [docs/storage.md](docs/storage.md)

  *Breaks:* `:truth`

- **A definitional membership question is answered at query time, not only by a forward
  rule.** *Class:* **Additive** — no signature moves, nothing is stored differently, and
  `ask` and `prove` answer questions that previously came back unknown. **One thing to
  know, because it is a boundary and not a feature:** the negation prover concludes `(not
  (Coll a))` from a failing necessary, so a `defnNecessary` is a disqualifier as well as
  an obligation. Membership stays open-world in the direction that matters —
  condition-*absence* still concludes nothing, and a thing the condition is silent about
  is neither a member nor a non-member — but a necessary that is positively *violated* is
  now a negative answer rather than silence. It is a query-time answer only: nothing is
  asserted, so a KB that states `(Coll a)` against a failing necessary is not rewritten,
  it merely answers both halves and says so. *Migration:* none, unless a KB leaned on a
  violated necessary staying silent. [docs/defns.md](docs/defns.md)

- **The `AtomicSentex` record is `LiteralSentex`.** *Class:* **Additive**: the class name
  reaches no public surface, no golden names a record class, and the durable frame is
  tagged with a number rather than a class name, so nothing on disk moves and no store
  needs rewriting. The tag constant moved with it, `atomic-tag` to `literal-tag`.
  *Migration:* none, unless a caller referenced `vaelii.impl.sentex.AtomicSentex`
  directly, which is an impl namespace. [docs/storage.md](docs/storage.md)

- **One word, one stratum: the docs get a vocabulary rule, and a gate that reads it.**
  *Class:* **Additive** — two renamed readers are private, and everything else is prose.
  *Migration:* none. [docs/naming.md](docs/naming.md#reserved-words)

- **CxCore names the expression kinds.** *Class:* **Additive**, with one thing to know:
  this claims eight generic names in CxCore, so a KB already using `sentence`, `formula`
  or `literal` as its own collection now shares ours and inherits the `genl` edges and the
  disjointness above. *Migration:* none to write, but the shipped-KB count moved and this
  release is where a reader should learn the real figure. CxCore ships **475** sentexes
  against **416** at 0.14.0 — +20 for the expression kinds here, +35 for the curation
  vocabulary below, +4 with the definitional provers. `docs/kbs.md`'s row now reads `~475`
  like its neighbours, and `core_context_test` asserts a band rather than an equality: an
  exact pin failed on every deliberate change to the vocabulary and caught nothing a
  deliberate change did not, `vocabulary-audit` being what actually guards CxCore by
  failing a term nobody classified. A count is kept only for what a count can catch — a
  load going wrong in bulk. [docs/glossary.md](docs/glossary.md)

- **CxCore gains a curation vocabulary: `seeAlso`, `termsRelated` and the example
  predicates.** *Class:* **Additive**, and inert: nothing derives from these and no
  existing query changes. It does claim the names in CxCore, so a KB already using
  `seeAlso` or `termsRelated` as its own predicate now shares ours. *Migration:* none.
  [docs/predicates.md](docs/predicates.md)
## 0.14.0 — 2026-08-29 — "the index image as a backend, and the heap it stops paying"

- **The mapped index image is a backend, not a property: `:disk-snapshot`.** *Class:*
  **Breaking** for anything setting the property. *Migration:* unset
  `vaelii.index.snapshot` and name the backend — `{:backend :disk-columnar}` +
  `-Dvaelii.index.snapshot=true` → `{:backend :disk-snapshot}`. The property is refused at
  every spelling rather than ignored, and `:disk-columnar` now always rebuilds on open. A
  directory written with the property set opens under `:disk-snapshot` as it stands; what
  this release does to the image inside it is the argument-roots entry below.
  [docs/storage.md](docs/storage.md#the-image-disk-snapshot)

  *Breaks:* `vaelii.index.snapshot`

- **`:argument-family-ceiling`** refuses a KB with more distinct `(predicate, position)`
  pairs than the packed root key's 24-bit scope field holds — 16,777,216, against the
  ~86k predicates an audited corpus carries — rather than wrapping two families onto one
  key. It names the pair it could not scope and carries `:remedy {:index :memory}`.
  *Class:* **Refusal** — a wrapped scope id is two predicates sharing one packed key, so
  an argument read answers the other family's postings and no query can tell. *Migration:*
  nothing: 16.8M distinct `(predicate, position)` pairs is orders of magnitude past the
  largest audited corpus, and a KB that genuinely holds that many takes the `:index
  :memory` the refusal names.
  [docs/troubleshooting.md](docs/troubleshooting.md#i-have-a-type-and-do-not-know-what-it-means)

  *Breaks:* `:argument-family-ceiling`

- **The disk store's live-handle sets are compressed bitmaps.** *Class:* **Fix**.
  *Migration:* none — no durable format moves, and no store needs reopening.
  [docs/storage.md](docs/storage.md#the-enumerations-and-what-a-roster-costs)

- **The mapped index image stops carrying the argument roots into heap.** *Class:*
  **Fix**. *Migration:* none, and this is the whole of what the release asks of a
  directory that already holds an image: the image's `format-version` bumps to 2, so one
  written by an older build is discarded on the first open as `:layout-changed` and
  rebuilt from the records — once, with the version-2 image published at the next refresh.
  The records do not move, the `:index :columnar` key layout is unchanged, and no other
  durable file is touched.
  [docs/indexing.md](docs/indexing.md#8-the-index-as-bytes-the-mapped-snapshot)

- **The writer refreshes a drifted image mid-life, and can be told not to.** *Class:*
  **Additive**. [docs/storage.md](docs/storage.md#the-cadence-and-whose-thread-it-runs-on)

- **A visibility `except` targeting a rule now removes totally in both directions.**
  *Class:* **Fix**. *Migration:* none.
  [docs/contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree)

- **A `functionalInArg` declaration arriving after the facts it convicts is reported.**
  *Class:* **Fix**. *Migration:* none — a KB using the mark gains reports it was owed;
  nothing that was believed stops being. [docs/taxonomy.md](docs/taxonomy.md)

- **`quotedArg` reads the sign-refined integer types instead of refusing every integer.**
  *Class:* **Fix**. *Migration:* none — a declaration that previously refused everything
  now refuses only what it means to. [docs/argtypes.md](docs/argtypes.md)

- **The quality report's rule-conflict detector reads both functional spellings.**
  *Class:* **Fix**. *Migration:* none. [docs/quality.md](docs/quality.md)

- **A bounded partner sweep says so: `:partner-sweep-truncated`.** *Class:* **Additive**.
  [docs/nmtms.md](docs/nmtms.md)
## 0.13.0 — 2026-08-25 — "calendar time, joined queries, and the entry points that refuse"

- **`:disk` and `:pg-disk` are `:disk-log` and `:pg-disk-log`.** *Class:* **Breaking** for
  any opts map, script or `VAELII_TEST_BACKEND` value naming either name. *Migration:*
  rename the selector — `{:backend :disk}` → `{:backend :disk-log}`, `{:index :disk}` →
  `{:index :disk-log}`, `{:backend :pg-disk}` → `{:backend :pg-disk-log}`,
  `VAELII_TEST_BACKEND=disk` → `=disk-log`. **The on-disk layout does not move**: a
  directory written under either old spelling opens under the new one with no reindex, no
  recovery and no `format-version` bump, and its record files are byte-identical across the
  open. Neither name is aliased — `open-kb` refuses both spellings with `:type
  :unknown-backend` and names the pairing to take instead, since an index axis names a
  directory *layout*, and a name that answers to two layouts opens a store in one its caller
  did not ask for. [docs/storage.md](docs/storage.md#backend-selection-two-independent-axes)

  *Breaks:* `:disk`, `:pg-disk`, `VAELII_TEST_BACKEND=disk`

- **`edit!` is all-or-nothing.** *Class:* **Breaking** for a caller that read a half-applied
  batch back, and for one reading `apply-proposal!`'s `:applied`, which now answers zero on
  a refusal instead of counting the prefix that landed. *Migration:* delete the recovery
  step — there is no half-applied batch to settle by hand or to clean up. Discriminate a
  refusal on `:type` as before; `:rolled-back true` is new alongside it.
  [docs/api.md](docs/api.md), [docs/preview.md](docs/preview.md),
  [docs/troubleshooting.md](docs/troubleshooting.md), [docs/feed.md](docs/feed.md)

  *Breaks:* `edit!`, `edit-with-consequences!`, `apply-proposal!`

- **A reified context is collected when nothing is in it, names it or wires it.** *Class:*
  **Breaking** — a caller that emptied a reified context and then read it back by its
  constant, or looked for it among `contexts`, finds it gone rather than standing empty.
  *Migration:* name the expression, never the constant: `(CxTimeFn CxMonad (DatetimeFn
  "2000"))` resolves through the map at every entry point and re-mints where the KB has collected
  it, dedupping to one constant as it always has — the `cx/` symbol and the handle are
  freshly allocated, as any re-mint's are. A context to be kept while its extent is empty
  takes a stored `genlCx` edge or a sentence naming it.
  [docs/context-nat.md](docs/context-nat.md), [docs/nat.md](docs/nat.md)

  *Breaks:* `contexts`, `count-in-context`, `contextDenotingFunction`

- **`lein cli load` reads a text KB, not an EDN vector.** *Class:* **Breaking** for a script
  feeding it the vector form. *Migration:* write one file per context named for it, holding
  the bare sentences (`(dog Muffet)`), and drop the per-entry context; a `{:strength
  :monotonic}` entry becomes a `(set/monotonic (dog Muffet))` wrapper.
  [docs/operations.md](docs/operations.md), [docs/api.md](docs/api.md)

  *Breaks:* `lein cli load`

- **The proving levels agree with belief about a defeated answer.** *Class:* **Breaking**:
  labeling.md documented the re-derivation, so a caller could have read it as a contract.
  *Migration:* a caller that read `prove`'s answer on a defeated side as a second opinion
  now gets belief's; `why-not` says `:defeated`. [docs/labeling.md](docs/labeling.md),
  [docs/levels.md](docs/levels.md), [docs/defenses.md](docs/defenses.md)

  *Breaks:* `prove`, `provable?`, `query`, `argue`

- **A forward firing that rests on a measure comparison names the unit rows it read.**
  *Class:* **Breaking**, in the sense that belief after a retraction is observable — a
  caller depending on the conclusion outliving its unit row was depending on the bug.
  *Migration:* none; a conclusion that outlived its unit row is withdrawn with it now, and
  `why` names the row. [docs/quantity.md](docs/quantity.md),
  [docs/inference.md](docs/inference.md)

  *Breaks:* `forward-chain`

- **Calendar constructors, and a time context computes its own year–month–day ancestor set.**
  *Class:* **Additive**. [docs/context-nat.md](docs/context-nat.md),
  [docs/time.md](docs/time.md)

- **A calendar term now has endpoints, so a date orders itself.** *Class:* **Additive**: a
  new opt-in reasoner and three new `CxTime` declarations, no public var moves, and a KB
  that registers nothing is unchanged. [docs/time.md](docs/time.md),
  [docs/context-nat.md](docs/context-nat.md)

- **`CxChange`: a shipped event calculus.** *Class:* **Additive**.
  [docs/time.md](docs/time.md), [docs/commonsense.md](docs/commonsense.md)

- **A metric constraint narrows an interval relation, without a word being written about
  intervals.** *Class:* **Additive**: no public var changes, nothing that was entailed stops
  being entailed, and a KB stating no `temporalDistance` reads exactly the network it read
  before. [docs/stp.md](docs/stp.md)

- **An arriving `temporalDistance` constraint is relaxed into the metric closure rather than
  closing the network again.** *Class:* **Additive**: a cost change with no answer change —
  `stp/close` keeps its signature and its meaning, the new `close-state` /
  `close-state-from` / `tightening-of?` are `vaelii.impl`, and `test/golden/api-surface.edn`
  does not move. [docs/stp.md](docs/stp.md)

- **`SupportingProver`, and the metric and duration provers reach a forward join.** *Class:*
  **Additive**: a new SPI protocol, pinned in `test/golden/spi-protocols.edn`, and forward
  rules that derived nothing now derive. [docs/inference.md](docs/inference.md),
  [docs/stp.md](docs/stp.md), [docs/duration.md](docs/duration.md)

- **A quantity can be rising.** *Class:* **Additive**: a new opt-in reasoner and new
  vocabulary, no public var moves, and a KB that registers nothing stores and retrieves
  these facts as ordinary facts. [docs/sign.md](docs/sign.md)

- **The instance-level comparatives compose.** *Class:* **Additive**: three declarations
  arrive, no predicate loses a property, and nothing that was answered stops being answered.
  [docs/commonsense.md](docs/commonsense.md)

- **The two numbers that bound the relation-algebra mask layer are written down.** *Class:*
  **Additive**: no constant moves and no answer changes; two numbers a reader could find
  only by reading the source are stated. [docs/qcn.md](docs/qcn.md)

- **`or` in a rule antecedent, stored as one rule per alternative.** *Class:* **Additive**:
  no rule that stores today stores differently, `or` having no meaning to change.
  [docs/canonicalization.md](docs/canonicalization.md)

- **`:disjunction-too-wide`, and the positions `or` is refused from.** *Class:*
  **Additive**: a `:type` where none was, over input the engine has no other reading for —
  `or` is not a declared predicate, so a literal on it matches nothing and fires never.
  [docs/canonicalization.md](docs/canonicalization.md)

- **A disjunctive *goal* is refused (`:shape`) rather than unioned.** *Class:* **Refusal**:
  a goal on the undeclared predicate `or` matches nothing, so the entry point answers with no
  solutions — the answer shape a caller is least likely to question, since it reads as "no"
  rather than as "I cannot". *Migration:* run the query once per alternative and
  concatenate, or put the disjunction in a rule — which *is* expanded — and ask for its
  conclusion. [docs/canonicalization.md](docs/canonicalization.md)

  *Breaks:* `ask`, `ask?`, `prove`, `query`, `query-plan`, `abduce`, `sentexes-matching`,
  `handle-of`

- **A `watch` on a disjunctive goal is refused rather than registered.** *Class:*
  **Refusal**: a registered watch on an `or` goal never called its listener, so no working
  caller exists. *Migration:* register one watch per alternative. *Breaks:* `watch`,
  `:not-watchable` [docs/api.md](docs/api.md), [docs/feed.md](docs/feed.md)

- **A NAF query joins its conjunction, and `forall` is the sugar over it.** *Class:*
  **Additive**: input the engine refused is read, and a `:type` where none was.
  [docs/naf.md](docs/naf.md)

- **An aggregate's census body joins.** *Class:* **Additive**: input the engine refused is
  read, and the `:quantified-conjunction` refusal is retired with the last site that raised
  it. [docs/aggregate.md](docs/aggregate.md)

- **`closedExtentPredicate` closes one predicate's extent, per context.** *Class:*
  **Additive**. [docs/naf.md](docs/naf.md), [docs/from-cyc.md](docs/from-cyc.md)

- **A forward join over a transitive predicate reads the closure, and names the edges it
  crossed.** *Class:* **Additive**: a rule that fired before fires on at least as much, and
  the closure was already what `ask` answered. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/inference.md](docs/inference.md), [docs/time.md](docs/time.md)

- **A rule joined to a growing transitive extent now derives the same conclusions whichever
  order its facts arrived in.** *Class:* **Fix**. *Migration:* none; a KB that worked around
  it with an explicit `forward-chain` still works. [docs/inference.md](docs/inference.md)

- **A rule concluding a more general predicate keeps its transitive walk.** *Class:*
  **Additive**: a derivation the walk was suppressed from now lands and no answer is
  withdrawn — a KB with no `genl` edge between a declared-transitive predicate and a rule
  conclusion is untouched, the shipped ontology included.
  [docs/inference.md](docs/inference.md)

- **A `genlCx` edge arriving last re-joins a rule over the subtypes of what its antecedent
  names.** *Class:* **Fix**. *Migration:* none; a KB that was loaded in an unlucky order
  gains the firings it was owed at its next `recover`. [docs/contexts.md](docs/contexts.md)

- **A `genlCx` edge arriving last restates the facts its widened ancestor set newly exposes to a
  merge.** *Class:* **Fix**. *Migration:* none; a KB loaded in an unlucky order gains the
  restatements it was owed at its next `recover`. [docs/equality.md](docs/equality.md)

- **A rule reaching a merged term concludes once, at the elected spelling.** *Class:*
  **Fix**. *Migration:* none; a conclusion under a retired spelling stops being believed,
  and the representative's was already believed beside it.
  [docs/equality.md](docs/equality.md)

- **A rule asserted after a predicate merge is restated under the representative, as one
  asserted before it is.** *Class:* **Fix**. *Migration:* none; a rule written after a
  predicate merge is stored superseded with its twin believed, which is what the other
  arrival order already produced. [docs/equality.md](docs/equality.md)

- **A cycle through negation that runs through a `different` antecedent is refused in every
  arrival order.** *Class:* **Fix**. *Migration:* a KB holding such a pair keeps it;
  re-asserting either rule, or the edge, through the public entry point is refused
  `:not-stratified`. [docs/exceptions.md](docs/exceptions.md)

- **Equational rewriting: the critical-pair unifier follows a binding chain to its end, and
  `normalize` keeps an empty list.** *Class:* **Fix**. *Migration:* none.
  [docs/equational.md](docs/equational.md)

- **A frame that names a class is refused before the name is resolved.** *Class:*
  **Refusal**: a sentence leaf of a class only `java.io.Serializable` round-trips —
  `java.time.LocalDate` and the other `java.time` locals, a `Throwable`, a joda `DateTime` —
  is refused `:not-encodable` at `assert`, and a file carrying such a value (or a record or
  deftype frame) is refused on the way in. *Migration:* write a date as the KB's own
  calendar term ([docs/time.md](docs/time.md)) or as a number or string; a `java.util.Date`,
  `java.time.Instant`, `java.time.Duration`, `java.util.UUID`, `java.net.URI`,
  `java.math.BigDecimal` and every array nippy has a type id for are unaffected. A store
  already holding such a leaf reads back under
  `taoensso.nippy/*thaw-serializable-allowlist*` only by exporting it with a build that
  predates this. *Breaks:* `assert` / `assert-many` / `load-text!` on such a leaf; `open-kb`
  / `import!` over a file that names a class [docs/storage.md](docs/storage.md),
  [docs/defenses.md](docs/defenses.md)

- **An EDN manifest is read under a byte bound.** *Class:* **Refusal**: a manifest over the
  bound, and a torn `records/format.edn`, are refused where they were read. *Migration:*
  none for a manifest of the size these hold; a directory refused this way is damaged rather
  than merely large. *Breaks:* `open-kb` on a store whose `format.edn` is truncated,
  `import!` / catalog discovery over an oversized manifest
  [docs/storage.md](docs/storage.md), [docs/defenses.md](docs/defenses.md)

- **A dump's chunk length is bounded before it is allocated.** *Class:* **Fix**.
  *Migration:* none; the writer never produces a chunk near the bound.
  [docs/storage.md](docs/storage.md)

- **A served read's depth and wall clock may be lowered by a request and not raised.**
  *Class:* **Refusal**: a request naming a bound past the ceiling was served and is now
  refused. *Migration:* name a smaller bound, or raise the ceiling on the daemon (`0` lifts
  it). *Breaks:* `POST /op` and the `kb_*` tools for `:query`, `:query?`, `:argue`, `:why`,
  `:why-not`, `:search-tree`, `:compare-tacticians`, `:ask-within`, `:prove-within`
  [docs/operations.md](docs/operations.md), [docs/defenses.md](docs/defenses.md)

- **`ask`, `ask?`, `prove` and `provable?` take a bound.** *Class:* **Additive**.
  *Migration:* none; every existing call shape answers as it did. [docs/api.md](docs/api.md)

- **The daemon holds `:ask`, `:ask?`, `:prove` and `:provable?` to its search ceiling.**
  *Class:* **Refusal**. *Migration:* a remote `:prove` or `:ask` that legitimately runs past
  `VAELII_MAX_QUERY_MS` needs the ceiling raised, or `0` to lift it; in process nothing
  changes, since a call with no option map is unbounded as before. *Breaks:* a served `:ask`
  / `:ask?` / `:prove` / `:provable?` taking longer than `VAELII_MAX_QUERY_MS` (30 s by
  default) now refuses where it ran on. [docs/operations.md](docs/operations.md)

- **The browser refuses a public bind with no token, and then requires it.** *Class:*
  **Refusal**: a browser that started on an address with no token no longer starts.
  *Migration:* set `VAELII_API_TOKEN` (and have the reverse proxy in front present it), or
  drop `--listen` and reach the browser over loopback. *Breaks:* `--listen`, `vaelii.web`
  [docs/operations.md](docs/operations.md), [docs/web.md](docs/web.md),
  [docs/defenses.md](docs/defenses.md)

- **A `find-terms` regex is bounded across the whole vocabulary, not only per term.**
  *Class:* **Refusal**: a pattern that reads more than a hundred million characters over one
  call ran to completion and now throws. *Migration:* narrow the pattern, or use `:prefix` /
  `:substring`, which read linearly. *Breaks:* `find-terms` `{:match :regex}`, `/find`, the
  daemon's `:find-terms`, `kb_find_terms` [docs/web.md](docs/web.md)

- **A `VAELII_ALLOWED_HOSTS` entry carrying a port matches the host it names.** *Class:*
  **Fix**. *Migration:* none. [docs/operations.md](docs/operations.md)

- **A host-path read stays out of the model's tool set.** *Class:* **Additive**: no served
  op changes shape and no public var moves — the model's tool set, derived from the op
  table, loses a read it should never have carried. [docs/llm.md](docs/llm.md)

- **A predicate is at most one of the three arity classifications.** *Class:* **Refusal**: a
  KB that declared one predicate two arity classes stored both and reconciled them under
  truth maintenance, and now the second declaration throws. *Migration:* declare one class,
  or `(variableArity P)` where the predicate really reads tuples of more than one length; a
  KB already holding both keeps them, a declaration arriving over stored content being
  reported by `exposed-clashes` rather than thrown at whoever wrote the second half.
  *Breaks:* `assert` / `load-text!` / `lein cli load` / `lein cli assert` on a second
  `unaryPredicate` / `binaryPredicate` / `ternaryPredicate` membership for one predicate
  [docs/taxonomy.md](docs/taxonomy.md), [docs/quality.md](docs/quality.md)

- **Every argument position the shipped contexts declare an arity for is typed, or excused
  by name.** *Class:* **Refusal**: a fact naming a non-predicate in a property slot, a
  non-integer in a position slot or a non-type in `interArg`'s type slots stored, and now
  throws `:arg-type` where it is written. *Migration:* none for well-formed content; a KB
  already holding such a fact keeps it, a declaration arriving over stored content being
  reported by `exposed-clashes` rather than thrown. *Breaks:* `assert` / `load-text!` /
  `lein cli assert` / `lein cli load` on `(transitive 42)`, `(interArg P "one" …)` and the
  like [docs/argtypes.md](docs/argtypes.md), [docs/kbs.md](docs/kbs.md)

- **An undeclared predicate's arity is the majority of its facts, not the first row.**
  *Class:* **Additive**: nothing public moves — the fallback is private to the inventory,
  and the arity that changes is one that had no fixed value to change from.
  [docs/llm.md](docs/llm.md), [docs/defenses.md](docs/defenses.md)

- **A map or a set anywhere in a sentence is refused.** *Class:* **Refusal**: a sentence
  carrying a map or set stored, and now throws where it is written. *Migration:* spell the
  value as a vector of pairs, or mint a term for it; a KB already holding one keeps it,
  stored content not being re-checked. *Breaks:* `assert` / `assert-rule` / `edit!` /
  `load-text!` / `lein cli assert` / `lein cli load` on a sentence with a map or set in any
  position [docs/storage.md](docs/storage.md),
  [docs/canonicalization.md](docs/canonicalization.md)

- **A bulk index load refuses (`:stacked-batch`) rather than overwriting what moved under
  it.** *Class:* **Refusal**. *Migration:* run one bulk load at a time over a space; a
  caller that nested two was already losing the inner one's entries. *Breaks:* a nested
  `with-bulk-writes` over one space now throws where it silently dropped the inner batch.
  [docs/storage.md](docs/storage.md)

- **Three option entry points on the operational surface refuse a value they do not read.**
  *Class:* **Refusal**: each of the three took the value and ran at a setting nobody chose.
  *Migration:* spell the option as the page, the flag or `client`'s docstring names it.
  *Breaks:* `/kbs` with an unknown choice value, `lein serve --listen <flag>`,
  `vaelii.client/client` with a key outside `:timeout-ms` / `:token`
  [docs/operations.md](docs/operations.md), [docs/catalog.md](docs/catalog.md)

- **The catalog refuses a misspelt `:belief?` and reads a blank search path as unset.**
  *Class:* **Fix**. *Migration:* none; a blank variable now means what an unset one does.
  [docs/catalog.md](docs/catalog.md)

- **One read answers "what can I ask about `X`?"** *Class:* **Additive** — three new public
  vars, one new op, one new CLI command; nothing existing moves, and the term page's three
  lines read the same as before. [docs/api.md](docs/api.md),
  [docs/troubleshooting.md](docs/troubleshooting.md), [docs/web.md](docs/web.md)

- **`why-not` can say which rule nearly fired.** *Class:* **Additive** — one new arity,
  three new public vars, one new CLI flag; the two existing arities answer exactly what they
  did. The CLI command takes a goal *or* a handle, and the flag belongs to the goal — a
  stored handle is stored, so `:not-stored` is not an answer it can get — so that pairing is
  refused rather than dropped, which is `check-flags!`'s rule one level in.
  [docs/api.md](docs/api.md), [docs/troubleshooting.md](docs/troubleshooting.md)

- **Two KBs can be compared as knowledge rather than as stores.** *Class:* **Additive** —
  one new public fn, one new op, one new CLI command. [docs/api.md](docs/api.md),
  [docs/operations.md](docs/operations.md)

- **Every refusal the tree raises is one a test provokes and a reader can look up.**
  *Class:* **Additive** — a documentation section and a test; no keyword moves.
  [docs/troubleshooting.md](docs/troubleshooting.md)

- **A refusal message names what it received and what it accepts.** *Class:* **Fix**.
  *Migration:* none; a caller reading a message rather than a `:type` reads different prose.
  [docs/troubleshooting.md](docs/troubleshooting.md)

- **Two refusals name themselves where they threw bare.** *Class:* **Fix**. *Migration:*
  none. [docs/foreign.md](docs/foreign.md), [docs/operations.md](docs/operations.md)

- **`:unrecovered-kb` carries one shape at both entry points.** *Class:* **Fix**. *Migration:* a
  caller reading `(:hazards ex-data)` off a refused `retract!` / `edit!` reads a vector of
  keys. [docs/storage.md](docs/storage.md)

- **The daemon serves the reads and writes the wire was short of.** *Class:* **Additive**:
  every op is new, no served op changes shape, and the three new writes are declared in
  `llm.tools/write-ops` so the model's tool set is still reads only.
  [docs/operations.md](docs/operations.md)

- **Every daemon op has a client wrapper, and the op table is what says so.** *Class:*
  **Additive**: vars and arities are added, none removed and none changed; the two `!`
  spellings still resolve and still answer, and `test/golden/api-surface.edn` moves only by
  growing. [docs/operations.md](docs/operations.md)

- **The engine's content order is public.** *Class:* **Additive**.
  [docs/api.md](docs/api.md)

- **The content order's last-resort branch stops reporting distinct values as equal.**
  *Class:* **Additive** — the affected pairs previously compared equal or in a
  print-dependent order, so no caller held an order over them that this can break.
  *Migration:* none. [docs/nmtms.md](docs/nmtms.md)

- **A KB writes the text format it is authored in.** *Class:* **Additive** — two new public
  fns (`vaelii.core/export-text!`, `vaelii.core/load-text!`), a new `--format text` on `lein
  cli export`; no existing behaviour changes. *Migration:* none. [docs/api.md](docs/api.md),
  [docs/kbs.md](docs/kbs.md)

- **`kb-quality` reads the rules against each other.** *Class:* **Additive**: two new keys
  on `kb-quality`'s map and two new sections in `quality-report`, both written only when the
  key is there, so a stored report from before them still renders; no public var changes and
  `test/golden/api-surface.edn` does not move. [docs/quality.md](docs/quality.md)

- **A stored claim that contradicts a known-true inherited claim is reported.** *Class:*
  **Additive**: a report where there was none, and one new key on one new `:kind` of clash
  entry — no public var moves, `test/golden/api-surface.edn` does not move, and a KB that
  declares no argument preservation is told so by one `empty?` on a roster kept at the store
  choke points, so nothing is added to the assert path it pays for.
  [docs/inherit.md](docs/inherit.md), [docs/nmtms.md](docs/nmtms.md)

- **An `exceptWhen` states a strength per half.** *Class:* **Additive**: a spelling where
  there was none — a `set/monotonic` in that position was refused as a literal before — and
  the three pairings that could already be written are written the same bytes, so only the
  fourth's export changes, from lossy to lossless. [docs/exceptions.md](docs/exceptions.md)

- **A fork answers the tally samplers itself and forwards the prefetch hint.** *Class:*
  **Additive**. [docs/overlay.md](docs/overlay.md)

- **`{:max-ms nil}` is accepted under an instrumented budget.** *Class:* **Fix**.
  *Migration:* none. [docs/anytime.md](docs/anytime.md)

- **`plan/*enabled*` false drops the cost ranking and keeps the readiness discipline.**
  *Class:* **Fix**. *Migration:* none; `plan/*enabled*` is `vaelii.impl` and its true root
  is unchanged. [docs/inference.md](docs/inference.md)

- **The planner's `est-matches` is one-sided everywhere it is read.** *Class:* **Fix**.
  *Migration:* none. [docs/indexing.md](docs/indexing.md)

- **A `:put` or `:delete` on an argument-root key inside a `kv-batch` applies on every
  backend.** *Class:* **Fix**. *Migration:* none. [docs/indexing.md](docs/indexing.md),
  [docs/storage.md](docs/storage.md)

- **The disk record store's resident state is written under the monitor its files are
  written under.** *Class:* **Fix**. *Migration:* none. [docs/storage.md](docs/storage.md)

- **The two snapshot protocols are pinned extension protocols.** *Class:* **Additive**: a roster
  entry and four golden lines, no method moves. [docs/storage.md](docs/storage.md)

- **Both readings of an index posting are named, and the raw read is refused.** *Class:*
  **Additive**: no public var changes and no answer moves — the entry points wrap the reads their
  callers already made. [docs/nmtms.md](docs/nmtms.md)

- **A global taxonomy closure read says `-global`.** *Class:* **Additive**:
  `vaelii.impl.taxonomy` is not a public namespace, `vaelii.core/genls` / `specs` / `genl?`
  keep both arities and both answers, and `test/golden/api-surface.edn` does not move.
  [docs/taxonomy.md](docs/taxonomy.md)

- **koinii is an app in the tree, not a corner of the engine.** *Class:* **Additive** — the
  six public namespaces are unchanged, and `vaelii.impl.*` is free to move without notice,
  so no pinned surface moved with it. Anything requiring the old namespace renames the
  prefix. [docs/koinii.md](docs/koinii.md), [docs/namespaces.md](docs/namespaces.md)

- **A multi-claim reply goes through the same entry points a single one does.** *Class:*
  **Refusal** — a batch that forged a speaker or aimed at the registry wrote knowledge
  attributed to someone who never said it, which no query could tell from the real thing.
  *Migration:* none for an honest caller. *Breaks:* `:koinii/speaker-mismatch`,
  `:koinii/creator-mismatch`, `:koinii/registry-forbidden` [docs/koinii.md](docs/koinii.md)

- **An agent context is marked as one, and a join refuses to graft under it.** *Class:*
  **Refusal** — a graft under another agent's context made one agent's claims
  indistinguishable from another's at every reader above it. *Migration:* a deployment that
  nested channels or rolled one up into another is unaffected; only a parent that is an
  agent's own context, or the registry, is refused. *Breaks:* `:koinii/not-a-channel`
  [docs/koinii.md](docs/koinii.md)

- **The contested-premise flag reads the conclusion the way the asker proves it.** *Class:*
  **Additive** — no working caller can observe it except where the old answer was wrong,
  which is the one place it changes. *Migration:* none; a caller that saw an empty list for
  a conclusion stored below its reading context now sees the contested premises.
  [docs/koinii.md](docs/koinii.md)

- **A reaped subscription spends the same catch-up budget a lag does.** *Class:* **Refusal**
  — the arm returned by not returning. *Migration:* a caller matching on
  `:koinii/catchup-thrashing` still matches; `:condition` is additive. *Breaks:*
  `:koinii/catchup-thrashing` [docs/koinii.md](docs/koinii.md)

- **A malformed marker is answered, not thrown.** *Class:* **Refusal**. *Migration:* a
  caller matching `:not-received` on a malformed marker sees `:malformed`; a well-formed
  marker for a sentence the seat does not hold still answers `:not-received`. A locator
  mangled in its `sha256:` tag now reads `:malformed` where it read `:locator-mismatch` —
  the digest never parsed, and reporting a mismatch implied a comparison that never
  happened. [docs/koinii.md](docs/koinii.md)

  *Breaks:* `dereference`, `resolve-by-locator`

- **A koinii registry read refuses two rows rather than naming one by position.** *Class:*
  **Refusal**: a registry that ever held two rows was silently halved by whichever came
  first, and the overwrite retracted that one. *Migration:* none for a well-formed registry;
  one holding two rows names them in the refusal. [docs/koinii.md](docs/koinii.md)

  *Breaks:* `set-trust!`, `trust-of`, `display-name-of`

- **koinii: a dispute is named by every handle in its clash.** *Class:* **Fix**.
  *Migration:* none for two-member disputes (the term is unchanged); a three-member one gets
  a term of its own. [docs/koinii.md](docs/koinii.md)

- **A catch-up poll that fails untyped is refused as `:koinii/feed-error`, a word the
  rosters can see.** *Class:* **Fix**. *Migration:* none.
  [docs/troubleshooting.md](docs/troubleshooting.md)

- **A documentation example that is a whole program is run by the suite.** *Class:*
  **Additive** — a fence marker and a test; no engine surface moves.
  [CONTRIBUTING.md](CONTRIBUTING.md)

- **The OpenCyc counts in the documentation are one cited reading rather than five
  independent ones.** *Class:* **Fix** — documentation only. [docs/kbs.md](docs/kbs.md),
  [docs/quality.md](docs/quality.md)

- **The suite scans itself for assertions that cannot fail.** *Class:* **Fix** — a test that
  reported a pass it had not earned now reports what it checks.
  [CONTRIBUTING.md](CONTRIBUTING.md)

- **`lein lint` fails on a git conflict marker in a tracked file.** *Class:* **Additive**: a
  gate that fails only on content no tree should hold.

- **The release's class check reads all four classes.** *Class:*` word it cannot place,
  because a word nothing recognises is read as Additive by everything downstream and the
  class is what decides the release number. **Fix** is the fourth class CONTRIBUTING §3.8
  names and the check places it: like Additive it owes neither a `*Breaks:*` line nor a `
  *Migration:*` line, since a Fix retires no name a sibling could be grepped for. Breaking
  and Refusal owe both, and a misspelt class — `Braeking` — is refused. *Class:*
  **Additive**: one release step reads one more word.

- **`lein bench-subgoal` measures whether a cross-query subgoal table would be hit, and it
  is not.** *Class:* **Additive**: a new `bench-*` alias and its namespace, nothing public
  moves and no golden shifts. [docs/inference.md](docs/inference.md)

- **`VAELII_PLAN=0` runs the whole suite with the cost ranking off, and the matrix runs what
  a change owes rather than everything.** *Class:* **Additive**: one test-harness switch and
  four script arguments, no entry point moved. [docs/inference.md](docs/inference.md),
  [docs/operations.md](docs/operations.md), [docs/storage.md](docs/storage.md)

- **The contracts that need two JVMs are tested with two JVMs.** *Class:* **Additive**: a
  test mark, a selector and an alias; no engine entry point moved.
  [docs/storage.md](docs/storage.md), [docs/operations.md](docs/operations.md)

- **`^:multi-jvm` is opt-in, and `:all` no longer adopts whatever mark is added next.**
  *Class:* **Additive**: one selector, one alias, one CI job.
  [docs/operations.md](docs/operations.md)

- **A bare keyword is not a test selector, and `lein test :llm some.ns` ran the whole
  suite.** *Class:* **Fix**. *Migration:* none; `lein test :llm` alone was always correct.
  [docs/operations.md](docs/operations.md)

- **The matrix dashboard alternates a command line with a bar, and stops walking down the
  screen.** *Class:* **Fix**. *Migration:* none; `SUITE_PROGRESS=lines` still forces the
  scrolling form. [docs/operations.md](docs/operations.md)

- **The exhaustive truncation sweep runs once rather than once per configuration, and in a
  couple of minutes where scratch space is cheap.** *Class:* **Additive**: a fourth test
  mark, a selector, an alias and one test-only switch; no engine entry point moved and no offset
  was dropped. [CONTRIBUTING.md](CONTRIBUTING.md), [docs/operations.md](docs/operations.md)
## 0.12.0 — 2026-08-23 — "query contexts, bulk loading, and a literal's type"

- **`resultIsa` and `resultGenl` are `result` and `genlResult`.** *Class:* **Breaking** for
  a KB or a tool that names either predicate. *Migration:* rename every occurrence —
  `resultIsa` → `result`, `resultGenl` → `genlResult`. The old names are gone rather than
  deprecated, and nothing reports one: an undeclared predicate stores clean, so a
  declaration still naming `resultIsa` constrains nothing and says nothing about it.
  [docs/nat.md](docs/nat.md)

  *Breaks:* `resultIsa`, `resultGenl`

- **The four function marks classify what they mark, and the reifiability criterion is
  written down.** *Class:* **Refusal** for a KB that marks one term both a function and a
  predicate, or that declares an `arg` / `genlArg` / `quotedArg` on a function. *Migration:*
  such a declaration constrained nothing before and constrains nothing now — drop it. A term
  genuinely holding both marks was already two things at once; keep the one its applications
  behave like. [docs/nat.md](docs/nat.md)

  *Breaks:* `reifiableFunction`, `unreifiableFunction`, `quotingFunction`, `contextDenotingFunction`

- **The faster reading of an unnamed context agreed with the reference in five fewer ways
  than it claimed.** *Class:* **Refusal** for that last one — such a firing drops its
  conclusion and is recorded like any other dropped one — and a **Fix** for the four above
  it. *Migration:* none — every case answered wrongly, threw, or wrote where nothing may be
  written. [docs/contexts.md](docs/contexts.md)

  *Breaks:* `ist`

- **A records read stays lazy, and a proof's witness is one of its bindings.** *Class:*
  **Fix**. *Migration:* a caller that had found the witness at the top level of a `:proof?`
  answer reads it from `:bindings` with every other binding; nothing else moves, and a
  bare-bindings answer is unchanged. The grouping `:proof?` gets is left as it is and
  documented instead — two proofs of one binding keep a witness each, which is the reading a
  proof asks for. [docs/api.md](docs/api.md)

  *Breaks:* `:proof?`

- **Three reads that could not answer the question answered empty instead.** *Class:*
  **Refusal**, all three. *Migration:* rename a goal variable spelled `?ctx`, or name a
  context to read in — at a named context there is no marker to collide with and `(p ?ctx
  ?b)` answers correctly, unchanged; give a context-denoting application its declaration and
  its ground arguments; and name a real context to the network reads.
  [docs/contexts.md](docs/contexts.md)

  *Breaks:* `?ctx` `qualitative-network` `possible-relations`

- **A literal argument is typed by what it is, and `arg` now says so.** *Class:* **Refusal**
  for a sentence putting a literal in a position typed against something its kind does not
  reach. *Migration:* none for a stored KB — `recover` replays content rather than
  re-checking it — but such a sentence is refused on re-assert. Widen the declaration to a
  type the kind reaches (`intangible` covers every literal), or drop it.
  [docs/argtypes.md](docs/argtypes.md), [docs/defenses.md](docs/defenses.md)

  *Breaks:* `:arg-type`, `:quoted-arg-type`

- **A result declaration binds the applications its function never mints.** *Class:*
  **Refusal** for a sentence putting a function application in a position typed against
  something the function's declared result does not reach. *Migration:* none for a stored KB
  — `recover` replays content rather than re-checking it — but such a sentence is refused on
  re-assert. Widen the declaration to a type the result reaches, drop the `result` /
  `genlResult`, or write the argument as a term. [docs/nat.md](docs/nat.md)

  *Breaks:* `result`, `genlResult`, `unreifiableFunction`, `:arg-type`, `:arg-genl`

- **An attitude is opaque: the asker's merges stop at the proposition.** *Class:*
  **Breaking** — a caller relying on the old answer was relying on an unsoundness.
  *Migration:* to get the substitution, assert the identity in the agent's context, where it
  is the agent's belief; a `genlCx` edge from the agent to the context holding the merge
  does the same for every merge that context states. *Breaks:* `believes` `modalPredicate`
  [docs/belief.md](docs/belief.md)

- **One vocabulary for the literal types, and `character_string` is retired.** *Class:*
  **Breaking** for a KB that names `character_string` — in a declaration, a rule, or a
  stored membership. *Migration:* rename every occurrence of `character_string` to `string`.
  The old name is gone rather than deprecated. [docs/argtypes.md](docs/argtypes.md)

  *Breaks:* `character_string`

- **A rule's shared variables are held to the argument constraints of every position they
  stand in.** *Class:* **Fix.** *Migration:* a KB holding such a rule keeps it; a rule
  re-asserted through the public entry point is refused, and the refusal names the variable.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A torn justification stream tears the import.** *Class:* **Fix.** *Migration:* none.
  [docs/operations.md](docs/operations.md)

- **An unsupported `:compression` is refused at the sink.** *Class:* **Fix.** *Migration:*
  none. [docs/operations.md](docs/operations.md)

- **A generated corpus is the same corpus however it is read.** *Class:* **Fix.**
  *Migration:* regenerate any saved generated corpus a comparison depends on.

- **The ASP backend frees what a failed solve leaves.** *Class:* **Fix.** *Migration:* none.
  [docs/asp.md](docs/asp.md)

- **The STP closure cache keys the tolerance its verdicts were read to.** *Class:* **Fix.**
  *Migration:* none. [docs/stp.md](docs/stp.md), [docs/qcn.md](docs/qcn.md)

- **A firing that subsumed under a negation names the edge it climbed, and an edge arriving
  after the facts reaches it.** *Class:* **Fix.** *Migration:* none.
  [docs/inference.md](docs/inference.md)

- **A portfolio races the tacticians it names.** *Class:* **Fix.** *Migration:* none.
  [docs/inference.md](docs/inference.md)

- **An inferred argument type is read from the asking context.** *Class:* **Fix** — a
  context answers fewer type goals, and each one it drops rested on a fact it cannot see.
  *Migration:* none. [docs/contexts.md](docs/contexts.md)

- **`prove-within` carries `:max-term-growth`.** *Class:* **Fix** — a budget key that was
  accepted and ignored now takes effect; a caller that never named it is unaffected, the
  shipped ceiling being what an unnamed one already meant. *Migration:* none.
  [docs/anytime.md](docs/anytime.md), [docs/inference.md](docs/inference.md)

- **Subsumption runs under a negation, the other way.** *Class:* **Additive** — a query that
  answered nothing now answers, and nothing stored changes shape; a KB with a rule on a
  negated antecedent does derive conclusions it did not, which is the point. *Migration:*
  none. [docs/inference.md](docs/inference.md), [docs/exceptions.md](docs/exceptions.md)

- **A negated `exceptWhen` conjunct is re-checked in both directions.** *Class:* **Fix.**
  [docs/exceptions.md](docs/exceptions.md)

- **The exposure sweep debits its budget once, and its empty gate runs first.** *Class:*
  **Fix** — a cost one, and a budget that reaches as far as it is sized to. *Migration:*
  none. [docs/nmtms.md](docs/nmtms.md)

- **`argue` explains a side a rule derived, not only a side the store holds.** *Class:*
  **Additive** — no existing key changes shape or drops, and a side carries at most one of
  the two. *Migration:* none. [docs/api.md](docs/api.md),
  [docs/inference.md](docs/inference.md)

- **Not naming a context no longer means the union.** *Class:* **Breaking** for a
  conjunctive read that relied on the union, and for any caller comparing whole answer maps
  from a read that passes a variable context (the witness is now among the bindings).
  *Migration:* pass `CxEverything` for the union, or a concrete context to scope the read.
  *Breaks:* `?ctx` [docs/contexts.md](docs/contexts.md),
  [docs/defenses.md](docs/defenses.md)

- **Three query contexts: `CxEverything`, `CxInference`, `CxNothing`.** *Class:*
  **Additive** — nothing about an existing read moves, `?ctx` included. *Migration:* none.
  [docs/contexts.md](docs/contexts.md), [docs/from-cyc.md](docs/from-cyc.md)

- **`CxInference` is answered two ways, and the bounded one is the default.** *Class:*
  **Additive** — the answers do not depend on the strategy, only what they cost does.
  *Migration:* none. [docs/contexts.md](docs/contexts.md),
  [docs/defenses.md](docs/defenses.md)

- **A placement is held to what a reader could have answered.** *Class:* **Fix** — the two
  strategies agree, which is what makes the default a cost decision. *Migration:* none.
  [docs/contexts.md](docs/contexts.md)

- **The enumerations promise a `java.util.Set`, and a store may compress it.** *Class:*
  **Additive** — every store the engine ships answers exactly what it answered; the contract
  now says what a store *may* answer. [docs/storage.md](docs/storage.md),
  [docs/defenses.md](docs/defenses.md)

- **`Tallying`: how many records, and is there one at all, without building the roster.**
  *Class:* **Additive** — a new optional protocol beside `Prefetching`; nothing an existing
  store does changes. [docs/storage.md](docs/storage.md)

- **`BulkLoading`: an `import!` writes its records through a sink a store can answer in
  bulk.** *Class:* **Additive** — a new optional protocol; every store the engine ships
  implements nothing and takes the loop. [docs/storage.md](docs/storage.md),
  [docs/defenses.md](docs/defenses.md)

- **`BulkAnnotating`: the premise marks and the provenance are written many at once too.**
  *Class:* **Additive.** [docs/storage.md](docs/storage.md)

- **The `:disk` record store bulk-loads too.** *Class:* **Additive**, with one new refusal
  type: `:bad-batch`, for a `:batch` that is not a positive number of records.
  [docs/storage.md](docs/storage.md)

- **`*prefetch-candidates*` refuses a value that is not a chunk, at the `binding`.**
  *Class:* **Fix.** *Migration:* a `binding` of `nil`, `0` or `true` now throws where it
  previously ran unhinted or failed mid-query; bind `false` or a chunk size (256 is the
  measured plateau). [docs/storage.md](docs/storage.md)

- **`recover` stops re-reading records the roster already answered for.** *Class:* **Fix**
  (a cost one, and no behaviour moves: a justification resting on a record the store lost is
  still left out of the network).

- **The recovery walks take the prefetch hint too.** *Class:* **Additive** — a second op on
  an optional protocol added in this same unreleased version; nothing implements it outside
  the Postgres adapter. [docs/storage.md](docs/storage.md)

- **`:pg-disk` names its directory, and the directory names its database.** *Class:*
  **Refusal** — `{:backend :pg-disk}` with no `:dir` had no correct meaning, and the backend
  is new in this release, so no caller is carrying one. *Migration:* name the directory.
  *Breaks:* `:pg-disk`, `:dir`, `:stale-index-records` [docs/storage.md](docs/storage.md)

- **A fork's own records cannot be `:pg`.** *Class:* **Fix.**

- **One database keys one index, however it is spelled.** *Class:* **Fix.**
  [docs/storage.md](docs/storage.md)

- **`:sqlite` and `:disk` records in one directory no longer share an index.** *Class:*
  **Fix.**

- **A prefetch hint for a record store whose fetch is not local.** *Class:* **Additive** — a
  new optional protocol and one setting that defaults off; nothing changes for a KB that
  leaves it alone. [docs/storage.md](docs/storage.md)

- **Postgres records: `:pg-memory` and `:pg-disk`.** *Class:* **Additive** — new backend
  names and one new option; a KB naming neither is unchanged. The durable `:disk` index now
  pairs with `:pg` records as well as `:disk`, where it refuses RAM ones and `:sqlite` as
  before. [docs/storage.md](docs/storage.md)

- **Five refusals the daemon answered 500 for are the caller's mistake.** *Class:* **Fix.**
  *Migration:* a client discriminating on the status rather than on `:type` sees five 500s
  become 400s. [docs/operations.md](docs/operations.md)

- **A tool argument the chosen signature cannot read is refused, not dropped.** *Class:*
  **Fix.** *Migration:* none. [docs/llm.md](docs/llm.md)

- **A feed subscription with a context and no goal is refused.** *Class:* **Fix.**
  *Migration:* none. [docs/feed.md](docs/feed.md)

- **`preview` and `edit-with-consequences!` refuse a cap that is not a positive integer.**
  *Class:* **Fix.** *Migration:* none. [docs/preview.md](docs/preview.md)

- **The proposal panel's apply refuses a target this process does not hold.** *Class:*
  **Fix.** *Migration:* none. [docs/web.md](docs/web.md)

- **`register-modal-predicate!` loses its `!`.** *Class:* **Breaking.** *Migration:* call
  `register-modal-predicate` — same arities, same return, the `!` spelling is gone.
  *Breaks:* `register-modal-predicate!` [docs/belief.md](docs/belief.md),
  [docs/api.md](docs/api.md)

- **The dense TMS's handle-ceiling refusal carries a `:type`.** *Class:* **Additive.**
  *Migration:* none. [docs/density.md](docs/density.md)

- **The rounding grid follows `*quantity-tolerance*`.** *Class:* **Fix.** *Migration:* none.
  [docs/quantity.md](docs/quantity.md)

- **A confluence report names only overlaps a term can reach.** *Class:* **Fix** — a warning
  is withdrawn, none is added. *Migration:* none. [docs/equational.md](docs/equational.md)

- **An unrepaired reified-NAT collision is swept against one expression.** *Class:* **Fix.**
  *Migration:* none. [docs/nat.md](docs/nat.md)

- **A koinii commit id is a function of belief, not of storage.** *Class:* **Breaking** —
  every id a seat computes moves, and a defeat moves it as a retraction does. *Migration:*
  re-derive any stored commit id or state root; ids taken before this are not comparable
  with ids taken after. *Breaks:* `commit-id`, `state-root`, `inclusion-proof`
  [docs/koinii.md](docs/koinii.md)

- **A koinii write is stamped by the identity it is made through.** *Class:* **Breaking.**
  *Migration:* drop the `:creator` from a `channel/assert` call (it was already the
  agent's), and take a compressed dump with `export!` directly, which makes no
  byte-stability claim. *Breaks:* `:koinii/creator-mismatch`, `:koinii/compression-pinned`,
  `publish!` [docs/koinii.md](docs/koinii.md)

- **The koinii adjudication reads follow belief.** *Class:* **Fix.** *Migration:* none.
  [docs/koinii.md](docs/koinii.md)

- **A catch-up poll that fails is a failure whatever it threw.** *Class:* **Fix.**
  *Migration:* none. [docs/koinii.md](docs/koinii.md)

- **Exactly one of several concurrent `unwatch`es of one token says it removed something.**
  *Class:* **Fix.** *Migration:* none. [docs/feed.md](docs/feed.md)

- **An LLM error body rides bounded in the message and whole in the data.** *Class:*
  **Fix.** *Migration:* a caller that parsed the failing body out of the message reads
  `:body` instead. [docs/llm.md](docs/llm.md)

- **A generated corpus counts its context edges, and draws direction and defeasibility
  separately.** *Class:* **Fix.** *Migration:* regenerate any saved generated corpus a
  comparison depends on. [docs/catalog.md](docs/catalog.md)

- **A compaction drops a handle whose frame the log cannot give back.** *Class:* **Fix.**
  *Migration:* none. [docs/storage.md](docs/storage.md)

- **The durability tick adds no work on a store nobody wrote to.** *Class:* **Fix.**
  *Migration:* none. [docs/storage.md](docs/storage.md)

- **The durability daemon installs one ticker and forgets no backend.** *Class:* **Fix.**
  *Migration:* none. [docs/storage.md](docs/storage.md)

- **The disk lock tells a second JVM from a second copy of itself, and keeps what it could
  not give back.** *Class:* **Fix.** *Migration:* none. [docs/storage.md](docs/storage.md)

- **An `:xz` dump allocates a dictionary the size of a chunk.** *Class:* **Fix.**
  *Migration:* none. [docs/namespaces.md](docs/namespaces.md)

- **A remote `why` re-asks a truncated proof deeper.** *Class:* **Additive.**
  [docs/api.md](docs/api.md)

- **Which justifications a rule exception blocks is a served read.** *Class:* **Additive.**
  [docs/exceptions.md](docs/exceptions.md)

- **The neighbour sets a closure walk builds are counted.** *Class:* **Additive.**
  *Migration:* none. [docs/caches.md](docs/caches.md), [docs/web.md](docs/web.md)

- **Three CLI commands print their answer sorted.** *Class:* **Fix.** *Migration:* a script
  depending on the previous output order of `match` / `query` / `ask` reads a different one.
  [docs/operations.md](docs/operations.md)

- **The log level survives a reload of the namespace that holds it.** *Class:* **Fix.**
  *Migration:* none. [docs/operations.md](docs/operations.md)

- **The browser refuses a request parameter it cannot read.** *Class:* **Fix.** *Migration:*
  a bookmarked URL carrying an unreadable value answers 400 rather than a page.
  [docs/web.md](docs/web.md)

- **A cancelled job's interrupt cannot reach a thread it has released.** *Class:* **Fix.**
  *Migration:* none. [docs/web.md](docs/web.md)

- **The profiler UI starts once under a race as well as under a reload.** *Class:* **Fix.**
  *Migration:* none. [docs/web.md](docs/web.md)

- **A term graph draws the same neighbours whatever else was asserted first.** *Class:*
  **Fix.** *Migration:* none. [docs/web.md](docs/web.md)

- **A post-join antecedent that answers two ways concludes nothing.** *Class:* **Fix.**
  *Migration:* none — a KB whose post-join literals are the built-in computations cannot
  reach it. [docs/aggregate.md](docs/aggregate.md)

- **An aggregate over measures renders in one unit whatever order they arrived in.**
  *Class:* **Fix.** *Migration:* none. [docs/quantity.md](docs/quantity.md)

- **A capped backward proof answers the same whichever order the rules arrived.** *Class:*
  **Fix.** *Migration:* none, unless a caller had pinned which single answer a capped
  `prove` returned. [docs/nmtms.md](docs/nmtms.md)

- **`nm/name-key` and `nm/by-print-key`, and no ordering key is a bare `str`.** *Class:*
  **Additive.** *Migration:* none. [docs/nmtms.md](docs/nmtms.md)

- **Two scaling claims are gated.** *Class:* **Additive.** *Migration:* none.
  [docs/qcn.md](docs/qcn.md)

- **`/levels` refuses a query context rather than failing on one.** *Class:* **Refusal.**
  *Migration:* none — no page produces such a URL, and a hand-written one gets a page
  instead of an error. *Breaks:* `/levels`, `/levels/rows` [docs/web.md](docs/web.md)

- **A continuation offset is capped, so a hand-edited one cannot overflow the arithmetic.**
  *Class:* **Fix.** *Migration:* none. [docs/web.md](docs/web.md)

- **A CSS width is written with a dot whatever the machine's locale.** *Class:* **Fix.**
  *Migration:* none. [docs/web.md](docs/web.md)

- **`POST /propose/level` is guarded exactly as the row it reposts.** *Class:* **Refusal.**
  *Migration:* none. *Breaks:* `/propose/level` [docs/web.md](docs/web.md)

- **Cancelling a job that has already finished answers false.** *Class:* **Fix.**
  *Migration:* a caller reading the answer as "the registry still holds this id" now reads a
  settled job as absent — ask `jobs/job` for that question instead.
  [docs/web.md](docs/web.md)

- **A koinii ballot is declared, so it cascades with the claim it was cast on.** *Class:*
  **Fix.** *Migration:* none — a KB that loads `CxSpeechActs` picks the marks up on the next
  load; ballots already stored on a claim that has since gone are orphans no cascade will
  reach, and are found by matching `(votesFor ?a (sentexHandle ?h))` against the handles the
  store still holds. [docs/koinii.md](docs/koinii.md)

- **Cross-seat dereference follows belief, as the commit id already did.** *Class:*
  **Breaking** for a caller resolving an unbelieved record. *Migration:* read the store
  directly (`handle-of` / `sentex`) where storage rather than belief is the question; a
  caller discriminating on `:reason` gains one value to match. *Breaks:* `dereference`
  `resolve-by-locator` [docs/koinii.md](docs/koinii.md)

- **Two koinii channel entry points stop nil-punning their argument.** *Class:* **Refusal.**
  *Migration:* none. *Breaks:* `channel/dispute`, `speech-acts/dispute`, `channel/vote`,
  `:koinii/no-such-handle`, `:koinii/no-such-stance` [docs/koinii.md](docs/koinii.md)

- **A wire subscription that dies says so, and a dropped event is not silent.** *Class:*
  **Additive.** *Migration:* none — a supplied handler still replaces the line.
  [docs/koinii.md](docs/koinii.md)

- **A refused arbiter ruling ends no dispute episode.** *Class:* **Fix.** *Migration:* none.
  [docs/koinii.md](docs/koinii.md)

- **A model host that never answers costs seconds, not the turn's whole budget.** *Class:*
  **Fix.** *Migration:* none — a caller that wanted a long connect deadline never had a way
  to ask for one. [docs/llm.md](docs/llm.md)

- **A sentence carrying an escaped non-ASCII character reads back with that character.**
  *Class:* **Fix.** *Migration:* none. [docs/llm.md](docs/llm.md)

- **A judged run's token counts add across batches instead of throwing.** *Class:* **Fix.**
  *Migration:* a `:usage` map now omits a key no host reported, where a single-batch run
  once carried it as nil. [docs/commonsense.md](docs/commonsense.md)

- **A tool failure with no message is named by its class.** *Class:* **Fix.** *Migration:*
  none. [docs/llm.md](docs/llm.md)

- **The vocabulary inventory says how many lines it left out.** *Class:* **Fix.**
  *Migration:* none. [docs/llm.md](docs/llm.md)

- **A test that reaches a model without the `^:llm` mark now fails the suite's own scan.**
  *Class:* **Additive.** *Migration:* a test that genuinely reaches a host carries the mark
  and the gate; one that exercises a probe offline pins the var it reaches through.
  [docs/llm.md](docs/llm.md)

### Performance

Six changes to what a read or a write costs. None of them moves an answer; the one that
moves a counted read says so.

- **A literal with no symmetric sub-predicate pays for one answer, not a mirror's two.**
  *Class:* neither label. [docs/indexing.md](docs/indexing.md)

- **A closure walk is a scan, so it neither reads the literal cache nor fills it.** *Class:*
  neither label. [docs/caches.md](docs/caches.md)

- **The reader set stops meet-closing the lattice against itself.** *Class:* neither label.
  [docs/contexts.md](docs/contexts.md)

- **The join budget stops charging for the read it was meant to guard.** *Class:* neither
  label. [docs/contexts.md](docs/contexts.md)

- **The belief flag is read once a retrieval path, not once a candidate.** *Class:* neither
  label. [docs/belief.md](docs/belief.md)

- **Two constants stop being recomputed on the hottest write paths.** *Class:* neither
  label. [docs/qcn.md](docs/qcn.md), [docs/nmtms.md](docs/nmtms.md)
## 0.11.0 — 2026-08-22 — "contradiction solving, arrival order, and the durable log"

- **`antiTransitive` convicts the chain it forbids.** *Class:* **Breaking** — a KB that
  declared the mark and stored a chain is now told about it, and `:nogood` / `:handles` /
  `:sides` on a clash report can hold three members where a reader may have assumed two.
  *Migration:* drop the mark, or state the chain's exception, where the declaration was
  documentation rather than a constraint. *Breaks:* `antiTransitive`, `:anti-transitive`,
  `:opposing-handles`, `contradictions`, `conflicts`, `check`
  [docs/nmtms.md](docs/nmtms.md), [docs/taxonomy.md](docs/taxonomy.md)

- **Register a computed predicate or function in one line.** *Class:* **Additive** — one new
  public fn (`vaelii.core/add-evaluatable`); no existing behaviour changes and nothing to
  migrate. [docs/inference.md](docs/inference.md), [docs/api.md](docs/api.md)

- **Definitional collection relations: membership tied to a defining condition.** *Class:*
  **Additive** — new `CxCore` vocabulary and one derivation off it; a KB using neither
  predicate is unchanged. [docs/defns.md](docs/defns.md)

- **Sibling disjointness: a collection's specializations separate themselves.** *Class:*
  **Additive** — new vocabulary and one taxonomy cache; a KB naming no `siblingDisjoint`
  behaves exactly as before. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/glossary.md](docs/glossary.md)

- **An escape hatch for a pair that must overlap.** *Class:* **Additive** — new vocabulary
  and one taxonomy cache; a KB naming no `siblingDisjointException` behaves exactly as
  before. [docs/taxonomy.md](docs/taxonomy.md), [docs/from-cyc.md](docs/from-cyc.md)

- **Why a sentex is believed, or is not, as a map instead of a bisection.** *Class:*
  **Additive** — two new public fns; nothing existing moves. [docs/api.md](docs/api.md),
  [docs/exceptions.md](docs/exceptions.md)

### One handle per canonical sentence

- **A bulk run's authority memo follows the handle cache's generation.** *Class:* Fix; a KB
  that derived a declaration mid-chain held duplicate records.
  [docs/canonicalization.md](docs/canonicalization.md),
  [docs/inference.md](docs/inference.md)

- **A non-ground sentence resolves to the handle whose stored sentence it equals.** *Class:*
  Fix; an exception that was silently dropped is now stored.
  [docs/exceptions.md](docs/exceptions.md),
  [docs/canonicalization.md](docs/canonicalization.md)

### The same knowledge in any order

- **An asymmetric twin stored in the vantage is a partner, not the sentence itself.**
  *Class:* Fix on order independence. [docs/nmtms.md](docs/nmtms.md)

- **Metatype membership records on the mark's storage, not its belief.** *Class:* Fix on
  order independence. [docs/taxonomy.md](docs/taxonomy.md)

- **A firing bound to a merged term is always an exception candidate.** *Class:* Fix on
  order independence. [docs/exceptions.md](docs/exceptions.md),
  [docs/equality.md](docs/equality.md)

- **A cycle-closing `genlCx` edge condenses the relation in place.** *Class:* Fix on order
  independence. [docs/taxonomy.md](docs/taxonomy.md), [docs/contexts.md](docs/contexts.md)

- **A symmetric fact reaches a rule the same way at either position.** *Class:* Fix on order
  independence. [docs/inference.md](docs/inference.md), [docs/inherit.md](docs/inherit.md)

- **A symmetric fact answers twice when the pattern asks twice.** *Class:* Fix on order
  independence. [docs/indexing.md](docs/indexing.md), [docs/inference.md](docs/inference.md)

- **A block condition is one question, asked under one spelling.** *Class:* Fix on order
  independence. [docs/exceptions.md](docs/exceptions.md), [docs/naf.md](docs/naf.md)

- **The derivation path reaches every integrate arm the rebuild does.** *Class:* Fix; the
  live KB and the recovered one answer alike. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/exceptions.md](docs/exceptions.md)

### Storage and the durable log

- **A dedup probe reads the exact leaf, not a match of it.** *Class:* **Breaking** — one
  method added to the `IndexStore` protocol, so an out-of-tree index implements `leaf-at`; it is
  the leaf handles at an exact path, which every trie already holds. *Migration:* implement
  `leaf-at`; the shipped backends all carry it. *Breaks:* `leaf-at`, `IndexStore`,
  `find-sentex-handle` [docs/indexing.md](docs/indexing.md),
  [docs/storage.md](docs/storage.md)

- **An append is all or nothing.** *Class:* Fix; a durable store could lose committed
  records to a partial write. [docs/storage.md](docs/storage.md)

- **A compaction that fails past its commit point retries, then refuses.** *Class:*
  **Additive** — one new refusal `:type`. [docs/storage.md](docs/storage.md)

- **The durable token dictionary is keyed as the in-RAM one is.** *Class:* Fix; an index
  snapshot over numeric arguments now reloads. [docs/storage.md](docs/storage.md),
  [docs/indexing.md](docs/indexing.md)

- **...and a log that already holds such a pair is repaired, not rediagnosed forever.**
  *Class:* Fix; one open repairs it and the next maps its image.
  [docs/storage.md](docs/storage.md)

- **A stray unindex touches nothing.** *Class:* Fix; a double retraction could unindex a
  believed sentex. [docs/indexing.md](docs/indexing.md)

- **A durable fork gates and rebuilds its own half through the merged mount.** *Class:* Fix;
  a remounted fork answered with facts it had retracted. [docs/overlay.md](docs/overlay.md)

- **A bulk load's transient takes only its own backend's writes.** *Class:* Fix; concurrent
  KBs on one thread no longer cross. [docs/storage.md](docs/storage.md)

- **A frame reader releases its file when the consumer stops early.** *Class:* Fix.
  [docs/storage.md](docs/storage.md)

- **A divergent unindex says so, and a counter is a cardinality.** *Class:* Breaking for an
  out-of-tree `KvBackend`, which now fails `kv_backend_test` if it lets one go negative.
  *Migration:* floor `kv-decrement` at zero in an out-of-tree `KvBackend`; the shipped
  backends already do. *Breaks:* `kv-decrement` [docs/indexing.md](docs/indexing.md)

- **Record fetches are counted, beside the index reads.** *Class:* **Additive** — one new
  snapshot key. [docs/storage.md](docs/storage.md), [docs/profile.md](docs/profile.md)

### Inference

- **A term-growing subgoal is cut at a ceiling over the query's depth.** *Class:* Breaking;
  a search that ran forever now stops. *Migration:* raise `:max-term-growth` for a proof
  that genuinely builds terms. *Breaks:* `:max-term-growth`, `prove`, `provable?`,
  `explain-levels` [docs/inference.md](docs/inference.md), [docs/levels.md](docs/levels.md)

- **A variable-functor goal expands every rule, not none.** *Class:* Fix; an open-predicate
  query returns derived answers. [docs/inference.md](docs/inference.md),
  [docs/indexing.md](docs/indexing.md)

- **A deadline stops the node engine at the next expansion, not the next answer.** *Class:*
  Fix on the anytime contract. [docs/anytime.md](docs/anytime.md)

### Contradiction solving

- **A solve that returned no answer set is not read as defeat-everything.** *Class:*
  Breaking; a caller reading a solve that did not finish now meets a refusal instead of a
  silent verdict. *Migration:* catch `:solver-failed` where a solve may be interrupted, or
  lift the time limit with `VAELII_ASP_TIME_LIMIT=0`. *Breaks:* `:solver-failed`,
  `:interrupted`, `kept-of`, `enumerate-optima`, `classify-program`
  [docs/asp.md](docs/asp.md), [docs/solving.md](docs/solving.md)

- **Every solve is bounded by a time limit.** *Class:* **Additive** — one setting and one
  status; a solve that finished inside a minute is unchanged. [docs/asp.md](docs/asp.md),
  [docs/operations.md](docs/operations.md)

- **The solve sweep takes a context's extent, not everything about it.** *Class:* Fix.
  [docs/labeling.md](docs/labeling.md)

- **One ruling per arbiter per dispute.** *Class:* Fix, plus one new public read
  (`standing-rulings`) and a `:withdrawn` key on the result.
  [docs/koinii.md](docs/koinii.md)

- **...and a ruling is found again for every dispute it settles.** *Class:* Breaking on one
  impl read (`who-ruled` answers `:dispute-ids`), Additive for the refusal. *Migration:*
  read `who-ruled`'s `:dispute-ids` as a set where a single id was expected, and name an
  arbiter who is not a party to the dispute. *Breaks:* `who-ruled`, `:dispute-ids`,
  `:arbiter-is-party` [docs/koinii.md](docs/koinii.md)

- **The edge solver refuses rather than degrades when a backend is present.** *Class:*
  Breaking; a caller reading `{:defeat :violated}` also gets `:error`. *Migration:* handle
  `:error` where the degraded local answer was relied on, or lift the bound with
  `VAELII_ASP_TIME_LIMIT=0` so the solve finishes. *Breaks:* `:error`, `edge-solver`,
  `:solver-failed` [docs/asp.md](docs/asp.md)

- **A backend failure is a result, not an exception through a settle.** *Class:* Fix.
  [docs/asp.md](docs/asp.md)

- **An infeasible program has no labeling, in every mode.** *Class:* Breaking; the two modes
  documented as feasible at scale now report `:count 0 :reason :unsatisfiable`. *Migration:*
  read `:count` rather than treating a returned labeling as evidence the program was
  feasible. *Breaks:* `:unsatisfiable` [docs/solving.md](docs/solving.md)

- **A negated choice literal binds its own variables.** *Class:* Fix.
  [docs/solving.md](docs/solving.md)

- **A run that cannot replace the last one refuses instead of writing beside it.** *Class:*
  Additive — one new refusal `:type` (`:labeling-run-blocked`).
  [docs/solving.md](docs/solving.md), [docs/troubleshooting.md](docs/troubleshooting.md)

- **The `:violated` reading is content-ordered.** *Class:* Fix. [docs/asp.md](docs/asp.md)

- **`VAELII_ASP_TIME_LIMIT` bounds one solve, and an operation makes several.** *Class:*
  neither label; what changed is what the KB says about itself. [docs/asp.md](docs/asp.md),
  [docs/operations.md](docs/operations.md)

### Equality, taxonomy and dates

- **`kbo>` decides an equal-weight pair that differs at a constant.** *Class:* Fix; a
  schematic equation that threw is now oriented. [docs/equational.md](docs/equational.md)

- **`del-equality!` drops the retracted handle from the partition's `:out`.** *Class:* Fix.
  [docs/equality.md](docs/equality.md)

- **A datetime bounds its date and time halves separately.** *Class:* Refusal; a string that
  parsed into nonsense is refused. [docs/time.md](docs/time.md)

### The API, the web and jobs

- **`query` refuses an option it does not read.** *Class:* Breaking; a key `query` ignored
  is now `:unknown-option`. *Migration:* spell the rostered key. *Breaks:*
  `:unknown-option`, `query-opt-keys`, `query`, `query?` [docs/api.md](docs/api.md)

- **A write entry point judges and writes one KB, resolved once per request.** *Class:* Fix.
  [docs/web.md](docs/web.md)

- **`reset-registry!` waits for a cancelled job to stop before forgetting it.** *Class:*
  Fix. [docs/operations.md](docs/operations.md)

- **One export at a time is checked and claimed as one step.** *Class:* Fix.
  [docs/catalog.md](docs/catalog.md)

- **`::context` admits a context-denoting application.** *Class:* Fix under `instrument`
  only. [docs/context-nat.md](docs/context-nat.md)

- **`serve`'s `-main` passes the thread-pool size, as `start` does.** *Class:* Fix.
  [docs/operations.md](docs/operations.md)

- **A refusal names the KB it judged, not the active one.** *Class:* Fix.
  [docs/web.md](docs/web.md)

- **`argue` holds `query`'s roster at its own entry point, and each debugger entry point rosters what it
  reads.** *Class:* Breaking; a key these entry points ignored is now `:unknown-option`.
  *Migration:* spell the rostered key, and stop passing `:strategy` or `:proof?` to the
  debugger entry points, which set both themselves. *Breaks:* `argue`, `search-tree`,
  `compare-tacticians`, `:unknown-option` [docs/api.md](docs/api.md)

### Efficiency

None of these change an answer; each is pinned by a test that fails on the old cost.

- **The forward join takes its argument lead only where there is a fan to collapse.**
  [docs/inference.md](docs/inference.md)

- **The supersession refresh takes the region the finish already read.**
  [docs/nmtms.md](docs/nmtms.md)

- **A clingo drain keeps the models its mode reads.** [docs/asp.md](docs/asp.md)

- **An export drains the writes it must and holds nothing after.**
  [docs/web.md](docs/web.md)

- **Four new counted gates, because a ratio cannot see a constant.**
  [docs/profile.md](docs/profile.md)

- **One `except` no longer turns `context-down` into N filtered walks.**
  [docs/taxonomy.md](docs/taxonomy.md)

- **A settle reads its relabelled region once per pass.** [docs/nmtms.md](docs/nmtms.md)

- **A negated antecedent is keyed by its body's predicate.**
  [docs/indexing.md](docs/indexing.md)

- **A bound-argument antecedent joins through the argument lead.**
  [docs/indexing.md](docs/indexing.md)

- **A candidate rule's view is built once an antecedent unifies**
  [docs/inference.md](docs/inference.md)

- **`explain` costs its report off the ranking's memoized reads**
  [docs/inference.md](docs/inference.md)

- **`find-terms` with a `:limit` selects its n smallest** [docs/api.md](docs/api.md)

- **The web view holds the type set by reference** [docs/web.md](docs/web.md)

- **An LLM tool result is printed into a bounded writer** [docs/llm.md](docs/llm.md)
## 0.10.0 — 2026-08-20 — "more than one agent over one knowledge base"

- **Koinii: several agents coordinate over one shared knowledge base.** *Class:*
  **Additive** — a new optional layer and two shipped contexts (`resources/kb/koinii/`); no
  existing behaviour changes. [docs/koinii.md](docs/koinii.md), [docs/feed.md](docs/feed.md)

- **Belief projection: what an agent holds true.** *Class:* **Additive** — new vocabulary
  and two public reads; nothing existing changes. [docs/belief.md](docs/belief.md)

- **A context can be a reified function application, and its `genlCx` edges compute
  themselves.** *Class:* **Additive** — a new context shape and vocabulary; object NATs are
  refused as contexts exactly as before. [docs/context-nat.md](docs/context-nat.md),
  [docs/nat.md](docs/nat.md)

- **Mention-opacity: a quoting function reads its argument by spelling.** *Class:*
  **Additive** — a new predicate property and constructor; a term naming neither reads
  exactly as before. [docs/glossary.md](docs/glossary.md),
  [docs/argtypes.md](docs/argtypes.md)

- **`quotedArg` types an argument as a term against a syntactic type.** *Class:*
  **Additive** — one new refusal `:type` a caller may now meet and inert vocabulary now
  read; no existing declaration changes behaviour. [docs/argtypes.md](docs/argtypes.md),
  [docs/glossary.md](docs/glossary.md)

- **The argument-constraint family is renamed to a shorter, regular scheme.** *Class:*
  **Breaking** — three shipped KB predicate names changed, so a KB text, rule or `isa?`
  naming an old spelling answers nothing. *Breaks:* `argIsa`, `argGenl`, `interArgIsa`.
  *Migration:* rename all three in your KB text — `argIsa → arg`, `argGenl → genlArg`,
  `interArgIsa → interArg`; nothing else changes. [docs/argtypes.md](docs/argtypes.md),
  [docs/inherit.md](docs/inherit.md)

- **A sentence carrying a non-serializable value is refused at every entry point.** *Class:*
  **Refusal** — accepting the value stored a sentence no `:disk` KB could recover, so no
  working caller is broken. *Breaks:* `:not-encodable`. *Migration:* replace the
  non-serializable leaf with data. [docs/storage.md](docs/storage.md)

- **New public reads for handles and un-stored canonical form, and `argue` is public.**
  *Class:* **Additive** — five public reads; nothing existing changes.
  [docs/api.md](docs/api.md)

- **The fast gate drops perf; `release-gate` keeps it.** *Class:* **Additive** — a
  build-command split; no engine behaviour changes.
## 0.9.0 — 2026-08-17 — "the truth-maintenance network defaults to dense"

- **The dense truth-maintenance network is the default.** *Class:* **Breaking** — a
  documented default changes, and `catalog/footprint`'s `:tms` estimate drops 467 → ~101
  B/sentex to match. No answer, match or ordering moves — only the representation and the
  footprint number. *Breaks:* the `:tms` default. *Migration:* pin `:tms :reference` to keep
  the persistent-map network and the old footprint figure.
  [docs/density.md](docs/density.md), [docs/nmtms.md](docs/nmtms.md)

- **The dense network gives a concurrent reader a consistent view.** *Class:* Additive — no
  answer, match or API changes; a race that could tear or fault a read on the new default
  now cannot. `jtms_concurrency_test`. [docs/density.md](docs/density.md),
  [docs/storage.md](docs/storage.md)

- **Four relation properties, enforced.** *Class:* **Additive** — two new refusal `:type`
  keywords a caller may now meet, and vocabulary that was inert before is now read; no
  existing declaration changes behaviour. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/nmtms.md](docs/nmtms.md)

- **A subsumption rests on its strongest route, not its shortest.** *Class:* **Breaking** —
  `defeat-class` of a conclusion reached across a taxonomy that offers two routes at
  different strengths can rise from `:default` to `:monotonic`; no answer *set* changes.
  *Breaks:* `defeat-class`. *Migration:* re-read `defeat-class` on such conclusions; the
  shortest-path placement witness is unchanged. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/defenses.md](docs/defenses.md)

- **An algebraic property is one predicate, not a mark and a twin.** *Class:* **Breaking** —
  a query, rule or `isa?` naming a `…Predicate` type now answers nothing; and because the
  surviving mark is a `decontextualizedPredicate`, its membership is read KB-wide rather
  than only in the context that once derived the twin. *Breaks:* `symmetricPredicate`,
  `asymmetricPredicate`, `transitivePredicate`, `reflexivePredicate`, `functionalPredicate`.
  *Migration:* replace `(…Predicate P)` with the bare mark, which answers the same
  membership. [docs/taxonomy.md](docs/taxonomy.md)

- **A rule may conclude a variable predicate.** *Class:* **Additive**; no rule that asserted
  before is refused, and one class of rule refused before now runs.
  [docs/indexing.md](docs/indexing.md)

- **The search a query would run, as data — and a debugger over it.** *Class:* **Additive**
  — two public reads and one route; nothing existing changes. [docs/web.md](docs/web.md),
  [docs/inference.md](docs/inference.md)

- **Which of my rules actually do anything — the chaining funnel.** *Class:* **Additive** —
  one public read and one route; nothing existing changes. [docs/web.md](docs/web.md),
  [docs/exceptions.md](docs/exceptions.md)

- **A rule is asked before it fires, and a definitional read is taken from where it is
  asked.** [docs/inference.md](docs/inference.md), [docs/contexts.md](docs/contexts.md),
  [docs/exceptions.md](docs/exceptions.md)

- **A dotted-rest pattern retrieves the facts it matches.** *Class:* **Additive** — a
  pattern shape that silently matched nothing now matches; no other shape changes.
  [docs/indexing.md](docs/indexing.md)

- **A clean cold open can skip the contradiction scan.** *Class:* **Additive** — one opt-in
  switch; nothing existing changes. [docs/storage.md](docs/storage.md),
  [docs/operations.md](docs/operations.md)

- **A third durable records backend, `:sqlite`.** *Class:* **Additive** — a new backend
  keyword; no existing pairing changes. [docs/storage.md](docs/storage.md)

- **`person` is a social agent, and `human` is the biological type.** *Class:* **Breaking**
  — a shipped taxonomy edge changed, so a query, rule or `isa?` that read a `person` as a
  `mammal`/`animal` answers differently. *Breaks:* the `person` membership entailment; the
  biological predicates now refuse a non-`animal` `person`. *Migration:* type biological
  individuals `(isa X human)` where you relied on `(isa X person)` implying `mammal` or
  `animal`; leave non-biological agents as `person`.
  [docs/commonsense.md](docs/commonsense.md)

- **`argPreserving` is renamed `transitiveInArg`.** *Class:* **Breaking** — a shipped KB
  predicate name changed. *Breaks:* `argPreserving`, `argPreservingInverse`. *Migration:*
  rename both in your KB text; nothing else changes. [docs/inherit.md](docs/inherit.md)

- **`argIsa` / `argGenl` / `interArgIsa` answer up the `genl` ancestor set.** *Class:* **Additive**
  — a query that answered nothing now answers; nothing stored or existing changes.
  [docs/argtypes.md](docs/argtypes.md), [docs/inherit.md](docs/inherit.md)
## 0.8.0 — 2026-08-14 — "predicates inherit down the hierarchy"

`arity`, `functional`, `asymmetric` and the three argument
constraints descend the predicate hierarchy now — at the entry point and on every retroactive
pass — so a claim spelled with a sub-predicate is held to what its supers declare, and
the six arrival orders of {declaration, fact, edge} reach one set of beliefs. Beside it
two structural gaps close: a KB whose derived state was never built refuses writes rather
than accepting them unchecked, and a firing rests on the `genlCx` edges its placement was
read over, so retracting one takes the conclusion back.

**Twenty entries are Breaking**, which is what makes this a minor rather than a point
release. Eight Refusal entries batch here rather than each forcing its own, which is what
§3.8 of `CONTRIBUTING.md` designates a minor for. Every Breaking and every Refusal entry
carries its *Migration* line, and every entry links the page that carries the mechanism —
an entry here says what moved and what to write instead, and the doc says how it works.

**Triage, for a 0.7.0 caller.** This is the index to what touches something you have
written.

| If your code… | Then |
|---|---|
| asserts a sub-predicate fact under a super's `argIsa` / `argGenl` / `interArgIsa` | refused `:arg-type`; widen the declaration, move it down, or drop the `genl` edge |
| declares an `arity` that disagrees with its super's | refused whichever sentence arrives second; give the two one arity, mark either end `variableArity`, or drop the edge |
| relies on `(functional P)` or `(asymmetric P)` binding P's exact functor alone | both convict a sub-predicate's tuples now, in either arrival order |
| reads an empty `violations` as a clean bill | `:arity` and `:constraint-exposure` entries appear in arrival orders that filed none, and a retraction no longer files `:no-placement` |
| branches on `violations`' `:violation` with a defaultless `case` | `:arity-truncated` and `:arity-report-truncated` are new kinds |
| counts `:arity` entries to size a problem | both retroactive passes file at most 8 and carry the totals on a truncation notice |
| writes to a KB opened `{:recover? false}`, or loaded `:belief? false` / `:belief? :stored` | refused `:unrecovered-kb`; call `recover` (or `reindex`) first, or bind `*write-unrecovered?*` |
| retracts against such a KB | refused, where it deleted the record and left its justifications dangling |
| spells one sentence as a top-level vector — `(assert kb '[likes Tom Ann])` | refused `:shape`; write the list, and ask a conjunction with `query` or `prove` |
| passes a non-map where an option map goes, `(open-kb :nope)` among them | `:unknown-option` by name, where it threw an unnamed error |
| reads `why`'s `:because`, `why-not`'s `:missing` or `preview`'s `:antecedents` | a cross-context firing lists the `genlCx` edges it was placed over, and a descended merge names each `genl` edge once rather than once per side |
| reads `defeat-class` on a cross-context conclusion | it caps on those edges, so a known-true fact read across a `:default` context edge answers `:default` |
| re-asserts known-true content over a `:monotonic` premise | the stronger class survives the re-assert; narrowing one is `retract!` and re-assert |
| asserts a rule concluding `(rewriteOf …)`, `(sameAs …)`, `(equals …)` or `(disjointMetatype …)` | it merges or separates while the KB runs, where only a restart saw it |
| lists a store directory through `catalog/classify` | classification reads `records/format.edn`; three disk backends classify as `:store` that did not, and a `records/`+`index/` pair alone no longer does |
| catches around `unload!` | a store that did not close reports `:unreleased`, where it reported silent success |
| runs `kb-quality` | a fifth reading, `:declarations`, names argument constraints that constrain nothing, and `:stranded-count` drops |
| matches an arity refusal on its `:message` | an inherited length reads "takes N arguments through P", not "is declared with N" |

### Writes over a KB whose derived state was never built

- **Breaking: such a KB refuses writes rather than accepting them unchecked.** *Class:*
  Breaking; writes that landed silently now throw. *Migration:* call `recover` (or
  `reindex`) before writing, which is what the content needed anyway; or bind
  `vaelii.core/*write-unrecovered?*` around the write, which now logs once per KB naming
  what is unchecked. *Breaks:* `:unrecovered-kb`, `:unrecovered-premise`,
  `*write-unrecovered?*`, `:recover?` [docs/storage.md](docs/storage.md),
  [docs/web.md](docs/web.md)

- **Breaking: a derived record's teardown is refused where belief was never built.**
  *Class:* Breaking; a retraction that deleted a record now throws. *Migration:* call
  `recover` (or `reindex`) before retracting, which is what the sweep needed anyway.
  *Breaks:* `:unrecovered-kb` [docs/storage.md](docs/storage.md)

- **`check` and `check-edit` answer for the entry point they mirror.** *Class:* Additive; a new
  problem `:type` on two readers that report problems. *Migration:* none. A caller matching
  on the message rather than the `:type` sees "index was" where the index hazard stands
  alone. *Breaks:* `:unrecovered-kb`, `check`, `check-edit`
  [docs/storage.md](docs/storage.md)

- **Refusal: a declared hazard survives being read while the store is still empty.**
  *Class:* Refusal; writes a prematurely-released hazard let through are now refused by
  name. *Migration:* code clearing a store through `p/clear-records!` rather than `clear!`
  should call `kb/note-hazards!` with both keys false, as the suite's fixtures now do.
  *Breaks:* `write-hazards`, `note-hazards!` [docs/storage.md](docs/storage.md)

- **Refusal: `recover` stops believing a record the store does not hold.** *Class:* Refusal;
  the handle read absent and its belief read true, so the state it produced was not one
  anybody asked for. *Migration:* nothing to change; a store carrying such a justification
  now says so. *Breaks:* `recover`, `justifications-unrooted`
  [docs/storage.md](docs/storage.md)

### Loading a dump

- **`:belief? :stored` — store what rests on what, and settle it later.** *Class:* Refusal
  for the `:belief?` **value** check; Additive for the mode itself. *Migration:* none —
  `true` is still the default. An unrecognised `:belief?` value is now refused by name
  (`:unknown-option`), since anything truthy would otherwise mean `true` and run the recover
  the caller asked to defer. *Breaks:* `:belief?`, `:unknown-option`
  [docs/catalog.md](docs/catalog.md), [docs/web.md](docs/web.md)

- **One frame a dump holds and this build will not construct stops taking the load with
  it.** *Class:* Additive for `:refused` and `:frames`. *Migration:* a load that threw
  `:naf-not-closed` — or any other construction refusal — now finishes; assert `(zero?
  (:skipped (:refused summary)))` to keep the old strictness.
  [docs/naming.md](docs/naming.md)

- **A justification the import writes no longer rests on a record the import deleted.**
  *Class:* Additive for both keys; a load that wrote a dangling justification now drops it
  and says so. *Migration:* none. A store already carrying them is repairable in place —
  delete every justification naming a handle `sentex-ids` does not yield.
  [docs/catalog.md](docs/catalog.md)

- **Refusal: an import frame that fills a justification's `:out` slot** *Migration:* nothing
  — no dump the engine produced carries one. *Breaks:* `:naf-justification`, `import!`,
  `import-dump` [docs/naf.md](docs/naf.md)

- **A dump that fills that slot is refused before the import writes anything.** *Class:*
  neither label; the refusal is the same refusal, and what changed is what the KB holds
  afterwards. [docs/catalog.md](docs/catalog.md), [docs/naf.md](docs/naf.md)

- **A restart stops answering through an edge nothing supports.** *Class:* neither label; a
  restart's answers move onto the running KB's. [docs/storage.md](docs/storage.md),
  [docs/taxonomy.md](docs/taxonomy.md)

### The predicate hierarchy descends

- **Breaking: `arity`, `asymmetric` and `functional` descend it.** *Migration:* a
  specialization that genuinely reads a different number of arguments is `variableArity` on
  either end of the edge; a sub-predicate declaring a conflicting arity is refused, so give
  the two one arity or drop the `genl` edge. *Breaks:* `variableArity`, `asymmetric`,
  `functional`, `:arity`, *Breaks:* `binaryPredicate`, `functional-clashes`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/inherit.md](docs/inherit.md),
  [docs/equality.md](docs/equality.md)

- **Breaking: an argument constraint on a predicate binds its sub-predicates' tuples.**
  *Migration:* a KB using predicate-level `genl` for retrieval fan-out alone, relying on the
  specialized predicate being unconstrained, is refused where 0.7.0 accepted it; widen the
  declaration, move it down, or drop the edge. *Breaks:* `argIsa`, `argGenl`, `interArgIsa`,
  `:arg-type` [docs/taxonomy.md](docs/taxonomy.md)

- **`argIsa` read as an *inference* descends with it, and so does the entailment.** *Class:*
  Additive; the entailment is opt-in and off by default.
  [docs/argtypes.md](docs/argtypes.md)

- **Three predicate-metadata kinds join `has-prop?` / `props`:** *Class:* Additive.
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a `functional` or `asymmetric` mark reaches back down a `genl` edge, on both
  retroactive paths.** *Class:* Breaking; a clashing pair that stood believed is now
  arbitrated. *Migration:* a caller reading `contradictions` or `violations` sees pairs the
  entry point has always refused when the mark arrived first — the two arrival orders agree now.
  *Breaks:* `contradictions`, `violations`, `:constraint-exposure`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: the cross-context exposure pass reads its marks down the hierarchy, as every
  check it gates already did.** *Class:* Breaking; a KB holding such a pair files a
  `:constraint-exposure` entry where it filed nothing. *Migration:* nothing to write — the
  entry names both handles, so the pair is what to look at. *Breaks:* `violations`,
  `:constraint-exposure` [docs/contexts.md](docs/contexts.md),
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: the retroactive arity report descends the hierarchy, as the entry point it mirrors
  already does.** *Class:* Breaking; nothing new is refused, and a caller reading
  `violations` sees a finding it did not. *Migration:* nothing to write — read `:via` to
  tell an inherited length from a declared one. *Breaks:* `violations`, `:arity`, `:via`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: that report answers a `genlCx` edge, its fourth ingredient.** *Class:*
  Breaking; `:arity` entries appear in two arrival orders that filed none. *Migration:* none
  for a KB whose contexts declare their own arities; one declaring in a super-context learns
  about facts that were already wrong. *Breaks:* `violations`, `:arity`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/contexts.md](docs/contexts.md)

- **Breaking: the arity entry point words an inherited length as inherited, as its retroactive half
  already did.** *Class:* **Breaking** on §3.8's counterweight: only the `:message` string
  moves, which is the class-1 test. *Migration:* read `:expected`, `:actual` and `:via` off
  the ex-data rather than matching the message. *Breaks:* `is declared with`,
  `:opposing-handle`, `:arity` [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a `variableArity` predicate may be given argument types past its declared
  length.** *Class:* Breaking; input that was refused is now admitted, and `kb-quality`'s
  `:stranded-count` drops. *Migration:* nothing in the shipped ontology moves — none of its
  three `variableArity` predicates declares past its length. *Breaks:* `variableArity`,
  `argIsa`, `:stranded-count`, `kb-quality` [docs/taxonomy.md](docs/taxonomy.md),
  [docs/quality.md](docs/quality.md)

- **`kb-quality` gains a fifth reading: argument constraints that constrain nothing.**
  *Class:* Breaking for the `:arg-position` refusal message, which now splits on `:via` as
  the entry point and the report do; Additive for the reading itself. *Migration:* read `:via` and
  `:arity` off the ex-data rather than parsing `:message`. *Breaks:* `kb-quality`,
  `quality-report`, `:arg-position`, `is declared with` [docs/quality.md](docs/quality.md),
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: neither retroactive pass can file its way through the ledger, and
  `:arity-report-truncated` says when a cap stopped one.** *Class:* Breaking for the cap,
  Additive for the kind and the keys. *Migration:* size a problem from `:predicates` and
  `:facts` on the notice rather than by counting `:arity` entries; past 8 the count is now
  visibly not the total. *Breaks:* `violations`, `:arity-report-truncated`,
  `:arity-truncated`, *Breaks:* `:constraint-exposure-truncated`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/nmtms.md](docs/nmtms.md)

- **The retroactive arity sweep says when its budget stopped it, including in the case that
  carries no finding.** *Class:* Additive; a new `:violation` kind, so a defaultless `case`
  over them has one more to admit. [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a descended merge names each `genl` edge once, not once per side.** *Class:*
  **Breaking** on §3.8's counterweight: the list is shorter, deterministically so.
  *Migration:* nothing, unless you counted. *Breaks:* `why-not`, `preview`, `:because`,
  `:antecedents` [docs/nmtms.md](docs/nmtms.md)

### Contexts and placement

- **Breaking: a firing rests on the `genlCx` edges its placement was read over, and now
  names them.** *Migration:* assert the `genlCx` wiring `{:strength :monotonic}` wherever a
  cross-context conclusion must stay indefeasible, and expect context edges among a
  justification's antecedents. Two things move for a caller who retracts nothing: antecedent
  lists are longer, and `defeat-class` caps on the edges like any other ground. *Breaks:*
  `genlCx`, `supporting-justifications`, `defeat-class`, `:monotonic`
  [docs/contexts.md](docs/contexts.md), [docs/nmtms.md](docs/nmtms.md)

- **Breaking: a retraction stops filing `:no-placement` entries about the rules it just took
  apart.** *Class:* Breaking; a public reader returns fewer entries. *Migration:* none for a
  caller reading `violations` for problems. A caller counting entries across a retraction
  sees the count it would have had if the rules had never been asserted. *Breaks:*
  `violations`, `:no-placement` [docs/contexts.md](docs/contexts.md)

### Rules that conclude structure

- **A rule generator may stamp a generator, at any depth, and a variable an enclosing level
  fills may head a literal.** *Class:* **Additive** — a shape that was refused is now
  accepted. [docs/generators.md](docs/generators.md)

- **Breaking: a rule concluding `(rewriteOf A B)` / `(sameAs A B)` / `(equals A B)`
  merges.** *Migration:* a KB with such a rule now merges where it did not, which moves
  matches, `different` answers and belief; if the rule meant something weaker than identity,
  restate it under a predicate of your own. *Breaks:* `rewriteOf`, `sameAs`, `equals`
  [docs/equality.md](docs/equality.md)

- **Breaking: a rule concluding `(disjointMetatype M)` separates M's members while the KB
  runs.** *Migration:* a fact contradicting such a separation is refused `:disjoint` at
  assert time now, where it was stored unchallenged. *Breaks:* `disjointMetatype`,
  `:disjoint`, `disjoint?` [docs/taxonomy.md](docs/taxonomy.md)

### Belief, and reports that read as content

- **Breaking: a re-asserted fact keeps the stronger defeat class.** *Migration:* narrowing a
  class is `retract!` and re-assert, as it is for a rule's `:direction`, `:defeasible` and
  `:strength`. *Breaks:* `:strength`, `defeat-class` [docs/nmtms.md](docs/nmtms.md),
  [docs/canonicalization.md](docs/canonicalization.md)

- **A justification reports as content, in both directions.** *Class:* neither label; the
  order it displaced was a function of how the KB was loaded, so nothing stable was there to
  depend on. [docs/nmtms.md](docs/nmtms.md), [docs/api.md](docs/api.md)

- **The wholesale wipe stops carrying the qualitative join baselines.** *Class:* none;
  resident engine state with no caller-visible surface. [docs/qcn.md](docs/qcn.md)

- **`why` builds its proof tree over an explicit work stack, not the JVM stack.** *Class:*
  neither label; the tree returned is identical, and the one input whose behaviour moves — a
  derivation deeper than the JVM's frame budget — returns its tree where recursion threw
  `StackOverflowError`. [docs/api.md](docs/api.md)

### Entry points, catalogs and reports

- **Breaking: a top-level vector sentence is refused at both families of entry point** *Class:*
  Breaking; a caller who wrote the vector spelling on both sides had code that did what its
  author believed, and it stops on upgrade. *Migration:* write one sentence as a list —
  `(likes Tom Ann)` — and ask a conjunction with `query` or `prove`, which are the entry points
  that join. *Breaks:* `:shape`, `sentexes-matching`, `handle-of`, `ask-within`,
  `prove-within`, *Breaks:* `query-plan`, `provable?`, `query?`, `abduce`, `assert-inert`,
  `check-edit` [docs/api.md](docs/api.md),
  [docs/troubleshooting.md](docs/troubleshooting.md)

- **Refusal: a `nil` conjunct is a conjunct, not the absence of one.** *Migration:* nothing
  — the goal never did what whoever wrote it believed. *Breaks:* `:shape`, `:conjunct`
  [docs/api.md](docs/api.md)

- **Ten option entry points word their refusal the same way, and `open-kb` gains the shape check.**
  *Class:* Refusal for `open-kb`'s non-map, which previously threw an unnamed error.
  *Migration:* none for a caller discriminating on `:type`. A caller matching refusal text
  should match `:type :unknown-option` and read `:options` / `:unknown` instead. *Breaks:*
  `:unknown-option`, `open-kb` [docs/namespaces.md](docs/namespaces.md)

- **Breaking: a store on disk is recognised by the format marker it writes, not by a
  directory pair.** *Class:* Breaking; a directory's classification changes in both
  directions. *Migration:* none for a store this build wrote. A catalog entry pinned by a
  caller's own path should be re-listed. *Breaks:* `classify`, `:store`
  [docs/catalog.md](docs/catalog.md)

- **Refusal: `unload!` reports the release it actually performed, and gives way to the walk
  it would have emptied.** *Migration:* nothing for an unload nothing else is holding, which
  is every unload that succeeds; a caller catching around `unload!` sees `:unreleased` where
  a store that did not close reported silent success. *Breaks:* `unload!`, `:unreleased`,
  `:still-exporting`, `reset-registry!` [docs/catalog.md](docs/catalog.md)

- **Every kind `violations` can file has a row in the table consumers branch on.** *Class:*
  neither label; no kind is new or moved. [docs/api.md](docs/api.md)

- **Refusal: a two-axis calculus checks its projection is a bijection.** *Migration:*
  nothing — both shipped tables are bijections; a caller building their own calculus gains
  the refusal. *Breaks:* `:bad-algebra` [docs/qcn.md](docs/qcn.md)

### The shipped ontology

- **`asymmetric` stops claiming it hands you irreflexivity.** *Class:* neither label;
  ontology content, which §3.8 exempts from the Breaking label however far it moves an
  answer — and here it moves none, the engine having always behaved this way. What changed
  is a description that told a reader to expect a refusal nothing performs.
  [docs/taxonomy.md](docs/taxonomy.md)

### Performance

Three passes over the predicate hierarchy were quadratic in a *batch* of `genl` edges,
which is what a load writes. All three are measured and explained in
[docs/taxonomy.md](docs/taxonomy.md), "What a batch of edges costs the passes that read it";
the answers computed are identical, and all three are free where nothing is declared.

- **A settle reads its `functional` and `asymmetric` marks once, from the marked end.**
  *Class:* neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **A batch of `genl` edges costs the union of its subtrees, not the sum of them.** *Class:*
  neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **The two retroactive `genl`-edge arms decide there is nothing to draw before reading the
  subtree, not once per fact inside it.** *Class:* neither label.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A check for a shape the sentence does not hold stops building a seq to find out.**
  *Class:* neither label; same answers, same depth-first pre-order.
  [docs/canonicalization.md](docs/canonicalization.md)

- **A refused sentence stops paying to resolve a stack trace nobody prints.** *Class:*
  neither label; same class, same message, same `:type :naming` ex-data.
  [docs/naming.md](docs/naming.md)

- **A justification listing builds its content key once per entry, not once per
  comparison.** *Class:* neither label; the same `compare` over the same keys, both sorts
  stable. [docs/nmtms.md](docs/nmtms.md)

### Tooling

- **The whole matrix at once.** *Class:* neither label.
  [docs/operations.md](docs/operations.md)

- **Every verdict names the tree it is a verdict about.** *Class:* neither label.
  [docs/operations.md](docs/operations.md)
## 0.7.0 — 2026-08-12 — "contexts get one spelling"

- **Breaking: a context name is `Cx`-prefixed, not `Context`-suffixed.** `CoreContext`
  is `CxCore`, `UniverseContext` is `CxUniverse`, and the `assert` public entry point refuses a
  `Context`-suffixed name by the same naming check that already refused a malformed
  predicate or type. *Migration:* respell every context name — in a stored KB, an
  `assert` call, and a saved dump — to the `Cx` form. `docs/naming.md`.

- **Breaking: the context-transitivity predicate is `genlCx`.** `(genlContext sub super)`
  is `(genlCx sub super)`, so the relation between two contexts is spelled the way the
  contexts it relates are. The `genl` closure over types keeps its name. *Migration:*
  respell the predicate wherever an edge is asserted, matched or retracted; a stored
  `genlContext` edge is a fact under a predicate nothing reads, so re-assert it rather
  than expecting the taxonomy to find it. `docs/taxonomy.md`.
## 0.6.0 — 2026-08-12 — "stored rules become first-class"

A rule can conclude a rule, a NAF guard written as a
conjunction guards instead of firing unconditionally, and every entry point that reaches a rule
reads **belief** rather than storage. Beside them, the arrival-order dependences left in
the belief loop are closed — a revived datum, an un-merged spelling, and every report,
digest and election that keyed on retrieval order — and two reads that grew with what the
KB *holds* rather than with what the write *touched* now read forward off the region.

**Three entries are Breaking**, which is what makes this a minor rather than a point
release: the daemon answers an export refusal 400 where it answered 500, the model's tool
surface drops two ops, and the CLI's refusals move to stderr. Seven Refusal entries batch
here rather than each forcing its own release, which is what §3.8 of `CONTRIBUTING.md`
designates a minor for. Every Breaking and every Refusal entry carries its *Migration*
line.

**Triage, for a 0.5.1 caller.** This is the index to what touches something you have
written.

| If your code… | Then |
|---|---|
| treats a 5xx from the daemon's `:export` op as a backend fault | the five destination refusals answer **400** now; retry logic keyed on 5xx stops retrying a caller mistake |
| drives `:preview` or `:clear-caches` through the LLM tool surface | they are no longer exposed to a model — call the op on the daemon or the API directly |
| writes `(ist Ctx S)` in an antecedent or an `exceptWhen` | refused `:not-well-formed`; say it with `decontextualizedPredicate` or a `genlCx` edge |
| passes `(ist Ctx S)` to a read | it answers now instead of returning empty, with the named context winning over the argument |
| writes `(unknown (and A B))` as a guard | it guards now; it fired unconditionally before. Under a quantifier the same shape is refused |
| branches on `violations`' `:violation` with a defaultless `case` | `:functional`, `:asymmetric` and `:constraint-exposure-truncated` are new kinds |
| runs `check` over `(not (implies …))` | refused `:not-well-formed` at both entry points, where `check` passed it and `assert` threw |
| runs a `:refuse` KB and reads an empty `violations` as a clean bill | cross-context `functional` and `asymmetric` pairs are reported there now |
| passes `--strength` to the CLI's `assert-rule`, or reads CLI refusals off stdout | the flag is honoured now, and refusals print on stderr |
| forks a KB with an opts map naming neither `:space` nor `:dir` | the fork lands on its own space instead of the shared process default |
| asks a `symmetric` predicate about a claim that is inherited rather than stored | the mirror composes with the other provers now, so an `ask` can answer more |
| writes a kind-level `(hasCapability <kind> …)` against the shipped ontology | kind-level claims are `capabilityType`; `hasCapability` is the instance-level reading alone |

- **A capability claim about a *kind* is `capabilityType`, and about a *member* is
  `hasCapability`.** *Class:* none; `resources/kb/` is data rather than surface (§3.8).
  [docs/inherit.md](docs/inherit.md), [docs/taxonomy.md](docs/taxonomy.md)

- **A guard keyed on the operator instead of on what it reads.** *Class:* neither label for
  the guard — belief moves for a rule of this shape, and the guard answered from arrival
  order rather than content; **Additive** for `check`.
  [docs/exceptions.md](docs/exceptions.md), [docs/naf.md](docs/naf.md)

- **A rule can conclude a rule.** *Class:* **Additive**; shapes that were refused are
  accepted, and nothing could previously make a stored rule un-believed.
  [docs/generators.md](docs/generators.md), [docs/defenses.md](docs/defenses.md)

- **A NAF guard written as a conjunction now guards.** *Class:* neither label for the guard,
  no author's code having done what its author believed; **Refusal** for the two shapes.
  *Migration:* bind the witness with a generator antecedent and leave one literal under the
  `unknown`. [docs/naf.md](docs/naf.md), [docs/aggregate.md](docs/aggregate.md),
  [docs/defenses.md](docs/defenses.md)

- **The strictest policy stops being the leakiest.** *Class:* **Additive** — a new entry
  kind in an accumulating ledger. A `:refuse` KB that saw an empty `violations` may now see
  entries, which is the point. [docs/nmtms.md](docs/nmtms.md)

- **A hidden set kept where the sentexes are, not rebuilt per placement.** *Class:* neither
  label; same arity, same contract, same answer set. [docs/contexts.md](docs/contexts.md)

- **The planner's subtype fan is made cheap rather than remembered.** *Class:* neither
  label; the number returned is identical by construction.
  [docs/inference.md](docs/inference.md)

- **`ist` places, and four layers had it half-reading.** *Class:* **Refusal** for the
  antecedent and the two read shapes, **Additive** for the reading. *Migration:* say a
  rule's premise with `(decontextualizedPredicate P)` or a `genlCx` edge into the rule's own
  ancestor set. [docs/contexts.md](docs/contexts.md), [docs/api.md](docs/api.md)

- **A datum that comes back believed goes back on the agenda.** *Class:* neither label;
  belief moves only toward conclusions the same knowledge already reached in another order.
  Guards: both un-merge routes and twenty orderings, six of which disagreed.
  [docs/nmtms.md](docs/nmtms.md), [docs/equality.md](docs/equality.md)

- **An answer picked from a fan is keyed on content, never on arrival.** *Class:* neither
  label; the order displaced was not reproducible for the same knowledge.

- **A collected NAT leaves none of its bookkeeping behind.** *Class:* neither label.

- **A stored sentex is not a believed one, and five reads had it the wrong way round.**
  *Class:* neither label; each read answers the question its docstring already claimed.
  [docs/nat.md](docs/nat.md)

- **Retrieval answers what the reference answers.** *Class:* neither label; the answer
  withdrawn was one the two paths disagreed about. [docs/inference.md](docs/inference.md),
  [docs/canonicalization.md](docs/canonicalization.md)

- **A symmetric or inverse reading composes with what is derived.** *Class:* neither label —
  answers are added, none withdrawn. [docs/inherit.md](docs/inherit.md),
  [docs/taxonomy.md](docs/taxonomy.md)

- **A negated rule is refused at the entry point.** *Class:* **Refusal** for both — one shape
  reached a stack trace rather than storage, the other a rule nothing was firing.
  *Migration:* assert a negated rule as the positive rule with the negation in the
  consequent; a rule meant as documentation is `set/inertRule`, and one already stored inert
  is `retract!`ed and re-asserted. [docs/solving.md](docs/solving.md),
  [docs/inference.md](docs/inference.md)

- **Storage keeps no dead frames, and a torn dump refuses.** *Class:* **Refusal** for the
  two new kinds — one input is a truncated file, the other loses a record it reports as
  loaded. *Migration:* re-export.

- **The uberjar loads the ontology it ships.** *Class:* neither label; a caller running from
  source saw every layer already.

- **ASP routes to a solver that can actually run.** *Class:* **Refusal** for the two new
  `:type`s. *Migration:* install `clasp` if you relied on the large-program path, which was
  throwing.

- **The daemon answers a caller's mistake with 400, and the model's tool surface loses two
  ops.** *Class:* **Breaking** — a status code, and a removal from the exposed tool set.
  *Migration:* a client that retries on 5xx will report these instead of retrying, which is
  the intent; call either op on the daemon or through `vaelii.core` directly.

- **The browser writes what it shows, and shows what the ledger holds.** *Class:* neither
  label. [docs/overlay.md](docs/overlay.md), [docs/web.md](docs/web.md)

- **CLI flags mean what they say.** *Class:* **Breaking** for the stream move and the
  per-command roster, **Refusal** for the flag-as-value. *Migration:* redirect with `2>&1`
  if you read refusals off stdout; drop the flags your commands were ignoring; re-assert any
  rule whose `--strength` was dropped. [docs/canonicalization.md](docs/canonicalization.md)

- **Three more costs read the change rather than the KB.** *Class:* neither label; each
  answers what it answered.
## 0.5.1 — 2026-08-11 — "faster writes, more to watch"

A run of costs that grew with what the
KB *holds* rather than with what the write *touched* — the taxonomy reconcile, the five
flat caches, the reified-NAT orphan sweep, a retraction's teardown, the standing-clash
ordering, a context-cycle repair, a repeated closure ask and a query plan's child count —
each now reads forward off the region a settle moved, and each has a `lein perf` check
standing where the claim is. Four places where **arrival order decided an answer** are
closed. Beside them the process gained instruments for the rest: the change feed crosses
the process boundary as a subscription with a cursor, long work is a job registry with a
screen that watches it, `kb-quality` reads the knowledge where every other instrument
reads the engine, and the conjunctive planner costs a join rather than a column of
literals.

**No entry is Breaking**, which is why this is a patch. Three carry a *Migration* line
anyway, because a caller can observe them and should be told what to expect.

**Triage, for a 0.5.0 caller.** This is the index to what touches something you have written.

| If your code… | Then |
|---|---|
| reads the first N of `preview` / `edit-with-consequences!`'s `:believed-added` or `:believed-removed` | you get a different N — the halves are content-ordered now, and were handle-ordered |
| calls `clear-caches` and expects the literal cache's hit rate to zero | pass `{:counters? true}`; the reset is off by default |
| walks a `declared-transitive` predicate that also declares an `inverse` | the walk sees the inverse-recorded hops too, so an `ask` can answer more |
| branches on `violations`' `:violation` with a defaultless `case` | `:arbitration-truncated` is a new kind |
| builds on the shipped Space or Time vocabulary | an argument position that held `thing` now names a type, so an assert 0.5.0 accepted can meet an `:arg-type` refusal — widen the convicting declaration it names, or state the argument at a type the position admits |

- **A settle pays for the region it moved, not for what the KB holds.** *Class:* neither
  label; every reading answers what it answered. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/equality.md](docs/equality.md)

- **The arbitrating half of a bounded pass says when its budget stopped it.** *Class:*
  Additive — a new `:violation` kind. [docs/taxonomy.md](docs/taxonomy.md)

- **A `disjointMetatype`'s membership is vocabulary, not a roster.**

- **Four places where arrival order decided an answer.** *Migration:* a caller reading the
  first N of either preview half gets a different, better-defined N. *Class:* neither label;
  a sequence that moved with load order was never a contract.
  [docs/preview.md](docs/preview.md), [docs/taxonomy.md](docs/taxonomy.md),
  [docs/llm.md](docs/llm.md)

- **A card's cut is a count, including the cut that was not counted.**

- **The model backends refuse by name, never by value, and a turn that ran out of tokens is
  not a deletion.** *Class:* Additive for the three new `:type`s.

- **The taxonomy's closures terminate, scope their repairs, and read a repeat.**
  *Migration:* such an `ask` returns at least what it did and never less. *Class:* Additive
  for the cache; neither label for the rest. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/storage.md](docs/storage.md)

- **A unary fact about a reified NAT was deleted with the constant, silently.** *Class:*
  neither label; a caller whose unary claim was being deleted underneath them was not
  getting what they believed.

- **The change feed crosses the process boundary, as a subscription with a cursor.**
  *Class:* neither label — the feed is new in this release. [docs/feed.md](docs/feed.md)

- **A conjunction is costed as a join rather than as a column of literals.** *Class:*
  **Additive**; a new `IndexStore` read, owed by both implementations.
  [docs/inference.md](docs/inference.md), [docs/indexing.md](docs/indexing.md)

- **Long work is one mechanism: a job registry, and the screen that watches it.** *Class:*
  not Breaking; `:busy` was thrown at one impl site and read by one impl namespace.
  [docs/web.md](docs/web.md)

- **What this process is holding, on a page — caches, heap, and the profiler.** *Class:*
  neither label; both are new in this release. [docs/web.md](docs/web.md)

- **The shipped ontology declares its positions, and decontextualizes predicate metadata and
  nothing else.** *Class:* no label — ontology content (§3.8); what it owes is the roster
  that pins the shipped set. *Migration:* a KB built on the shipped Space or Time vocabulary
  can be refused where 0.5.0 accepted it — the refusal names its convicting declaration.
  [docs/argtypes.md](docs/argtypes.md), [docs/contexts.md](docs/contexts.md)

- **A bulk load is decomposed, and the index write is 57% of it.**
  [docs/storage.md](docs/storage.md), [docs/profile.md](docs/profile.md)

- **Eleven checks join the perf gate, and 27 in the vector all judge.**
## 0.5.0 — 2026-08-07 — "operating the engine as a service"

Operating the engine, in the two senses a running process needs: what it will let a caller
do, and what it will tell an operator it is doing. The daemon authenticates and refuses to
bind an address without a credential, ships as a container image, and says which posture it
started in; every switch the build reads has a row in a table a test keeps honest; the log
level is a dial a running process turns; and the failures that look like answers each
gained something that says so. Nine entries are **Breaking**; the three **Refusal** entries
(§3.8) cover input where what 0.4.0 did with it was run a configuration nobody asked for
and report a clean pass.

**Triage, for a 0.4.0 caller.** Every Breaking and Refusal entry carries its own one-line
*Migration*; this is the index to the ones that touch something you have written or
deployed.

| If your code… | Then |
|---|---|
| names `:record-space` / `:index-space` | one `:space` — keep the record number, drop the index one |
| runs a daemon on a non-loopback `--listen` | export `VAELII_API_TOKEN` there and in every client, or it exits 2 |
| reads a daemon 401, or branches on the wire `:type` | `:unauthorized` is a new one; `GET /health` is the only route without the token |
| relies on `VAELII_RETE=0` running the sweep | it means off now; unset, or `=1` for on |
| sets `VAELII_NOHIER` | it is `VAELII_HIER`, the other way up — `VAELII_NOHIER=1` becomes `VAELII_HIER=0` |
| sets `VAELII_QUERY_ENGINE` / `VAELII_QUERY_STRATEGY` | a name outside the roster is refused rather than silently running the default |
| sets `VAELII_WEB_PORT` for `lein browser` while `-main` stayed on 3000 | it moves both; pass `--port 3000` to pin `-main` |
| lists KBs out of a search-path directory holding more than 200 | name the ones that matter in the catalog file |
| depends on vaelii and has no SLF4J provider of its own | add one — `org.slf4j/slf4j-nop` no longer arrives transitively |
| branches on what `term-role` answers | `:sense` and `:lexeme` are two new answers — add arms, or a `default` |
| writes a `lex`-namespaced predicate | it names a lexeme now, and a lexeme names no relation |
| calls `core/context-size`, or sends the daemon `:context-size` | both are `count-in-context` — same arguments, same answer |
| compares two compound terms with `different` | a merged symbol inside one now makes them equal, where it did not |
| sets `VAELII_ASP_SOLVER` to a name outside `clingo`/`clasp` | it is refused at `open-kb` rather than silently running auto |

- **Breaking: a name can carry two more roles — a sense, and a lexeme.** `term-role`
  answers `:sense` for a disambiguated type and `:lexeme` for a symbol in the `lex`
  namespace, so its documented domain gains two values a total `case` has no arm for; a
  lowercase dashed name is a legal unary type where it was refused, and a lexeme applied to
  arguments is refused (`:lexeme-functor`). *Migration:* add `:sense` and `:lexeme` arms or
  a `default`; a `lex`-namespaced predicate names a lexeme now and cannot be applied.
  `docs/naming.md`.
- **Breaking: `context-size` is `count-in-context`.** The three O(1) cardinality readers are
  one family and two of them said so. *Migration:* `(v/context-size kb ctx)` becomes
  `(v/count-in-context kb ctx)` and `{:op :context-size}` becomes `{:op :count-in-context}`
  — same arguments, same answer, old spellings gone rather than deprecated.
  `docs/api.md`, `docs/indexing.md`.
- **Breaking: `different` descends into compound arguments.** It normalized each argument
  with one lookup in the symbol-keyed equality closure, so a compound was never found in it
  and `(different (QuantityFn 5 Kilogram) (QuantityFn 5 Kg))` answered *different* with
  `(sameAs Kilogram Kg)` believed. *Migration:* a goal comparing two compounds can newly
  answer false where a merge reaches inside one; comparing symbols is unchanged.
  `docs/equality.md`.
- **Breaking: one space number names a KB's stores, `:space`.** A `:disk` KB's derived
  directory is `space-<n>`, and the suite owns a block of two db numbers rather than four.
  *Migration:* `{:record-space 2 :index-space 3}` becomes `{:space 2}`; either retired key
  is refused by name (`:unknown-option`) rather than ignored, and `:dir` names a durable
  directory the derived spelling does not reach.
  *Breaks:* `:record-space`, `:index-space`
  `docs/storage.md`.
- **Breaking: the daemon authenticates, and refuses to bind an address without a token.**
  With `VAELII_API_TOKEN` set every request carries `Authorization: Bearer <token>` or is
  answered 401 `{:type :unauthorized}`, with `GET /health` the only route that answers
  without it. `--listen` naming a non-loopback address without a token is one line on
  stderr and exit 2, where 0.4.0 logged a warning and served the whole write block to
  anything that could reach the port. *Migration:* export `VAELII_API_TOKEN` for a daemon
  that names an address and give the same value to every client; nothing changes on the
  loopback default. `docs/operations.md`.
- **Every switch the build reads has a row, and a test keeps the roster honest.**
  `docs/operations.md` gains a configuration table — 56 environment variables and system
  properties, each with where it is read, its legal values, its default and the one thing it
  decides. `config_surface_test` pins the names in both directions and checks each
  `file:line` citation against the line it names, so the table cannot drift without a
  failing test.
- **Refusal: the four harness switches read a value instead of a presence.** They were
  membership tests, so `=0` ran the sweep it names, and the two query switches took a bare
  `(keyword …)`, so a misspelt engine ran the *default* and reported a clean pass for a
  configuration nothing exercised — the worst shape a test switch can have, since the result
  reads as evidence. *Migration:* none for a value in the vocabulary; a job relying on `=0`
  meaning *on* now gets the sweep off. `docs/operations.md`.
- **Refusal: the ASP backend switches are read against their domains, at the entry point.** A
  misspelt `VAELII_ASP_SOLVER` matched no arm and ran auto, so a run pinned to clasp could
  use clingo and report a clean pass; `VAELII_CLINGO_MAX_BYTES` threw from the first ASP
  solve rather than from the configuration that was wrong. Both go through `config/check!`,
  refused at `open-kb` by name. *Migration:* none for a legal value. `docs/operations.md`.
- **Breaking: `VAELII_NOHIER` is `VAELII_HIER`, and the sense is the other way up.** A
  switch carrying the negation in its own name makes `=0` mean *on*, and the entry above had
  just made the value required. `VAELII_HIER` defaults true. *Migration:*
  `VAELII_NOHIER=1` becomes `VAELII_HIER=0`; a `VAELII_NOHIER` left set is simply unread,
  since a variable cannot be refused by name. `docs/operations.md`.
- **The log level is a dial a running process turns.** `set-log-level` takes one of
  `:error :warn :info :debug :trace` and installs Trove's console backend at it; `log-level`
  reads back what is in force, and `VAELII_LOG_LEVEL` says it at startup. Unset, the engine
  installs **no** backend at all, so an application holding its own `*log-fn*` keeps it.
  Three `:debug` statements are what make turning it up worth doing. `docs/operations.md`.
- **Breaking: `VAELII_WEB_PORT` moves `-main`'s port, and not only `lein browser`'s.** Both
  read one `default-port`: the variable, else the `vaelii.web.port` property, else 3000, and
  an explicit `--port` still wins. *Migration:* a deployment that set the variable for `lein
  browser` while relying on `-main` ignoring it now moves both; pass `--port 3000` to pin it.
- **Breaking: a search-path directory is probed for its first 200 entries.** `sources` is
  recomputed per request, which is what lets a corpus appear with no restart and what made
  the scan unbounded. The cut is named on the page and in the log, since a list that quietly
  ends early reads as "this machine has no other KBs". *Migration:* name the ones that
  matter in the catalog file to list them regardless of the count. `docs/catalog.md`.
- **The public entry point says what a legal-but-wrong sentence should have been.** `(isa Muffet
  Dog)` breaks no naming invariant, so it stored a two-place relation nothing reads while
  `isa?` answered false with nothing to search for. `nm/advice` reads intent where
  `problems` reads the invariants, logging `:warn` once per process with the rewrite that
  was meant; a `:no-placement` drop names `genlCx` beside the entry's own keys.
  `docs/naming.md`.
- **A second `open-kb` defaulting onto the shared in-RAM space now warns**, naming both
  fixes — give the KB its own number, or name `{:space 0}` to say the sharing is meant. A
  warning rather than a refusal, since sharing the space is how `recover` sees the same
  records and how a base is mounted. `docs/storage.md`.
- **Refusal: the CLI checks each command's argument count before it dispatches.** `dispatch`
  reached into `args` with `nth`, so a short line answered `error:
  IndexOutOfBoundsException` and a long one dropped the extra operand in silence. One table
  carries every command's arity, operands and gloss, so `check-arity!` and the usage text
  cannot go out of step. *Migration:* none at the right arity; `lein cli help` prints the
  count each command takes. `docs/operations.md`.
- **`docs/troubleshooting.md` is a new page, indexed by symptom rather than by subsystem.**
  The engine's hardest failures are the ones where nothing goes wrong — a query answers
  `()`, an `assert` returns a handle — so a reader has to already know the cause to find the
  page explaining it. Nine symptoms, each with what you would have observed, how to confirm
  it in one call, and the fix.
- **`lein lint` gains a versions check, and the kondo row notes a local/CI mismatch.** The
  0.4.0 bump left the `:with-foreign` pin naming `0.3.0`, so every
  `lein with-profile +with-foreign` command failed to resolve; `lint-versions` reads that
  pair and the `lein-cloverage` version stated twice.
- **Three doc samples now print what they actually produce, and `prove`'s docstring says it
  counts proofs, not answers.** A goal reachable both as a materialized fact and as the rule
  concluding it comes back twice with equal maps — wrap in `distinct`, or reach for `query`
  / `ask`, which project to the goal's variables.
- **The daemon ships as a container image**, with a two-stage `Dockerfile` and
  `docker-compose.yml`. The container binds an address, so the token is required — an image
  run without `VAELII_API_TOKEN` does not start rather than serving unauthenticated — and
  one container per volume, a second opener being refused `:disk-locked` rather than scaled,
  which is why the compose file carries no `replicas:`. `docs/operations.md`.
- **A reflection warning and an uncalled public var now stop the build.** Both signals were
  already emitted and neither was read: `reflect` compiles `src` and `bench` and fails on
  any reflection, auto-boxing or primitive-recur warning, and `unused` fails on a public
  definition with no usage against a baseline. Ten warnings had to go first, none in `src`.
- **Breaking: `org.slf4j/slf4j-nop` no longer reaches a consumer's classpath.** It sat in
  top-level `:dependencies`, where it could win SLF4J's provider race against a consuming
  application's own backend and silence it — the one thing a library must not do on a
  consumer's behalf. *Migration:* an application that had no provider of its own and relied
  on vaelii's now sees SLF4J's "no providers" line again — add one as its own dependency.
  `docs/operations.md`.
- **A public `--listen` bind with no `VAELII_ALLOWED_HOSTS` now warns.** Naming an address
  drops the `Host` allowlist to every `Host` answered — deliberate, since a reverse proxy
  sets its own — but nothing said so at startup. `host-posture` names the policy beside the
  token question, apart from the TLS line so a reader knows which check is missing.
- **`docs/troubleshooting.md` and `docs/storage.md` name `:type :unknown-backend`.**
  `open-kb` throws it from five call sites and none carried a line in either doc; the entry
  reads the other key each throw's ex-data carries to say which of the five it is.
## 0.4.0 — 2026-08-05 — "correctness fixes against the invariants"

Correctness fixes found by reading the engine against its own stated invariants, in the
places 0.2.0 and 0.3.0 did not reach: a backward-chaining loop guard that made a
conjunctive query answer nothing, entry points that disagreed about what they would accept, an
index trusted without being checked against the records it describes, slots and keys that
let arrival order decide belief, and derived caches a settle read one revival out of date.
Thirteen entries are **Breaking**, which is why this is 0.4.0. The **Refusal** entries
(§3.8) cover input where what 0.3.0 did with it was corrupt state or answer a different
question in silence.

**Triage, for a 0.3.0 caller.** Every Breaking and Refusal entry carries its own one-line
*Migration*; this is the index to the ones that touch source you have written.

| If your code… | Then |
|---|---|
| hands `assert` text it did not read as EDN | it is refused (`:shape`) — fix the producer |
| writes `exceptWhen` literals like `(lives_in ?x cold_place)` | spell them to the invariants; re-check any rule 0.3.0 left bare |
| spells an `edit!` batch `{:adds …}` | spell it `{:add […] :remove […]}` — the old key wrote nothing |
| names one of `:record-space` / `:index-space` | name both, or neither, in every opts map |
| passes `:direction` to `assert` on a non-rule | it is refused; a rule takes it and now acts on it |
| states one rule two ways (bare `implies` after a `set/*Rule`) | the slots join by content; `retract!` and re-assert to narrow one |
| calls `edit` or `edit-with-consequences` | they are `edit!` and `edit-with-consequences!` — the wire op stays `:edit` |
| matches `:bad-opt`, or a `:shape` from a non-map `opts` | match `:unknown-option` |
| reads a dump's `meta.edn` dialect | it is `:vaelii` |
| stores skolem witness names across runs | the names moved; rebuild from the assertions rather than carrying both spellings |
| parses a daemon 500 for a client mistake | it is a 400 with a `:type` |
| writes `(ist Ctx S)` with other than three elements | it is refused with `:shape` |

- **A conjunctive query could answer nothing while each of its conjuncts answered.**
  `[(anc Tom ?y) (anc Tom ?z)]` was empty where `(anc Tom ?y)` answered twice: the per-path
  loop guard grew for a whole frame, and a queued conjunct is a sibling of the expansion
  rather than a descendant. Silent in every direction — forward chaining and the node engine
  both answered, `provable?` said false, and `prove-within` reported `:status :complete`.
  `docs/inference.md`.
- **Breaking: `assert` refuses a sentence that is not an s-expression.** A string — what a
  failed EDN read hands back — was stored, indexed and believed as an object no query can
  match; `nil` likewise; a symbol, number or map threw an untyped
  `UnsupportedOperationException`. `check` refused all five, so the entry point built to predict
  `assert` disagreed with it. *Migration:* nothing a working caller sent is refused; fix the
  producer that handed `assert` unread text, and discriminate on `:shape`.
- **Breaking: an `exceptWhen` query's literals are held to the naming invariants.** A
  literal `docs/naming.md` says is refused was stored as an exception no query could match,
  so the rule read as guarded and fired as bare. Both entry points read each conjunct before the
  rule is stored. *Migration:* spell the exception's literals to the invariants, and
  re-check any rule 0.3.0 left bare.
- **Breaking: an `edit!` batch key nothing reads is refused.** `{:adds […]}` bound nil, so
  `edit!` wrote nothing and reported a success, while `check-edit` — whose job is to predict
  exactly that — reported no problem; over the daemon it was a `200 {:ok true}` for a write
  that did not happen. *Migration:* spell the batch `{:add […] :remove […]}`.
- **Breaking: naming one in-RAM space number and not the other is refused.** The two default
  independently, so `{:backend :memory :record-space 77}` paired a private record store with
  the process-default index every other in-memory KB writes: `assert` found the other KB's
  handle, read it as a duplicate, **stored nothing**, and returned a handle `in?` answered
  true for. *Migration:* name both or neither, in every opts map.
- **A durable index is checked against the records it claims to describe.** `layout.edn`
  gated the index's key shape and nothing gated its coverage, so a short index opened clean,
  answered short forever and re-cemented its own stamp — and re-asserting a fact it could
  not find minted a second handle for a sentence already stored. Three ways in: a torn
  `kv.log` tail, a directory grown under a derived-index mode, and a crash between the
  record write and the index batch. `docs/storage.md`.
- **Breaking: `assert` acts on `:direction` instead of accepting and dropping it.** Only
  `assert-rule` read the key, so a rule asserted `{:direction :backward}` stored `:both` and
  forward-chained, materializing the cross product a backward-only rule exists to avoid. A
  `:direction` on a non-rule, one contradicting the sentence's own wrapper, and a value
  outside the roster are refused. *Migration:* spell the direction; a `check` caller matching
  `:shape` for a non-map opts matches `:unknown-option` now.
- **Breaking: a re-asserted rule's direction and defeasibility resolve by content.** Neither
  slot is in the identity key, so a rule stated two ways resolved to one record and the
  second spelling was dropped — arrival order deciding a slot that decides belief. A bare
  `implies` after a `set/inertRule` stayed inert and never fired. The resolution reaches
  conclusions already derived, a justification baking the rule's contribution in at fire
  time. *Migration:* the join only widens a slot; to narrow one, `retract!` and re-assert.
  `docs/canonicalization.md`.
- **The derived caches are reconciled with what `clear-defeats!` revived.** A settle lifts
  last settle's defeats at its top while the cached closures were refreshed only in
  `settle-finish` — after `constraint-nogoods` had read them — so discovery asked its
  question against a vocabulary one settle out of date, and a `P`/`¬P` pair made visible by
  a revived `genlCx` edge went unarbitrated in a state `recover` disagrees with.
- **The disk KV index reads and publishes its RAM map under the lock.** `apply-ops!` read
  `@data` before acquiring and published after releasing while `compact!` runs on the
  durability daemon's executor — a thread the single-writer contract says nothing about — so
  a compaction in either window rewrote the log from a map missing the in-flight write.
  `kv-clear!` was sharper: a compaction between its truncate and its publish wrote the whole
  pre-clear map back over the log just emptied.
- **Breaking: a client's mistake answers 400 with a `:type`, not 500 with none.** An
  unreadable body, a wrong argument count and an unknown op all answered untyped, the first
  two as 500s — which count as backend faults at every reverse proxy and 5xx alarm. The
  engine's whole refusal vocabulary answers 400, unlogged. *Migration:* branch on `:type`
  rather than on the status code; every `{:ok false}` carries a non-nil keyword.
- **The browser's `/propose/*` EDN read catches `Throwable`**, as every other untrusted-EDN
  read in the namespace already does: a deeply nested form raises `StackOverflowError`,
  which an `Exception` catch let escape, and the browser has no exception middleware.
- **Refusal: `query` refuses a non-map `opts` and a negative or non-integer `:max-depth`.**
  Both read as "no depth", which is not an error condition but a *different question* — the
  no-rule-expansion answer, returned as if it were the bounded one asked for.
  `{:max-depth 0}` is admitted: it is that answer asked for by name. *Migration:* none for a
  working caller.
- **Breaking: `edit!` refuses what `check-edit` reports, before applying anything.** The two
  disagreed in both directions: a 4-element `:add` entry applied with the extra silently
  dropped where the dry run reported `:shape`, and a non-sequential entry threw a bare
  `ISeq` error from every entry point. An unknown `:remove` handle is refused before any entry is
  applied, so a checked-clean batch cannot half-apply. *Migration:* a remove-if-present batch
  filters its handles through `in?` first.
- **The recursive-literal hold-back keys on the peeled predicate.** A `not`- or `ist`-headed
  consequent read its own frame as the predicate, so every frame-headed antecedent was "the
  recursive literal" — two orderings of a negated-head rule minted two handles, and a
  genuinely recursive rule with a negated head lost the hold-back, turning right-recursion
  left-recursive.
- **Breaking: a skolem witness is a function of its rule's content, not its handle.**
  Retracting and re-asserting the same rule re-fired to a *different* witness, so a fact
  stated about the old one silently stopped co-referring — and two KBs holding the same
  knowledge in different orders stored different `termOfUnit` content, a handle in stored
  content that order independence rules out. *Migration:* rebuild the KB from its assertions
  (`export!` / `import!` replays firings) rather than carrying both spellings.
  `docs/skolem.md`.
- **Breaking: `edit` is `edit!`, and `edit-with-consequences` is
  `edit-with-consequences!`.** The batch's `:remove` half runs the same `retract-storage!`
  sweep `retract!` runs, while the name read as additive — the one gap in the `!` roster the
  convention exists to close. *Migration:* rename the calls; the wire op stays `:edit`.
- **Breaking: `:bad-opt` is retired, and one compression spelling survives.** Two keywords
  split one failure class on no rule a reader could predict — seven sites said `:bad-opt`
  where thirty-four said `:unknown-option`. *Migration:* discriminate on `:unknown-option`
  and `:unsupported-compression`.
- **Breaking: the dump's `meta.edn` names its dialect `:vaelii`.** Decorative on the read
  side, but it is a value in the frozen format and a documented key of `import-dump`'s
  return, so the name it carries is now-or-never. *Migration:* a reader matching the old
  value matches `:vaelii`; `import-dump` reads dumps written either way.
- **The node engine's claimed-key reads each guard's identity, not the guard count.** Two
  distinct rules, each carrying its own `exceptWhen`, can rewrite one goal to the same
  canonical residual through the `genl` fan; keyed on the count the two children were one
  key, so the second was dropped before it was enqueued and every answer only its exception
  admits was lost — silently, on the path `query` routes to whenever `:max-depth` is given.
  `docs/inference.md`.
- **A belief flip on a visibility `except` queues the same re-check as its arrival.** Only
  the store and removal chokepoints called `recheck-except`, so an except *defeated* by a
  settle's resolution revived nothing it hid: backward proving answered yes while the store
  held nothing, and which belief set the KB ended with depended on the order the except and
  its defeater arrived.
- **`recover` reads only positive, atomic declarations into the taxonomy.**
  `sentexes-with-functor` returns both polarities and the rebuild arms destructure the
  positive shape positionally, so a stored `(not (genl a b))` bound its inner sentence as a
  taxonomy node and nil as the other — poisoning every cache on any recover, the default
  `{:recover? :auto}` reopen included.
- **A `:neg` nogood is an at-least-one in every reader.** The ASP translation's soft branch
  emitted only the positive body atoms, so a `:neg`-only nogood — what `set/softConstraint`
  over negated choice literals produces — emitted its violation witness as an unconditional
  fact: no steering pressure, and `:violated` reported a satisfied at-least-one as broken.
  `docs/solving.md`.
- **`conflicts` and `contradictions` are content-ordered.** Each report's sides were already
  ordered by content; the *list* came off a hash set of handle-keyed nogoods, so which pair
  `(first (contradictions kb))` returned was an answer about which was typed first.
  `docs/nmtms.md`.
- **Refusal: the connective frames are shape-checked at every entry point.** An `implies` at arity
  2 threw a bare `IndexOutOfBoundsException` while arity 4 stored a silently truncated rule
  `check` read as clean; `(not A B)` stored as a positive fact whose record and index
  disagreed; a bare symbol passed as a rule literal was accepted, unmatchable; and a
  non-finite measure magnitude stored cleanly, then threw out of every later duration goal
  in the context. *Migration:* nothing a working caller sent is refused — every one of these
  stored an object no query could match.
- **Refusal: the last open rosters close.** `find-terms` and `abduce` take key rosters (a
  misspelt `:keep?` tore down the scratch context whose handles the caller meant to commit),
  the CLI refuses a flag outside its roster, `escalate` refuses a floor outside 0–7, and
  `import-dump` refuses an unknown `:framing` where it guessed a reader and failed as a
  `ZipException`. *Migration:* spell the key or flag as the refusal's roster lists it.
- **Refusal: the web and serve entry points refuse what their grammars do not know.**
  `vaelii.web --listen` with no address parsed to a nil host — Jetty's wildcard bind, with
  the Host allowlist reading nil as *any* — so a truncated command line put the browser's
  unauthenticated write routes on every interface with the rebinding guard off. `serve` read
  its positionals as a prefix, so a misplaced flag ran a disk daemon in memory.
  *Migration:* none beyond completing the command line.
- **Refusal: the opts and shape rosters reach the remaining entry points.** The roster guard held
  at `assert`, `why`, `query` and `open-kb`, and every other entry point took the misspelt key in
  silence — answering a different question than the one asked. *Migration:* spell the key as
  the refusal's roster lists it.
- **Refusal: the operator's mistakes answer in one line.** A CLI flag missing its value bound
  nil in silence — `lein cli assert '(dog Muffet)' Ctx --strength` stored known-true content
  at `:default` — and now exits 1 naming the flag; `--memory --dir` is refused as a
  contradiction. *Migration:* none beyond completing the command line.
- **The browser and CLI survive what they read.** The repl loop and the CLI command arm
  catch `Throwable`, so a deeply nested form answers `error:` and a next prompt; the
  browser's retract POST makes the `check-edit` round-trip `docs/operations.md` promises, so
  a stale handle answers the problem panel rather than a success-styled "Retracted 0
  sentexes".
- **Refusal: every durability switch is read against a domain, and a value outside it fails
  the open.** Each of the thirteen checkable switches was a membership test or an equality
  against one spelling, so none of them had a wrong value — every misspelling was the *other
  branch*, silently: `vaelii.disk.auto-compact=disabled` read as compaction on, and
  `vaelii.disk.fsync=always` as the three-second tick, the level the operator was trying to
  leave. *Migration:* none for a working setup, but two spellings now *act* where they were
  ignored. Spell what you mean. `docs/storage.md`.
- **Refusal: the mapped index image refuses the platform it corrupts on.** The image
  publishes by renaming a new file over the live one while it is mapped, which is what put
  `vaelii.index.snapshot` on macOS and Linux only — `docs/storage.md` said so and nothing
  enforced it, so on Windows the publish failed part-way through a four-file commit.
  *Migration:* none — the property never worked where it is now refused.
- **Breaking: `assert-rule` refuses a rule literal whose predicate is a variable.** Such a
  rule was indexed under `?var0`, which no arriving fact and no goal can spell, so it
  answered no backward goal at all and fired forward only when the concrete-predicate
  antecedent beside it arrived: two arrival orders, two answers, from a rule the engine
  reported as accepted. An `:inert` rule is exempt. *Migration:* assert the instantiated
  rules, one per predicate the metarule ranged over.
## 0.3.0 — 2026-08-04 — "a type on every refusal"

Correctness fixes across the durable index, the snapshot, the JTMS, the export dump
and the bounded prover, a sweep that gives every refusal a `:type`, the one wire
contract 0.2.0's own sweep left qualified, and the serialization both servers' storage
layer already assumed. Then a run of **inference and belief** work: two orders that
reached two answers, the two entry points that disagreed about an inherited claim, and two
enumerations that grew with the vocabulary rather than with their own answer. Eight
entries are marked **Breaking** — they refuse input 0.2.0 accepted or change an
observable contract, which is why this is 0.3.0 and not 0.2.1; the rest are compatible.

- **Breaking: the daemon's refusal `:type` keywords are plain** — `:not-edn`,
  `:cross-origin`, `:bad-host`, `:body-too-large`, where the namespace serving them
  qualified each one. This finishes tree-wide what 0.2.0's own breaking entry claimed.
- **Breaking: both servers hold one request-body ceiling.** The cap and its
  `VAELII_MAX_BODY_BYTES` override (16 MiB) live in `vaelii.impl.guard`, which both
  read, so the browser answers **413** for an oversized form body where only the daemon
  did. A daemon read is also fully realized **inside** the write monitor — `wire-safe`'s
  walk is what realizes a lazy answer, so running it after the monitor released let a
  `:query` straddle a concurrent `:assert`.
- **Breaking: the browser serializes its writes.** Jetty serves the write routes on a
  thread pool, so two POSTs were two writers — where the storage layer is written on the
  promise that they are not. Interleave two and the WAL holds both frames while the RAM
  map holds one, so the running index and the one replayed on the next open disagree.
  The browser now takes one process-wide monitor around every content write, as the
  daemon always did; a concurrent write waits rather than racing.
- **Every `ex-info` the engine throws carries a `:type`.** Twenty refusals threw an
  untyped map, so a caller had to guess from which keys were present. Two forms that
  threw a raw Java exception now answer instead: `(genl ?x ?x)` / `(disjoint ?x ?x)`
  answer the question one variable in both positions asks.
- **Breaking: an `ist` form must have exactly three elements.** 0.2.0 read `assert` and
  `check` positionally, so `(ist Ctx S junk)` asserted with the extra silently ignored
  and `(ist Ctx)` raised a raw `IndexOutOfBoundsException`. Both refuse with `:shape`.
- **The durable index is gated on its key layout at open.** A log whose stamp does not
  match `kv/index-layout-version` is cleared, rebuilt from the records and restamped,
  `:recover?` notwithstanding; without the gate such a log replays cleanly and then
  misses every read whose key shape moved. **A 0.2.0 durable store carries no stamp, so
  its first open under 0.3.0 pays one automatic reindex**: O(records), logged at `:warn`,
  paid once. `docs/storage.md`.
- **Breaking: `open-kb` refuses a `:base` whose durable index is at an older key
  layout** (`:stale-index-layout`). The repair is a write and a base is mounted
  read-only, so the refusal names the one place the rebuild can happen: open that
  directory as a KB, then mount the fork over it.
- **Breaking: `(fork (fork base))` is refused** (`:stacked-fork`), which is what
  `docs/overlay.md` has always stated.
- **Breaking: `open-kb` refuses a `:recover?` setting it does not name.** `:auto` is the
  default, `true` an alias for it, `:warn` and `false` the rest; any other value read as
  the warn branch and handed back an empty TMS over a store that is not empty, which
  answers `[]` to everything. A stale derived index is dropped on open whatever
  `:recover?` says.
- **Breaking: `close!` releases a durable fork's own directory.** A fork's writable half
  takes the same exclusive lock as any durable KB, so without its own `:dir` it could
  never be handed to another process short of exiting the JVM. 0.2.0's docstring promised
  the opposite, so code that closed a fork in a `finally` and kept reading it worked and
  now does not.
- **A failed compaction takes its temporary files with it.** A rewrite that threw closed
  its handles and left `<log>.compact` behind, and the next compaction in the same
  session opened that temp and appended to it — its replay then put back records deleted
  in between. The cleanup is scoped to the pre-commit phase: past the marker the temps
  are the only complete copy.
- **A failed open gives back the directory lock with no handles still on it.**
  `open-kv-backend` and `open-token-log` replayed their logs outside any guard, so a torn
  frame propagated to a caller that answers a failed open by releasing the lock —
  leaving it released while this JVM still held an open handle.
- **A fork's merged `kv-entries` is realized under its monitor.** Both halves were lazy,
  so the seq handed back from inside the lock realized outside it. An export of a fork
  taken while anything wrote it projected two states at once.
- **The rete alpha registry is synchronized.** It is JVM-lifetime shared state reached
  from the store observer hooks, which fire on whichever thread is writing, and a
  `HashMap` racing its own rehash can leave a reader spinning on a probe loop that never
  terminates. Its check-then-put is one step too, so two callers cannot leave the loser's
  alpha permanently unmaintained.
- **`load-source` claims the catalog under one monitor.** The busy test, the
  already-loaded test and the registration were three separate reads, so two requests
  arriving together each passed all three and spawned a loader.
- **The browser reads untrusted EDN under `Throwable`, as the daemon does.** A deeply
  nested form overflows the reader's stack with a `StackOverflowError`, which an
  `Exception` catch lets escape — a 500 where an unreadable term is the ordinary answer.
- **The index snapshot's roots-fallback blob is validated like the sections beside it.**
  `roots-fallback.nippy` carries argument-root postings, which are primary index truth,
  and a missing or torn blob loaded as `[]` behind a warning while every argument-root
  read answered `#{}` out of a snapshot that opened clean. The meta records the blob's
  count and byte length, and the load thaws strictly.
- **The mapped index snapshot survives a JVM shutdown, and a failed save leaves the
  previous image intact.** The stamp is taken against the records before a byte moves,
  durability registrants close in phases, and every section lands in a `.tmp` until the
  swap. A failed *open* likewise gives back the handles it took.
- **An export dump carries every provenance stamp, and `export → import → export` is
  byte-stable.** The provenance walk covers justification handles as well as sentex ones,
  and import stores a justification's antecedents as a **vector**, the shape the engine's
  own write path stores.
- **The JTMS dedup index carries the identity of the TMS it mirrors.** A nested chain
  over a second KB — legal from an `:on-progress` callback, with overlapping handle
  spaces — could answer one KB's dedup question out of the other's supports. Keys coerce
  fixnum boxing to `Long` at the boundary, since the map compares with Java `equals`
  where the scan compares with `=`.
- **`prove-within` prepares its goal**, through the same `prepare-goal-for-read` every
  other read path takes, so a reifiable NAT or a merge-retired spelling is the same
  question under the bounded prover that it is under `ask`.
- **The rete forward matcher fans over predicate-`genl` sub-predicates at every arity**,
  as the reference `res/match-pattern` does. Fanning only for a two-element sentence gave
  the opt-in matcher a different belief set on any rule whose antecedent had another
  arity.
- **A firing refused at derive time comes back when its exception releases.**
  `place-conseq` does not place a firing whose `exceptWhen` exception already holds, and
  such a firing left no justification and nothing in `jtms/blocked` — so a settle pass
  could not see it and the conclusion stayed suppressed after the block lifted. The same
  knowledge in the other order concluded it. The refusal is recorded as `[rule handle,
  bindings]`, capped at 4096 entries per rule. `docs/exceptions.md`.
- **Five order-independence repairs.** `contradictions` names the same side of a clash
  whatever order the two arrived in; the two settle sweeps sharing one exposure-instance
  budget walk their moved region in content order; `query` with `{:proof? true
  :portfolio? true}` returns each answer once; `negation-nogoods` writes with a
  compare-and-set; and the node engine's inline join plans with the `:est-override`
  belonging to its registry leaf.
- **A forward rule fires on a claim argument-position preservation licenses**, so
  `sentexes-matching` and `ask` stop disagreeing about the same knowledge.
  `(argPreserving largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, which `ask` reached while the fixpoint fired only
  on the claims that were written — so the conclusion it never drew had no `why`, no
  retraction path and no way to be an antecedent. The join contributes the handles the
  inherited claim was read from, so retracting any of them withdraws the conclusion. One
  asymmetry is left: a justification confers the weakest class it rests on, so a
  `:monotonic` claim declared preserved by a `:default` declaration draws a `:default`
  conclusion. `docs/inherit.md`.
- **A head-existential rule carrying an aggregate mints a ground witness.**
  `skolem/frontier-vars` subtracts a post-join literal's output, so the Skolem NAT no
  longer takes a variable into its argument list.
- **An open `disjoint` goal is enumerated from the declarations rather than from the
  vocabulary.** A separation convicts two subtrees, so the answers are the subtypes of
  what a *visible* declaration names and the cost is the answer's own size; 0.2.0 asked
  `taxonomy/disjoint?` once per type, and once per **pair** with both arguments open. On
  4,000 types carrying one separation that is 15.4 ms to 0.13 ms with an argument bound —
  flat where it grew linearly — and at 1,000 types the two-variable goal goes from 2.5 s
  to 4 ms. `lein perf`'s `disjoint-enumeration` check is the claim.
- **A definitional clash is arbitrated from a context that can see both halves.** The
  checks are scoped to the context they are asked in, so a pair whose halves sit either
  side of a `genlCx` edge was answerable from exactly one of the two, and only when
  that half was the one the settle moved. `settle/clash-askers` runs the check from the
  candidate's own context and from the maximal common descendant of it and each context
  holding a sentex it could pair with; nothing is widened.
- **A pair per opposing sentex, not per opposing type.** One sentence stated in a general
  context and again in one that sees it is two sentexes, of possibly different strength,
  and a claim that denies it denies both — where the checks named one handle each, so the
  content-first of the two was weighed and the other left believed beside content that
  contradicts it.
## 0.2.0 — 2026-08-03 — "the public API boundary, drawn"

**Not a drop-in upgrade from 0.1.0.** Several of the changes below refuse input
0.1.0 accepted or change an observable contract — each such entry is marked
**Breaking** — which is why this is 0.2.0 and not 0.1.1. Entries between here and
the 0.1.0 header are in it, newest first.

- **The argument roots are scoped by predicate** (`[:argument-root pred pos
  term]`), so a materialising join reads one literal's postings rather than
  wading through every functor's at a shared slot. An `[:argument-slot pos
  term]` roster, reference-counted off those postings, keeps the
  predicate-agnostic reads answerable as a union over the predicates present.
  The packed long has no room for a fourth key part, so the dense roots route
  the family to their boxed fallback. `index-layout-version` is **2**: an index
  written by 0.1.0 reads as `:layout-changed` and is rebuilt on first open —
  no action needed, but a large durable store pays a reindex for it.
- **Breaking: every handle-taking fn refuses a non-handle** (`:bad-handle`) —
  the vector `assert` returns for a conjunctive rule included, which 0.1.0's
  `retract!` silently answered with `{:removed-sentexes 0}`. `nil` stays a
  question with an answer (`in?` false, `why` `{:stored? false}`,
  `add-provenance` a no-op), and `check-edit` reports what `edit!` throws. `why`
  also takes `{:max-depth n}` (default 256), marks a capped branch
  `{:truncated? true}` instead of overflowing, and refuses bad opts
  (`:unknown-option`).
- **`close!` releases a durable KB's directory** without waiting for JVM exit,
  and `import!` is `export!`'s inverse. An unclean close still releases the
  lock and registry; the first component failure is rethrown after.
- **An `argIsa` / `interArgIsa` / `argGenl` refusal names its convicting
  declaration in content order**, not in whichever order retrieval enumerated.
- **The five sweeps run in CI** — dense TMS, incremental matcher, node query
  engine, its tacticians, reference retrieval — each failing-set-identical
  with the default it replaces. Nothing ran them before.
- **Breaking: `assert` refuses a non-map `opts`** (`:unknown-option`) —
  `(assert kb s ctx :monotonic)` stored a defeasible sentence in 0.1.0.
  `check` already reported the same request; the two agree now.
- **Breaking: `open-kb` recovers by default** (`:recover? :auto`). The old
  `:warn` default handed back a KB that answered wrongly from a reopened
  store. The cost moves to construction — O(records) on a populated store —
  and `{:recover? false}` defers it. `:warn` and `false` remain.
- **The public surface is six namespaces**, where it was one: `vaelii.core`
  plus thin shims `vaelii.client`, `vaelii.starter`, `vaelii.web`,
  `vaelii.serve` and `vaelii.cli` over the `impl` namespaces they front. The
  boundary is now what the docs said it was.
- **Breaking: `vaelii.client`'s `assert` and `assert-rule` are spelled bare**,
  without the `!` 0.1.0 gave them. A `!` marks a fn that destroys stored
  knowledge and neither does — both are additive, and `retract!` is what takes
  one back — so the client now spells them exactly as `vaelii.core` does. A call
  site writing `c/assert!` or `c/assert-rule!` no longer resolves.
- **A clash names the sentex that states the membership**, not one that merely
  entails it, under either retrieval strategy.
- **An auto-compaction queued for a closed store is dropped**, so the next
  open no longer replays it as a crash-interrupted compaction.
- **Breaking: error `:type` keywords are plain across the tree**
  (`:unknown-source`, not `:vaelii.impl.catalog/unknown-source`), and
  `open-kb`'s backend refusals carry one. Swept in the same pass: the settle
  re-check queue no longer drops entries queued by a concurrent thread, and
  `foreign/register` refuses with `ex-info` rather than an elidable `{:pre}`.
- **Leiningen 2.10 is the minimum**: `:preserve-eval-meta` needs it, and 2.9
  ignores the key silently.
- **Breaking: `POST /op` requires `Content-Type: application/edn`.** The type
  is not CORS-simple, so a browser must preflight and the daemon answers no
  CORS headers — which closes cross-site request forgery against a loopback
  daemon. A client that sent no content-type is refused; add the header.
- **Breaking: a request body over 16 MiB is refused** (413) before it reaches
  the heap; `VAELII_MAX_BODY_BYTES` adjusts the cap.
- **Breaking: DNS rebinding is closed on both servers.** Every route requires
  a `Host` naming the interface the server was started on. A request with no
  `Host` still passes (a non-browser client carries no ambient browser
  context); a reverse proxy or local alias sets `VAELII_ALLOWED_HOSTS`.
- **`+with-foreign` names a coordinate that exists**
  (`com.vaelii/vaelii-foreign`); the bare id it carried resolved nothing.
## 0.1.0 — 2026-07-31 — "the first release"

The first release. Below is the development log that produced it, newest
first; every entry below is in 0.1.0.
## 2026-07-30 — "declarations re-check what they change"

- A declaration re-checks the exceptions it moves: `(symmetric P)`,
  `(transitive P)`, `(inverse P Q)` and the `argPreserving` forms change what
  may be concluded with no fact arriving; `(functional P)` sweeps the extent
  when it lands.
- An equality restates a fact for each reader rather than once for the KB, and
  is itself a re-check trigger for `exceptWhen`, `unknown` and census reads.
- A change feed: the region a settle already computes is handed to a listener
  instead of discarded.
- English in — a sentence read into candidates a person still has to accept.
- A qualitative relation two contexts entail together fires a forward
  rule; a believed negative reaches the wiring a positive does; "some context"
  means the union of what the readers answer.
- Three readers of one question agree over a cyclic hierarchy, and settle
  repairs the context ranking after reconciling belief as well as before it.
## 2026-07-29 — "one entry point for backward chaining"

- One public entry point for backward chaining: the four paths measured, then
  consolidated to two chainers behind one entry point with one dial. A proof
  of an ephemeral answer reads the way `why` does.
- The goal frontier's order is a policy measured on time-to-first-answer,
  `:ground-first` by default; the goal-stack chainer drives one solution at a
  time and level 7 streams its search.
- Foreign formats arrive as a classpath plugin, so a reader ships and retires
  without touching the engine.
- A constraint declaration may name a second sentex it must not weigh, and a
  depth bound has no default because there is no defensible one.
## 2026-07-28 — "the gate: lint, suite, and scaling"

- `lein gate`: lint, the suite, and the scaling claims, measured and failed on
  rather than asserted; five checks added for costs that grow with what they
  must not.
- The columnar index is written once and mapped back; backend names read
  `<records>-<index>`, all seven.
- A literal's matches are remembered and retired on a clock; converging
  branches share one rule expansion; a third backward chainer whose state is
  a frontier.
- The naming invariants belong to the knowledge base, and the bulk entry point counts
  what it skips.
## 2026-07-27 — "aggregation over query results"

- Aggregation: a count is a query operator, and a firing that rests on one is
  maintained like any other — gated by a permutation test. A census counts
  distinctness through the representative the asking context elects.
- `argIsa` entails as well as constrains, behind a toggle, retroactively too.
- A definitional clash names a second sentex, making it a nogood, and the
  arbitrating sweep asks the taxonomy rather than a fixed functor set.
- The qualitative network lives on the knowledge base and warm-starts off its
  own previous answer; a violation ledger is a claim about one KB.
- The browser draws term shapes, composes English at three densities, and
  gained `lein browser`; OpenCyc loading went from 378s to 277s.
## 2026-07-26 — "reads scoped to the asking context"

- Contexts got a vantage: every taxonomy supporter records the context it
  asserts from, so disjointness, matching fan-out and settle all read only
  what the asking context can see.
- A firing names the `genl` edges it subsumed through — belief and strength
  run through them like any antecedent, checked against all 24 orderings.
- Records and index became two independent choices, plus an overlay backend:
  a private writable fork over a shared read-only base.
- A knowledge base is readable before it finishes loading, and the suite runs
  on every backend from one script.
## 2026-07-25 — "OpenCyc in the engine's own format"

- OpenCyc, read and re-expressed: every constant given back its role, 1.1M
  sentexes in the engine's own format, on the machine that reads it. Nothing
  of Cycorp's is redistributed.
- An export format no rename can break, with `xz`, an importer, and an oracle
  comparing two knowledge bases; a dump lands every record at its handle.
- Qualitative spatial and temporal reasoning: RCC-8 and three more spatial
  algebras, Allen intervals, durations and instants, behind one glue.
- One gap written in two units is one constraint: both spellings snap to the
  tolerance grid, and a unit given two conversion factors is its own base.
- A knowledge-base catalog with a browser that switches between KBs;
  `inherit` declared rather than assumed; definitional checks reach every
  term; `argGenl` constrains one level up.
## 2026-07-24 — "denser storage, measured first"

- The scale program opened with measurement first: the truth-maintenance
  wall, a posting-encoding bake-off on a real corpus, and a rule audit.
- Three dense representations, each measured: `:memory-dense` integer
  postings, the `:memory-columnar` int-token trie with CSR compaction (3.18x
  whole-index), and a bitmapped TMS behind a protocol.
- The disk side got dense too: positional record reads with a hot-record LRU,
  a positional frame codec, tokenized bodies over a durable dictionary — all
  behind a backend parity gate.
- Recursive forward chaining went O(n³) → O(n log n); a term roster
  enumerates vocabulary in O(terms).
- The web browser was hardened — escape by default, guard the parse, bind
  loopback, refuse cross-origin writes — and a pluggable LLM proposes edits
  and never applies them.
## 2026-07-23 — "performance fixes, and an operational surface"

- A performance review, its findings fixed: the disk log records operations
  rather than grown values (killing an O(N²) write amplification), settle
  keeps a coincidence set, re-checks narrow to the moved ancestor set, region
  fixpoints became semi-naive worklists, compaction is copy-on-write.
- Symbolic equational reasoning: pure oriented rewriting with full
  Knuth-Bendix orientation, order-independent normalization, and
  non-confluence surfaced; `rewriteOf` extended over predicates and types.
- An operational surface: an EDN-over-HTTP daemon, a command-line driver, a
  thin client, and a browser that attaches to a daemon — with the public API
  closing every hole the browser tracked.
- Existential rule heads with deterministic skolemization; an occurs check;
  closures answered on demand; the record split into atomic and rule shapes
  with interned symbols; a bulk-load fast path.
## 2026-07-22 — "sound negation as failure"

- Negation as failure, at top level and in antecedents, with block, sweep and
  revive, and stratification to keep it sound.
- Resource-bounded anytime inference with qualitative cost tiers and a
  cost-ordered forward-chain join; `ask-within` normalizes its goal.
- Reification of non-atomic terms; structural subterm indexing,
  oracle-proven, then on by default.
- The storage protocol: index logic onto one key-value protocol, an in-memory
  backend, then the on-disk substrate — files, lock, durability, record
  store, index store.
- The index benchmark harness, and a per-handle provenance side map.
## 2026-07-21 — "equality lands, and a sudoku solved"

- `exceptWhen` canonicalized into the record, blocking excepted conclusions
  with only reachable firings re-checked; its query reified the way a fact
  is.
- Equality landed: the closure, the `different` prover, a specification
  suite, and wiring into assert; stratification is checked on edge change.
- The engine split out of one namespace into five, and the knowledge base
  restructured into a layered tree loaded on start.
- `assumptionRules` with persistent solve and labeling contexts, proven on a
  sudoku.
- Retrieval got sharper: argument roots, multi-column narrowing, predicate
  subsumption, set-algebra retrieval, an opt-in incremental matcher.
- Truth-maintenance mutations are atomic; lint arrived.
## 2026-07-20 — "order independence, made an invariant"

- Canonical rule form — canonical variables with a varmap, literal order,
  comparison direction — so rules alike up to renaming share one handle.
- The eight-level lookup-to-query stack, lazy throughout, with a browser page
  showing which level answered.
- Order independence and locality pinned as invariants: region-local
  relabelling, belief-following closures, content-keyed tie-breaks.
- The answer-set layer wired to the edge-solver protocol, with a labeling
  materialized as a context; the defeasible layer made sound, six bugs
  pinned as failing tests first; `exceptWhen` began as a failing suite.
- Everything but `core` moved under `vaelii.impl.*`; `!` reserved for
  irreversible operations; tests became net-neutral, and a second concurrent
  run fails fast rather than corrupting the first.
## 2026-07-19 — "the whole stack, day one"

The first day: a contextualized common-sense knowledge base with a trie
index, inference and truth maintenance.

- Sentexes — a sentence plus the context it holds in — stored as records
  behind protocols with nippy serialization; rules are sentexes too, with
  built-in transitivity for types and contexts.
- Forward chaining with dependency-directed retraction, and a backward
  chainer; a non-monotonic TMS with strengths, soft prioritized
  contradictions, and a solver protocol.
- An inverted term index, directed rules, disjointness, well-formedness
  checks, and a pluggable prover query engine; structural connectives
  canonicalize into the record; evaluable arithmetic.
- A web browser over the whole thing, over a starter ontology with every
  term documented.