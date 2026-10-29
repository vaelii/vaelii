# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.30.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking

- **The reification marks are in the forced-monotonic set.** `core.txt` declares
  `(forced_monotonic_predicate reifiable_function)` and `(forced_monotonic_predicate
  unreifiable_function)`, so each mark goes OUT only by retraction. A stored denial of a
  mark is never believed, where a known-true `(not (reifiable_function F))` took the mark
  OUT and left `F`'s applications structural. A `:default` `(reifiable_function F)` beside
  a `:default` `(unreifiable_function F)` is an irreducible conflict: both stay believed
  and `conflicts` reports the pair, where one of them was the loser.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-set).

  *Migration:* retract a mark rather than denying it, and retract one of two clashing
  marks, since a defeat no longer picks one.
  *Breaks:* `ask`, `query`, `conflicts`

## Unreleased

### Breaking: inference

- **No unary predicate declares its argument position.** core.txt drops `(arg C 1 T)` for
  `fixed_arity`, `variable_arity`, `bounded_arity`, `unbounded_arity`, `at_least_binary`,
  `forced_monotonic_between_predicates`, `reifiable_function` and
  `unreifiable_function`, and time.txt drops it for `initially`. Each restated a type the
  predicate's `genl` edges conclude, and added a second justification for every membership
  the edge concluded: the upper layer holds 4,673 justifications with every mint kept
  (was 7,066) and the starter 5,342 (was 8,127). A unary predicate's argument type is
  `thing`. An argument that no disjointness separates from the edge's type is now typed by
  the edge: `(fixed_arity 5)` derives `(relation 5)`, where the declaration refused it
  `:arg-type`. `ontology_test` fails on an `arg` declaration of any predicate of arity 1.
  [argtypes.md](docs/argtypes.md#a-unary-predicate-carries-no-arg-declaration)
  *Migration:* drop `arg` declarations of unary predicates; state the type as a `genl`
  edge.
  *Breaks:* `try-assert` of a unary predicate's membership over an argument outside the
  removed declaration's type

### Breaking: storage

- **A store records its reasoner set, and an open under another set is refused.**
  `add-reasoner` and `open-kb`'s new `:reasoners` option record the shipped reasoners'
  names in the store (`reasoners.edn` in a directory, the memory registry for a space),
  and `export!` writes them into the dump's `meta.edn`. An `open-kb` naming another set,
  none included, and an `import!` into a KB registering another set are refused
  (`:reasoner-mismatch`, naming both sets); `:reasoners :stored` registers the recorded
  set. `fork` registers the reasoners of the KB it forks. The CLI, the daemon and the
  browser's attach open a directory with `:reasoners :stored`.
  [storage.md](docs/storage.md#the-reasoner-set)
  *Migration:* reopen a store that `add-reasoner` was called on with `:reasoners
  [<the names>]` or `:reasoners :stored`, and pass `{:reasoners :stored}` to `import!` or
  `koinii.deref/pull!` to register a dump's set.
  *Breaks:* `open-kb` over a store a KB called `add-reasoner` on, and `import!` of such a
  KB's dump, without `:reasoners`

### Fix: answers

- **An open query answers a part's location and ownership again.** With the starter,
  `(query kb '(locatedIn U1 ?w) ctx)` answered `()` where `ask?` on `(locatedIn U1 Desk)`
  answered true, and `(owns Ann ?p)` named the whole and none of its parts. `CxMereology`
  states its two forward rules again and acknowledges kb-integrity's
  `transitiveInArgInverse` suggestion for each, so `query`, `prove` and `ask?` agree.
  [inherit.md](docs/inherit.md), [integrity.md](docs/integrity.md#what-a-rule-macro-finding-means)
  *Migration:* none; a part's derived `locatedIn` and `owns` are stored again.

### Fix: inference

- **A rule reading `different` beside the starter's time-slice equality is stored.** A
  forward rule with a `(different ?a ?b)` antecedent concluding a kind of
  `uninterrupted` was refused `:not-stratified`, the cycle running through the
  backward `(equals (CxTimeFn (CxTimeFn ?c ?t1) ?t2) …)` rule in `time.txt`. A forward
  rule concluding an equality from a `different` antecedent is refused as before.
  [equality.md](docs/equality.md#interactions)
  *Migration:* a rule set whose only cycle ran through a backward-only equality rule is
  stored.

- **`chain-report` no longer counts a firing an aggregate's moved count withdrew as
  refused.** A rule on `(agg/count 0 …)` whose counted fact arrived in the same `edit!`
  as its subject reported one `:blocked` refusal per subject with no reason, where the
  facts arriving first reported the rule `:silent`. Both orders report it `:silent`, and
  belief is unchanged.
  [aggregate.md](docs/aggregate.md#maintenance-when-the-aggregate-is-a-rule-antecedent)
  *Migration:* none.

- **A rule binding a variable to a class of binary predicates and to an argument of
  `genl` is believed.** Each position of a `type_relation_predicate` asks for what its
  `args` declaration names, `predicate` for `genl`, where it asked for a
  `unary_predicate`; such a rule was held inert as `:arg-variable` and listed as
  `:inert-rule`, although `(genl performedBy doneBy)` relates two binary predicates. A
  position no `args` declaration covers, as in a KB that does not load `core.txt`, carries
  no relation-kind constraint. An
  `:arg-variable` conviction at such a position names the `args` type in `:expected`
  ([#244](https://github.com/vaelii/vaelii/issues/244)).
  [taxonomy.md](docs/taxonomy.md#and-against-the-variables-of-a-rule)
  *Migration:* none.

### Fix: performance

- **A KB that registers a shipped reasoner keeps a reasoning image and seals its log.**
  A `:disk-snapshot` KB opened with `:reasoners` or given `add-reasoner` wrote no image
  at close, so every open paid a full recover, and a crash of its log rebuilt from the
  records. The image's manifest records the reasoner set, and an open with the same
  set installs it.
  [storage.md](docs/storage.md#the-reasoning-image)
  *Migration:* none; the first close after the upgrade writes the image.

## 0.30.0 — 2026-10-27 — "Chaining writes rolled back at `:max-derivations` and a full heap, `why` as a justification graph, `functionCorrespondingPredicate` scoped to the reader, `kb-integrity`'s stranded declarations and rule clashes, `CxTimeFn` time slices"

| Area | Change |
|---|---|
| inference | forward chaining bounds term nesting (`:max-term-depth`) and no derivation depth by default; a write past `:max-derivations` or over a full heap refused `:interrupted` and rolled back; `forward-chain`'s `:on-stop :keep`; every chaining write takes `:max-ms` and `:stop?`; a minted rule's firings capped at the generator fill's class; a convicted firing stored and held OUT; `(args R T)` derives `(argAndRest R 1 T)`; an unsatisfiable qualitative network blocks only its unsatisfiable components |
| NATs | `functionCorrespondingPredicate` respells only where the reader's ancestor set holds the declaration; a rule's consequent stored as written; a `:default` corresponding fact resolves nothing and each use takes a copy; compound `rewriteOf` resolved in every arrival order |
| introspection | `why` returns `{:root h :nodes {…}}` and takes no options; `why-not`'s `{:nearest n}`; `preview` of removing an `except` |
| integrity | `kb-integrity`'s default sweep adds `:stranded-declaration` and live rule clashes; `:work` and `:elapsed-ms` on every answer; Specified obligations audited at their defining contexts; `acknowledgedFinding`; a truncated sweep names its `:pass` |
| daemon | a wire write naming `:principal` refused 403; `VAELII_MAX_QUERY_DEPTH` holds the four clockless reads; `VAELII_TOKEN_TABLE`; `VAELII_MAX_WRITE_MS`; `VAELII_INTEGRITY_MAX_WORK`, `VAELII_INTEGRITY_MAX_RESULTS` |
| refusals and canonicalization | an argument declaration past its predicate's bound length stored; a value naming a predicate or function refused `:not-well-formed`; a ground compound below the literal stored in its marks' argument order; `associative`, `idempotent`, `meetFunctionOf` |
| storage | `import!`'s `:drop-principal?`; `record-arg-types!` stops and resumes; a retraction keeps an inert record a derivation reached; `reindex` and `import!` post re-check keys; `:oplog?` crash recovery |
| shipped ontology | an `inverse` partner's declarations type the swapped position; `CxTimeFn`, `Forever`, `IntervalBeforeFn`, `IntervalAfterFn`, `DatetimeRangeFn`; `intangiblePartOf`; `information_bearing_thing` renamed `information`; the starter types its terms' positions |
| performance | a `genlCx` edge costs what it makes visible; a backward `prove` down a chain costs the same per link; an in-session `recover` costs the store it replays; bounded closure cache |
| koinii, browser, ASP | koinii's surface golden; the term page's concept-graph column; the sentex page's meta-sentexes; `asp/atMostSum`, `asp/atLeastSum`; `VAELII_ASP_OPT_STRATEGY=usc` |

Nineteen entries are **Breaking** and one is a **Refusal**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.29.0 caller changes.

| If your code… | Then |
|---|---|
| relies on forward chaining's default derivation-depth or derivation cap | pass `{:max-depth 64}` and `{:max-derivations 100000}`; pass a larger `:max-term-depth` for deep terms |
| passes `:max-derivations` to a chaining write or `forward-chain` | catch `:interrupted`, pass a larger cap or none, or pass `:on-stop :keep` to `forward-chain` |
| chains over a nearly full heap | nothing: the write is refused `:interrupted` with `:bound :heap` and rolled back |
| resolves an application through a `:default` corresponding fact | assert the corresponding fact `:monotonic`; reload a store written before this release from its source |
| relies on a `functionCorrespondingPredicate` its reader's ancestor set does not hold | state the declaration in a context the reader sees |
| writes a rule whose consequent names an application | state the rule forward (`set/forwardRule`) |
| reads an unsatisfiable network's silence as the whole context's | read `qualitative-network`'s `:consistent?` |
| reads a minted rule's firings as `:monotonic` | assert the generator's fill `:monotonic` |
| reads `violations`' `:arg-type` entries of a firing | read the `:inert-argument` entries |
| declares `args` in a KB that does not load `core.txt` | state `(argAndRest R 1 T)`, or assert the rule |
| reads `why`'s nested shape or passes it options | read `((:nodes w) (:root w))`; drop the third argument |
| stores its own `:principal` provenance field over the wire | rename the field |
| bounds `:prove` and the other clocked reads with `VAELII_MAX_QUERY_DEPTH` | bound them with `VAELII_MAX_QUERY_MS` |
| runs `kb-integrity` without `:categories` | fix the new findings, or pass `:categories` |
| compares `kb-integrity` answers with `=` | `dissoc` `:work` and `:elapsed-ms` first |
| audits a Specified obligation in a descendant context's population | declare the requirement in each descendant context |
| catches `:arg-position` or `:arg-constraint-kind` from `assert` | write with `try-assert` and catch `:definitional-clash` |
| looks up a nested commuting compound in a store written before this release | `export-text!` then `load-text!`; write patterns in canonical order |
| relies on the catalog card's 100,000 derivation cap | fill in the corpus card's cap |
| declares a mark or `inverse` over a value in a predicate position | retract the declaration |

### Breaking: inference

- **Forward chaining bounds the nesting of the terms a firing builds, and no longer bounds
  derivation depth by default.** A derivation deeper than 64 was never stored, so a
  400-link chain through one recursive rule derived 64 of its 400 conclusions; it now
  derives all 400. A firing whose conclusion nests terms deeper than `:max-term-depth`
  (default 8) and deeper than every term it rests on is not placed, which ends a
  recursive `SuccFn` mint or a recursive head existential after 8 terms; the run returns
  `:term-cut`. `default-chain-opts` is `{:max-term-depth 8}`: `:max-derivations` and
  `:max-depth` are still accepted and have no default, so a run past 100,000 conclusions
  goes on until it reaches its fixpoint or the caller's bound.
  [inference.md](docs/inference.md#forward-chaining)
  *Migration:* pass `{:max-depth 64}` to keep the derivation-depth bound, and
  `{:max-derivations 100000}` to keep the derivation cap; pass a larger `:max-term-depth`
  for a rule set that builds deeper terms on purpose.
  *Breaks:* `default-chain-opts`' keys, `assert`, `try-assert`, `assert-rule`,
  `assert-many`, `edit!`, `edit-with-consequences!`, `forward-chain` and `preview` without
  `:max-depth` or `:max-derivations`

- **A chaining write or `forward-chain` that goes past the caller's `:max-derivations` is
  refused and rolled back.** `assert`, `try-assert`, `assert-rule`, the adds of `edit!` and
  `edit-with-consequences!`, and `forward-chain` throw `:interrupted` with `:bound
  :max-derivations` when their chaining makes more than `:max-derivations` conclusions,
  and leave the store and belief as they found them, where the write kept what it had
  placed and returned, under `*bulk-load?*` as outside it. A closure of exactly
  `:max-derivations` conclusions is stored. `assert-many`
  rolls back the sentence in flight, keeps the sentences before it, and throws
  `:interrupted` with their handles as `:stored`. A `forward-chain` that a throw from
  `:on-progress` ends rolls back too. `forward-chain` with `{:on-stop :keep}` keeps what
  it placed and returns `:truncated? true` with `:bound :max-derivations`.
  [inference.md](docs/inference.md#stopping-a-run)
  *Migration:* catch `:interrupted`, or pass a larger `:max-derivations` or none. Pass
  `:on-stop :keep` to `forward-chain`, and in the daemon's `:forward-chain` op, to keep
  what a stopped run placed; the catalog loader, the browser's `/chain` job and the
  generator pass it.
  *Breaks:* `assert`, `try-assert`, `assert-rule`, `assert-many`, `edit!`,
  `edit-with-consequences!` with `:max-derivations`, `forward-chain` and the daemon's
  `:forward-chain` op with `:max-derivations` or a throwing `:on-progress`

- **A chaining write over a nearly full heap is refused `:interrupted` with `:bound
  :heap`.** Every `open-kb` arms the heap mark, so a library embedding with no memory guard
  installed is refused too. A collection that leaves the old generation over 92% stops the
  run at its next firing, and the write rolls back in what is left. The stop holds only
  while the old generation also reads over 92% at that firing, so dead objects a young
  collection counted stop nothing. `assert-many` reads the mark before each sentence, so a
  batch under `:chain? false` stops too. `forward-chain` is
  refused and rolled back there too, under either `:on-stop` value. A removal's settle,
  `recover` and an operation-log replay go on. `vaelii.heap.mark=false` leaves the old
  generation's collection-usage threshold to an embedder that sets its own.
  [caches.md](docs/caches.md#the-heap-mark)
  *Migration:* none.
  *Breaks:* `:interrupted`, `assert`, `try-assert`, `assert-rule`, `assert-many`, `edit!`,
  `edit-with-consequences!` that kept the conclusions placed before a full heap stopped them,
  `forward-chain` that ran to its fixpoint over a full heap

- **A `:default` corresponding fact no longer resolves an application or merges its
  placeholder; each use of the placeholder takes a copy naming the value.** With
  `(motherOf Muffet Mary)` asserted `:default`, `(likes Tom (MotherFn Muffet))` stores a
  minted constant `K` where it stored `Mary`, and a `K` already minted keeps its sentexes
  believed beside a derived `(likes Tom Mary)` placed where the fact, the declaration and
  the use are seen; a rule naming `K` takes a copy the same way, and a goal naming `K`
  reads both spellings. A defeat of the fact takes the copies OUT. A `:monotonic` fact
  resolves and merges as before. The projection `(motherOf Muffet K)` and the merge
  `(rewriteOf Mary K)` are derivations where they were premises, so `why` shows their
  justifications; two declarations for one function each project the placeholder onto
  their own predicate, and the value side reads only the declarations the context sees.
  [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* assert a corresponding fact `:monotonic` where the application should
  resolve to its value. A store written before this release holds its projections and
  merges as premises, so reload it from its source.
  *Breaks:* `assert` of an application beside a `:default` corresponding fact, `assert`
  of a `:default` corresponding fact, `why` of a projection or a merge, `ask` of a
  corresponding predicate under two declarations of one function

- **A `functionCorrespondingPredicate` respells a rule or a goal only where the reader's
  `genlCx` ancestor set holds the declaration's context.** A declaration stated only in a
  context under CxUniverse respelled CxUniverse's rules and goals, so `(ripe AppleTree)` was
  believed at CxUniverse through a correspondence CxUniverse does not see. A rule now reads
  the declarations its own context sees, and is held there where it sees none; its
  spelling through each other declaration is stored at the contexts that see both, so a
  CxUniverse rule beside a CxSide declaration fires in CxSide. A goal at a query context or
  a variable context reads the declaration through a predicate variable, which its answers
  bind. [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* a KB whose reader relies on a declaration its ancestor set does not hold
  states the declaration in a context the reader sees. `recover` stores the spellings a
  held rule reads at those contexts in a store written before them. The reasoning image
  carries the held rules, so an image written before this release is declined and the
  first open recovers in full ([storage.md](docs/storage.md)).
  *Breaks:* `assert` of a rule applying a function declared outside its context's ancestor
  set, `prove`, `query` at `CxInference`, `CxEverything` or a variable context

- **A rule's consequent is stored as written, and only its antecedents are read through
  `functionCorrespondingPredicate`.** A forward firing mints a constant for each
  application of a `reifiable_function` its consequent names, with or without a
  correspondence, and a recursive consequent such as `(num (SuccFn ?x))` mints up to the
  chain's `:max-term-depth` per write. A consequent application whose arguments an antecedent
  names takes that antecedent's variable. A backward rule whose consequent names an
  application answers no goal over it: `prove` of `(grownIn (FruitFn AppleTree) ?o)`
  through `(implies (bears ?t ?o) (grownIn (FruitFn ?t) ?o))` answers nothing.
  [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* state such a rule forward (`set/forwardRule`): its firing mints the
  application and stores the conclusion over the constant, which the goal reads.
  *Breaks:* `assert` of a rule whose consequent names an application, `prove`, `query`

- **An unsatisfiable qualitative network blocks only its unsatisfiable connected
  components.** With `(before A B)` and `(after A B)` in a context, `(subintervalOf D D)`
  answered false there for a `D` no fact names, and true once a rule concluded
  `subintervalOf`; it answers true on both routes, and `(before D F)` beside a `(before D
  E)`, `(before E F)` chain answers true. A goal naming a node of an unsatisfiable
  component answers nothing, on both routes: the `reflexive` and `transitive` provers
  answer no goal there either. A negative metric cycle or a point-network cycle blocks
  the intervals its instants bound, and a cycle through instants that bound no interval
  leaves the interval network satisfiable; a forward firing is withdrawn only when its
  calculus antecedent names a blocked node. `qualitative-network`'s
  `:unsatisfiable-sources` holds one entry per unsatisfiable component of the source that
  bounds an interval ([#232](https://github.com/vaelii/vaelii/issues/232)).
  [qcn.md](docs/qcn.md#unsatisfiability-is-per-component)
  *Migration:* a caller that read an unsatisfiable network's silence as the whole
  context's reads `qualitative-network`'s `:consistent?`, which still reports the whole
  network.
  *Breaks:* `ask`, `query`, `possible-relations`, `qualitative-network`
  `:unsatisfiable-sources`, forward firings over a calculus antecedent in a context with
  a contradiction

- **A generator's minted rule caps the class of each of its firings at its own class, the
  class of the generator's fill.** A rule informant with no premise mark joins the class
  cap, as an antecedent does: a generator over a `:default` fill concludes `:default` from
  `:monotonic` facts, where it concluded `:monotonic`, and a defeat of the fill hides
  those conclusions with the minted rule. An `intersection` asserted `:default` gives
  `:default` memberships.
  [nmtms.md](docs/nmtms.md#strength-propagates-from-the-antecedents)
  *Migration:* assert the generator's fill `:monotonic` to keep its conclusions
  `:monotonic`.
  *Breaks:* `defeat-class` of a firing of a minted rule, `intersection` membership class

- **A rule's conclusion an argument declaration convicts is stored and held OUT, as the
  same sentence asserted is.** The firing stores the conclusion with its justification,
  and `violations` lists it as `:inert-argument` where it listed `:arg-type`, `:arg-genl`,
  `:inter-arg-type` or `:quoted-arg-type` under the rule's handle. The retraction or edge
  that lifts the conviction brings it IN, live and after a `recover` in place or over a
  fresh open. `chain-report` lists the firing among its rule's `:refusals` as `:blocked`
  with reason `:constraint`. A conviction of a function application's input still drops
  the conclusion.
  [argtypes.md](docs/argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert)
  *Migration:* read a convicted firing from the `:inert-argument` entries of `violations`.
  *Breaks:* `violations` `:arg-type` entries of a firing

- **`(args R T)` derives `(argAndRest R 1 T)`.** A `set/forwardRule` in `core.txt` states
  the entailment the two spellings' comments describe and stores the `argAndRest` twin, so
  `query (argAndRest R ?n ?t)` answers `[{?n 1 ?t T}]` of a relation declared only
  through `args`, and the readers of what a position holds look up `arg` and `argAndRest`
  alone. So do the assert-time checks: an `args` declaration is refused, and derives
  memberships, through the twin, whose handle an entailment rests on and whose
  `argAndRest from 1, position N` a refusal names. Retracting the `args` declaration
  retracts the twin. [argtypes.md](docs/argtypes.md)
  *Migration:* a KB that loads `core.txt` needs none. A KB that does not has no forward
  rule, so its `args` declarations type nothing: state `(argAndRest R 1 T)` instead, or
  assert the rule.
  *Breaks:* `args`, `assert`, `check`

### Breaking: introspection

- **`why` returns the justification graph, `{:root h :nodes {h node …}}`, with each
  reachable handle once, and takes no options.** A node's `:support` entries name their
  antecedents by handle in `:because`, where they held each antecedent's node. The result
  grows with the reachable graph and not with the paths through it, so `why` has no depth
  bound: the `:max-depth` option and the `{:truncated? true}` and `{:cycle? true}` nodes
  are gone, and a 300-link chain comes back whole. `argue`'s `:for-why` and
  `:against-why` carry the same graph. The browser's proof page expands each derived node
  once and links each later occurrence to it. [api.md](docs/api.md)
  *Migration:* read the root as `((:nodes w) (:root w))` and an antecedent `h` as
  `((:nodes w) h)`; drop a third argument to `why`.
  *Breaks:* `why`, `why`'s `:max-depth`, `argue`'s `:for-why` and `:against-why`, `vaelii.client/why`, the CLI's `why` output

### Breaking: daemon

- **A wire write naming the provenance `:principal` is refused**, 403
  `:creator-mismatch`, at `:assert`, `:try-assert`, `:assert-rule`, `:assert-many`,
  `:edit`, `:edit-with-consequences` (in opts or their `:provenance`) and
  `:add-provenance`, on the daemon and the browser's `POST /op`, with or without a token
  table. The daemon records that key from a token-table grant.
  [operations.md](docs/operations.md#the-token-table)
  *Migration:* a client storing its own `:principal` provenance field renames it.
  *Breaks:* `:principal`, `:add-provenance`

- **The daemon's depth ceiling, `VAELII_MAX_QUERY_DEPTH`, holds only `:query`, `:query?`,
  `:query-status` and `:argue`, the four reads that take no clock.** `:prove`,
  `:provable?`, `:prove-within`, `:why-not`, `:search-tree` and `:compare-tacticians` are
  held to the clock ceiling alone, so a request to one of them naming a `:max-depth` past
  the ceiling answers where it was refused `:over-ceiling`.
  [defenses.md](docs/defenses.md#a-search-bound-may-be-lowered-by-a-request-and-not-raised)
  *Migration:* bound those reads with `VAELII_MAX_QUERY_MS`.
  *Breaks:* `VAELII_MAX_QUERY_DEPTH` at `:prove`, `:provable?`, `:prove-within`, `:why-not`, `:search-tree` and `:compare-tacticians`

### Breaking: integrity

- **`kb-integrity`'s default sweep reports stranded declarations and live rule
  clashes.** Two new categories run without `:categories`: `:stranded-declaration`, each
  believed `arg`, `genlArg`, `interArg` or `interArgEqual` declaration the audit context
  sees that names a position its predicate does not have, and `:rule-clash`, each pair of
  rules the audit context sees whose conclusions would contradict if both fired, where
  both rules chain and no `exceptWhen` handles the clash. A KB holding either now sweeps
  `:gap` where it swept `:audited`. On the starter plus the test-world, `:rule-clash` pairs
  every rule the audit context sees, and one default sweep at `CxUniverse` took 1.9 s at a
  load average of about 100 on 10 cores, 0.1 s of it outside `:rule-clash`; a `:categories`
  set that leaves `:rule-clash` out skips the pairing. [integrity.md](docs/integrity.md#what-a-rule-clash-finding-means)
  *Migration:* fix the finding, or pass `:categories` naming the categories to run.
  *Breaks:* `kb-integrity`

- **Every `kb-integrity` answer carries `:work` and `:elapsed-ms`**, where only a
  `:truncated` one did, so a sweep with the work ceiling lifted reports what it spent.
  [integrity.md](docs/integrity.md#the-call)
  *Migration:* `dissoc` `:work` and `:elapsed-ms` before comparing an answer with `=`.
  *Breaks:* `kb-integrity`'s `:audited` and `:gap` answers, `vaelii.client/kb-integrity`

- **Specified obligations audit their defining contexts.** `all-specified-violations`
  and `kb-integrity` read each visible `predAllSpecified` / `predSpecifiedAll`
  declaration's population and fillers where the declaration is stored. Descendant-only
  instances and fillers no longer alter an ancestor obligation. Multiple definitions
  combine under the existing key without consuming extra result-cap entries.
  Native-only registry declarations, which have no stored defining context, retain
  their querying-context audit.
  [predall.md](docs/predall.md)
  *Migration:* declare a Specified requirement in each descendant context whose local
  population must be audited. Direct `specified-violations`, Exists audits and
  native-only registry declarations retain their existing context behavior.
  *Breaks:* `all-specified-violations`, `kb-integrity`

### Breaking: refusals

- **`assert` stores an argument declaration naming a position past its predicate's bound
  length, and a `genlArg` on an `instance_relation_predicate`, in either arrival order.**
  A bound length strands the declaration: it constrains nothing, mints nothing, and
  `kb-quality`'s `:declarations` lists it. `try-assert` refuses whichever of the
  declaration and the length binding (or the membership) arrives second, as
  `:definitional-clash` with `:violation :arg-position` or `:arg-constraint-kind`, and
  `check` no longer reports either.
  [taxonomy.md](docs/taxonomy.md#the-declarations-are-checked-against-each-other)
  *Migration:* write declarations with `try-assert` to keep the refusal, and catch
  `:definitional-clash` reading `:violation` where a caller caught `:arg-position` or
  `:arg-constraint-kind`.
  *Breaks:* `assert` of `arg`, `genlArg`, `interArg`, `interArgEqual`, `argArg` and
  `arg1`…`arg5`, `try-assert`, `check`

### Breaking: canonicalization

- **A ground compound below the literal stores in its marks' argument order.** Under
  `(commutative PairFn)`, `(holds (PairFn Ann Bob))` and `(holds (PairFn Bob Ann))` are
  one sentex, and so are two spellings of a symmetric or commuting literal inside a
  sentence argument; a ground goal finds the row in either order, and a mark arriving or
  leaving re-spells the rows nesting its functor. A quoted form, a `natFormula` or
  `rewriteOf` expression and a `reifiable_function` application keep their written order.
  A variable inside a quoted form leaves its compound sortable, and `core.txt` declares
  `(commutative RulePairFn)`, so the two orders of an `acknowledgedFinding :rule-clash`
  subject are one sentex. A pattern holding a variable inside such a compound matches the
  stored order only ([#228](https://github.com/vaelii/vaelii/issues/228)).
  [canonicalization.md](docs/canonicalization.md#compounds-below-the-literal-sorted)
  *Migration:* a store written before this keeps each nested compound as written, and a
  ground lookup by that spelling misses the row; `export-text!` then `load-text!`
  re-canonicalizes it. Write a pattern's commuting compound in its canonical order, or
  bind the whole compound to one variable.
  *Breaks:* `assert`, `ask`, `ask?`, `handle-of` and `sentexes-matching` over a ground
  compound below the literal whose functor is `symmetric` or commuting, against a store
  written before; a goal or rule antecedent whose commuting compound below the literal
  holds a variable and is written out of canonical order

### Breaking: browser

- **The catalog's load cards fill in no derivation cap.** Both cards filled in a
  `:max-derivations` of 100,000, so a chained corpus load deriving more stopped there with
  `:truncated? true`; a corpus load now chains to its fixpoint unless the reader fills in
  the cap. A generator card left without a cap takes `generate/defaults`' value, as a
  `generate/load-into` call does.
  [catalog.md](docs/catalog.md#loading)
  *Migration:* fill in the corpus card's derivation cap to keep a bound.
  *Breaks:* the corpus card's `:max-derivations` default of 100,000

### Refusal: naming and well-formedness

- **`assert` and `check` refuse a value in a position that names a predicate or a
  function, as `:not-well-formed`.** A string, number, keyword, boolean, character, `nil`
  or tagged literal as the argument of a predicate mark (`transitive`, `symmetric`,
  `commutative`, `modal_predicate` and the rest), as the relation of `closedExtentForArg`,
  `functionalInArg`, `commutativeInArgAndRest` or `commutativeInArgs`, or on either side of
  `inverse` or `genlInverse` was stored, and the mark and `inverse` caches filed it as a
  predicate. A stored one recovers with no taxonomy entry.
  [taxonomy.md](docs/taxonomy.md#well-formedness-vaeliiimplwff)
  *Migration:* retract each such declaration; a store that keeps one holds the sentex,
  installs no mark, `inverse` or `genlInverse` entry from it, and `check` of its sentence
  reports the refusal.
  *Breaks:* `:not-well-formed`, `transitive`, `inverse`, `genlInverse`, `closedExtentForArg`

### Additive: daemon

- **`VAELII_TOKEN_TABLE` names a per-principal token table**, an EDN file mapping each
  bearer token to `{:principal :writes :admin?}`; `serve/start` and `serve/app` take it as
  `:token-table`. Set, it replaces `VAELII_API_TOKEN`, and a write op lands only in the
  contexts the presenting token's grant names (403 `:forbidden-context`), recorded under
  the grant's principal as `:creator` and provenance `:principal` (403
  `:creator-mismatch` for another). A write whose rule firings conclude outside those
  contexts is refused the same way and taken back. Reads stay open to every token. A
  table that does not check stops the daemon at start (`:bad-token-table`, exit 2). Unset,
  the daemon authenticates as before. A grant bounds every context a write's storage
  reaches: the placement context, a `CxUniverse` lift, a `genlCx` edge's lower context and
  each context a rule's consequent concludes into; placement declarations,
  variable-functor consequents and `:export` need an `:admin?` grant.
  [operations.md](docs/operations.md#the-token-table)
  *Migration:* none.

- **`VAELII_MAX_WRITE_MS` holds the served `:assert`, `:try-assert`, `:assert-rule`,
  `:assert-many`, `:edit` and `:edit-with-consequences` to a clock, off (0) by default.**
  Set, a request may name a smaller `:max-ms` and is refused `:over-ceiling` for a larger
  one, a write naming none is given the ceiling, and a write the clock ends is **400**
  `:interrupted` and rolled back. `:forward-chain` takes a `:max-ms` the ceiling does not
  fill in, and `:preview` and `:abduce` take no clock.
  [operations.md](docs/operations.md#operator)
  *Migration:* none.

- **`VAELII_INTEGRITY_MAX_WORK` and `VAELII_INTEGRITY_MAX_RESULTS` set the daemon's
  `:kb-integrity` ceilings**, 10000 work units and 1000 findings by default, and `0` lifts
  either. A request may still name a smaller bound and is refused `:over-ceiling` for a
  larger one. [operations.md](docs/operations.md#operator)
  *Migration:* none.

### Additive: koinii

- **`adjudication/resolve-by-majority` counts a wire ballot whose daemon-recorded
  `:principal` is its voter**, as it counts an attested one, when the ballot is in the
  voter's own context. A daemon holding a token table records the principal, and
  `deref/pull!` drops a pulled commit's. A ballot with neither stays refused.
  [koinii.md](docs/koinii.md#identity-and-the-write-boundary)
  *Migration:* none.

- **koinii's `dispute`, `adjudication`, `belief`, `deref` and `identity` fns refuse a
  `vaelii.client` connection or a medium in place of a KB** with `:koinii/needs-kb`, whose
  `:fn` names the fn, where they threw an engine exception naming neither.
  [koinii.md](docs/koinii.md#the-deployment-shape)
  *Migration:* none.

- **koinii's surface is frozen in `test/golden/koinii-surface.edn`**, apart from the
  engine's goldens: the public vars of `vaelii.koinii.*` with their arglists, the refusal
  `:type`s its modules raise, and the arity of each term CxRegistry, CxSpeechActs and
  CxDisputes declare. A koinii change that removes one, or changes an arglist or an arity,
  is a contract change, and its changelog entry names it (CONTRIBUTING §3.8).
  [koinii.md](docs/koinii.md)
  *Migration:* none.

### Additive: inference

- **Every write that chains takes `:max-ms` and `:stop?`, and a write either one ends is
  rolled back.** `:max-ms` is wall-clock milliseconds from the call; `:stop?` is a function
  of no arguments, asked at most every `:progress-every-ms`. `assert`, `try-assert`,
  `assert-rule` and the adds of `edit!` and `edit-with-consequences!` (a new `edit!` arity
  takes a map of `edit-opt-keys`) throw `:interrupted` and leave the store and belief as
  they found them.
  `assert-many` keeps the sentences before the one in flight and carries their handles as
  `:stored`, and `bulk-assert-facts!` reads the bound and the heap mark before each fact
  and does the same. A write under `*bulk-load?*` rolls back as one outside it does.
  `forward-chain` takes both, and takes `:on-stop`: `:rollback`, the default, rolls a
  stopped run back as a write does, and `:keep` keeps what the run placed, settles, and
  returns `:truncated? true` with `:bound` naming the bound. A kept run is incomplete until a run with no bound completes
  the closure.
  [inference.md](docs/inference.md#stopping-a-run)
  *Migration:* none.

- **A goal answers the declared result type of a ground application that is never
  minted.** `(time_point (InstantFn 2026 10 6 0 0 0))` holds by `(result InstantFn
  time_point)`, from `ask`, `prove` and the inference engine, so a backward rule with a
  `(time_point ?w)` antecedent fires for an `InstantFn` term. A forward rule's type
  antecedent does not read it.
  [nat.md](docs/nat.md#typing-an-application-that-is-never-minted)
  *Migration:* none.

### Additive: integrity

- **`(acknowledgedFinding category subject "reason")` records that a `kb-integrity`
  finding was looked at, and why it stays.** The sweep moves an acknowledged finding to a
  review-only bucket instead of dropping it, carrying the reason as `:acknowledged`: a
  rule pair `(RulePairFn (Quote R1) (Quote R2))` from `:rule-clash` to
  `:rule-clash-review`, and a suggested declaration from `:rule-macro` to the new
  review-only `:rule-macro-review`. Each rule is quoted on its own rather than the pair
  as a whole, since a quoted term is opaque: `RulePairFn`, outside both quotes, holds the
  pair (its corresponding predicate is `rulePairOf`), and the sweep reads its two
  arguments in either order as one pair. `acknowledgedFinding`'s second argument is a
  quoted `expression`, which admits a `RulePairFn` subject beside a `:rule-macro`
  declaration, and an atomic subject as well.
  `declined_rule_macro` is now sugar: a `core.txt` forward rule concludes
  `(acknowledgedFinding :rule-macro D "Acknowledged via declined_rule_macro; no reason
  supplied.")` from it, and the sweep reads only the acknowledgment. `abstract.txt`
  acknowledges the two clashes it leaves unexcepted on purpose, the root denial against
  the tangible and the situation proper readings' definitions, so the shipped ontology
  sweeps `:audited`. [integrity.md](docs/integrity.md#acknowledged-findings)
  *Migration:* none; a declined suggestion is still absent from `:rule-macro`, and is
  listed under `:rule-macro-review` when `:categories` names it.

- **A truncated `kb-integrity` names the pass it stopped in**, as `:pass`, beside its
  `:reason` and `:work`. [integrity.md](docs/integrity.md#the-call)
  *Migration:* none.

- **Taxonomy coverage, stranded declarations and rule clashes are `kb-integrity`
  categories, implemented once.** The three checks move out of `vaelii.impl.quality` into
  `vaelii.impl.integrity`, which reports them as `:stranded-declaration`, `:rule-clash`,
  and two review-only categories: `:taxonomy-island`, each edged type node the audit
  context sees that does not reach the found root, and `:rule-clash-review`, each clash
  pair with a `set/inertRule` (marked `:inert true`) or one a stated exception handles
  (`:excepted true`). `kb-quality`'s `:taxonomy`, `:declarations` and `:clashes` keys,
  `quality-report`, the `:kb-quality` and `:quality-report` daemon ops and `lein cli
  quality` answer as before, computed by the same code over the whole KB.
  [integrity.md](docs/integrity.md), [quality.md](docs/quality.md).

### Additive: storage

- **`import!` takes `:drop-principal? true`**, which drops the `:principal` key from every
  provenance map it imports. By default provenance lands as written.
  [api.md](docs/api.md),
  [operations.md](docs/operations.md#the-token-table)
  *Migration:* none.

- **`record-arg-types!` runs the argument-type pass so that it stops, resumes and moves
  past a slow fact.** Each fact's checks run under `:budget-ms` (2000); a fact past it is
  set aside with the part of the checks that ran out, and `:retry-deferred? true` draws it
  again. `:stop?`, `request-stop!`, a shutdown and a throw from `:on-progress` stop it at a
  fact boundary after a commit that settles, forces the stores to disk and records what the
  pass owes in the KB's directory (`arg-types-owed`), which the next call resumes under
  any engine; `clear!` removes it. `edit-records!` makes the pass owed when it removes
  anything, and `settle-record-edits!` takes `:on-progress` and, under
  `{:arg-types? false}`, returns a settled KB on disk with the pass owed.
  `record-arg-types` draws each functor's facts by handle. Two new refusals: `:owed-record-ahead`, an owed record written after the records
  the store holds, and `:unknown-owed-record`, one of a shape this engine does not read.
  [argtypes.md](docs/argtypes.md#the-pass-over-a-stored-kb),
  [storage.md](docs/storage.md#editing-the-records-of-a-kb-without-belief)
  *Migration:* none.

- **`settle-record-edits!`' `:on-progress` reports the loop a recover step is in.** While a
  step runs, a `:recover` call carries `:sub`, `{:id :label :done :total}` of the loop that
  ticked (`:id` the loop's progress-line keyword), at most once a second a loop, so a step
  of hours shows its count.
  [operations.md](docs/operations.md#progress-lines)
  *Migration:* none.

### Additive: canonicalization

- **`associative`, `idempotent` and `meetFunctionOf` reshape a function's ground
  applications below the literal.** Under `(meetFunctionOf F subintervalOf)`, `(p (F A
  (F B A)))` and `(p (F B A))` store as one sentex `(p (F A B))`, and `(p (F (DatetimeFn
  "2000") (DatetimeFn "2000-03")))` stores as `(p (DatetimeFn "2000-03"))`. Absorption
  reads the order's registered comparator and never a stored fact of the order; a
  declaration arriving after the facts merges their rows, and its retraction splits them
  back. No shipped function carries a mark.
  [canonicalization.md](docs/canonicalization.md#a-functions-terms-reshaped-by-declaration)
  ([#181](https://github.com/vaelii/vaelii/issues/181))
  *Migration:* none.

### Additive: browser

- **The sentex page lists the meta-sentexes naming the sentex and shows its provenance
  map.** `sentexes-naming` answers every stored sentex nesting `(sentexHandle h)`, with
  `{:believed? true}` to filter, and the daemon serves it.
  [web.md](docs/web.md), [api.md](docs/api.md)
  *Migration:* none.

- **On a landscape screen 60rem or wider, a term page puts its concept graph in a
  right-hand column** that stays in view while the sentex groups scroll. A narrower or
  portrait screen stacks the heading, the graph and the groups. [web.md](docs/web.md)
  *Migration:* none.

### Additive: ASP

- **`VAELII_CLASP_BIN` (or `-Dvaelii.clasp.bin`) names the executable the subprocess
  backend runs**, and the `clingo` executable serves in clasp's place: a machine with
  `clingo` alone, or `pip install clingo` behind a wrapper script, gets the edge solver
  without `clasp` on `PATH`. The solver install steps are per platform.
  [asp.md](docs/asp.md#getting-a-solver)
  *Migration:* none.

- **`asp/atMostSum` / `asp/atLeastSum` and their soft twins bound the total weight of the
  chosen heads**, each head weighed by a background fact:
  `(asp/atMostSum 9 ?w ?c (and (load ?c) (tons ?c ?w)))`. A negative or non-integer weight
  is refused at the solve as `:not-well-formed`.
  [solving.md](docs/solving.md#atmostsum--atleastsum--a-weighted-bound)
  *Migration:* none.

- **`VAELII_ASP_OPT_STRATEGY=usc` runs every ASP solve under core-guided optimization**,
  which proves optima that the default branch-and-bound (`bb`) stops short of at the solve
  limit. [asp.md](docs/asp.md#the-optimization-strategy)
  *Migration:* none.

- **`do/label`'s result carries `:unenumerated` and `:unenumerated-in-guards`**, naming
  each `transitive` predicate the grounding read with both arguments open, where the
  stored edges answer and the closure does not.
  [solving.md](docs/solving.md#dolabel-base-into-mode)
  *Migration:* none.

### Additive: shipped ontology

- **An argument declaration of one partner of an `inverse` types the swapped position of
  the other.** From `(inverse parentOf childOf)`, the `arg` and `quotedArg` declarations
  of `parentOf` conclude those of `childOf`, argument 1 to argument 2 and back.
  `core.txt` declares `inverse` forced-monotonic and `symmetric`, so where `core.txt` is
  loaded a denial of `(inverse P Q)` loses to a believed one at either strength. An inert
  inverse, as `space.txt` states for each converse pair, types no argument.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-set)
  *Migration:* none.

- **`time.txt` ships `CxTimeFn`, the time slice of a context, with the vocabulary of
  [#181](https://github.com/vaelii/vaelii/issues/181): `time_slice_context`,
  `monad_context`, `genlMonad`, `CxMonadOfFn`/`cxMonadOf` and `CxTimeOfFn`/`cxTimeOf`.**
  `(CxTimeFn CxStory (YearFn 2000))` is the year 2000 of `CxStory`. The KB now believes
  `(result CxTimeFn context)` and `(contextArgSubrelation CxTimeFn 2 subintervalOf)`,
  which a KB had to assert itself before reading a time-sliced context through its
  application. `(result CxTimeFn time_slice_context)` classifies every slice, with
  `(genl time_slice_context context)`. `CxTimeFn`'s first argument is any `context` and
  its second a `time`. `monad_context` is a context that is not a slice; `(not (arg
  CxTimeFn 1 monad_context))` states that the first argument is not typed by it, because
  a declared argument type entails membership. `CxMonadOfFn` and `CxTimeOfFn` name a
  context's monad and time. `genlMonad` is a binary relation between two contexts that
  orders monads alone, as `subintervalOf` orders times.
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad)
  *Migration:* none.

- **A slice of a slice is the slice at the intersection of the two times, and `time.txt`
  ships `subtimeOf` and `TimeIntersectionFn`
  ([#181](https://github.com/vaelii/vaelii/issues/181)).** `(subtimeOf A B)` is one time
  lying within another, whatever the two kinds of time; it is reflexive, `(genl
  subtimeOf partOf)` and `(genl subintervalOf subtimeOf)` place it, and an instant a
  time includes is a subtime of it by a backward rule. `(TimeIntersectionFn A B)` is the
  time two times have in common, the meet over `subtimeOf`, an `unreifiable_function`
  with `timeIntersectionOf` as its corresponding predicate. Backward rules make it a
  `subtimeOf` each argument when both are believed times, and a `subintervalOf` each
  when both are believed `time_interval`s. Backward rules over `cxMonadOf` and
  `cxTimeOf` take a slice apart: a context that is not a slice is its own monad, a slice
  has the monad of the context it slices, a slice of a `monad_context` covers its own
  time, and a slice of a slice covers the `TimeIntersectionFn` of the inner slice's time
  and its own. They read the `natFormula` of the slice's `cx/` constant, so a depth-6
  `query (cxTimeOf K ?t)` answers for `K` written as `(CxTimeFn S Jan)` with `S` the
  `cx/` constant of `(CxTimeFn CxStory Y2000)`. A backward rule states that `(CxTimeFn
  (CxTimeFn C A) B)` equals `(CxTimeFn C (TimeIntersectionFn A B))`; it concludes about
  two applications, so it answers no goal, and the two spellings reify to two `cx/`
  constants. [time.md](docs/time.md#a-slice-of-a-slice)
  *Migration:* none.

- **Two `CxTimeFn` slices that differ only in the monad are ordered by `genlMonad`
  ([#181](https://github.com/vaelii/vaelii/issues/181)).** `time.txt` declares
  `(contextArgSubrelation CxTimeFn 1 genlMonad)` beside the position-2 `subintervalOf`
  declaration, so with `(genlMonad CxSubStory CxStory)` stated, `(CxTimeFn CxSubStory
  (YearFn 2000))` is a computed genlCx spec of `(CxTimeFn CxStory (YearFn 2000))` and
  sees what it states. The producer reads a stated `genlMonad` fact, so retracting it
  withdraws the edge. Two slices that differ in both the monad and the time are ordered
  only through a third slice that differs from each in one argument and has been written
  into. [context-nat.md](docs/context-nat.md#the-structural-genlcx-producer),
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad)
  *Migration:* none.

- **`time.txt` ships `Forever`, the time interval that contains every time.** Every
  `time_interval` is `(subintervalOf ?interval Forever)`, every `time_point` gives
  `(includesInstant Forever ?instant)`, and every `monad_context` has `(cxTimeOf ?monad
  Forever)`. The three are backward rules: a query that asks gets the answer, and
  nothing is stored for every interval, so a network relates Forever only where
  something mentions it. An interval and an instant get separate rules because
  `subintervalOf` relates two `time_interval`s and an instant is never one.
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad)
  *Migration:* none.

- **`time.txt` ships `IntervalBeforeFn` and `IntervalAfterFn`, the time before and the
  time after a moment, with their corresponding predicates `intervalBeforeOf` and
  `intervalAfterOf`.** `(IntervalBeforeFn W)` is every moment before W and
  `(IntervalAfterFn W)` is W and every moment after it: every interval includes its
  start and excludes its end, so the two meet at W and W belongs to the after side
  alone. Each is an `unreifiable_function` from a `time_point` to a `time_interval`, and
  a `set/backwardRule` gives its one bound, `(endOf (IntervalBeforeFn W) W)` and
  `(startOf (IntervalAfterFn W) W)`, when `(time_point W)` is believed. An `(InstantFn
  …)` term answers no `time_point` query, so for one the bound is stated.
  [time.md](docs/time.md#naming-an-interval-the-calendar-constructors)
  *Migration:* none.

- **`time.txt` ships `DatetimeRangeFn`, a range between two reduced-precision ISO
  strings, with its corresponding predicate `datetimeRangeOf`.** `(DatetimeRangeFn
  "2000-01" "2000-06")` is January through June 2000: it begins when `(DatetimeFn
  "2000-01")` begins and ends when `(DatetimeFn "2000-06")` ends. It is an
  `unreifiable_function` and a `time_interval`, like `DatetimeFn`, and two
  `set/backwardRule`s give it its endpoints from the two `DatetimeFn` intervals, so with
  `:calendar` registered a depth-3 `query (startOf (DatetimeRangeFn "2000-01" "2000-06")
  ?i)` answers `(InstantFn 2000 1 1 0 0 0)` and `endOf` answers `(InstantFn 2000 7 1 0 0
  0)`. Calendar units nest or are disjoint, so this is the first term that names two
  stretches that partially overlap. Nothing reads its strings as fields, so neither the
  interval relations nor the context ordering compare a range the way they compare a
  calendar term. [time.md](docs/time.md#naming-an-interval-the-calendar-constructors)
  *Migration:* none.

- **The upper ontology ships `intangiblePartOf`, `tangiblePartOf`'s twin for things
  without mass.** It is transitive, reflexive and below `partOf`, and types both positions
  `intangible`. A mixed pair, such as a mind as part of a person, stays plain `partOf`.
  [glossary.md](docs/glossary.md)
  *Migration:* none.

- **CxTra ships `conceptual_work`, `carries`, `subInformationOf`, `agentClaims`,
  `dataContent` and `propositionalContent`.** `conceptual_work` is below `information`.
  `(carries ?carrier ?info)` types position 1 `temporal` and position 2 `information`, so
  a tangible paper copy and an intangible event, such as a bird's chirp, are both
  accepted, and one carrier holds more than one piece of information.
  `subInformationOf` specializes `intangiblePartOf` for a chapter in a book or a frame in
  a video. `(agentClaims ?agent (sentexHandle H))` says that `?agent` presents sentex `H`
  as true: position 1 is typed `thing`, position 2 is a sentex handle left untyped, the
  relation is a `target_following_predicate`, and no rule concludes it from `carries`.
  `(dataContent ?info ?string)` is functional over the exact symbol sequence `?info`
  holds. `(propositionalContent ?info ?proposition)` is not functional. No rule derives
  either content relation; both are stated directly. [contexts.md](docs/contexts.md)
  *Migration:* none.

- **`sentex_handle_term` names the expression `(sentexHandle N)`, N a positive integer.**
  `reflection.txt` places it below `non_atomic_term`, and `ExpressionKindProver` answers
  `(sentex_handle_term (Quote (sentexHandle 212)))` by the form's shape.
  [argtypes.md](docs/argtypes.md#what-a-quoted-form-is)
  *Migration:* none.

### Fix: answers

- **A compound `(rewriteOf T E)` resolves `E` to `T` only in the contexts that see the
  context it is stated in.** With `(rewriteOf Mary (MotherFn Muffet))` in `CxStory`,
  `(likes Tom (MotherFn Muffet))` asserted in a sibling `CxOther` or in `CxUniverse` was
  stored as `(likes Tom Mary)`, and `ask` of `(hates Tom (MotherFn Muffet))` in `CxOther`
  answered from a stored `(hates Tom Mary)`.
  [nat.md](docs/nat.md#a-nat-resolves-under-the-readers-merges)
  *Migration:* none.

- **A conclusion a forward rule derived through a `genl` edge stands where the edge's
  second supporter is believed, after a forced denial puts out the first, and only
  there.** With `(genl dog pet)` derived from `(srcRel dog pet)` and also stated by
  `(partition pet dog cat)`, a `:monotonic` `(not (srcRel dog pet))` put `(breathes
  Muffet)` out, though `(pet Muffet)` held. A rule over `(genl ?a pet)` concluded for
  `dog` in a context where an `except` hides the `partition`, and where a denial of the
  `partition`'s own premise puts it out; it now concludes in neither.
  [nmtms.md](docs/nmtms.md#where-the-layer-stops)
  *Migration:* none.

- **A computed literal runs once the inputs its prover reads are bound.** A
  result-binding evaluatable waited for its output to be bound, so a check reading that
  output ran first on written order: `(reachN ?x ?n) (sumOf ?m ?n 1) (chk ?m ?n)` never
  fired forward, and a `query` of the conjunction written in the other order answered
  nothing. The planner threads ready computed literals to a fixpoint, and an evaluatable's
  estimate reads its own bound inputs. [inference.md](docs/inference.md)
  *Migration:* none.

- **A `(reflexive P)` declaration answers `(P a a)` only for a term `P`'s argument
  declarations admit at both positions.** With `(arg sameRegionAs 1 region)` and `(person
  Ann)` beside `(disjoint person region)`, `ask?` of `(sameRegionAs Ann Ann)` answered
  true, and `(sameRegionAs Ann ?y)` bound `?y` to `Ann`. A term holding no type is still
  admitted. On a predicate a calculus answers, such as `subintervalOf`, the answer now
  agrees whether or not a rule concludes the predicate
  ([#232](https://github.com/vaelii/vaelii/issues/232)).
  [inference.md](docs/inference.md#the-pluggable-prover-engine-vaeliiimplprovers-ask)
  *Migration:* none.

- **`ArgTypeProver` types a term at a position an `argAndRest` declaration types.** A
  believed `(P … x …)` with `x` at position `n` or later beside `(argAndRest P n T)`
  answers `(T x)`, as `(arg P n T)` at `x`'s position does; `(args P T)` answers through
  the `argAndRest` twin its rule stores. The exception re-check that follows the inference
  reads the same declarations, in both arrival orders. [argtypes.md](docs/argtypes.md)
  *Migration:* none. Under the constraint-only reading, `ask` answers such a membership
  where it answered nothing.

- **A recursive rule fires when a registered evaluatable or a `SupportingProver`
  antecedent holds a variable only the recursive literal binds.** The join ran that
  antecedent before the recursive literal, on an open variable, and found nothing, while
  `query` of the same antecedents answered.
  [inference.md](docs/inference.md#conjunctive-query-planning-vaeliiimplplan)
  *Migration:* none.

- **A forward rule concluding `equals` or `sameAs` over applications of a
  `reifiable_function` that have no constant yet mints them and stores the equality**, as
  `assert` of the ground sentence does. The firing dropped it as `:not-well-formed`, and
  `check` of the ground sentence reported the same problem `assert` does not raise.
  [nat.md](docs/nat.md#derivation-path)
  *Migration:* none.

- **A goal holding a never-minted application inside another application answers
  nothing, except by identity and congruence**, as a goal holding it as an argument does.
  With `FooFn` a `reifiable_function` never minted on `(Xa Xb)`, `(different (BarFn (FooFn
  Xa Xb)) Zed)` answered `{}`, and `(genl (BarFn (FooFn Xa Xb)) ?y)` bound `?y` to `(BarFn
  nat/no-match)`. [nat.md](docs/nat.md#read-path)
  *Migration:* none.

- **A goal keeps a never-minted `Quote` or `Quasiquote` application as written** under a
  `(reifiable_function Quote)` declaration. `(different (Quote Bar) (Quote Baz))` holds for
  quotations stored only as a `modal_predicate`'s proposition, as the plugin's Cyc
  preamble stores them. [nat.md](docs/nat.md#read-path)
  *Migration:* none.

- **`settle-record-edits!` re-derives a firing whose `genl` or `genlCx` edge an
  `edit-records!` batch removed while a second route still licenses it.** With `(genlCx
  CxB CxA)` and a route `CxB → CxM → CxA`, a forward rule in `CxA` and `(p A)` in `CxB`,
  removing the direct edge through `edit-records!` left `(q A)` unbelieved in `CxB`, where
  `edit!` keeps it; a `genl` route behaved the same.
  [storage.md](docs/storage.md#editing-the-records-of-a-kb-without-belief)
  *Migration:* none.

- **`chain-report` counts a firing the forced-monotonic set holds void under `:void`, not
  under `:placed`**, and a rule whose every firing is void reads `:status :blocked`, where
  it read `:fires`. [exceptions.md](docs/exceptions.md)
  *Migration:* read `:void` beside `:placed` for the firings a rule made that support
  nothing.

- **A `predAllSpecified` or `predSpecifiedAll` slot typed by a tail declaration is
  audited.** A slot typed only by `argAndRest`, `args`, `argAndRestGenl` or `argsGenl`
  reported `{:status :gap :gap :missing-slot-typing}`; the audit derives its contract from
  those declarations as from `arg` and `genlArg`. [predall.md](docs/predall.md)
  *Migration:* none. A declaration that reported the gap reports `:audited`.

- **`kb-quality`'s `:clashes` judges a rule pair in each maximal common descendant of the
  two rules' contexts, and reports one entry per context the pair clashes in.** With the
  rules in `CxLeft` and `CxRight`, and `CxP` and `CxQ` each seeing both, a `(disjoint bird
  penguin)` in `CxP` dropped the pair, though nothing separates it in `CxQ`; it is now
  reported at `CxQ`. A pair clashing in both is two entries, one per context, and
  `:pair-count` counts entries. [integrity.md](docs/integrity.md#what-a-rule-clash-finding-means)
  *Migration:* none.

### Fix: order independence

- **A compound `(rewriteOf T E)` resolves a use of `E` written before the reader saw it.**
  With `(likes Tom (MotherFn Muffet))` stored over a minted constant, a later
  `(rewriteOf Mary (MotherFn Muffet))` in the same context, or a `genlCx` edge that puts
  the rewriteOf's context above the use's, left both `(likes Tom (MotherFn Muffet))` and
  `(likes Tom Mary)` unanswered there. Both now hold in every order of the use, the
  `rewriteOf` and the edge. [nat.md](docs/nat.md#a-nat-resolves-under-the-readers-merges)
  *Migration:* none.

- **Two compound `rewriteOf` targets for one expression leave the expression minted in
  every arrival order.** With `(rewriteOf Mary (MotherFn Muffet))` in `CxA` and `CxB` and
  `(rewriteOf Jane (MotherFn Muffet))` in `CxC`, a write in a context below all three
  stored `Mary` in some orders and minted a constant in others.
  [nat.md](docs/nat.md#the-corresponding-predicate)
  *Migration:* none.

- **A settle's re-chain runs under the write's `:max-depth`, `:max-term-depth` and
  `:max-derivations`.** A `genlCx` move's re-chain took the default bounds, so a fact
  asserted after the edge derived to the caller's `:max-term-depth` and the same edge
  asserted after the fact derived to the default, and `:max-derivations` refused one order
  and not the other. `assert-many`'s closing settle runs under the call's `:max-depth` and
  `:max-term-depth`. [inference.md](docs/inference.md)
  *Migration:* none.

- **A function application inside a `modal_predicate`'s proposition stays as written in
  a rule, a goal and a firing, so a derived belief and an asserted one match alike.** With
  `(functionCorrespondingPredicate FruitFn fruitOf)`, a firing stored `(believes Bob
  (likes Bob (FruitFn Pear)))` over the minted constant, and a rule or a goal over
  `(believes ?a (likes ?a (FruitFn ?t)))` was read through `fruitOf`, so neither matched
  the asserted `(believes Ann (likes Ann (FruitFn Apple)))`. With no correspondence the
  rule was held. A rule over a belief no longer matches a belief spelled with the
  application's value. [nat.md](docs/nat.md#a-rule-or-a-goal-that-names-an-open-application)
  *Migration:* none.

- **A forward rule's computed antecedent waits for its binders behind a literal the index
  counts at no rows.** A trigger binding a `commutativeInArgs` literal to the spelling the
  store does not hold had the computed antecedent asked with its variables open, and the
  firing arrived only if a full join ran after the trigger's facts: a rule reading
  `(segLen ?a ?b ?x)` concluded nothing when its trigger arrived last, and now concludes
  in every arrival order. [inference.md](docs/inference.md#conjunctive-query-planning-vaeliiimplplan)
  *Migration:* none.

- **A rule the argument-hold refresh releases fires at the releasing write over the facts
  stored while it was held.** Retracting `(disjoint a b)` released
  `(set/forwardRule (implies (p ?x) (q ?x)))` under `(arg p 1 a)` and `(arg q 1 b)`, but
  left `(q Foo)` underived over a `(p Foo)` stored before the retraction; `(p Foo)` stored
  after it derived `(q Foo)`. [nmtms.md](docs/nmtms.md#a-revived-datum-is-a-datum-the-agenda-has-not-seen)
  *Migration:* none.

- **A compound under `quotedArg` is held inert in every arrival order when the
  separation of the type from its kind is stated below the declaration's context.**
  `(holds (MsrFn 5))` in a context below `(quotedArg holds 1 qtype)`, with `(disjoint
  qtype non_atomic_expression)` stated beside the fact, was believed in four of the six
  orders of the three writes. [argtypes.md](docs/argtypes.md#what-a-quoted-form-is)
  *Migration:* none; a recover holds the facts.

- **A `genlCx` declaration derived again by a rule draws no `context` membership over a
  `genlCx` edge the structural producer computed.** A rule re-deriving `(arg genlCx 1
  context)` after the producer ordered two reified contexts stored `(context cx/…)` for
  both, which a KB where the rule fired first did not store.
  [argtypes.md](docs/argtypes.md#where-it-does-not-mint)
  *Migration:* none.

- **A `genlCx` move places a functional or `anti_symmetric` merge at the most general
  reader that gains the pair, in every arrival order.** A lower reader visited first kept a
  merge its upper reader then placed again, and a merge stored at a reader before a more
  general reader placed it stayed, so an `except` of the general merge left the pair
  merged below it in that order only. The settle drops each copy a more general merge
  covers, with its restated twins. [equality.md](docs/equality.md)
  *Migration:* none.

### Fix: koinii

- **`identity/load-registry` and `speech-acts/load-speech-acts` load the CxDisputes seed**,
  so a context that sees CxDisputes reads the dispute marks' declarations before the first
  mark. A mark into a KB that ran neither loader still loads the seed first.
  [koinii.md](docs/koinii.md)
  *Migration:* none.

### Fix: storage

- **A retraction keeps an inert sentex a derivation had reached.** With `(set/inert (p
  Tom))` stored and a forward rule concluding `(p Tom)` from `(q Tom)`, retracting `(q
  Tom)` deleted the inert record. The same held for a `decontextualized_predicate` lift:
  asserting `(inverse westOf eastOf)` in a context below CxUniverse and retracting it
  deleted `space.txt`'s inert `(inverse eastOf westOf)`. The record now stays stored and
  inert. [solving.md](docs/solving.md#the-inert-fact-primitive)
  *Migration:* none.

- **After `reindex` or `import!`, a fact withdraws the conclusion of a rule or
  `exceptWhen` whose condition reads the taxonomy, as it does after `assert`.** With
  `(closed_extent_predicate month)`, a rule concluding from `(not (month ?m))` kept its
  conclusion for `Smarch` after `(month Smarch)` arrived; an `(unknown (not (cat ?x)))`
  beside `(disjoint cat dog)` survived `(dog Rex)`, and an `(unknown (not (admires ?x
  Bob)))` beside `(negates scorns admires)` survived `(scorns Ann Bob)`. A rebuilt or
  imported index posts each stored rule and `exceptWhen` under the re-check keys a write
  posts. [exceptions.md](docs/exceptions.md)
  *Migration:* run `reindex` over a KB whose index `reindex` or `import!` built.

- **A failed browser backup deletes only its own directory.** Its cleanup followed a
  symbolic link the store's clone kept, and deleted the contents of the directory the
  link named, outside the backup. The cleanup now deletes the link and leaves the
  directory it names.
  [web.md](docs/web.md#backing-up-a-store-kept-in-postgres)
  *Migration:* none.

- **An `:oplog?` open rebuilds instead of restoring the images when another writer moved
  the records, with or without frames a crash left to replay.** A second `:pg` KB over the
  same schema retracting a fact left the seal in place, and the restore answered
  `:restored true` believing the retracted handle; a re-assert of the sentence answered
  that handle and stored nothing. A dropped premise mark was believed the same way. A
  records fingerprint that differs from the seal's declines the restore as
  `:records-moved`. [storage.md](docs/storage.md#the-operation-log)
  *Migration:* none.

- **An `:oplog?` log's unusable mark and a retired seal survive a machine crash.** After
  `clear!`, `import!` or `edit-records!` under `:tick`, a crash that kept the records'
  deletes and lost the log's tail let the next open restore the images of the records as
  they were before the operation. A write by a KB opened without `:oplog?` over a sealed
  directory retired the seal in a way a power loss could undo, and the next `:oplog?` open
  restored images that did not hold the write; the write now retires it durably.
  [storage.md](docs/storage.md#the-operation-log)
  *Migration:* none.

- **A recover makes no network node for an `assert-inert` record**, as `assert-inert`
  makes none. `export-text!` after a reopen that recovered writes each such record as
  `(set/inert S)`, where it wrote none of them, and the first `lein cli upgrade --verify` of
  a freshly built `:disk-snapshot` store reads `:labels :same`, where it read `:differs`.
  [storage.md](docs/storage.md)
  *Migration:* none.

- **Two browser backups of one store taken in the same second write two directories.**
  A second backup that failed deleted the first backup's directory, and one that
  succeeded wrote its clone into the first one's `store/` and replaced its
  `records.dump`. The second backup's directory ends `-2`, and the job's progress names
  the directory the backup wrote.
  [web.md](docs/web.md#backing-up-a-store-kept-in-postgres)
  *Migration:* none.

- **`edit-records!` counts a nil removal under `:absent`.** `handle-of` answers nil on a
  KB whose index is not built (`:no-index`), and a removal of that nil left the batch
  answering `{:removed 0 :absent 0}`. The record-edit example in storage.md opens
  `:disk-log`, whose index `handle-of` reads without a rebuild; it named `:disk`, which
  `open-kb` refuses.
  [storage.md](docs/storage.md#editing-the-records-of-a-kb-without-belief)
  *Migration:* none.

### Fix: performance

- **A `genlCx` edge costs what it makes visible, not what the lower context or the rest of
  the KB holds.** Adding `(genlCx CxData CxWorld)` and `(genlCx CxWell CxData)` over two
  near-empty contexts made the settle re-read every fact, mint and constrained tuple CxWell
  sees, past ten minutes on a large store. A move now groups the readers under its `sub` by
  the contexts each sees through the moved edges alone, and when such a gain states facts
  alone the merge, argument-type, mint-withdrawal and argument-hold sweeps read what the
  gain's facts meet; a placement is re-read only where a more general one can now displace
  it. The edge also read every standing merge and every displaced fact in the KB, and
  re-derived the functional merges over every fact its `super` already saw: one edge took
  10.5 ms beside 1,600 `sameAs` merges stated in contexts it does not reach, against 2.4 ms
  beside 100, and now takes about 1 ms at both. Answers are those of the whole sweep. A
  shutdown also stops a write between the rows a move runs, and a long move logs progress.
  [contexts.md](docs/contexts.md#one-context-move),
  [equality.md](docs/equality.md#a-late-genlcx-edge-is-a-third-arrival-order)
  *Migration:* none.

- **A backward `prove` down a derivation chain costs the same per link at any depth.** A
  `prove` of the end of a 4,000-link chain took 60 s and grew about as n^2.2; it takes 1.9
  s, and 10,000 links take 4.7 s. A rule instance renamed apart on a path is spelled `?v'N`
  where it was spelled `?v` and one `'` per earlier renaming. Answers are unchanged
  (`lein perf`'s `prove-down-a-derivation-chain`).
  [inference.md](docs/inference.md#each-rule-instance-gets-its-own-variables)
  *Migration:* none.

- **An in-session `recover` costs the store it replays, not the square of a chain's
  depth.** A premise re-marked at the strength the network holds relabels nothing, so a
  `recover` over a KB holding a 10,000-link derivation chain takes 0.75 s where it took 31
  s, and re-asserting a stored fact no longer relabels what it supports. Labels are
  unchanged (`lein perf`'s `recover-over-a-derivation-chain`).
  [nmtms.md](docs/nmtms.md#2-locality)
  *Migration:* none.

- **A recover's membership placement reads each context set once a pass, not once a
  route.** The maximal common descendants a placed nogood reads, a reader's scope, a
  declaration's believed supporters and whether an except reaches a handle are held for the
  placement pass. A recover over 1,024 terms, each placing a nogood over nine routes with
  1,024 contexts below each of its members' contexts, took 4.5 ms a term against 1.1 ms at
  128, and takes about 0.5 ms at both. Placements are unchanged
  (`placed-nogood-test`'s `a-reading-pass-places-each-membership-nogood-as-a-fresh-read-does`).
  [nmtms.md](docs/nmtms.md#the-placement-pass)
  *Migration:* none.

- **The taxonomy's closure cache is bounded by the taxonomy's size**, at 256 terms per
  `genl` and `genlCx` node, at least 65,536 and at most one term per 256 bytes of heap. Its
  bound was at least 50 million terms, so a small KB never evicted the closures an edge
  change retired: loading the starter ontology into a memory KB held 31.6 MB, and now
  holds 20.5 MB. The `:taxonomy-closures` row of `caches` reports the KB's own bound.
  [taxonomy.md](docs/taxonomy.md)
  *Migration:* none.

- **A settled browser job holds no reference to the KB it wrote.** A chain or edit job's
  report stays listed for up to an hour, and it kept that KB reachable for as long, after
  the KB was closed or replaced. [web.md](docs/web.md#long-work-as-jobs)
  *Migration:* none.

- **A settle that queued many `genl` edges into a broad type re-checks the preserved
  firings once a pass, not once an edge.** With a predicate declared `(transitive P)` and
  preserved along `genl`, each edge's exception re-check read the type's whole joint reach
  (every term of its closure, and a `P` literal of each) under a memo of its own, copied
  it into a fresh set, and read each literal's whole fan of sub-predicates. The markers of
  a pass now share one memo, the goal test is a membership over the reaches it holds, and
  the walk cuts each literal's fan by the slot predicate sets whatever its size, so a term
  no fact of `P` names costs two slot reads. A batch of 16 edges into a type of
  4,096 specs takes 0.19 s where it took 21.5. The firings re-decided are the same.
  [inherit.md](docs/inherit.md#what-one-question-costs)
  *Migration:* none.

- **The settle's subsumed-mint withdrawal and its membership placement pass read their
  records a round trip a chunk.** Each candidate mint and the memberships or edges that
  could subsume it, and each nogood's members, placed `contradicts` and `defeat`s and their
  justifications' antecedents, were fetched a record at a time, so over a Postgres store
  whose fetch cache holds a fraction of the records a `recover`, or a settle that placed
  the nogoods again, spent its time in point reads. Both now hint the store 256 candidates
  or terms at a time. Over a 2,048-record cache, a recover of 2,000 mints made 3,396 point
  reads in the withdrawal and now makes 119, and 2,000 nogoods placed again made 12,001
  point reads and now make 1. The withdrawals and the placements are the same.
  [argtypes.md](docs/argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on),
  [nmtms.md](docs/nmtms.md#the-placement-pass)
  *Migration:* none.

- **A write no longer walks every placed defeat's consequences again.** Whether a `genl`
  supporter rests on a target of the stored excepts and placed defeats is read at the
  first scoped `genl?` or `genls` after each write, and with the defeats no more than the
  supporters it walked forward from every target over the justifications resting on it,
  a supporter probe a handle: 0.4 to 0.8 s per mint over a large store, so
  `record-arg-types!` set each `causes` fact aside past its budget. A walk that meets no
  supporter is now held across writes, and the next read walks on from the handles the
  writes since touched; a stored `except`, `defeat` or rule reads it whole again. Per fact
  of `lein perf`'s `record-pass-beside-defeated-chains` at 4,096 defeats, 0.40 ms where
  the fresh walk took 90.5. A walk that meets a supporter
  is held as the path it met it by, and the next read checks that path: per fact of
  `record-pass-beside-a-reached-supporter` at 4,096 defeats, 0.61 ms where the walk
  to the supporter took 80.2. The read walk also no longer
  reads the record of a support handle that holds no `nogood` justification to ask
  whether a placement there is exempt. The answers are the same.
  *Migration:* none.

- **An open negative fetches the denials it reads and none of the positive facts beside
  them.** The argument roots and the predicate extent hold both polarities, and
  `(not (unary_predicate ?w))` fetched every positive member to drop it on polarity, a
  probe each minted `type` paid twice through its
  cover arm's denial of `empty` and `nonempty`, so `record-arg-types` wrote one `causes`
  fact a minute. With no denial stored in the contexts read the candidates are none, and
  otherwise the positives are taken out by their stored shape before a fetch; the
  answers are the same. [profile.md](docs/profile.md#the-access-paths-named)
  *Migration:* none.

- **The argument-type pass asks no checks of a mint the fact would leave as it is.**
  `record-arg-types` and `record-arg-types!` pass over an entailment whose mint is stored
  with the fact's support, or still withheld, before its admission checks, as the
  release of withheld mints does (`unchanged-mint?`): over a store whose mints were drawn,
  0.025 ms a fact where asking the checks cost 1.0 (`lein perf`'s
  `record-pass-over-recorded-facts`). Such a mint is no longer asked, so a
  violation of one already stored is no longer reported again.
  [argtypes.md](docs/argtypes.md#the-pass-over-a-stored-kb)
  *Migration:* none.

- **A `record-arg-types` pass whose facts each write a fresh mint proves a cover's parts
  only when the cover could refuse the mint, and asks each mint's admission checks once
  between writes.** The cover arm proved every part of every cover over the mint's type,
  and the inheritance prover read each part's extent to deny it; it now reads the stated
  denials first. `lein perf`'s `record-pass-mints-beside-an-inherited-extent` reads 1.46x
  against 4.78x, and the admission asks of the facts naming one term are counted by
  `argtype_entail_test`'s `a-record-pass-asks-each-terms-admission-once-between-writes`.
  [argtypes.md](docs/argtypes.md)
  *Migration:* none.

- **A losing write reads the forced-monotonic predicates' counts once across writes, not
  once per write.** The answer is held in the taxonomy's closure memo while the
  forced-monotonic sets stand, and a write since asks only the functors it stored: whole
  reads per losing write fall from 1.0 to 0.0033. [exceptions.md](docs/exceptions.md)
  *Migration:* none.

- **A `genl` edge, a `SupportingProver` datum and a `genlCx` move read the rule-key set
  from the smaller side.** The subsumption seeds, the computed re-join and the move seeds
  read the whole antecedent-key set, which the columnar index decodes on every read, once
  per edge, datum or move; each now tests membership per key it asks or meets the keys
  with its own fan, and a move from a context storing nothing reads no key.
  [indexing.md](docs/indexing.md)
  *Migration:* none.

- **`kb-integrity`'s rule-macro findings read the rules in the audit context's `genlCx`
  ancestor set**, not every rule the KB holds. [integrity.md](docs/integrity.md)
  *Migration:* none.

- **A symmetric goal reads the store once where every predicate it fans over is
  symmetric.** A ground `(orthogonal a b)` made two uncached reads and now makes one, with
  the same answers; the disjointness audit's per-pair call takes 0.86 of its time.
  [inference.md](docs/inference.md#the-pluggable-prover-engine-vaeliiimplprovers-ask)
  *Migration:* none.

- **A forward rule's registered evaluatable or `SupportingProver` antecedent runs once
  the join has bound its variables, ahead of the antecedents expected to multiply the
  rows.** The join ran it after every stored antecedent: a check over two `memberOf`
  literals ahead of a literal that multiplies their rows by five was asked 125 times, and
  is now asked 25 times, with the same conclusions.
  [inference.md](docs/inference.md#conjunctive-query-planning-vaeliiimplplan)
  *Migration:* none.

- **A merge re-decides the `different` guard only on the firings naming a term of the
  merged class, and joins the rule nowhere.** Two merges beside a rule with eight firings
  joined it over all eight rows and asked the guard 27 times; they now join no row and ask
  it at most four times, with the same conclusions.
  [exceptions.md](docs/exceptions.md#five-channels-a-declaration-or-a-fact-reaches-an-exception-through-sideways)
  *Migration:* none.

- **A datum on a `SupportingProver`'s source re-joins a rule over the rows resting on
  it.** Five ranks asserted one at a time beside a rule reading a ranking prover joined
  20 rows for 10 firings, and now join 10; a forward chain over the five, stored
  unchained, re-joined the rule five times and now re-joins it once.
  [inference.md](docs/inference.md#what-a-computed-answer-rests-on)
  *Migration:* none.

### Fix: inference

- **A firing's mint is chained by the run that fired it, so `:max-derivations` and a
  caller's bound reach every firing it leads to.** Each of the mint's asserts chained
  from its seeds in a run of its own inside the firing, one run deeper per mint along a
  chain of mints, and each run counted its own `:max-derivations`. The run now takes the
  seeds onto its agenda and counts them against `:max-derivations`. With `(result SuccFn
  num)`, `(num (SuccFn ?x))` from `(num Zero)` restarts at depth 1 on every mint, so
  `:max-depth` never ends it either: the write overflowed the stack and was undone. It
  now ends at `:max-derivations`, where the write is refused `:interrupted` and rolled
  back, and `chain-stats` counts one run per write.
  [inference.md](docs/inference.md#forward-chaining)
  *Migration:* none.
- **A believed `inverse` between two predicates of one calculus leaves its prover
  answering alone.** `(inverse partOfRegion hasRegionPart)`, believed, sent every
  `partOfRegion` goal to the union of every applicable prover. The calculus reads both
  predicates and applies its converse table, so the prover now answers alone when that
  table implies the pair. An `inverse` naming a predicate outside the calculus still
  takes the union.
  [qcn.md](docs/qcn.md#support-what-an-entailed-relation-rests-on)
  *Migration:* none.

- **A goal whose predicate a stored rule concludes at arguments the goal cannot unify
  with is answered by its prover alone.** The `:rules` channel opened for any goal whose
  predicate or a spec of it some rule concludes, so such a goal went down the union path
  although no rule could answer it. [inference.md](docs/inference.md)
  *Migration:* none.

### Fix: refusals

- **A `quotedArg` whose type is a kind of `expression` decides a value or a symbol.** Every
  value kind and `symbol` sit in the expression lattice, so `(quotedArg P n
  non_atomic_term)` refuses `(P 212)` and `(P Muffet)`, where it read the type
  open-world and admitted both. A compound stays exempt, as for every declared type.
  `(quotedArgAndRest P n T)` is the tail form of `quotedArg`, as `argAndRest` is of
  `arg`. [argtypes.md](docs/argtypes.md#what-a-quoted-form-is)
  *Migration:* a value or a symbol stored where a `quotedArg` names a kind of expression
  it is not of is now refused at assert.

- **`assert` stores a sentence naming an application of a `reifiable_function` whose
  `result` is a unary class.** With `(result ColorPropertyFn unary_predicate)`,
  `(likesProperty Tom (ColorPropertyFn Red))` threw `:length-against-spelling`, since the
  mint's `(unary_predicate nat/K)` read the minted name as camelCase. A `nat/` or `cx/`
  constant is held to no length by its spelling.
  [naming.md](docs/naming.md#a-length-binding-is-held-to-the-spelling)
  *Migration:* none.

- **`assert` stores `commutative`, `commutativeInArgAndRest` and `commutativeInArgs` of a
  function spelled `…Fn`, in either order with its function declaration.**
  `(commutative RulePairFn)` threw `:not-well-formed`, "RulePairFn is an individual",
  since the relation slot read every CapitalCamelCase name as an individual. A name ending
  in `Fn` is a function by spelling; `genl`, `symmetric` and the other predicate and type
  positions still refuse it
  ([#227](https://github.com/vaelii/vaelii/issues/227)).
  [taxonomy.md](docs/taxonomy.md#well-formedness-vaeliiimplwff)
  *Migration:* none.

- **`try-assert` refuses a clash that a `genl` edge stated below the writer's context forms,
  in either order.** With `(genl likesPet likesDog)` stated in a context below, `try-assert`
  stored `(arg likesDog 2 dog)` over a breaking `likesPet` tuple there, `(irreflexive
  likesDog)` over a `likesPet` self tuple, and a `likesPet` tuple under a declaration on
  `likesDog` stated beside the edge. Beside `(implies (likesPet ?x ?y) (likesCat ?x ?y))`
  in that context, with `likesCat`'s position 2 declared `cat` and the two types disjoint,
  it stored `(arg likesDog 2 dog)`. The reverse order refuses each. `assert` stores each
  as it did, and belief does not change.
  [api.md](docs/api.md#refusing-a-clash)
  *Migration:* none.

- **`try-assert` stores a length binding over tuples it breaks that are stored and not
  believed.** With `(likes Ann Bob Cy)` defeated by a `:monotonic` denial, `try-assert`
  of `(binary_predicate likes)` threw `:violation :arity` counting the defeated tuple. The
  `:arity` refusal of a binding, a `genl` edge or a metatype route counts believed tuples
  only, and `:detail :shapes` gives each length's believed count.
  [api.md](docs/api.md#refusing-a-clash)
  *Migration:* none.

### Fix: shipped ontology

- **The starter types the argument positions its terms' own definitions fix.**
  `DayFn`, `MonthFn` and `YearFn` take their corresponding predicates' field types
  (`integer`, then `positive_integer`), `QuantityFn` and `QuantityIntervalFn` take
  `number` and `unit_of_measure`, and `FatherFn` and `MotherFn` take an `animal`. The
  Exists cells' subject, filler and placeholder positions declare `thing`, `greaterThan`
  and `lessThan` type their whole chain `number`, `not` and the bodies of `forall`,
  `thereExists` and `exists` declare `formula`. Under assertive argument types, a symbol
  written in one of these positions now derives the declared membership: `(QuantityFn 5
  Furlong)` derives `(unit_of_measure Furlong)`. A value of the wrong kind there is
  refused. The binder of `forall`, `thereExists` and `exists` is a `(quotedArg Q 1
  open_expression)`. The five aggregation operators type their result, value and body:
  `agg/count`'s result is a `non_negative_integer`, and the other four's result and every
  value are a `thing`. `except`'s one position, `exceptWhen`'s rule and every member of
  `contradicts` are a `sentex_handle_term` taken as written, and `exceptWhen`'s query is a
  `formula`. [integrity.md](docs/integrity.md#what-a-missing-arg-finding-means)
  *Migration:* an `(except 212)`, an `(except Muffet)` or a `(contradicts 212)` asserted by
  hand is now refused; write `(except (sentexHandle 212))`.

- **`information_bearing_thing` renames to `information`.** CxTra declares
  `information` with the same comment, examples and `genl` edges to `intangible` and
  `acausal`, and `digital_artifact` sits below it. [contexts.md](docs/contexts.md)
  *Migration:* rename `information_bearing_thing` to `information` in any KB text that
  names it.
  *Breaks:* `information_bearing_thing`

- **The starter passes the default `kb-integrity` sweep from every middle context.**
  `CxMereology` states `(transitiveInArgInverse locatedIn 1 tangiblePartOf)` and
  `(transitiveInArgInverse owns 2 tangiblePartOf)` where it held two forward rules of that
  shape, so a part's location and ownership are answered at query time and stored nowhere;
  a reader that sees the whole's fact and the parthood fact answers, wherever each is
  stored. `CxBiology` records `(declined_rule_macro (genl organism mortal))` beside the
  `mortal` default, which stays a default. `arity_type`, `spatiality_type` and
  `temporality_type` are placed under `unary_predicate`, `origin_type` under `type` and
  `except` under `non_atomic_term`, so `kb-integrity` reports none of them as
  `:not-under-thing`.
  [inherit.md](docs/inherit.md), [integrity.md](docs/integrity.md#what-a-rule-macro-finding-means)
  *Migration:* a caller that read a part's derived `locatedIn` or `owns` with
  `sentexes-matching` asks it with `ask?`, or asserts the forward rule in its own context.

- **`termsRelated` clusters vocabulary names by mention, as `seeAlso` cross-references
  them.** `(quotedArgAndRest termsRelated 1 denotational_term)` types the start of its
  variable-arity tail and every later position the same way, the suffix form of the
  `(quotedArg seeAlso 1 denotational_term)` / `(quotedArg seeAlso 2 denotational_term)`
  pair. The named terms can be of any kind — the grouping is for a reader, not an
  inference — so a symbol the KB says nothing else about is still accepted, taken as
  written. [argtypes.md](docs/argtypes.md#what-a-quoted-form-is)
  *Migration:* none.

### Fix: introspection

- **`preview` of a batch removes what the batch derives above its mark.** Previewing a
  forward rule over a stored backward rule left the forward run's conclusions stored after
  the rollback. [preview.md](docs/preview.md#what-the-rollback-restores-and-what-it-does-not)
  *Migration:* none.

- **`preview` of removing an `except` reports the conclusions the removal releases.**
  The preview's suspension of the `except` queued no re-join of the firings it refused, so
  `(preview kb {:remove [h]})` reported none of the conclusions `retract!` of `h` derives.
  The preview now reports them, and its rollback refuses those firings again.
  [preview.md](docs/preview.md#the-mechanism)
  *Migration:* none.

- **`why-not`'s `{:nearest n}` reports as satisfied only antecedents that hold under one
  binding.** With `(livesIn ?a ?t)`, `(coastal_town ?t)` and `(ferryTo Dover ?t)` as a
  rule's body, each holding for a different `?t`, `why-not` of the conclusion listed all
  three under `:satisfied` and `:missing []`; one of them is now under `:missing`.
  [api.md](docs/api.md#three-reads-for-a-reader-rather-than-a-program)
  *Migration:* none.

- **`kb-integrity`'s `:missing-arg` reads a relation's declarations from the contexts that
  state them.** The engine places an exact-arity class in CxUniverse, and the starter's
  unary batch writes `unary_predicate` there, while a middle context's declarations stay in
  that context. The audit from CxUniverse reported those relations' typed positions as
  missing. It now also reads each context that sees the audit context and stores an
  `arg`-family declaration on the relation or a `genl` edge out of it, and reports a
  position only if one of those leaves it untyped too. At CxUniverse over the starter it
  reports 3 findings, where it reported 80: the example predicates' quoted sentence.
  [integrity.md](docs/integrity.md#what-a-missing-arg-finding-means)
  *Migration:* none.

### Fix: browser

- **A browser backup copies the store directory on Linux.** It ran `cp -cR`, whose `-c`
  only macOS's `cp` takes, so every backup on Linux failed `:backup-failed`; it clones
  with `cp -cR` on macOS and copies with `cp -R` elsewhere, and `backup.edn`'s restore
  step names the same command. [web.md](docs/web.md)
  *Migration:* none.

- **Each KB's `/removed` list holds only that KB's removals.** KBs named `a/b` and `a_b`,
  names differing only in case, two catalog entries of one name, and every KB no catalog
  entry holds each shared one list and one cap of 50, and **Put back** asserted another
  KB's removal into the KB on screen. [web.md](docs/web.md#editing-sentexes)
  *Migration:* a list noted before this release is no longer shown; its file under
  `~/.vaelii/removed/` can be deleted.

### Internal

- **koinii.md carries a whole koinii session that `doc_examples_test` runs**: two agents
  and an arbiter join one channel, assert, endorse, ask and answer, dispute, rule, and
  retract the ruling to reopen the dispute, each step checked by a `;=>` value.
  [koinii.md](docs/koinii.md#a-session-start-to-finish)

- **koinii.md maps each `CxSpeechActs` act to its KQML / FIPA-ACL performative and
  dialogue move**, states the commitment the stored act records, and cites the sources.
  [koinii.md](docs/koinii.md#lineage-acl-performatives-and-social-commitments)

- **`lein perf`'s `:settle` group holds each phase of `settle-record-edits!` per unit to
  a growth ratio and to its share of an hour**, read in the calling thread's CPU time,
  with `VAELII_SETTLE_HOUR` and `VAELII_SETTLE_REMOVE` as its switches; a check over its
  share is marked `:budget-unmet` and does not fail the run.

- **A `^:red` test asserts behaviour not built yet**, and only `lein test :red <ns>` runs
  it: `:default`, `:slow` and `:all` exclude the mark. CONTRIBUTING §5 lists it beside
  the other four marks.

- **Lint's E21 holds each `handbook/` clojure block to the API and the shipped KB**: a
  `v/` call names a var `vaelii.core` defines, and every other block's forms appear in
  `resources/kb/` or the test-world files. The orientation, var, path, link and
  s-expression checks read `handbook/` as they read `docs/`.

- **`lein test-parallel` starts at least `TEST_MIN_JOBS` (3) shards** when no count is
  named, the run locks take and restore with a noclobber create (Android refuses
  `link(2)`), and `ALLOW_WORKTREE_RUN` accepts only `release`.

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
