# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.31.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

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
- **A second disk open naming neither `:dir` nor `:space` logs the default-space
  warning.** The warning fired for in-RAM records only; two such disk opens share
  `space-0` under the default directory the same way.
  [storage.md](docs/storage.md#opening-a-kb)

### Fix: browser

- **The Postgres backup page reads a snapshot store's `records.edn` with `clojure.edn`.**
  It read the file with `clojure.core/read-string`, the one reader of a store file not
  held to the EDN reader.
  [web.md](docs/web.md#backing-up-a-store-kept-in-postgres)

## 0.31.0 — 2026-10-30 — "Separations that lose to a stronger denial, lazy-forward rules and a computed `nonempty`, forks that pull a newer base and merge peers' deltas, content digests across seats, `CxTimeFn` slices ordered across monads"

| Area | Change |
|---|---|
| inference | a separation keeps its written strength and loses to a stronger denial; `argue` answers `:false` for a placed nogood's loser; a minted type justified under a stored inert rule; `set/lazyForwardRule`, with `core.txt`'s arity converse one; `(nonempty C)` computed from a believed member; `try-assert` refuses a write that makes a calculus network unsatisfiable; the reification marks forced-monotonic; no `arg` declaration on a unary predicate; a decided nogood as a defeat report; `argue`'s `:supports` |
| contexts and time | `CxTimeFn` slices ordered when they differ in both arguments and over a `genlCx` path between monads; `monad_context` derived |
| storage | a store records its reasoner set and refuses `:reasoner-mismatch`; a handle at a reference position exported as `(ist Cx S)`; a target-following meta names a sentence by content; `import!`'s `:rebase?`; `export-text!`'s `:delta?` and `load-text!`'s `:merge?`; a sentex's content digest; `:lock-unsupported`; manifests written by rename |
| koinii | a dispute id is the sorted content digests of its sides; `->SentexRef`, `locator-index` and `resolve-by-locator` gone; `pull!` rebases a seat's fork; a mesh of peer seats |
| daemon and change feed | the start scripts take the heap from physical memory; `:digests?` on a reply; `watch` refuses a calculus predicate; a feed event's `:defeats` and `:unsatisfiable`; `.stop` removes a server's feed listeners; `*print-length*` elides nothing written |
| upgrades | `resources/renames/<version>.edn`; `upgrade --sync` rewrites and reports what a release renames; lint's E22 |
| integrity | `kb-integrity`'s `:undeclared-term`, `:open-sibling-pair` and `:undecided-relation-property`; `acknowledgedFinding` on a `:derivable-stated-edge` |
| shipped ontology | a stated membership of every constant the upper files use; `syncategorematic`; `birthDate`; `CxKinship`'s `genlInverse` edges; `measure.txt`'s rows `set/monotonic` |
| answers and rule checks | an open query answers a part's location and ownership; a negated antecedent reads a separation's denial; measures compare in one base unit; `args` and `argAndRest` constrain a rule's variables; a rule reading `different` beside the starter stored |
| performance | a KB with reasoners keeps a reasoning image; a write keeps each context's reader frame; a settle that stores defeats costs the support it reads; a defeat cycle's read reads each defeat once; `edit!` reads one stratification graph per batch |
| browser | a term page's definitional block; `/quality` renders `kb-quality` |

Fourteen entries are **Breaking** and three are **Refusals**. Each carries its own
`*Migration:*` line, and the table indexes them by what a 0.30.0 caller changes.

| If your code… | Then |
|---|---|
| relies on a denial of a separation losing, or on a `disjoint` between `genl`-related types being a hard clash | state the separation `:monotonic` where it must hold against every denial |
| reads `argue`'s `:unknown` for the loser of a definitional clash | read `:defeated-by` to tell a defeat from a stated denial |
| reads a minted type's `:informant` as a symbol, or counts a KB's sentexes | read the informant as a rule handle; a durable index at layout 16 rebuilds at the first open |
| reads the shipped arity converse as backward, or a rule's `:engines` | read `:lazy` among a rule's `:engines` |
| reads `(nonempty C)` as a stated fact | read a stated one with `sentexes-matching`; `ask` answers the computed one too |
| reads two `CxTimeFn` slices differing in both arguments as unordered | nothing: `sees?` and visibility answer the ordering |
| calls `try-assert` with a calculus fact that contradicts the stored network | pass `{:refuse-unsatisfiable? false}` to store it |
| denies a reification mark, or relies on a defeat between two marks | retract the mark, and retract one of two clashing marks |
| declares `arg` of a unary predicate | drop the declaration and state the type as a `genl` edge |
| opens a store `add-reasoner` was called on, or imports its dump | pass `:reasoners` or `{:reasoners :stored}` |
| reads `export-text!`'s `:skipped`, or writes `(except S)` meaning the sentence | load the file with this build's `load-text!`; write `(except (sentexHandle H))` to except by handle |
| calls `dispute-id` with one argument, or holds rulings under handle ids | call `(dispute-id kb entry)`, retract the stored marks and rule again |
| calls `vaelii.koinii.deref/->SentexRef` | call `locate` or `vaelii.core/digest` |
| calls `resolve-by-locator` or `locator-index` | send the `marker` and call `dereference` |
| watches a calculus predicate | watch the whole feed and read the relation with `query` or `qualitative-network` |
| relies on the start scripts' `40g` default, or sets `VAELII_HEAP` above physical memory | set `VAELII_HEAP` for the store's recover, within physical memory |
| asserts a target-following meta before the sentence it names | assert the sentence first; `load-text!` asserts a file's reference declarations first and retries a refused meta |

### Breaking: inference

- **A separation keeps its written strength and loses to a stronger denial.** `disjoint`,
  `covering`, `partition`, `sibling_disjoint` and `siblingDisjointException` leave the
  forced-monotonic set; `orthogonal` and the arity bindings stay in it. A `:monotonic`
  `(not (disjoint animal vehicle))` stated in a context defeats a `:default` `(disjoint
  animal vehicle)` there and below, and the memberships it separated clash with nothing
  there, where the denial lost at either strength. A `:monotonic` copy of the declaration
  stays believed wherever it is visible. A `disjoint` over two `genl`-related types is a
  nogood of the declaration and the edges of each route between them, where it was a
  one-member hard clash of the declaration, so a `:default` edge loses to a `:monotonic`
  declaration. The part edges a `:default` `covering` installs are `:default`, so a
  separation's denial no longer climbs through them.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-set)
  *Migration:* state `:monotonic` a separation that must hold against every denial, as
  `CxRealWorld` states `(disjoint animal vehicle)`.
  *Breaks:* belief, `conflicts` and `contradictions` under a denial of a separation, over
  a `disjoint` between `genl`-related types, and through a `:default` `covering`'s part
  edges
- **`argue` answers `:false` for a stored sentence a placed nogood defeats.** A
  `:default` `(ageOf Tom 3)` beside a `:monotonic` `(ageOf Tom 4)` under `(functional
  ageOf)` read `:unknown`, since no `(not (ageOf Tom 3))` is provable; it reads `:false`,
  with the defeat reports under `:defeated-by`. A context above the nogood's placement
  still reads the loser `:true`.
  [nmtms.md](docs/nmtms.md#observation-beats-expectation)
  *Migration:* read `:defeated-by` to tell a defeat from a stated denial.
  *Breaks:* `argue`'s `:verdict` for the loser of a disjointness, functionality or other
  definitional clash
- **A minted argument type is justified under a stored inert rule.** Each argument
  declaration kind's entailment is a `set/inertRule` in CxUniverse, which `core.txt`
  states and a KB without it stores with its first declaration of that kind. A mint's
  justification names the rule's handle as its informant, beside the fact and the
  declaration, so `why` of a minted type shows the rule where it showed the declaring
  predicate's symbol. `retract!` and `edit!` refuse to remove one of these rules as
  `:mint-rule`. The starter stores eleven more sentexes. A stored rule whose consequent
  functor is a variable is checked for stratification as the stored graph reads it, so an
  inert one concludes nothing there. The rules' handles are an index family,
  `[:mint-rules]`, at index layout 17.
  [argtypes.md](docs/argtypes.md#the-entailment-as-a-justified-datum),
  [indexing.md](docs/indexing.md#10-the-mint-family)
  *Migration:* read a mint's informant as a rule handle; a store written earlier keeps its
  symbol informants, which still read as mints. A durable index at layout 16 is rebuilt
  from its records at the first open.
  *Breaks:* `why` and `supporting-justifications` `:informant` of a minted type; sentex
  counts of a KB that mints; `retract!` of one of the eleven rules
- **A forward rule reads what a lazy-forward rule concludes, and the arity converse is
  one.** `set/lazyForwardRule` (`{:direction :lazy-forward}`) stores a rule with engines
  `#{:backward :lazy}`, which backchains and fires on no datum. A forward rule's antecedent
  on the functor it concludes is proved inside the join, and the firing rests on the lazy
  rule and the facts that join read. `core.txt`'s `(T ?r) ⇒ (arity ?r n)` converse is
  lazy-forward, so a forward rule guarded on `(arity ?r ?n)` fires for a relation its
  exact-arity class declares. Inside `with-deferred-settle`, the re-joins those readers owe
  run once, at the batch's settle. `edit-records!` refuses a direction onto or off
  `:lazy-forward`.
  [inference.md](docs/inference.md#a-lazy-forward-rule)
  ([#226](https://github.com/vaelii/vaelii/issues/226))
  *Migration:* read `:lazy` among a rule's `:engines`; an earlier build reads a stored
  lazy-forward rule as backward.
  *Breaks:* sentex counts of the starter and of a KB whose forward rules read `arity`;
  `:engines` of the shipped arity converse; `edit-records!` of a lazy-forward rule
- **`(nonempty C)` holds for a type with a believed member.** `provers/NonemptyProver`
  answers it from a membership of C, or of a type below C, visible from the asking context,
  and stores nothing. A forward rule reading `(nonempty ?c)` fires for an inhabited type
  once a prior antecedent binds `?c`, rests on the member and the `genl` edges, and
  withdraws its conclusion when the last believed member goes.
  [inference.md](docs/inference.md#what-a-computed-answer-rests-on)
  ([#121](https://github.com/vaelii/vaelii/issues/121))
  *Migration:* read a stated `(nonempty C)` with `sentexes-matching`; `ask` answers the
  computed one too.
  *Breaks:* `ask` and `query` of `(nonempty C)`; firings of a rule reading
  `nonempty`
- **Two `CxTimeFn` slices that differ in both the monad and the time are ordered, and a
  `genlCx` path between two monads orders their slices as a stated `genlMonad` does
  ([#181](https://github.com/vaelii/vaelii/issues/181),
  [#219](https://github.com/vaelii/vaelii/issues/219)).** `(CxTimeFn CxSubStory (MonthFn
  2000 1))` sees `(CxTimeFn CxStory (YearFn 2000))` under `(genlMonad CxSubStory CxStory)`
  or under a `genlCx` path from `CxSubStory` to `CxStory`, with no slice between them
  written into. A path whose edge a rule concludes orders them too, a rule a `formula`
  declaration releases included, as does a declaration
  or an evidence fact a rule concludes or a retraction revives. A `genlCx` edge between two
  slices, stated or computed, orders the slices of those two slices. A write that orders
  slices nested past the producer's eight rounds logs
  `:vaelii.impl.nat-maintenance/producer-rounds`. A path and a stated
  `genlMonad` each justify the slice edge, so retracting either leaves it believed under its
  handle. A retraction reads the
  edges and data its settles moved, and a `genlCx` edge or a mint reads the slices along
  the contexts it can order, so none of the three costs more with the slices it does not
  reach.
  [context-nat.md](docs/context-nat.md#the-structural-genlcx-producer),
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad)
  *Migration:* none.
  *Breaks:* `sees?`, visibility and belief between `CxTimeFn` contexts that differ in both
  arguments, and between slices of two monads a `genlCx` path orders
- **`try-assert` refuses a write that makes a calculus network unsatisfiable.** With a
  calculus prover registered, a write whose stored or concluded sentex the support pass
  blames for an unsatisfiable component is refused as `:definitional-clash` with
  `:violation :unsatisfiable-network`, naming the other blamed facts in `:clashes-with`
  and the calculus, context, nodes and pairs in `:detail`; the call stores nothing.
  [qcn.md](docs/qcn.md#support-what-an-entailed-relation-rests-on)
  *Migration:* pass `{:refuse-unsatisfiable? false}` to store the write as `assert` does.
  *Breaks:* `try-assert` of a calculus fact that contradicts the stored network
- **The reification marks are in the forced-monotonic set.** `core.txt` declares
  `(forced_monotonic_predicate reifiable_function)` and `(forced_monotonic_predicate
  unreifiable_function)`, so each mark goes OUT only by retraction. A stored denial of a
  mark is never believed, where a known-true `(not (reifiable_function F))` took the mark
  OUT and left `F`'s applications structural. A `:default` `(reifiable_function F)` beside
  a `:default` `(unreifiable_function F)` is an irreducible conflict: both stay believed
  and `conflicts` reports the pair, where one of them was the loser.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-set)
  *Migration:* retract a mark rather than denying it, and retract one of two clashing
  marks, since a defeat no longer picks one.
  *Breaks:* `ask`, `query`, `conflicts`
- **No unary predicate declares its argument position.** core.txt drops `(arg C 1 T)` for
  `fixed_arity`, `variable_arity`, `bounded_arity`, `unbounded_arity`, `at_least_binary`,
  `forced_monotonic_between_predicates`, `reifiable_function` and
  `unreifiable_function`, and time.txt drops it for `initially`. Each restated a type the
  predicate's `genl` edges conclude, and added a second justification for every membership
  the edge concluded. A unary predicate's argument type is `thing`. An argument that no
  disjointness separates from the edge's type is now typed by the edge: `(fixed_arity 5)`
  derives `(relation 5)`, where the declaration refused it `:arg-type`. `ontology_test`
  fails on an `arg` declaration of any predicate of arity 1.
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
- **A text export writes a handle at a reference position as the `(ist Cx S)` it resolves
  from.** `export-text!` wrote no form for an `(except H)`, a koinii reply naming its
  target or another sentence naming a sentex by handle, and counted it in `:skipped`. It
  writes `(ist Cx S)`, the named record's context and sentence, in place of each
  `(sentexHandle H)` at a position a `quotedArg` or `quotedArgAndRest` declaration types
  `sentex_handle_term`, and `load-text!` resolves it as `assert` does, asserting each such
  declaration in the load first. A function term is read at its function's own reference
  positions, so `(noteOn Rex (MarkFn (sentexHandle H)))` is written `(noteOn Rex (MarkFn
  (ist Cx S)))`. `assert` and `assert-inert` resolve such a position too, so `(except (dog
  Muffet))` excepts the stored `(dog Muffet)` and is refused `:unresolved-reference` when
  nothing stores it. `:skipped` counts a record naming a handle at any other position or
  one no record holds.
  [canonicalization.md](docs/canonicalization.md#a-reference-to-a-stored-sentex)
  *Migration:* load such a file with `load-text!` of this build; write `(except (sentexHandle
  H))` to except by handle.
  *Breaks:* the files and the `:skipped` count `export-text!` writes for a KB holding a
  sentence that names a handle; `assert` and `assert-inert` of an `(except S)`, a koinii
  reply act holding a sentence at its target position, or a function term holding an `(ist
  Cx S)` at its function's reference position, which stored the sentence as written

### Breaking: koinii

- **A dispute id is the sorted content digests of its sides, and `dispute-id` takes the
  KB.** `(dispute-id kb entry)` returns the `"sha256:"` digests of the entry's `:handles`,
  sorted, so two seats holding a clash at different handles name it with one value.
  `disputes-in`'s `:dispute-id`, the `(DisputeFn "sha256:…" …)` marks and the
  `:adjudication` provenance tag carry it, and none of them holds a handle.
  `adjudication/rule` refuses a sentence that is neither a side of the dispute the id names
  nor a side's negation (`:koinii/not-a-side`). It finds a dispute's sides by content, so a
  party is refused `:arbiter-is-party` after another arbiter's ruling cleared the clash,
  where its ruling landed on its own claim.
  [koinii.md](docs/koinii.md#disputes-and-adjudication)
  *Migration:* call `(dispute-id kb entry)`; retract the `disputeNotified` and
  `disputeStale` marks stored under a handle id, and rule again on a dispute a ruling under
  a handle id settled.
  *Breaks:* `vaelii.koinii.dispute/dispute-id` at one argument; `dispute-state`,
  `standing-rulings` and `who-ruled` over marks and rulings stored under handle ids;
  `dispute-term`, `mark-notified`, `mark-stale`, `reopen!` and `adjudication/rule` called
  with a handle seq; `adjudication/rule` upholding a sentence that is neither a side nor a
  side's negation, which stored the ruling; `adjudication/rule` by a party after another
  arbiter's ruling cleared the clash
- **`koinii.deref` no longer publishes `->SentexRef`.** The locator encoder is the
  engine's content digest, reached through `vaelii.core/digest`, and the private record
  type it encodes a named sentex with left koinii's surface with it.
  [storage.md](docs/storage.md#content-digests)
  *Migration:* call `locate` or `vaelii.core/digest`; no caller builds a `SentexRef`.
  *Breaks:* a caller of `vaelii.koinii.deref/->SentexRef`
- **`koinii.deref` drops `locator-index` and `resolve-by-locator`.** A locator is a checksum
  and names no sentex: `dereference` finds a marker's record by its `:sentence` and
  `:context` and compares the locator, and no index is keyed by a locator.
  `resolve-by-locator` built one over every believed record per call.
  [koinii.md](docs/koinii.md#the-other-deployment-shape-independent-seats)
  *Migration:* send the `marker`, which carries the sentence and context, and call
  `dereference`.
  *Breaks:* `vaelii.koinii.deref/resolve-by-locator`, `vaelii.koinii.deref/locator-index`

### Refusal: change feed

- **`watch` refuses a goal on a predicate a registered calculus answers, as
  `:not-watchable`.** A watch on `(before ?x ?y)` under the Allen prover matched stored
  facts alone: it reported a fact in an unsatisfiable component, which `ask` answers
  nothing about, and never reported a relation the network entails. `add-reasoner`
  refuses a calculus answering a standing watch's goal the same way.
  [feed.md](docs/feed.md#what-is-refused)
  *Migration:* watch the whole feed and read the relation with `query` or
  `qualitative-network`.
  *Breaks:* `watch` and the daemon's `watch` op on a calculus predicate, either polarity;
  `add-reasoner` of a calculus answering a standing watch's goal

### Refusal: daemon

- **The start scripts take the heap from physical memory, and refuse a `VAELII_HEAP` above
  it.** Unset, `VAELII_HEAP` is half of the host's physical memory up to `31g`, where it was
  `40g`. Set above physical memory, the script prints the two sizes and exits 1 before the
  JVM starts. [operations.md](docs/operations.md#a-seat-on-a-small-host)
  *Migration:* set `VAELII_HEAP` for a store whose recover needs more than the default.
  *Breaks:* `scripts/start-vaelii*.sh`, `scripts/upgrade-kb.sh` and
  `scripts/test-full-kb.sh` under a `VAELII_HEAP` above physical memory

### Refusal: storage

- **A target-following meta-sentex names a stored sentence by its content, and one naming
  no stored sentence is refused.** At a position of a `target_following_predicate` that
  `(arg P n sentence)` declares, `assert` replaces a sentence, or `(ist Cx S)`, with the
  `(sentexHandle H)` of the sentex stored for it, either spelling of a symmetric sentence
  finding the one stored, and refuses one no stored sentex answers or a rule stored as
  several (`:unresolved-reference`). 0.30.0 stored such a sentence as written: the meta named
  no sentex, so retracting the sentence it was about left the meta standing. `export-text!`
  writes the handle back as `(ist Cx S)`, so a text KB can state a note on a stated sentence
  that follows its retraction ([#185](https://github.com/vaelii/vaelii/issues/185)).
  [canonicalization.md](docs/canonicalization.md#a-reference-to-a-stored-sentex)
  *Migration:* assert the sentence before the meta naming it; `load-text!` asserts a file's
  reference declarations first and retries a refused meta once its sentence is stored.
  *Breaks:* `assert` of a `target_following_predicate` meta naming a sentence nothing
  stores, `:unresolved-reference`

### Additive: storage

- **A fork pulls a newer dump as its base and keeps its own writes.** `(import! fork dir
  {:rebase? true})` replaces the base of a fork opened from `:base` opts with the dump and
  asserts the fork's premises, inert sentexes and retractions of base premises again over
  it, reporting under `:rebase` what it could not assert. `koinii.deref/pull!` passes it,
  so a seat opened as a fork over a base directory and a directory of its own pulls a
  newer commit without losing its observations. A read on another thread waits for the
  rebase to end, the replay of a marker an earlier rebase left included, and answers from
  the fork before it or after it. A lazy seq a read returned is realized against the fork
  as it stands, partway through a rebase included, and a read that starts a rebase of its
  own fork deadlocks. `:on-replayed` is called with each replayed premise's captured
  record and its new handle, and `pull!` rebases through `koinii.identity/rebase!`, which
  seals an attestation again over the new handle when it verified before the rebase, on
  the writes of a stopped rebase it finishes as well. The rebase writes a durable fork's
  writes to its directory as a delta with a marker before it empties the own half, and an
  `open-kb` that finds the marker asserts them again, so a crash outside the import of the
  dump loses none of them. After a crash inside the import, that open drops each write the
  partly imported base cannot hold, and pulling again does not restore it. A
  fork `fork` took over a live KB is refused `:frozen-base`.
  [overlay.md](docs/overlay.md#replacing-the-base),
  [koinii.md](docs/koinii.md#the-other-deployment-shape-independent-seats)
- **A seat publishes its fork's writes as a delta, and a peer merges it.**
  `(export-text! fork dir {:delta? true})` writes the fork's own premises and inert
  sentexes as a text KB, counting the base premises it retracted in `:retractions`, and
  `(load-text! kb dir {:merge? true})` reads it into a KB holding content of its own,
  reporting each form it refuses under `:refused`. The delta's `digests.edn` holds the
  content digest of each reference, and a reference the loading KB resolves to a sentex
  with another digest is refused `:canonical-mismatch`. A peer that loads a seat's
  observation reaches the seat's defeat of a shared default. A mesh of peer seats, each a
  daemon over its own copy that merges every peer's delta, is the supported multi-machine
  topology. [overlay.md](docs/overlay.md#a-delta),
  [operations.md](docs/operations.md#a-mesh-of-seats)
- **A sentex has a content digest.** `digest`, `digests` and `digest?`, and the daemon ops
  `:digest` and `:digests`, compute the `"sha256:"` checksum `koinii.deref` builds its
  commit identities from, equal in every KB that holds the sentex.
  [storage.md](docs/storage.md#content-digests)
- **`upgrade --sync` rewrites the premises a release renamed.** Each release records
  what it renames, merges, re-means and retires in `resources/renames/<version>.edn`;
  this release's file holds `koinii.deref`'s three retired vars and `dispute-id`'s
  re-meaning. `upgrade --sync` rewrites a stored premise naming a renamed symbol
  or merged context, and reports one naming a re-meant or retired symbol under
  `:renames`. The starter's load logs a warning for each retired symbol a stored sentex
  names. `lein lint`'s E22 holds the file to the Breaking entries, the shipped KB
  and the API goldens. ([#246](https://github.com/vaelii/vaelii/issues/246))
  [catalog.md](docs/catalog.md#a-releases-renames)
- **A disk KB on a filesystem that refuses advisory locks is refused with
  `:lock-unsupported`.** An open whose single-writer lock request the filesystem answers
  with an I/O error throws `:lock-unsupported` with `:dir` and the OS's `:reason`, and the
  `IOException` as its cause, where it threw that `IOException` untyped. The lock's holder
  tag takes the host name from `HOSTNAME` before it asks the resolver, and asks the
  resolver once per process.
  [troubleshooting.md](docs/troubleshooting.md#the-disk-kb-will-not-open)

### Additive: daemon

- **A daemon reply carries each sentex's content digest on request.** A body carrying
  `:digests? true`, and every call of a `client` opened with `{:digests? true}`, adds
  `:digest` to each map in the reply that names a sentex: a sentex record, a feed or
  `preview` entry, a clash report's side. A handle names a sentex on its own KB only, so a
  peer seat finds the sentex by its `:sentence` and `:context` and checks the digest.
  [operations.md](docs/operations.md#daemon--vaeliiserve),
  [overlay.md](docs/overlay.md#a-handle-stays-in-its-kb)

### Additive: inference

- **A decided nogood is reported as a defeat report.** `(conflicts kb {:defeats? true})`
  adds, beside the conflicts, one entry per nogood whose placements defeat one member,
  such as a `:monotonic` observation beside the `:default` expectation it refutes: the
  report shape with `:verdict :defeat`, `:placed-in`, `:loser` and `:winners`, each side
  naming its sentence, context, class and the rules concluding it. A change-feed event
  whose settle placed such a defeat carries the reports under `:defeats`, over the wire
  too, and a standing query on the loser below the placement receives them.
  [nmtms.md](docs/nmtms.md#observation-beats-expectation),
  [feed.md](docs/feed.md#a-defeat-arrives-as-a-report)
- **A write that makes a calculus network unsatisfiable files its ledger entry at the
  settle.** The `:qualitative-inconsistency` entry was filed by the first read of the
  network, or by a forward rule's join on it; the settle now asks every governing context
  of each calculus the write moves. A plain listener's feed event carries the entry under
  `:unsatisfiable`, and the feed event, read forward through a subscription's cursor, is
  the record that outlives the in-memory ledger. The settle closes each context's recorded
  pass from the pairs the moved facts narrow, so loading N facts one write at a time solves
  no network N times. A rolled-back write, preview or `edit!` puts the calculi's report
  records back with the ledger, so an `assert` after a refused `try-assert` of the same
  fact files the entry.
  [qcn.md](docs/qcn.md#support-what-an-entailed-relation-rests-on),
  [preview.md](docs/preview.md#what-the-rollback-restores-and-what-it-does-not)
- **`argue` names what an answer no record holds was read from.** A derivation leaf a
  `SupportingProver` answered carries `:supports`, one vector of `{:handle :sentence
  :context}` per reading, and a ground side a prover answered gets that one leaf without a
  `:max-depth` too. A `transitiveInArg` answer names the claim, the declaration and the
  edges, and the `/demo` travelling row links them.
  [inference.md](docs/inference.md#an-answer-no-record-holds)
  ([#239](https://github.com/vaelii/vaelii/issues/239))

### Additive: integrity

- **`kb-integrity` reports a candidate term a sentence uses whose every membership the
  uses entail, under `:undeclared-term`.** A constant used only as `(genl X retired)` and
  `(genlArg ranks 1 retired)` holds `predicate` and `unary_predicate` memberships the two
  declarations entail, and the default sweep over `#{retired}` reports `{:term retired
  :arity 1}` until a membership or an arity binding is stated. A `(comment T "…")` is a
  use. The `:unknown-option` message lists the category.
  ([#224](https://github.com/vaelii/vaelii/issues/224))
  [integrity.md](docs/integrity.md#what-an-undeclared-term-finding-means)
- **`kb-integrity` reports, for review, the sibling type pairs nothing decides and the
  binary predicates no relation property decides.** `:open-sibling-pair` gives each
  parent with the pairs of its direct specs that nothing the audit context sees decides,
  `genl` edges included, as `{:parent body_part :count 27 :pairs [[feather fin] …]}`.
  `:undecided-relation-property` gives each binary predicate with no relation property
  mark and no stated denial of one, as `{:predicate likes}`; an `inverse` or a
  `functionalInArg` decides nothing. A sweep runs either only when `:categories` names it.
  A `:derivable-stated-edge` finding whose stated sentence an `(acknowledgedFinding
  :derivable-stated-edge S "reason")` names carries the reason as `:acknowledged`.
  [integrity.md](docs/integrity.md#what-an-open-sibling-pair-finding-means),
  [integrity.md](docs/integrity.md#what-an-undecided-relation-property-finding-means)

### Additive: shipped ontology

- **The upper ontology states a membership of every constant it uses.** 31 types its
  `genl`, `disjoint` and argument declarations name are stated `unary_predicate`
  (`building`, `vehicle`, `wing`, `quantity`, `unit_of_measure`, …), the twelve units
  `unit_of_measure`, and `Length`, `Mass` and `Duration` `physical_dimension`. `defeat` is
  declared as `except` is. reflection.txt adds `syncategorematic`, a constant of the
  syntax that names nothing, under `nowhere_never` and separated from `linguistic` and
  `quantitative`, so a `(reifiable_function Quote)` is not convicted under either
  argument-type reading. core.txt states each `set/` wrapper and `Quote` one, so a
  `kb-integrity` `:undeclared-term` sweep over every upper term is `:audited`.
  ([#224](https://github.com/vaelii/vaelii/issues/224))
  [integrity.md](docs/integrity.md#what-an-undeclared-term-finding-means)
- **`time.txt` derives `monad_context` of a believed `context` that is not a slice, so a
  slice of such a context answers its monad and its time
  ([#219](https://github.com/vaelii/vaelii/issues/219)).** For the `cx/` constant of
  `(CxTimeFn CxRealWorld (IntervalAfterFn W))`, a query of `cxMonadOf` answers
  `CxRealWorld` and a query of `cxTimeOf` answers `(IntervalAfterFn W)`, with no
  `monad_context` statement.
  [time.md](docs/time.md#a-context-at-a-time-cxtimefn-and-the-monad)
- **`life.txt` ships `birthDate`, an organism's birth stated as a calendar term, and
  concludes `birthYearOf` from it.** `(birthDate Tom (DayFn 1970 3 14))` states the day,
  and concludes the `MonthFn` and `YearFn` birth dates holding it and `(birthYearOf Tom
  1970)`; an `InstantFn` value concludes its `DayFn` the same way, so `olderThan` reads a
  birth date at any of those precisions. `birthDate` is not functional: the day of one
  birth and its year are both its `birthDate`. A `DatetimeFn` value concludes no
  `birthYearOf`.
  [contexts.md](docs/contexts.md#the-context-topology)

### Additive: browser

- **A term page lists the term's definitional block, with each missing part marked.**
  `describe` of a type or a predicate answers `:definitional-block`, the parts
  `handbook/06-definitional-block.md` names as `{:part :value}` rows in its order,
  `:missing` where the KB holds none, the arity class apart from the kind, and a type's
  siblings each with the separation or the witnessed overlap that decides them. The links
  part (`seeAlso`, `termsRelated`) has no row. The term page renders the block at the top
  of its prose, a link beside each missing part opening the assert form on a sentence
  that supplies it, and the button under `/stats`'s definitional blocks heading runs a
  read job tallying how many types hold each part.
  [web.md](docs/web.md#a-term-page-lists-its-definitional-block), [api.md](docs/api.md)
- **`/quality` renders `kb-quality`'s seven readings**, one region each in
  `quality-report`'s order, every listed rule and declaration linked to its sentex. The
  button runs the census as a job beside a load; `/stats` and `/quality` link each other.
  [web.md](docs/web.md#the-health-report)

### Fix: answers

- **An open query answers a part's location and ownership again.** With the starter,
  `(query kb '(locatedIn U1 ?w) ctx)` answered `()` where `ask?` on `(locatedIn U1 Desk)`
  answered true, and `(owns Ann ?p)` named the whole and none of its parts. `CxMereology`
  states its two forward rules again and acknowledges kb-integrity's
  `transitiveInArgInverse` suggestion for each, so `query`, `prove` and `ask?` agree.
  A part's derived `locatedIn` and `owns` are stored again.
  [inherit.md](docs/inherit.md), [integrity.md](docs/integrity.md#what-a-rule-macro-finding-means)
- **A forward rule's negated antecedent reads a separation's denial.** With `(disjoint dog
  cat)` and `(cat Tom)`, the forward rule `(implies (and (pet ?x) (not (dog ?x))) (stray
  ?x))` stored no `(stray Tom)`, where `prove` and `query` answered it. The forward join
  answers the literal from the denying membership in every arrival order, and the
  conclusion rests on the membership, the declaration and the `:monotonic` edges the
  denial climbs.
  [inference.md](docs/inference.md#a-negated-antecedent-reads-a-separations-denial)
- **A functional slot holding measures compares magnitudes.** Under `(functional
  weightOf)`, `(weightOf Muffet (QuantityFn 20000 Gram))` beside `(QuantityFn 20 Kilogram)`
  was a `:functional` clash, which `try-assert` refused and `assert` stored as a nogood,
  and so was an interval holding the point. Two measures that normalize to one dimension
  and base unit with bounds that meet are one value: `try-assert` stores the second, and
  the settle places no nogood where the unit table reads them so. A unit-table row stored
  or retracted after the facts moves the clash.
  [quantity.md](docs/quantity.md#a-functional-measure-slot)
- **A measure compares and aggregates only with measures in its own base unit.**
  `(dimensionOf Foot Length)` alone made `(QuantityFn 1 Foot)` the same quantity as
  `(QuantityFn 1 Meter)`, and `agg/sum` over the two answered `(QuantityFn 2 Foot)`. A
  unit with no `conversionFactor` is its own base at factor 1, so it compares with itself
  and with the units converting to it, and with no metre. An aggregate over two units of
  one dimension whose factor rows name different bases has no answer, as a comparison
  between them has none.
  [quantity.md](docs/quantity.md#comparison-semantics)
  *Migration:* give each unit both rows, its factor stated against the dimension's base.
- **A forward firing over a stored calculus fact is withdrawn when its node is
  blocked.** A rule on `(nonTangentialProperPart ?x ?y)` kept its conclusion after
  `(spatiallyDisconnected A B)` made the network unsatisfiable: the settle blocked the
  firing and a later join placed it again from the stored fact. A placement over a node
  of an unsatisfiable component is refused and released when the network is satisfiable
  again, as a firing over an entailed relation is.
  [qcn.md](docs/qcn.md#what-a-registered-prover-is-reachable-from)

### Fix: order independence

- **A mint is withdrawn when its subsumer is also a premise or has a second derivation.**
  With `(genl pType aType)` stated after `(pType Rex)` and `(arg pType 1 aType)`, the
  minted `(aType Rex)` stayed stored when a rule concluded `(pType Rex)` again over it;
  stated before them, the mint was withheld. Both orders now hold the same records
  ([#241](https://github.com/vaelii/vaelii/issues/241)).
  [argtypes.md](docs/argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on)
- **A type an argument declaration mints is lifted when its type is decontextualized.**
  With `(decontextualized_predicate aType)` stated before `(pType Rex)` in CxWorld, the
  minted `(aType Rex)` stayed in CxWorld; stated after it, the mint was lifted into
  CxUniverse, and `recover` lifted it in either order. A new mint now lifts as an asserted
  fact does ([#242](https://github.com/vaelii/vaelii/issues/242)).
  [contexts.md](docs/contexts.md#the-lift-is-about-the-predicate-so-derived-content-is-lifted-too)
- **A forward rule on `disjoint` and `genl` fires on a pair two edges apart whichever
  arrives last.** In `(and (disjoint ?a ?b) (genl ?a ?b))` each literal binds the other's
  ends, so a rule arriving after its facts read the stored `genl` edges alone and missed
  a pair two edges apart that a stored `disjoint` names. The join runs a second time led
  by the `disjoint` literal, and the rule fires with one justification.
  [inference.md](docs/inference.md#a-disjoint-antecedent-reads-the-separations)
- **`chain-report` no longer counts a firing an aggregate's moved count withdrew as
  refused.** A rule on `(agg/count 0 …)` whose counted fact arrived in the same `edit!`
  as its subject reported one `:blocked` refusal per subject with no reason, where the
  facts arriving first reported the rule `:silent`. Both orders report it `:silent`, and
  belief is unchanged.
  [aggregate.md](docs/aggregate.md#maintenance-when-the-aggregate-is-a-rule-antecedent)

### Fix: rule checks

- **A rule binding a variable to a class of binary predicates and to an argument of
  `genl` is believed.** Each position of a `type_relation_predicate` asks for what its
  `args` declaration names, `predicate` for `genl`, where it asked for a
  `unary_predicate`; such a rule was held inert as `:arg-variable` and listed as
  `:inert-rule`, although `(genl performedBy doneBy)` relates two binary predicates. A
  position no `args` declaration covers, as in a KB that does not load `core.txt`, carries
  no relation-kind constraint. An `:arg-variable` conviction at such a position names the
  `args` type in `:expected` ([#244](https://github.com/vaelii/vaelii/issues/244)).
  [taxonomy.md](docs/taxonomy.md#and-against-the-variables-of-a-rule)
- **`(args P T)` and `(argAndRest P n T)` constrain a rule's variables as `arg` does.** A
  covering declaration typed a rule's variables only on a `type_relation_predicate`, so
  `(args p b)` left believed a rule that `(arg p 1 b)` held inert, and `try-assert` of an
  `argAndRest` or `args` that convicts a stored rule stored it where it refuses the `arg`.
  Both are now read at every predicate, and `try-assert` refuses the covering declaration
  as `:definitional-clash` with `:violation :arg-variable`, naming the rule
  ([#244](https://github.com/vaelii/vaelii/issues/244)).
  [taxonomy.md](docs/taxonomy.md#and-against-the-variables-of-a-rule)
- **A rule reading `different` beside the starter's time-slice equality is stored.** A
  forward rule with a `(different ?a ?b)` antecedent concluding a kind of
  `uninterrupted` was refused `:not-stratified`, the cycle running through the
  backward `(equals (CxTimeFn (CxTimeFn ?c ?t1) ?t2) …)` rule in `time.txt`. A forward
  rule concluding an equality from a `different` antecedent is refused as before.
  [equality.md](docs/equality.md#interactions)
  *Migration:* a rule set whose only cycle ran through a backward-only equality rule is
  stored.
- **A generator fed by another generator is stored when nothing feeds back.** A generator
  reading `genl` beside core.txt's `partitionedByType` generator, which concludes `genl`,
  was refused `:not-stratified` although no generator reads what it concludes. A generator
  is refused only on a path of feeds back to itself, and the refusal message names that
  path.
  [generators.md](docs/generators.md#what-is-refused)

### Fix: daemon and client

- **A stopped daemon or browser server leaves no feed listener on its KB.** `.stop` on a
  `serve/start` server left every wire subscription's listener registered, so `watchers`
  listed it and each later write filed an event into a ring nothing could poll. `.stop` on
  a `vaelii.web/start` server, or `dev-stop`, left every `POST /op` subscription's listener
  registered, and a parked poll held its thread until its 30 s ceiling. The browser servers
  in one process share one subscription registry, so stopping one of them drops the
  subscriptions every other browser server in the process issued.
  [feed.md](docs/feed.md#across-the-wire)
- **A caller's `*print-length*` or `*print-level*` elides nothing the daemon, the client
  or the starter's write-back writes.** Under a bound, the daemon's reply could be
  unreadable EDN, a request from `vaelii.client` sent `...` in place of the rest of a
  sentence, and `sync/write-back!` wrote `(set/monotonic #)` into a shipped file.
  [operations.md](docs/operations.md#daemon--vaeliiserve)
- **A CLI command releases the `--dir` it opened when it ends, a `--starter` load that
  throws included.** `vaelii.cli/-main` left the KB open, so a process calling it kept the
  directory's lock and the durability daemon's registration until the process exited.
  [operations.md](docs/operations.md#the-single-writer-contract)

### Fix: koinii

- **A wire subscription whose poll fails drops its subscription on the daemon.** The loop
  stopped, and the daemon's subscription stayed until its idle reap and counted against
  the daemon's subscription limit.
  [koinii.md](docs/koinii.md#the-deployment-shape)

### Fix: storage

- **A crash while a store directory's manifest is written leaves a directory that
  opens.** `reasoners.edn`, `records.edn`, `format.edn` and an index's `layout.edn` were
  written in place, so a crash mid-write left a file the next open refused as
  `:malformed-manifest` or `:unreadable-store`. Each is written to a temp, fsynced and
  renamed over the old one.
  [storage.md](docs/storage.md#a-directorys-sentinel)
- **A `close!`, an `open-kb {:oplog? true}` or a `fork` that throws releases what it
  opened.** A `close!` whose directory close threw skipped the operation log and the
  record store, and an `open-kb` that threw after its log opened left the log open. In
  both cases the durability daemon went on fsyncing a log in a directory whose lock was
  released. A `fork` that threw from its recovery or reasoner registration left its own
  in-RAM half in the process registries, one space per failed `fork`.
  [storage.md](docs/storage.md#the-on-disk-backend-disk),
  [storage.md](docs/storage.md#the-operation-log),
  [storage.md](docs/storage.md#two-stores)

### Fix: inference

- **A stopped write keeps the class memberships' justifications it found.** A write whose
  run synced a class membership over a `genl` edge it added, and then stopped at
  `:max-derivations`, `:max-ms`, `:stop?` or the heap mark, left the justification over
  the path it replaced deleted, and the rollback stored it again at a new handle. The
  run now leaves that drop to the settle.
  [taxonomy.md](docs/taxonomy.md#arity)
- **A portfolio race inside a forward-chaining run leaves the run's handle cache to the
  writing thread, and a race inside a settle reads the belief the settle is deciding.**
  Each racer of a `{:portfolio? true}` query that a prover ran during a chain wrote the
  run's `java.util.HashMap` handle cache and chain authority memo from its own thread,
  beside the other racers. Each racer runs with neither bound. Inside a settle, each racer
  read the belief the settle held for other threads, so the race could miss answers the
  same query without `:portfolio?` found.
  [inference.md](docs/inference.md#which-node-pops-next-is-a-policy-vaeliiimpltactics)
- **`blocked-justifications` names only justifications the KB holds.** A settle that
  placed a guard defeat could delete a justification its exception pass had just found
  blocked, and the blocked set kept the deleted id. Every later settle carried it, and an
  `exceptWhen` case in the suite ended with 36 such ids and no live one.
  [nmtms.md](docs/nmtms.md#blocked-justifications-exceptwhen)

### Fix: performance

- **A KB that registers a shipped reasoner keeps a reasoning image and seals its log.**
  A `:disk-snapshot` KB opened with `:reasoners` or given `add-reasoner` wrote no image
  at close, so every open paid a full recover, and a crash of its log rebuilt from the
  records. The image's manifest records the reasoner set, and an open with the same
  set installs it. The first close after the upgrade writes the image.
  [storage.md](docs/storage.md#the-reasoning-image)
- **A write keeps each context's reader frame while nothing it reads moves.** In a KB
  holding an `except` and a placed `defeat`, every belief read of a firing in `assert` or
  `edit!` rebuilt the context's reader frame from the stored rules and their records,
  where a settle kept the frame. An `edit!` of twelve memberships builds 2 frames, not 24.
  Answers are unchanged.
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion)
- **A settle that stores defeats costs the support it reads.** A settle asks whether each
  defeat it stored still leaves its target believed in the target's own context. That read
  cost every firing resting on a derived handle of the target's support, and read every
  justification of each handle in the support, a premise's included. The settle now keeps
  the reasons for its reads and reads no premise's justifications. Sixteen defeats beside
  8,192 firings on a derived handle took 4.3 ms a defeat and take 1.0 ms, and beside a
  premise 8,192 firings conclude took 22.8 ms and take 1.1 ms, as beside 256. The read logs
  progress as "settle: read the defeats' own-context belief". Answers are unchanged
  (`lein perf`'s `defeats-beside-a-wide-derived-support` and
  `defeats-beside-a-wide-premise`).
  [nmtms.md](docs/nmtms.md#a-nogood-placed-as-a-conclusion)
- **A defeat cycle's read reads each defeat in it once, and `record-arg-types!`'s fact
  budget bounds the read.** A read that met a defeat cycle read each defeat of the cycle
  again on every path reaching it, so its reads grew as 2 to the depth of the nested
  defeats: a cycle of 41 defeats in 20 layers of two took 2.1 million defeat reads, and
  takes 3,444. A membership check under a fact's budget stops inside the walk when the
  budget passes, so the pass sets the fact aside at the budget.
  [nmtms.md](docs/nmtms.md#a-defeat-dependency-cycle),
  [argtypes.md](docs/argtypes.md#the-pass-over-a-stored-kb)
- **`ask` skips three per-goal checks a goal does not need.** `(reflexive P)`'s diagonal
  and a typed calculus's positive answer read a term's types only at a position `P`
  declares, where the read was 8% of an `ask` of `(P a ?y)` over a reflexive, symmetric,
  transitive `P` with ten-member classes. `NegatesProver` and `CommonGenlProver` test the
  predicate before they collect a `(not (P ?x))` goal's free variables, which takes that
  `ask` over 300 birds and 30 penguins from 40.9 to 37.3 µs. A goal holding no
  `nat/no-match` answers from one scan of its symbols, which takes the no-match walk from
  3.5% to 0.8% of the first `ask`. Answers are unchanged.
  [inference.md](docs/inference.md#the-pluggable-prover-engine-vaeliiimplprovers-ask),
  [naf.md](docs/naf.md#fully-bound-to-evaluate), [nat.md](docs/nat.md#read-path)
- **`edit!` reads the stored stratification graph once for a batch's adds.** Each add built
  the graph again, reading every rule node its walk reached once per `genl` edge in the
  batch. A rule the batch writes still empties the held graph. Answers are unchanged.
  [exceptions.md](docs/exceptions.md)
- **A settle's loop over no items schedules no progress timer, a closed loop's timer task
  leaves the queue, and the `place the nogoods` line counts the placements a pass
  removes.** A fact assert over `core.txt` runs 16 progress loops, and each scheduled a
  timer task that the timer kept queued for 15 s after the loop closed. Under a Trove log
  fn vaelii did not install, each task also held every binding of the writing thread for
  those 15 s. A loop over a total of 0 schedules none. The `place the nogoods` total left
  out the placements a pass removes. A pass that only removed placements had a total of 0,
  so it scheduled no timer and printed no line however long its removals ran. A pass that
  also placed some counted none of its removals.
  [operations.md](docs/operations.md#progress-lines)

### Fix: shipped ontology

- **`measure.txt`'s `dimensionOf` and `conversionFactor` rows are `set/monotonic`.** A
  conclusion a forward rule draws through a measure comparison names the rows it
  converted through, and rested at `:default` on them whatever the strength of the facts
  and the rule; it keeps that strength now.
  [quantity.md](docs/quantity.md#a-functional-measure-slot)
- **`CxKinship.txt` states `(genlInverse fatherOf parentOf)` and `(genlInverse motherOf
  parentOf)` in place of the two forward rules that restated them.** A `fatherOf` or
  `motherOf` fact answers a `parentOf` goal and satisfies a `parentOf` antecedent through
  the edge, and stores no `parentOf` conclusion.
  [inference.md](docs/inference.md#genlinverse-the-fan-with-the-arguments-swapped)
  *Migration:* a caller that counted the stored `parentOf` conclusions reads them through
  `ask` or `query`.

### Fix: integrity

- **The rule-clash pairing reports a `:disjoint` pair a conclusion's declared arg type or a
  `partition` separates.** `(arg cat_kind 1 feline_kind)` beside a rule concluding
  `(cat_kind ?x)` dropped its clash with a rule concluding a `canine_kind`, disjoint from
  `feline_kind`, as unreachable; a KB whose only separation was a `partition` or
  `separating` declaration paired no unary conclusions. `kb-integrity`'s `:rule-clash`
  and `kb-quality`'s `:clashes` now report both pairs
  ([#243](https://github.com/vaelii/vaelii/issues/243)).
  [integrity.md](docs/integrity.md#what-a-rule-clash-finding-means)

### Fix: browser

- **`dev-repl` called again releases the starter KB it opened before, instead of clearing
  that KB's stores under it.** The second starter opened over the first one's memory
  space, so the first KB kept its belief over emptied records, and a write through it
  landed in the second KB's records. The call refuses with `:still-writing` while a job
  writes the earlier starter, and the browser it started before keeps serving.
  [web.md](docs/web.md#working-on-it-lein-browser)
- **`/lists` and `/quality` show a result only on the KB it was read from.** Two KBs no
  catalog entry holds, such as a test's KB and an `--attach`, each showed the other's last
  list run and last reading.
  [web.md](docs/web.md#the-health-report)

### Internal

- **`lein lint`'s `doc-size` check holds each `.clj` file's docstring lines past the
  eighth and its comment lines to `scripts/doc-size-baseline.txt`.** `lein lint-doc-size`
  runs it alone, and `--update` lowers a budget and never raises one.
- **`lein test-red` runs the `^:red` tests with the verdict inverted per test.** It exits
  1 on a red test that passes and prints that test's `lein test :only` line. `lein gate`
  prints "red owed" when its pending diff touches a file the red tests drive.
  [CONTRIBUTING.md](CONTRIBUTING.md)

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
