# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.22.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Refusals

- **A durable fork remounted over a base that has grown since is refused
  `:fork-base-overlap`.** A fork keys its records and its excepts' targets by handle, and
  mints them above the base's handles at the time. Remounted over a base that has since
  grown (a newer starter, more files loaded at startup), the fork's record at each handle
  the base now also held won every read: the base's sentence there answered `unknown`
  through the fork, `argue` returned the fork's justification for it, and an except naming
  a handle the fork had retracted hid the base sentence that took that handle (#99). A
  fork that had only retracted inherited premises hid the grown base's sentences too,
  under any key it had emptied, and so did a reindexed fork; over a base rebuilt in another
  order, a tombstone hid whichever sentence took the handle. Each mount now records the
  base's watermark in the fork's bookkeeping, and the next mount refuses when the base
  holds a record at or above it and the fork has written anything. A fork pins a digest
  of each base record it tombstones, overrides or releases, and a mount over a base
  holding another record at a pinned handle is refused. A fork mounted before this
  release is checked on its first mount by comparing its own records with the base's at
  the handles both hold. The refusal names the `:handles` at issue and leaves the fork's
  directory unlocked. [overlay.md](docs/overlay.md#the-merge-model--record-half).

  *Class:* **Refusal** (a remount over a grown base answered base sentences with the
  fork's records, with no error).
  *Migration:* mount the fork over the base it was taken against, read its premises, and
  re-assert them by content in a fresh fork over the new base, re-pointing each except
  at the new handle of its target.

  *Breaks:* `fork`, `open-kb`

## 0.22.0 — 2026-09-29 — "prove answers what ask answers, a rule record names the engines that run it, and a clash is decided where its grounds come into view"

### Breaking

- **`prove`, `ask` and `query` answer the entailed goal where they answered the stored
  one, and a depthless `query` expands no rule.**
  - **`prove` answers a literal as `ask` does.** A literal the backward chainer does not
    rewrite is answered by the prover registry, not the stored facts alone, so `prove`
    finds `(genl pug mammal)` two edges apart, the reflexive `(genl pug pug)`, an
    evaluable and an inferred argument type; level 7 of `lookup` is now `prove`'s search.
    `prove`, `provable?` and `prove-within` return answers they did not.
    [inference.md](docs/inference.md#the-two-side-by-side).
  - **An open-functor goal answers every type the term holds.** `(?c Muffet)` beside
    `(dog Muffet)` and `(genl dog animal)` answers `animal` as well as `dog`, so
    `[(genl ?c animal) (?c Muffet)]` answers the same whichever literal leads. A functor
    variable that is also an argument, or one under a negation, binds the stored functor
    alone. `ask`, `query` and `prove` of such a goal return answers they did not.
    [indexing.md](docs/indexing.md).
  - **`query` with no depth reads no depth from `inference/*max-depth*`.** A depthless
    `query`, `query?` or `query-status` answers from the prover registry alone unless
    `opts` or `*query-options*` names a `:max-depth`; `search-tree` and
    `compare-tacticians` read their depth from the same two places. `prove` still reads
    `inference/*max-depth*`. [api.md](docs/api.md).

  *Class:* **Breaking** (the three read paths return answers they did not).
  *Migration:* for `prove` and open-functor goals, none for a caller that wanted the
  entailed answers; one that wanted stored facts only reads `sentexes-matching`. For a
  depthless `query`, pass `{:max-depth n}`, or bind `*query-options*` to `{:max-depth n}`.

  *Breaks:* `prove`, `provable?`, `prove-within`, `resume`, `ask`, `query`, `query?`
  *Breaks:* `query-status`, `search-tree`, `compare-tacticians`

- **A rule record holds `:engines` and `:effect` in place of `:direction`,
  `:assumption` and `:constraint`.** `:engines` is the subset of
  `#{:forward :backward :solve}` that runs the rule (`#{:backward}` bare, `#{:forward
  :backward}` for `set/forwardRule`, `#{:forward}` for `set/forwardOnlyRule`, `#{}` for
  `set/inertRule`, `#{:solve}` for a choice or constraint rule); `:effect` is what the head
  is (`:derive`, `:choose`, `:forbid`, `:penalize`). A sentex map from `sentex` or
  `sentexes-matching` carries the two keys, and a re-assert joins two spellings' engines by
  union. Stores, dumps and frames holding the three old fields read as before, and no
  index rebuilds.
  [canonicalization.md](docs/canonicalization.md#rule-wrappers-become-fields),
  [storage.md](docs/storage.md#the-sentex-records--literalsentex-and-rulesentex).
  *Class:* **Breaking** (a rule map's keys). *Migration:* read `(:engines sx)` where
  `(:direction sx)` was read — `(contains? (:engines sx) :forward)` for forward — and
  `(:effect sx)` where `(:assumption sx)` / `(:constraint sx)` were; the `:direction` opt
  on `assert` and `assert-rule` is unchanged.

  *Breaks:* `(:direction`, `(:assumption`, `(:constraint`, `RuleSentex`

- **A clash is decided where its grounds come into view, and `violations` no longer files
  the clashes the settle decides.**
  - **A clash is decided where its grounds come into view, not only where its members
    do.** A separation (`disjoint`, the `genl` edge to a separated type, a `functional`
    or `asymmetric` mark) in a context the members' maximal common descendant could not
    see convicted nothing, and a context seeing both members and the separation believed
    both. The vantages are now the most general contexts of each reading of the grounds
    (`settle/clash-vantages`), and `(contradictions kb context)` keeps an entry only for a
    reader at or below a vantage that weighed it. Such a pair moves belief below the
    vantage and leaves `violations`.
    [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).
  - **An inherited converse refuses only when the claim and its reading are known-true.**
    Under `(asymmetric P)` preserved along `genl`, a `:default` converse of a `:monotonic`
    claim read over `:default` declarations or edges was refused as `:asymmetric` in one
    order and stored as an `:inherited` dilemma in the other. The entry point weighs it at
    the weakest class of the claim, the declarations and the edges, so `assert` stores a
    converse it refused and both orders report one `:inherited` dilemma.
    [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).
  - **The settle files no `:exposure-truncated` entry and no cross-context `:disjoint`
    entry.** A pair a context sees whole is answered by `contradictions` or `conflicts`;
    one the budgeted sweep has not reached is counted by `:arbitration-truncated`, and
    `exposed-clashes` names every jointly-visible pair. A settle over separated types
    spends 3% to 8% less time.
    [defenses.md](docs/defenses.md#a-clash-the-settle-has-not-decided-is-counted-not-named).
  - **A settle hands no nogood to a solver, and the `:not-defeasible` refusal is gone.**
    `decide-nogood` answers every nogood with a defeat, a dilemma or a hard clash, so the
    solver arm never ran, and the documented refusal `:type` it alone threw is removed.
    [nmtms.md](docs/nmtms.md#only-default-content-reaches-a-solver).

  *Class:* **Breaking** (belief below a vantage, the stored converse and the violation
  kinds a caller branches on all move).
  *Migration:* read these clashes off `contradictions` and `conflicts` rather than off the
  `:disjoint` exposure entry; assert the declarations and `genl` edges
  `{:strength :monotonic}` to keep the converse refusal; read `:arbitration-truncated` for
  a cut sweep and call `exposed-clashes` for the jointly-visible pairs; `:not-defeasible`
  needs none, since no path threw it.

  *Breaks:* `violations`, `contradictions`, `assert`, `:exposure-truncated`
  *Breaks:* `:not-defeasible`

- **An argument-type mint gives way to a more specific membership by default, and one
  that clashes with a believed disjoint membership is weighed at settle.**
  - **A minted argument type gives way to the membership that says it more specifically
    (`VAELII_PRUNE_SUBSUMED_MINTS`, now on).** `(arg parentOf 1 animal)` over
    `(parentOf Fred Mary)` stores no `(animal Fred)` while `(dog Fred)` is believed, and
    draws it when that membership or the edge behind it leaves. Answers are unchanged;
    stored records change: the starter holds 3,702 sentexes against 4,142 and CxCore
    1,256 against 1,544, `handle-of` and `sentexes-matching` find no withheld mint, and
    `why` shows the subsumption route. [argtypes.md](docs/argtypes.md).
  - **A mint that clashes with a believed disjoint membership is weighed at settle, as a
    rule's conclusion is.** It was dropped as `:disjoint` in one arrival order and stood
    in the other; the stronger class now wins, and an equal `:default` pair stays believed
    and is listed by `contradictions`. Under `:arbitrate`, `assert` stores a `:default`
    sentence it refused `:disjoint`, and the derivation path places the mint where it
    filed a `:disjoint` entry in `violations`.

  *Class:* **Breaking** (stored records a caller reads by handle or pattern, and the
  `:disjoint` refusal and entry).
  *Migration:* `VAELII_PRUNE_SUBSUMED_MINTS=0` stores every mint; read a clashing pair
  from `contradictions`, and assert the membership `:monotonic` for the mint to lose.

  *Breaks:* `handle-of`, `sentexes-matching`, `why`, `VAELII_PRUNE_SUBSUMED_MINTS`
  *Breaks:* `assert`, `violations`, `:disjoint`

- **A rule antecedent on `matchesPattern` or `integer` is computed, as one on `lessThan`
  is.** A forward rule on either derived nothing, and a backward rule on `matchesPattern`
  answered nothing; the join now computes both through `EvaluableProver`, after the
  literals that bind their arguments. A rule whose argument no other antecedent binds is
  refused `:naf-not-closed` by `assert`, `check` and import; `watch` refuses a goal on
  either predicate; and a rule holding either canonicalizes to a different sentence.
  [naf.md](docs/naf.md#fully-bound-to-evaluate),
  [defns.md](docs/defns.md#query-time-the-condition-is-evaluated-not-only-matched).
  *Class:* **Breaking** (a rule whose only binder of an `integer` argument was the
  `integer` literal is refused; such rules canonicalize differently).
  *Migration:* bind the argument with a stored literal in the same rule. A disk store
  written before this change holds such a rule under its old canonical sentence, so the
  stored rule and its re-assert are two handles until the store is reloaded from text.

  *Breaks:* `assert`, `check`, `handle-of`, `watch`

- **The LLM stack is removed.** The `vaelii.host.llm.*` namespaces, the browser's proposal
  panel and its `/propose` routes, the English-reading pipeline, the model judge of derived
  conclusions, their environment variables, the `^:llm` test mark and their doc pages are
  gone. `vaelii.core` and every other browser page are unchanged; the editor's line format
  moves to `vaelii.host.lines`. For more information, contact support@vaelii.com.
  *Class:* **Breaking** (configuration names and browser routes). *Migration:* none in
  the engine; contact support@vaelii.com.

  *Breaks:* `VAELII_LLM_PROVIDER`, `vaelii.llm.provider`, `VAELII_LLM_LIVE`
  *Breaks:* `VAELII_OLLAMA_HOST`, `VAELII_OLLAMA_MODEL`, `VAELII_OLLAMA_GENERATION_MODEL`
  *Breaks:* `VAELII_OLLAMA_NUM_CTX`, `VAELII_OLLAMA_KEEP_ALIVE`, `OLLAMA_HOST`
  *Breaks:* `ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN`, `ANTHROPIC_BASE_URL`
  *Breaks:* `/propose`, `:llm`, `vaelii.host.llm`, `with-model`

- **The taxonomy's closure cache is one weighted LRU the cache manager shrinks, and a
  membership test no longer materializes a closure.** Global and scoped closures share
  `:taxonomy-closures`, bounded at 50,000,000 closure terms (`closure-memo-limit`, scaled
  and pinnable) and trimmed coldest-first under memory pressure; the unbounded global memo
  and the per-pass scoped budget are gone. `vaelii upgrade` installs the memory guard.
  [caches.md](docs/caches.md).
  *Class:* **Breaking** (a cache id `cache-profile` reported, and a dynamic var a caller
  could bind, are gone). *Migration:* pin `:taxonomy-closures` with `set-cache-limit` where
  a caller bound `*scoped-memo-budget*`; the recover benchmark reads
  `vaelii.closure.limit` where it read `vaelii.memo.budget`.

  *Breaks:* `:taxonomy-scoped-closures`, `*scoped-memo-budget*`, `vaelii.memo.budget`

- **`open-kb` ends a failed background rebuild read-only, and refuses a directory that
  cannot hold the lock file by name.**
  - **A `:recover? :background` rebuild writes no record and no index posting.** A rebuild
    placing a conclusion the image lacked wrote the record and its postings from the
    rebuild's thread. Its record store now refuses every write, the rebuild ends as a
    failed one, `rebuild-progress` reports `:failed` naming `recover`, and the KB answers
    from the image with writes refused; it no longer becomes writable when the rebuild
    ends. [storage.md](docs/storage.md#the-reasoning-image).
  - **A disk KB's directory that cannot hold the lock file is refused by name.** A `--dir`
    or `:dir` that is a regular file, or lies under one, is refused `:not-a-directory`,
    and one this process cannot write `:not-writable`, where both threw a
    `java.io.FileNotFoundException` naming `.vaelii.lock`. [storage.md](docs/storage.md),
    [troubleshooting.md](docs/troubleshooting.md#the-disk-kb-will-not-open).

  *Class:* **Breaking** (what such a KB accepts after its rebuild, and the exception
  `open-kb` throws for these two directories).
  *Migration:* call `(recover kb)` when `rebuild-progress` reports `:failed`; it rebuilds
  on the calling thread and writes the conclusion. Catch `ExceptionInfo` and read `:type`
  for the two directories; the `IOException` is its cause.

  *Breaks:* `open-kb` with `:recover? :background`, `rebuild-progress`, `open-kb`

- **A `lein cli` refusal line names its `:type`.** It reads `error: [:naming] naming
  invariant: functor warmBlooded …`, where it was the message alone. A throwable with no
  `:type` reads `[:internal-error]`, an unknown command word `[:unknown-command]`, and the
  REPL's error lines take the same shape.
  [operations.md](docs/operations.md#cli--vaeliicli). *Class:* **Breaking** (the text
  after `error: ` on every refusal line). *Migration:* a script matching the message reads
  it after the bracket, `error: [<:type>] <message>`; a script branching on the kind of
  refusal reads the bracket.

  *Breaks:* `lein cli`

- **koinii's majority resolution counts only ballots an in-process `:proof-tier` ingest
  attested, and the registry's admin is minted by `authenticate`.** Ballots stored under
  any name turned a count into a defeating ruling, and any caller could build an admin.
  `resolve-by-majority` refuses `:koinii/identity-unverified` for an unattested ballot and
  names those in `:unattested`; `identity/admin-principal` is gone; the registry functions
  refuse a principal `authenticate` did not mint (`:koinii/registry-forbidden`). The wire
  contract is unchanged. [koinii.md](docs/koinii.md#identity-and-the-write-boundary).
  *Class:* **Breaking** (a majority over `channel/vote` ballots, and an admin from
  `admin-principal`, are refused).
  *Migration:* cast ballots with `adjudication/cast-ballot` under a `:proof-tier`
  principal from `authenticate`; mint the admin with `(identity/authenticate
  {:claimed-id 'AdminRoot :credential c :admin? true} {:verify-fn f})`, where `f` has a
  three-argument arm that passes it; set `identity/*attest-key*` when ballots must verify
  after a restart.

  *Breaks:* `resolve-by-majority`, `admin-principal`, `register-agent`, `set-trust!`

- **An `ask` deadline stops the argument-preservation claim walk at the row it passes
  on.** `ask`, `ask?` and `ask-within` with a `:max-ms` checked the deadline only between
  answers, so a goal under `transitiveInArg` read the whole predicate extent, or the whole
  product of its reaches, before the deadline was seen. The walk now checks it per row and
  the step answers `:budget-exhausted` (`:timeout` at `ask-within`) after one row at any
  extent. A resumed `ask-within` step runs the interrupted walk to its end. The asymmetry
  check at `assert`, settle and forward chaining read the same claims under no deadline.
  [anytime.md](docs/anytime.md#the-budget), [inherit.md](docs/inherit.md#what-one-question-costs).
  *Class:* **Breaking** (an `ask` that answered past its deadline now refuses).
  *Migration:* widen `:max-ms`, or drop it, where a preserved goal's walk outlasts it.

  *Breaks:* `ask`, `ask?`, `ask-within`, `resume`

- **A `prove` deadline stops the argument-preservation claim walk at the row it passes
  on.** `prove`, `provable?` and `prove-within` with a `:max-ms` checked the deadline only
  between DFS steps or node expansions, so a leaf under `transitiveInArg` read the whole
  predicate extent, or the whole product of its reaches, before the deadline was seen, and
  a leaf that found nothing on the last frame answered `[]` / `false` past the deadline.
  The leaf's walk now checks it per row, on both engines, and the run answers
  `:budget-exhausted` (`:timeout` at `prove-within`) after one row at any extent. A resumed
  `prove-within` step runs the stopped leaf to its end. Forward chaining, settle and the
  asymmetry check at `assert` read the same claims under no deadline.
  [anytime.md](docs/anytime.md#the-budget), [inherit.md](docs/inherit.md#what-one-question-costs).
  *Class:* **Breaking** (a `prove` that answered past its deadline now refuses).
  *Migration:* widen `:max-ms`, or drop it, where a preserved leaf's walk outlasts it.

  *Breaks:* `prove`, `provable?`, `prove-within`, `resume`

- **An ASP solve stops at 100,000 conflicts, so what an `:asp` round decides is the same
  on every machine.** `VAELII_ASP_SOLVE_LIMIT` (default 100,000) bounds one solve by the
  conflicts its search spends, on both backends, and every solve runs on one thread under
  a fixed seed. A solve the limit stops reads as one the time limit stops: the edge solver
  decides nothing that round, an imperative refuses with `:solver-failed`, and a `:label`
  solve holding a model returns it as best-effort. `VAELII_ASP_TIME_LIMIT` stays at 60
  seconds as the wall-clock backstop. [asp.md](docs/asp.md#the-solve-limit).
  *Class:* **Breaking** (a program that needs more than 100,000 conflicts, and decided
  within 60 seconds, now decides nothing).
  *Migration:* set `VAELII_ASP_SOLVE_LIMIT=0` for the wall-clock limit alone, or raise it
  to cover the program.

  *Breaks:* `VAELII_ASP_SOLVE_LIMIT`, `settle`, `do/label`, `do/labeling`, `do/classify`

### Refusals

- **`assert`, `check` and `import!` refuse a malformed rule they stored before.** Each is
  `:not-well-formed`, and an import skips and counts such a rule under that type.
  - **A bare variable as a rule's consequent.** `(implies (holds ?x ?s) ?s)` was stored
    and concluded whatever `?s` bound, forward only; the same holds for a conjunct of a
    head `and`, under a head `exists` or `not`, and in a generator's stamped rule.
    [naming.md](docs/naming.md#literals-wrappers-and-arguments).
  - **A bare variable as an antecedent or exception conjunct.** `(implies (and (dog ?x)
    ?y) (animal ?x))` fired forward as if `?y` were absent and never backward; also under
    `not`, `unknown`, `thereExists` or an aggregate. `(set/forwardRule ?y)` and a
    top-level `(not ?y)` are `:not-well-formed` too.
    [troubleshooting.md](docs/troubleshooting.md).
  - **A `thereExists`, `forall` or head `exists` whose binder is a constant.**
    `(unknown (thereExists Kid (owns ?x Kid)))` read `Kid` as an individual.
    [naf.md](docs/naf.md#fully-bound-to-evaluate).
  - **A bare symbol as the operand of a rule wrapper or a `not`.** `(set/defaultRule Foo)`
    threw an untyped `IllegalArgumentException`, and `(not Foo)` was stored and answered
    `(not ?x)`.
  - **A rule wrapper combination the record cannot hold.** Two direction wrappers, an
    assumption and a hard constraint, a hard and a soft constraint, or a direction or
    default wrapper on a choice or constraint rule; a `:direction` opt there is
    `:unknown-option`, and `check` predicts each. A repeated wrapper is still accepted.
    [canonicalization.md](docs/canonicalization.md#rule-wrappers-become-fields).

  *Class:* **Refusal** (each of these rules was stored, or threw untyped).
  *Migration:* conclude the dotted rest, `(implies (holds ?x (?pred . ?args)) (?pred .
  ?args))`, for a variable consequent; write a variable antecedent as a literal; write a
  variable in a quantifier binder; assert the fact or rule a wrapper was meant to hold;
  keep one direction and one head wrapper per rule, and none on a choice or constraint
  rule.

  *Breaks:* `assert`, `check`, `import!`, `thereExists`, `forall`, `set/assumptionRule`
  *Breaks:* `set/hardConstraint`, `set/softConstraint`

- **A handle that names no stored sentex, and a sentence or context that is not one, are
  refused.**
  - **`assert` and `check` refuse an `except` naming a handle no sentex is stored under.**
    Handles are allocated in assertion order, so such an except hid whichever sentex
    received the handle next. It is `:unknown-handle` now, and the except graph is
    acyclic.
    [contexts.md](docs/contexts.md#except-removing-visibility-down-a-context-subtree).
  - **`handle-of` refuses a sentence or a context that is not one, where it answered
    `nil`.** A number, map, string or `nil` sentence, and a `nil`, numeric, non-ground or
    variable context, are `:shape`; koinii's `dereference` reports such a marker as
    `:malformed`. [api.md](docs/api.md), [koinii.md](docs/koinii.md).

  *Class:* **Refusal** (an except asserted before its target was stored; a malformed
  `handle-of` call answered `nil`).
  *Migration:* assert the except's target first and name the handle `assert` returned for
  it; pass `handle-of` the context the sentence is stored in, and ask a variable context
  with `sentexes-matching`.

  *Breaks:* `assert`, `check`, `edit!`, `handle-of`

- **A function's argument declarations are read over the inputs of its applications.**
  `(arg InputGapFn 1 integer)` was stored and read by nothing, so
  `(inputGapObserver (InputGapFn "not-an-integer"))` was admitted (#78). Each
  application's inputs are now checked against its function's `arg`, `genlArg`,
  `quotedArg`, `interArg` and covering declarations at any depth; the refusal carries the
  arm's `:type` and `:application`, a `quotedArg` position is not descended into, and a
  reifiable function's inputs are read before `assert` mints the application.
  [docs/argtypes.md](docs/argtypes.md#relation-wide-declarations-and-the-runtime-boundary).
  *Class:* **Refusal** (a fact whose application is given an input its function's
  declarations forbid, admitted before, is refused).
  *Migration:* correct the input, or the function's declaration where the declaration is
  what is wrong; a fact already stored is not re-read, as for every argument constraint.

  *Breaks:* `assert`, `check`

- **A disk store refuses a damaged log frame and every call after it stops, where it
  deleted records or threw untyped.**
  - **A frame inside a log the open reads whole that does not decode is refused, not read
    as the log's end.** One damaged `tokens.log` frame ended the dictionary, and the open
    tombstoned every record citing a later token (27 of 31 in the reproduction). The open
    now refuses `:damaged-frame` naming the file, offset and frame, and deletes nothing; a
    damaged `kv.log` frame rebuilds the index, and one in the operation log declines a
    restore. The last frame is still read as a torn tail, and the warning names
    `:malformed-record`. [storage.md](docs/storage.md),
    [defenses.md](docs/defenses.md#torn-tail-recovery-reads-lengths-not-frames).
  - **A disk store that stops refuses every call after it with `:store-unusable`.** An
    interrupt closed a file channel and every later call threw `ClosedChannelException`
    or `IOException: Stream Closed` with no `:type`. A closed channel, a failed write or
    fsync, and `close!` now latch the store with a `:reason`, reads included, until the
    directory is opened again; a call on a KB after its `close!` is refused.
    [api.md](docs/api.md#batched-assertion),
    [storage.md](docs/storage.md#a-store-that-stops),
    [troubleshooting.md](docs/troubleshooting.md).

  *Class:* **Refusal** (an open that tombstoned records after a damaged token frame, and a
  read after `close!` or after a store stopped, are refused).
  *Migration:* nothing for the damaged frame: the open this refuses deleted records a
  working caller still held. Catch `:store-unusable` where a disk write's
  `ClosedChannelException` or `IOException` was caught, and open the directory again.

  *Breaks:* `open-kb`, `close!`, `ClosedChannelException`, `Stream Closed`

- **`open-kb`, `set-cache-limit` and `lein cli --dir` refuse an option value that names
  nothing they can act on.**
  - **`open-kb` refuses `:overlay` on one axis alone, naming the half to change.**
    `:records :overlay` threw an untyped message and `:index :overlay` over plain records
    opened a KB whose index named handles its records lacked; both are `:unknown-backend`
    with `:mismatch :illegal-pair`. [overlay.md](docs/overlay.md).
  - **`open-kb` refuses a `:space`, `:dir` or `:base-stores` value that names no store.**
    A string, `nil`, negative or fractional `:space`, a blank or non-path `:dir`, and a
    `:base-stores` that is not open stores each opened the wrong store or threw untyped;
    each is `:unknown-option` (`:mismatch :bad-value`), in a fork's halves too.
    [storage.md](docs/storage.md).
  - **`set-cache-limit` refuses a pin on a cache no pin moves.** A pin on
    `:symbol-pool`, `:taxonomy-scoped-closures` or a nil-bound cache was recorded and
    enforced nowhere; it is `:unknown-option`, and clearing with `nil` is accepted.
    [caches.md](docs/caches.md#tuning-the-bounds).
  - **`lein cli --dir` refuses a directory whose parent does not exist, and creates
    nothing.** A mistyped `--dir` answered `[]` at exit 0 and left an empty store; it is
    `:unknown-source` now. [operations.md](docs/operations.md#cli--vaeliicli).

  *Class:* **Refusal** (each value opened a store, recorded a pin or created a directory
  that did nothing the caller asked).
  *Migration:* spell a fork `{:backend :overlay :base … :overlay …}`, or use `fork`; name a
  space with a whole number, or a keyword, symbol or vector for a private one, and drop a
  `:space nil` or `:dir nil` to take the default; drop a refused `set-cache-limit` call
  (`*symbol-pool-limit*` and `*scoped-memo-budget*` bound those two); create a `--dir`
  parent first (`mkdir -p`).

  *Breaks:* `open-kb`, `:overlay`, `:space`, `:dir`, `:base-stores`, `set-cache-limit`
  *Breaks:* `--dir`

- **Starting either server from code with an address and no token is refused.**
  `vaelii.serve/start` and `vaelii.web/start` with a non-loopback `:host` served `POST
  /op` and every browser route open, and `vaelii.web/start` ignored `VAELII_API_TOKEN`.
  Both refuse `:unauthorized` before anything binds, and `vaelii.web/start` takes `:token`
  (default `VAELII_API_TOKEN`). [operations.md](docs/operations.md).
  *Class:* **Refusal** (a public `start` with no token, served open before, is refused).
  *Migration:* pass `:token`, or set `VAELII_API_TOKEN`, or bind loopback.

  *Breaks:* `vaelii.serve/start`, `vaelii.web/start`

- **The browser refuses an unreadable parameter and a write or unload that would act on a
  KB being released.**
  - **Every browser parameter that does not read is a 400 page naming it.** An unreadable
    goal, term, context, handle, path id or choice was answered as if absent, and `POST
    /edit` with a stale handle asserted its text as a new sentence. A write route reads
    its parameters before it takes the writer, a stale `/edit` handle is `:unknown-handle`,
    and `/find` says a pattern past 128 characters is too long.
    [web.md](docs/web.md#a-parameter-the-page-cannot-read-is-a-400-not-a-default),
    [caches.md](docs/caches.md#tuning-the-bounds).
  - **A browser write waiting for the write monitor does not land on a KB unloaded while
    it waited.** It answered 200 into cleared memory or a closed store; the page says
    "Nothing was written", `/op` answers 404 `:not-found`, a `/chain` job fails naming the
    unload, and a parked poll answers `:unknown-subscription` at once.
    [catalog.md](docs/catalog.md#unloading-never-deletes-an-on-disk-kb),
    [operations.md](docs/operations.md), [feed.md](docs/feed.md#across-the-wire).
  - **The browser's unload refuses a KB a job is writing, and answers at once.**
    `/kbs/unload` waited for the whole job, and `unload!` with no `:run-in` released the
    stores under it; it refuses `:still-writing` now, and `reset-registry!` stops every
    running job first. [troubleshooting.md](docs/troubleshooting.md).

  *Class:* **Refusal** (browser requests with an unreadable parameter, answered 200, are
  refused 400; a write, `:watch`, `:poll` or unload over a KB being released is refused).
  *Migration:* send a parameter in the form the page's own controls send it, or leave it
  out where the route has a default; load the KB again and repeat the write, or `:watch`
  again on the KB now active; cancel the job, or wait for it, then unload.

  *Breaks:* `/levels`, `/inference`, `/network`, `/term`, `/find`, `/assert`, `/edit`
  *Breaks:* `/edit/preview`, `/retract`, `/sentex/:id`, `/why/:id`, `/justification/:id`
  *Breaks:* `/demo`, `/reasoning`, `/jobs/cancel`, `/kbs/load`, `/kbs/unload`
  *Breaks:* `/kbs/activate`, `/kbs/export`, `/caches/scale`, `POST /op`, `unload!`

- **`do/label` and `do/classify` refuse a non-empty `<Into>Class` that `do/classify` did
  not mark, where they cleared it.** A classification carries an inert `(classificationOf
  <Into>Class <Into>)` marker, and only a marked one is replaced; an unmarked one is a
  context of the caller's that shares the name, or a classification written before the
  marker, and is refused `:labeling-run-blocked` with the context under `:unmarked`.
  [solving.md](docs/solving.md), [troubleshooting.md](docs/troubleshooting.md#dolabel-refuses-to-re-run).
  *Class:* **Refusal** (a run over an `Into` whose `<Into>Class` holds only inert or
  unbelieved sentexes cleared them, and is refused).
  *Migration:* retract the extent of a classification written before this release, or
  name a different `Into`; a context of your own named `<Into>Class` keeps its content.

  *Breaks:* `do/label`, `do/classify`

### Additions

- **`rebuild-progress` reports a background belief rebuild's step, its time and the image
  it replaces.** While `:recover? :background` rebuilds belief, `(rebuild-progress kb)`
  answers the step running of eight, the time since the rebuild began, the image's and the
  running build's source digests, and a fraction against the recover the image records; nil
  when no rebuild runs. Each step logs at `:info`, the image stamp carries the recover's
  step timings, and the browser's rebuild banner shows a progress bar, the step, the image's
  source and how to avoid the rebuild next time. [api.md](docs/api.md),
  [storage.md](docs/storage.md#the-reasoning-image). *Class:* **Additive**.

- **Every temporal thing has six named points, and the point network orders them.**
  `CxTime` declares `StartFn`, `EndFn`, `EarliestStartFn`, `LatestStartFn`,
  `EarliestEndFn` and `LatestEndFn`. The point network orders one thing's points and
  calendar moments by their fields, the interval network reads Allen relations off the
  points, and the `:includes-instant` reasoner answers `(includesInstant X t)` and its
  negation, so `argue` answers `:unknown` for a moment inside an uncertain bound. A
  `qcn-kb` calculus may name a node test and a narrowing over its node set.
  [time.md](docs/time.md), [qcn.md](docs/qcn.md). *Class:* **Additive**.

- **`set/solveRule` runs a rule inside a solve.** A `do/label` program held only choices
  and nogoods, so a constraint could not bite downstream of a choice. A `set/solveRule`
  rule is ground into the program as `h :- b`, recursively and with default negation, and
  each labeling lists its derived atoms under `:derived`. The wrapper adds `:solve` to the
  rule's `:engines`; a choice or constraint rule and a `set/defaultRule` take none.
  Grounding is semi-naive, so its cost per derived atom holds flat with chain length
  (`lein perf`'s `solve-rule-grounding`).
  [solving.md](docs/solving.md#solverule--a-derived-atom-inside-a-solve).
  *Class:* **Additive**.

- **The browser takes extensions, the chaining funnel continues past 200 rules, and seven
  reads are daemon ops.**
  - **The browser takes extensions.** `vaelii.web/register-extension` files routes under
    `/ext/<name>/`, a term-page panel, a start hook and a stylesheet and script;
    `unregister-extension` removes them. `:post` routes are origin-checked, `:write` ones
    run under the write guard, and a malformed map is `:unknown-option`. The shim
    publishes `local-kb`, `read-form`, `render-form`, `term-link`, `consequences` and
    `stored-sentexes`. [web.md](docs/web.md#extensions).
  - **The chaining funnel continues past its first 200 rules.** `/funnel` ends in a
    sentinel that fetches the next 200 from `/funnel/rows`.
    [web.md](docs/web.md#long-lists-continue).
  - **Seven reads are daemon ops**: `:query-status`, `:find-sentexes-all`,
    `:subsumption-status`, `:subsumption-statuses`, `:functional-at-instant-violations`,
    `:all-functional-at-instant-violations` and `:last-program`, each with a
    `vaelii.client` wrapper. operations.md states which `vaelii.core` fns are not ops and
    why. [operations.md](docs/operations.md#daemon--vaeliiserve).

  *Class:* **Additive**.

- **A loaded store or dump states this engine's shipped spindle, and an unreadable text KB
  form names its file and line.**
  - **A loaded store or dump states this engine's shipped spindle.** The browser's catalog
    syncs a loaded KB's CxCore, `kb/upper/` and `kb/middle/` contexts to what
    `starter/load-into` produces before its entry reads `:done`, retracting a premise the
    engine does not ship and syncing only the layers the KB has; the report is the entry's
    `:spindle`. New: `vaelii.host.spindle`, `text/premise-entries`, and a `loaded` callback
    on `starter/load-into`.
    [catalog.md](docs/catalog.md#a-loaded-kb-states-this-engines-spindle).
  - **A text KB form the EDN reader refuses is `:unreadable`, naming the file and the
    line.** `load-text!` and a path `kb-diff` raised the reader's untyped
    `RuntimeException`; the refusal carries `:file` and `:line`, and its message does not
    quote the file. [kbs.md](docs/kbs.md#text-you-exported-yourself).

  *Class:* **Additive** (a `:type` where none was, and a sync on load).

### Fixes: data and storage

- **A write that is refused, or whose store stops, leaves the store as it was or reports
  what landed.**
  - **A refused `assert` leaves the KB as it found it.** A throw out of `assert` left the
    writes made before the refusing check: a minted NAT constant with its `termOfUnit`
    and derivations, a head existential's `reifiable_function` declaration, a fact
    believed with its settle skipped, and rules stored before an inline `exceptWhen` was
    refused `:exception-not-closed` or `:not-stratified`. The call's writes are now taken
    back with the undo `edit!` runs, and a change-feed listener sees none of them.
    [api.md](docs/api.md#validating-without-writing),
    [feed.md](docs/feed.md#one-settle-is-one-event).
  - **An assert whose index write is refused leaves no record.** On `:disk-log`, a
    `:compaction-failed` refusal left the appended record, which a reopen believed as a
    premise whose forward rules never fired. The record is deleted before the refusal
    travels. [storage.md](docs/storage.md).
  - **An index write refused part-way leaves no posting.** On `:memory-columnar`, a
    posting outlived its deleted record, so `handle-of` found a handle with no record.
    The postings are taken out with the record.
    [storage.md](docs/storage.md#a-store-that-stops).
  - **An assert whose store stops after the write landed returns its handle.** It threw
    although a reopen held the fact and its consequences; the stop is now logged at
    `:error` naming the handle, and the next call is refused.

  *Class:* **Fix**.

- **An import stores what `assert` would store, and a refused import leaves nothing.**
  - **An engine-dialect dump's facts import as themselves.** `import-dump` read every
    frame carrying `:antecedent` as its own dialect, so each fact decoded to a nil
    sentence and collapsed onto the first in its context, which lost all but a fraction of
    a percent of such a dump's facts. A frame is ours when it carries `:sentence`, or an
    `:antecedent` beside a `:varmap`. [foreign.md](docs/foreign.md).
  - **An import refused for its dump's content leaves the destination empty.** A frame
    refused mid-stream left the frames before it stored, a retry was refused
    `:not-empty`, and a `:disk-log` reopen believed the prefix. The import now empties
    the record store and the index before the refusal travels, and a foreign reader with
    no `:replay-belief!` is refused before the first write.
    [api.md](docs/api.md#three-formats-and-which-question-each-answers).
  - **`import!` stores an `or` antecedent or an `and` consequent as one rule per form.**
    It stored one record holding the connective, which a later `assert` did not dedup
    against and which derived nothing; the summary counts the expansion in `:expanded`,
    `{:frames n :records n}`.
  - **`import!` skips and counts every frame `assert` refuses.** A rule that is not
    range-restricted, carries a `do/` imperative or an irreducible `or`, an `ist` or
    `(not A B)` or top-level `and` frame, an open literal, a variable antecedent functor
    and a sentex in a query context were stored believed with `:refused` at zero. Each
    is counted in `:refused` under the `:type` `assert` raises (`:not-range-restricted`,
    `:not-assertible`, `:not-well-formed`, `:not-ground`, `:not-indexable`, `:shape`), on
    both import paths; an `(ist Ctx S)` frame is stored as S in Ctx.
    [naming.md](docs/naming.md#whose-invariants-the-two-policies).

  *Class:* **Fix**.

- **Store reads, restores, bounded reads and closes do what the storage docs state.**
  - **A disk record read cannot put a deleted record back in the hot-record cache.** The
    put ran after the read lock was released, so a retraction landing in between was
    overwritten until eviction; the put is now made under the lock.
    [storage.md](docs/storage.md#the-single-writer-contract).
  - **A read beside a fork's writer never answers the base's record behind an
    override.** Each write of the fork record store is ordered so a read on another
    thread answers the fork before the write or after it.
    [overlay.md](docs/overlay.md#the-merge-model--record-half).
  - **An operation-log restore declines when a frame fails rather than refuses.**
    `replay!` skipped a frame that died of an `Error` or an I/O fault and answered
    `:restored true` for a KB missing the write. Only an `ex-info` is skipped now.
  - **A store's `format.edn` past the manifest byte bound is refused at `open-kb`.**
    `format.edn`, `layout.edn`, `records.edn` and a belief image's `manifest.edn` are read
    under the bound: past it is `:manifest-too-large`, or `:stale` for `layout.edn`, and a
    cut `records.edn` is `:malformed-manifest`.
    [storage.md](docs/storage.md#a-directorys-sentinel).
  - **Unloading an attached adapter store closes it.** A `:sqlite` or `:pg-disk-log`
    store kept its file or connection open until the JVM exited; the unload now closes
    every backend but memory.
    [catalog.md](docs/catalog.md#unloading-never-deletes-an-on-disk-kb).
  - **`close!` ends the KB's change feed.** `watchers` answers empty afterwards, where it
    listed each listener as live. [feed.md](docs/feed.md#across-the-wire).

  *Class:* **Fix**.

- **A reasoning image installs when it is sound, and is declined when it is not.**
  - **A reasoning image holding a clash with a derived side installs.** The image wrote
    the clash's justifications as `Justification` records, a class its own reader
    refuses, so every open declined it as `:unreadable` and paid a full recover. It now
    writes field maps.
  - **A reasoning image that names a class is declined, not constructed.** `state.nippy`
    and `network.bin` go through the class-name check every other file read goes
    through, and a refused image falls back to a recover.
    [storage.md](docs/storage.md#a-file-names-no-class).
  - **An export whose KB moved during the walk writes no reasoning image.** An image
    stamped after a concurrent write installed with a premise OUT that a recover
    believes; the export now declines the image as `:not-writable` when the change clock
    moved.

  *Class:* **Fix**.

- **A fork whose `:base` and `:overlay` name one store is refused before it writes.**
  - **A `:base-stores` fork from a `:memory` KB with an `:overlay` naming that KB's space
    is refused `:base-is-overlay`.** It opened and wrote its facts into the base, where
    the same pair over one `:disk` directory was already refused.
  - **The `:disk` refusal leaves the directory as it was.** It ran after the base's store
    opened, and left an empty directory holding `.vaelii.lock`, `index/` and `records/`.

  [overlay.md](docs/overlay.md).
  *Class:* **Fix** (overlay.md states that both halves naming one store are refused).

- **A failure path releases the lock, stream or monitor its happy path took.**
  - **A lock whose holder-tag write throws is released, or refused by name.** The unwind
    swallowed a failed `.release`, so the directory read as free while this JVM could
    still hold its OS lock, and the next open blamed another channel. The failure is
    logged and the directory is refused `:unreleased`.
    [storage.md](docs/storage.md#the-single-writer-contract).
  - **A `close!` waiting on a background belief rebuild blocks no other directory.** It
    waited for the rebuild to stop while holding the process-wide store registry's
    monitor, so every other disk `open-kb` and `close!` in the process waited out the
    rebuild's settle too. [storage.md](docs/storage.md#the-reasoning-image).
  - **An import holds no frame its walk has passed.** The close each stream reader kept
    for the walk held the seq's head, so every frame read stayed in the heap until the
    stream ended.
  - **A foreign reader's `:replay-belief!` that throws leaves no stream open.** A stream
    it opened through `:read-fn` and did not read to the end stayed open until GC; the
    importer now closes every such stream when the replay returns or throws.
    [foreign.md](docs/foreign.md).

  *Class:* **Fix**.

### Fixes: security

- **The browser and the daemon close three ways a request reached what it should not.**
  - **A sandbox context is named from a digest of its session token.** The name carried
    the token, which is the session cookie, so any session could read another's from
    `/find` and write its sandbox. A sandbox opened before this change keeps its old name
    and belongs to no session. [web.md](docs/web.md#somewhere-safe-to-be-wrong).
  - **No other site can frame a browser page.** Every response carries
    `X-Frame-Options: DENY` and `Content-Security-Policy: frame-ancestors 'none'`, since
    a POST from a framed page passes the origin check.
  - **A daemon request whose body ends before its `Content-Length` answers 400
    `:not-edn`,** where it answered 500 `:internal-error`.

  *Class:* **Fix**.

### Fixes: answers

- **Equations are answered as stated, and a denial or `except` of one holds.**
  - **A stated equation is answered.** A believed `sameAs`, `equals` or `rewriteOf` was
    denied by `ask?`, `ask`, `prove` and `sentexes-matching`. `ask` now answers `sameAs`
    and `equals` from the equality closure, so symmetric, reflexive and chained forms
    hold and `(sameAs A ?y)` enumerates `A`'s class; a ground `equals` a schematic
    equation normalizes to one form answers true.
    [equality.md](docs/equality.md#answering-an-equation).
  - **A denied instance of a schematic equation is carved out of the equation, and keeps
    its spelling.** A believed `(not (equals (fatherOf (fatherOf Tom)) (grandfather_of
    Tom)))` blocks that instance's rewrite for the readers that see it, where `ask?`
    answered both the instance and its denial true; the denial is no longer restated as
    a denial of reflexivity. [equational.md](docs/equational.md#a-denied-ground-instance).
  - **An `except` of an equality leaves its context the facts the equality restated.**
    Excepting a schematic equation or a ground `sameAs` / `equals` / `rewriteOf` left a
    known-true fact answered under neither spelling; the original is now read as
    spelled, including below the fact's context, and `except-merge-scaling` holds the
    cost to the data the except reaches.
    [equational.md](docs/equational.md#an-except-of-an-equation),
    [equality.md](docs/equality.md), [nmtms.md](docs/nmtms.md).
  - **A merge or lift mark that revives reaches the facts stored while it was OUT.** A
    `functional`, `functionalInArg`, `anti_symmetric` or `decontextualized_predicate`
    mark revived after a denial merged or lifted none of them. Past
    `*exposure-instance-budget*` a revived `genl` edge files
    `:genl-edge-revival-truncated`.
    [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing),
    [contexts.md](docs/contexts.md#decontextualized_predicate-a-fact-that-belongs-to-the-kb-not-to-one-theory).
  - **A type or merge that descends over two `genl` routes survives either route's edge
    going,** where `isa?` answered false while `ask?` answered true.
    [argtypes.md](docs/argtypes.md#the-entailment-as-a-justified-datum).

  *Class:* **Fix**.

- **A forward rule concludes what a query over the same knowledge answers.**
  - **A `genl` or `genlCx` antecedent reads the closure a query reads.** A rule on
    `(genl ?a ?b)` fired on neither the reflexive pair nor a two-edge pair; with an end
    bound the join now reads the cached closure, and with both ends open it waits for
    the literal that binds one.
    [inference.md](docs/inference.md#a-genl--genlcx-antecedent-reads-the-closure).
  - **A conclusion stores an application's constant, as `assert` does.** A derived
    `(FruitFn AppleTree)` stayed a compound that `ask`, `query` and joins missed; the
    chainer reifies each ground reifiable application, and a mint that refuses files
    `:mint-refused` in `violations`. [nat.md](docs/nat.md#derivation-path).
  - **A rule walks a transitive predicate where its declaration meets the hops,** and the
    firing is placed and withdrawn with the declaration.
    [inference.md](docs/inference.md#what-a-computed-answer-rests-on).
  - **A `genlCx` edge arriving last pairs rules and facts every lower context sees.** It
    re-joined only `super`'s ancestors and `sub`'s descendants, so the same sentences
    concluded `(flies Tweety)` in one arrival order and nothing in another; it now also
    joins two facts across a diamond and hands a rule the network, transitivity or
    preservation that licenses its antecedent.
    [contexts.md](docs/contexts.md#the-consumers-and-what-each-of-them-may-reach).
  - **A shorter `genl` route arriving after a firing replaces the route the firing
    named,** so `why` and `supporting-justifications` answer the same in both orders.
    [nmtms.md](docs/nmtms.md).
  - **A variable-functor consequent is held to the naming policy at each firing.** Under
    `:naming :strict` the conclusion `assert` refuses is dropped and reported as a
    `:naming` violation. [naming.md](docs/naming.md).

  *Class:* **Fix**.

- **Time and qualitative reasoning answer in every arrival order and after every
  inconsistency.**
  - **An unsatisfiable point or metric network makes the interval network reading it
    unsatisfiable,** so a cycle of instants or a negative `temporalDistance` cycle
    withdraws the Allen firings drawn from it (`stp/unsatisfiable-narrowing`).
    [qcn.md](docs/qcn.md), [time.md](docs/time.md), [stp.md](docs/stp.md).
  - **`includesInstant` answers in conjunctions, forward rules, stored facts and negated
    support-carrying goals.** An open literal is planned after its binders, a stated
    fact or its negation is answered beside the network, and `solve-with-support`
    agrees with `solve`. [time.md](docs/time.md), [inference.md](docs/inference.md).
  - **A moment spelled as a term is its own six points.** `(StartFn (InstantFn …))` is
    that moment; a symbol argument keeps extent.
  - **Point rules fire in every order.** An instant fact re-joins the rules of every
    calculus it moves, and a rule naming a point no fact states is enumerated in full on
    each re-join. [qcn.md](docs/qcn.md).
  - **An unsatisfiable point network is reported once, whatever nodes the queries
    name,** where ten queries filed ten `:qualitative-inconsistency` entries.
  - **The interval network reads the point network's Allen relations off one closed
    network** (`qcn-kb/closure-with-support`): at n = 80 chained things the first read
    after a write takes 493 ms against 10,435 ms.
  - **A rebound `*quantity-tolerance*` reaches the metric-time verdict.**
    [stp.md](docs/stp.md).
  - **A qualitative product, and a sum of like signs, no longer rest on a stored
    magnitude comparison,** so retracting an unrelated comparison withdraws no firing.
    [sign.md](docs/sign.md).
  - **An exception a calculus answers by composition is re-decided when a composing fact
    arrives or leaves.** A rule excepted on `(spatiallyDisconnected ?x Room)` kept its
    firing on `Canary` after `(nonTangentialProperPart Canary Cage)` and
    `(spatiallyDisconnected Cage Room)` made the network entail the exception, in either
    order, unless the rule also joined on the calculus; a fact on a sub-predicate of a
    calculus predicate, and the `genl` edge making it one, missed it too. Such a rule
    re-decides every firing on each arrival that moves the calculus, about 13 µs a
    firing.
    [exceptions.md](docs/exceptions.md#five-channels-a-declaration-or-a-fact-reaches-an-exception-through-sideways).
  - **A fact on a sub-predicate of a calculus predicate, and the `genl` edge making it one,
    move the rules joining on the calculus.** A rule on `(spatiallyDisconnected ?x ?y)`
    missed the firing such a fact composed into its antecedent, and kept one it made the
    network contradict, unless the fact and the edge arrived before the rule. Retracting
    the edge withdraws a firing the network drew through it.
    [qcn.md](docs/qcn.md#what-a-registered-prover-is-reachable-from).

  *Class:* **Fix**.

- **Choice and constraint rules are solved and fingerprinted as written.**
  - **A negated constraint literal naming an atom the program lacks holds.** A hard
    constraint dropped every such binding, so a requirement nothing could meet read as
    met; a nogood left with no atom now reports `:unsatisfiable`.
    [solving.md](docs/solving.md).
  - **A dump's index fingerprint reads a choice or constraint rule's head.**
    `record-hash` folds in a non-`:derive` effect, so an index describing a different
    rule head no longer validates; a dump written by an earlier build with such a rule
    rebuilds its index on import. [storage.md](docs/storage.md).

  *Class:* **Fix**.

- **A `preview` reads and restores the state it was given.**
  - **Removing a `genl` or `genlCx` edge reads the closures without it.** `genl?`,
    `genls` and `sees?` answered through the suspended edge inside the preview's
    settle. [nmtms.md](docs/nmtms.md#what-settle-finish-reconciles).
  - **Re-asserting a premise at a stronger class and removing it leaves the class it
    found.** The rollback puts every audited handle back at the state the batch found,
    where `h` stayed `:monotonic`. [preview.md](docs/preview.md#the-mechanism).

  *Class:* **Fix**.

- **`check` predicts the refusal the write makes, and two options read as documented.**
  - **`check` and `check-edit` report the `:not-stratified` and `:unrecovered-kb`
    refusals** only the writes made.
  - **`check` agrees with `assert` about an inline `exceptWhen` and a reifiable NAT,**
    reading a minted application as its constant and an unminted one as the constant
    `assert` would mint. [nat.md](docs/nat.md#typing-an-application-that-is-never-minted),
    [api.md](docs/api.md#validating-without-writing).
  - **`assert` and `check` refuse an `exceptWhen` around a fact as `:not-well-formed`,**
    where `assert` threw a bare `IndexOutOfBoundsException`.
    [exceptions.md](docs/exceptions.md).
  - **`abduce` reads a nil `:max-hypotheses` as no bound,** where it threw a
    `NullPointerException`. [abduction.md](docs/abduction.md).

  *Class:* **Fix**.

- **The shipped content loads as documented.**
  - **The starter loads with an empty violations ledger.** It filed
    `:exposure-truncated` and `:arbitration-truncated`, so `/stats` on the browser's
    default KB reported content undecided; both retroactive sweeps now skip a whole-store
    region, with belief unchanged.
    [nmtms.md](docs/nmtms.md#which-entry-point-the-content-came-through).
  - **A catalog corpus load with no `:profile` loads at `ontology`, as the card does,**
    in `load-dir` and `load-source`. [catalog.md](docs/catalog.md).

  *Class:* **Fix**.

### Fixes: clashes and order independence

- **Inherited, preserved and permuted claims are decided the same way in every arrival
  order and at every context that sees their grounds.**
  - **A stored claim denied by a known-true claim read by argument preservation is decided
    where the general claim comes into view.** The clash was judged at the stored claim's
    own context only, so a reader seeing both contexts believed the default with nothing
    in `conflicts`, `contradictions` or `violations`. The pairing is now asked from the
    most general contexts that see every context a denying reading rests on
    (`inherit/denial-contexts`).
    [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).
  - **An `anti_transitive` chain whose three steps sit in three contexts is decided where
    all three are seen.** Vantages were taken one partner context at a time, so a context
    seeing all three steps believed them with `contradictions` empty. The vantages now
    include the chain's common descendants (`settle/chain-contexts`).
    [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).
  - **A claim read by preservation over several routes opposes at its strongest route.**
    The converse was refused in one edge order and stored as an `:inherited` dilemma in
    the other; the assert check and the settle now take the reading whose weakest member
    is strongest, so both orders refuse it.
  - **A `genlCx` edge that brings a stored claim and the claim denying it by preservation
    into one reader forms their inherited clash.** With the edge written last no conflict
    was reported; the inherited-clash memo now keeps the claim for that reader to ask
    again. [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).
  - **An `:asymmetric` pair whose inherited claim has no reading stays an arbitrable
    violation.** `checks/inherited-opposing` gave the claim an empty reading, which the
    settle's pairing ignored; the pair is now arbitrated over the claim alone.
  - **A permuting mark is read from a context that sees no statement of it as the store
    reads it there.** `has-prop?` now answers `:symmetric` and `:commutative` from any
    context, and a firing through a mirror is placed by its rule and matched facts
    (`chain/placement-antecedents`), so it stands in both arrival orders.
    [contexts.md](docs/contexts.md#a-context-outside-the-spindle).
  - **Retracting or defeating a permuting mark hands back each spelling as it was
    written.** After `(symmetric bRel)`, `(bRel Zed Amy)` and the mark's retraction, the
    fact as written answered `false` and its mirror `true`. Each row records its written
    spellings under the provenance entry `:vaelii/spellings`, which `core/provenance`
    does not return and `add-provenance` cannot overwrite.
    [canonicalization.md](docs/canonicalization.md#a-mark-leaving-hands-the-spellings-back).
  - **`functionalInArg` is lifted like `functional`.** A mark stated in one theory merged
    fillers below that theory alone; CxCore now declares the lift, so it merges from every
    context. [contexts.md](docs/contexts.md#where-a-relation-property-is-read-from).

  *Class:* **Fix** (conflicts, belief and firings that varied with arrival order).

- **Clash arbitration reaches the same beliefs in every arrival order.**
  - **A budget-cut arbitration sweep resumes in later settles until its reach is
    decided.** Pairs past a `tax/*exposure-instance-budget*` cut stayed undecided, so
    arrival order decided them; each later settle continues the sweep, and every settle
    with an unfinished sweep files `:arbitration-truncated`.
    [taxonomy.md](docs/taxonomy.md#what-a-declaration-reaches-back-over).
  - **A refuted cover is arbitrated like a disjointness clash.** Under `:arbitrate` it was
    refused even against `:default` content, and never reported with the `covering`
    declaration written last. It now refuses only under `:refuse` or when every ground is
    `:monotonic`, and is otherwise a nogood `settle` arbitrates.
    [taxonomy.md](docs/taxonomy.md).
  - **A `genl` edge relating two of a type's supertypes withdraws the metatype or
    partition clash they separated.** `(genl car_t boat_t)` left the dilemma reported. A
    KB with a `sibling_disjoint` mark also no longer re-derives every standing clash on
    every `genl` edge. [nmtms.md](docs/nmtms.md#how-a-settle-finds-the-clashes).
  - **Retracting a denial of a `genl` edge that released a decided clash decides the clash
    again.** Both memberships stayed believed where the KB that never held the denial
    believes the known-true one alone.
  - **A `rewriteOf` merge and its retraction move the definitional clashes between the
    spellings they retire and give back.** A settle re-asks the sentexes naming a term
    whose equality class moved and the handles whose supersession flipped.
  - **A late `irreflexive` or `anti_symmetric` mark reports the stored facts it
    convicts.** `violations` names them, one `:irreflexive` or `:anti-symmetric` entry per
    marked predicate (`:via` `:count` `:sample` `:message`), in every arrival order; a
    sweep the instance budget cuts files `:unarbitrable-reach-truncated`.
    [nmtms.md](docs/nmtms.md).
  - **A stratification refusal names the same cycle in every arrival order.** `:cycle` and
    the message named the cycle met first in handle order; the walk now reads content
    order. [exceptions.md](docs/exceptions.md#stratification).
  - **A forward run's `:max-depth` reads the same derivation depths whatever order a
    premise mark arrived or left in.** Both `:tms` networks re-solve the depths a removal
    or a lowered node reaches. [nmtms.md](docs/nmtms.md#derivation-depth).

  *Class:* **Fix** (belief and clashes that varied with arrival order).

- **With `VAELII_PRUNE_SUBSUMED_MINTS=1`, the mints a KB stores no longer depend on arrival
  order or on a restart.**
  - **A `genl` or `genlCx` edge arriving after a mint withdraws it as the same edge
    arriving first withholds it.** A membership arriving with the switch on looks the
    term up in a roster of stored mints; `lein perf` gains
    `mint-withdrawal-under-busy-term`.
  - **A recovered KB draws a withheld mint back when what displaced it leaves.** The
    withholding lived in memory and a restart lost it; the settle now re-derives the mints
    from the facts naming the departing record's term. `lein perf` gains
    `settle-beside-withheld-mints`.

  [argtypes.md](docs/argtypes.md).
  *Class:* **Fix** (stored records that varied with arrival order or a restart).

### Fixes: concurrency

- **A reader thread beside the writer reads one settle's state and caches nothing
  stale.**
  - **A reader reads each settle's belief before it and after it, never in between.** A
    reader on another thread read the loser of a standing contradiction as believed on
    9–26% of its reads during any settle. A settle now holds its starting belief for other
    threads and publishes its decisions in one step, and no reasoning image is written
    while a settle holds the network.
  - **A match or closure a reader computes across a TMS call is not cached.** Every TMS
    entry point now moves the change clock after its mutation as well as before it.
  - **A reader no longer leaves a stale withdrawal for the writer to read.** The
    `:withdrawn` cache carries a generation, and an answer computed under an earlier one
    is not installed.
  - **A rollback keeps the violations a reader filed beside it.** A `preview`, a refused
    `edit!` or a refused `assert` removes only the entries the batch filed, and
    `preview`'s `:violations` names those alone.
    [preview.md](docs/preview.md#what-moves-anyway).
  - **Three process-wide settings hold under concurrent callers.** Browser activation
    tests and activates in one step, overlapping imports each hold auto-compaction paused
    for their own duration, and concurrent host starts arm one memory-guard listener.

  [storage.md](docs/storage.md#the-single-writer-contract).
  *Class:* **Fix**.

### Fixes: performance

- **A settle's cost no longer grows with the standing clashes, merges, `except`s, firings
  or taxonomy depth it does not touch.**
  - **The clash pass over a large taxonomy no longer climbs each type's ancestry per
    membership.** On a large store four costs each took a quarter to over half of a
    recover's settle in turn. Up-closures are built from the parents' closures
    over the condensation, `covers-over` walks the smaller side, and only a budgeted
    sweep's triggers are sorted. On a synthetic 100k-type DAG the cold closure pass takes
    454 s against 1,033 s.
    [taxonomy.md](docs/taxonomy.md#the-closure-is-not-materialized--it-is-answered-on-demand).
  - **A `genlCx` edge no longer pages every fact in the contexts it widens to find the
    ones a tuple mark reaches.** Both of its sweeps — the functional and anti-symmetric
    equalities, and the settle's constraint exposure — read the ancestor set's facts and
    then asked each for a mark; they now read from the smaller of the marked predicates'
    extent and the ancestor set's.
  - **A settle that moves many `genl` edges no longer walks the types under each one to
    find the mints they give a new route.** A `recover` brings every edge IN at once, and
    each read the closure under its own sub plus a count per type in it, so a subtree
    many edges leave from was walked once per edge, and a large store's recover spent its
    whole settle there. The types under all of a
    settle's edges are now one `tax/specs-of-all` walk, and the members below them one
    read. What thirty more edges add to a recover's pruning no longer depends on the
    subtree's depth; it grew from 390 reads at depth 5 to 1,290 at depth 20.
    [argtypes.md](docs/argtypes.md).
  - **A `genl` edge no longer pages every membership below it to find the mints it
    subsumes.** Only a member holding a mint can be one, and the members were read to
    learn their terms before the roster was asked; they are now read from the smaller of
    the roster and the extent. What pruning pages on an edge over 200 members is 22
    records rather than 202.
  - **A clash sweep no longer pages the records of members nobody believes.** Each read
    of the believed sentexes among a set of handles fetched the record before asking
    belief, so over a dump imported `{:belief? :stored}`, before its `recover`, a
    declaration's sweep paged every member below its type without spending the instance
    budget. A `genl` edge over 200 such members now pages 3 records rather than 203.
  - **A fact of a calculus or a claim on a preserved predicate no longer re-decides every
    firing of the rules over it.** Loading n such facts cost n² checks. An arrival over
    8,128 standing firings takes 4.2 ms rather than 22.4 ms.
    [exceptions.md](docs/exceptions.md#two-withdrawals-a-firing-carries).
  - **A settle's cost no longer grows with the merges standing, and a deferred batch of
    merges is linear in the batch.** At 4,096 standing merges an un-merge takes 0.53 ms
    against 52 ms, and a `with-deferred-settle` batch of 2,048 merges 0.9 s against 59 s.
    [equality.md](docs/equality.md#what-a-merge-does),
    [nmtms.md](docs/nmtms.md#where-the-scaling-arguments-hold).
  - **An assert beside standing `except`s it does not reach recomputes no reader's
    withdrawal.** Beside 4,096 believed `except`s an unrelated assert takes 0.20 ms
    against 10.0 ms, and `lein perf`'s `assert-over-standing-excepts` is judged, under 3x.
    [nmtms.md](docs/nmtms.md#the-withdrawal-cache).
  - **An assert beside 512 standing inherited clashes takes 14 to 26 ms, where it took 659
    to 1868 ms.** A settle carries a clash whose members, reading and askers did not move.
    `lein perf` gains `inherited-clash-arbitration` and
    `inherited-clash-arbitration-split`. [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).
  - **A settle over standing clashes costs about a fifth less per standing pair.** At 800
    definitional clashes a `genl` edge costs 3.3–4.1 ms against 4.6–4.8 ms; the
    `taxonomy-edge-arbitration` bound returns to 35x. [nmtms.md](docs/nmtms.md).
  - **A clash whose separation only a lower context sees costs the contexts below that
    separation, not the lattice below the members.** The second membership's assert
    beside 2,000 lower contexts takes 0.39 ms against 8.72 ms. `lein perf` gains
    `per-reading-vantages` and `chain-join`.
    [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).
  - **A `genlCx` edit beside a context cycle no longer reads every cycle in the KB.**
    Beside a cycle of 8,192 contexts an insert takes 0.26 ms rather than 2.20 ms.

  *Class:* **Fix** (settle costs that grew with standing state the write does not reach).

- **An assert and a forward-chain run do less work per fact.**
  - **An assert under `{:chain? false}` computes no chaining seeds.** `visibility-seeds`
    ran before `:chain?` was read and exhausted the heap on one unchained `genlCx` edge
    into a large KB. [api.md](docs/api.md).
  - **A forward-chain firing allocates about half what it did.** On the join pyramid at
    1k the forward-chain thread allocates 9.7 GB against 17.3 GB.
    [inference.md](docs/inference.md).
  - **A forward rule seeded beside its facts fires each combination once.** On the join
    pyramid at 1k, placements fall from 857,800 to 428,900 and the run from 14.8 s to
    10.4 s, with the identical derived set.
    [inference.md](docs/inference.md#what-a-run-pays-per-witness-chainagenda-arrivals).
  - **cyc-tiny loads at `:ontology` in 7 s, where it took 187 s.** The stratification
    check builds each graph node once; `lein perf` gains `edge-stratification-walk`.
    [exceptions.md](docs/exceptions.md#the-search).
  - **A fact written into a context NAT costs the same beside 256 sibling contexts as
    beside 16.** It took 642 ms against 4 ms; `lein perf` gains
    `context-nat-existing-context`.
    [context-nat.md](docs/context-nat.md#the-structural-genlcx-producer).

  *Class:* **Fix** (costs that grew with the KB rather than with the write).

- **Existence questions, and sign, labeling, disjointness and qualitative reads, no longer
  grow faster than the facts they read.**
  - **`provable?` with no bound, and `query?` at a depth, stop at the first answer.** Both
    ran the search to exhaustion before testing it for emptiness, so an existence question
    over a goal with k derivations cost k; the answers are unchanged.
    [api.md](docs/api.md#choosing-a-query-function).
  - **A preservation goal whose predicate's facts sit on a sub-predicate reads the
    product, not the sub-predicate's extent.** The retrieval priced the open probe by the
    goal predicate's own facts, so a goal with a four-tuple product read 20,000 rows over
    10,000 sub-predicate facts; it now reads four.
    [inherit.md](docs/inherit.md#what-one-question-costs).
  - **A `(bravely S)` or `(cautiously S)` ask classifies once per write, and with an ASP
    backend only the dilemmas sharing a member with `S`'s.** With a backend 20 Nixon
    diamonds took 32 s an ask and 40 threw at the solver's time limit. `lein perf` gains
    `brave-ask-between-writes`. [labeling.md](docs/labeling.md).
  - **A sign ask after a write rebuilds its reading in time linear in the sign facts.**
    Along an 800-link `qualitativeSum` chain an ask takes 12 ms against 83 ms; `lein perf`
    gains `sign-chain-rebuild`. [sign.md](docs/sign.md#the-fixpoint).
  - **A `genl` edge into a `sibling_disjoint` clique costs the same at 4,096 members as at
    256.** An edge takes 0.16 ms at 1,000 and 10,000 siblings, against 0.58 ms and 4.3 ms;
    `lein perf` gains `sibling-disjoint-new-spec`, judged between 256 and 4,096 members. [taxonomy.md](docs/taxonomy.md).
  - **A `do/label` run finds its choice, constraint and solve rules without reading the
    facts beside them.** Each grounding walked the whole extent of the base and its
    ancestor contexts once per rule kind; beside 32,000 unrelated facts a grounding takes
    0.20 ms against 17.25 ms. `lein perf` gains `label-beside-unrelated-facts`.
    [solving.md](docs/solving.md#dolabel-base-into-mode).
  - **A write that leaves a qualitative network unmoved no longer compares it pair by
    pair.** An arrival in a sibling context of a 192-region chain takes 2.8 ms rather than
    7.2 ms.
    [qcn.md](docs/qcn.md#the-network-is-resident-and-the-clock-is-what-makes-that-sound).

  *Class:* **Fix** (ask and edge costs linear, quadratic or exponential in the facts read).

### Fixes: errors and reporting

- **A JVM error or an interrupt propagates instead of being read as an answer.**
  - **One `OutOfMemoryError` no longer makes a value class unstorable for the rest of the
    process.** The memoized storability probe behind `:not-encodable` cached an `Error`
    thrown mid-freeze as a verdict, so every later `java.util.Date` was refused until
    restart. Only an `Exception` is a verdict now; an `Error` caches nothing.
  - **An out-of-memory error while loading clingo no longer disables it for the process.**
    A `VirtualMachineError` routes that one solve to clasp and the next call loads again;
    any other throw is remembered as before and now logged at `:warn`.
    [asp.md](docs/asp.md).
  - **The ASP edge solver rethrows a JVM error and keeps an interrupt.** An
    `OutOfMemoryError`, a `StackOverflowError` or an `InterruptedException` read as
    "decide nothing", and the cleared interrupt flag lost a stop meant for the settle. A
    `VirtualMachineError` propagates; an interrupt decides nothing with the flag set again.
  - **A change-feed listener's JVM error propagates, and its interrupt is kept.** A
    `VirtualMachineError` now propagates out of the write that delivered the event (the
    write stands), and an interrupt is logged and skipped with the flag set again. The log
    line for a listener that threw carries the throwable, where it carried the message.
    [feed.md](docs/feed.md).
  - **A browser job whose status arm throws is filed `:failed` and releases the writer.**
    A second `OutOfMemoryError` left the job `:running` with the process's one writer
    claim, and every later writing job was refused `:job-busy`. An `InterruptedException`
    is filed `:cancelled` only when `cancel!` asked the job to stop.
    [web.md](docs/web.md).
  - **A koinii `sync!` pass that throws closes the subscription it opened.** Each retry
    opened another, and 64 failed passes filled the daemon's table, so another client's
    `:watch` was refused `:too-many-subscriptions`. The medium protocol gains
    `-feed-close`. [koinii.md](docs/koinii.md).
  - **A koinii wire subscription whose poll raises an `Error` reads stopped.** A
    `StackOverflowError` ended the thread with `:running` still true and nothing logged;
    the poll catches `Throwable`, as the callback beside it does.
  - **A wire feed subscription unregisters from the KB it watched.** After
    `/kbs/activate`, `:unwatch` and the idle reap unregistered from the newly active KB,
    so one client's unwatch removed another client's listener and left its own.
  - **A cache trim that throws is logged.** The memory-pressure guard skipped it silently;
    it is now logged at `:warn` naming the cache, and still costs that cache alone.
    [caches.md](docs/caches.md).

  *Class:* **Fix**.

- **A clasp process that outlives its time limit is killed, and the solve raises
  `:solver-unavailable`.** clasp stops itself at `VAELII_ASP_TIME_LIMIT`; a process that
  did not held the single writer until it exited. It is now killed with every process it
  started at twice the limit, or the limit plus 10 s when that is later, and the edge
  solver decides nothing, as it does for a missing binary.
  [asp.md](docs/asp.md#the-time-limit).

  *Class:* **Fix**.

- **Failures report what happened and what to do.**
  - **A background belief rebuild that throws is reported, not read as no rebuild.**
    `rebuild-progress` answered nil while `write-hazards` kept `{:stale-belief true}` and
    every write was refused. It now reports `:failed` (`{:at :class :message}`), the step
    and the time at the throw, until `recover` rebuilds belief; the browser's banner names
    the failure and the repair. [storage.md](docs/storage.md).
  - **An assert that closes a `genl` cycle under an asymmetric preserved predicate returns
    instead of throwing `IllegalArgumentException`.** The settle read a claim's own
    converse, carried round the cycle, as a claim denying it, threw "Duplicate key" and
    lost the write. A claim no longer denies the sentence it states.
    [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).
  - **The daemon answers an arity error raised inside an op as a fault, not as
    `:bad-args`.** Only a mismatch at the op's entry point is `:bad-args`; one raised
    inside it is 500 `:internal-error`. operations.md states that a `:bad-reply` can follow
    a write the daemon applied. [operations.md](docs/operations.md).
  - **Three refusals name the fix.** The daemon's 404 names the method and path and the
    routes it serves; `:exception-not-closed` says to bind the variable or drop it;
    `:arbiter-is-party` says to name an arbiter who holds no side.
  - **`apply-proposal!` counts the adds a fault past `edit!`'s commit point keeps.** It
    reported `:applied 0` for any throw; a throw without `:rolled-back` is counted from
    the store now.
  - **A blank `vaelii.clingo.lib`, `VAELII_TEST_TMS`, `VAELII_TEST_SPACE`,
    `VAELII_TEST_LOG_LEVEL` or `VAELII_BENCH_LOG_LEVEL` is unset**, as every other
    switch's blank is, where each read `""` as a value and refused it.

  *Class:* **Fix**.

### Fixes: browser, CLI and koinii

- **The browser and `lein cli` state what a write did, and refuse before they write.**
  - **The browser no longer reports a derived sentex as retracted.** `retract!` takes a
    premise mark, so a derived sentex stays stored and believed, yet the confirmation, the
    POST and the editor's Save counted it as gone. The confirmation names each sentex
    that stays and why, with a `/why` link; the tallies count the handles gone from the
    store after the settle. [web.md](docs/web.md#editing-sentexes).
  - **The browser's assert form and `lein cli` check before they write.** A refused form
    left a new sandbox's `genlCx` edge, and a command line refused for its operands
    (`:bad-args`, a non-numeric `--depth`, an unknown `--format` or command, `--nearest`
    with a handle) created its `--dir` store first, with `--starter` loaded. Both now check
    first. [api.md](docs/api.md).
  - **`lein cli diff` answers beside a daemon holding `--dir`.** It compares two text KBs
    and now opens no KB, so the daemon's single-writer lock no longer refuses it.
    [operations.md](docs/operations.md#the-single-writer-contract).
  - **The browser's `/find` shows a failed read as a failed search.** Every failure read
    "Not a valid regular expression"; only a pattern that does not compile or overflows
    the stack does now, and any other failure is logged and shown as "Search failed".
  - **`/levels` names the channel that keeps a complete prover from running alone, and
    `/caches` names the derived state it does not list.** The row reads `guarded by
    rules`; `/caches` lists the refusal memory, the re-check set, the disjointness and
    negation ledgers and the rule index's reference counts as not caches.
  - **A cancelled job's card shows what the report that stopped it had reached**, where it
    read one report short.
  - **The browser logs an unusable `VAELII_WEB_PORT` or `vaelii.web.port`** at `:warn`,
    naming the source, where a typo started it on 3000 unexplained.

  *Class:* **Fix**.

- **koinii's replies and marks read the same on every seat.**
  - **koinii locates a reply by its target.** A sentence naming `(sentexHandle n)`, as
    every response act does, digested the number `n`, so two seats that built one
    conversation in different orders computed different locators and commit ids. The
    digest carries the named record's digest, and a reply's `marker` carries its targets'
    markers under `:targets`. Stored records are unchanged; a seat believing such a
    sentence computes new locators, commit ids, state roots and inclusion proofs.
    [koinii.md](docs/koinii.md#the-other-deployment-shape-independent-seats).
  - **The predicates koinii writes outside its speech acts are declared.** `agentContext`
    in `CxSpeechActs`, and `disputeNotified`, `disputeStale` and `dispute` in a
    `CxDisputes` seed under `CxCore`, so a mark at the wrong arity is refused (`:arity`).
    An agent context rooted under `CxCore` alone does not see `CxSpeechActs`, so its mark
    stays undeclared there. [koinii.md](docs/koinii.md).

  *Class:* **Fix**.

### Tooling, CI and benches

- **`lein test-matrix` runs one matrix at a time, adjusts its slots while running, and
  runs under `sh`.**
  - **One matrix at a time, from the primary checkout.** A second matrix now exits 75
    without starting; an `--owed` one queues its baseline. `--covered=<a>..<b>` reports
    the newest run per owed configuration at a revision holding those commits.
    `test-matrix`, `test-backends`, `test-sweeps`, `test-shuffle` and `perf` refuse a
    linked worktree (exit 3) unless `ALLOW_WORKTREE_RUN` is set.
  - **`--set-jobs <n>` changes a running matrix's slot count**, re-read every scheduler
    pass, where the count was fixed at start. [operations.md](docs/operations.md).
  - **`scripts/test-matrix.sh` runs under `sh` and is executable**; it re-executes itself
    in bash.

  *Class:* **Fix** (developer tooling; no public function moves).

- **The gate, lint and profile checks count what they state.**
  - **`lein gate` says "perf owed" for the files the perf claims time.**
    `PERF_SENSITIVE_RE` in `scripts/gate.sh` missed 29 files a timed body runs, among them
    `naming` (48 of 55 claims) and `assert_entry` (28); `solve.clj` leaves the roster.
  - **`lein lint`'s prose check refuses the bare evaluative words the prose rules ban.**
    P2 matched them only inside fixed phrases, so 227 uses in 136 files passed.
  - **The profile instrument's `:fetches` counts every `RecordStore` read**, including
    `premise-strength`, `sentex-ids`, `justification-ids` and `premise-ids`.
    [profile.md](docs/profile.md).
  - **The unused-publics check does not count a var's call to itself**, so
    `scripts/check-unused-publics.py` sees a recursive public fn nothing else names.
  - **A `lein` alias that runs a script prints no `$CLASSPATH` warning**; `lein shell`
    drops the launcher's variable from the script's environment.

  *Class:* **Fix** (developer tooling; no public function moves).

- **CI and the Docker image run Temurin 25, and a weekly job measures coverage.**
  - **Temurin 25 in CI and the image.** The weekly deep run keeps one `memory` leg on 21,
    the stated floor. `:jvm-opts` add `--enable-native-access=ALL-UNNAMED` and, from 23,
    `--sun-misc-unsafe-memory-access=allow`, so a JVM starts without the JNA and
    `sun.misc.Unsafe` warnings.
  - **Compact object headers on JDK 25, and a class-loading cache in the image.**
    `-XX:+UseCompactObjectHeaders` holds 7.4% less live heap on `:memory` and 9.3% less on
    `:memory-dense` over a 120k-sentex load; the image reads `/app/vaelii.aot`, and an
    empty daemon answers `/health` in 0.58 s against 1.61 s.
    [operations.md](docs/operations.md#container--the-daemon-as-an-image).
  - **A weekly coverage job and current dependencies.** The deep workflow runs
    `scripts/coverage.sh :default --fail-under 78`. reitit-ring moves to 0.11.0,
    slf4j-nop to 2.0.20, tools.namespace to 1.5.1 and lein-cljfmt to 0.16.6.
    [dependencies.md](docs/dependencies.md).

  *Class:* **Additive** (the engine still runs on JDK 21; nothing a caller calls changes).

- **The gate and the matrix say what a change owes and hold off after a red run.**
  - **An owed `lein test-matrix` run starts at most four configurations, and a red run
    holds off the next matrix for 30 minutes.** `MATRIX_OWED_MAX` (4) takes a changed
    file's own configurations first; `MATRIX_RED_COOLDOWN` (1800 s) refuses a new or
    queued matrix with exit 75, naming each failing test with a re-run command. A matrix
    stopped by ^C or TERM files its ledger row and `summary.tsv`. Every script outside
    `scripts/lib/` is one brace group, which `lint-shellcheck.sh` enforces.
    [operations.md](docs/operations.md).
  - **`lein gate` fails on a JVM warning in its stage logs**: a restricted native call, a
    `sun.misc.Unsafe` caller, a dynamically loaded agent, a JVM option warning or lein's
    `$CLASSPATH` warning.
  - **`lein gate` says "slow owed"** when the diff touches the files `SLOW_OWED_RE` names
    for the `^:slow` tests, and blocks nothing.
  - **The API golden pins a roster's members.** A keyword-collection public var is frozen
    in `test/golden/api-surface.edn` as its sorted members, so a dropped or respelled
    option key or wire op is red. [CONTRIBUTING.md §3.8](CONTRIBUTING.md).

  *Class:* **Additive** (developer tooling; no public function moves).

- **New benches and perf baselines.**
  - **`lein test-full-kb` probes a full-size KB.** The `^:full-kb` tests hold reads,
    writes, retractions, the spindle sync and edge writes on a store of millions of
    sentexes to ceilings of index operations and milliseconds; no other selector runs
    them. `sync-spindle!` takes the shipped content as a second argument. CONTRIBUTING.md
    §5.
  - **`lein perf` judges `assert-over-standing-excepts` and
    `unmerge-over-standing-merges` under 3x, and prints `qcn-chain-load` as a baseline it
    does not judge.**
    [nmtms.md](docs/nmtms.md#where-the-scaling-arguments-hold).
  - **Three benches read the columnar index beside `:memory`.** `vaelii.bench.pyramid`
    gains a `backends [reps]` mode, `lein bench-plan` gives each width its own store, and
    `lein bench-subgoal` takes the store as a third argument. On join.1k the columnar
    index runs the fixpoint in 0.85× the CPU and 0.83× the resident heap.
  - **`lein bench-witness` measures the surplus the route covering test keeps**: 12 of 162
    sentexes on the new `generated-siblings` corpus, 0 on the starter.
    [defenses.md](docs/defenses.md#routes-in-sibling-contexts-each-carry-a-firing).

  *Class:* **Additive** (bench modes and output; no engine change).

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
paths drop work that changes no answer, an operation log records a `:disk-snapshot` KB's
public writes behind a seal, and a settle-phase instrument splits a settle's wall clock
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
