# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.20.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

- **A relation can state that its arguments commute.** `symmetric` said it of the two
  arguments of a binary predicate and nothing else, so a variable-arity relation whose
  arguments are unordered could not be stated at all. Three marks say it at any arity:

  ```clojure
  (commutative P)                    ; every argument, at each arity P is applied at
  (commutativeInArgs P 1 2)          ; exactly the named positions; the rest stay put
  (commutativeInArgAndRest P 2)      ; position 2 through the application's own end
  ```

  Every permitted permutation of a ground fact stores as **one sentex and one handle**,
  so queries, rule matching, context visibility and retraction all follow from the
  sentence being stored once. `(covering Engine Piston Rod Valve)` answers a goal naming
  the parts in any order, off the one stored row. A tail is closed by the literal's own
  arity, so `(covering W A B)` and `(covering W A B C)` stay two claims and no
  permutation moves an argument between them; repeats keep their multiplicity;
  overlapping marks merge into one component rather than applying in sequence, which
  would make the stored form depend on which was applied first. A declaration arriving
  after the facts re-spells what is already stored, as a late `symmetric` does.

  Each of the three installs its permutation group at its own arm, so no spelling is
  derived from another and the canonicalizer reads one table whichever was written. The
  equivalence between `(commutative P)` and `(commutativeInArgAndRest P 1)` stays in
  CxCore as two `set/inertRule`s, believed and queryable but run by neither engine.
  `(genl symmetric commutative)` classifies, and `(commutative P)` with `(arity P 2)`
  concludes `(symmetric P)` — commutativity at two arguments is symmetry, where
  commutativity at any other arity implies neither symmetry nor arity 2 — as a
  `set/forwardOnlyRule`.

  Those three directions are what the vocabulary costs a backward search. `set/forwardRule`
  adds forward chaining **without** taking the backward use away, so written that way each
  of the three answers goals as well; and each concludes a mark another of them needs —
  the equivalence directly, the arity bridge because `(genl symmetric commutative)` makes
  its conclusion a spec of `commutative`, which `provers/candidate-rules` offers as a
  candidate for the supertype goal its own antecedent poses. No ancestor-goal guard stops
  the descent, the depth bound turns the cycle into an exponential frontier rather than a
  refusal, and `(genl commutative relation)` puts `(commutative ?p)` under every open
  `(relation ?x)` query. Any KB that loaded CxCore and read through the inference engine
  stalled, whether or not it asked about commutativity.
  *Class:* **Additive**.
  [#55](https://github.com/vaelii/vaelii/issues/55),
  [docs/canonicalization.md](docs/canonicalization.md)

- **An open query under the node engine converges on a rule graph containing a cycle.**
  A node is a conjunction of literals, and `children` rewrites one literal through one
  rule by splicing the rule's antecedents in where that literal stood. The splice kept a
  conjunct the conjunction already held. Conjunction is idempotent, so `A ∧ B ∧ B` and
  `A ∧ B` are one question under two `node-key`s, and the claimed-key set could not
  recognize the state as one it had already expanded: each turn of the cycle added a
  conjunct instead of returning to a claimed key. A repeat now collapses onto the first
  copy, which takes the largest depth of the copies folded onto it, so no rewrite a copy
  admitted is refused; the rewrite window reopens at the position a copy folded onto,
  which is what makes that depth reachable. `(relation ?x)` over CxCore with three bridge
  rules chaining forward expanded 192,971 nodes at depth 5 and did not finish depth 6
  within 411 s; the same query expands 710 nodes and 1,843, and completes at depth 8 —
  the bound the suite runs under — in 11,446 nodes and 4.1 s. The answers are the same
  121 at every depth. *Class:* **Fix**.
  [docs/inference.md](docs/inference.md)

- **A bulk load no longer stores a permutation of a row it already holds.** The fast
  path skips the dedup probe because a distinct corpus never hits an existing sentex —
  but a permutation of a stored row is not distinct, and the caller cannot tell:
  separating `(covering W C A B)` from a stored `(covering W A B C)` needs exactly the
  taxonomy read the fast path avoids. Three permutations bulk-loaded landed as three
  records for one proposition, each retractable without the others. A commuting
  relation now keeps the probe, as a symmetric one already did. *Class:* **Fix**.

- **The rete alpha matcher fans a commuting literal's arrangements.** Under
  `VAELII_RETE=1` a rule whose antecedent named a commuting relation's arguments in an
  order the stored row does not hold them in derived nothing, where the same rule fired
  on the default retrieval path. The two now fan identically. *Class:* **Fix**.

- **The exposure sweep budget is 8192.** `tax/*exposure-instance-budget*` bounds a sweep
  against a large extent, and 4096 was not doing that: the shipped ontology plus a
  200-fact generated corpus exhausted it with the threshold measured between 4096 and
  4224, so any three terms added to `CxCore` cut five triggers short and left the
  clashes they implicate unreported for that settle. Which sweeps the cap refuses is
  unchanged, and so is every KB that never came near it. *Class:* **Fix**.
  [docs/nmtms.md](docs/nmtms.md)

## 0.20.0 — 2026-09-17 — "a defeated fact stays believed outside the context that decided the clash, and the belief record is renamed Reasoning"

- **A clash's defeated member is disbelieved only where the clash is seen.** A nogood is
  decided at its vantage, the most general context that sees every member, and the
  defeated member is disbelieved at the vantage and in every context below it.

  ```
  CxUniverse   (disjoint dog cat)
   └─ CxA      (cat Rex)   :default
       └─ CxD  (dog Rex)   :monotonic      ← the vantage
  ```

  A read from `CxD` finds `(dog Rex)` and not `(cat Rex)`; a read from `CxA`, which cannot
  see `(dog Rex)`, still finds `(cat Rex)`. Before this change the engine disbelieved the
  member in every context, so a fact `CxA` cannot see decided what `CxA` believed. `in?`
  still answers the network's label, which is now the label before any reader's scoping;
  `believed?`, `ask`, `query`, `lookup`, `prove`, `sentexes-matching`, the extent reads'
  `{:believed? true}` option, `why`, `why-not` and `belief-status` apply the scoped defeat.
  The stored-count reads (`count-with-functor` and its siblings) count what is stored, as
  they always did. *Class:* **Breaking** (a context above a clash's vantage believes the
  defeated member, and `in?` answers true for it). *Migration:* read belief with
  `believed?` and a reader context rather than `in?`, which answers the unscoped label; to
  decide a clash for a general context, state the stronger side in that context.
  [docs/nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage),
  [docs/contexts.md](docs/contexts.md)

  *Breaks:* `in?`, `believed?`

- **A conclusion follows its reader, so an `except` subtracts what rests on what it
  hides.** A conclusion whose every justification rests on a handle a reader reads as
  withdrawn is withdrawn from that reader too, wherever it is stored. A visibility
  `except` therefore reaches further than the sentex it names: a reader at or below the
  `except` no longer sees a conclusion stored **above** it that rests only on the hidden
  sentex. Before this change the `except` hid its target and left every conclusion drawn
  from it believed. Withdrawal follows the current justification graph, not the derivation
  that first stored the conclusion, so a second justification resting on nothing withdrawn
  keeps the conclusion — and everything below it — believed. *Class:* **Breaking** (a
  reader below an `except` stops seeing a conclusion stored above it that rests only on
  the hidden sentex). *Migration:* none for a KB whose excepts hide facts nothing is
  derived from; where a conclusion should survive its hidden support, give it a second
  justification or state it in the reader's context.
  [docs/contexts.md](docs/contexts.md), [docs/exceptions.md](docs/exceptions.md)

  *Breaks:* `except`, `sentexHandle`

- **`do/labeling` commits inside its context, so two labelings stand side by side.** The
  strengthened copy and the losing side form a nogood whose vantage is the labeling
  context, so the loser is defeated there and below and nowhere else. The base keeps
  believing both sides and keeps reporting its dilemma in `contradictions`, and a second
  labeling of the same dilemma in a sibling context decides it the other way without
  disturbing the first. Before this change a labeling committed globally: the loser went
  OUT for every context and the base's dilemma stopped being reported, so rival labelings
  had to be compared sequentially, retracting one before running the next.
  *Class:* **Breaking** (`do/labeling` no longer removes the dilemma from
  `contradictions`, and the losing side stays believed outside the labeling context).
  *Migration:* read the labeled world from the labeling context; a caller that read the
  base after labeling to see the decision reads that context instead.
  [docs/labeling.md](docs/labeling.md),
  [docs/nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage)

  *Breaks:* `do/labeling`, `contradictions`

- **The reasoning image is `<dir>/reasoning/`, and `Belief` is `Reasoning`.** One word named
  four things: the JTMS label `in?` answers, the record a KB holds its network, taxonomy and
  derived atoms in, an agent's propositional attitude, and the durable image of the second.
  The record is now `Reasoning` in `vaelii.impl.types.reasoning`, built by
  `kb/empty-reasoning` and held under the KB's `:reasoning` field; the image is
  `vaelii.impl.reasoning-image`, and it writes `<dir>/reasoning/` beside the records and
  `<dump>/reasoning/` inside an export dump. `belief` keeps the label: `jtms/in?`,
  `resolution/*belief-blind*`, `belief-status`, the `:belief?` export and import option —
  which decides whether the labels are carried at all — and `vaelii.koinii.belief`, an
  agent's attitude, are unchanged. No behaviour moved. *Class:* **Breaking** (an existing
  store's image is not read, a sealed store's `seal.nippy` is layout 2, and four result
  keys are renamed). *Migration:* a `:disk-snapshot` store written by an earlier release
  recovers once on the next open and writes `<dir>/reasoning/`; `lein cli upgrade --dir
  <dir>` does that ahead of time, and the leftover `<dir>/belief/` is deleted by hand. An
  earlier seal is declined by version, so the open replays the log and recovers. An earlier
  dump imports with a full recover in place of the image install. A caller reading
  `import!`/`export!`'s `:belief-image` summary key reads `:reasoning-image`,
  `cli/upgrade!`'s `:belief` reads `:reasoning`, `recovery/recover-with-image` answers
  `{:reasoning …}`, and `export!`'s `:on-progress` reports `{:phase :reasoning-image}`.
  *Breaks:* `belief-image`, `:belief-image`, `belief_image`, `types.belief`, `map->Belief`
  *Breaks:* `derived-state`, `belief-fingerprint`, `register-belief-image!`, `:belief-fp`
  [docs/storage.md](docs/storage.md), [docs/namespaces.md](docs/namespaces.md)

- **Seven extension-point protocols move to held namespaces.**
  `vaelii.impl.provers/Prover` and `SupportingProver` are `vaelii.impl.types.prover/…`;
  `vaelii.impl.solve/Solver` is `vaelii.impl.types.solve/Solver`;
  `vaelii.impl.io.snapshot/SnapshotSink` and `SnapshotSource` are
  `vaelii.impl.types.snapshot/…`; `vaelii.impl.kv/KvBackend` is
  `vaelii.impl.protocols/KvBackend`; koinii's `channel/Medium` and `catchup/CursorStore`
  are `vaelii.koinii.types/…`. Each protocol's method names and arglists are unchanged, and
  each method fn moves with its protocol. The development browser's reloader never
  re-evaluates a held namespace. *Class:* **Breaking**
  (an implementer or caller that names a protocol or a method through the old namespace
  fails to compile). *Migration:* require the new namespace and name the protocol and its
  methods through it — `(reify vaelii.impl.types.prover/Prover …)`, `(protocols/kv-get b
  k)`, `(snapshot-types/write-section! sink name frames)`. `save-index!`, `load-index!`
  and `memory-medium` stay in `vaelii.impl.io.snapshot`. [docs/storage.md](docs/storage.md),
  [docs/qcn.md](docs/qcn.md)

  *Breaks:* `Prover`, `SupportingProver`, `Solver`, `SnapshotSink`, `SnapshotSource`, `KvBackend`, `kv-get`

- **Only `scripts/start-vaelii-dev.sh` turns hot reload on, and `vaelii.web/start` refuses
  `:reload?`.** `lein browser` serves the nREPL reload channel and watches source files
  only with `VAELII_DEV` set, which the script sets. `-main` never reloads, where it took
  the reloading handler under `VAELII_DEV` before. `start` refuses `:reload?` as
  `:unknown-option`. *Class:* **Breaking** (a caller passing `:reload?` to `start`
  throws). *Migration:* drop `:reload?` and run `scripts/start-vaelii-dev.sh` for a server
  that follows source edits.
  *Breaks:* `:reload?`
  [docs/web.md](docs/web.md)

- **A rule is refused an `(ist Ctx S)` consequent.** Such a rule placed its conclusion in
  `Ctx` whether or not `Ctx` saw the rule or the facts the firing rested on. `Ctx` then
  believed a sentex whose support it could not read. The rule's `exceptWhen` query ran in
  `Ctx`, so an exception stated beside the rule did not block the conclusion. The backward
  chainers never answered from such a rule, so a rule's direction changed what the KB
  believed. `assert`, `assert-rule` and `check` now refuse the consequent as
  `:not-well-formed`, as they already refused `ist` in antecedent, exception and NAF
  position. Forward chaining's `ist` placement branch is removed, and so is CxCore's inert
  rule `(implies (?pred . ?args) (ist CxUniverse (?pred . ?args)))`; the `comment` on
  `decontextualized_predicate` states the lift instead. `(ist Ctx S)` given to `assert` or
  to a read is unchanged. *Class:* **Refusal** (a rule with an `ist` consequent, accepted
  before, is refused). *Migration:* conclude `S` plainly, and make it visible where it is
  wanted with `(decontextualized_predicate P)` or a `genlCx` edge. Retract a stored
  `ist`-consequent rule before opening a durable store under this build.
  [docs/contexts.md](docs/contexts.md#ist-find-or-create-in-a-context)

  *Breaks:* `assert`, `assert-rule`, `check`

- **`contradictions` takes a reader.** `(contradictions kb context)` reports the pairs
  standing for one context: it keeps an entry whose every side `context` sees and whose
  every member `context` believes. A dilemma is a pair standing together, so a reader that
  reads one side as withdrawn — by a scoped defeat at a vantage it sees, or by an `except`
  — is not looking at one, and the reading agrees with `believed?` for that reader. A
  vantage therefore drops the pair it decided, a reader below two vantages that disagreed
  keeps it, and a pair one vantage decided while another only tied drops for the readers
  that defeat reaches. The no-context arity is the KB-wide reading, unchanged, and a nil or
  variable context reads as that. The reading's own cost is a placement rather than a
  growth term: the `except` predicate the filter asks through was rebuilt once per member
  of every reported pair and one predicate now serves a whole reading, and the per-vantage
  disagreement reports are built once per settle and cached beside the per-reader
  withdrawals, which `clear-withdrawn!` empties wherever belief or either roster moves.
  `clash_reading_cost_test` pins both at one build, at two sizes, a constant factor per
  report being out of a `lein perf` ratio's reach. *Class:* **Additive**. *Migration:* none.
  [docs/api.md](docs/api.md)

- **`open-kb` takes `:recover? :background`, and the development browser opens a store with
  it.** A
  `:disk-snapshot` store whose reasoning image an earlier engine build wrote installs that
  image and answers from it, while belief is rebuilt under the running build on a daemon
  thread and then replaces the installed belief in one step. A public read reads one belief
  whole, so no read sees the network of one belief beside the taxonomy of the other. Writes
  are refused (`:unrecovered-kb`, `:hazards [:stale-belief]`) until the rebuilt belief is
  installed, and `close!` and `recover` stop the rebuild first. The browser takes it under
  `VAELII_DEV` only, which `scripts/start-vaelii-dev.sh` sets; a served browser opens with
  `:auto` and waits for the recover. *Class:* **Additive**. *Migration:* none.
  [docs/storage.md](docs/storage.md), [docs/web.md](docs/web.md)

- **`belief-status` reports `:withdrawn?` and `:scoped-vantages`.** `:withdrawn?` is true
  when the context reads the handle as withdrawn: hidden by an `except`, scoped-defeated at
  a vantage the context sees, or resting only on such a handle. `:scoped-vantages` names
  the vantages the context sees at which the handle itself is scoped-defeated, and
  `:believed?` is false whenever `:withdrawn?` is true. A backward derivation of a
  scoped-defeated sentence is dropped for a reader at or below the vantage, and the
  extent fns' `{:believed? true}` reads each sentex as its own context reads it. `why-not`
  of a handle reads it at its own context too, and answers `:reason :withdrawn`, with the
  scoped defeats behind it under `:withdrawn-by`, for a sentex that is IN in the network
  and withdrawn where it is stored. *Class:* **Additive**. *Migration:* none. [docs/api.md](docs/api.md),
  [docs/nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage)

- **`lein cli upgrade --dir DIR` and `scripts/upgrade-kb.sh` bring a store up to the
  running engine.** `upgrade` opens the store under its own backend, installs its belief
  image or, when the image was written under another image layout, other engine source or
  other policies, recovers belief from the records and writes a new image, then closes it,
  which writes the index image a rebuilt index leaves due. It prints whether the image was
  current, rebuilt or written for the first time, and refuses a directory holding no store.
  `--verify` recovers anyway and reports whether the believed sets changed.
  `scripts/upgrade-kb.sh [KB-DIR...]` runs it per directory, defaulting to
  `checkouts/kb`. *Class:* **Additive**. *Migration:* none.
  [docs/operations.md](docs/operations.md)

- **`store-backend` names the backend a store directory was written by.** `(store-backend
  dir)` answers `:disk-snapshot` for a mapped index image, `:disk-log` for a
  write-ahead-logged index, `:disk-columnar` for records with no index file, and nil for a
  directory holding no store. The browser's catalog and the daemon open a directory
  through it. *Class:* **Additive**. *Migration:* none. [docs/api.md](docs/api.md)

- **`vaelii.core` publishes ten functions the browser read from engine namespaces.**
  `negative?`, `rests-on`, `query-contexts`, `assertable-strengths`, `write-hazards`,
  `read-manifest` and `install-memory-guard!` delegate to the engine function the browser
  called before. `load-foreign!` loads a directory through the foreign reader plugin
  registered for a kind, and refuses a kind whose reader loads no directory
  (`:no-foreign-reader`). `store-state` reports whether a KB's records read back as
  sentexes, whether its belief network holds a node and an IN node, and whether `recover`
  has a premise mark or a justification to rebuild belief from; an optional key set limits
  it to the probes a caller asks for. `switch-value` reads a `VAELII_*` or `vaelii.*`
  switch against its domain through the engine's switch roster, and refuses a name the
  roster does not hold (`:unknown-option`). The browser's namespaces move from
  `vaelii.host.*` to `vaelii.browser.*`, an application over this API; the public entry
  point `vaelii.web` is unchanged, and `lein run -m vaelii.browser.web` replaces the
  private `vaelii.host.web`. *Class:* **Additive**. *Migration:* none.
  [docs/api.md](docs/api.md), [docs/web.md](docs/web.md)

- **The browser answers the daemon protocol, and the daemon loads the starter on
  request.** `vaelii.browser.web` serves `GET /health` and `POST /op` over its active KB
  through the daemon's handler, which is now the public `vaelii.host.serve/handle-op`,
  under the browser's write monitor. It refuses an op with 404 `:not-found` while it reads
  a remote daemon, and with 409 `:still-loading` or `:still-exporting` while a job writes
  or an export walks the active KB. `vaelii.serve` takes `--starter`, which loads the
  shipped starter schema into the KB before the port is bound. *Class:* **Additive**.
  [docs/operations.md](docs/operations.md), [docs/web.md](docs/web.md)

- **The browser draws framed regions in one monospace face, and every sentence box is an
  editor.** Dark is the base theme and light the override. Each region is a square frame
  titled in its top border, and its number folds it, by click or by digit key. Every box
  that takes a sentence (the editor panel, `/assert`, the `/levels` goal) colours parens by
  depth, indents on Enter and Tab, completes a symbol through `/complete`, and previews the
  save through `/edit/preview` while typing pauses. A sentex badge is one circle whose
  colour gives its kind and strength, filled when asserted, a ring when derived and dimmed
  when not believed. A term inside a hierarchy is a link to its page. A sentex row is
  selectable text with an `[edit]` control; the checkboxes, marquee selection and
  selection action bar are removed, and `/edit?handles=` still takes a comma-separated
  batch. *Class:* **Additive**. *Migration:* none. [docs/web.md](docs/web.md)

- **The browser loads `VAELII_KB_DIR` at startup, and three scripts start vaelii over a KB
  directory.** With `VAELII_KB_DIR` set, the browser opens on the starter and loads that
  directory as a catalog job with belief recovered; the KB becomes the active one when the
  load finishes. `scripts/start-vaelii-dev.sh` runs the browser with an nREPL, hot reload
  and the profiler UI; `scripts/start-vaelii.sh` runs the browser alone;
  `scripts/start-vaelii-server.sh` runs the daemon without the development profile, under
  a Leiningen trampoline, with a bearer token required. All three default to
  `checkouts/kb` and set the heap from `VAELII_HEAP` (default `40g`).
  *Class:* **Additive**. *Migration:* none. [docs/web.md](docs/web.md)

- **A refused switch names itself under `:switch`.** A `VAELII_*` or `vaelii.*` switch
  refused for an out-of-domain value, and a name `switch-value` does not read, carry the
  switch's spelling under `:switch` as well as under `:property`. `:property` holds
  environment-variable names too, although its name describes only the system-property kind
  of switch. It stays, with the same value, so a caller reading it is unaffected. *Class:* **Additive**.
  *Migration:* none; read `:switch` in new code. [docs/troubleshooting.md](docs/troubleshooting.md)

- **`why-not` of a sentence explains the sentex its reader inherits.** `(why-not kb
  sentence context)` looked for a sentex stored in `context` itself and answered
  `:not-stored` when it found none, although `ask?` and `believed?` answer the same
  sentence from the contexts `context` inherits from. It now probes `context` first and
  then the contexts `context` sees, taking the most specific candidate and breaking a tie
  on content, and reports that sentex under the context storing it. A sentence no visible
  context stores is `:not-stored` as before. *Class:* **Fix**. *Migration:* none.
  [docs/api.md](docs/api.md)

- **A reader below two vantages that defeated different members believes both.** A nogood
  whose members' contexts have several maximal common descendants is decided at each of
  them, and two vantages can rank the same member differently: one reads a member's
  monotonic support as withdrawn and defeats it, the other reads that support whole and
  defeats the other member. Each verdict holds at its own vantage and below. A reader that
  sees two such vantages read both verdicts and took both, so it believed no member of the
  clash. One nogood convicts one member, so that reader now takes neither verdict, reads
  every member as believed, and `contradictions` reports the nogood as the represented
  dilemma it is. `settle` records the disagreeing verdicts in the KB's
  `:vantage-disagreements`, and a defeat of the same handle at a vantage outside the
  disagreement still reaches the reader. Such an entry carries `:vantages`, the `{vantage
  handle}` map of what each vantage decided, and is read off that roster rather than off
  the settle that weighed the nogood, so a later settle whose region does not reach the
  pair leaves the report standing. *Class:* **Fix**. *Migration:* none.
  [docs/nmtms.md](docs/nmtms.md#vantages-that-disagree)

- **`why` reads a handle as its own context reads it.** `why` decided `:believed?` from
  the network's raw label, so a conclusion withdrawn where it is stored — resting only on a
  sentex an `except` hides or on a member scoped-defeated at a vantage its context sees —
  came back `{:believed? true}` with a full proof tree, while `why-not` and `belief-status`
  answered `:withdrawn` and `:believed? false` for that same handle. `why` now reads each
  node of the tree at that node's own context (`res/believed-at?`), the reading `why-not`
  already used, so the two are complements again. *Class:* **Fix**. *Migration:* none.
  [docs/api.md](docs/api.md), [docs/nmtms.md](docs/nmtms.md)

- **An `exceptWhen` blocks only in contexts that see the context it is stated in.** An
  exception stated in `CxSpec` below `CxGen` blocked a firing whose conclusion is placed in
  `CxGen`, because the block decision read every believed exception without checking where
  it was stored. Forward placement, the justification re-check, the backward guard and
  `why-not` now keep only the exceptions the evaluation context's `genlCx` ancestor set
  holds. *Class:* **Fix**. *Migration:* none. [docs/exceptions.md](docs/exceptions.md)

- **The daemon opens a store under the backend its files were written by.** `lein run -m
  vaelii.serve PORT DIR` opened every directory as `:disk-log`. A `:disk-snapshot` or
  `:disk-columnar` store opened that way finds no index log, so the daemon served an empty
  KB over a full store. It now reads the backend off the files beside the records, and a
  directory holding no store still gets a new `:disk-log` store. *Class:* **Fix**.
  [docs/operations.md](docs/operations.md)

- **`lein cli --dir` opens a store under the backend its files were written by.** The CLI
  opened every `--dir` as `:disk-log`, so a `:disk-snapshot` or `:disk-columnar` store read
  as an empty KB. A directory holding no store still gets a new `:disk-log` store.
  *Class:* **Fix**. [docs/operations.md](docs/operations.md)

- **A settle whose region holds every stored sentex skips the retroactive clash sweep.**
  Such a region already holds every sentex the sweep can return, so the sweep adds no
  candidate, yet it called `declaration-implicates` for every stored `genl` and `disjoint`
  declaration and computed their spec closures and extents. On a 12.26M-sentex `:refuse`
  store recover's first settle filled a 40 GB heap and spent 66 of its 94 minutes in full
  garbage collection. A bulk load into an empty KB has such a region too: there the sweep
  spent its 4,096-instance budget on `(genlCx CxUniverse CxCore)` and four more
  declarations whose reach is the store, and filed `:arbitration-truncated` — the notice
  saying content a declaration implicates went undecided — on the one settle that decided
  all of it, which left `violations` non-empty after a clean load. `recover` binds
  `settle/*whole-store-region?*` around its first settle, and `clash-candidates` skips the
  sweeps when that binding holds and the region is at least as large as the store, or when
  the believed region's own size is. It asks the store for its sentex count only when the
  region carries a declaration or a retract left an exception pair to re-arm. Recover's
  second settle and every settle over part of a store still sweep. *Class:* **Fix**.
  *Migration:* none. [docs/nmtms.md](docs/nmtms.md)

- **A solve with no objective stops at the first model.** 0.18.0 made a `:label` solve
  stream every improving model (`--opt-mode=opt`, all models), so an optimization cut
  off by the time limit keeps its best. A program with no minimize statement has nothing
  to improve, and the same flags enumerate every model: `do/label … :sat` over a
  3-coloring of a 10k-node graph ran to the time limit on each solve and read back
  gigabytes of witnesses instead of answering in 110 ms, and a belief arbitration whose
  program carries no objective was exposed the same way. Both backends now read the
  program: with no objective a `:label` solve stops at the first model, and with one —
  a soft constraint under `:sat` included — it still streams improving models to the
  optimum. *Class:* **Fix**. *Migration:* none. [docs/solving.md](docs/solving.md)

- **A disk store whose `tokens.log` a crash truncated to zero bytes opens.** The store
  opened its token dictionary only for a non-empty `tokens.log`, so a torn, empty one left
  the tokenized frames in `sentexes.log` with no dictionary, and the open threw a
  `NullPointerException`. An existing `tokens.log` now opens the dictionary whatever its
  length. Each record the empty dictionary cannot decode becomes a `:damaged-dictionary`
  tombstone, the repair a record log that outran its dictionary already gets.
  *Class:* **Fix**. *Migration:* none. [docs/storage.md](docs/storage.md)

- **An edit to engine code recover cannot run keeps a store's reasoning image.** The source
  identity hashed every form of the 123 namespaces recover's `ns` closure spans, so an edit
  to `why`, an export writer or a quality report discarded every reasoning image, and the next
  open ran the full recover. The identity now hashes the top-level forms reachable from
  `open-kb`, `recover`, `recover-with-image` and the three `vaelii.impl.wiring` targets. It
  also hashes the forms that run without a direct call: a method of a reached multimethod,
  an extension of a reached protocol, every record, and every top-level form that defines no
  var. Over the 50 commits to `src/` before this change, the image survives 11, where the
  file-level digest kept it across 6. A `deftype` its own namespace constructs by its
  short class name is reached through that name. An image written before this change
  carries the file-level digest, so its store's first open under this build recovers once.
  *Class:* **Fix**. [docs/storage.md](docs/storage.md)

- **A term page stays within its row bound on a term with millions of sentexes.** The page
  found a term's argument positions by walking its whole extent, ordered each group by
  context before paging it, and computed the "In rules" and "Nested elsewhere" groups as
  a set difference over every id the roots hold. The positions are now twelve
  `count-with-arg` reads, and a term named only past argument position 12 is claimed by
  no argument group and stays in the remainder groups, where the page had counted a term
  at any position as claimed by one. A group past `group-sort-cap` pages in the index's order. The
  remainder walk stops at `remainder-scan`, and a page whose walk stopped says so and shows
  no remainder groups. The radial view's second hop reads at most `ego-scan` matches. On
  the 12.26M-sentex import the `genl` page renders in 0.75 s against 207 s, and `isa` in
  25 ms against 2.9 s. *Class:* **Fix**. *Migration:* none. [docs/web.md](docs/web.md)

- **A KB loaded in the development browser survives an engine edit.** The development
  browser reloaded every changed file under `src` before each request, together with every
  namespace that requires it, and an `impl/` edit redefined the engine's records, types and
  protocols under a loaded KB, whose existing records then failed `instance?` checks and
  protocol dispatch. `vaelii.browser.reload` replaces ring-devel's `wrap-reload`, so the
  `:dev` profile drops `ring/ring-devel` and takes `org.clojure/tools.namespace`. It
  reloads the changed files under `src` and their loaded dependents in dependency order,
  loads each file form by form, and leaves out every `defprotocol`, `defrecord`, `deftype`
  and `definterface` whose protocol or class already exists. It skips a held namespace, and
  the state the watched namespaces keep is in `defonce`. An edit inside a left-out form or
  a held namespace is named on every page until the process restarts. Each record keeps its
  methods inline, so protocol dispatch on it stays a direct interface call.
  *Class:* **Fix**. [docs/web.md](docs/web.md)

- **The genl and genlCx reconcile keeps only the edges whose state changes.** The
  reconcile after a relabel, and the one recovery runs over every edge, built a context map,
  a key set and three set differences over every edge in its region and held them until
  the pass ended, so a pass over a large taxonomy outlived young collections and promoted
  its intermediate collections into the old generation. One classifying pass now collects
  only the edges to deactivate, activate or retarget. Over 200k edges with every edge named,
  the pass allocates 42.9 MB against 453.2 MB and runs in 102 ms against 556 ms, and the
  resulting relation is equal, generation counter included. *Class:* **Fix**.
  *Migration:* none. [docs/taxonomy.md](docs/taxonomy.md)

- **A whole-network snapshot of the dense TMS is taken under the read stamp.** `DenseTms`'s
  `deref` built the snapshot map field by field with no stamp held, so a reader taking one
  beside a writer could read `:nodes` before a `sweep!` deleted a datum and `:in` after, and
  come back believing a datum with no node behind it. The `deref` now runs under the stamp
  `-snapshot` already takes. `jtms-concurrency-test`'s dense arm counted 26 torn snapshots
  before the change and none after. *Class:* **Fix**. *Migration:* none.
  [docs/density.md](docs/density.md)

- **The symbol pool drops its older generation at the limit instead of clearing
  wholesale.** The pool held one map and cleared it at 1,000,000 entries. A disk store whose
  index dictionary names several million tokens refilled it within seconds of each clear,
  so the count on the caches page cycled between about 280k and 950k during a recovery,
  and every name in use lost its shared object at each clear. The pool now holds two
  generations: a name found in the older one moves into the newer one, and when the newer
  one reaches half the limit the older one is dropped. A name read at least once per
  generation keeps one object, and the pool still never holds more than the limit.
  *Class:* **Fix**. *Migration:* none. [docs/storage.md](docs/storage.md)

- **A foreign dump reader missing `:versions` or `:replay-belief!` is refused by name.**
  `import!` of an `:engine-dump` applied both fields without a nil check, so a plugin's
  reader map that omitted one threw a `NullPointerException` several frames into the
  import. It now refuses with `:no-foreign-reader` and names the missing field, as it
  already refused a missing `:decode-frame`. *Class:* **Fix**. *Migration:* none.
  [docs/foreign.md](docs/foreign.md)

- **`project.clj` declares top-level `:jvm-opts`, so `LEIN_JVM_OPTS` no longer caps project
  JVMs at C1.** Leiningen's `:base` profile appends `-XX:TieredStopAtLevel=1` whenever
  `LEIN_JVM_OPTS` contains `Tiered`, and it supplies a project's JVM options when the
  project declares none. A shell exporting that variable therefore ran `lein test`, `lein
  perf` and `lein run` without C2. The declared vector replaces `:base`'s and keeps its
  `-XX:-OmitStackTraceInFastThrow`. *Class:* **Fix**. *Migration:* none.

- **`lein repl` waits ten minutes for the project JVM's nREPL ack.** `lein browser` opens
  the KB and loads `VAELII_KB_DIR` before its nREPL server starts, and Leiningen's
  60-second default abandoned a boot whose recover ran longer, leaving the JVM running with
  the single-writer lock held. *Class:* **Fix**. *Migration:* none.

- **Four benches assert their rules `{:direction :forward}` again.** `bench-jtms`,
  `bench-budget`, `bench-scale` and `bench-qcnchain` called `assert-rule` with no
  direction, which is backward-only since 0.18.0, so their rules never fired. `bench-jtms`
  reported 0 justifications on both corpora, and `bench-budget`'s justifications-per-node
  target produced none, so its truth-maintenance row priced premise nodes only. The
  re-run measures 77 B per justification on the rules-heavy corpus, against the 166 B
  `docs/density.md` states. *Class:* **Fix**. *Migration:* none.
  [docs/density.md](docs/density.md)

- **The `:bench` profile passes `-Djol.magicFieldOffset=true`.** jol measured a hidden
  class through `Unsafe.objectFieldOffset`, which a JDK 17 or later refuses, so
  `bench-budget` stopped with `UnsupportedOperationException` at its first block when the
  KB graph reached a `java.util.regex.Pattern` lambda. The property makes jol compute the
  offsets itself. *Class:* **Fix**. *Migration:* none.

- **Every check run records the revision it was taken at.** `lein lint`, `lein
  test-parallel` (so `lein gate`), `lein perf` and `lein test-matrix` each append one row to
  `logs/runs.tsv` as they exit: the revision the run started at, how many files under `src/`
  or `test/` were uncommitted then, the wall clock, the run's closing figures and the
  verdict. The stage logs already held all of this, one directory at a time and under
  `target/`, which `lein clean` deletes. `lein lint` and `lein perf` keep their reports too,
  at `logs/lint/` and `logs/perf/`, where before only a run under the gate was captured, and
  the `perf`, `test-multi-jvm` and `test-fuzz` aliases run through the same harness, so a
  selector no gate reaches now leaves a report and a row. `bash scripts/runlog-backfill.sh`
  appends the rows nothing wrote at the time, and is idempotent on the log path. A matrix
  over fewer configurations than the routine roster is recorded under its own variant,
  decided on what the run covered, so a subset does not overwrite when the whole roster last
  went green. *Class:* **Additive** (developer tooling; no public function moves).
  *Migration:* none. [scripts/lib/runlog.sh](scripts/lib/runlog.sh)

- **`tools/vaelii-top` shows the checkout and what has been checked in it.** A btop-style
  terminal UI over `logs/runs.tsv`, the run directories, `git` and `ps`, in five tiles: the
  version, branch, revision, dirt and tree counts; the last run of each check with the
  revision it was taken at; the git history with a column per check, showing what ran at
  each commit and what it said; the JVMs on the machine with the run each belongs to; and
  the parts of a run under way. **A commit with no run of its own shows the verdict it
  inherits** — where nothing a check reads changed between that commit and one that did
  run, the tree the check sees is the same tree — and an inferred cell is drawn in the
  never-ran grey rather than in a verdict colour. `scripts/test-matrix.sh` writes a
  `configs.tsv` into its run directory naming the process group each configuration was
  launched in, so the JVM tile can say which configuration a JVM is running. `vaelii-top --once` prints the verdicts as
  lines and exits non-zero unless every one is a pass at HEAD over a clean tree. A Python
  package beside the engine rather than part of it: it runs nothing and writes nothing, so
  it cannot change what it reports. *Class:* **Additive** (developer tooling; a Python
  package beside the engine). *Migration:* none.
  [tools/vaelii-top/README.md](tools/vaelii-top/README.md)

- **`lein lint` reads the Python under `tools/` as well.** A twelfth check, `tools`, runs
  ruff over the tracked `*.py` there, which no earlier check reached: four of the eleven are
  Clojure, `shellcheck` globs `scripts/*.sh`, and the two doc checks walk `docs/` plus a
  fixed list of root markdown. The rules and the 3.9 target are
  `tools/vaelii-top/pyproject.toml`, and the file roster is `git ls-files`, so the
  gitignored virtualenv beside the package is excluded without a list to keep. **The check
  skips rather than fails when ruff is absent**, and the row says `skipped` rather than
  `clean`, because no CI image this repo uses carries ruff and a hard check would red every
  runner. `lein lint-tools` runs it alone, and the `prose` check reads `tools/` now too.
  *Class:* **Additive** (developer tooling; a lint check over `tools/`). *Migration:* `brew
  install ruff` or `pipx install ruff` to have the check actually run.
  [scripts/lint-tools.sh](scripts/lint-tools.sh)

- **`lein test-matrix` shuffles its launch order and prints the seed.** The matrix ordered
  its configurations longest-first, so the same set started in the first wave every time and
  a run stopped short — by `--fail-fast`, by ^C, by a box that needed the cores back — had
  covered that same prefix and never the rest. The order is now a seeded shuffle, the seed
  is printed with the header and again with the verdict, and `TEST_MATRIX_SEED=<n>` runs an
  order again. `--ordered` restores the longest-first schedule, which finishes about a
  minute sooner over the routine roster because the configuration that starts last sets the
  wall clock. The run directory's `matrix.plan` gains `order`, `seed` and `sequence` rows.
  *Class:* **Additive** (developer tooling; the matrix's launch order). *Migration:* none —
  pass `--ordered` for the previous order. [docs/operations.md](docs/operations.md)

- **`VAELII_AUDIT_SUPPORT=<dir>` lists the justifications that rest on a supporter their
  conclusion's context cannot see.** The suite's teardown reads every stored justification
  of a live KB once, and writes one EDN map per offending justification into
  `<dir>/<pid>.edn`: the conclusion and its context, the informant, whether the conclusion
  is believed, and each supporter the conclusion's context does not see. Unset, teardown
  does nothing more than before, and set, no test's outcome changes. *Class:* **Additive** (developer tooling; a test-suite audit behind an environment switch).
  [docs/operations.md](docs/operations.md)

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

**15 entries** — 2 Breaking, 1 Refusal, 9 Additive, 3 Fix. Assertive argument types become
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
`arityMin`, `(lessThan`, `(greaterThan`, `(termsRelated`, `(functionCorrespondingPredicate`

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

**93 entries** — 5 Breaking, 12 Refusal, 32 Additive, 22 Fix. The largest release:
calendar time, joined queries and a sweep through the entry points that refuse.
`CxChange` ships an event calculus, calendar constructors give a date its own endpoints
so it orders itself, and a metric constraint narrows an interval relation. `or` is
accepted in a rule antecedent, stored as one rule per alternative, and refused as a
goal. Every search entry point takes a bound and the daemon holds them to its ceiling.
Twelve refusals close inputs whose acceptance stored junk, and the `:disk` and
`:pg-disk` pairings are renamed to say that both halves are out of core.

*Breaks:* `:disk`, `:pg-disk`, `VAELII_TEST_BACKEND=disk`, `edit!`,
`edit-with-consequences!`, `apply-proposal!`, `contexts`, `count-in-context`,
`contextDenotingFunction`, `lein cli load`, `prove`, `provable?`, `query`, `argue`,
`forward-chain`, `ask`, `ask?`, `query-plan`, `abduce`, `sentexes-matching`,
`handle-of`, `assert`, `load-text!`, `lein cli assert`, `unaryPredicate`,
`binaryPredicate`, `ternaryPredicate`, `/kbs`, `lein serve --listen <flag>`,
`vaelii.client/client`, `:timeout-ms`, `:token`, `dereference`, `resolve-by-locator`,
`set-trust!`, `trust-of`, `display-name-of`

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
