# Changelog

## 0.5.0 — 2026-08-07

Operating the engine, in the two senses a running process needs: what it will let a
caller do, and what it will tell an operator it is doing. The daemon authenticates and
refuses to bind an address without a credential, ships as a container image, and says
which posture it started in; every switch the build reads has a row in a table a test
keeps honest, and the four that took a presence where they meant a value now refuse a
value nothing reads; the log level is a dial a running process turns; and the failures
that look like answers — a query that returns `()`, a KB that shares another's store, a
sentence legal enough to store and wrong enough to never match — each gained something
that says so. Beside all of that, two entries are about the vocabulary rather than the
process: a name can carry two more roles than it could, which is what a KB built by
reading text needs of it, and a reader that counted a context's contents was the only one
of three that did not say `count`. Nine entries are marked **Breaking**, one of which
simplifies a store's name from two numbers to one and one of which turns a switch's name
the right way up. The three **Refusal** entries (CONTRIBUTING §3.8)
cover input that is newly refused where what 0.4.0 did with it was run a configuration
nobody asked for and report a clean pass, so no working caller loses anything it had.
Each entry says what a reader would have observed; the mechanism is in the subsystem's
doc, and the entry names it.

**Triage, for a 0.4.0 caller.** Every Breaking and Refusal entry below carries its own
one-line *Migration*; this is the index to the ones that touch something you have
written or deployed.

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
  answers `:sense` for a disambiguated type (`abrasive-grit`, `abandonment-romantic`) and
  `:lexeme` for a symbol in the `lex` namespace (`lex/fool's_gold`), so its documented
  domain gains two values a total `case` over it has no arm for. Two things move at a
  `:strict` front door with them: a lowercase dashed name is a legal unary type where it
  matched no convention and was refused, and a lexeme applied to arguments is refused
  (`:lexeme-functor`, a seventh `problem-classes` key) since a surface form names no
  relation. *Migration:* a `case` over `term-role` gains `:sense` and `:lexeme` arms, or
  a `default`. Nothing else changes unless you wrote a `lex`-namespaced predicate, which
  names a lexeme now and cannot be applied to anything.
  `docs/naming.md`.
- **Breaking: `context-size` is `count-in-context`.** The three O(1) cardinality readers
  are one family and two of them said so: `count-with-functor`, `count-with-arg`, and a
  context reader named for a size instead. It delegates to a protocol method already
  called `count-in-context`, so the name it now carries is the one it always answered to
  a layer down. The daemon's op keyword moves with it, since a wire name that disagreed
  with the function would be the same split one seam further out. *Migration:*
  `(v/context-size kb ctx)` becomes `(v/count-in-context kb ctx)`, and `{:op
  :context-size}` becomes `{:op :count-in-context}` — same arguments, same answer, and
  the old spellings are gone rather than deprecated.
  `docs/api.md`, `docs/indexing.md`.
- **Breaking: `different` descends into compound arguments.** It normalized each argument
  with one lookup in the equality closure, and the closure is keyed by symbol — so a
  compound was never found in it and came back unchanged, and `(different (QuantityFn 5
  Kilogram) (QuantityFn 5 Kg))` answered *different* with `(sameAs Kilogram Kg)`
  believed. It now replaces symbols at every depth before comparing, which is the
  congruence its documentation always described. *Migration:* a goal comparing two
  compounds can newly answer false where a merge reaches inside one of them; comparing
  symbols is unchanged, and so is every `different` over terms nothing has merged.
  `docs/equality.md`.
- **Breaking: one space number names a KB's stores, `:space`.** `open-kb` takes a single
  number where it took `:record-space` and `:index-space`, and it defaults to 0; a
  `:disk` KB's derived directory is `space-<n>`, and the suite owns a block of two db
  numbers rather than four (scratch 15, isolated 14). *Migration:* `{:record-space 2
  :index-space 3}` becomes `{:space 2}` — keep the record number, drop the index one;
  either retired key is refused by name (`:type :unknown-option`) rather than ignored.
  Pass `:dir` to name a durable directory the derived spelling does not reach.
  `docs/storage.md`.
- **Breaking: the daemon authenticates, and refuses to bind an address without a
  token.** With `VAELII_API_TOKEN` set, every request carries `Authorization: Bearer
  <token>` or is answered 401 with a `WWW-Authenticate: Bearer` challenge and `{:ok
  false :type :unauthorized}` — a new `:type` on the wire. `GET /health` is the only
  route that answers without it. What the daemon binds decides what it requires:
  `--listen` naming a non-loopback address without a token is one line on stderr and
  exit 2, where 0.4.0 logged a warning and served the whole write block — `assert`,
  `retract`, `edit`, `export`, and the chaining run beside them — to anything that
  could reach the port. `vaelii.client` reads the same variable and takes `:token`.
  *Migration:* export `VAELII_API_TOKEN` for a daemon that names an address, and give
  the same value to every client that reaches it. Nothing changes on the loopback
  default. `docs/operations.md`.
- **Every switch the build reads has a row, and a test keeps the roster honest.**
  `docs/operations.md` gains a configuration table — 56 environment variables and JVM
  system properties, grouped by who sets one, each with where it is read, its legal
  values, its default, and the one thing it decides. `config_surface_test` pins the
  names against `test/golden/config-surface.edn` in both directions and checks each
  `file:line` citation against the line it names, so the table cannot drift from the
  code without a failing test. CONTRIBUTING §3.8 files a renamed or removed switch as
  **Breaking**.
- **Refusal: the four harness switches read a value instead of a presence.**
  `VAELII_RETE` and the hierarchical-retrieval switch were membership tests, so `=0` ran
  the sweep it names and an exported-but-empty variable ran one nobody asked for;
  `VAELII_QUERY_ENGINE` and `VAELII_QUERY_STRATEGY` took a bare `(keyword …)`, so a
  misspelt engine ran the *default* and reported a clean pass for a configuration
  nothing exercised — the worst shape a test switch can have, since the result reads as
  evidence. All four take the engine's boolean vocabulary now and refuse anything else
  by name. Beside them, a test calls each reader with the properties cleared, so the
  table's **Default** column fails rather than merely reading wrong. All four are read
  only by the test harness — `docs/operations.md` lists them under *Developer*, and
  nothing in a deployment sets one — which is what keeps a silent change of sense inside
  a Refusal rather than making it a ninth Breaking. *Migration:* none
  for a value in the vocabulary; a suite or CI job relying on `=0` meaning *on* now gets
  the sweep off, which is what it says.
- **Refusal: the ASP backend switches are read against their domains, at the door.**
  `VAELII_ASP_SOLVER` took a bare `(keyword …)`, so a misspelt backend matched no arm of
  the selector and ran **auto** — a run pinned to clasp could use clingo and report a
  clean pass for a backend nothing exercised. `VAELII_CLINGO_MAX_BYTES` parsed with a
  bare `Long/parseLong` inside a cached delay, so a non-numeric value threw from the
  first ASP solve rather than from the configuration that was wrong. Both are read
  through `vaelii.impl.config` now, which puts them in `config/check!` — refused at
  `open-kb`, by name, in the same shape as every other switch. *Migration:* none for a
  legal value.
  `docs/operations.md`.
- **Breaking: `VAELII_NOHIER` is `VAELII_HIER`, and the sense is the other way up.**
  A switch that carries the negation in its own name makes `=0` mean *on*, which is the
  one thing a reader must not have to work out at a glance — and the entry above had
  just made the value load-bearing, so the two had to move together or `=0` would read
  as the fallback path it now selects. `VAELII_HIER` defaults `true` (the set-algebra
  retrieval), and `VAELII_HIER=0` routes every context-scoped match through the
  reference nested fan-out. *Migration:* `VAELII_NOHIER=1` becomes `VAELII_HIER=0`; a
  `VAELII_NOHIER` left set is simply unread, since a variable cannot be refused by name.
  `docs/operations.md`.
- **The log level is a dial a running process turns.** `vaelii.core/set-log-level` takes
  one of `:error :warn :info :debug :trace` and installs Trove's console backend at it;
  `log-level` reads back what is in force, and `VAELII_LOG_LEVEL` says it at startup (a
  value outside the five is refused by name). Unset, the engine installs **no** backend
  at all, so an application holding its own `taoensso.trove/*log-fn*` keeps it. Three
  `:debug` statements are what make turning it up worth doing: what a chaining run
  concluded and how long it took, what a settle cost and found, and the rule a dropped
  conclusion came from. `docs/operations.md`.
- **Breaking: `VAELII_WEB_PORT` moves `-main`'s port, and not only `lein browser`'s.**
  `dev-repl` read the variable and `-main` did not, so `VAELII_WEB_PORT=3011 lein run -m
  vaelii.web` bound 3000 and logged 3000. Both read one `default-port` now: the variable,
  else the `vaelii.web.port` property, else 3000; an explicit `--port` still wins.
  *Migration:* a deployment that set the variable for `lein browser` while relying on
  `-main` ignoring it now moves both; pass `--port 3000` to pin `-main`.
- **Breaking: a search-path directory is probed for its first 200 entries, and a KB
  below the cut no longer appears on `/kbs`.** `sources` is recomputed per request, which
  is what lets a corpus appear with no restart and what made the scan unbounded — a
  `classify` per candidate, and a size estimate per `:store` one, on every page load.
  `catalog/max-discovered` bounds it, and the cut is named on the page and in the log,
  since a list that quietly ends early reads as "this machine has no other KBs".
  *Migration:* name the ones that matter in the catalog file to list them regardless of
  the count. `docs/catalog.md`.
- **The front door says what a legal-but-wrong sentence should have been.** `(isa Muffet
  Dog)` breaks no naming invariant, so it stored a two-place relation nothing reads and
  `(isa? kb 'Muffet 'Dog)` answered false with nothing to search for. `nm/advice` reads
  intent where `problems` reads the invariants: it recognizes the shape and logs a
  `:warn` once per process spelling the rewrite that was meant. Beside it, a
  `:no-placement` drop names `genlContext` and points at the `:rule-context` /
  `:fact-contexts` already on the entry. `docs/naming.md`.
- **A second `open-kb` defaulting onto the shared in-RAM space now warns**, naming both
  fixes — give the KB its own number, or name `{:space 0}` explicitly to say the sharing
  is meant. A warning rather than a refusal, since sharing the space is how `recover`
  sees the same records and how a base is mounted. `docs/storage.md`.
- **Refusal: the CLI checks each command's argument count before it dispatches, and
  `help` names what each one takes.** `dispatch` reached into `args` with `nth`, so `lein
  cli assert '(dog Rex)'` answered `error: IndexOutOfBoundsException` — true about a
  vector, no help to someone who left off a context — and a long line was worse, since
  the extra operand was dropped in silence. One table now carries every command's arity,
  operands and gloss, so `check-arity!` and the usage text cannot go out of step.
  *Migration:* none for a call already at the right arity; `lein cli help` prints the
  count each command takes. `docs/operations.md`.
- **`docs/troubleshooting.md` is a new page, indexed by symptom rather than by
  subsystem.** The engine's hardest failures are the ones where nothing goes wrong — a
  query answers `()`, an `assert` returns a handle, and both are legitimate values no
  error distinguishes from the answer that was wanted — so a reader has to already know
  the cause to find the page explaining it. Nine symptoms, each with what you would have
  observed, how to confirm it in one call, and the fix.
- **`lein lint` gains a versions check, and the kondo row notes a local/CI version
  mismatch.** The `:with-foreign` pin and `defproject`'s own version are cut together and
  nothing held them to it: the 0.4.0 bump left the pin naming `0.3.0`, so every
  `lein with-profile +with-foreign` command failed to resolve. `lint-versions` reads that
  pair and the `lein-cloverage` version stated twice, failing when either disagrees. The
  kondo row prints a `NOTE` — never a failure — when the local binary is not the version
  CI pins, since a newer kondo infers more than an older one flags.
- **Three doc samples now print what they actually produce, and `prove`'s docstring says
  it counts proofs, not answers.** `prove` returns one solution per derivation, so a goal
  reachable both as a materialized fact and as the rule concluding it comes back twice
  with equal maps — wrap it in `distinct` for an answer set, or reach for `query` / `ask`,
  which project to the goal's variables and answer each binding once.
- **The daemon ships as a container image**, with a two-stage `Dockerfile` and
  `docker-compose.yml`: a build stage that runs `lein uberjar`, and a runtime stage of a
  JRE and the jar alone. The container binds an address, so the token is required — an
  image run without `VAELII_API_TOKEN` does not start rather than serving
  unauthenticated. One container per volume; a second opener is refused `:disk-locked`
  rather than scaled, which is why the compose file carries no `replicas:`. No `-Xmx` and
  no collector flag are baked in, the second measured rather than omitted, and a JVM with
  its own reason to ask has the new `:zgc` profile. `docs/operations.md`.
- **A reflection warning and an uncalled public var now stop the build.** Both signals
  were already emitted and neither was read. `lein lint` gains two rows: **`reflect`**
  compiles `src` and `bench` and fails on any reflection, auto-boxing or primitive-recur
  warning (the test tree is covered through the gate's own test log instead, since
  compiling it here costs 8s → 74s), and **`unused`** reads clj-kondo's analysis over
  `src test bench` and fails on a public definition with no usage, against
  `scripts/unused-publics-baseline.txt`. Ten warnings had to go first, none in `src`.
  `lein lint` is 9/9 and about 15s longer. CONTRIBUTING §1.1.
- **Breaking: `org.slf4j/slf4j-nop` no longer reaches a consumer's classpath.** It sat in
  top-level `:dependencies`, so every application depending on vaelii inherited it too,
  where it could win SLF4J's provider race against that application's own backend and
  silence it — the one thing a library must not do on a consumer's behalf. It lives in
  the `:dev` and `:uberjar` profiles now, so every entry point this repo ships still
  carries it while `lein deploy` publishes it as a test-scope declaration a consumer does
  not resolve. *Migration:* an application that ships Jetty, had no provider of its own,
  and relied on vaelii's to keep it quiet now sees SLF4J's "no providers" line again —
  add `org.slf4j/slf4j-nop`, or any other provider, as its own dependency.
  `docs/operations.md`.
- **A public `--listen` bind with no `VAELII_ALLOWED_HOSTS` now warns.** Naming an address
  drops the `Host` allowlist to every `Host` answered — a deliberate default, since a
  reverse proxy legitimately sets its own and an operator cannot always enumerate it in
  advance — but nothing said so at startup. `host-posture` names the policy
  (`:allowlisted` / `:open`) beside the token question, and a public bind left unset gets
  its own warning, apart from the token and TLS lines so a reader knows which check is
  missing.
- **`docs/troubleshooting.md` and `docs/storage.md` now name `:type :unknown-backend`.**
  `open-kb` throws it from five call sites — an unknown `:backend` sugar name, the one
  `{:records :memory :index :disk}` pairing the axes refuse, and an unknown `:records` /
  `:index` / `:tms` kind — and none carried a line in either doc. The new entry reads the
  other key each throw's `ex-data` carries to say which of the five it is.

## 0.4.0 — 2026-08-05

Correctness fixes found by reading the engine against its own stated invariants, in
the places 0.2.0 and 0.3.0 did not reach: a backward-chaining loop guard that made a
conjunctive query answer nothing, doors that disagreed about what they would accept,
an index trusted without being checked against the records it describes, slots and
keys that let arrival order decide belief, and derived caches a settle read one
revival out of date. Thirteen entries are marked **Breaking** — they refuse input
0.3.0 accepted, rename what it exported, or change an observable contract — which is
why this is 0.4.0. The **Refusal** entries (CONTRIBUTING §3.8) cover input that is
newly refused where what 0.3.0 did with it was corrupt state or answer a different
question in silence, so no working caller loses anything it had. Each entry says what
a reader would have observed; the mechanism is in the subsystem's doc.

**Triage, for a 0.3.0 caller.** Every Breaking and Refusal entry below carries its own
one-line *Migration*; this is the index to the ones that touch source you have written,
so the rest can be read at leisure.

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
| stores skolem witness names across runs | the names moved; rebuild from the assertions (`export!` / `import!`) rather than carrying both spellings |
| parses a daemon 500 for a client mistake | it is a 400 with a `:type` |
| writes `(ist Ctx S)` with other than three elements | it is refused with `:shape` |

- **A conjunctive query could answer nothing while each of its conjuncts answered.**
  `[(anc Tom ?y) (anc Tom ?z)]` was empty where `(anc Tom ?y)` answered twice, because
  the per-path loop guard grew for a whole frame and a queued conjunct is a sibling of
  the expansion, not a descendant. Silent in every direction: forward chaining and the
  node engine both answered, `provable?` said false, `prove-within` reported `:status
  :complete`, and the planner became semantic. `docs/inference.md`, "The loop guard's
  scope is the subtree, not the frame".
- **Breaking: `assert` refuses a sentence that is not an s-expression.** A string — what
  a failed EDN read hands back, from `impl.cli`'s `read-arg` and the daemon's `:args` —
  was stored, indexed and believed as an object no query can match; `nil` likewise; a
  symbol, number or map threw a bare `UnsupportedOperationException` with no `:type`.
  `check` refused all five, so the door built to predict `assert` disagreed with it.
  *Migration:* nothing a working caller sent is refused; fix the producer that handed
  `assert` unread text, and discriminate on `:shape`.
- **Breaking: an `exceptWhen` query's literals are held to the naming invariants.**
  `(exceptWhen (lives_in ?x cold_place) …)` stored a literal `docs/naming.md` says is
  refused, as an exception no query could match — so the rule read as guarded and fired
  as bare. Both doors now read each conjunct, before the rule is stored, so a refused
  exception leaves no bare rule believed. *Migration:* spell the exception's literals to
  the invariants (`livesIn`, not `lives_in`), and re-check any rule 0.3.0 left bare.
- **Breaking: an `edit!` batch key nothing reads is refused.** `{:adds […]}` bound nil,
  so `edit!` wrote nothing and reported `{:added [] :removed {…0}}` — a success — while
  `check-edit`, whose job is to predict exactly that, reported no problem. Over the
  daemon it was a `200 {:ok true}` for a write that did not happen. *Migration:* spell
  the batch `{:add […] :remove […]}`; a batch under any other key wrote nothing.
- **Breaking: naming one in-RAM space number and not the other is refused.**
  `:record-space` and `:index-space` default independently, so
  `{:backend :memory :record-space 77}` paired a private record store with the
  process-default index every other in-memory KB writes. `assert` then found the other
  KB's handle, read it as a duplicate, **stored nothing**, and returned a handle `in?`
  answered true for. A fork's `:base` and `:overlay` halves take the same keys and are
  refused the same way. *Migration:* name both or neither, in every opts map.
- **A durable index is checked against the records it claims to describe.** `layout.edn`
  gates the index's key shape; nothing gated its coverage, so a short index opened
  clean, answered short forever and re-cemented its own stamp — and re-asserting a fact
  it could not find minted a second handle for a sentence already stored. Three ways in:
  a torn `kv.log` tail, a directory grown under a derived-index mode, and a crash
  between the record write and the index batch. `docs/storage.md`.
- **Breaking: `assert` acts on `:direction` instead of accepting and dropping it.** Only
  `assert-rule` read the key, so a rule asserted `{:direction :backward}` stored `:both`
  and forward-chained, materializing the cross product a backward-only rule exists to
  avoid. A `:direction` on a non-rule, one contradicting the sentence's own wrapper, and
  a value outside the roster are refused rather than resolved. In the same pass a
  non-map `opts` answers `:unknown-option` from both doors, where `check` said `:shape`.
  *Migration:* spell the direction `:backward` (`:forward` `:backward` `:inert` `:both`);
  a `check` caller matching `:shape` for a non-map opts matches `:unknown-option` now.
- **Breaking: a re-asserted rule's direction and defeasibility resolve by content.**
  Neither slot is in the identity key, so a rule stated two ways resolves to one record
  and the second spelling was dropped — letting arrival order decide a slot that decides
  belief. A bare `implies` after a `set/inertRule` stayed inert and never fired; after a
  `set/defaultRule` it stayed defeasible and lost to a monotonic rival it should have
  tied with. The resolution reaches conclusions already derived, since a justification
  bakes the rule's contribution in as its `:strength` at fire time.
  `docs/canonicalization.md`. *Migration:* the join only widens a slot; to narrow one,
  `retract!` the handle and re-assert the intended spelling.
- **The derived caches are reconciled with what `clear-defeats!` revived.** A settle
  lifts last settle's defeats at its top, but the cached closures were refreshed only in
  `settle-finish` — after `constraint-nogoods` had read them — so discovery asked its
  question against a vocabulary one settle out of date. A `P`/`¬P` pair made visible by
  a revived `genlContext` edge went unarbitrated and `retract!` returned with both
  believed, a state `recover` over the same records disagrees with.
- **The disk KV index reads and publishes its RAM map under the lock.** `apply-ops!`
  read `@data` before acquiring and published after releasing, while `compact!` runs on
  the durability daemon's executor — a thread the single-writer contract says nothing
  about — so a compaction in either window rewrote the log from a map missing the
  in-flight write. `kv-clear!` was sharper: a compaction between its truncate and its
  publish wrote the entire pre-clear map back over the log just emptied.
- **Breaking: a client's mistake answers 400 with a `:type`, not 500 with none.**
  `docs/operations.md` promises every `{:ok false}` carries the type the engine threw;
  an unreadable body, a wrong argument count and an unknown op all answered untyped, the
  first two as 500s. The engine's whole refusal vocabulary now answers **400**, unlogged
  — answered 500 they count as backend faults at every reverse proxy and 5xx alarm.
  *Migration:* a client branching on the status code should branch on `:type`; every
  `{:ok false}` carries a non-nil keyword.
- **The browser's `/propose/*` EDN read catches `Throwable`**, as every other
  untrusted-EDN read in the namespace already does. A deeply nested form raises
  `StackOverflowError`, which an `Exception` catch let escape — and the browser has no
  exception middleware, so it left the handler entirely.
- **Refusal: `query` refuses a non-map `opts` and a negative or non-integer
  `:max-depth`.** Both read as "no depth", which is not an error condition but a
  *different question* — the no-rule-expansion answer, returned as if it were the
  bounded one asked for. `{:max-depth 0}` is admitted: it is that answer asked for by
  name. *Migration:* none for a working caller.
- **Breaking: `edit!` refuses what `check-edit` reports, before applying anything.** The
  two disagreed in both directions: a 4-element `:add` entry applied with the extra
  silently dropped where the dry run reported `:shape`, and a non-sequential entry threw
  a bare `ISeq` error from every door. An unknown `:remove` handle is refused before any
  entry is applied, so a checked-clean batch cannot half-apply. *Migration:* a
  remove-if-present batch filters its handles through `in?` first.
- **The recursive-literal hold-back keys on the peeled predicate.** A `not`- or
  `ist`-headed consequent read its own frame as the predicate, so every frame-headed
  antecedent was "the recursive literal" — two orderings of a negated-head rule minted
  two handles, and a genuinely recursive rule with a negated head lost the hold-back,
  turning right-recursion left-recursive.
- **Breaking: a skolem witness is a function of its rule's content, not its handle.**
  Retracting and re-asserting the same rule re-fired to a *different* witness, so a fact
  stated about the old one silently stopped co-referring — and two KBs holding the same
  knowledge in different orders stored different `termOfUnit` content, a handle in
  stored content that order independence rules out. `docs/skolem.md`. *Migration:*
  rebuild the KB from its assertions (`export!` / `import!` replays firings) rather than
  carrying both spellings.
- **Breaking: `edit` is `edit!`, and `edit-with-consequences` is
  `edit-with-consequences!`.** The batch's `:remove` half runs the same
  `retract-storage!` sweep `retract!` runs, while the name read as additive — the one
  gap in the `!` roster the convention exists to close. *Migration:* rename the calls;
  the wire op stays `:edit`, as `:retract` stays for `retract!`.
- **Breaking: `:bad-opt` is retired, and one compression spelling survives.** Two
  keywords split one failure class on no rule a reader could predict — seven sites said
  `:bad-opt` where thirty-four said `:unknown-option`. *Migration:* discriminate on
  `:unknown-option` and `:unsupported-compression`.
- **Breaking: the dump's `meta.edn` names its dialect `:vaelii`.** Decorative on the read
  side — the frame decides how a sentence is reconstructed — but it is a value in the
  frozen format and a documented key of `import-dump`'s return, so the name it carries
  is now-or-never. *Migration:* a reader matching the old value matches `:vaelii`;
  `import-dump` reads dumps written either way.
- **The node engine's claimed-key reads each guard's identity, not the guard count.** Two
  distinct rules, each carrying its own `exceptWhen`, can rewrite one goal to the same
  canonical residual through the `genl` fan; keyed on the count the two children were
  one key, so the second was dropped before it was enqueued and every answer only its
  exception admits was lost — silently, on the path `query` routes to whenever
  `:max-depth` is given. `docs/inference.md`.
- **A belief flip on a visibility `except` queues the same re-check as its arrival.**
  Only the store and removal chokepoints called `recheck-except`, so an except *defeated*
  by a settle's resolution revived nothing it hid: backward proving answered yes while
  the store held nothing, and which belief set the KB ended with depended on the order
  the except and its defeater arrived.
- **`recover` reads only positive, atomic declarations into the taxonomy.**
  `sentexes-with-functor` returns both polarities and the rebuild arms destructure the
  positive shape positionally, so a stored `(not (genl a b))` bound its inner sentence as
  a taxonomy node and nil as the other — poisoning every cache on any recover, the
  default `{:recover? :auto}` reopen included.
- **A `:neg` nogood is an at-least-one in every reader.** The ASP translation's soft
  branch emitted only the positive body atoms, so a `:neg`-only nogood — what
  `set/softConstraint` over negated choice literals produces — emitted its violation
  witness as an unconditional fact: no steering pressure, and `:violated` reported a
  satisfied at-least-one as broken. `docs/solving.md`.
- **`conflicts` and `contradictions` are content-ordered.** Each report's sides were
  already ordered by content; the *list* came off a hash set of handle-keyed nogoods, so
  which pair `(first (contradictions kb))` returned was an answer about which was typed
  first. `docs/nmtms.md`.
- **Refusal: the connective frames are shape-checked at every door.** An `implies` at
  arity 2 threw a bare `IndexOutOfBoundsException` while arity 4 stored a silently
  truncated rule `check` read as clean; `(not A B)` stored as a positive fact whose
  record and index disagreed; a bare symbol passed as a rule literal was accepted,
  unmatchable; and a non-finite measure magnitude stored cleanly, then threw out of every
  later duration goal in the context. *Migration:* nothing a working caller sent is
  refused — every one of these stored an object no query could match.
- **Refusal: the last open rosters close.** `find-terms` and `abduce` take key rosters (a
  misspelt `:mtch` ran the prefix default; a misspelt `:keep?` tore down the scratch
  context whose handles the caller meant to commit), the CLI refuses a flag outside its
  roster, `escalate` refuses a floor outside 0–7, and `import-dump` refuses an unknown
  `:framing` where it guessed a reader and failed as a `ZipException`. *Migration:* spell
  the key or flag as the refusal's roster lists it.
- **Refusal: the web and serve entry points refuse what their grammars do not know.**
  `vaelii.web --listen` with no address parsed to a nil host — Jetty's wildcard bind,
  with the Host allowlist reading nil as *any* — so a truncated command line put the
  browser's unauthenticated write routes on every interface with the rebinding guard
  off. `serve` read its positionals as a prefix, so `4200 --listen 0.0.0.0 /var/lib`
  dropped the directory and ran a disk daemon in memory. *Migration:* none beyond
  completing the command line.
- **Refusal: the opts and shape rosters reach the remaining doors.** The roster guard
  held at `assert`, `why`, `query` and `open-kb`, and every other door took the misspelt
  key in silence — answering a different question than the one asked. Now refused: an
  `open-kb` mount or durability key without its axis, an opts key nothing reads at
  `forward-chain`, the extent readers, `preview`, `export!`, `import!` and the anytime
  budget maps. *Migration:* spell the key as the refusal's roster lists it.
- **Refusal: the operator's mistakes answer in one line.** A CLI flag missing its value
  bound nil in silence — `lein cli assert '(dog Muffet)' Ctx --strength` stored known-true
  content at `:default` — and now exits 1 naming the flag; `--memory --dir` is refused as
  a contradiction. *Migration:* none beyond completing the command line.
- **The browser and CLI survive what they read.** The repl loop and the CLI command arm
  catch `Throwable`, so a deeply nested form answers `error:` and a next prompt; the
  browser's retract POST makes the `check-edit` round-trip `docs/operations.md` promises,
  so a stale handle answers the problem panel rather than a success-styled "Retracted 0
  sentexes".
- **Refusal: every durability switch is read against a domain, and a value outside it
  fails the open.** Each of the thirteen checkable `vaelii.*` / `VAELII_*` switches was a
  membership test or an equality against one spelling, so none of them had a wrong value
  — every misspelling was the *other branch*, silently.
  `vaelii.disk.auto-compact=disabled` read as compaction on; `vaelii.disk.fsync=always`
  read as the three-second tick, the level the operator was trying to leave. The three
  numeric reads had no catch at all. `docs/storage.md`. *Migration:* none for a working
  setup, but two spellings now *act* where they were ignored — `vaelii.disk.tokens=1` and
  `vaelii.index.snapshot=1` turn their features on, and `vaelii.disk.lock=0` disables the
  lock. Spell what you mean.
- **Refusal: the mapped index image refuses the platform it corrupts on.** The image
  publishes by renaming a new file over the live one while it is mapped, which is what
  put `vaelii.index.snapshot` on macOS and Linux only — `docs/storage.md` said so and
  nothing enforced it, so on Windows the publish failed part-way through a four-file
  commit, in a place naming neither the cause nor the fix. *Migration:* none — the
  property never worked where it is now refused; unset it and `:disk-columnar` rebuilds
  its index on open.
- **Breaking: `assert-rule` refuses a rule literal whose predicate is a variable.**
  `(implies ((?p ?x ?y) (transitive ?p)) (?p ?y ?x))` asserted cleanly and was indexed
  under `?var0`, which no arriving fact and no goal can spell — so the rule answered no
  backward goal at all and fired forward only when the concrete-predicate antecedent
  beside it arrived. Two arrival orders, two answers, from a rule the engine reported as
  accepted. An `:inert` rule is exempt, which is what `CoreContext`'s decontextualized-
  predicate lift is. *Migration:* assert the instantiated rules, one per predicate the
  metarule ranged over.

## 0.3.0 — 2026-08-04

Correctness fixes across the durable index, the snapshot, the JTMS, the export dump
and the bounded prover, a sweep that gives every refusal a `:type`, the one wire
contract 0.2.0's own sweep left qualified, and the serialization both servers' storage
layer already assumed. Then a run of **inference and belief** work: two orders that
reached two answers, the two doors that disagreed about an inherited claim, and two
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
  side of a `genlContext` edge was answerable from exactly one of the two, and only when
  that half was the one the settle moved. `settle/clash-askers` runs the check from the
  candidate's own context and from the maximal common descendant of it and each context
  holding a sentex it could pair with; nothing is widened.
- **A pair per opposing sentex, not per opposing type.** One sentence stated in a general
  context and again in one that sees it is two sentexes, of possibly different strength,
  and a claim that denies it denies both — where the checks named one handle each, so the
  content-first of the two was weighed and the other left believed beside content that
  contradicts it.

## 0.2.0 — 2026-08-03

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

## 0.1.0 — 2026-07-31

The first release. What follows is the development log that produced it, newest
first; every entry below is in 0.1.0.

## 2026-07-30

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

## 2026-07-29

- One front door for backward chaining: the four paths measured, then
  consolidated to two chainers behind one entry point with one dial. A proof
  of an ephemeral answer reads the way `why` does.
- The goal frontier's order is a policy measured on time-to-first-answer,
  `:ground-first` by default; the goal-stack chainer drives one solution at a
  time and level 7 streams its search.
- Foreign formats arrive as a classpath plugin, so a reader ships and retires
  without touching the engine.
- A constraint declaration may name a second sentex it must not weigh, and a
  depth bound has no default because there is no defensible one.

## 2026-07-28

- `lein gate`: lint, the suite, and the scaling claims, measured and failed on
  rather than asserted; five checks added for costs that grow with what they
  must not.
- The columnar index is written once and mapped back; backend names read
  `<records>-<index>`, all seven.
- A literal's matches are remembered and retired on a clock; converging
  branches share one rule expansion; a third backward chainer whose state is
  a frontier.
- The naming invariants belong to the knowledge base, and the bulk door counts
  what it skips.

## 2026-07-27

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

## 2026-07-26

- Contexts got a vantage: every taxonomy supporter records the context it
  asserts from, so disjointness, matching fan-out and settle all read only
  what the asking context can see.
- A firing names the `genl` edges it subsumed through — belief and strength
  run through them like any antecedent, checked against all 24 orderings.
- Records and index became two independent choices, plus an overlay backend:
  a private writable fork over a shared read-only base.
- A knowledge base is readable before it finishes loading, and the suite runs
  on every backend from one script.

## 2026-07-25

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

## 2026-07-24

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

## 2026-07-23

- A performance review, its findings fixed: the disk log records operations
  rather than grown values (killing an O(N²) write amplification), settle
  keeps a coincidence set, re-checks narrow to the moved cone, region
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

## 2026-07-22

- Negation as failure, at top level and in antecedents, with block, sweep and
  revive, and stratification to keep it sound.
- Resource-bounded anytime inference with qualitative cost tiers and a
  cost-ordered forward-chain join; `ask-within` normalizes its goal.
- Reification of non-atomic terms; structural subterm indexing,
  oracle-proven, then on by default.
- The storage seam: index logic onto one key-value protocol, an in-memory
  backend, then the on-disk substrate — files, lock, durability, record
  store, index store.
- The index benchmark harness, and a per-handle provenance side map.

## 2026-07-21

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

## 2026-07-20

- Canonical rule form — canonical variables with a varmap, literal order,
  comparison direction — so rules alike up to renaming share one handle.
- The eight-level lookup-to-query stack, lazy throughout, with a browser page
  showing which level answered.
- Order independence and locality pinned as invariants: region-local
  relabelling, belief-following closures, content-keyed tie-breaks.
- The answer-set layer wired to the edge-solver seam, with a labeling
  materialized as a context; the defeasible layer made sound, six bugs
  pinned as failing tests first; `exceptWhen` began as a failing suite.
- Everything but `core` moved under `vaelii.impl.*`; `!` reserved for
  irreversible operations; tests became net-neutral, and a second concurrent
  run fails fast rather than corrupting the first.

## 2026-07-19

The first day: a contextualized common-sense knowledge base with a trie
index, inference and truth maintenance.

- Sentexes — a sentence plus the context it holds in — stored as records
  behind protocols with nippy serialization; rules are sentexes too, with
  built-in transitivity for types and contexts.
- Forward chaining with dependency-directed retraction, and a backward
  chainer; a non-monotonic TMS with strengths, soft prioritized
  contradictions, and a solver seam.
- An inverted term index, directed rules, disjointness, well-formedness
  checks, and a pluggable prover query engine; structural connectives
  canonicalize into the record; evaluable arithmetic.
- A web browser over the whole thing, over a starter ontology with every
  term documented.
