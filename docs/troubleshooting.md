# When it does not do what you meant

- **Covers:** what to check, symptom by symptom, when a query, a rule, or `assert` does not
  do what you expected.
- **Not here:** how belief and defeat are actually computed → [nmtms.md](nmtms.md); the
  record and index stores a symptom often traces back to → [storage.md](storage.md).
- **Assumes:** sentex, context, belief → [glossary.md](glossary.md).

Every other page here describes a subsystem. This one is indexed by **symptom**, because
a symptom is what you have when you are stuck, and the engine's hardest failures are the
ones where nothing goes wrong: a query answers `()`, an `assert` returns a handle, and
both are legitimate values that no error can distinguish from the answer you wanted.

Each entry says what you would have observed, how to confirm it in one call, and the
fix. The mechanism stays in the subsystem's own page and is linked, never restated.

| Symptom | Most often |
|---|---|
| [A query answers nothing](#a-query-answers-nothing) | the reading context sees neither the fact nor the rule |
| [A rule does not fire](#a-rule-does-not-fire) | it fired and the conclusion had nowhere to go |
| [Facts I never asserted](#facts-i-never-asserted-or-facts-i-did-and-cannot-find) | two KBs on one in-RAM space |
| [Both `P` and `not P` are believed](#both-p-and-not-p-are-believed) | `:default` strength on something known true |
| [`assert` refused it](#assert-refused-it) | a naming invariant — the `:type` says which |
| [An `argIsa` constraint never convicts](#an-argisa-constraint-never-convicts) | the argument's type is outside the hierarchy |
| [`prove` returns more than I count](#prove-returns-more-solutions-than-there-are-answers) | one solution per derivation, not per answer |
| [A foreign KB will not load](#a-foreign-kb-will-not-load) | no reader on the classpath |
| [`open-kb` refuses an unknown backend](#open-kb-refuses-an-unknown-backend) | a `:backend`, `:records`, `:index` or `:tms` opt names something the storage layer doesn't implement |
| [The disk KB will not open](#the-disk-kb-will-not-open) | another process holds the lock |
| [The daemon exits 2](#the-daemon-exits-2-without-serving) | `--listen` names an address and no token is set |
| [Every call to the daemon is refused](#every-call-to-the-daemon-is-refused) | the client presents no token, or a different one |
| [The log does not say enough](#the-log-does-not-say-enough) | the run boundaries are at `:debug`, and the level is a dial |

## A query answers nothing

`()` is a legitimate answer, so nothing is thrown and nothing is logged. Four causes, in
the order they are worth ruling out.

**The reading context does not see the fact.** A read sees what its context sees, up the
`genlContext` cone — so a fact in `NaturalWorldContext` is invisible from
`UniverseContext` unless an edge says otherwise, and the direction matters:
`(genlContext NaturalWorldContext UniverseContext)` says the *natural world* context reads
the *universe* one, not the reverse. Confirm by asking with no context filter and seeing
whether the sentex exists at all:

```clojure
(v/sentexes-matching kb '(dog ?x))          ; every context
(v/sentexes-matching kb '(dog ?x) 'SomeContext)
```

Two answers from the first and none from the second is this. [contexts.md](contexts.md).

**The sentex is stored but not believed.** Storage and belief are different questions: a
retracted premise, a defeated default or an unrecovered store all leave a record that
`sentexes-matching` filters out. `(v/in? kb handle)` answers the belief question directly,
and `(v/why-not kb goal context)` says which of the two it is — `:not-stored` is a
different fix from a defeat. [nmtms.md](nmtms.md), [taxonomy.md](taxonomy.md).

**The store was opened without recovering.** A KB over records that already exist has an
empty TMS and taxonomy until `recover` runs, so every query answers nothing and every
`isa?` answers false — all of it quietly. `{:recover? :auto}` is the default and does this
at construction; `{:recover? false}` is the setting that turns the whole class of symptom
back on. `(v/sentex-count kb)` reading non-zero while queries answer nothing is the tell.
[storage.md](storage.md).

**The membership was written the way another system spells it.** `(isa Muffet Dog)` stores a
two-place predicate named `isa`, which nothing reads; types here are unary, so membership
is `(dog Muffet)` and the hierarchy is `genl`. The front door logs this once per process,
and `docs/naming.md` states the convention. [naming.md](naming.md).

Past those: `ask` answers from what is stored or cached and **never expands rules**, so a
goal only a rule reaches comes back empty from `ask` and answers from `query` with a
`:max-depth`, or from `prove`. The table of which reader does what is
[api.md](api.md#choosing-a-query-function).

## A rule does not fire

Most often it *did* fire, and the conclusion had nowhere to land. A firing needs one
context that sees the rule, every antecedent fact, and any `genl` edges the match climbed
through — sibling contexts with no common descendant have no such place, so the conclusion
is dropped rather than stored. It is recorded, not silent:

```clojure
(v/violations kb)      ; :no-placement entries, with :rule-context and :fact-contexts
```

The entry names the contexts that had to be seen together; the fix is the `genlContext`
edges that put one context above all of them. [contexts.md](contexts.md),
[inference.md](inference.md).

Three other causes, each with its own tell:

- **The rule is backward-only.** `{:direction :backward}` means the conclusion exists
  while a backchainer is looking for it and is never materialized, so `ask` and
  `sentexes-matching` do not see it and `prove` does. [inference.md](inference.md).
- **An exception guards it.** `(v/why-not kb goal context)` answers `{:reason :excepted}`
  with the exception and the rule handle. [exceptions.md](exceptions.md).
- **A rival defeated it.** `why-not` names the defeater; `(v/conflicts kb)` lists what was
  arbitrated. A `:default` losing to a `:monotonic` rival is the ordinary case.
  [nmtms.md](nmtms.md).

## Facts I never asserted, or facts I did and cannot find

**The space number names the store.** `:space` defaults to 0, so `(open-kb {})` twice in
one process is one set of records behind two KB values — the
second recovers the first's facts, and from then on a write through either is invisible to
the other, because belief is per-KB and only the writer's is relabelled. This is the REPL's
ordinary gesture for starting clean, so the second such open warns. Give a KB that wants
its own store its own space:

```clojure
(def kb2 (v/open-kb {:space 2}))
```

Naming the number at all — 0 included — says the sharing is meant. One number covers both
stores, so there is no half-shared arrangement to land in by accident. A `:disk` KB is
keyed by its directory instead, and takes a lock. [storage.md](storage.md).

A KB that has *lost* facts is usually the other half of the same question: see the
unrecovered store above, and `(v/recover kb)` to rebuild belief from the records.

## Both `P` and `not P` are believed

Not a bug, and the most surprising thing here on a first read. At `:default` strength a
contradiction **coexists**: `(v/query? kb '(likesCake Tom) ctx)` and the same question of
`(not (likesCake Tom))` both answer true, and neither side is defeated, because a default
is defeasible at the edges and the KB does not guess which of two defaults to drop.

Confirm with `(v/contradictions kb)`, which lists the coexisting pairs, and
`(v/conflicts kb)` for the ones that *were* arbitrated. The fix is to say that the side you
know is true is known:

```clojure
(v/assert kb '(likesCake Tom) 'SomeContext {:strength :monotonic})
```

Assert known-true content with `:monotonic`; the default is `:default`, which is right for
most of a common-sense KB and wrong for the fact you are certain of.
[nmtms.md](nmtms.md), [levels.md](levels.md).

## `assert` refused it

Every refusal carries a `:type` in its `ex-data`, and that is what to discriminate on
rather than the message text. `(v/check kb sentence context)` asks the same question
without storing anything, and answers with the identical problem.

| `:type` | What it means |
|---|---|
| `:naming` | a symbol's spelling does not match its role — [naming.md](naming.md) |
| `:not-ground` | a fact with a variable in it; write a universal as a rule |
| `:shape` | not an s-expression at all — a string, `nil`, a map, a bare symbol |
| `:not-well-formed` | a malformed connective frame, such as a bare `(implies)` |
| `:not-range-restricted` | a rule variable in the consequent that no antecedent binds |
| `:arg-type` / `:arg-genl` | an `argIsa` / `argGenl` constraint convicted it — [argtypes.md](argtypes.md) |
| `:disjoint` / `:functional` / `:asymmetric` | a definitional clash — [exceptions.md](exceptions.md) |
| `:unknown-option` | an option key nothing reads, or a non-map `opts` |

The one worth knowing in advance: **snake_case means arity 1.** An underscored functor
names a type, and a type is a one-place predicate, so `(lives_in ?x cold_place)` is refused
— write `livesIn`. The full roster of checks, with the regexes, is
[naming.md](naming.md).

## An `argIsa` constraint never convicts

`(argIsa parentOf 1 person)` plus `(disjoint dog person)` plus `(dog Muffet)` accepts
`(parentOf Muffet Bob)` without complaint. That is open-world and deliberate: the check
convicts only when the argument's own type closure reaches `thing`, and `dog` reaches it
only once something says so. Add the edge and the identical assertion throws `:arg-type`:

```clojure
(v/assert kb '(genl dog thing) 'UniverseContext)
```

So a type that appears only as a fact's functor and never as a `genl` node leaves every
constraint naming it dormant. The same precondition governs the entailment reading —
[argtypes.md](argtypes.md), whose "Where it does not mint" table is the full list of cases
where nothing is derived.

## `prove` returns more solutions than there are answers

`prove` returns **one solution per derivation**, so a goal reachable two ways — a fact
forward chaining already materialized *and* the rule that concludes it, or two rules with
the same consequent — comes back twice with equal binding maps. `(count (prove …))` is a
count of proofs.

```clojure
(distinct (v/prove kb goal ctx))     ; the answer set
(v/ask kb goal ctx)                  ; projected and answered once, no rule expansion
```

[api.md](api.md#choosing-a-query-function).

## A foreign KB will not load

This build reads its own dump format and nothing else; a corpus or a foreign dialect needs
a reader on the classpath, which ships as a separate artifact. A found KB is still
*offered* without one — the honest answer to "I cannot read this" is a load that fails
saying so — so the card appears and the load reports `this build does not read
cyc-corpus`. That message means the reader is absent, not that the KB is bad.

The route to a reader, and what each load costs, is [kbs.md](kbs.md); the seam it plugs
into is [foreign.md](foreign.md). Two things about the development tree specifically:
`lein install` in the sibling installs the sibling's *own* current version, so it satisfies
the `:with-foreign` pin only when the two versions agree — `lein lint`'s versions check
holds that. And `scripts/link-checkouts.sh` puts the sibling on **every** command's
classpath, so a foreign read that works may be the link rather than the code.

## `open-kb` refuses an unknown backend

Five throws share `:type :unknown-backend`, every one of them at `open-kb` before a
store is ever touched, so there is no partial KB to close. The other key in `ex-data`
says which opt was wrong:

| `ex-data` carries | What was wrong |
|---|---|
| `:backend` | the `:backend` sugar names nothing in the table — [storage.md](storage.md#backend-selection-two-independent-axes) lists the seven legal names |
| `:records` **and** `:index` together | the axes resolved to `{:records :memory :index :disk}`, the one pairing among eight the table refuses — a durable index over records that do not survive JVM exit |
| `:records` alone | the `:records` opt names a kind nothing implements — `:memory` or `:disk` are the only two |
| `:index` alone | the `:index` opt names a kind nothing implements — `:memory`, `:dense`, `:columnar` or `:disk` |
| `:tms` alone | the `:tms` opt names a kind nothing implements — `:reference` or `:dense` |

`(v/open-kb {:backend :bogus})` throws `unknown KB backend :bogus — want one of […], or
the :records / :index opts`; `(v/open-kb {:records :memory :index :disk})` throws `the
:disk index needs :disk records — …`; a bad `:records`, `:index` or `:tms` kind names
itself the same way (`unknown record backend …`, `unknown index backend …`, `unknown TMS
…`). None of these reaches a daemon client: `open-kb` runs before the daemon answers its
first request, so a caller across the wire opens a KB the daemon already opened.

## The disk KB will not open

One process, one writer. A `{:backend :disk}` KB takes an exclusive lock on its directory,
and the refusal names the other JVM's pid, host and the time it took the lock. Two
processes over one store corrupt rather than lag, which is why it is a lock and not a
warning: point this JVM at a different directory, or `(v/close!)` the KB holding it.
[storage.md](storage.md).

A daemon holding a directory is the ordinary case, and the browser reads one over the API
rather than opening the store beside it — `lein run -m vaelii.web --attach HOST PORT`.
[operations.md](operations.md).

## The daemon exits 2 without serving

`--listen` names an address, and a bind that publishes `POST /op` requires
`VAELII_API_TOKEN`. That flag exposes the KB's only writer *and* drops the `Host`
allowlist, so without the refusal the exposed configuration would be the one with the
fewest checks. Export a token, or drop the flag and take the loopback default.

The refusal lands before the KB is opened, so a daemon that is not going to serve does
not first take the directory's single-writer lock off the process that could have. On
the loopback default a missing token is not an error: the daemon starts and says which
of the two postures it is in, every time, which is the line to grep for afterwards.

The `Host` allowlist drop is not held to the same refusal — a daemon fronted by a
reverse proxy legitimately receives whatever `Host` the proxy sets, and an operator
cannot always enumerate that in advance, so a refusal here would trip a normal
deployment as often as a broken one. Left unset, the daemon starts anyway and warns
once (`:id :vaelii.impl.serve/open-hosts`) rather than staying silent; the startup
line's `:hosts` — `:allowlisted` or `:open` — says which policy is in force, beside
`:auth`. `VAELII_ALLOWED_HOSTS` (comma-separated) names the hosts a public bind should
answer and silences the warning. [operations.md](operations.md).

## Every call to the daemon is refused

A 401 carrying `:type :unauthorized` means the token the caller presented is not the one
the daemon holds. It does not say which way it went wrong — a wrong token, a missing
header and a malformed `Authorization` line answer identically, because a refusal that
distinguished would be an oracle for guessing the token.

Both ends read `VAELII_API_TOKEN`, so a daemon and a client on one host agree without
either being configured; a client elsewhere needs the value exported in its own
environment or passed as `:token`. An attached browser is a client too, and one started
without the token shows the daemon's own refusal on every page rather than an empty KB.
`GET /health` answers unauthenticated by design, so a probe that succeeds while `POST
/op` refuses is the daemon working, not a half-configured one. [operations.md](operations.md).

## The log does not say enough

The level is a dial, and a running process turns it — `(v/set-log-level :debug)` from a
REPL, `VAELII_LOG_LEVEL=debug` at startup — so a daemon a week into a run does not have
to be restarted to answer a question, which matters because a `:disk` KB pays `recover`
on the way back up. At `:debug` every chaining run says what it concluded and how long
it took, every settle says what it cost in passes and what it found, and a dropped
conclusion is followed by the rule behind it: the `:warn` line names that rule by
**handle**, which is not a thing a log reader can look up.

Two silences are deliberate and neither is a fault to chase. With nothing set the engine
installs no backend at all, so an application holding its own function in
`taoensso.trove/*log-fn*` keeps it. And neither server logs a request: a 401, a 403, a
413 and a 415 leave nothing on the server, so the status code the *client* holds is the
evidence for one. [operations.md](operations.md).

## The browser is not on the port I asked for

`VAELII_WEB_PORT` is the **default**, so an explicit `--port` wins over it, and a value
that does not parse falls back to 3000 rather than refusing to start. Both `lein browser`
and `lein run -m vaelii.web` read it. The startup log names the interface and port it
actually took, which is the thing to read rather than the command you typed.
[web.md](web.md).
