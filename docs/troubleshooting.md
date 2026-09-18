# When it does not do what you meant

- **Covers:** what to check, symptom by symptom, when a query, a rule, or `assert` does not
  do what you expected — and, at the end, the whole `:type` refusal vocabulary, a line
  each.
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
| [What can I ask about X?](#what-can-i-ask-about-x) | one read answers it — `describe` |
| [A query answers nothing](#a-query-answers-nothing) | the reading context sees neither the fact nor the rule |
| [A rule does not fire](#a-rule-does-not-fire) | it fired and the conclusion had nowhere to go |
| [Facts I never asserted](#facts-i-never-asserted-or-facts-i-did-and-cannot-find) | two KBs on one in-RAM space |
| [Both `P` and `not P` are believed](#both-p-and-not-p-are-believed) | `:default` strength on something known true |
| [`assert` refused it](#assert-refused-it) | a naming invariant — the `:type` says which |
| [My batch half-landed](#my-batch-half-landed) | it no longer can — `edit!` is all-or-nothing; the other batch entry points are not |
| [An `arg` constraint never convicts](#an-arg-constraint-never-convicts) | the argument's type is outside the hierarchy |
| [`prove` returns more than I count](#prove-returns-more-solutions-than-there-are-answers) | one solution per derivation, not per answer |
| [`do/label` refuses to re-run](#dolabel-refuses-to-re-run) | a previous run's labeling context has been written into, or has lost its marker |
| [A foreign KB will not load](#a-foreign-kb-will-not-load) | no reader on the classpath |
| [`open-kb` refuses an unknown backend](#open-kb-refuses-an-unknown-backend) | a `:backend`, `:records`, `:index` or `:tms` opt names something the storage layer doesn't implement — `:axis` says which |
| [The disk KB will not open](#the-disk-kb-will-not-open) | another process holds the lock |
| [The daemon exits 2](#the-daemon-exits-2-without-serving) | `--listen` names an address and no token is set |
| [Every call to the daemon is refused](#every-call-to-the-daemon-is-refused) | the client presents no token, or a different one |
| [The log does not say enough](#the-log-does-not-say-enough) | the run boundaries are at `:debug`, and the level is a dial |
| [The browser is not on the port I asked for](#the-browser-is-not-on-the-port-i-asked-for) | `VAELII_WEB_PORT` is the default and `--port` wins; a value that does not parse falls back to 3000 |
| [I have a `:type` and do not know what it means](#i-have-a-type-and-do-not-know-what-it-means) | the whole refusal vocabulary, a line each, with the page that owns the mechanism |

## What can I ask about X?

Not a failure, and the question that comes before most of the ones below: you have a
term and no idea what the KB will accept about it.  One read answers it.

```clojure
(v/describe kb 'parentOf 'CxWell)
;; {:role :predicate :arity 2
;;  :arg-declarations [{:kind :arg :sentence (arg parentOf 1 animal) :context CxLife} …]
;;  :props #{} :inverse childOf :extent-count 0 :comment ["(parentOf ?parent ?child) …"]
;;  :genls {…} :specs {…} :disjoint {…}}
```

The answer is shaped by the term's **role**, so ask about a type and you get its
supertypes, what it is disjoint from, how many instances are stored and — the one that
answers "what may I say about a dog?" — `:predicates-for-type`, the predicates whose
argument declarations admit it.  Ask about an individual and you get its asserted types
and the predicates it appears under with a count each; about a context, its two `genlCx`
ancestor sets and how many sentexes hold in it.

**The context argument is not decoration.**  An `arg` declaration, an
`abducible_predicate` grant and a `comment` are each a policy of the context that states
them, so `describe` reads them up that context's `genlCx` ancestor set: `(describe kb 'parentOf
'CxCore)` reports no declaration at all, because `CxCore` sits *above* the one that binds
`parentOf`, and a reader there is genuinely unconstrained.  If a declaration you expected
is absent, that is the first thing to check — it is the same ancestor set `assert` consults when
it decides whether to refuse ([contexts.md](contexts.md), [argtypes.md](argtypes.md)).

`lein cli describe <term> [--context C]` is the same read from a shell.
[api.md](api.md).

## A query answers nothing

`()` is a legitimate answer, so nothing is thrown and nothing is logged. Four causes, in
the order they are worth ruling out.

**The reading context does not see the fact.** A read sees what its context sees, up the
`genlCx` ancestor set — so a fact in `CxNaturalWorld` is invisible from
`CxUniverse` unless an edge says otherwise, and the direction matters:
`(genlCx CxNaturalWorld CxUniverse)` says the *natural world* context reads
the *universe* one, not the reverse. Confirm by asking with no context filter and seeing
whether the sentex exists at all:

```clojure
(v/sentexes-matching kb '(dog ?x))          ; every context
(v/sentexes-matching kb '(dog ?x) 'CxSome)
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
is `(dog Muffet)` and the hierarchy is `genl`. The public entry point logs this once per process,
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

The entry names the contexts that had to be seen together; the fix is the `genlCx`
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
- **Another rule already concluded it**, so the firing added nothing to see. `(:subsumption
  (v/kb-quality kb))` names the rules a broader one covers, with the substitution;
  `(:clashes (v/kb-quality kb))` names the pairs whose conclusions would fight if both
  fired. Neither reads the KB's facts — they are static analysis of the rules, so they
  answer on a KB nothing has been asserted into yet. [quality.md](quality.md).
- **An antecedent is missing.** This is the one `why-not` cannot say on its own: the
  conclusion was never stored, so there is no handle, no support and no defeat to report,
  and `:not-stored` is the whole answer. Ask for the near misses:

  ```clojure
  (v/why-not kb goal context {:nearest 3})
  ;; :nearest [{:rule 7
  ;;            :rule-sentence (implies (and (parentOf ?x ?y) (parentOf ?y ?z))
  ;;                                    (grandparentOf ?x ?z))
  ;;            :satisfied [(parentOf Ann ?y)]
  ;;            :missing   [(parentOf ?y Cid)]
  ;;            :bindings  {?x Ann ?z Cid}}]
  ```

  `:missing` is the line to read — it is the fact nobody has asserted, written in the
  rule's own variable names. It is **off unless asked for**, because it runs a bounded
  backward search where the plain call runs none; `:nearest-search` reports which bound
  bit, and a rule further away than `:max-depth` (3 by default) is not reached at all.
  `lein cli why-not '<goal>' <CxName> --nearest 3` is the same read.
  [api.md](api.md), [inference.md](inference.md).

## Facts I never asserted, or facts I did and cannot find

**The space number names the store.** `:space` defaults to 0, so `(open-kb {})` twice in
one process is one set of records behind two KB values — the
second recovers the first's facts, and from then on a write through either is invisible to
the other, because belief is per-KB and only the writer's is relabelled. This is the REPL's
ordinary gesture for starting clean, so the second such open warns. Give a KB that wants
its own store its own space:

```clojure run
(def kb2 (v/open-kb {:space 2}))
```

Naming the number at all — 0 included — says the sharing is meant. One number covers both
stores, so there is no half-shared arrangement to land in by accident. A `:disk` KB is
keyed by its directory instead, and takes a lock. [storage.md](storage.md).

A KB that has *lost* facts is usually the other half of the same question: see the
unrecovered store above, and `(v/recover kb)` to rebuild belief from the records.

## Both `P` and `not P` are believed

Not a bug, and the most surprising thing here on a first read. At `:default` strength a
contradiction **coexists**: `(v/query? kb '(likes_cake Tom) ctx)` and the same question of
`(not (likes_cake Tom))` both answer true, and neither side is defeated, because a default
is defeasible at the edges and the KB does not guess which of two defaults to drop.

Confirm with `(v/contradictions kb)`, which lists the coexisting pairs, and
`(v/conflicts kb)` for the ones that *were* arbitrated. The fix is to say that the side you
know is true is known:

```clojure
(v/assert kb '(likes_cake Tom) 'CxSome {:strength :monotonic})
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
| `:shape` | not an s-expression at all — a string, `nil`, a map, a bare symbol — or a **vector**, which is a query's conjunction.  Refused at the read entry points as well as the write ones, carrying `:goal` or `:conjunct` ([api.md](api.md)) |
| `:not-well-formed` | a malformed connective frame, such as a bare `(implies)` — or an `or` somewhere the polycanonicalization cannot expand it away: a conclusion, a closed-query body, an `exceptWhen` query, under `not` ([canonicalization.md](canonicalization.md)) |
| `:not-range-restricted` | a rule variable in the consequent that no antecedent binds — asked per alternative of a disjunctive antecedent, and the message names the disjunct |
| `:disjunction-too-wide` | a disjunctive antecedent over the 16-alternative cap; the message names the count — [canonicalization.md](canonicalization.md) |
| `:arg-type` / `:arg-genl` | an `arg` / `genlArg` constraint convicted it — [argtypes.md](argtypes.md) |
| `:arg-variable` | a **rule** variable two argument constraints demand disjoint types of — [taxonomy.md](taxonomy.md) |
| `:disjoint` / `:functional` / `:asymmetric` | a definitional clash — [exceptions.md](exceptions.md) |
| `:unknown-option` | an option key nothing reads, or a non-map `opts` — `:mismatch` says which. A refused `VAELII_*` or `vaelii.*` switch is named under `:switch`, and under `:property`, the older key |

The one worth knowing in advance: **snake_case means arity 1.** An underscored functor
names a type, and a type is a one-place predicate, so `(lives_in ?x cold_place)` is refused
— write `livesIn`. The full roster of checks, with the regexes, is
[naming.md](naming.md).

## My batch half-landed

It no longer can, through `edit!`. A batch refused by an engine check part-way through is
rolled back at the handles it wrote: every add retracted (which collects what it derived),
every premise mark undone, every strength it raised restored, the ledgers put back. Belief
and the handle roster are what they were before the call, and the change feed is told
nothing ([feed.md](feed.md)).

Confirm it in one call — the refusal says so itself:

```clojure
(try (v/edit! kb batch)
     (catch clojure.lang.ExceptionInfo e (ex-data e)))
;; => {:type :disjoint :rolled-back true :in :add :index 2 :entry [(cat Muffet) CxThe] …}
```

**`:rolled-back true` means the KB is back at baseline.** `:in` / `:index` / `:entry` name
the line that raised it, in `check-edit`'s vocabulary, so the fix is to that entry. The
original refusal's own `ex-data` is kept — discriminate on `:type` as everywhere — and the
original exception is the cause. A throw that is not an `ex-info` carries no `:rolled-back`
key because there is no `ex-data` to add one to; the rollback ran the same.

Two things a rolled-back batch does leave behind, and neither is state: the **handle
counter**, which never reissues a number ([preview.md](preview.md) says the same of a
preview), and the `chain-stats` / `settle-stats` counters, which record work that genuinely
ran.

**The other batch entry points are not transactions.** `with-deferred-settle`, `assert-many` and
`bulk-assert-facts!` leave what was already stored in place with belief unsettled — the
documented state, and what `seed/load-sentences`' order-insensitive retry is built on.
Settle by hand, or re-run; or use `edit!` where the batch must be all-or-nothing
([api.md](api.md)).

Where it *is* a refusal `check-edit` could have predicted — a malformed entry, a `:remove`
handle naming nothing stored — nothing was applied at all: those are refused before the
batch is read. Run `(v/check-edit kb batch)` first and you will see them; what it cannot
see is an entry that only clashes once an earlier entry in the same batch has landed,
because it judges each `:add` against the KB as it stands.

## An `arg` constraint never convicts

`(arg parentOf 1 person)` plus `(disjoint dog person)` plus `(dog Muffet)` accepts
`(parentOf Muffet Bob)` without complaint. That is open-world and deliberate: the check
convicts only when the argument's own type closure reaches `thing`, and `dog` reaches it
only once something says so. Add the edge and the identical assertion throws `:arg-type`:

```clojure
(v/assert kb '(genl dog thing) 'CxUniverse)
```

So a type that appears only as a fact's functor and never as a `genl` node leaves every
constraint naming it dormant. The same precondition governs the entailment reading —
[argtypes.md](argtypes.md), whose "Where it does not mint" table is the full list of cases
where nothing is derived.

## A `functionalInArg` clash is not reported

Two things stop one, and they are different failures.

**The determinant differs.** `(functionalInArg P n)` says every argument *except* `n`
fixes the filler at `n`, so two tuples are the same slot only when they agree on all the
others. `(namesObject NsA PathA ObjOne)` and `(namesObject NsA PathB ObjTwo)` differ at
argument 2 and are two slots, not one — nothing is owed. Check the determinant before the
declaration.

**Or the mark is not on the last argument.** The assert entry point checks every shape
correctly. What is narrower is *cross-context* discovery: the pass finds a pair's far half
by reading one argument root, and its candidate gate asks only whether some mark
constrains the tuple's **final** position. A declaration whose `n` is below the arity —
`(functionalInArg P 2)` on a ternary predicate — is never asked about, so two mutually
blind contexts each holding half of such a clash are not brought together.

A mark *on* the last argument is covered, whatever the arity. At arity 1 the determinant
is empty; above arity 2 it is composite, several positions at once — neither is a single
argument root, so both reach an extent sweep bounded by
`tax/*exposure-instance-budget*` rather than a posting read, and past that bound the pass
files `:partner-sweep-truncated` rather than going quiet. Arity 2 is the one that *is* a
single root and takes the same narrow path `functional` does.

Same context, or a vantage that already sees both halves when the second arrives, is the
entry point's business and is checked.

[taxonomy.md](taxonomy.md) has the shape table; [equality.md](equality.md) has the merge
rule and the four arrival orders.

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

## `do/label` refuses to re-run

`:labeling-run-blocked` means the previous run's artifacts under this `Into` cannot be
replaced, and a run that cannot replace them must not write beside them — two groundings
in one `Into` make a `do/classify` that aggregates worlds from different solves. The
`ex-data` names the contexts, in one of two keys:

| key | what happened | fix |
|---|---|---|
| `:believed` | a labeling context, or `<Into>Class`, holds a **believed** sentex — everything a solve writes is inert, so this came from somewhere else | retract that sentex, or name a different `Into` |
| `:orphaned` | a labeling context lost its `labelingOf` ownership marker, so nothing can rediscover it while its `genlCx` edge still holds it under the base | retract the context's extent and its `(genlCx <ctx> <Base>)` edge, or name a different `Into` |

```clojure
(v/sentexes-in-context kb 'CxPlan1)                        ; what is actually in there
(v/sentexes-matching kb '(genlCx CxPlan1 CxUniverse) 'CxUniverse)   ; the placement edge
```

`:one` and `:sat` are never blocked — they persist nothing, so they have nothing to
replace. [solving.md](solving.md).

## A foreign KB will not load

This build reads its own dump format and nothing else; a corpus or a foreign dialect needs
a reader on the classpath, which ships as a separate artifact. A found KB is still
*offered* without one — the honest answer to "I cannot read this" is a load that fails
saying so — so the card appears and the load reports `this build does not read
cyc-corpus`. That message means the reader is absent, not that the KB is bad.

The route to a reader, and what each load costs, is [kbs.md](kbs.md); the extension point it plugs
into is [foreign.md](foreign.md). Two things about the development tree specifically: a
snapshot you are developing is not on Clojars, so put it on the classpath from source with
`scripts/link-checkouts.sh` or `lein install` it and name that version in an ad-hoc
dependency add. And `scripts/link-checkouts.sh` puts the sibling on **every** command's
classpath, so a foreign read that works may be the link rather than the code.

## `open-kb` refuses an unknown backend

Eleven throws share `:type :unknown-backend` — ten in `open-kb` itself and one in the
overlay's bookkeeping store, which `open-kb` reaches when mounting a fork. All eleven are
raised while building, and `open-kb` returns no KB value when it throws, so there is
nothing half-built to close.

**Three keys are on every one of them.** `:axis` says which axis the selection was read
on — `:backend`, `:records`, `:index` or `:tms`; `:kind` is what was named there; and
`:mismatch` says which kind of wrong it is, which is what decides whether a fallback is
even the right response:

| `:mismatch` | What was wrong | Also carries |
|---|---|---|
| `:unknown-name` | the axis names a kind nothing implements — the `:backend` sugar is not in the table ([storage.md](storage.md#backend-selection-two-independent-axes) lists the twelve legal names), or `:records` / `:index` / `:tms` names no implementation | |
| `:reserved-name` | a spelling refused on purpose — `:disk`, `:pg-disk`, `{:index :disk}` — because it reads as both halves out of core, which no pairing here is | `:instead`, the pairing to take |
| `:illegal-pair` | both halves are legal apart and not together: the `:disk-log` index over records it cannot be derived from, or the `:snapshot` image over anything but `:disk`, whose slot fingerprint is the stamp it is checked against | `:records` and `:index`, the pair as resolved |
| `:illegal-position` | a legal record kind somewhere it is not written for — `:pg` as a fork's **own** writable half, which keeps tombstones and released premise marks beside its records | `:half` |

`(v/open-kb {:backend :bogus})` throws `unknown KB backend :bogus — want one of […], or
the :records / :index opts`; `(v/open-kb {:records :memory :index :disk-log})` throws `the
:disk-log index needs durable records — :disk or :pg — and these are :memory …`; a bad
`:records`, `:index` or `:tms` kind names itself the same way (`unknown record backend
…`, `unknown index backend …`, `unknown TMS …`).

A `:pg` KB can still be the frozen base of a fork ([overlay.md](overlay.md)); it is only
the writable half that is refused.

**A missing adapter is not one of these.** `:sqlite` and `:pg` records live in the
**Apache-2.0 sibling adapters**, resolved lazily so the SSPL engine loads no JDBC driver
unless a KB selects one — and a legal `:backend :sqlite` or `:pg-memory` with the sibling
off the classpath is a missing *dependency*, not a name the engine does not know. It
throws `:type :missing-adapter` carrying `:records` and the `:coordinate` to add
(`com.vaelii/sqlite`, `com.vaelii/postgres`), so a caller falling back on `:memory` for an
unknown backend does not silently do it for a backend it could have had.

The `:pg` opts have their own refusals, under `:type :unknown-option` rather than
`:unknown-backend`, because the backend named is legal and what it was handed is not:
`:pg` absent or naming no database (nothing derives a server, and the index is keyed by
which database its records are in); `:pg-disk-log` with no `:dir` (the durable index is files
on *this* host, so a derived default is one two KBs over two databases would share);
`:pg` given to records that are not `:pg`. [storage.md](storage.md#postgres-records-pg-memory-pg-disk-log).

None of these reaches a daemon client: `open-kb` runs before the daemon answers its
first request, so a caller across the wire opens a KB the daemon already opened.

## The disk KB will not open

One process, one writer. A `{:backend :disk-log}` KB takes an exclusive lock on its directory,
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
once (`:id :vaelii.host.serve/open-hosts`) rather than staying silent; the startup
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

## I have a `:type` and do not know what it means

Every refusal carries a `:type` keyword in its `ex-data`, and that keyword is the
contract: the message is prose and gets reworded, the keyword is what a caller branches
on. The sections above cover the common ones in detail; this is the **whole** vocabulary,
so a keyword caught in a `catch` is never a dead end.

```clojure
(try (v/assert kb sentence 'CxSome)
     (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))
```

A refusal built as a **problem map** rather than thrown — what `check`, `check-edit` and
the browser's proposal preview answer with — carries the same keyword under the same key,
so one vocabulary reads both.

| `:type` | What happened | Where |
|---|---|---|
| `:already-loaded` | the catalog already holds a KB under this source's key — unload it first | [catalog.md](catalog.md) |
| `:anti-symmetric` | a sentence and its converse both hold of a predicate declared `anti_symmetric`, which would force an `equals` no merge can make hold | [taxonomy.md](taxonomy.md) |
| `:anti-transitive` | two steps of a predicate declared `anti_transitive` are stored, so the direct step between their ends cannot also hold | [taxonomy.md](taxonomy.md) |
| `:arg-constraint-kind` | `genlArg` on a predicate declared `instance_relation_predicate`, or `arg` on a `type_relation_predicate` | [argtypes.md](argtypes.md) |
| `:arg-genl` | a `genlArg` constraint convicted the sentence — see [An `arg` constraint never convicts](#an-arg-constraint-never-convicts) | [argtypes.md](argtypes.md) |
| `:arg-position` | an argument constraint names a position the predicate's declared arity does not have | [argtypes.md](argtypes.md) |
| `:arg-type` | an `arg` constraint convicted the sentence — see [`assert` refused it](#assert-refused-it) | [argtypes.md](argtypes.md) |
| `:arg-variable` | two argument constraints demand disjoint types of one rule variable | [taxonomy.md](taxonomy.md) |
| `:arity` | the functor is used at an arity its declaration does not admit | [naming.md](naming.md) |
| `:asymmetric` | a definitional clash with a predicate declared `asymmetric` | [exceptions.md](exceptions.md) |
| `:bad-algebra` | a two-axis projection table does not cover all nine `[x y]` pairs exactly once | [space.md](space.md) |
| `:bad-arg` | a `foreign/register` argument is the wrong kind of thing — the kind must be a keyword, the reader a namespace-qualified symbol | [foreign.md](foreign.md) |
| `:bad-args` | an operation was given the wrong number of arguments — an op over the wire, or a CLI command; `:op` names it either way | [operations.md](operations.md) |
| `:bad-batch` | a bulk `:batch` size that is not a positive number of records | [storage.md](storage.md) |
| `:bad-cursor` | a feed cursor that is not a whole number, or is ahead of what the subscription has delivered | [feed.md](feed.md) |
| `:bad-foreign-manifest` | a plugin's manifest is not EDN, is not a map, or holds an entry that is not `:kind ns/reader` | [foreign.md](foreign.md) |
| `:bad-handle` | a handle argument that is not one handle — a collection where one was wanted, or a value that is no handle at all | [api.md](api.md) |
| `:bad-host` | the daemon's `Host` allowlist does not recognize the header the request carried | [operations.md](operations.md) |
| `:bad-level` | a `lookup` level or an `escalate` floor outside the stack's range | [levels.md](levels.md) |
| `:bad-pattern` | a `matchesPattern` pattern argument the regex engine cannot compile, refused at the assert entry point rather than left to fail silently at query time | [defns.md](defns.md) |
| `:bad-registrant` | a durability registrant's key, value or `:phase` is not one the close sequence reads | [storage.md](storage.md) |
| `:bad-reply` | the daemon's reply does not read as EDN, or is not a map | [operations.md](operations.md) |
| `:bad-snapshot` | an index snapshot file's magic number is not this engine's — the index rebuilds from the records, which are untouched | [storage.md](storage.md) |
| `:bad-table-entry` | a roster and the arms that answer to it do not agree, refused at namespace load: a declaration with a partial cache triple or no arm at all, arms that disagree with what `vaelii.impl.predicates` declares about the functor, a mark family whose spellings disagree about what they sweep, a sweep naming a reach `settle` has no arm for, a switch reader with no row, a backend axis nothing opens, a quality reading nothing renders. `:mismatch` says which. Unlike the other discriminants here, this vocabulary is read by whoever is looking at a failed build rather than branched on by a caller, so the message is the remedy and the words are pinned in `type_contract_test` rather than listed in this row | [predicates.md](predicates.md) |
| `:base-is-overlay` | a fork's own half and its base name one store, so the fork would write its own base | [overlay.md](overlay.md) |
| `:body-too-large` | a request body over `VAELII_MAX_BODY_BYTES` | [operations.md](operations.md) |
| `:budget-exhausted` | a bounded `ask` / `ask?` / `prove` / `provable?` hit its `:max-ms` before the search ran dry, so what it held was a prefix rather than an answer | [anytime.md](anytime.md) |
| `:choice-head-not-positive` | an `assumptionRule` head is negated, and a choice head must be a positive literal | [solving.md](solving.md) |
| `:compaction-failed` | a record or index log compaction failed after its commit point — the store refuses writes until it is reopened | [storage.md](storage.md) |
| `:context-escape` | a proposed sentence is an `ist`, so it would file itself somewhere other than the context the caller named | [llm.md](llm.md) |
| `:cross-origin` | the daemon refused a request whose `Origin` names another site | [operations.md](operations.md) |
| `:daemon-error` | the daemon refused and its reply carried no `:type` of its own — the client's fallback | [operations.md](operations.md) |
| `:damaged-dictionary` | a tokenized frame cites a token id the dictionary has no entry for | [storage.md](storage.md) |
| `:disjoint` | a definitional clash between two disjoint types — see [`assert` refused it](#assert-refused-it) | [exceptions.md](exceptions.md) |
| `:disjunction-too-wide` | a disjunctive antecedent over the alternative cap | [canonicalization.md](canonicalization.md) |
| `:disk-locked` | another JVM holds the directory's single-writer lock — see [The disk KB will not open](#the-disk-kb-will-not-open) | [storage.md](storage.md) |
| `:duplicate-handle` | a dump names one handle twice, and a handle-preserving import gives each record the id the dump names | [storage.md](storage.md) |
| `:duplicate-tokens` | the durable token dictionary holds a token twice, so its ids have shifted; the index rebuilds from the records | [storage.md](storage.md) |
| `:error` | a check reached something it could not classify, and reports the throwable's own message | [api.md](api.md) |
| `:exception-not-closed` | an `exceptWhen` reads a variable no antecedent binds, or the anonymous wildcard `_`, which binds nothing | [exceptions.md](exceptions.md) |
| `:export-busy` | an export is already running, and one runs at a time | [catalog.md](catalog.md) |
| `:frozen-base` | a write reached the overlay's base, which is mounted read-only | [overlay.md](overlay.md) |
| `:functional` | a second value for a predicate declared `functional`, or for the position a `functionalInArg` declaration names — see [`assert` refused it](#assert-refused-it) | [equality.md](equality.md) |
| `:handle-ceiling` | a handle past the dense TMS's int-keyed ceiling | [density.md](density.md) |
| `:argument-family-ceiling` | more distinct `(predicate, position)` pairs than the packed root key's 24-bit scope field holds; take `:index :memory` | [indexing.md](indexing.md) |
| `:incomplete-racer` | a portfolio was handed a strategy with `:first-result?` on, which stops the search rather than steering it | [inference.md](inference.md) |
| `:inter-arg-type` | an `interArg` constraint convicted one argument because of what another one is | [argtypes.md](argtypes.md) |
| `:internal-error` | the daemon caught a throwable carrying no `:type` of its own | [operations.md](operations.md) |
| `:irreflexive` | a predicate declared `irreflexive` holds of a thing and itself | [taxonomy.md](taxonomy.md) |
| `:job-busy` | a job holding this process's one writer is already running | [operations.md](operations.md) |
| `:labeling-inconsistent` | a labeling disagrees with the brave/cautious classification of the same program | [labeling.md](labeling.md) |
| `:labeling-run-blocked` | a previous run's artifacts cannot be replaced — see [`do/label` refuses to re-run](#dolabel-refuses-to-re-run) | [solving.md](solving.md) |
| `:llm-api-error` | a provider answered an error status, or put an error in a 200 body or a stream chunk | [llm.md](llm.md) |
| `:llm-bad-credential` | a credential holds a character an HTTP header cannot carry; the value is never quoted back | [llm.md](llm.md) |
| `:llm-bad-response` | a provider answered with a body that is not JSON | [llm.md](llm.md) |
| `:llm-encode` | a content block whose `:type` the request encoder does not write | [llm.md](llm.md) |
| `:llm-no-credential` | no provider credential is set | [llm.md](llm.md) |
| `:llm-not-applicable` | a proposal was asked to apply at a status that does not admit it; `{:force? true}` overrides | [llm.md](llm.md) |
| `:llm-timeout` | a provider stopped answering inside the turn's `:timeout-ms` budget | [llm.md](llm.md) |
| `:malformed-entry` | an index entry stream holds something that is not a `[key value]` pair | [storage.md](storage.md) |
| `:malformed-manifest` | a `meta.edn` / `format.edn` / `catalog.edn` the EDN reader cannot parse — cut mid-form, or never EDN | [storage.md](storage.md) |
| `:malformed-record` | a tokenized record body holds a code this codec does not write | [storage.md](storage.md) |
| `:manifest-too-large` | a manifest file longer than the bound the reader allows; a manifest is a handful of keys | [storage.md](storage.md) |
| `:missing-adapter` | a **legal** `:sqlite` or `:pg` records axis whose Apache-2.0 sibling is not on the classpath — `:coordinate` names the dependency to add, and the backend is not the thing to change | [storage.md](storage.md) |
| `:missing-resource` | a KB file, ontology layer or text KB is not where it was looked for | [kbs.md](kbs.md) |
| `:naf-justification` | a dump names a justification with a non-empty `:out`, and a justification here has no out-list | [naf.md](naf.md) |
| `:naf-not-closed` | an `unknown` antecedent or an aggregate census reads a variable nothing else in the rule binds | [naf.md](naf.md) |
| `:naming` | a symbol's spelling does not match its role — see [`assert` refused it](#assert-refused-it) | [naming.md](naming.md) |
| `:nippy-version-moved` | the nippy on the classpath is not the release the class-name check was written against; re-read its three attachment points, then move `thaw/pinned-nippy-version` | [defenses.md](defenses.md) |
| `:nippy-version-unreadable` | nippy's own Maven descriptor could not be read, so the class-name check cannot say which release it is guarding | [defenses.md](defenses.md) |
| `:no-base` | an `:overlay` backend was opened with neither `:base` nor `:base-stores` | [overlay.md](overlay.md) |
| `:no-depth-bound` | the node engine was asked a goal with no `:max-depth` and no `*max-depth*` binding | [inference.md](inference.md) |
| `:no-destination` | an export was asked for with a blank destination directory | [catalog.md](catalog.md) |
| `:no-dump` | the directory holds no `meta.edn`, so it is not a dump | [storage.md](storage.md) |
| `:no-foreign-reader` | this build reads no such format — see [A foreign KB will not load](#a-foreign-kb-will-not-load) | [foreign.md](foreign.md) |
| `:not-a-directory` | an export destination names a file | [storage.md](storage.md) |
| `:not-a-report` | a value handed to the quality renderer is not the map `kb-quality` answers | [quality.md](quality.md) |
| `:not-assertible` | a `do/` imperative inside a rule, an imperative this build does not carry, or one written with the wrong arguments | [labeling.md](labeling.md) |
| `:not-checkable` | `check` was handed a `do/` imperative, which stores nothing and so has nothing to check | [api.md](api.md) |
| `:not-defeasible` | known-true content reached the edge solver, which arbitrates `:default` content only | [solving.md](solving.md) |
| `:not-edn` | a request body does not read as EDN | [operations.md](operations.md) |
| `:not-empty` | an export or import destination already holds content, and each wants a place of its own | [storage.md](storage.md) |
| `:not-encodable` | a value in a sentence does not round-trip through the durable log | [storage.md](storage.md) |
| `:not-found` | the daemon has no route for the path | [operations.md](operations.md) |
| `:not-ground` | a fact with a variable in it, or an `abduce` with a variable context — see [`assert` refused it](#assert-refused-it) | [nmtms.md](nmtms.md) |
| `:not-in-process` | the KB is served by a daemon, so its dump is written on that daemon's own host | [catalog.md](catalog.md) |
| `:not-indexable` | a rule nothing could index or reach — a variable functor, or a rule asked to be stored inert | [indexing.md](indexing.md) |
| `:not-range-restricted` | a consequent variable no antecedent binds | [nmtms.md](nmtms.md) |
| `:not-stratified` | the rule set would close a cycle through negation | [naf.md](naf.md) |
| `:not-watchable` | a `watch` that could never deliver — no listener, a goal nothing unifies with, or an unscoped goal | [feed.md](feed.md) |
| `:not-well-formed` | a malformed connective frame, or an `or` somewhere polycanonicalization cannot expand it away | [canonicalization.md](canonicalization.md) |
| `:pattern-too-costly` | a `find-terms` regex read past its per-term or scan-wide character budget | [api.md](api.md) |
| `:quantifier-not-local` | a bound existential or universal variable appears outside its own quantifier | [aggregate.md](aggregate.md) |
| `:quoted-arg-type` | a `quotedArg` constraint convicted the argument on its EDN kind as a term | [argtypes.md](argtypes.md) |
| `:report-only` | the proposal preview's row for a line the corrector would rewrite rather than store | [web.md](web.md) |
| `:reserved-family` | a packed index key names the reserved family, which nothing packs | [indexing.md](indexing.md) |
| `:reset` | the sandbox page's row saying how much a reset discarded | [web.md](web.md) |
| `:shape` | not an s-expression at all — see [`assert` refused it](#assert-refused-it) | [api.md](api.md) |
| `:short-transfer` | a file copy stalled before the byte count it was told to move | [storage.md](storage.md) |
| `:solver-failed` | the ASP backend ran and produced no usable answer | [asp.md](asp.md) |
| `:solver-unavailable` | the ASP backend is not on this machine — no `clasp` binary, no `libclingo` | [asp.md](asp.md) |
| `:stacked-batch` | a bulk load's in-memory index state moved under it, so installing the batch would discard what moved | [storage.md](storage.md) |
| `:stacked-fork` | a fork's base is itself a fork, and stacks are refused rather than half-supported | [overlay.md](overlay.md) |
| `:stale-index-layout` | a durable index was written under another key layout, and a fork mounts its base read-only | [indexing.md](indexing.md) |
| `:stale-index-records` | a durable index was built against other records, and an index cannot answer another store's reads | [indexing.md](indexing.md) |
| `:still-exporting` | an unload was asked for while an export of that KB is running | [catalog.md](catalog.md) |
| `:still-loading` | an export was asked for while the KB is still being written | [catalog.md](catalog.md) |
| `:still-stopping` | an unload was asked for while the loader has not reached an interruptible point | [catalog.md](catalog.md) |
| `:too-many-subscriptions` | the daemon already holds its maximum of feed subscriptions | [feed.md](feed.md) |
| `:too-many-waiters` | the daemon already has its maximum of long polls parked | [feed.md](feed.md) |
| `:torn-snapshot` | a durable index part reloaded at a size its own metadata contradicts | [storage.md](storage.md) |
| `:truncated-dump` | a dump stream ended early, or holds a chunk length this framing does not write | [storage.md](storage.md) |
| `:unauthorized` | the token presented is not the one the daemon holds — see [Every call to the daemon is refused](#every-call-to-the-daemon-is-refused) | [operations.md](operations.md) |
| `:unbound-deferred` | a computed antecedent reached the join with an input no earlier antecedent bound | [generators.md](generators.md) |
| `:unforkable-index` | a `:columnar` index cannot be forked, since its trie is not written over a KV backend | [overlay.md](overlay.md) |
| `:unknown-backend` | a backend selection the storage layer refuses; `:axis` says which axis, `:kind` what was named, `:mismatch` which kind of wrong (`:unknown-name`, `:reserved-name`, `:illegal-pair`, `:illegal-position`) — see [`open-kb` refuses an unknown backend](#open-kb-refuses-an-unknown-backend) | [storage.md](storage.md) |
| `:unknown-command` | the CLI was given a word that is not one of its commands | [api.md](api.md) |
| `:unknown-entry` | an operation named a loaded KB the catalog does not hold | [catalog.md](catalog.md) |
| `:unknown-frame` | a record frame tag or an index write op this build does not read | [storage.md](storage.md) |
| `:unknown-framing` | a dump's `:framing` is not one this build reads | [storage.md](storage.md) |
| `:unknown-handle` | no sentex is stored under the handle | [api.md](api.md) |
| `:unknown-op` | the daemon has no op by that name | [operations.md](operations.md) |
| `:unknown-option` | an option an entry point will not take, `:mismatch` saying how: `:unknown-key`, `:bad-value`, `:missing-value`, `:not-a-map`, `:missing-companion` or `:conflict` | [api.md](api.md) |
| `:unknown-source` | the catalog has no KB source by that id, the source names a kind nothing loads, or the directory `lein cli upgrade` names holds no store | [catalog.md](catalog.md) |
| `:unknown-subscription` | the feed token names no subscription — it was dropped, timed out, or belongs to another daemon | [feed.md](feed.md) |
| `:unknown-tactician` | a strategy names a tactician the ordering table does not hold | [inference.md](inference.md) |
| `:unminted-nat` | `assert-inert` was handed a reifiable NAT this KB never minted; it never mints, so assert the NAT-bearing fact first | [nat.md](nat.md) |
| `:unparseable` | a model's answer does not read as EDN | [llm.md](llm.md) |
| `:unreadable` | a line of a proposal or an edit batch does not read as EDN | [web.md](web.md) |
| `:unreadable-store` | the records in that store do not thaw as sentexes — it was written by a build whose record classes differ | [storage.md](storage.md) |
| `:unrecovered-kb` | the KB is open over a store whose belief was never built, so writes are refused until `recover` runs; with `:hazards [:stale-belief]`, a `:recover? :background` open is rebuilding belief behind an earlier build's image, and writes resume when the rebuild finishes | [storage.md](storage.md) |
| `:unrecovered-premise` | a retract named a premise this KB never recovered, so the dedup walk that would find its twin has not run | [storage.md](storage.md) |
| `:unreleased` | an unload's release did not finish cleanly; the entry is still listed and unloading again retries it | [catalog.md](catalog.md) |
| `:unsupported-compression` | a compression this build does not write, does not read, or whose codec is off the classpath | [storage.md](storage.md) |
| `:unsupported-context` | a query context reached a read that does not resolve one, and would answer as though the KB were empty | [contexts.md](contexts.md) |
| `:unsupported-format` | a durable store's format version is not one this engine reads | [storage.md](storage.md) |
| `:unsupported-platform` | the mapped index image is asked for on a platform that cannot publish it by rename | [storage.md](storage.md) |
| `:unsupported-variant` | a dump variant this build does not write or read | [storage.md](storage.md) |
| `:unsupported-version` | a dump's format version is not one this build reads | [storage.md](storage.md) |

**koinii's refusals are namespaced**, because the app carries a vocabulary of its own
rather than adding to the engine's flat one ([koinii.md](koinii.md)).

| `:type` | What happened |
|---|---|
| `:arbiter-is-party` | the arbiter holds a side of the dispute it was asked to rule, so a ruling would restamp or retract its own claim |
| `:koinii/admin-off-registry` | an admin principal aimed a write at a context other than the registry it governs |
| `:koinii/catchup-thrashing` | catch-up spent its snapshot budget — the subscription is reaped, or the consumer cannot keep up |
| `:koinii/compression-pinned` | `publish!` pins `:compression :none`, since a published commit's streams are a byte-stable function of the KB |
| `:koinii/creator-mismatch` | an agent handle was asked to assert under another agent's `:creator` |
| `:koinii/feed-error` | a catch-up poll failed and said nothing about why — an untyped transport failure, reported rather than read as an empty batch |
| `:koinii/foreign-context` | an agent aimed a write at a context that is not its own |
| `:koinii/identity-unverified` | a `:proof-tier` claim has no verify-fn bound, or did not pass the one that is |
| `:koinii/missing-seed` | koinii's seed KB file for a context is not on the classpath |
| `:koinii/no-cursor` | a catch-up poll answered something that is not a resumable cursor |
| `:koinii/no-such-handle` | a handle names no record on this medium |
| `:koinii/no-such-stance` | a ballot stance other than `:for` or `:against` |
| `:koinii/no-wire-feed` | an in-process medium has no cursor feed; catch-up is a wire-only concern |
| `:koinii/not-a-channel` | an agent cannot join under that parent, since a channel is a context agents are lifted into |
| `:koinii/not-own-statement` | an agent may disregard only its own statement |
| `:koinii/registry-forbidden` | the governed may not write the authority that governs them |
| `:koinii/registry-not-functional` | a registry read matched more than one row, where the vocabulary declares one |
| `:koinii/reply-inadmissible` | a multi-claim reply's batch did not pass `check-edit`, and a batch lands whole or not at all |
| `:koinii/speaker-mismatch` | a speech act names a speaker other than the handle that asserted it |
| `:koinii/uncanonical-value` | a value in a sentence has no canonical byte encoding, so it has no sentence identity |
| `:koinii/unknown-policy` | an identity policy other than `:cooperative` or `:proof-tier` |
