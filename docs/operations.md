# Operational surface

- **Covers:** the five surfaces that drive a KB — CLI, daemon, client, access facade
  and the browser's launch path — the single-writer contract across them, and every
  environment variable or system property with where it is read.
- **Not here:** the browser's own pages, panels and editing UI → [web.md](web.md); which
  KB a process has loaded, and how one is found → [catalog.md](catalog.md).
- **Assumes:** sentex, context, handle → [glossary.md](glossary.md).

`vaelii.core` is the engine; the operational surface is the set of in-repo surfaces
that *drive* it. There are five:

| Interface | Namespace | Launch | For |
|-----------|-----------|--------|-----|
| Browser | `vaelii.web` | `lein run -m vaelii.web` | reading a KB in a browser |
| CLI | `vaelii.cli` | `lein cli <cmd> …` | driving a KB from a shell |
| Daemon | `vaelii.serve` | `lein serve [port [dir]]` | one process owns a KB, serves it over HTTP |
| Client | `vaelii.client` | *(library)* | talking to a daemon from Clojure |
| Access | `vaelii.browser.access` | *(library)* | a read that resolves to a local KB or a remote daemon |

All five go through `vaelii.core` alone — the same boundary the rest of the repo keeps
([api.md](api.md)). None of them is a separate repo: the
engine does its own storage (the `:disk` backend), so a surface is an in-repo
namespace, not a sibling.

## The single-writer contract

The store allows **one writer per directory** (docs/storage.md); the `:disk` backend
enforces it with a fail-fast file lock. That shapes how the surfaces coexist:

- The **daemon** is the canonical single writer — one JVM owns one KB and every client
  reaches it through that one process. The daemon serializes its ops through one
  monitor, so concurrent client writes apply one at a time.
- The **CLI** with `--dir` takes the same lock, so it and a daemon **cannot own one
  directory at once**. Point them at different directories, or let the daemon own the
  writable KB and give the CLI its own.
- An in-memory KB (no `--dir`) has no lock and no persistence — fine for a REPL session
  or a one-shot check, useless for one-shot commands that expect earlier facts.

## CLI — `vaelii.cli`

```sh
lein cli assert  '(dog Muffet)' CxNaturalWorld --dir /var/lib/vaelii
lein cli match   '(dog ?x)'   CxNaturalWorld --dir /var/lib/vaelii   # => [(dog Muffet)]
lein cli why     3                                --dir /var/lib/vaelii
lein cli export  /var/backups/vaelii-2026-07     --dir /var/lib/vaelii     # back it up
lein cli repl --starter                                                    # interactive
```

- **Commands:** `assert`, `assert-rule`, `match` (`sentexes-matching`, sentences only),
  `query`, `query?`, `ask`, `prove`, `provable?`, `retract`, `why`, `why-not`, `in`,
  `isa`, `types-of`, `describe`, `handle-of`, `types`, `contexts`, `conflicts`,
  `contradictions`, `quality`, `load`, `export`, `diff`, `upgrade`, `repl`. `--depth n` is how the line says how far to expand rules,
  and `query` without one expands none. A sentence is
  written as an EDN string (`'(dog Muffet)'`), a context as a symbol, a handle as an
  integer, and a path as itself — an argument that reads as no EDN form is kept as the
  string it already was, which is what `/var/lib/vaelii` is.
- **A command that answers a set prints it sorted.** `match`, `query` and `ask` answer
  sets, and a set has no order of its own — so an unsorted print was whichever order the
  retrieval enumerated, and two loads of the same knowledge printed it differently, which
  a `diff` of two runs is indistinguishable from a change in the KB. They are ordered by content key
  (`naming/print-key`), alongside `types` and `contexts`, which always were. **`prove` is
  the exception and stays in DFS order**: it answers one solution per derivation, and the
  order those were found in is part of what a proof says ([inference.md](inference.md)).
- **`load <path>`** reads a **text KB** — a `Cx<Name>.txt` file, or a directory of them —
  and asserts every form. The file name is the context, so the command takes no context
  argument, and a whole directory is one order-insensitive pass ([api.md](api.md)). It is
  the inverse of `export --format text`, and the format the shipped ontology under
  `resources/kb/` is authored in.
- **`upgrade --dir <path>`** brings an existing store up to the running engine. It opens
  the store under the backend its files were written by, installs its reasoning image or,
  when the image was written under another image layout, other engine source or other
  policies, recovers belief from the records and writes a new image; closing the store
  then writes the index image a rebuilt index leaves due. It prints whether the image was
  `:current`, `:rebuilt` or `:written`, and refuses a directory holding no store
  (`:unknown-source`). The records are read and never rewritten.
  `scripts/upgrade-kb.sh [KB-DIR...]` runs it once per directory, defaulting to
  `checkouts/kb`, with the heap from `VAELII_HEAP`. Run it after pulling engine
  changes, so the next open installs belief in about a minute rather than recovering it.
  **`--verify`** moves the image to
  `reasoning.prev/`, recovers and writes a new image, and reports whether the two agree:
  `:labels` compares the believed sets, and `:network` and `:state` compare the files byte
  for byte. The script passes the flag to every directory.
- **`describe <term>`** prints everything the KB holds about one term, shaped by the
  term's role ([api.md](api.md)) — the shell spelling of "what can I ask about this?".
  **`--context <CxName>`** is the vantage: the argument declarations, the grants and the
  comments are each read from that context's `genlCx` ancestor set, so two vantages give two
  correct answers; absent, it reads every context.
- **`why-not '<goal>' <CxName> --nearest <n>`** adds the rules that came closest to
  concluding the goal, each with the antecedent it is still missing. A flag rather than
  the default because it runs a bounded backward search, which the plain command does
  not ([api.md](api.md)). The command takes a goal *or* a handle — one integer operand
  is a handle, as `why`'s is — and the flag belongs to the goal: a stored handle is
  stored, so `:not-stored` is not an answer it can get, and the pairing is **refused**
  rather than dropped.
- **`diff <a> <b>`** is the one command that reads two KBs and neither of them is the one
  the run opened: both arguments are **text KBs on disk**, each read into an in-RAM KB of
  its own, and what it prints is `{:added :removed :moved :belief-changed}`. Keyed on
  content, so two exports of one KB taken at different handles diff empty and a `diff` of
  the output means something. Pair it with `export --format text` to see what a day of
  editing did.
- **`quality`** prints the report on the *knowledge* — unfired rules, extent skew, chain
  depth and taxonomy coverage among its seven readings — as Markdown rather than as data,
  because seven distributions pretty-printed are not a reading anybody takes
  ([quality.md](quality.md)).
- **`export <dir>`** writes the KB out as a portable dump (`vaelii.core/export!`) and
  prints the writer's summary. `--variant
  records|records+index`, `--compression gzip|xz|none`. **`--format text`** writes a text
  KB instead (`vaelii.core/export-text!`) — the premises, one `Cx<Name>.txt` per context,
  which `load` reads back; `--variant` and `--compression` describe a dump and are refused
  beside it rather than dropped, since a compression flag accepted and ignored reads from
  the outside exactly like one that was applied. The destination must be empty or
  absent; a refusal is printed as `error: …` **on stderr** in the engine's own words,
  with a non-zero exit status — the same message the daemon and the browser report,
  because none of them writes one of its own, and on the stream that leaves stdout's
  data parseable when a script redirects it.
- **Options:** `--dir <path>` selects the durable backend (recovered on open, so it
  persists across invocations); `--memory` says the ephemeral default out loud — and
  contradicts `--dir`, so naming both is refused; `--starter` loads the shipped schema
  so you can explore the ontology; `--strength monotonic` marks an `assert` or
  `assert-rule` known-true — for a rule that is the rule's own defeat class, not the
  class its firings confer (a bare rule already concludes at its weakest antecedent).
  A flag outside the roster, one missing its value, or one whose "value"
  is the next flag (`--dir --starter` names no directory) is one line on stderr and
  exit 1. The REPL loop is the one place errors stay on stdout: it is a conversation,
  and its errors belong in the transcript beside the line that caused them.
- **A flag belongs to the commands that read it**, and one carried by a command that
  does not is refused the same way rather than dropped — an ignored option reads from
  outside exactly like an honoured one. The first three above name the KB and go
  anywhere; `--strength` is `assert` and `assert-rule`'s, `--depth` is `query` and
  `query?`'s, `--variant`, `--compression` and `--format` are `export`'s, `--context` is
  `describe`'s, `--nearest` is `why-not`'s, and `repl` carries all of
  them because its options are fixed at session start and each line reuses them. `help`
  prints the owner beside each flag, and the refusal names what the command does read.
- **`repl`** holds the KB in-process, so a memory KB accumulates for the session. Each
  line is `<cmd> <edn-forms…>`.

`dispatch` takes args already parsed to data, so the shell (which `edn`-reads each argv
string) and the REPL (which reads forms off the line) share one command table.

## Daemon — `vaelii.serve`

```sh
lein serve 4200 /var/lib/vaelii                             # disk-backed; omit the dir for in-memory
lein serve 4200 --starter                                   # in memory, with the starter schema
VAELII_API_TOKEN=… lein serve 4200 /var/lib/vaelii --listen 0.0.0.0   # off-machine (opt-in)
```

- **`--starter` loads the shipped starter schema** (`vaelii.host.starter/load-into`) into
  the KB after it opens and before the port is bound, so `GET /health` answers only once
  the schema is in. The flag takes no value and sits anywhere among the arguments. Over a
  directory that already holds the schema, every starter sentence dedups to its stored
  handle, and the load still reads every starter file.

- **It binds loopback**, and exposing it is an explicit choice. `POST /op` is the write
  route of the *single writer*, so the default answers only the machine it runs on — the
  same rule the browser holds to ([web.md](web.md)), and the more consequential of the
  two, since the browser edits a KB where this one *is* the KB's only writer. Jetty binds
  every interface when no host is given, so this is a host the daemon passes rather than
  one it omits.

  **The rule is one rule and both servers hold it**: `--listen` naming a non-loopback
  address requires `VAELII_API_TOKEN`, and without one the server prints a line and
  exits **2** before it opens a KB. `lein run -m vaelii.web --listen 0.0.0.0` is refused
  on the same terms and, with the token set, answers **401** to a request that does not
  carry it — the browser's write routes include two (`/kbs/export`, `/kbs/load`) that
  write the host filesystem at a path the request names. A **loopback** bind is
  unchanged on both: the token is used by the daemon when set, the browser never asks
  for it, and its absence is a startup warning naming the flag that would require one.
  [why a refusal rather than a warning](defenses.md#what-a-server-binds-decides-what-it-requires)
- **One shared bearer token authenticates the caller.** With `VAELII_API_TOKEN` set,
  every request carries `Authorization: Bearer <token>` or is answered **401** with a
  `WWW-Authenticate: Bearer` challenge and `{:ok false :type :unauthorized}`. The
  comparison is constant-time (`MessageDigest/isEqual` over UTF-8 bytes), and a missing
  header, a wrong token and a malformed `Authorization` line answer *identically* — a
  refusal that said which is an oracle a caller walks a byte at a time. One token for
  the process, not a session and not an identity: per-caller identity is a reverse
  proxy's job, and this is the check below it. The wrapper sits outside the `Host`
  allowlist and the origin check, so an anonymous caller is answered before the daemon
  forms any other opinion about the request.
- **`GET /health` answers without the token**, and it is the only route that does. A
  daemon only its token-holder can probe is one no container orchestrator, load balancer
  or shell script can watch, and `{:ok true}` tells a caller nothing it did not learn by
  connecting.
- **What it binds decides what it requires.** `--listen` naming a **non-loopback**
  address requires `VAELII_API_TOKEN`: without one the daemon prints a line and exits
  **2**, before it opens the KB and takes the directory's writer lock. It is the flag
  that publishes `POST /op` *and* the flag that drops the `Host` allowlist, so the
  exposed configuration must not also be the one with the fewest checks. On **loopback**
  — the default, and `--listen 127.0.0.1` said out loud — the token is used when set and
  its absence is a startup warning naming the flag that would require one; an open
  loopback daemon is drivable by every process on the machine. Either way the daemon
  logs which posture it started in, since that is the line to grep for after an incident.
  Put a reverse proxy in front for TLS and rate limiting; the wire is plaintext.
- **Wire format is EDN.** A sentence is a symbol s-expression — `(dog Muffet)`, `?x` —
  which EDN round-trips losslessly; JSON would mangle the symbols. Bodies are read with
  `clojure.edn/read-string`, which has no reader-eval, so an untrusted body cannot run
  code.
- **The protocol is one endpoint.** `POST /op` with `{:op <keyword> :args [...]}` returns
  `{:ok true :result …}` or `{:ok false :error "…" :type <keyword>}`. `GET /health`
  returns `{:ok true}`. The op is looked up in an **allowlist** (`serve/ops`) of
  `vaelii.core` fns — the KB is supplied by the daemon, so the client sends only the op
  and the remaining args, and no client can reach an arbitrary var. Four ops are not in
  that table and are looked up in a second one (`serve/feed-ops`, below);
  `serve/op-names` is the two together, which is the roster an `:unknown-op` refusal
  hands back.
- **`POST /op` requires `Content-Type: application/edn`** — parameters and case are
  tolerated (`application/edn;charset=utf-8` passes), anything else is refused with 415
  in the same `{:ok false :error … :type …}` shape every refusal carries. The
  requirement is a CSRF guard rather than a parsing one: the type is not CORS-simple,
  so a browser must preflight it, and the daemon answers no CORS headers — which stops
  a page the operator merely visits from driving the write route over loopback. A
  request stamping another site's `Origin` (or `Referer`) is refused with 403, the
  second layer on the same entry point.
- **Every route answers only a recognised `Host`** — the allowlist follows the
  interface the daemon is bound to, so the loopback default answers only loopback
  names, which is what closes DNS rebinding; an unrecognised `Host` gets 400.
  `VAELII_ALLOWED_HOSTS` (comma-separated) overrides the list — a reverse proxy
  preserving the original `Host`, or a local alias name, needs it. A request with
  **no** `Host` header passes: every browser sends one, so its absence marks a
  non-browser client with no ambient browser context to ride. Binding to an address
  with `--listen` drops the allowlist (the name you reach it by is then yours to
  know); set `VAELII_ALLOWED_HOSTS` to keep the check. Left unset, the daemon starts
  anyway rather than refusing — a reverse proxy setting its own `Host` needs exactly
  this, and an operator cannot always enumerate what that will be — but it is not
  silent about it: a public bind with no allowlist warns once at startup
  (`:id :vaelii.host.serve/open-hosts`), and the `vaelii daemon listening` line's
  `:hosts` — `:allowlisted` or `:open` — is the one to grep for afterwards, beside
  `:auth`.
- **A body over 16 MiB is refused** with 413 before it reaches the heap. An op body is a
  sentence and its context, so the ceiling is nowhere near a legitimate call — it is
  there so a caller who reaches the port cannot spend the daemon's heap by streaming one.
  The cap and its `VAELII_MAX_BODY_BYTES` override are `vaelii.host.guard`'s
  (`max-body-bytes`, `wrap-body-limit`), not this namespace's, because the browser has
  the same exposure through a form body and reads the same number — one ceiling, two
  servers ([web.md](web.md)).
- **A search bound may be lowered by a request and not raised.** The two dials a caller
  sizes a served read with are `:max-depth` and `:max-ms`, and each is held under a
  ceiling — `VAELII_MAX_QUERY_DEPTH` (**256**) and `VAELII_MAX_QUERY_MS` (**30000**).
  Under it answers; over it is refused **400** with `{:type :over-ceiling}` carrying the
  requested figure and the ceiling, so the next request knows what to name. A read that
  names *no* `:max-ms` is given the ceiling's, because absent there means no clock at all
  — and for the four backward-search entry points that holds even when the request sent no
  option map, since the alternative is an unbounded search on the write monitor. `0` on
  either variable lifts that ceiling. The ops it applies to are the ones with a bound to
  raise — `:query`, `:query?`, `:argue`, `:why`, `:why-not`, `:search-tree`,
  `:compare-tacticians`, `:ask`, `:ask?`, `:prove`, `:provable?`, `:ask-within`,
  `:prove-within`. A search that reaches its clock is **400** `{:type
  :budget-exhausted}` at the four plain entry points, which answer with a solution set or a
  boolean and have no room to say the answer is a prefix; `:ask-within` and
  `:prove-within` return the prefix with a `:status` instead
  ([anytime.md](anytime.md)). **30 seconds is the client's own read timeout**
  (`vaelii.client`, below): every op runs under the single write monitor, so a read still
  running past the point the caller stopped listening is holding every other request
  behind an answer nobody will receive. The ceiling is applied in the op table rather
  than at this route, so the model's generated tool surface is held to it too
  ([llm.md](llm.md)).
  [why a refusal and not a clamp](defenses.md#a-search-bound-may-be-lowered-by-a-request-and-not-raised)
- **A read is realized under the write monitor.** Projecting the answer for the wire is
  what realizes a lazy result, so it runs *inside* the lock the daemon serializes ops
  with. [why inside the lock](defenses.md#a-read-that-crosses-the-wire-is-realized-inside-the-write-monitor)
- **The change feed crosses the wire as a subscription with a cursor** (`:watch`,
  `:poll`, `:unwatch`, `:watchers` — [feed.md](feed.md), "Across the wire"). These are
  the one thing on the wire that is *not* a `vaelii.core` fn with the KB supplied, which
  is why they are a table of their own: `core/watch` takes a callback, and a callback
  does not cross an EDN wire any more than `:export`'s `:on-progress` does. What crosses
  instead is state the daemon holds — one bounded ring per subscription, read forward
  with an integer. `:poll` takes `{:wait-ms n}` to park until the first event arrives,
  which buys the latency without a second wire format or a second thing to authenticate;
  the wait runs **outside** the write monitor, so a parked poll never blocks a writer.
  A subscription is heap a caller can allocate, so it is bounded three ways — 64 per
  daemon, 256 events on each ring, and one nobody has polled in five minutes is reaped —
  and every drop is reported as `:lagged` rather than left silent. The registry is per
  handler, so a token means nothing to a daemon that did not issue it.
- **Nine refusals are the daemon's own**, and each carries a plain `:type` keyword —
  unqualified, like every other `:type` the tree throws (docs/api.md): `:unauthorized`
  (401, the token), `:not-edn`
  (415 for a missing or wrong content-type — the guard above — and 400 for a body
  that does not read as EDN), `:cross-origin` (403), `:bad-host` (400),
  `:body-too-large` (413), `:bad-args` (400 — the wrong number of args for the op, or
  an `:args` that is not a sequence), `:unknown-op` (400, with the op roster in the
  reply), `:not-found` (404, any route the router does not serve), and
  `:internal-error` (500, the default the catch-all arms fill in when nothing typed
  the failure, so the key is never present with nil in it). Every other `{:ok false}`
  carries whatever `:type` the engine threw — the request-refusal vocabulary
  (`:naming`, `:not-ground`, `:unknown-option`, `:bad-handle`, …) at **400**, since
  it is the caller's mistake, and anything outside that roster at 500 — so a client
  discriminates on the one `:type` vocabulary, with the status as the coarse
  client-fault/server-fault split.
- **The feed adds four refusals to that roster**, all at 400: `:unknown-subscription`
  (a token dropped, timed out, or issued by another daemon), `:bad-cursor` (not a whole
  number, or ahead of what the subscription has delivered), `:too-many-subscriptions`
  (the daemon holds all it will) and `:too-many-waiters` (it has as many long polls
  parked as its thread pool allows — poll on a timer instead). The last two are the odd
  ones and are 400 on purpose: the request is well formed and the daemon is at capacity,
  but the caller is who can act on it — by dropping a subscription, or by not asking to
  wait — and a status of its own would break the promise that a client discriminates on
  `:type`. The first two exist because an empty answer
  was the alternative to avoid for each: [why they refuse
  instead](defenses.md#unknown-subscription-and-bad-cursor-refuse-rather-than-answer-an-empty-feed)
- **Sentex records are projected to plain maps** before they hit the wire (the
  `sentex`-map contract, docs/api.md), so a client needs no `impl` record class.
- **The vocabulary is served** (`:terms`, `:term-count`, `:find-terms`): a remote client
  has no records to walk, so enumerating or prefix-searching the KB's terms has to be an
  op rather than something the client reconstructs. `:find-terms` filters daemon-side, so
  a search returns its hits and not the whole vocabulary; send a regex as its source
  string, since EDN carries no regex literal.
- **Belief is served in batch** (`:believed`): a client rendering n rows asks about n
  handles, and over the wire one op per row is one round-trip per row. `:believed` takes
  the whole handle list and answers the subset that is IN, so a listing costs one call.
- **The write path has a dry run** (`:check`, `:check-edit`): the remote spelling of
  "would this assert succeed, and why not?" (docs/api.md). It stores nothing and answers
  the problems with the same `:type` keywords a refusal carries, so a remote editor
  validates a line *before* it writes rather than by writing and catching.
- **…and a consequence preview** (`:preview`): not whether the batch would be admitted
  but what it would *mean* — the belief it adds and takes away (docs/preview.md). Served
  because the daemon is the single writer, which is exactly what a preview needs: it
  applies the batch and rolls it back, so it must not run beside another write. The
  answer is sentences and handles, EDN-clean, and it is why the op sits with the writes
  rather than the reads although it stores nothing.
- **…and its counterpart after the fact** (`:edit-with-consequences`): the same write as
  `:edit`, reporting what the batch turned out to mean. `:edit` answers with the handles it
  stored, which the caller already knows; this adds the belief that followed and the belief
  that went away, in `:preview`'s entry shapes, so a remote caller renders a promise and its
  outcome with one renderer.
- **Abduction is served with the writes** (`:abduce`, `:abduce-discard`). A hypothesis is
  minted through the whole `assert` pipeline into a scratch context hung below the asking
  one, so the op holds the daemon's single writer for its run. Without `{:keep? true}` the
  scratch is torn down before the reply is built and the KB is left as it was found; with
  it the handles are real and `:abduce-discard` is what drops them
  ([abduction.md](abduction.md)).
- **The anytime reads cross the wire without their tail** (`:ask-within`,
  `:prove-within`). The partial-result contract's `:resume` is a *function* closing over
  an unrealized lazy tail or a DFS goal stack, and neither it nor the heap it pins crosses
  an EDN wire — the same wall `:export`'s `:on-progress` hits. So the daemon answers
  `:results`, `:status`, `:count` and `:elapsed-ms` as ever, and replaces `:resume` with
  **`:resumable`**, a boolean: the search had more to give. **`core/resume` is in-process
  only.** A remote caller continues by asking again under a larger budget — a bounded run
  is a strict prefix of the unbounded one, so the larger call is a superset rather than a
  second answer ([anytime.md](anytime.md)). The boolean is there rather than the key
  simply omitted, because the documented `(when (:resume r) …)` loop would otherwise read
  every partial as complete and stop one step in.
- **The knowledge readings are served** (`:kb-quality`, `:quality-report`, `:argue`,
  `:vocabulary-audit`, `:settle-stats`, `:provenance`, `:add-provenance`).
  `:quality-report` takes the **map**, not the KB, so a client renders a reading it
  already holds; `:kb-quality`'s `:on-progress` is a function and does not cross, so a
  census over a large KB reports nothing until it answers ([quality.md](quality.md)).
  `:add-provenance` is the one write among them, and it is metadata rather than belief —
  it moves nothing ([api.md](api.md)).
- **The cached closures are served whole** (`:genl?`, `:context-up`, `:context-down`,
  `:sees?`, `:has-prop?`, `:props`, `:inverse-of`, `:representative`, `:same-class?`,
  `:equiv-class`, `:deprecated?`). Transitivity and the equality partition are cached
  rather than derived by rules ([taxonomy.md](taxonomy.md), [equality.md](equality.md)),
  so a remote caller has no query that reconstructs them — `:deprecated?` in particular is
  what makes the `rewriteOf` / `sameAs` distinction observable at all.
- **…and the whole-KB enumerations an audit pass folds over** (`:handles`,
  `:contexts-of`, `:canonical-sentex`). `:handles` answers a **sorted vector**: the
  roster a store hands back is a `java.util.Set` that is deliberately not an
  `IPersistentSet` at scale ([storage.md](storage.md)) and has no EDN print form, and
  sorting it means two daemons over one store answer the same bytes.
  `:canonical-sentex` is the content identity of a sentence that was never stored, which
  is the read behind content-addressing one ([canonicalization.md](canonicalization.md)).
- **Five ops take no KB** — `:levels`, `:calculi`, `:readable-sentence`, `:sentence-of`
  and `:quality-report` (above) — and are in
  the table all the same, because a client that has to *display* a stored rule needs the
  author's variable names put back and cannot compute them from a sentex map alone, and a
  rule map carries no `:sentence`, so `:sentence-of` builds its canonical `implies` form. The
  daemon supplies a KB to every row of `serve/ops`; `serve/kbless-ops` is the roster of
  the rows that drop it, held as data because two generators read the table and both have
  to know whether an op's first `vaelii.core` parameter is the KB or an argument.
- **Three reads are for a reader rather than a program** (`:describe`, `:why-not` with
  `{:nearest n}`, `:kb-diff` — [api.md](api.md)). `:describe` matters most over the wire:
  a remote client rendering a term otherwise asks a dozen questions about it and pays a
  round trip for each, and this answers them together. `:why-not` needs no table entry of
  its own for the near-miss option — the op table `apply`s the `vaelii.core` var, so a new
  arity crosses the wire the moment the API grows one. `:kb-diff`'s second side is a
  **path on the daemon's host**, for the reason `:export`'s destination is one: the daemon
  owns the KB, a KB value does not cross an EDN wire, and a text export is a directory the
  daemon can read — so the remote reading is "what has the live KB done since this export
  was taken".
- **Export runs on the daemon's host** (`:export`). It is a write to the *filesystem*
  rather than to the KB, and the directory it names is resolved where the daemon runs —
  the only place it can be, since the daemon owns the KB and there is no stream to hand a
  client back. Two consequences follow: it reports **no progress** (`:on-progress`
  is a function, and functions do not cross an EDN wire), and it runs under the write
  monitor — the walk fetches record by record, which needs the same protection a query's
  projection does ([why](defenses.md#a-read-that-crosses-the-wire-is-realized-inside-the-write-monitor)).
  There is no `:import` op — `import!` is
  a local operation, run in the process that owns the (empty) KB the dump lands in. There
  is no text op either, and for the two halves of the same reason: `export-text!` resolves
  its directory where the daemon runs, exactly as `:export` does, and would be served on
  the same terms — but `load-text!` reads a path, so over a wire it would name a file on
  the daemon's disk while reading like one on the caller's. Text goes over the CLI, which
  is in the process that can see the files.
- **Five `vaelii.core` fns are deliberately not ops**, and each is the same kind of
  absence: a lifecycle operation belongs to whoever owns the process, and the daemon's
  callers do not.

  | Not served | Why |
  |---|---|
  | `import!` | a dump lands in an **empty** KB, in the process that owns it — a daemon is already serving one |
  | `recover` | rebuilds the taxonomy and the JTMS from the durable stores at open; a client cannot know the daemon is unrecovered, and a rebuild mid-service moves belief under every other caller |
  | `reindex` | the same, for the index — a whole-store rewrite under the one lock every other request is queued behind |
  | `clear!` | destroys the KB the daemon exists to serve, and leaves every client's handles naming nothing |
  | `close!` | ends the process's ownership of the store; the socket that asked would be answering from a KB that no longer has one |

  All five stay reachable where they belong — the CLI, `vaelii.starter`, or the process
  that called `open-kb` — and none of them is a read a client is short of.
- `serve/app` is a pure `request -> response` handler (reitit-ring), so it is tested
  without a socket; `serve/start` runs it on jetty and returns the `Server`.

- **The browser serves the protocol too.** `vaelii.browser.web` answers `GET /health` and
  `POST /op` over its active KB by calling the daemon's handler (`serve/handle-op`), so a
  native client connects to `http://127.0.0.1:3000` as it connects to a daemon. The op
  table, guards, ceilings and refusals are the daemon's. The monitor is the browser's
  `write-monitor`, which the browser's own write routes take, so the browser process stays
  the KB's one writer. Three refusals precede the op: **404** `:not-found` when the browser
  reads a remote daemon (`--attach`), and **409** `:still-loading` or `:still-exporting`
  while a job writes or an export walks the active KB. The two 409s refuse reads as well,
  because the op table does not mark which ops write. The token rule is the browser's:
  a loopback bind asks for none, and `--listen` with an address requires it on every
  route, `GET /health` included ([web.md](web.md)).

## Client — `vaelii.client`

```clojure
(require '[vaelii.client :as c])
(def conn (c/client "localhost" 4200))
(c/assert conn '(dog Muffet) 'CxNaturalWorld)    ; => 1
(c/query  conn '(dog ?x)   'CxNaturalWorld)    ; => ({?x Muffet})
(c/ask?   conn '(animal Muffet) 'CxNaturalWorld)
(c/why    conn 1)
```

- A thin client over JDK `java.net.http` — **no dependency** (JDK 21 ships it).
- **Every call threads an explicit connection handle first** — `(query conn goal ctx)` —
  the network mirror of `vaelii.core`'s explicit-`kb` API. `client` returns a `conn`
  holding a reusable `HttpClient`; no socket opens until a call. It reads `:timeout-ms`
  and `:token` and nothing else — a key outside those two, or a non-map, is refused
  `:unknown-option` at the same entry point every other options map goes through, because a
  misspelt `:token` is not an explicit nil: it falls back to `VAELII_API_TOKEN`, so a
  caller meaning to present a different credential presents the environment's.
- **The `conn` carries the bearer token**, and every call sets one more header on the
  request it was already building. `(client "localhost" 4200 {:token "…"})` names it;
  omit the key and it is `VAELII_API_TOKEN`, the same variable the daemon reads, so a
  client and a daemon in one environment agree with nothing configured. An explicit
  `{:token nil}` sends no `Authorization` header, which is what an open daemon wants. A
  call with no token to a daemon that requires one throws the daemon's own
  `:unauthorized`, like any other remote refusal.
- A daemon `{:ok false}` reply becomes an `ex-info` carrying its `:error` and `:type`,
  so a remote naming / disjointness refusal is indistinguishable from a local one. The client mints
  two `:type`s of its own, for what the wire hands it that the daemon never typed:
  `:daemon-error` (an `{:ok false}` with no usable `:type` — the fallback holds even
  against `:type nil`) and `:bad-reply` (a reply that does not read as EDN, or reads
  as something other than a map — a proxy's HTML error page, a truncated body).
- **Every op has a wrapper, and the op table is what says so.** A wrapper mirrors the
  `vaelii.core` fn its op runs — bare or `!`-marked exactly as `vaelii.core` spells it,
  never as the op keyword does (the keywords drop the suffix, so `:retract` runs
  `retract!`) — and carries that fn's arities with `kb` replaced by `conn`. Arity for
  arity, because a wrapper short of an arity the daemon accepts is a read a remote caller
  cannot make: `(c/why conn h {:max-depth 32})` is how a `{:truncated? true}` branch is
  re-asked whole.

  The claim is **generated rather than maintained**. `lein regen-client`
  (`vaelii.regen-client`) reads `serve/ops`, resolves each op in `vaelii.core` and writes
  the wrappers between two markers in `vaelii.host.client` and `vaelii.client`; a
  hand-written wrapper in the public shim wins, so prose written for one survives.
  Generated at *build* time rather than macroexpanded from the table, because requiring
  the table would pull the engine, jetty and reitit onto the classpath of a namespace
  whose whole point is not needing them — the client is JDK-only and stays that way.
  `client_surface_test` compares both files against what the generator would write now,
  so an op added to the daemon reds the suite until the wrapper is written; that red is
  the notification rather than the chore, which is the bargain the frozen goldens under
  `test/golden/` make too.

  `call` still reaches any op in `serve/op-names` directly, which is what the change
  feed (`serve/feed-ops`, no `vaelii.core` fn behind it) and an op newer than the client
  both need.
- **`assert!` and `assert-rule!` are deprecated spellings** of `assert` / `assert-rule`
  on `vaelii.host.client`, kept because a caller outside this repo may hold them.
  Identical in every other respect: `!` means *irreversible* ([api.md](api.md)) and an
  assertion is neither, `retract!` taking it back.
- **`blocked-justifications`** is the read a remote proof tree needs and no per-handle
  call answers: the ids a rule exception currently blocks, every antecedent IN and
  supporting nothing ([exceptions.md](exceptions.md)). Blocking lives in the network
  rather than in a record, so without this op an attached reader draws a blocked
  justification as supporting.
- **`watch` / `poll` / `unwatch` / `watchers` are the change feed** ([feed.md](feed.md)),
  and the one place the client's shape differs from `vaelii.core`'s: in process `watch`
  takes a callback, and here it returns a token a caller reads forward with a cursor.

  ```clojure
  (let [{:keys [token cursor]} (c/watch conn)]          ; or (c/watch conn goal ctx)
    (loop [c cursor]
      (let [{:keys [events cursor lagged]} (c/poll conn token c {:wait-ms 20000})]
        (when (pos? lagged) (resync!))                  ; the ring outran this reader
        (run! render! events)
        (recur cursor))))
  ```

  `:wait-ms` is the long poll, and the only thing it costs this client is a read timeout
  extended by the wait it asked for — one more `Duration` on the request builder, no
  second protocol and no dependency. `:lagged` is on every reply and is the one field a
  caller must read: non-zero, the daemon's ring dropped that many events before this
  poll reached them.

## Browsing a live daemon — `vaelii.browser.access`

The browser (`vaelii.web`) reaches a KB through the `vaelii.core` surface alone. That
surface is re-exported by `vaelii.browser.access` as a facade whose every op takes a
*target* that is either an in-process KB or a remote daemon — the reads the browser
renders with (`check` among them: it writes nothing, so it is a read), plus the four
writes it performs: `edit!`, `edit-with-consequences!`, `forward-chain`, and `preview`
(filed with the writes although it stores nothing, because it applies the batch and
rolls it back and so holds the single writer for its duration):

```sh
lein serve 4200 /var/lib/vaelii              # a daemon owns the KB
lein run -m vaelii.web --attach localhost 4200   # browse it, over the API, on :3000
```

- **The token rides along.** `access/remote` builds an ordinary client, so an attached
  browser reads `VAELII_API_TOKEN` out of its own environment and presents it on every
  page. Start it where the daemon's token is exported and there is nothing to configure;
  start it without, against a daemon that requires one, and every page reports the
  daemon's `:unauthorized` rather than rendering an empty KB.

- **Why it exists:** the single-writer lock means a second process can't open the
  daemon's disk KB directly, so to browse a *live* daemon you must go through its API.
  `--attach` does exactly that; every page reads over HTTP instead of in-process.
- **How:** `web/app` is written against the access facade (`local`/`remote`), so it runs
  unchanged either way — a raw KB takes the in-process path, `(remote host port)` takes
  the client. Local and remote dispatch through the *same* `serve/ops` table, so they
  can't drift, and a page renders byte-for-byte identically over either.
- The default (no `--attach`) is still an in-process starter KB — fast, standalone, and
  the right choice for local exploration. Attach is for inspecting a running daemon.
- **Writing over the wire:** the browser's Save and its Retract dispatch to the daemon
  `:edit` op, its assert form and its accepted-proposal commit to
  `:edit-with-consequences` (which answers with what the batch turned out to mean), and
  its forward-chain trigger to `:forward-chain` — so modifying a KB works against an
  attached daemon too, with the daemon the single writer serializing each one under its
  lock. The write forms are preceded by a `:check-edit` round-trip, so a refusal costs
  a message rather than a half-applied batch; the proposal preview runs on a local KB
  only (`docs/web.md`), so an attached browser proposes without previewing.

## Container — the daemon as an image

```sh
export VAELII_API_TOKEN=$(openssl rand -hex 32)   # every compose subcommand reads it, build included
docker compose up -d                              # builds the image when it is absent, then starts
curl -fsS http://127.0.0.1:4200/health            # {:ok true} — the one route needing no token
```

The variable is exported rather than set on the `up` line because compose interpolates
the whole file when it *parses* it: the token is declared required, so a bare
`docker compose build` — or `config`, or `ps` — refuses before it does its own job.
`docker build -t vaelii .` reads no compose file and needs nothing set.

`Dockerfile` builds in two stages and ships the second: Leiningen resolves and
`lein uberjar` runs in a JDK stage, and what reaches the runtime image is a JRE and the
jar. The uberjar needs no checkout and no local artifact — every `:dependencies` entry
resolves from a public repository and the uberjar path activates no profile — so the
image builds from a clean clone. `clojure.main -m vaelii.host.serve` is the entry point
rather than `java -jar`, because the jar's Main-Class is `vaelii.core`.

- **A token is not optional here.** The container binds an address so that a published
  port can reach it, and `vaelii.serve` refuses that bind with no `VAELII_API_TOKEN`,
  exiting 2 before it opens the KB. `docker-compose.yml` declares the variable required,
  so the failure is a message at `up` rather than a daemon that starts unauthenticated.
  The port is published to host loopback: the daemon authenticates, and putting an
  authenticated writer on a public network interface stays a deliberate act.
- **One container per volume.** The `:disk` backend takes an exclusive lock on open and
  refuses a second opener with `:disk-locked`, which is uncaught — so a second container
  over one volume dies at startup rather than corrupting the store. A `replicas:` count
  is a configuration error, not throughput, which is why the compose file has none.
- **The heap is the operator's.** No `-Xmx` is baked in; a JVM in a container reads the
  cgroup limit, so `--memory` is the ceiling. No collector flag is set either, and that
  is measured rather than skipped. `lein perf`, two alternating passes at a fixed 6 GiB
  heap, 2026-08-06: the JDK default took **about 41 s at roughly 1.5 GB** peak resident,
  generational ZGC **about 56 s at roughly 6 GB** — about a third slower holding four
  times the resident set, and ZGC alone tripped the `:negation-arbitration` growth bound
  on both passes. In a container the resident set is also
  what the memory limit is set against, which is what makes the choice operationally
  relevant rather than academic. [why the JDK default over a concurrent
  collector](defenses.md#the-default-collector-is-chosen-against-this-engines-measured-footprint)
  `lein with-profile +zgc` selects it for a JVM that has a reason.
- **`HEALTHCHECK` polls `/health`**, the one route that answers without the token, since
  a daemon only its token-holder can probe is one no orchestrator can watch. An empty
  volume answers in about three seconds; the start period is far longer than that because
  it is sized for the other case, where a restart over a populated volume runs `recover` —
  one pass over every stored record — before Jetty accepts a connection. That pass is
  O(records), so a store large enough to outlast the window wants a longer one.
- **The image sets `VAELII_LOG_LEVEL`.** Unset, the level installs no backend at all, and
  a container that writes nothing is one nobody can operate.
- **No ASP solver is installed.** `set-solver` is `:stub` unless asked otherwise, and the
  stub is in-process ([asp.md](asp.md)).

A client reaches it with the same token from its own environment:

```clojure
(require '[vaelii.client :as c])
(def conn (c/client "127.0.0.1" 4200))                   ; VAELII_API_TOKEN, or :token
(c/health conn)                                          ; => {:ok true}
(c/assert conn '(dog Muffet) 'CxNaturalWorld)
```

## Logging — a dial, and what is behind it

```sh
VAELII_LOG_LEVEL=debug lein serve 4200 /var/lib/vaelii   # the level this process starts at
```
```clojure
(v/set-log-level :debug)   ; ...or the level it changes to, without stopping
(v/log-level)              ; => :debug — nil when the engine has installed nothing
```

- **Five levels, quietest first: `:error :warn :info :debug :trace`.** Anything else is
  refused by name (`:unknown-option`), by the variable and by the call alike — a dial
  that read `:verbose` as `:info` would be one an operator turns and believes.
- **The point of a dial is that a running process turns it.** Raising verbosity by
  restarting costs a `recover` proportional to the corpus, and the process that most
  needs a different level is the daemon a week into a run that has started refusing
  things. Lowering it is the same argument with a number attached: at `:warn` a bulk
  load into a KB with a definitional clash in it prints a line per dropped conclusion.
- **Unset, the engine installs no backend at all.** `VAELII_LOG_LEVEL` and
  `set-log-level` install one; loading the engine and opening a KB do not. An
  application that put its own function in `taoensso.trove/*log-fn*` keeps it — a
  library that replaces its host's logging because it was *loaded* costs the host every
  line it has, and leaves it nothing to correlate. With nothing installed the level is
  Trove's own default, its console backend at `:info`.
- **Process-wide, not per-KB.** Two KBs in one JVM share one `*log-fn*`, so there is one
  dial and it is the process's.
- **What each level carries.** `:error` is a load or an export that failed outright.
  `:warn` is most of what the engine says, and nearly all of it is *a conclusion that
  did not land*: `::dropped-conclusion` with the ledger entry that names it,
  `::chain-truncated`, the naming and aggregate refusals, a definitional clash the
  exception fixpoint could not settle. `:info` is lifecycle — a daemon or browser
  starting, a catalog loading, the posture a server bound in. `:debug` is the boundary
  of each run plus the disk store's own open: what a chaining run concluded and how long
  it took, what a settle cost in passes and what it found, the rule a dropped conclusion
  came from (the `:warn` line names it by *handle*, which is not a thing a log reader can
  look up), and the lock, cache and premise-set lines the durable store writes as it
  opens. Nothing logs at `:trace`; the level exists so a host application's own
  statements have a floor below the engine's.
- **It is not an op.** `serve/ops` carries reads and writes, all of them about
  the KB the daemon owns. The level is about the *process*, the bearer token is optional
  on the loopback default, and an op that turns on `:debug` is a caller spending the
  operator's disk from the far end of a socket. A daemon's level is the one it started
  with, or one set from its own REPL.

### Neither server logs a request

Jetty logs through SLF4J, and every entry point that runs one — `lein run -m
vaelii.web`, `lein serve`, `lein browser`, `lein test`, and the standalone jar `lein
uberjar` builds — carries a no-op binding, `org.slf4j/slf4j-nop`, that silences Jetty's
lifecycle output and its request log with it, rather than leaving SLF4J to print a "no
providers" line on every start. It lives in the `:dev` and `:uberjar` Leiningen
profiles, not top-level `:dependencies`: the same rule the log dial above holds to
(`vaelii.impl.logging` installs no backend unless asked) applies to Jetty's, and
top-level `:dependencies` is exactly what would make this binding an application's
whether it asked for one or not — winning SLF4J's provider race against whatever
backend that application had already chosen. An application depending on vaelii as a
library resolves no SLF4J provider from it.

What follows is worth knowing before an incident rather than during one:

- **A refused request leaves no line on the server.** The 401, the 403 (cross-origin),
  the 413 (body over the ceiling) and the 415 (not `application/edn`) are all answered by
  middleware that writes nothing. The evidence for one is the status code the *client*
  holds. The daemon does log a **500** (`::op-error`, at `:warn`, with the
  exception) and its two start-up posture lines — which is why the authentication posture
  is announced at start: it is the line to grep for afterwards.
- **Turning the dial up does not add request lines.** The dial governs the engine's own
  statements; there are no HTTP ones for it to reach.
- **An application embedding the engine chooses its own SLF4J provider, or none.**
  Nothing here wins that race on its behalf. One that ships Jetty, or anything else
  logging through SLF4J, and wants the same silence adds `org.slf4j/slf4j-nop` — or any
  other provider — as its own dependency; one that already ships a provider keeps
  seeing exactly that provider's output.

## Configuration — every switch, and where it is read

Everything an environment variable or a JVM system property decides, in one table. The
**options maps are a different surface** and are not repeated here: they are already
askable — `kb/opt-keys` is the roster `open-kb` checks against ([storage.md](storage.md)),
`assert-opt-keys` is `assert`'s ([api.md](api.md)) — and a key outside one is refused by
name. A misspelt *variable* can be asked nothing at all, which is why these need a table.

Three things hold for every row:

- **A value outside the domain is refused, not read as the other branch.** The
  properties `vaelii.impl.config` reads are checked at `open-kb` (`config/check!`), so
  `vaelii.disk.fsync=always` fails the open naming itself rather than silently selecting
  the three-second tick. The ASP three are in that sweep too, which is why they are read
  through `config` rather than where they are used: a misspelt backend read as a bare
  keyword matched no arm and ran **auto**, and a non-numeric byte cutoff threw from a
  cache at the first solve. Both now refuse at the same entry point as everything else. `VAELII_MAX_BODY_BYTES` and `VAELII_LOG_LEVEL` refuse at
  namespace load, each being the root value of a var. **Every** switch is in that sweep
  and not the ones somebody remembered to list: `check!` walks `config/switches`, one row
  per reader, and a reader with no row fails the build rather than going unchecked.
- **The boolean switches share one vocabulary**: `true` `1` `on` `yes` and `false` `0`
  `off` `no`, case-insensitively, and nothing else. A blank value is *unset* — an
  exported-but-empty variable is the shell's way of saying nothing.
- **A property and a variable spelling of one switch are one switch**, and the table says
  which is read first. Nothing here is named both ways by accident: a JVM cannot set its
  own environment, so the property twin is what a test and an embedded process use.

The names themselves are frozen: `config_surface_test` collects them from the sources and
pins them against `test/golden/config-surface.edn`, both directions, and checks that every
one has a row below and that every citation resolves. Renaming or
removing one is **Breaking** (CONTRIBUTING §3.8). Nine rows are outside that net and say
so where they sit.

**A "Read at" cell is a floor, not an address.** `web.clj:NNN+` reads *start at line
NNN and read down*, and the number is rounded to a multiple of ten. An exact line was
checked exactly and drifted the moment anything above it was edited — a comment six
screens up failed the surface test with a diff that had nothing to do with
configuration, and the fix was always to retype a number nobody is indistinguishable from a number.

The rule the test applies is **floor ≤ the file's first mention of the switch**, which
is what makes the tolerance real and the check still worth running. Insertion above
moves that first mention *down* and the floor keeps holding, without bound; a floor that
has drifted *past* what it cites fails, as does a wrong file or a switch renamed out
from under its row. Checking "named anywhere at or below the floor" instead was the
obvious reading and is too weak to catch anything — `VAELII_WEB_PORT` is named in a
docstring, in `--port` help text and in a startup line, so a floor a hundred lines past
the read still found one of them. Set a new floor by rounding the first mention down.

### Operator

**The servers.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_API_TOKEN` | `src/vaelii/host/guard.clj:140+` | any string; blank or whitespace-only is unset | unset | The one shared bearer token: with it set every daemon request carries `Authorization: Bearer …` or is answered 401, and a client and an attached browser present it from their own environment. |
| `VAELII_ALLOWED_HOSTS` | `src/vaelii/host/guard.clj:40+` | comma-separated host **names**; a port on an entry is read as the name alone, and a value naming nothing is unset | unset | The `Host` headers a server answers, overriding the list the bind address implies. Entries are compared in the form a `Host` header is, so `kb.example.com:8080` and `kb.example.com` are one entry. |
| `VAELII_MAX_BODY_BYTES` | `src/vaelii/host/guard.clj:160+` | a positive whole number of bytes | `16777216` (16 MiB) | The request-body ceiling both servers refuse above, with 413. |
| `VAELII_MAX_QUERY_MS` | `src/vaelii/impl/config.clj:330+` | a whole number of milliseconds, 0 or more | `30000` | The wall clock a served read may name. A request may name less and is refused (`:over-ceiling`, 400) for naming more; a read naming none is given this, the four backward-search entry points included. `0` lifts the ceiling. |
| `VAELII_MAX_QUERY_DEPTH` | `src/vaelii/impl/config.clj:340+` | a whole number of rule expansions, 0 or more | `256` | The rule-expansion depth a served read may name, refused the same way. `0` lifts it. |
| `VAELII_WEB_PORT` | `src/vaelii/browser/web.clj:5830+` | a port number | `3000` | The port the browser binds. An unparseable value falls through to the property rather than failing the start. |
| `vaelii.web.port` | `src/vaelii/browser/web.clj:5830+` | a port number | `3000` | The same port, read after the variable. |
| `VAELII_KB_DIR` | `src/vaelii/browser/web.clj:6930+` | a KB directory: a store, a dump or a corpus; blank is unset | unset | The directory the browser loads at startup, as a catalog job with belief recovered, while it serves the starter. The KB becomes the active one when the load finishes. A path holding no KB is logged and the browser stays on the starter. The three `scripts/start-vaelii*.sh` set it. |
| `VAELII_HEAP` | `scripts/lib/start.sh:20+` | a JVM heap size (`40g`, `24g`) | `40g` | The `-Xmx` the three `scripts/start-vaelii*.sh` add to `JVM_OPTS`, beside `-XX:+ExitOnOutOfMemoryError`. |
| `VAELII_DEV` | `src/vaelii/impl/config.clj:240+` | the boolean vocabulary | `false` | Whether `lein browser` hot-reloads source edits (`docs/web.md`) and re-reads its stylesheet per request, serving it uncached. Set only by `scripts/start-vaelii-dev.sh`; `-main` never hot-reloads. |
| `VAELII_PROFILER` | `src/vaelii/impl/config.clj:240+` | the boolean vocabulary | `false` | Whether the browser starts the sampling profiler's UI. Off unless asked for: it attaches an agent to the JVM and serves on a port of its own with no authentication. The dependency ships in the `:repl` profile, so `lein browser` has it and `lein run -m vaelii.web` does not — with it absent the start logs a line and `/caches` says so rather than linking to nothing. |
| `VAELII_PROFILER_PORT` | `src/vaelii/impl/config.clj:250+` | a port number | `8080` | Where that UI binds. Read only when the switch above says to start one. |
| `VAELII_LOG_LEVEL` | `src/vaelii/impl/config.clj:280+` | `error` `warn` `info` `debug` `trace`, case-insensitive | unset | The level the engine's own statements print at, installed as the engine loads. Unset installs no backend at all, which is a setting rather than a default. |
| `VAELII_CACHE_SCALE` | `src/vaelii/impl/config.clj:290+` | a number 0 or more | `1.0` | The multiplier on every in-memory derived cache's shipped entry limit, applied as the engine loads. Below 1 shrinks the caches for a small heap; above 1 grows them for a bulk load. A per-cache floor keeps a small scale from taking a cache below the point where it saves nothing. `vaelii.core/set-cache-scale` is the same dial on a running process, and `caches` shows the effective limit each cache enforces. |

**The durable store.** All system properties, all read at `open-kb`.

What the defaults cost, stated once rather than left to be assembled from the rows: on
the default an append is durable **within `vaelii.disk.sync-ms`**, so a machine that
loses power or a JVM killed outright drops up to three seconds of acknowledged writes.
A clean exit drops nothing — `close!` and the shutdown hook flush — so the window is a
crash window and not a shutdown one. `vaelii.disk.fsync=dsync` closes it and makes every
append durable when it returns, which is the trade a store of record wants and most of a
common-sense KB does not. The other defaults are off because *on* is the choice that
costs something a KB cannot give back for free: `tokens` adds a durable ground truth a
store opts into, and `compress` spends CPU per frame.

The mapped index image is not among them, because it is not a switch. It is an index
representation, named in the KB's own opts as `{:backend :disk-snapshot}` — the one
pairing there is, the image being stamped with the disk record store's own slot
fingerprint — so which index a KB holds is readable from its configuration rather than
from the JVM's, and only macOS and Linux can swap one, so that backend is refused
elsewhere ([storage.md](storage.md)). `vaelii.index.snapshot` is read for one purpose
only, which is to **refuse** it: it has the row below because the build reads the name,
and a process whose unit file sets it fails at `open-kb` rather than running on a
representation nobody chose.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `vaelii.disk.dir` | `src/vaelii/impl/disk/backend.clj:240+` | a directory path | `<java.io.tmpdir>/vaelii-disk` | The base a disk KB's space directory hangs under when no `:dir` names one. |
| `vaelii.disk.fsync` | `src/vaelii/impl/config.clj:10+` | `dsync`, or unset | unset | Whether every append is durable when it returns (`dsync`), or durability waits for the tick below. |
| `vaelii.disk.sync-ms` | `src/vaelii/impl/config.clj:160+` | a whole number ≥ 0; `0` stops the daemon | `3000` | The durability daemon's tick, in milliseconds. |
| `vaelii.disk.auto-compact` | `src/vaelii/impl/config.clj:10+` | the boolean vocabulary | `true` | Whether background and opportunistic compaction runs at all — one knob for the fsync tick, the close path, and a `:disk-snapshot` KB's mid-life image refresh, which is an opportunistic compaction of a derived structure like the others. `false` is how a batch that fills a KB in one run and closes cleanly asks for exactly one image, at the end. |
| `vaelii.disk.compact-dead-ratio` | `src/vaelii/impl/config.clj:200+` | a number from 0 to 1 | `0.5` | The dead fraction a log must reach before compacting it is worth the write. |
| `vaelii.disk.compact-min-interval-ms` | `src/vaelii/impl/config.clj:210+` | a whole number ≥ 0 | `300000` | The floor between two auto-compactions of one backend. |
| `vaelii.disk.compress` | `src/vaelii/impl/config.clj:170+` | `zstd` `lz4` `none` `off` `false` | uncompressed | The codec durable frames are written with. |
| `vaelii.disk.tokens` | `src/vaelii/impl/config.clj:60+` | the boolean vocabulary | `false` | Whether sentex bodies are written as token ids. Reading is never gated on it — a frame carries its own tag. |
| `vaelii.disk.cache` | `src/vaelii/impl/config.clj:180+` | a whole number ≥ 0; `0` disables the cache | `65536` | Hot records held in memory per kind. |
| `vaelii.disk.lock` | `src/vaelii/impl/config.clj:210+` | the boolean vocabulary | `true` | Whether the single-writer `FileLock` is taken when a directory opens. Off removes the enforcement and not the contract. |
| `vaelii.index.snapshot` | `src/vaelii/impl/config.clj:230+` | none — the domain is empty and every value is refused | unset | **Refused, not read.** The mapped index image is an index representation, so it is named in the KB's opts (`{:backend :disk-snapshot}`) and not process-wide. `config/check!` reads it at every `open-kb`, so a `-D` left over from an older unit file fails the open with `:unknown-option` naming the backend to take instead — rather than a KB quietly rebuilding the index the property was meant to save. |
| `vaelii.index.snapshot-drift` | `src/vaelii/impl/config.clj:250+` | a ratio, 0–1 | `0.5` | How far a `:disk-snapshot` KB's live index may drift from its image — in indexed roots, against the count the image holds — before the writer rewrites it. The rewrite happens on the writer's thread and is a full image write, so `vaelii.disk.compact-min-interval-ms` floors how often it can happen. **`0` is the most eager setting in the range, not the off one**: as a threshold it means "any drift at all", so it rewrites the image on every write past the floor — 400 asserts under it measured 401 images. `vaelii.disk.auto-compact=false` is what turns the mid-life refresh off. Only `assert` drives the cadence: a store filled by `reindex` or by an import gets one image, at the close, whatever this says. |
| `vaelii.belief.snapshot` | `src/vaelii/impl/config.clj:270+` | none — the domain is empty and every value is refused | unset | **Refused, not read.** A reasoning image is written and installed for every `{:backend :disk-snapshot}` KB on the dense network ([storage.md](storage.md#the-reasoning-image)), and no property turns it on or off. `config/check!` reads it at every `open-kb`, so a `-D` left in a unit file fails the open with `:unknown-option` naming the backend to take instead. |

**Finding a KB.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_KB_PATH` | `src/vaelii/browser/catalog.clj:20+` | `:`-separated directory list | `./kbs` and `~/.vaelii/kbs` | The directories KB discovery walks. |
| `vaelii.kb.path` | `src/vaelii/browser/catalog.clj:250+` | as above | as above | The same list, read after the variable. |
| `VAELII_KB_CATALOG` | `src/vaelii/browser/catalog.clj:20+` | a file path | `~/.vaelii/catalog.edn` | The file naming KBs that live outside the search path. |
| `vaelii.kb.catalog` | `src/vaelii/browser/catalog.clj:260+` | a file path | as above | The same file, read after the variable. |

**What the engine reasons with.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_ARBITRATE_CONSTRAINTS` | `src/vaelii/impl/config.clj:230+` | the boolean vocabulary | `false` | Whether the process arbitrates a definitional clash rather than refusing it. A KB naming a `:constraints` policy overrides it. |
| `VAELII_ASSERTIVE_ARG_TYPES` | `src/vaelii/impl/config.clj:230+` | the boolean vocabulary | `true` | Whether the argument constraints entail types as well as constrain them; `=0` opts out to the constraint-only reading ([argtypes.md](argtypes.md)). |
| `VAELII_ASP_SOLVER` | `src/vaelii/impl/config.clj:270+` | `clingo` `clasp` | unset | Which ASP backend solves. Unset is auto: in-process clingo when it loads, else clasp. A name outside the roster is refused rather than read as auto. |
| `vaelii.asp.solver` | `src/vaelii/impl/config.clj:50+` | `clingo` `clasp` | unset | The same choice, and it is read **first**. |
| `VAELII_CLINGO_MAX_BYTES` | `src/vaelii/impl/config.clj:280+` | a whole number of bytes, 0 or more | `3000` | The program size above which auto mode routes a plain-ASP program to clasp even where clingo loads. |
| `VAELII_ASP_TIME_LIMIT` | `src/vaelii/impl/config.clj:290+` | a whole number of seconds, 0 or more | `60` | How long one ASP solve may run before the backend is interrupted; 0 lifts the limit. An interrupted solve is no answer: the edge solver decides nothing and an imperative refuses with `:solver-failed`. One *operation* makes several solves, each with the whole budget ([asp.md](asp.md)). |
| `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS` | `src/vaelii/impl/config.clj:400+` | a whole number ≥ 1 | `12` | The most members a coupled dilemma cluster may hold for the solve-free brave/cautious classifier to enumerate its resolutions; a larger cluster is left `:supportable`, and a backend is the tool for the large interacting set. Read per classification by `classify-local`, which reads resolutions from the JTMS and calls no solver ([labeling.md](labeling.md)). |
| `VAELII_CLASSIFY_RESOLUTION_BUDGET` | `src/vaelii/impl/config.clj:400+` | a whole number ≥ 1 | `20000` | The number of candidate subsets one cluster's resolution enumeration may examine before the classifier abandons the cluster to `:supportable`. A cluster of *m* members has 2^*m* − 1 candidates, so under the default member cap of 12 (at most 4,095) the budget binds only once `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS` is raised above 14. A per-read search bound, nothing retained. |
| `VAELII_CLASSIFY_MAX_JOINT_OPTIMA` | `src/vaelii/impl/config.clj:400+` | a whole number ≥ 1 | `1024` | The cap on the product of optima a cross-cluster datum's classification enumerates — the clusters that move the datum, times their optima. A datum whose product is larger is left `:supportable`, since its class needs joint resolutions a backend enumerates. |
| `vaelii.clingo.lib` | `src/vaelii/impl/asp/clingo.clj:20+` | a library name or an absolute path | `clingo`, resolved through `jna.library.path` | Which libclingo the in-process bridge loads. |

**The model host.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_LLM_PROVIDER` | `src/vaelii/host/llm/provider.clj:10+` | `ollama` `anthropic` | unset | Which backend the LLM pipeline calls. |
| `vaelii.llm.provider` | `src/vaelii/host/llm/provider.clj:10+` | `ollama` `anthropic` | unset | The same choice, read **first**. |
| `VAELII_OLLAMA_HOST` | `src/vaelii/host/llm/ollama.clj:40+` | a base URL | `http://localhost:11434` | Where the Ollama backend connects. |
| `VAELII_OLLAMA_MODEL` | `src/vaelii/host/llm/ollama.clj:40+` | a model name | `phi4:14b` | The model a turn runs. |
| `VAELII_OLLAMA_GENERATION_MODEL` | `src/vaelii/host/llm/ollama.clj:60+` | a model name | `qwen3-coder:30b` | The model the page-generation path runs. |
| `VAELII_OLLAMA_NUM_CTX` | `src/vaelii/host/llm/ollama.clj:90+` | a whole number of tokens | `8192` | The context window a request asks for. An unparseable value is indistinguishable from the default. |
| `VAELII_OLLAMA_KEEP_ALIVE` | `src/vaelii/host/llm/ollama.clj:80+` | an Ollama duration (`30m`, `0`) | `30m` | How long the host is asked to hold the model resident after a turn. |

**Read, not ours.** Four names another project defines and the engine reads. An operator
still sets them, and a rename by Anthropic or Ollama is their change rather than a break
here.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `OLLAMA_HOST` | `src/vaelii/host/llm/ollama.clj:40+` | a base URL; a bind address (`0.0.0.0`, `::`, `*`) is ignored | unset | Ollama's own variable, read after `VAELII_OLLAMA_HOST`. A host binds `0.0.0.0`; nothing connects to it. |
| `ANTHROPIC_API_KEY` | `src/vaelii/host/llm/anthropic.clj:100+` | an API key | unset | The credential sent as `x-api-key`, tried first. |
| `ANTHROPIC_AUTH_TOKEN` | `src/vaelii/host/llm/anthropic.clj:100+` | a bearer token | unset | The credential sent as `Authorization: Bearer`, tried when there is no key. |
| `ANTHROPIC_BASE_URL` | `src/vaelii/host/llm/anthropic.clj:370+` | a base URL | `https://api.anthropic.com` | The host that backend calls. |

**The build stamp.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `vaelii.build` | `src/vaelii/impl/io/export.clj:180+` | any label | the git HEAD, else `dev` | How the writing build names itself in a dump's `meta.edn`. Diagnostic: a dump that will not read is first a question about which build wrote it. |
| `VAELII_BUILD` | `src/vaelii/impl/io/export.clj:180+` | any label | as above | The same label, read after the property. |

### Developer — the suite and the scripts

CI sets these too; nothing in a deployment does.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_TEST_BACKEND` | `test/vaelii/test_util.clj:210+` | a `<records>-<index>` backend name (`memory`, `disk-log`, `memory-columnar`, …), or `overlay` | `memory` | Which of the eight stores the whole suite runs on. |
| `VAELII_TEST_TMS` | `test/vaelii/test_util.clj:60+` | `reference` `dense` | `dense` | Which truth-maintenance representation the suite runs on. |
| `VAELII_TEST_SPACE` | `test/vaelii/test_util.clj:190+` | a whole number from 5 to 15 | `15` | The top of the two-space block the suite's KBs live on, so two runs can have distinct directories. |
| `VAELII_AUDIT_SUPPORT` | `test/vaelii/test_util.clj:460+` | a directory that exists | unset (no audit) | Makes the suite's teardown write, one EDN map per line into `<dir>/<pid>.edn`, every stored justification whose conclusion's context does not see the context of one of its supporters — an antecedent, or the rule a firing names. Changes no test's outcome. |
| `VAELII_TEST_TMPDIR` | `test/vaelii/truncation_fuzz_test.clj:70+` | a directory that exists | unset (the platform temp directory) | Where the `^:fuzz` truncation sweep builds each probe's directory. A probe's whole cost is one device cache flush, so pointing this at a tmpfs (`/dev/shm`) takes the sweep from ~10 minutes to a couple. Nothing else reads it. |
| `VAELII_TEST_LOG_LEVEL` | `project.clj:130+` | `error` `warn` `info` `debug` `trace` | `error` | The floor the `:test` profile installs the engine's logging at, through `set-log-level` itself. |
| `VAELII_TEST_NS_COUNTS` | `project.clj:150+` | any non-empty value | unset | Prints one `NSCOUNT <namespace> <assertions>` line per test namespace. Two runs diffed name the namespace whose count moved, which is what `test-backends.sh`'s assertion-count check cannot say on its own. |
| `VAELII_BENCH_LOG_LEVEL` | `project.clj:170+` | `error` `warn` `info` `debug` `trace` | `error` | The same floor for the `:bench` profile, so `lein perf` and the `bench-*` harnesses print readings rather than the logging their workloads provoke. |
| `VAELII_LLM_LIVE` | `test/vaelii/test_util.clj:200+` | `1` `true` `yes` | unset | The consent to call a real model. The `^:llm` mark is the separate half, and both are needed. |
| `VAELII_RETE` | `test/vaelii/test_util.clj:30+` | the boolean vocabulary | `false` | Runs the suite's forward chaining through the incremental matcher instead of the reference. |
| `VAELII_HIER` | `test/vaelii/test_util.clj:60+` | the boolean vocabulary | `true` | The set-algebra context-scoped retrieval. `0` routes every match through the reference nested fan-out instead. |
| `VAELII_PLAN` | `test/vaelii/test_util.clj:60+` | the boolean vocabulary | `true` | The conjunctive planner's cost ranking. `0` runs a conjunction's generators in the order they were written, so the whole suite answers unranked; the readiness discipline is not behind it and runs either way. |
| `VAELII_QUERY_ENGINE` | `test/vaelii/test_util.clj:50+` | `dfs` `inference` `hybrid` | unset | Runs every `prove` on the engine named rather than the goal-stack DFS. |
| `VAELII_QUERY_STRATEGY` | `test/vaelii/test_util.clj:60+` | a tactician `tactics/tacticians` names, such as `breadth-first` | unset | Which tactician orders the node engine's goals. Only meaningful beside the row above. |
| `VAELII_CLINGO_LIB` | `project.clj:80+` | a directory holding `libclingo` | `/opt/homebrew/lib` | What the `+with-clingo` profile points `jna.library.path` at. |
| `VAELII_COLOR` | `scripts/gate.sh:110+` | `always` `never` | unset | Whether `lein gate` and `lein lint` colour their output; unset asks the terminal. |
| `VAELII_GATE_OUT` | `scripts/test-parallel.sh:40+` | a directory | `target/gate` | Where the parallel test stage writes its per-shard logs. `lein gate` sets it to that run's own directory, so the shard logs land beside the stage logs rather than in a directory two gates share. |
| `VAELII_GATE_TIMINGS` | `scripts/test-parallel.sh:40+` | a file | `target/gate/test-timings.tsv` | The per-namespace timings the test stage bin-packs its shards from. **Per checkout, not per run** — they are feedback for the *next* gate, so they sit above the run directory and every run shares them. Inside a per-run directory each gate starts blind and falls back to round-robin sharding, which is slower and silent. |
| `GATE_JOBS` | `scripts/gate.sh:60+` | a whole number | unset | The test stage's shard count. **Unpinned** — see below. |
| `PERF_TOLERANCE` | `scripts/gate.sh:60+` | a multiplier (`1.5`) | unset | Passed through to `lein perf --tolerance`, for a loaded box. **Unpinned.** |
| `TEST_BACKENDS_OUT` | `scripts/test-backends.sh:70+` | a directory | `target/test-backends/run-<pid>` | Where `lein test-backends` writes one log per run; the default is per-run, with `latest` pointing at the newest. **Unpinned.** |
| `TEST_SWEEPS_OUT` | `scripts/test-sweeps.sh:50+` | a directory | `target/test-sweeps` | Where `lein test-sweeps` writes one log per run. **Unpinned.** |
| `SUITE_PROGRESS` | `scripts/lib/suite-marks.sh:40+` | `marks` `lines` `auto` | `auto` | How `lein test-backends` and `lein test-sweeps` report a namespace as it finishes: `marks` is the ✔/✘ rows a terminal animates, `lines` is one named, counted and timed line each — what a log, a pipe or CI gets, since a row of ticks in a file names nothing. `auto` reads the terminal. **Unpinned.** |
| `TEST_MATRIX_OUT` | `scripts/test-matrix.sh:50+` | a directory | `logs/test-matrix/run-<pid>` | Where `lein test-matrix` writes one log per configuration, plus `summary.tsv`; per-run, with `latest` pointing at the newest. Under `logs/` (gitignored), not `target/`, so a concurrent `lein clean` cannot delete a live run; old run dirs are pruned to the last `MATRIX_KEEP_RUNS` (20), sparing any touched in the last 24h. **Unpinned.** |
| `MATRIX_JOBS` | `scripts/test-matrix.sh:50+` | a whole number | performance cores − 2, less the vaelii JVMs already running (`scripts/lib/slots.sh`) | How many of the thirteen configurations run at once. One run is about one core of test work, so more slots than cores buys nothing and costs a JVM each. **Unpinned.** |
| `TEST_MATRIX_SEED` | `scripts/test-matrix.sh:50+` | a whole number | a fresh one per run | The seed the launch order is shuffled with. `lein test-matrix` shuffles by default, so a run stopped early — by `--fail-fast`, by ^C, by the box — has covered a random subset of the roster rather than the same prefix every time; the seed is printed with the header and again with the verdict, and giving it back runs that order again. `--ordered` ignores it and schedules the longest configuration first instead, which is ~1 minute faster over the routine roster. **Unpinned.** |
| `MATRIX_JVM_OPTS` | `scripts/test-matrix.sh:50+` | JVM flags | unset | Extra `JVM_OPTS` for every configuration. `-XX:ActiveProcessorCount=2` is the one worth measuring on a loaded box — each JVM otherwise sizes its GC and JIT pools from every core while doing one core of work. It lands in each configuration's log header (`# env … lein test …`, under the revision stamp), so a run stays reproducible by copying that line. **Unpinned.** |
| `MATRIX_HEARTBEAT` | `scripts/test-matrix.sh:50+` | seconds; `0` disables | `60` | How often `lein test-matrix` prints how far each running configuration has got. Thirteen interleaved per-namespace streams are not readable, so this is what replaces them. **Unpinned.** |

Those nine are the names the contract test does not freeze, and the reason is what a
regex can tell apart: `${VAELII_…}` in a shell script is name-shaped enough for one
pattern, and `${GATE_JOBS}` is indistinguishable from every local variable the script
has. Nine names outside the net, named as such, is a better trade than a test that
parses shell. The scripts also honour `NO_COLOR`, `CI` and `TERM` — conventions, read as
inputs to the colour decision and not knobs of this project's.

### Bench

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_BENCH_STORE` | `bench/vaelii/bench/survey.clj:360+` | a directory holding a record log | `~/.vaelii/kbs/store` | The corpus the real-corpus benchmarks sample when the command line names none. |
| `VAELII_SURVEY_STORE` | `bench/vaelii/bench/survey.clj:20+` | a directory holding a record log | as above | A second name for the same directory, read when the row above is unset. |
| `VAELII_PYRAMID_CORPUS` | `bench/vaelii/bench/pyramid.clj:20+` | a directory holding `vaelii.txt` | none — a run without it is refused, naming itself | The join.1k corpus the pyramid benchmark reads. It is a field-harness artifact and is not in this repo, so a default could only name whoever wrote one. |
| `VAELII_RECOVER_CORPUS` | `bench/vaelii/bench/recoverphase.clj:570+` | a directory holding a `:disk` store of sentexes | none — a store-reading run without it is refused, naming itself | The corpus the recover benchmark's store-reading modes read when the command line names no path. A dev-box `:disk` store, not in this repo, so a default could only name whoever wrote one. |
| `vaelii.memo.budget` | `bench/vaelii/bench/recoverphase.clj:90+` | a whole number of distinct visibility sets | `8192` | The `*scoped-memo-budget*` the recover benchmark binds while it recovers, so the scoped-closure cache the phase runs under is a knob rather than the code's steady-state constant. |

## Not here

There is no **read replica** — no way to tail a change log and re-derive belief on
another node. That would need a changelog or event-sourcing layer, and the engine has
none: a durable store records the records, not the sequence of edits that produced
them. The change feed is not that and does not become it: an event names the belief one
settle moved, in `preview`'s entry shapes, and a reader that missed events is told it
missed them rather than handed what it would need to reconstruct them.

There is no **server-sent-events route and no websocket**. The feed crosses the wire as a
long poll ([feed.md](feed.md)), which keeps one endpoint, one content type and one thing
to authenticate; a streaming transport is a second protocol with a second entry point on it, and
the latency it would buy over a parked `POST /op` is the round trip the poll already
saves.

There is no **per-caller identity**. The bearer token is one shared credential for the
process, so the daemon can say that a request is authorised and cannot say by whom —
which is why `:watchers` lists every subscription rather than the asking caller's, and
why the subscription ceiling is per daemon rather than per client. Per-caller identity is
a reverse proxy's job, and this is the check that has to exist below it.
