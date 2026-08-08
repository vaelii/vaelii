# Operational surface

- **Covers:** the five interfaces that drive a KB — CLI, daemon, client, access facade
  and the browser's launch path — the single-writer contract across them, and every
  environment variable or system property with where it is read.
- **Not here:** the browser's own pages, panels and editing UI → [web.md](web.md); which
  KB a process has loaded, and how one is found → [catalog.md](catalog.md).
- **Assumes:** sentex, context, handle → [glossary.md](glossary.md).

`vaelii.core` is the engine; the operational surface is the set of in-repo interfaces
that *drive* it. There are five:

| Interface | Namespace | Launch | For |
|-----------|-----------|--------|-----|
| Browser | `vaelii.web` | `lein run -m vaelii.web` | reading a KB in a browser |
| CLI | `vaelii.cli` | `lein cli <cmd> …` | driving a KB from a shell |
| Daemon | `vaelii.serve` | `lein serve [port [dir]]` | one process owns a KB, serves it over HTTP |
| Client | `vaelii.client` | *(library)* | talking to a daemon from Clojure |
| Access | `vaelii.impl.access` | *(library)* | a read that resolves to a local KB or a remote daemon |

All five go through `vaelii.core` alone — the same boundary the rest of the repo keeps
([api.md](api.md)). None of them is a separate repo: the
engine does its own storage (the `:disk` backend), so an interface is an in-repo
namespace, not a sibling.

## The single-writer contract

The store allows **one writer per directory** (docs/storage.md); the `:disk` backend
enforces it with a fail-fast file lock. That shapes how the interfaces coexist:

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
lein cli assert  '(dog Muffet)' NaturalWorldContext --dir /var/lib/vaelii
lein cli match   '(dog ?x)'   NaturalWorldContext --dir /var/lib/vaelii   # => [(dog Muffet)]
lein cli why     3                                --dir /var/lib/vaelii
lein cli export  /var/backups/vaelii-2026-07     --dir /var/lib/vaelii     # back it up
lein cli repl --starter                                                    # interactive
```

- **Commands:** `assert`, `assert-rule`, `match` (`sentexes-matching`, sentences only),
  `query`, `query?`, `ask`, `prove`, `provable?`, `retract`, `why`, `why-not`, `in`,
  `isa`, `types-of`, `handle-of`, `types`, `contexts`, `conflicts`, `contradictions`,
  `load`, `export`, `repl`. `--depth n` is how the line says how far to expand rules,
  and `query` without one expands none. A sentence is
  written as an EDN string (`'(dog Muffet)'`), a context as a symbol, a handle as an
  integer, and a path as itself — an argument that reads as no EDN form is kept as the
  string it already was, which is what `/var/lib/vaelii` is.
- **`load <file>`** reads an EDN vector of `[sentence context]` (or `[sentence context
  opts]`) entries and asserts them in one batch (`with-deferred-settle` — one settle for
  the whole file).
- **`export <dir>`** writes the KB out as a portable dump (`vaelii.core/export!`) and
  prints the writer's summary. `--variant
  records|records+index`, `--compression gzip|xz|none`. The destination must be empty or
  absent; a refusal is printed as `error: …` in the engine's own words, with a non-zero
  exit status — the same message the daemon and the browser report, because none of them
  writes one of its own.
- **Options:** `--dir <path>` selects the durable backend (recovered on open, so it
  persists across invocations); `--memory` says the ephemeral default out loud — and
  contradicts `--dir`, so naming both is refused; `--starter` loads the shipped schema
  so you can explore the ontology; `--strength monotonic` marks an `assert`
  known-true. A flag outside the roster, or one missing its value, is one line and
  exit 1.
- **`repl`** holds the KB in-process, so a memory KB accumulates for the session. Each
  line is `<cmd> <edn-forms…>`.

`dispatch` takes args already parsed to data, so the shell (which `edn`-reads each argv
string) and the REPL (which reads forms off the line) share one command table.

## Daemon — `vaelii.serve`

```sh
lein serve 4200 /var/lib/vaelii                             # disk-backed; omit the dir for in-memory
VAELII_API_TOKEN=… lein serve 4200 /var/lib/vaelii --listen 0.0.0.0   # off-machine (opt-in)
```

- **It binds loopback**, and exposing it is an explicit choice. `POST /op` is the write
  route of the *single writer*, so the default answers only the machine it runs on — the
  same rule the browser holds to ([web.md](web.md)), and the more consequential of the
  two, since the browser edits a KB where this one *is* the KB's only writer. Jetty binds
  every interface when no host is given, so this is a host the daemon passes rather than
  one it omits.
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
  and the remaining args, and no client can reach an arbitrary var.
- **`POST /op` requires `Content-Type: application/edn`** — parameters and case are
  tolerated (`application/edn;charset=utf-8` passes), anything else is refused with 415
  in the same `{:ok false :error … :type …}` shape every refusal carries. The
  requirement is a CSRF guard rather than a parsing one: the type is not CORS-simple,
  so a browser must preflight it, and the daemon answers no CORS headers — which stops
  a page the operator merely visits from driving the write route over loopback. A
  request stamping another site's `Origin` (or `Referer`) is refused with 403, the
  second layer on the same door.
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
  (`:id :vaelii.impl.serve/open-hosts`), and the `vaelii daemon listening` line's
  `:hosts` — `:allowlisted` or `:open` — is the one to grep for afterwards, beside
  `:auth`.
- **A body over 16 MiB is refused** with 413 before it reaches the heap. An op body is a
  sentence and its context, so the ceiling is nowhere near a legitimate call — it is
  there so a caller who reaches the port cannot spend the daemon's heap by streaming one.
  The cap and its `VAELII_MAX_BODY_BYTES` override are `vaelii.impl.guard`'s
  (`max-body-bytes`, `wrap-body-limit`), not this namespace's, because the browser has
  the same exposure through a form body and reads the same number — one ceiling, two
  servers ([web.md](web.md)).
- **A read is realized under the write monitor.** Projecting the answer for the wire is
  what realizes a lazy result, so it runs *inside* the lock the daemon serializes ops
  with; run after it, a `:query` could straddle a concurrent `:assert` and report a
  KB that never existed.
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
- **Export runs on the daemon's host** (`:export`). It is a write to the *filesystem*
  rather than to the KB, and the directory it names is resolved where the daemon runs —
  the only place it can be, since the daemon owns the KB and there is no stream to hand a
  client back. Two consequences worth stating: it reports **no progress** (`:on-progress`
  is a function, and functions do not cross an EDN wire), and it runs under the write
  monitor, because the walk fetches record by record and a dump of a KB something is
  asserting into is a dump of no single state. There is no `:import` op — `import!` is
  a local operation, run in the process that owns the (empty) KB the dump lands in.
- `serve/app` is a pure `request -> response` handler (reitit-ring), so it is tested
  without a socket; `serve/start` runs it on jetty and returns the `Server`.

## Client — `vaelii.client`

```clojure
(require '[vaelii.client :as c])
(def conn (c/client "localhost" 4200))
(c/assert conn '(dog Muffet) 'NaturalWorldContext)    ; => 1
(c/query  conn '(dog ?x)   'NaturalWorldContext)    ; => ({?x Muffet})
(c/ask?   conn '(animal Muffet) 'NaturalWorldContext)
(c/why    conn 1)
```

- A thin client over JDK `java.net.http` — **no dependency** (JDK 21 ships it).
- **Every call threads an explicit connection handle first** — `(query conn goal ctx)` —
  the network mirror of `vaelii.core`'s explicit-`kb` API. `client` returns a `conn`
  holding a reusable `HttpClient`; no socket opens until a call.
- **The `conn` carries the bearer token**, and every call sets one more header on the
  request it was already building. `(client "localhost" 4200 {:token "…"})` names it;
  omit the key and it is `VAELII_API_TOKEN`, the same variable the daemon reads, so a
  client and a daemon in one environment agree with nothing configured. An explicit
  `{:token nil}` sends no `Authorization` header, which is what an open daemon wants. A
  call with no token to a daemon that requires one throws the daemon's own
  `:unauthorized`, like any other remote refusal.
- A daemon `{:ok false}` reply becomes an `ex-info` carrying its `:error` and `:type`,
  so a remote naming / disjointness refusal reads like a local one. The client mints
  two `:type`s of its own, for what the wire hands it that the daemon never typed:
  `:daemon-error` (an `{:ok false}` with no usable `:type` — the fallback holds even
  against `:type nil`) and `:bad-reply` (a reply that does not read as EDN, or reads
  as something other than a map — a proxy's HTML error page, a truncated body).
- The convenience wrappers (`assert`, `assert-rule`, `sentexes-matching`, `ask`, `prove`,
  `why`, `retract!`, …) mirror the `vaelii.core` surface, bare and `!`-marked exactly as
  it spells them; `call` reaches any allowlisted op directly.

## Browsing a live daemon — `vaelii.impl.access`

The browser (`vaelii.web`) reaches a KB through the `vaelii.core` surface alone. That
surface is re-exported by `vaelii.impl.access` as a facade whose every op takes a
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
image builds from a clean clone. `clojure.main -m vaelii.impl.serve` is the entry point
rather than `java -jar`, because the jar's Main-Class is `vaelii.core`.

- **A token is not optional here.** The container binds an address so that a published
  port can reach it, and `vaelii.serve` refuses that bind with no `VAELII_API_TOKEN`,
  exiting 2 before it opens the KB. `docker-compose.yml` declares the variable required,
  so the failure is a message at `up` rather than a daemon that starts unauthenticated.
  The port is published to host loopback: the daemon authenticates, and putting an
  authenticated writer on a public interface stays a deliberate act.
- **One container per volume.** The `:disk` backend takes an exclusive lock on open and
  refuses a second opener with `:disk-locked`, which is uncaught — so a second container
  over one volume dies at startup rather than corrupting the store. A `replicas:` count
  is a configuration error, not throughput, which is why the compose file has none.
- **The heap is the operator's.** No `-Xmx` is baked in; a JVM in a container reads the
  cgroup limit, so `--memory` is the ceiling. No collector flag is set either, and that
  is measured rather than skipped. `lein perf`, two alternating passes at a fixed 6 GiB
  heap, 2026-08-06: the JDK default took **40.7-41.2 s at 1493-1510 MB** peak resident,
  generational ZGC **55.5-55.9 s at 6224-6258 MB** — 36% slower holding 4.2x the resident
  set, and ZGC alone tripped the `:negation-arbitration` growth bound on both passes. A
  concurrent collector earns its throughput cost on a live set of tens of gigabytes, and
  this engine's peak is 1.5 GB; in a container the resident set is also what the memory
  limit is set against. `lein with-profile +zgc` selects it for a JVM that has a reason.
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
(c/assert conn '(dog Muffet) 'NaturalWorldContext)
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
- **It is not an op.** `serve/ops` carries reads and the four writes, all of them about
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
  holds. What the daemon does log is a **500** (`::op-error`, at `:warn`, with the
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
  cache at the first solve. Both now refuse at the same door as everything else. `VAELII_MAX_BODY_BYTES` and `VAELII_LOG_LEVEL` refuse at
  namespace load, each being the root value of a var.
- **The boolean switches share one vocabulary**: `true` `1` `on` `yes` and `false` `0`
  `off` `no`, case-insensitively, and nothing else. A blank value is *unset* — an
  exported-but-empty variable is the shell's way of saying nothing.
- **A property and a variable spelling of one switch are one switch**, and the table says
  which is read first. Nothing here is named both ways by accident: a JVM cannot set its
  own environment, so the property twin is what a test and an embedded process use.

The names themselves are frozen: `config_surface_test` collects them from the sources and
pins them against `test/golden/config-surface.edn`, both directions, and checks that every
one has a row below and that every citation resolves to a line that names it. Renaming or
removing one is **Breaking** (CONTRIBUTING §3.8). Three rows are outside that net and say
so where they sit.

### Operator

**The servers.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_API_TOKEN` | `src/vaelii/impl/guard.clj:157` | any string; blank or whitespace-only is unset | unset | The one shared bearer token: with it set every daemon request carries `Authorization: Bearer …` or is answered 401, and a client and an attached browser present it from their own environment. |
| `VAELII_ALLOWED_HOSTS` | `src/vaelii/impl/guard.clj:55` | comma-separated host names | unset | The `Host` headers a server answers, overriding the list the bind address implies. |
| `VAELII_MAX_BODY_BYTES` | `src/vaelii/impl/guard.clj:176` | a positive whole number of bytes | `16777216` (16 MiB) | The request-body ceiling both servers refuse above, with 413. |
| `VAELII_WEB_PORT` | `src/vaelii/impl/web.clj:5308` | a port number | `3000` | The port the browser binds. An unparseable value falls through to the property rather than failing the start. |
| `vaelii.web.port` | `src/vaelii/impl/web.clj:5309` | a port number | `3000` | The same port, read after the variable. |
| `VAELII_DEV` | `src/vaelii/impl/config.clj:245` | the boolean vocabulary | `false` | Whether the browser re-reads its stylesheet per request and serves it uncached. |
| `VAELII_LOG_LEVEL` | `src/vaelii/impl/config.clj:283` | `error` `warn` `info` `debug` `trace`, case-insensitive | unset | The level the engine's own statements print at, installed as the engine loads. Unset installs no backend at all, which is a setting rather than a default. |

**The durable store.** All system properties, all read at `open-kb`.

What the defaults cost, stated once rather than left to be assembled from the rows: on
the default an append is durable **within `vaelii.disk.sync-ms`**, so a machine that
loses power or a JVM killed outright drops up to three seconds of acknowledged writes.
A clean exit drops nothing — `close!` and the shutdown hook flush — so the window is a
crash window and not a shutdown one. `vaelii.disk.fsync=dsync` closes it and makes every
append durable when it returns, which is the trade a store of record wants and most of a
common-sense KB does not. The other defaults are off because *on* is the choice that
costs something a KB cannot give back for free: `tokens` adds a durable ground truth a
store opts into, `compress` spends CPU per frame, and `index.snapshot` publishes an
image that only macOS and Linux can swap.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `vaelii.disk.dir` | `src/vaelii/impl/disk/backend.clj:247` | a directory path | `<java.io.tmpdir>/vaelii-disk` | The base a disk KB's space directory hangs under when no `:dir` names one. |
| `vaelii.disk.fsync` | `src/vaelii/impl/config.clj:166` | `dsync`, or unset | unset | Whether every append is durable when it returns (`dsync`), or durability waits for the tick below. |
| `vaelii.disk.sync-ms` | `src/vaelii/impl/config.clj:200` | a whole number ≥ 0; `0` stops the daemon | `3000` | The durability daemon's tick, in milliseconds. |
| `vaelii.disk.auto-compact` | `src/vaelii/impl/config.clj:159` | the boolean vocabulary | `true` | Whether background and opportunistic compaction runs at all — one knob for the tick and the close path. |
| `vaelii.disk.compact-dead-ratio` | `src/vaelii/impl/config.clj:207` | a number from 0 to 1 | `0.5` | The dead fraction a log must reach before compacting it is worth the write. |
| `vaelii.disk.compact-min-interval-ms` | `src/vaelii/impl/config.clj:213` | a whole number ≥ 0 | `300000` | The floor between two auto-compactions of one backend. |
| `vaelii.disk.compress` | `src/vaelii/impl/config.clj:176` | `zstd` `lz4` `none` `off` `false` | uncompressed | The codec durable frames are written with. |
| `vaelii.disk.tokens` | `src/vaelii/impl/config.clj:186` | the boolean vocabulary | `false` | Whether sentex bodies are written as token ids. Reading is never gated on it — a frame carries its own tag. |
| `vaelii.disk.cache` | `src/vaelii/impl/config.clj:194` | a whole number ≥ 0; `0` disables the cache | `65536` | Hot records held in memory per kind. |
| `vaelii.disk.lock` | `src/vaelii/impl/config.clj:220` | the boolean vocabulary | `true` | Whether the single-writer `FileLock` is taken when a directory opens. Off removes the enforcement and not the contract. |
| `vaelii.index.snapshot` | `src/vaelii/impl/config.clj:226` | the boolean vocabulary | `false` | Whether the mapped index image is written and read. Publishing one is refused on Windows whatever this says. |

**Finding a KB.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_KB_PATH` | `src/vaelii/impl/catalog.clj:252` | `:`-separated directory list | `./kbs` and `~/.vaelii/kbs` | The directories KB discovery walks. |
| `vaelii.kb.path` | `src/vaelii/impl/catalog.clj:252` | as above | as above | The same list, read after the variable. |
| `VAELII_KB_CATALOG` | `src/vaelii/impl/catalog.clj:258` | a file path | `~/.vaelii/catalog.edn` | The file naming KBs that live outside the search path. |
| `vaelii.kb.catalog` | `src/vaelii/impl/catalog.clj:259` | a file path | as above | The same file, read after the variable. |

**What the engine reasons with.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_ARBITRATE_CONSTRAINTS` | `src/vaelii/impl/config.clj:233` | the boolean vocabulary | `false` | Whether the process arbitrates a definitional clash rather than refusing it. A KB naming a `:constraints` policy overrides it. |
| `VAELII_ASSERTIVE_ARG_TYPES` | `src/vaelii/impl/config.clj:239` | the boolean vocabulary | `false` | Whether the argument constraints entail types as well as constrain them ([argtypes.md](argtypes.md)). |
| `VAELII_ASP_SOLVER` | `src/vaelii/impl/config.clj:261` | `clingo` `clasp` | unset | Which ASP backend solves. Unset is auto: in-process clingo when it loads, else clasp. A name outside the roster is refused rather than read as auto. |
| `vaelii.asp.solver` | `src/vaelii/impl/config.clj:260` | `clingo` `clasp` | unset | The same choice, and it is read **first**. |
| `VAELII_CLINGO_MAX_BYTES` | `src/vaelii/impl/config.clj:267` | a whole number of bytes, 0 or more | `3000` | The program size above which auto mode routes a plain-ASP program to clasp even where clingo loads. |
| `vaelii.clingo.lib` | `src/vaelii/impl/asp/clingo.clj:29` | a library name or an absolute path | `clingo`, resolved through `jna.library.path` | Which libclingo the in-process bridge loads. |

**The model host.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_LLM_PROVIDER` | `src/vaelii/impl/llm/provider.clj:42` | `ollama` `anthropic` | unset | Which backend the LLM pipeline calls. |
| `vaelii.llm.provider` | `src/vaelii/impl/llm/provider.clj:41` | `ollama` `anthropic` | unset | The same choice, read **first**. |
| `VAELII_OLLAMA_HOST` | `src/vaelii/impl/llm/ollama.clj:127` | a base URL | `http://localhost:11434` | Where the Ollama backend connects. |
| `VAELII_OLLAMA_MODEL` | `src/vaelii/impl/llm/ollama.clj:135` | a model name | `phi4:14b` | The model a turn runs. |
| `VAELII_OLLAMA_GENERATION_MODEL` | `src/vaelii/impl/llm/ollama.clj:141` | a model name | `qwen3-coder:30b` | The model the page-generation path runs. |
| `VAELII_OLLAMA_NUM_CTX` | `src/vaelii/impl/llm/ollama.clj:148` | a whole number of tokens | `8192` | The context window a request asks for. An unparseable value reads as the default. |
| `VAELII_OLLAMA_KEEP_ALIVE` | `src/vaelii/impl/llm/ollama.clj:156` | an Ollama duration (`30m`, `0`) | `30m` | How long the host is asked to hold the model resident after a turn. |

**Read, not ours.** Four names another project defines and the engine reads. An operator
still sets them, and a rename by Anthropic or Ollama is their change rather than a break
here.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `OLLAMA_HOST` | `src/vaelii/impl/llm/ollama.clj:128` | a base URL; a bind address (`0.0.0.0`, `::`, `*`) is ignored | unset | Ollama's own variable, read after `VAELII_OLLAMA_HOST`. A host binds `0.0.0.0`; nothing connects to it. |
| `ANTHROPIC_API_KEY` | `src/vaelii/impl/llm/anthropic.clj:83` | an API key | unset | The credential sent as `x-api-key`, tried first. |
| `ANTHROPIC_AUTH_TOKEN` | `src/vaelii/impl/llm/anthropic.clj:85` | a bearer token | unset | The credential sent as `Authorization: Bearer`, tried when there is no key. |
| `ANTHROPIC_BASE_URL` | `src/vaelii/impl/llm/anthropic.clj:323` | a base URL | `https://api.anthropic.com` | The host that backend calls. |

**The build stamp.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `vaelii.build` | `src/vaelii/impl/io/export.clj:241` | any label | the git HEAD, else `dev` | How the writing build names itself in a dump's `meta.edn`. Diagnostic: a dump that will not read is first a question about which build wrote it. |
| `VAELII_BUILD` | `src/vaelii/impl/io/export.clj:241` | any label | as above | The same label, read after the property. |

### Developer — the suite and the scripts

CI sets these too; nothing in a deployment does.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_TEST_BACKEND` | `test/vaelii/test_util.clj:150` | a `<records>-<index>` backend name (`memory`, `disk`, `memory-columnar`, …), or `overlay` | `memory` | Which of the eight stores the whole suite runs on. |
| `VAELII_TEST_TMS` | `test/vaelii/test_util.clj:159` | `reference` `dense` | `reference` | Which truth-maintenance representation the suite runs on. |
| `VAELII_TEST_SPACE` | `test/vaelii/test_util.clj:124` | a whole number from 5 to 15 | `15` | The top of the two-space block the suite's KBs live on, so two runs can have distinct directories. |
| `VAELII_TEST_LOG_LEVEL` | `project.clj:152` | `error` `warn` `info` `debug` `trace` | `error` | The floor the `:test` profile installs the engine's logging at, through `set-log-level` itself. |
| `VAELII_LLM_LIVE` | `test/vaelii/test_util.clj:208` | `1` `true` `yes` | unset | The consent to call a real model. The `^:llm` mark is the separate half, and both are needed. |
| `VAELII_RETE` | `test/vaelii/test_util.clj:47` | the boolean vocabulary | `false` | Runs the suite's forward chaining through the incremental matcher instead of the reference. |
| `VAELII_HIER` | `test/vaelii/test_util.clj:105` | the boolean vocabulary | `true` | The set-algebra context-scoped retrieval. `0` routes every match through the reference nested fan-out instead. |
| `VAELII_QUERY_ENGINE` | `test/vaelii/test_util.clj:64` | `dfs` `inference` `hybrid` | unset | Runs every `prove` on the engine named rather than the goal-stack DFS. |
| `VAELII_QUERY_STRATEGY` | `test/vaelii/test_util.clj:93` | a tactician `tactics/tacticians` names, such as `breadth-first` | unset | Which tactician orders the node engine's goals. Only meaningful beside the row above. |
| `VAELII_CLINGO_LIB` | `project.clj:87` | a directory holding `libclingo` | `/opt/homebrew/lib` | What the `+with-clingo` profile points `jna.library.path` at. |
| `VAELII_COLOR` | `scripts/gate.sh:104` | `always` `never` | unset | Whether `lein gate` and `lein lint` colour their output; unset asks the terminal. |
| `VAELII_GATE_OUT` | `scripts/test-parallel.sh:37` | a directory | `target/gate` | Where the parallel test stage writes its per-shard logs. |
| `GATE_JOBS` | `scripts/gate.sh:79` | a whole number | unset | The test stage's shard count. **Unpinned** — see below. |
| `PERF_TOLERANCE` | `scripts/gate.sh:203` | a multiplier (`1.5`) | unset | Passed through to `lein perf --tolerance`, for a loaded box. **Unpinned.** |
| `TEST_BACKENDS_OUT` | `scripts/test-backends.sh:125` | a directory | `target/test-backends` | Where `lein test-backends` writes one log per run. **Unpinned.** |

Those three are the names the contract test does not freeze, and the reason is what a
regex can tell apart: `${VAELII_…}` in a shell script is name-shaped enough for one
pattern, and `${GATE_JOBS}` is indistinguishable from every local variable the script
has. Three names outside the net, named as such, is a better trade than a test that
parses shell. The scripts also honour `NO_COLOR`, `CI` and `TERM` — conventions, read as
inputs to the colour decision and not knobs of this project's.

### Bench

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_BENCH_STORE` | `bench/vaelii/bench/survey.clj:372` | a directory holding a record log | `~/.vaelii/kbs/store` | The corpus the real-corpus benchmarks sample when the command line names none. |
| `VAELII_SURVEY_STORE` | `bench/vaelii/bench/survey.clj:373` | a directory holding a record log | as above | A second name for the same directory, read when the row above is unset. |
| `VAELII_PYRAMID_CORPUS` | `bench/vaelii/bench/pyramid.clj:52` | a directory holding `vaelii.txt` | none — a run without it is refused, naming itself | The join.1k corpus the pyramid benchmark reads. It is a field-harness artifact and is not in this repo, so a default could only name whoever wrote one. |

## Not here

There is no **read replica** — no way to tail a change log and re-derive belief on
another node. That would need a changelog or event-sourcing layer, and the engine has
none: a durable store records the records, not the sequence of edits that produced
them.

The **change feed** ([feed.md](feed.md)) is the in-process half of the same idea:
`watch` calls a listener with the belief every settle moved. It does not
cross the daemon, and deliberately — this surface is request/response, a listener is a
function in the writer's own process, and `read-ops` is an allowlist of questions with
answers. Pushing a feed to a remote client needs a transport that can hold a connection
open, which is a decision about the daemon rather than about the feed. So a KB behind
`serve` has exactly the polling an in-process caller no longer needs.
