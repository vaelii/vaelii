# Operational surface

- **Covers:** the five surfaces that drive a KB — CLI, daemon, client, access facade
  and the browser's launch path — the single-writer contract across them, what to do
  after a crash, the mesh of seats, a seat on a phone-sized host, and every environment
  variable or system property with where it is read.
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
  writable KB and give the CLI its own. `diff` and `upgrade` are the two commands that
  open no KB of the run's, so `diff` answers beside a daemon holding `--dir`. A command
  closes the KB it opened before it returns, refused or not, so a process that calls
  `vaelii.cli/-main` holds the lock only while the command runs.
- **Every open writes the lock file first**, reads included, so the directory must be
  writable by the process opening it. A directory that cannot hold the file is refused
  by name before the lock is tried: `:not-a-directory` when the path, or a part of it
  above, is a regular file, and `:not-writable` when the process cannot create files
  there, naming the user it runs as. The OS's own words name `.vaelii.lock`, a file the
  operator never typed, so neither refusal repeats them as its subject. A filesystem that
  answers the lock request with an I/O error, as one with no POSIX advisory locks does, is
  refused with `:lock-unsupported`, naming the directory and the OS's reason.
- An in-memory KB (no `--dir`) has no lock and no persistence — fine for a REPL session
  or a one-shot check, useless for one-shot commands that expect earlier facts.
- A **seat** (koinii's independent-seat layout) is a fork over two directories: the base,
  which each `pull!` replaces with the pulled commit, and the fork's own half, which holds
  the seat's writes ([koinii.md](koinii.md#the-other-deployment-shape-independent-seats)).
  The process that opens the seat holds both locks, the base's until the JVM exits, and a
  pull writes both directories on the writer's thread
  ([overlay.md](overlay.md#replacing-the-base)).

## After a crash

A process that ended without `close!` (killed, out of memory, a machine crash) leaves its
directory for the next open to repair. Open it again with the options it was opened with,
and delete nothing in it: the open truncates torn log tails, tombstones slots past the end
of their log, and checks the index against the records
([storage.md](storage.md#the-on-disk-backend-disk)). The OS lock dies with the process, so
a `:disk-locked` refusal names a process that is still running.

- **Without `:oplog?`**, the open rebuilds the index and belief from the records, which
  is the `reindex` and `recover` the backend otherwise skips. A machine crash loses the
  writes after the durability daemon's last fsync (`vaelii.disk.sync-ms`); a killed
  process loses none, since the page cache keeps what it wrote.
- **With `:oplog?`**, the open restores from the last seal and logs at `:info`:
  `restored <dir> from its seal, replaying n operations, in t ms`. Nothing is left to do.
  Under `:oplog? true` a machine crash loses no write whose call returned.
- **A crash inside a seat's pull** (`import!` with `:rebase?`) leaves the seat's writes in
  its own directory, and the next open asserts them again
  ([overlay.md](overlay.md#replacing-the-base)). A crash inside the import of the dump
  leaves the base partly imported, and that open keeps in the marker each write the partial
  base cannot hold: a form naming a record not yet imported, a form refused, and a
  retraction of a sentence the partial base holds no premise of. The open logs them at `:warn`, and pulling
  the commit again restores the base and asserts them over it.
- **A declined restore** logs at `:warn`: `opened <dir> from its records and sealed it in
  t ms: the restore declined, <reason>`. The KB holds what the records hold, and its log
  starts again at a new generation. The reason says which write the log could not
  describe ([storage.md](storage.md#the-operation-log)):

  | reason | what happened | what to do |
  |---|---|---|
  | `[:unusable [:config op]]` | a prover, evaluatable, reasoner or solver was registered | nothing; the next seal clears a reasoner's mark, and a KB that registers any of the others cannot be sealed, so each crash of it rebuilds |
  | `[:unusable [:seal op]]` | the crash came inside `import!`, `clear!`, `recover`, `reindex` or `load-text!`, before its seal | check what that operation stored, and run it again if it did not finish |
  | `[:unusable [:unfreezable op cls]]`, `[:unusable [:listener-write op]]`, `[:unusable [:unlogged-write kind]]` | a write the log could not record ran | nothing; writes from a change-feed listener are the usual source |
  | `[:unusable [:vm-error op cls]]` | a write ran out of heap or stack after its frame was written, and was rolled back | raise `-Xmx` (or `-Xss` for `StackOverflowError`) |
  | `[:unusable [:interrupted op]]`, `[:unusable [:shutdown-abort op]]` | the caller's bound, a nearly full heap or a shutdown stopped a write ([inference.md](inference.md#stopping-a-run)); the write rolled back what it had in flight, except a `forward-chain` under `:on-stop :keep`, which kept what it placed, and `assert-many` and `bulk-assert-facts!`, which kept the sentences before the cut | nothing for the rolled-back write; send it again with a larger bound or none. A later `forward-chain` with no bound reaches what a kept run left unmade |
  | `[:unusable [:damaged-frame offset]]` | a frame inside the log does not decode | check the disk; the records are intact |
  | `[:index r]`, `[:reasoning r]` | the crash came inside a seal, or an image was changed | nothing |
  | `[:diverged …]`, `:extra-records` | a replayed write differs from the record stored at its handle, or a record has no frame | under `:tick` after a machine crash, nothing; otherwise report it, with the directory |

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
  string it already was, which is what `/var/lib/vaelii` is. **One argument is one
  form**: a second in the same argument is refused (`:bad-args`, naming the command)
  rather than dropped, since `assert '(dog Muffet) (cat Felix)' CxWell` otherwise stored
  the dog, printed its handle and exited 0 with nothing said about the cat.
- **A command that answers a set prints it sorted.** `match`, `query` and `ask` answer
  sets, and a set has no order of its own — so an unsorted print was whichever order the
  retrieval enumerated, and two loads of the same knowledge printed it differently, which
  a `diff` of two runs reports as a change in the KB. They are ordered by content key
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
  (`:unknown-source`). Without `--sync` the records are read and never rewritten.
  `scripts/upgrade-kb.sh [KB-DIR...]` runs it once per directory, defaulting to
  `checkouts/kb`, with the heap from `VAELII_HEAP`, and under `+with-postgres` for a
  directory whose records live on a postgres server (`index/records.edn`), as the start
  scripts do. Run it after pulling engine
  changes, so the next open installs belief in about a minute rather than recovering it.
  **`--verify`** moves the image to
  `reasoning.prev/`, recovers and writes a new image, and reports whether the two agree:
  `:labels` compares the believed sets, and `:network` and `:state` compare the files byte
  for byte. **`--trust`** opens as the browser does (`:recover? :trust`): an image written
  under other engine source is kept and reported `:current`, and belief is recovered only
  when the records moved behind the images, as a writer killed before its close leaves
  them. `--trust` with `--verify` is refused. **`--sync`** rewrites the premises naming a
  symbol a release renamed and reports the ones naming a re-meant or retired symbol, under
  `:renames` ([catalog.md](catalog.md#a-releases-renames)). It then brings the shipped
  contexts to what this engine ships, one change at a time (`vaelii.host.sync/sync-each!`,
  [catalog.md](catalog.md#a-loaded-kb-states-this-engines-shipped-contexts)), with a
  progress line per change on stderr, and reports `:sync {:added :removed :forwarded
  :refused}`. It runs after `--verify`'s comparison, so the comparison reads the open's
  image, and `:reasoning` still says what the open did; the close writes a new image for
  the records the sync moved. A store whose belief is still being rebuilt is not synced
  (`:sync {:skipped [...]}`). The sync reads what ships off a scratch load of the whole
  starter, so `--sync` costs a starter load even on a store already in sync. The script
  passes each flag to every directory.
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
- **`diff <a> <b>`** is the one command that reads two KBs and neither of them is the
  run's: both arguments are **text KBs on disk**, each read into an in-RAM KB of its own,
  and what it prints is `{:added :removed :moved :belief-changed}`. It opens no KB for
  `--dir`, and so takes no lock: a daemon owning that directory does not refuse it, and
  `--dir`, `--memory` and `--starter` change nothing it prints. Keyed on
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
  the outside exactly like one that was applied. `text` is the **only** value `--format`
  takes, and any other is refused for that same reason: dropped, `--format texr` wrote the
  dump the flag was there to replace and exited 0. The destination must be empty or
  absent.
- **A refusal is one line on stderr, and it names its class**:
  `error: [:naming] naming invariant: functor warmBlooded …`. The bracket holds the
  refusal's `:type`, the keyword the daemon returns on the wire and the browser renders
  as a chip, so a script branches on it rather than on the prose
  ([troubleshooting.md](troubleshooting.md#i-have-a-type-and-do-not-know-what-it-means)
  lists them all). A throwable carrying no `:type`, such as a missing `load` file's
  `FileNotFoundException`, reads `[:internal-error]`, the daemon's word for the same
  case. The message after the bracket is the engine's own words, the same message the
  daemon and the browser report, because none of them writes one of its own. The exit
  status is 1 for every refusal and 2 for an unknown command word, whose line
  (`[:unknown-command]`) is followed by the command list. stderr is the stream that leaves
  stdout's data parseable when a script redirects it.
- **Options:** `--dir <path>` selects the durable backend (recovered on open, so it
  persists across invocations). The CLI creates the KB's own directory and nothing
  above it: an existing directory, empty or holding a store, opens, and so does an absent
  one under an existing parent, which is how a new KB is made. A `--dir` whose **parent
  does not exist** is refused (`:unknown-source`, the keyword `upgrade` refuses a
  directory holding no store under) and nothing is created, since the store would
  otherwise create the whole path and a mistyped one would answer a read with `[]` at
  exit 0, from an empty store left behind to answer the same way next time. Of the other options, `--memory` says the ephemeral default out loud — and
  contradicts `--dir`, so naming both is refused; `--starter` loads the shipped schema
  so you can explore the ontology; `--strength monotonic` marks an `assert` or
  `assert-rule` known-true — for a rule that is the rule's own defeat class, not the
  class its firings confer (a bare rule already concludes at its weakest antecedent).
  A flag outside the accepted flags, one missing its value, or one whose "value"
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
- **stdout is the answer and nothing else.** The refusal is not the only thing that would
  otherwise land in it: the engine logs through a console backend, which prints to
  `*out*`, at `:info` when nothing is set — so an ordinary
  `export` (`::exported`) or a `--starter` load (`::dropped-conclusion`) put lines inside
  the answer with nothing set at all. `-main` installs a wrapper that writes the engine's
  log lines to **stderr** for the CLI process, the servers keeping theirs where they are.
  A script redirecting stdout gets the command's value; one wanting the lines too reads
  stderr, or turns the dial down (`VAELII_LOG_LEVEL=error`).

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
  exits **2** before it opens a KB. The code is distinct from the exit 1 of a configuration typo
  (a flag without its value, a non-numeric port), so a supervisor can tell a missing
  credential from a mistyped line. `lein run -m vaelii.web --listen 0.0.0.0` is refused
  on the same terms and, with the token set, answers **401** to a request that does not
  carry it — the browser's write routes include two (`/kbs/export`, `/kbs/load`) that
  write the host filesystem, and both servers' `/op :export` writes it too, at a path the
  request names only when `VAELII_REQUEST_PATHS` is on. A **loopback** bind is
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
- **A token table gives each caller its own token and write boundary.** With
  `VAELII_TOKEN_TABLE` set, the shared token is unread, every token the table holds
  authenticates, and a write op lands only in the contexts its grant names
  ([The token table](#the-token-table)).
- **`GET /health` answers without the token**, and it is the only route that does. A
  daemon only its token-holder can probe is one no container orchestrator, load balancer
  or shell script can watch, and `{:ok true}` tells a caller nothing it did not learn by
  connecting.
- **What it binds decides what it requires.** `--listen` naming a **non-loopback**
  address requires `VAELII_API_TOKEN`: without one the daemon prints a line and exits
  **2**, before it opens the KB and takes the directory's writer lock. A caller starting
  either server from code (`vaelii.serve/start`, `vaelii.web/start`) with an address and
  no `:token` is refused the same way, `:unauthorized`, before anything binds. It is the flag
  that publishes `POST /op` *and* the flag that drops the `Host` allowlist, so the
  exposed configuration must not also be the one with the fewest checks. On **loopback**
  — the default, and `--listen 127.0.0.1` said out loud — the token is used when set and
  its absence is a startup warning naming the flag that would require one; an open
  loopback daemon is drivable by every process on the machine. Either way the daemon
  logs which posture it started in, since that is the line to grep for after an incident.
  Put a reverse proxy in front for TLS and rate limiting; the wire is plaintext. The
  origin check reads the scheme from `X-Forwarded-Proto` when a proxy sets one and the
  host from `Host` alone, never `X-Forwarded-Host`: a proxy that rewrites `Host` makes
  every browser write a 403, so pass the browser's `Host` through.
- **Wire format is EDN.** A sentence is a symbol s-expression — `(dog Muffet)`, `?x` —
  which EDN round-trips losslessly; JSON would mangle the symbols. Bodies are read with
  `clojure.edn/read-string`, which has no reader-eval, so an untrusted body cannot run
  code. The daemon and the client write a body with `guard/edn-str`, which releases
  `*print-length*` and `*print-level*`, so a caller's print bound elides no sentence.
- **The protocol is one endpoint.** `POST /op` with `{:op <keyword> :args [...]}` returns
  `{:ok true :result …}` or `{:ok false :error "…" :type <keyword>}`. `GET /health`
  returns `{:ok true}`. The op is looked up in an **allowlist** (`serve/ops`) of
  `vaelii.core` fns — the KB is supplied by the daemon, so the client sends only the op
  and the remaining args, and no client can reach an arbitrary var. Four ops are not in
  that table and are looked up in a second one (`serve/feed-ops`, below);
  `serve/op-names` is the two together, which is the list an `:unknown-op` refusal
  hands back.
- **A handle names a sentex on this daemon's KB only.** Another seat allocates its own
  handles, so a client that forwards a reply names each sentex by its `:sentence` and
  `:context` ([overlay.md](overlay.md#a-handle-stays-in-its-kb)). A sentence in a reply
  keeps each `(sentexHandle n)` as stored, so a meta-sentex's sentence names the daemon's
  target, and its `:digest` digests that target by its content. A body carrying
  `:digests? true` adds `:digest`, the content digest
  ([storage.md](storage.md#content-digests)), to each map in the reply that names a
  sentex: a sentex record, a feed or `preview` entry, a clash report's side. A `client`
  opened with `{:digests? true}` sends it with every call, and a `:digests?` that is not a
  boolean is refused `:bad-args`.
- **`POST /op` requires `Content-Type: application/edn`** — parameters and case are
  tolerated (`application/edn;charset=utf-8` passes), anything else is refused with 415
  in the same `{:ok false :error … :type …}` shape every refusal carries. The
  requirement is a CSRF guard rather than a parsing one: the type is not CORS-simple,
  so a browser must preflight it, and the daemon answers no CORS headers — which stops
  a page the operator merely visits from driving the write route over loopback. A
  request carrying another site's `Origin` (or `Referer`) is refused with 403, the
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
  sizes a served read with are `:max-ms` and `:max-depth`, held under the ceilings
  `VAELII_MAX_QUERY_MS` (**30000**) and `VAELII_MAX_QUERY_DEPTH` (**256**).
  Under it answers; over it is refused **400** with `{:type :over-ceiling}` carrying the
  requested figure and the ceiling, so the next request knows what to name. A read that
  names *no* `:max-ms` is given the ceiling's, because absent there means no clock at all
  — and for the four backward-search entry points that holds even when the request sent no
  option map, since the alternative is an unbounded search on the write monitor. `0` on
  either variable lifts that ceiling. The ceilings hold the search bounds of reads. The
  clock holds ten ops — `:why-not`, `:search-tree`, `:compare-tacticians`, `:ask`, `:ask?`,
  `:prove`, `:provable?`, `:ask-within`, `:prove-within`, `:kb-integrity` — and none of
  them is held to a depth. The depth ceiling holds the four that take no clock: `:query`,
  `:query?`, `:query-status` and `:argue`. `:why` reads no bound. `:kb-integrity` has two more dials,
  `:max-work` and `:max-results`, held the same way under `VAELII_INTEGRITY_MAX_WORK`
  (**10000**) and `VAELII_INTEGRITY_MAX_RESULTS` (**1000**), `0` lifting either, and filled
  with the ceiling when a request omits them or sends no option map, so a served sweep always
  runs under all three ([integrity.md](integrity.md)). Eight writes bound their chaining:
  `:assert`, `:try-assert`, `:assert-many`, `:assert-rule` and `:forward-chain` read
  `:max-depth`, `:max-term-depth` and `:max-derivations`, and `:edit`,
  `:edit-with-consequences` and `:preview` read the same three keys off each batch entry's
  opts. A request may name any of the three at any size, and the run holds the write
  monitor for its whole length; when it names none, only the term-nesting bound of 8 is in
  force. Every one of the eight but `:preview` also reads `:max-ms`. **`VAELII_MAX_WRITE_MS`
  is the write ceiling, off (0) by default.** Once an operator sets it, the six writes
  `serve/write-bounds` names (all but `:forward-chain` and `:preview`) are held to it as
  a read is held to `VAELII_MAX_QUERY_MS`, and a write the clock ends is refused **400**
  `{:type :interrupted}` and rolled back ([inference.md](inference.md#stopping-a-run)).
  `:forward-chain`'s `:max-ms` is a clock no ceiling fills in. `:preview` takes no clock. A search that reaches its clock is **400** `{:type
  :budget-exhausted}` at the four plain entry points, which answer with a solution set or a
  boolean and have no room to say the answer is a prefix; `:ask-within` and
  `:prove-within` return the prefix with a `:status` instead
  ([anytime.md](anytime.md)). **30 seconds is the client's own read timeout**
  (`vaelii.client`, below): every op runs under the single write monitor, so a read still
  running past the point the caller stopped listening is holding every other request
  behind an answer nobody will receive. The ceiling is applied in the op table rather
  than at this route, so every caller dispatching through the table is held to it too.
  [why a refusal and not a clamp](defenses.md#a-search-bound-may-be-lowered-by-a-request-and-not-raised)
- **A read is realized under the write monitor.** Projecting the answer for the wire is
  what realizes a lazy result, so it runs *inside* the lock the daemon serializes ops
  with. [why inside the lock](defenses.md#a-read-that-crosses-the-wire-is-realized-inside-the-write-monitor)
  A read therefore waits for the whole of the op ahead of it: behind one `:assert-many`
  it waits for the whole batch, so a loader sharing the daemon with readers sets their
  wait by the size of the batches it sends. `GET /health` is outside the monitor and
  answers throughout.
- **An op runs on a thread the HTTP server does not own.** The Jetty worker that read the
  request waits for the op's answer and nothing else. Jetty interrupts a busy worker when
  its server stops, and an interrupt during a disk write closes the store's channel and
  latches it `:store-unusable` ([storage.md](storage.md#a-store-that-stops)); the
  interrupt reaches the worker's wait instead. Stopping a daemon `serve/start` returned
  refuses every op that has not entered the write monitor with **503 `:stopping`**,
  answers every parked long poll with the events it has, then waits for the op inside the
  monitor, which answers its caller before the connectors close.
- **An op runs to completion whether or not its caller is still listening.** The daemon
  does not watch the socket: a caller whose read timeout fires, or whose connection
  drops, has abandoned the reply and not the op, which runs, settles and is answered to
  nobody. A request still queued for the monitor when its caller leaves runs too. The
  caller holds a `java.net.http.HttpTimeoutException` (from `vaelii.client`) and nothing
  that says how far the op got, so the one way to learn the outcome is to read the KB —
  `:handle-of` for a sentence, `:sentexes-matching` for a pattern. A re-send is the other
  way, since it queues behind the first and answers after it. Re-sent after the first
  landed, each write answers as follows:

  | Re-sent write | Answers |
  |---|---|
  | `:assert`, `:try-assert`, `:assert-many`, `:assert-rule` | the same handles, and nothing new is stored: a sentence dedups to its canonical form's handle ([canonicalization.md](canonicalization.md)) |
  | `:edit`, `:edit-with-consequences` | with `:add` alone, the same handles; with a `:remove`, refused `:unknown-handle`, and the KB stays as the first send left it |
  | `:retract` | `{:removed-sentexes 0 :removed-justifications 0}` |
  | `:forward-chain` | `{:derived 0}`, the fixpoint being reached |
  | `:add-provenance` | the same merged map |
  | `:abduce-discard` | zero counts |
  | `:export` (under `VAELII_REQUEST_PATHS`) | refused `:not-empty`, and the first dump stands |
  | `:abduce` with `{:keep? true}` | **a second scratch context**, each one discarded through the context its own answer names; without `:keep?` the KB is left as it was found either time |
  | `:watch` | **a second subscription**; the first counts toward the 64 until it has gone five minutes unpolled and a later feed call reaps it |

  The dedup is a property of `assert`, not of the protocol: a request carries no id, and
  the daemon keeps no record of what it answered.
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
  an `:args` that is not a sequence; an arity error raised by a call inside the op is a
  fault of the daemon and answers 500 `:internal-error`), `:unknown-op` (400, with the
  op list in the reply), `:not-found` (404, any route the router does not serve), and
  `:internal-error` (500, the default the catch-all arms fill in when nothing typed
  the failure, so the key is never present with nil in it). Every other `{:ok false}`
  carries whatever `:type` the engine threw — the request-refusal vocabulary
  (`:naming`, `:not-ground`, `:unknown-option`, `:bad-handle`, …) at **400**, since
  it is the caller's mistake, and anything outside that list at 500 — so a client
  discriminates on the one `:type` vocabulary, with the status as the coarse
  client-fault/server-fault split.
- **The feed adds four refusals to that list**, all at 400: `:unknown-subscription`
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
  an unrealized lazy tail or a DFS goal stack, and neither it nor the heap it keeps
  reachable crosses an EDN wire — the same wall `:export`'s `:on-progress` hits. So the daemon answers
  `:results`, `:status`, `:count` and `:elapsed-ms` as ever, and replaces `:resume` with
  **`:resumable`**, a boolean: the search had more to give. **`core/resume` is in-process
  only.** A remote caller continues by asking again under a larger budget — a bounded run
  is a strict prefix of the unbounded one, so the larger call is a superset rather than a
  second answer ([anytime.md](anytime.md)). The boolean is there rather than the key
  simply omitted, because the documented `(when (:resume r) …)` loop would otherwise read
  every partial as complete and stop one step in.
- **The knowledge readings are served** (`:kb-quality`, `:kb-integrity`,
  `:quality-report`, `:argue`, `:vocabulary-audit`, `:settle-stats`, `:provenance`,
  `:add-provenance`). `:kb-integrity` takes its finite candidate set over the wire as an
  EDN set ([integrity.md](integrity.md)).
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
  `:contexts-of`, `:canonical-sentex`, `:digest`, `:digests`). `:handles` answers a **sorted vector**: the
  handle set a store hands back is a `java.util.Set` that is deliberately not an
  `IPersistentSet` at scale ([storage.md](storage.md)) and has no EDN print form, and
  sorting it means two daemons over one store answer the same bytes.
  `:canonical-sentex` is the content identity of a sentence that was never stored, which
  is the read behind content-addressing one ([canonicalization.md](canonicalization.md)).
  `:digest` and `:digests` read the content digest, the checksum a sentex has in every
  store that holds it ([storage.md](storage.md#content-digests)).
- **Five ops take no KB** — `:levels`, `:calculi`, `:readable-sentence`, `:sentence-of`
  and `:quality-report` (above) — and are in
  the table all the same, because a client that has to *display* a stored rule needs the
  author's variable names put back and cannot compute them from a sentex map alone, and a
  rule map carries no `:sentence`, so `:sentence-of` builds its canonical `implies` form. The
  daemon supplies a KB to every row of `serve/ops`; `serve/kbless-ops` is the list of
  the rows that drop it, held as data because two generators read the table and both have
  to know whether an op's first `vaelii.core` parameter is the KB or an argument.
- **Three reads are for a reader rather than a program** (`:describe`, `:why-not` with
  `{:nearest n}`, `:kb-diff` — [api.md](api.md)). `:describe` matters most over the wire:
  a remote client rendering a term otherwise asks a dozen questions about it and pays a
  round trip for each, and this answers them together. `:why-not` needs no table entry of
  its own for the near-miss option — the op table `apply`s the `vaelii.core` var, so a new
  arity crosses the wire the moment the API grows one. `:kb-diff`'s second side names a
  KB the server serves, since a KB value does not cross an EDN wire: the browser's
  catalog key of another loaded entry, diffed against the active one. A string naming no
  served KB is refused with **403** `:path-not-served` and nothing is read, so a daemon,
  which serves one KB, refuses every wire `:kb-diff`. The server decides which KBs it
  serves, and a request names no path: a path side would load a whole KB per request
  and read any file the process can read, `..` and symlinks included.
  `VAELII_REQUEST_PATHS=1` at the server's start lets a request name a text KB on the
  server's host. The browser's `/kbs/load` and `/kbs/export` refuse a `dir` the same way
  and write under the catalog's `write-root` ([catalog.md](catalog.md#where-the-server-writes)).
  `:export` names a directory on the server's host, so it is refused with **403**
  `:path-not-served` before anything is written unless the switch is on.
- **`:query-status` says whether the depth bound cut an answer.** A query truncated at
  `:max-depth` answers the same empty or short seq as a goal the KB does not entail, and
  over the wire the bound in force is often the daemon's `VAELII_MAX_QUERY_DEPTH` rather
  than the caller's. `:query-status` answers `query`'s answers with `:status`
  (`:complete`, `:truncated`, or `:incomplete` when a transitive goal with both ends open
  answered its extent) and the run's counters, under the same depth ceiling as
  `:query` ([api.md](api.md)).
- **Six reads are served beside a read on the wire that answers the same kind of
  question**: `:find-sentexes-all` beside `:find-sentexes`,
  `:subsumption-status` and `:subsumption-statuses` beside `:genl?` and `:disjoint?`,
  `:functional-at-instant-violations` and `:all-functional-at-instant-violations` beside
  the `predAllSpecified` pair `:specified-violations` and `:all-specified-violations`,
  and `:last-program`, the question the edge solver was last asked, beside `:conflicts`.
- **Export runs on the daemon's host** (`:export`), and only under `VAELII_REQUEST_PATHS`
  (above). It is a write to the *filesystem*
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
- **A `vaelii.core` fn that takes a KB is an op or a row of the table below**, and one
  rule decides which. A fn is an op when four conditions hold:

  1. **The data crosses the wire.** Every argument and the answer are values an EDN body
     carries: no function, no KB value, and no path the daemon would load knowledge
     from.
  2. **The fn acts on the KB, not on the process.** It reads or writes knowledge. The
     process's ownership of the store, its prover registry and the state that opening
     the store left belong to whoever started the process, and the daemon's callers did
     not.
  3. **A write runs every check.** A write goes through the checks
     `assert`, `edit!` and `retract!` run for a local caller, so a remote write is
     refused wherever a local one is. A write that empties a diagnostic record every
     caller reads, and that nothing rebuilds, fails this condition too.
  4. **Something bounds the cost.** A request's own bounds (the ceilings above, a
     required limit) or the size of what the fn reads bounds its cost.

  A fn that fails a condition is a row below, with the condition it fails. A fn whose
  work an op already does under another spelling is a row too, naming that op.
  `serve_parity_test/every-kb-fn-is-an-op-or-a-named-absence` fails on a `vaelii.core`
  fn that takes a KB and is in neither `serve/ops` nor this table, so a fn added to the
  API is decided in the commit that adds it.

  | Not served | Fails | Why |
  |---|---|---|
  | `import!` | 2 | A dump lands in an **empty** KB, in the process that owns it — a daemon is already serving one |
  | `recover` | 2 | It rebuilds the taxonomy and the JTMS from the durable stores at open; a client cannot know the daemon is unrecovered, and a rebuild mid-service moves belief under every other caller |
  | `reindex` | 2 | It does the same for the index, as a whole-store rewrite under the one lock every other request is queued behind |
  | `clear!` | 2 | It destroys the KB the daemon exists to serve, and leaves every client's handles naming nothing |
  | `close!` | 2 | It ends the process's ownership of the store; the socket that asked would be answering from a KB that no longer has one |
  | `seal` | 2 | It writes the images of an operation log `open-kb`'s `:oplog?` attached, and the daemon opens without one; the cadence of seals is the opener's |
  | `write-hazards`, `store-state`, `rebuild-progress` | 2 | Each reads the state that opening the store left. The daemon opens with `open-kb`'s default, `{:recover? :trust}`, so each answers the same value for the whole of its service, and the repair each one names (`recover`, `reindex`, a reload) is a row above. A write into an unrecovered KB is refused `:unrecovered-kb` over the wire as in process |
  | `add-prover`, `add-evaluatable`, `add-reasoner`, `set-solver` | 1, 2 | The prover registry and the edge solver are held in the process's memory. `add-prover` and `add-evaluatable` take a function, and `add-reasoner` and `set-solver` answer the KB value. The daemon registers the reasoners its store records when it opens ([storage.md](storage.md#the-reasoner-set)) |
  | `fork` | 1 | It answers a KB value |
  | `with-deferred-settle` | 1 | It is a macro over a body of forms, and `:assert-many` is the batch a request sends |
  | `watch`, `unwatch`, `watchers` | 1 | `watch` takes a callback. The feed crosses as a subscription with a cursor, `serve/feed-ops` (above) |
  | `load-text!`, `load-foreign!` | 1 | Each reads a path, which over a wire names a file on the daemon's disk while reading like one on the caller's (the export bullet above). Text goes over the CLI |
  | `export-text!` | 1 | It is the other half of `load-text!`, and the two are served together or not at all |
  | `assert-inert` | 3 | It stores past the constraint, wff and equality checks, and never premises what it stores. It is the solve's labeling primitive ([solving.md](solving.md)) |
  | `bulk-assert-facts!` | 3 | It skips the definitional checks and the dedup for a corpus its caller vouches for. `:assert-many` is the checked batch |
  | `clear-violations!`, `reset-settle-stats!` | 3 | Each empties a diagnostic record every caller reads (`:violations`, `:settle-stats`), and nothing rebuilds either one |
  | `record-arg-types` | 2, 4 | It completes a store its opener loaded around `assert`, once, after the load; a daemon serves a KB already loaded. It reads every stored fact of every functor an argument declaration reaches, with no bound a request can set |
  | `record-arg-types!`, `request-stop!`, `arg-types-owed` | 2, 4 | The same pass as `record-arg-types`, run by its opener as a job it can stop and resume, with a callback for its progress and its cancel; `request-stop!` reaches it from another thread. `arg-types-owed` reads what it owes |
  | `release-withheld!` | 2, 4 | It drains what an open or a bulk load left owed, once, at the opener's choice of time. It re-derives the facts naming every term an owed row releases, with no bound a request can set. `:owed-releases` reads the count |
  | `edit-records!`, `settle-record-edits!` | 2, 3 | They edit and then rebuild a KB opened without belief, which a daemon does not serve. `edit-records!` writes with no check, no dependency sweep and no settle; `settle-record-edits!` is the `recover` (and `reindex`) above with a sweep after it ([storage.md](storage.md#editing-the-records-of-a-kb-without-belief)) |
  | `remove-unsupported!`, `mark-inert!` | 2 | Each repairs a record a failed write left, which the open reported, on evidence the opener holds: the handles its own record of its writes marks failed. `:unsupported` reads the report |
  | `disjointness-audit` | 4 | It runs a subsumption read for every pair of the n types, n(n−1)/2 of them, with no bound a request can set. `:subsumption-status` answers one pair |
  | `ist` | — | It is `assert` with its arguments reordered: `:assert` of `(ist Ctx S)` stores the same sentex |
  | `register-modal-predicate` | — | `:assert` of `(modal_predicate pred)` in the context is the same write, and answers a handle where this answers the KB |

  Every row stays reachable in the process that called `open-kb`, and the lifecycle rows
  through the CLI and `vaelii.starter` as well.
- `serve/app` is a pure `request -> response` handler (reitit-ring), so it is tested
  without a socket; `serve/start` runs it on jetty and returns the `Server`.

- **The browser serves the protocol too.** `vaelii.browser.web` answers `GET /health` and
  `POST /op` over its active KB by calling the daemon's handler (`serve/handle-op`), so a
  native client connects to `http://127.0.0.1:3000` as it connects to a daemon. The op
  table, guards, ceilings and refusals are the daemon's. The monitor is the browser's
  `write-monitor`, which the browser's own write routes take, so the browser process stays
  the KB's one writer. Two ops are the browser's own and answer in every state: `:kbs`, the
  catalog (the active key, the heap, and each entry's status, progress, error and live
  stored count), and `:jobs`, the job registry, so a client watches a load from the
  endpoint it will query. Three refusals precede every other op: **404** `:not-found` when the browser
  reads a remote daemon (`--attach`), and **409** `:still-loading` or `:still-exporting`
  while a job writes or an export walks the active KB. The two 409s refuse reads as well,
  because the op table does not mark which ops write. The op then waits for the monitor,
  and `handle-op` asks again once it holds it: a KB `/kbs/unload` released meanwhile
  answers **404** `:not-found` and nothing is written, and a KB an export started walking
  meanwhile answers **409** `:still-exporting`. `:watch` is asked the same question, so no
  subscription is registered on a released KB, and the unload drops the subscriptions
  already on it ([feed.md](feed.md)). The token rule is the browser's:
  a loopback bind asks for none, and `--listen` with an address requires it on every
  route, `GET /health` included ([web.md](web.md)).

### The token table

`VAELII_TOKEN_TABLE` names an EDN file mapping each bearer token to a **grant**:

```clojure
{"<Ava's token>"  {:principal AgentAva :writes #{CxAva}}
 "<Ben's token>"  {:principal AgentBen :writes #{CxBen}}
 "<operator's>"   {:principal AgentOperator :admin? true}}
```

`serve/start` and `serve/app` take the same table as `:token-table`, a map or a path. Set,
it replaces the shared token: a request presents a token the table holds or is answered
**401** `:unauthorized`, exactly as a wrong shared token is, and `VAELII_API_TOKEN` in the
daemon's environment is unread. Each caller presents its own token as `:token` (or its own
`VAELII_API_TOKEN`), so the client needs no change. A table that is not a readable file,
does not read as EDN, names no token, or holds a grant with a key outside the three is
refused at start (`:bad-token-table`, exit **2**), before the KB is opened. A table also
satisfies the rule that `--listen` with an address requires a credential.

**Reads stay open.** Every token in the table reads every context, as the shared token does.

**Nine ops are bounded by the grant**, inside the write monitor, before the op runs
(`serve/write-ops`, `bound-write`) and, for the conclusions a stored sentence fires,
again after the write:

- `:assert`, `:try-assert`, `:assert-rule` and `:assert-many` store each sentence only when
  `:writes` names every context its storage writes (`serve/placements`). `:assert-many`
  reads its sentences from any collection, a set included. The contexts are:
  - the one `assert` stores in (`assert-entry/storage-context`): an `(ist Ctx S)` names its
    own, through a `(set/monotonic …)` wrapper, an omitted context is `CxUniverse`, and a
    `forced_decontextualized_predicate`'s fact is stored in `CxUniverse`;
  - `CxUniverse` beside it for a fact the store also lifts there: a permuting mark, and a
    `decontextualized_predicate`'s fact
    ([contexts.md](contexts.md#decontextualized_predicate-a-fact-that-belongs-to-the-kb-not-to-one-theory));
  - for a `(genlCx Sub Super)` edge, `Sub` as well, since the `genlCx` closure is global and
    the edge widens `Sub`'s ancestor set wherever it is stored;
  - for a rule, its own context and the contexts of every literal its consequent concludes.
    A negated conclusion is the literal `(not …)` and is placed as one. The engine refuses
    every `(ist Ctx S)` consequent with **400**, so no rule concludes into a context through one;
  - for a `defn*` fact and for a fact a stored generator's antecedent matches, the contexts
    of each rule the engine writes for it (`sx/defn-companion-rules`, `serve/generated-rules`),
    read as a rule's. Every stored generator is read, in whatever context it is stated, so
    a `genlCx` edge stored later makes no generator visible that the check skipped. A rule
    is placed as the engine places a firing that climbed the `genl` closure
    (`chain/placements-over`): in the fact's context when that context sees every edge of
    some route from the fact's predicate to the antecedent's, else in the maximal common
    descendants of the fact's context and the contexts of the edges on each route
    (`serve/firing-contexts`). A route whose edges no descendant of the fact's context sees
    places nothing. A fact is matched with its first two arguments exchanged only against an
    antecedent its predicate reaches over an odd number of `genlInverse` edges;
  - for a `genl` or `genlInverse` edge, the contexts of each rule a stored generator writes
    for a stored fact the edge connects to the generator's antecedent, read as a rule's, in
    each context the fact's own check places it in once the edge is stored and did not place
    it in before (`serve/edge-generated-rules`), so the verdict is the same whichever of the
    fact and the edges is written last. A rule concluding an edge with a variable term may
    connect any fact, so each antecedent the edge could reach is read with nothing bound.

  A grant's bound covers the rules its own writes make the engine write at the time of the
  write. A generator or rule an admin grant adds later fires on the facts already stored,
  and its conclusions are the admin's.

  The check above does not predict two placements the engine makes. It leaves the
  generator's own context out of a generated rule's placement, so a generator stated in a
  context the fact's context does not see places the rule in a common descendant the check
  does not read. It judges routes by their contexts alone, where the engine also
  compares each edge's defeat class (`chain/descent-placements`), so a `:monotonic` route
  whose contexts a `:default` route covers places a rule the check does not read.

  **Each sentence is checked again against the conclusions its rule firings stored.** The
  op runs with `assert-entry/*write-check*` bound (`serve/write-check`). Once a sentence is
  stored, chained and settled, every sentex a justification the write added under a rule
  concludes is held to the contexts the check above reads for a literal: its own,
  `CxUniverse` for a fact the store also lifts there, `Sub` for a `(genlCx Sub Super)`
  edge, and an admin grant for a placement declaration. One outside `:writes` refuses the
  sentence with 403 and takes back what it wrote, as a write `:max-derivations` ends is
  taken back ([inference.md](inference.md#stopping-a-run)). So an admin's rule concluding
  a `decontextualized_predicate`'s fact refuses the granted fact that fires it, whether or
  not the conclusion is already stored, and so does a firing placed in a common descendant
  of the grant's context and another. A rule a generator writes is held the same way, in
  the context the engine places it in. A justification under no rule, such as a
  `contradicts` record a clash places, is not read. `:assert-many` keeps the sentences
  stored before the refused one, as it does for any refusal, and `:edit` refuses the batch
  whole.

  Only an admin grant writes a `do/` imperative, a `forced_decontextualized_predicate` or
  `decontextualized_predicate` declaration, or a literal with a variable functor, whether
  as a fact, in a rule's consequent or in a rule the engine writes. A placement declaration
  places every `(P …)` the KB holds, in any context, in `CxUniverse`. A variable functor
  may conclude any predicate. Neither has a context a grant's `:writes` could bound.
- `:edit` and `:edit-with-consequences` hold every `:add` entry to the same check and
  every `:remove` handle to the next one; one entry out of bounds refuses the batch, and
  nothing in it is applied.
- `:retract` removes, and `:add-provenance` annotates, a sentex only when its stored
  context is in `:writes`. `:add-provenance` on a handle naming no stored sentex is
  refused too, since provenance written there first would read as the sentex's own.
- `:export` runs only under an admin grant: it writes the whole KB to a directory on the
  server's host.

A write outside the grant is **403** `:forbidden-context`, carrying `:principal` and
`:context`. `:admin? true` grants every context.

**The daemon records the identity.** Every stored write under a grant gets
`:principal` in its provenance, the grant's principal, and `:creator`, the same principal
unless an admin grant names another (the operator placing an agent's context writes it
as that agent). A request naming a `:creator` other than its principal, in its opts or in
their `:provenance`, or naming any `:principal` but its own, is **403** `:creator-mismatch`.
A daemon with **no** table refuses every request naming the provenance `:principal`, since
it records that key from a grant and never from a request, and the browser's `POST /op`
holds the same rule. `import!` keeps the key, so a backup restored or a store moved through
a dump keeps its principals. `import!`'s `:drop-principal? true` drops the key from every
provenance map the dump carries, and koinii's `deref/pull!` passes it: a peer's principals
were recorded by no daemon of the pulling operator's choosing. So a `:principal` in provenance
names the token that wrote the sentex, and koinii's majority count reads it for that
([koinii.md](koinii.md#identity-and-the-write-boundary)). The provenance merge records the
principal of the last stored write of a sentence, a re-assert included.

The other ops are not bounded by the grant: `:forward-chain` stores what the rules
derive, `:abduce` with `{:keep? true}` stores its hypotheses in a scratch context below
the asking one, and `:abduce-discard` and `:clear-caches` take any token in the table.

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
- **Every refusal carries `:status`**, the HTTP status it came back under, beside the
  `:type` a caller discriminates on. The status is the coarse split described above —
  the caller's mistake at 4xx, the daemon's fault at 5xx — and a client that read the
  body alone could not see it, so a `:type` outside the request-refusal list (500)
  arrived looking exactly like one inside it (400). `:bad-reply` needs it most, being
  the one refusal no `:type` vocabulary covers: a proxy's 502 and a daemon that answered
  200 with a truncated body are two different faults and the status is what tells them
  apart.
- **A `:bad-reply` says nothing about whether a write was applied.** The daemon applies
  the op and then sends the reply, so a write whose reply was truncated or replaced on
  the way back is stored at the daemon although the caller received an exception.
  Before retrying a write after a `:bad-reply`, read whether it landed (`handle-of`).
- **Every op has a wrapper, and the op table is what says so.** A wrapper mirrors the
  `vaelii.core` fn its op runs — bare or `!`-marked exactly as `vaelii.core` spells it,
  never as the op keyword does (the keywords drop the suffix, so `:retract` runs
  `retract!`) — and carries that fn's arities with `kb` replaced by `conn`. Arity for
  arity, because a wrapper short of an arity the daemon accepts is a read a remote caller
  cannot make: `(c/why-not conn s ctx {:nearest 3})` is the only read that names the rules
  that came closest to concluding `s`.

  The claim is **generated rather than maintained**. `lein regen-client`
  (`vaelii.regen-client`) reads `serve/ops`, resolves each op in `vaelii.core` and writes
  the wrappers between two markers in `vaelii.host.client`; `vaelii.client` interns each
  one it does not write out by hand, with its docstring and arglists, so prose written
  for one survives.
  Generated at *build* time rather than macroexpanded from the table, because requiring
  the table would pull the engine, jetty and reitit onto the classpath of a namespace
  whose whole point is not needing them — the client is JDK-only and stays that way.
  `client_surface_test` compares the file against what the generator would write now,
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
  `:edit` op, its assert form to
  `:edit-with-consequences` (which answers with what the batch turned out to mean), and
  its forward-chain trigger to `:forward-chain` — so modifying a KB works against an
  attached daemon too, with the daemon the single writer serializing each one under its
  lock. The write forms are preceded by a `:check-edit` round-trip, so a refusal costs
  a message rather than a half-applied batch.

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
`lein uberjar` runs in a Temurin 25 JDK stage, and what reaches the runtime image is a
Temurin 25 JRE and the jar. The uberjar needs no checkout and no local artifact — every `:dependencies` entry
resolves from a public repository, and so does every `+with-` profile — so the image builds
from a clean clone. The `PROFILES` build argument names the profiles the jar is built with:
`docker build --build-arg PROFILES=+with-postgres,+with-sqlite -t vaelii .` gives an image
that opens `:pg-*` and `:sqlite` KBs ([storage.md](storage.md)), and an empty one builds
the engine alone. The build context excludes `checkouts/`, so an image carries the released
adapters, never a linked source tree. `clojure.main -m vaelii.host.serve` is the entry point
rather than `java -jar`, because the jar's Main-Class is `vaelii.core`. The entry point
also names the flags `project.clj`'s `:jvm-opts` give a JVM that lein launches, since an
uberjar carries no `:jvm-opts`: `--enable-native-access=ALL-UNNAMED` and
`--sun-misc-unsafe-memory-access=allow`, without which JDK 25 warns when JNA loads a native
solver and when nippy's LZ4 compressor calls `sun.misc.Unsafe`, and
`-XX:+UseCompactObjectHeaders`, an 8-byte object header that holds about 8% less heap.

- **The image carries a class-loading cache.** The build runs the daemon once over a
  scratch store until `/health` answers, and the JVM writes what that start loaded to
  `/app/vaelii.aot`, which the entry point reads with `-XX:AOTCache`. A daemon over an
  empty store answers `/health` in 0.58 s with it and 1.61 s without, for about 90 MB of
  image. The cache is valid only for the JVM build and the jar that wrote it, which is
  why it is built in the runtime stage; a JVM that finds it stale logs a warning and starts
  without it.

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
  volume answers in under a second; the start period is far longer than that because
  it is sized for the other case, where a restart over a populated volume runs `recover` —
  one pass over every stored record — before Jetty accepts a connection. That pass is
  O(records), so a store large enough to outlast the start period wants a longer one. The probe
  curls `127.0.0.1`, and `/health` is behind the `Host` check like every route, so a
  `VAELII_ALLOWED_HOSTS` naming only the public host answers it 400 and the container
  reports unhealthy; keep `127.0.0.1` on the list, as the compose file does.
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

## A mesh of seats

The supported multi-machine topology is a mesh of peer seats. Every machine runs the same
vaelii as a seat: a daemon in its own process over a fork of its own copy of the shipped KB
([koinii.md](koinii.md#the-other-deployment-shape-independent-seats)). No seat is special,
and each one publishes its own writes and merges every peer's.

- **A seat starts from its own copy.** Its first open imports the shipped dump as the
  fork's base with `import! {:rebase? true}`. A restart opens the same two directories and
  imports nothing.
- **A seat publishes its writes as a delta** with `export-text! {:delta? true}`, and each
  peer merges the delta with `load-text! {:merge? true}`. The merge reports each form it
  refuses with the refusal's `:type`, and a reference the peer canonicalizes otherwise is
  refused `:canonical-mismatch` ([overlay.md](overlay.md#a-delta)).
- **A seat may take a peer's dump as its base** with `deref/pull!`, which asserts the
  seat's writes again over the new base. A seat killed after the pull imported the dump
  holds its writes again at its next open. One killed inside the import holds the writes
  the partial base can hold, and the next pull asserts the rest
  ([After a crash](#after-a-crash)).
- **Once every seat has merged every peer's delta, the seats believe one set** over the
  shared contexts, when no merge refused a form and no seat retracted a shared premise. A
  delta writes no retraction ([overlay.md](overlay.md#a-delta)). A form one merge refuses
  stays stored at the seats that accepted it: a seat that merges a peer's `except` before
  a third seat's `(symmetric P)` respells its target holds the `except`, and the third seat
  refuses it `:canonical-mismatch`.
- **Compare the sets by `:digest` and `:strength`** (a client opened with `{:digests?
  true}`), not by sentence: a meta-sentex's sentence names its target by the seat's own
  handle ([the daemon](#daemon--vaeliiserve)), and a digest leaves the strength out.

`multi_jvm_test/three-seats-merging-each-others-deltas-believe-one-set-after-each-round`
runs three seat daemons through four rounds, with a clean restart, a kill inside a pull of
a peer's dump and a `:canonical-mismatch` refusal, and compares the believed sets after
each round. Its refused `except` sits in seat A's own context, outside the compared ones,
and the test asserts which seats hold it. `lein test-multi-jvm` runs it.

## A seat on a small host

A phone-sized host, such as an Android phone under Termux or a small ARM virtual machine,
runs a seat as a server does, with a smaller heap and slower storage. No configuration of
the suite has run on Android, Termux or Linux on aarch64, and the suite runs at a 4 GB
heap (`VAELII_TEST_HEAP`). At a 1 GB heap, `_JAVA_OPTIONS=-Xmx1g lein perf --only
membership,recover` passes 24 of its 26 growth checks on a development machine
(2026-10-30, load average about 30). The other two read below its noise floor, which
leaves them unjudged.

- **The heap comes from the host.** The start scripts set `-Xmx` from `VAELII_HEAP`, else
  half the host's physical memory up to `31g`, the largest heap the JVM addresses with
  compressed object pointers (`scripts/lib/start.sh`). They refuse a `VAELII_HEAP` above
  physical memory: the OS kills a JVM whose heap it cannot back before the heap mark at
  92% of the old generation fires ([caches.md](caches.md#the-heap-mark)). A seat started
  from the jar without a start script names `-Xmx` itself. The heap mark rolls back a
  chaining write that a larger heap stores, so two seats fed one stream on different heaps
  can store different knowledge.
- **Run the jar, not `lein`.** A cold start through `lein` compiles the sources before the
  KB opens. `lein uberjar` writes an ahead-of-time compiled standalone jar under `target/`,
  started as the container starts it: `java <flags> -cp <jar> clojure.main -m
  vaelii.host.serve`, with the flags [the container section](#container--the-daemon-as-an-image)
  lists.
- **Open over `:disk-snapshot`, and seed it from a dump that carries a reasoning image.** An
  open that installs the store's reasoning image skips the recover
  ([storage.md](storage.md#the-reasoning-image)). `export!` on a larger host writes the
  image into the dump by default, and `import!` with `{:belief? true}` on the seat installs
  it in place of the recover. `:recover? false` is not a faster open: every query on it
  answers empty.
- **Give no `--starter` on a restart.** A store that already holds the schema dedups each
  starter sentence to its stored handle, and the load still reads every starter file.
- **Keep the store under `$HOME`.** Termux's home directory is app-private storage on the
  device's own filesystem. Android's shared storage (`/sdcard`) is a FUSE mount, and the
  engine's file lock, rename and fsync have not been run over one
  ([The single-writer contract](#the-single-writer-contract)).
- **Run one engine version across the fleet.** An open installs a store's reasoning image
  only under the source identity that wrote it ([storage.md](storage.md#the-source-identity)),
  so a seat on another engine build pays the full recover at every open.
- **Durability waits for the 3 s tick.** On the default, an append is durable within
  `vaelii.disk.sync-ms`, so a host that loses power, or an OS that kills the process, drops
  up to three seconds of acknowledged writes. `-Dvaelii.disk.fsync=dsync` makes each
  append durable when it returns, for one device sync per append.
- **A thread interrupt during disk I/O stops the store until it is reopened.** The
  interrupt closes the store's channel, and every later call on the store throws
  `:store-unusable` with `:reason :interrupted`
  ([storage.md](storage.md#a-store-that-stops)). Only opening the directory again clears
  the refusal.

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
- **The installed backend prints one short line per call.** An `:info` line is the local
  time and the message (`16:05:28 import: store the sentexes: …`). A louder line adds
  its level and namespace (`16:05:28 WARN recovery: …`), and a `:debug` or `:trace`
  line adds the id and the `:data` map after the message. The browser (`lein browser`,
  `lein run -m vaelii.web`) and `lein cli` install it at `:info` when no level is set.
  Trove's own backend, which a process with nothing installed uses, prefixes the ISO
  instant, the namespace, the source coordinates and the id, and prints `:data` on a
  second line.
- **The sink is `*out*`, which the CLI moves.** Trove's console backend prints to
  `*out*`; under `lein cli` that stream is the answer a script reads, so `-main` wraps
  whatever backend is installed to write on stderr instead (above). The dial is
  unaffected: the same lines at the same levels, on the other stream.
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

### Progress lines

A long loop logs its progress at `:info` through `vaelii.impl.progress`. A loop that ends
within 15 s prints nothing. A longer one prints a line at 15 s, 30 s, 1 min, 2 min and
4 min, then every 5 minutes, then a closing line:

```
recover: add the justifications: 120,000 of 1,000,000 (12%), 1.0 min in, about 7.3 min left
recover: add the justifications: done, 1,000,000 in 8.3 min
```

- **The count is the loop's own unit**: sentexes, justifications, frames, rules,
  passes, bytes or MB, as the label says. A label opens with the operation it belongs to
  (`recover:`, `settle:`, `import:`, `export:`, `reindex:`, `open:`, `compact:`,
  `quality:`, `integrity:`, `starter:`, `sync:`), so `grep 'recover:'` over the log
  follows one operation. A step on one store's files opens with the store's directory
  name instead (`kb-2026-10-18/index: read the token log`), since an open, an import and
  a close all run it. A loop whose total is unknown before it ends (a forward chaining
  run) prints its count and rate instead of a share and an estimate.
- **A timer logs a line that no tick does.** A step that counts nothing (the index
  snapshot and reasoning image writes) or a loop held on one item still prints
  `kb-2026-10-18: write the index snapshot: 15 s in` when its line falls due, so a
  console silent for 15 s has a line above it naming the step that runs. A loop over a
  total of 0 items schedules no timer, and a closed loop's timer task leaves the timer's
  queue when the loop closes.
- **The estimate waits for 0.1% of the loop.** A rate read off fewer items names hours
  for a loop that ends in minutes.
- **A rate change logs a line outside the schedule.** When the projected total time
  (elapsed plus left) halves or doubles against the last line's, at least 15 s after
  that line, a line logs the new estimate. A settle whose estimate falls from 2.6 h to
  14 min between two 5-minute lines prints each halving on the way down. A loop at a
  steady rate prints no extra line.
- **Each line is whole.** A `grep --line-buffered` filter reads it when it is written,
  and a line from another thread cannot land inside it. Its Trove `:id` names the loop
  and its `:data` carries `{:done :total :elapsed-ms}`.
- **A recover's steps keep their own line** (`::recover-step`), and a step's loops log
  inside it.
- **A caller follows the loops beneath it** by binding `progress/*observer*`: each loop
  started under the binding calls it with `{:id :label :done :total}` at most once a
  second, and once as it closes after such a call. A recover binds it to hand `*on-recover-step*` the step
  running with `:sub`, the loop that ticked, so `settle-record-edits!`' `:on-progress`
  reads the count of a step that runs for hours.

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
- **No request line is written, but a request's content can reach the log.** The
  exception in an `::op-error` line carries its message and `ex-data`, which can hold the
  path or sentence the request named. The engine's own `:warn` and `:info` lines
  (`::probably-not-meant`, `::dropped-conclusion`, `::exported`) name the sentences and
  paths they are about. No token reaches a log line at any level.
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
askable — `kb/opt-keys` is the key set `open-kb` checks against ([storage.md](storage.md)),
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
checks them against `test/golden/config-surface.edn`, both directions, and checks that every
one has a row below and that every citation resolves. Renaming or
removing one is **Breaking** (CONTRIBUTING §3.8). Nine rows are outside that net and say
so where they sit.

**A "Read at" cell is a floor, not an address.** `web.clj:NNN+` reads *start at line
NNN and read down*, and the number is rounded to a multiple of ten. An exact line was
checked exactly and drifted the moment anything above it was edited — a comment six
screens up failed the surface test with a diff that had nothing to do with
configuration, and the fix was always to retype a line number no reader used.

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
| `VAELII_TOKEN_TABLE` | `src/vaelii/host/guard.clj:240+` | the path of an EDN file mapping each token to `{:principal <symbol> :writes #{<context> …} :admin? <boolean>}`; blank or whitespace-only is unset | unset | The per-principal token table: set, it replaces `VAELII_API_TOKEN`, and a write op lands only in the contexts the presenting token's grant names ([The token table](#the-token-table)). A file that does not check stops the daemon at start. |
| `VAELII_ALLOWED_HOSTS` | `src/vaelii/host/guard.clj:40+` | comma-separated host **names**; a port on an entry is read as the name alone, and a value naming nothing is unset | unset | The `Host` headers a server answers, overriding the list the bind address implies. Entries are compared in the form a `Host` header is, so `kb.example.com:8080` and `kb.example.com` are one entry. |
| `VAELII_MAX_BODY_BYTES` | `src/vaelii/host/guard.clj:160+` | a positive whole number of bytes; blank is unset | `16777216` (16 MiB) | The request-body ceiling both servers refuse above, with 413. |
| `VAELII_MAX_QUERY_MS` | `src/vaelii/impl/config.clj:330+` | a whole number of milliseconds, 0 or more | `30000` | The wall clock a served read may name. A request may name less and is refused (`:over-ceiling`, 400) for naming more; a read naming none is given this, the four backward-search entry points included. `0` lifts the ceiling. |
| `VAELII_MAX_QUERY_DEPTH` | `src/vaelii/impl/config.clj:340+` | a whole number of rule expansions, 0 or more | `256` | The rule-expansion depth `:query`, `:query?`, `:query-status` and `:argue` may name, refused the same way; a read that takes a clock is held to no depth. `0` lifts it. |
| `VAELII_INTEGRITY_MAX_WORK` | `src/vaelii/impl/config.clj:460+` | a whole number of cooperative query units, 0 or more | `10000` | The `:max-work` a served `:kb-integrity` may name, refused the same way; a request naming none is given this. `0` lifts it. |
| `VAELII_INTEGRITY_MAX_RESULTS` | `src/vaelii/impl/config.clj:470+` | a whole number of findings, 0 or more | `1000` | The `:max-results` a served `:kb-integrity` may name, held the same way as `VAELII_INTEGRITY_MAX_WORK`. `0` lifts it. |
| `VAELII_MAX_WRITE_MS` | `src/vaelii/impl/config.clj:470+` | a whole number of milliseconds, 0 or more | `0` | The wall clock a served chaining write may name (`serve/write-bounds`). `0`, the default, sets no ceiling. Set, a request may name less and is refused (`:over-ceiling`, 400) for naming more, a write naming none is given this, and a write the clock ends is refused `:interrupted` and rolled back ([inference.md](inference.md#stopping-a-run)). |
| `VAELII_REQUEST_PATHS` | `src/vaelii/impl/config.clj:430+` | the boolean vocabulary | `false` | Whether a served request may name a path for the server to read or write. Off, a wire `:kb-diff` side names a KB the server serves and a string naming none is refused (`:path-not-served`, 403), a wire `:export` is refused the same way, and the browser's `/kbs/load` and `/kbs/export` refuse a `dir` (`:path-not-served`) and write under the catalog's `write-root`; on, the string is read as a text KB on the server's host, `:export` writes the directory it names, and the two routes take a `dir`. |
| `VAELII_SANDBOX_MAX` | `src/vaelii/impl/config.clj:440+` | a whole number ≥ 1 | `256` | How many browser sandboxes a KB holds. Opening one more resets the sandbox the eviction table ranks lowest ([web.md](web.md#how-many-sandboxes-a-kb-holds)). Read at each admission. |
| `VAELII_SANDBOX_IDLE_MINUTES` | `src/vaelii/impl/config.clj:450+` | a whole number of minutes ≥ 1 | `1440` | How long a browser sandbox may go unused before an admission resets it ahead of every used one. |
| `VAELII_SANDBOX_KEY` | `src/vaelii/browser/sandbox.clj:80+` | any string; blank or whitespace-only is unset | unset (32 random bytes per process) | The key the browser's sandbox cookies are tagged with (HMAC-SHA256). Set it to keep sessions across a restart or across replicas behind one name; unset, a restart re-mints every cookie. |
| `VAELII_WEB_PORT` | `src/vaelii/browser/web.clj:5830+` | a port number | `3000` | The port the browser binds. An unparseable value, or a number outside 0–65535, is logged at `:warn` and falls through to the property rather than failing the start. |
| `vaelii.web.port` | `src/vaelii/browser/web.clj:5830+` | a port number | `3000` | The same port, read after the variable, and logged the same way when unusable. |
| `VAELII_KB_DIR` | `src/vaelii/browser/web.clj:6930+` | a KB directory: a store, a dump or a corpus; blank is unset | unset | The directory the browser loads at startup, as a catalog job with belief recovered, while it serves the starter. The KB becomes the active one when the load finishes. A path holding no KB is logged and the browser stays on the starter. The three `scripts/start-vaelii*.sh` set it. |
| `VAELII_HEAP` | `scripts/lib/start.sh:20+` | a JVM heap size (`40g`, `24g`) | half of physical memory, up to `31g` | The `-Xmx` the three `scripts/start-vaelii*.sh` add to `JVM_OPTS`, beside `-XX:+ExitOnOutOfMemoryError`. A value above physical memory is refused, exit 1. |
| `VAELII_DEV` | `src/vaelii/impl/config.clj:240+` | the boolean vocabulary | `false` | Whether `lein browser` hot-reloads source edits and syncs shipped KB file edits into its loaded KBs and the starter's writes back into the files (`docs/web.md`), and re-reads its stylesheet per request, serving it uncached. Set only by `scripts/start-vaelii-dev.sh`; `-main` never hot-reloads. |
| `VAELII_PROFILER` | `src/vaelii/impl/config.clj:240+` | the boolean vocabulary | `false` | Whether the browser starts the sampling profiler's UI. Off unless asked for: it attaches an agent to the JVM and serves on a port of its own with no authentication. The dependency ships in the `:repl` profile, so `lein browser` has it and `lein run -m vaelii.web` does not — with it absent the start logs a line and `/caches` says so rather than linking to nothing. |
| `VAELII_PROFILER_PORT` | `src/vaelii/impl/config.clj:250+` | a port number | `8080` | Where that UI binds. Read only when the switch above says to start one. |
| `VAELII_LOG_LEVEL` | `src/vaelii/impl/config.clj:280+` | `error` `warn` `info` `debug` `trace`, case-insensitive | unset | The level the engine's own statements print at, installed as the engine loads. Unset installs no backend at all, which is a setting rather than a default. |
| `VAELII_CACHE_SCALE` | `src/vaelii/impl/config.clj:290+` | a number 0 or more | `1.0` | The multiplier on every in-memory derived cache's shipped entry limit, applied as the engine loads. Below 1 shrinks the caches for a small heap; above 1 grows them for a bulk load. A per-cache floor keeps a small scale from taking a cache below the point where it saves nothing. `vaelii.core/set-cache-scale` is the same dial on a running process, and `caches` shows the effective limit each cache enforces. |
| `vaelii.heap.mark` | `src/vaelii/impl/config.clj:240+` | the boolean vocabulary | `true` | Whether `open-kb` arms the heap mark: the old generation's collection-usage threshold at 0.92 and a listener under which a chaining write refuses `:interrupted :bound :heap` and rolls back, `forward-chain` included, instead of running out of heap; an operation-log replay takes no heap stop ([caches.md](caches.md#the-heap-mark)). Armed once per JVM and never disarmed. `false` is for an embedder that sets the old generation's threshold itself, since the JVM holds one per pool. |

**The durable store.** All system properties, all read at `open-kb`.

What the defaults cost, stated once rather than left to be assembled from the rows: on
the default an append is durable **within `vaelii.disk.sync-ms`**, so a machine that
loses power or a JVM killed outright drops up to three seconds of acknowledged writes.
A clean exit drops nothing — `close!` and the shutdown hook flush — so the interval of lost writes is a
crash window and not a shutdown one. `vaelii.disk.fsync=dsync` closes it and makes every
append durable when it returns, which is the trade a store of record wants and most of a
common-sense KB does not. The other defaults are off because *on* is the choice that
costs something a KB cannot give back for free: `tokens` adds a durable ground truth a
store opts into, and `compress` spends CPU per frame and can grow a store: each frame is
compressed alone, so a frame holding one fact comes out larger by the codec's own framing.

The mapped index image is not among them, because it is not a switch. It is an index
representation, named in the KB's own opts as `{:backend :disk-snapshot}` — the one
pairing there is, the image being validated against the disk record store's own slot
fingerprint — so which index a KB holds is readable from its configuration rather than
from the JVM's, and only macOS and Linux can swap one, so that backend is refused
elsewhere ([storage.md](storage.md)). `vaelii.index.snapshot` is read for one purpose
only, which is to **refuse** it: it has the row below because the build reads the name,
and a process whose unit file sets it fails at `open-kb` rather than running on a
representation nobody chose.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `vaelii.disk.dir` | `src/vaelii/impl/disk/backend.clj:240+` | a directory path; blank is unset | `<java.io.tmpdir>/vaelii-disk` | The base a disk KB's space directory hangs under when no `:dir` names one. |
| `vaelii.disk.fsync` | `src/vaelii/impl/config.clj:10+` | `dsync`, or unset | unset | Whether every append is durable when it returns (`dsync`), or durability waits for the tick below. |
| `vaelii.disk.sync-ms` | `src/vaelii/impl/config.clj:160+` | a whole number ≥ 0; `0` starts no daemon | `3000` | The durability daemon's tick, in milliseconds. **Read once per process**: the first disk store to open starts the tick at this value, and a later open's value neither restarts it nor, at `0`, stops it. |
| `vaelii.disk.auto-compact` | `src/vaelii/impl/config.clj:10+` | the boolean vocabulary | `true` | Whether background and opportunistic compaction runs at all — one knob for the fsync tick, the close path, and a `:disk-snapshot` KB's mid-life image refresh, which is an opportunistic compaction of a derived structure like the others. `false` is how a batch that fills a KB in one run and closes cleanly asks for exactly one image, at the end. |
| `vaelii.disk.compact-dead-ratio` | `src/vaelii/impl/config.clj:200+` | a number from 0 to 1 | `0.5` | The dead fraction a log must reach before compacting it is worth the write. |
| `vaelii.disk.compact-min-interval-ms` | `src/vaelii/impl/config.clj:210+` | a whole number ≥ 0 | `300000` | The floor between two auto-compactions of one backend. |
| `vaelii.disk.compress` | `src/vaelii/impl/config.clj:170+` | `zstd` `lz4` `none` `off` `false` | uncompressed | The codec durable frames are written with, one frame at a time. A store of small facts grows under it: 3,000 facts measured 442,559 bytes uncompressed, 463,559 under `lz4` and 520,559 under `zstd`. |
| `vaelii.disk.tokens` | `src/vaelii/impl/config.clj:60+` | the boolean vocabulary | `false` | Whether sentex bodies are written as token ids. Reading never depends on it — a frame carries its own tag. |
| `vaelii.disk.cache` | `src/vaelii/impl/config.clj:180+` | a whole number ≥ 0; `0` disables the cache | `65536` | Hot records held in memory per kind. |
| `vaelii.disk.shutdown-unwind-ms` | `src/vaelii/impl/config.clj:220+` | a whole number ≥ 0 | `10000` | How long the JVM shutdown hook waits, after it asks the running writes to stop, before it closes the stores under the ones still running ([storage.md](storage.md#a-shutdown-under-a-running-write)). A process whose batches settle for minutes sets it above its longest batch. |
| `vaelii.disk.lock` | `src/vaelii/impl/config.clj:210+` | the boolean vocabulary | `true` | Whether the single-writer `FileLock` is taken when a directory opens. Off removes the enforcement and not the contract. |
| `vaelii.index.snapshot` | `src/vaelii/impl/config.clj:230+` | none — the domain is empty and every value is refused | unset | **Refused, not read.** The mapped index image is an index representation, so it is named in the KB's opts (`{:backend :disk-snapshot}`) and not process-wide. `config/check!` reads it at every `open-kb`, so a `-D` left over from an older unit file fails the open with `:unknown-option` naming the backend to take instead — rather than a KB quietly rebuilding the index the property was meant to save. |
| `vaelii.index.snapshot-drift` | `src/vaelii/impl/config.clj:250+` | a ratio, 0–1 | `0.5` | How far a `:disk-snapshot` KB's live index may drift from its image — in indexed roots, against the count the image holds — before the writer rewrites it. The rewrite happens on the writer's thread and is a full image write, so `vaelii.disk.compact-min-interval-ms` floors how often it can happen. **`0` is the most eager setting in the range, not the off one**: as a threshold it means "any drift at all", so it rewrites the image on every write past the floor — 400 asserts under it measured 401 images. `vaelii.disk.auto-compact=false` is what turns the mid-life refresh off. Only `assert` drives the cadence: a store filled by `reindex` or by an import gets one image, at the close, whatever this says. |
| `vaelii.belief.snapshot` | `src/vaelii/impl/config.clj:270+` | none — the domain is empty and every value is refused | unset | **Refused, not read.** A reasoning image is written and installed for every `{:backend :disk-snapshot}` KB on the dense network ([storage.md](storage.md#the-reasoning-image)), and no property turns it on or off. `config/check!` reads it at every `open-kb`, so a `-D` left in a unit file fails the open with `:unknown-option` naming the backend to take instead. |

**Finding a KB.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_KB_PATH` | `src/vaelii/browser/catalog.clj:20+` | `:`-separated directory list (`;` on Windows) | `./kbs` and `~/.vaelii/kbs` | The directories KB discovery walks. |
| `vaelii.kb.path` | `src/vaelii/browser/catalog.clj:250+` | as above | as above | The same list, read after the variable. |
| `VAELII_KB_CATALOG` | `src/vaelii/browser/catalog.clj:20+` | a file path | `~/.vaelii/catalog.edn` | The file naming KBs that live outside the search path. |
| `vaelii.kb.catalog` | `src/vaelii/browser/catalog.clj:260+` | a file path | as above | The same file, read after the variable. |
| `vaelii.browser.detach-ms` | `src/vaelii/browser/inflight.clj:10+` | a positive integer (ms) | 5000 | How long a browser page load waits for its read before it is answered with the waiting page and the read goes on ([web.md](web.md), "Page loads that read long"). |
| `vaelii.removed.dir` | `src/vaelii/browser/removed.clj:10+` | a directory path | `~/.vaelii/removed` | Where the browser keeps each KB's list of the last sentexes it removed, for `/removed` to put back. The test profile points it under `target/`. |

**What the engine reasons with.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_ARBITRATE_CONSTRAINTS` | `src/vaelii/impl/config.clj:290+` | none — the domain is empty and every value is refused | unset | **Refused, not read.** No switch chooses whether a definitional clash is refused: the KB stores it, decides it and reports it ([nmtms.md](nmtms.md#1-order-independence)). `config/check!` reads it at every `open-kb`, so a variable left set fails the open with `:unknown-option`. |
| `VAELII_ASSERTIVE_ARG_TYPES` | `src/vaelii/impl/config.clj:230+` | the boolean vocabulary | `true` | Whether the argument constraints entail types as well as constrain them; `=0` opts out to the constraint-only reading ([argtypes.md](argtypes.md)). |
| `VAELII_PRUNE_SUBSUMED_MINTS` | `src/vaelii/impl/config.clj:230+` | the boolean vocabulary | `true` | Whether a minted argument type gives way to a membership the KB believes more specifically, storing about a tenth fewer sentexes for the same answers; `=0` opts out and stores every mint ([argtypes.md](argtypes.md)). |
| `VAELII_ASP_SOLVER` | `src/vaelii/impl/config.clj:270+` | `clingo` `clasp` | unset | Which ASP backend solves. Unset is auto: in-process clingo when it loads, else clasp. A name outside that list is refused rather than read as auto. |
| `vaelii.asp.solver` | `src/vaelii/impl/config.clj:50+` | `clingo` `clasp` | unset | The same choice, and it is read **first**. |
| `VAELII_CLINGO_MAX_BYTES` | `src/vaelii/impl/config.clj:280+` | a whole number of bytes, 0 or more | `3000` | The program size above which auto mode routes a plain-ASP program to clasp even where clingo loads. |
| `VAELII_ASP_SOLVE_LIMIT` | `src/vaelii/impl/config.clj:370+` | a whole number of conflicts, 0 or more | `100000` | How many conflicts one ASP solve may spend before its search stops; 0 sets no limit. Both backends take it as clasp's `--solve-limit` and search on one thread under a fixed seed, so a solve that meets it meets it on every machine and under any load. A solve it stops is no answer, as at the time limit: the edge solver decides nothing, an imperative refuses with `:solver-failed`, and a `:label` solve holding a model returns it as best-effort ([asp.md](asp.md#the-solve-limit)). |
| `VAELII_ASP_TIME_LIMIT` | `src/vaelii/impl/config.clj:380+` | a whole number of seconds, 0 or more | `60` | How long one ASP solve may run before the backend is interrupted; 0 lifts the limit. It is the backstop behind `VAELII_ASP_SOLVE_LIMIT`, and the only limit when that is set to 0: which solves meet it depends on the machine. A clasp process still running at twice the limit (at least the limit plus 10 s) is killed and the solve raises `:solver-unavailable`. An interrupted solve is no answer: the edge solver decides nothing and an imperative refuses with `:solver-failed`. One *operation* makes several solves, each with the whole budget ([asp.md](asp.md)). |
| `VAELII_ASP_OPT_STRATEGY` | `src/vaelii/impl/config.clj:400+` | `bb` `usc` | `bb` | How every ASP solve optimizes: `bb` is clasp's branch-and-bound, `usc` core-guided optimization (`--opt-strategy=usc,k,0,stratify`). Both backends take it beside the solve limit, so a solve stops at the same point on every machine under either; the strategy changes which model a `:label` solve that meets the limit returns ([asp.md](asp.md#the-optimization-strategy)). |
| `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS` | `src/vaelii/impl/config.clj:400+` | a whole number ≥ 1 | `12` | The most members a coupled dilemma cluster may hold for the solve-free brave/cautious classifier to enumerate its resolutions; a larger cluster is left `:supportable`, and a backend is the tool for the large interacting set. Read per classification by `classify-local`, which reads resolutions from the JTMS and calls no solver ([labeling.md](labeling.md)). |
| `VAELII_CLASSIFY_RESOLUTION_BUDGET` | `src/vaelii/impl/config.clj:400+` | a whole number ≥ 1 | `20000` | The number of candidate subsets one cluster's resolution enumeration may examine before the classifier abandons the cluster to `:supportable`. A cluster of *m* members has 2^*m* − 1 candidates, so under the default member cap of 12 (at most 4,095) the budget binds only once `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS` is raised above 14. A per-read search bound, nothing retained. |
| `VAELII_CLASSIFY_MAX_JOINT_OPTIMA` | `src/vaelii/impl/config.clj:400+` | a whole number ≥ 1 | `1024` | The cap on the product of optima a cross-cluster datum's classification enumerates — the clusters that move the datum, times their optima. A datum whose product is larger is left `:supportable`, since its class needs joint resolutions a backend enumerates. |
| `vaelii.clasp.bin` | `src/vaelii/impl/asp/clasp.clj:20+` | an executable name or an absolute path; blank is unset | `clasp`, found on `PATH` | Which executable the subprocess backend runs: clasp, or the clingo executable, which takes the same flags ([asp.md](asp.md#getting-a-solver)). Read once, when the namespace loads. |
| `VAELII_CLASP_BIN` | `src/vaelii/impl/asp/clasp.clj:20+` | as above | as above | The same executable, read after the property. |
| `vaelii.clingo.lib` | `src/vaelii/impl/asp/clingo.clj:20+` | a library name or an absolute path; blank is unset | `clingo`, resolved through `jna.library.path` | Which libclingo the in-process bridge loads. |

**The build label.**

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `vaelii.build` | `src/vaelii/impl/io/export.clj:130+` | any label; blank is unset | the git HEAD, else `dev` | How the writing build names itself in a dump's `meta.edn`. Diagnostic: a dump that will not read is first a question about which build wrote it. |
| `VAELII_BUILD` | `src/vaelii/impl/io/export.clj:130+` | any label; blank is unset | as above | The same label, read after the property. |

### Developer — the suite and the scripts

CI sets these too; nothing in a deployment does.

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_TEST_BACKEND` | `test/vaelii/test_util.clj:210+` | a `<records>-<index>` backend name (`memory`, `disk-log`, `memory-columnar`, …), or `overlay` | `memory` | Which of the eight stores the whole suite runs on. |
| `VAELII_TEST_TMS` | `test/vaelii/test_util.clj:60+` | `reference` `dense`; blank is unset | `dense` | Which truth-maintenance representation the suite runs on. |
| `VAELII_TEST_SPACE` | `test/vaelii/test_util.clj:190+` | a whole number from 5 to 15; blank is unset | `15` | The top of the two-space block the suite's KBs live on, so two runs can have distinct directories. |
| `VAELII_AUDIT_SUPPORT` | `test/vaelii/test_util.clj:410+` | a directory that exists | unset (no audit) | Makes the suite's teardown write, one EDN map per line into `<dir>/<pid>.edn`, every stored justification whose conclusion's context does not see the context of one of its supporters — an antecedent, or the rule a firing names. Changes no test's outcome. |
| `VAELII_TEST_TMPDIR` | `test/vaelii/truncation_fuzz_test.clj:70+` | a directory that exists | unset (the platform temp directory) | Where the `^:fuzz` truncation sweep builds each probe's directory. A probe's whole cost is one device cache flush, so pointing this at a tmpfs (`/dev/shm`) takes the sweep from ~10 minutes to a couple. Nothing else reads it. |
| `VAELII_FULL_KB_DIR` | `test/vaelii/full_kb_test.clj:20+` | a store directory; blank is unset | unset (the `^:full-kb` tests fail at once) | The store the `^:full-kb` probes open and write into. `scripts/test-full-kb.sh` sets it to a disposable clone; set it by hand only to a KB you can lose. |
| `VAELII_FULL_KB_WORK` | `scripts/test-full-kb.sh:0+` | a directory on the same volume as KB-DIR | `testbench/full-kb` | Where `lein test-full-kb` puts each run's clone of KB-DIR, deleted after the run. Outside `target/`, so a `lein clean` during a run does not delete the KB the test JVM has open. KB-DIR itself is what the run upgrades. The clone is an APFS clone, so another volume turns it into a full copy. The script's `VAELII_HEAP` default is `44g`. |
| `VAELII_TEST_LOG_LEVEL` | `project.clj:130+` | `error` `warn` `info` `debug` `trace`; blank is unset | `error` | The floor the `:test` profile installs the engine's logging at, through `set-log-level` itself. |
| `VAELII_TEST_NS_COUNTS` | `project.clj:150+` | the boolean vocabulary | `false` | Prints one `NSCOUNT <namespace> <assertions>` line per test namespace. Two runs diffed name the namespace whose count moved, which is what `test-backends.sh`'s assertion-count check cannot say on its own. |
| `VAELII_TEST_VERDICTS` | `project.clj:150+` | the boolean vocabulary | `false` | Prints one `TESTVERDICT <ns/name> pass\|fail` line per test var. `lein test-red` sets it and fails on a `^:red` test that passes. |
| `VAELII_SETTLE_HOUR` | `test/vaelii/settle_hour_test.clj:0+` | `1` or unset | unset (the settle test prints that it skipped) | Runs `settle-of-the-full-kb-within-an-hour`, the `^:full-kb` test that opens `VAELII_FULL_KB_DIR` without belief, settles it with `settle-record-edits!`, prints each phase's minutes and fails past 60. Opt-in beyond the selector because `full_kb_test` opens the same clone with belief and two full-size KBs do not fit one heap: `VAELII_SETTLE_HOUR=1 lein test-full-kb <store> :only vaelii.settle-hour-test`. A postgres store is refused. |
| `VAELII_SETTLE_REMOVE` | `test/vaelii/settle_hour_test.clj:0+` | a count | `0` | How many stored premises the settle test removes through `edit-records!` before it settles, so the sweep has seeds. |
| `VAELII_TEST_HEAP` | `project-env.clj:40+` | a JVM heap size (`4g`, `6144m`) | `4g` | The `-Xmx` the `:test` profile gives a test JVM. Unset, a `JVM_OPTS` that already names `-Xmx` keeps its own, which is how `lein test-full-kb` passes `VAELII_HEAP`. The profile also sets G1 to return freed heap (`MaxHeapFreeRatio=30`, a 15 s periodic collection) and two parallel and one concurrent collector thread per JVM. |
| `VAELII_BENCH_LOG_LEVEL` | `project.clj:170+` | `error` `warn` `info` `debug` `trace`; blank is unset | `error` | The same floor for the `:bench` profile, so `lein perf` and the `bench-*` harnesses print readings rather than the logging their workloads provoke. |
| `VAELII_RETE` | `test/vaelii/test_util.clj:30+` | the boolean vocabulary | `false` | Runs the suite's forward chaining through the incremental matcher instead of the reference. |
| `VAELII_HIER` | `test/vaelii/test_util.clj:60+` | the boolean vocabulary | `true` | The set-algebra context-scoped retrieval. `0` routes every match through the reference nested fan-out instead. |
| `VAELII_PLAN` | `test/vaelii/test_util.clj:60+` | the boolean vocabulary | `true` | The conjunctive planner's cost ranking. `0` runs a conjunction's generators in the order they were written, so the whole suite answers unranked; the readiness discipline is not behind it and runs either way. |
| `VAELII_QUERY_ENGINE` | `test/vaelii/test_util.clj:50+` | `dfs` `inference` `hybrid` | unset | Runs every `prove` on the engine named rather than the goal-stack DFS. |
| `VAELII_QUERY_STRATEGY` | `test/vaelii/test_util.clj:60+` | a tactician `tactics/tacticians` names, such as `breadth-first` | unset | Which tactician orders the node engine's goals. Only meaningful beside the row above. |
| `VAELII_CLINGO_LIB` | `project.clj:80+` | a directory holding `libclingo` | `/opt/homebrew/lib` | What the `+with-clingo` profile points `jna.library.path` at. |
| `VAELII_BASH` | `project-env.clj:10+` | a bash to run | unset (on Windows, Git for Windows' bash when installed; else `bash`) | The bash every script alias (`lein lint`, `lein gate`, `lein fix`, `lein test-*`, `lein perf`) runs, and that the suite runs scripts with. On Windows a bare `bash` is WSL's whenever WSL is installed, ahead of `PATH`, which is why the default names Git's; `bash` here asks for WSL's. |
| `vaelii.test.bash` | `test/vaelii/test_util.clj:230+` | a bash to run | `bash` | The bash a test drives a script with. The `:test` profile sets it to the choice above, so set `VAELII_BASH` instead. |
| `VAELII_COLOR` | `scripts/gate.sh:110+` | `always` `never` | unset | Whether `lein gate` and `lein lint` colour their output; unset asks the terminal. |
| `VAELII_GATE_OUT` | `scripts/test-parallel.sh:40+` | a directory | `logs/gate` | Where the parallel test stage writes its per-shard logs, `test.assign` (each shard's namespaces with their predicted seconds) and each shard's `test.timing-<n>.tsv`. `lein gate` sets it to that run's own directory, so the shard logs land beside the stage logs rather than in a directory two `lein gate` runs share. |
| `VAELII_GATE_TIMINGS` | `scripts/test-parallel.sh:40+` | a file | `logs/test-timings.tsv` | The per-namespace timings the test stage bin-packs its shards from, a moving average each run moves 0.3 of the way to its own figures. **Per checkout, not per run**: they are feedback for the *next* `lein gate` run, so every run shares them, outside `target/`, which `lein clean`, `lein jar` and `lein install` empty. A namespace the file lacks takes its CI weight scaled to local time. |
| `GATE_JOBS` | `scripts/gate.sh:60+` | a whole number | unset | The test stage's shard count. **Not frozen** — see below. |
| `TEST_MIN_JOBS` | `scripts/test-parallel.sh:30+` | a whole number | `3` | The fewest shards `lein test-parallel` (and so `lein gate`'s test stage) starts when no `--jobs` or `GATE_JOBS` names a count. The load-aware count subtracts every vaelii JVM running, an idle REPL or server included, and at one shard the suite takes over 50 minutes. Under `GATE_MAX_CONCURRENT`'s default of 2, two `lein gate` runs at this floor start six test JVMs. **Not frozen.** |
| `PERF_TOLERANCE` | `scripts/gate.sh:60+` | a multiplier (`1.5`) | unset | Passed through to `lein perf --tolerance`, for a loaded box. **Not frozen.** |
| `GATE_MAX_CONCURRENT` | `scripts/lib/slots.sh:280+` | a whole number; `0` disables | `2` | How many `lein gate` test stages run at once on the box, from any worktree: each holds one `gate-lock.<i>` file in the shared git directory's `vaelii-matrix/`. A `lein gate` run over the cap runs lint and waits for a slot, naming the holders once a minute, and its test stage reads its shard count after admission. **Not frozen.** |
| `GATE_NO_WAIT` | `scripts/lib/slots.sh:280+` | any non-empty value | unset | Makes `lein gate` exit 75 instead of waiting when every gate slot is held. **Not frozen.** |
| `PERF_NO_WAIT` | `scripts/lib/slots.sh:280+` | any non-empty value | unset | Makes `lein perf` and `lein perf-ab` exit 75 instead of waiting while another perf run holds `perf-lock`. **Not frozen.** |
| `TEST_BACKENDS_OUT` | `scripts/test-backends.sh:70+` | a directory | `logs/test-backends/run-<pid>` | Where `lein test-backends` writes one log per run; the default is per-run, with `latest` pointing at the newest, and old run dirs are pruned to the last `BACKENDS_KEEP_RUNS` (20), sparing any touched in the last 24h. **Not frozen.** |
| `TEST_SWEEPS_OUT` | `scripts/test-sweeps.sh:50+` | a directory | `logs/test-sweeps` | Where `lein test-sweeps` writes one log per run. **Not frozen.** |
| `SUITE_PROGRESS` | `scripts/lib/suite-marks.sh:40+` | `marks` `lines` `auto` | `auto` | How `lein test-backends` and `lein test-sweeps` report a namespace as it finishes: `marks` is the ✔/✘ rows a terminal animates, `lines` is one named, counted and timed line each — what a log, a pipe or CI gets, since a row of ticks in a file names nothing. `auto` reads the terminal. **Not frozen.** |
| `TEST_MATRIX_OUT` | `scripts/test-matrix.sh:50+` | a directory | `logs/test-matrix/run-<pid>` | Where `lein test-matrix` writes one log per configuration, plus `summary.tsv`; per-run, with `latest` pointing at the newest. Under `logs/` (gitignored), not `target/`, so a concurrent `lein clean` cannot delete a live run; old run dirs are pruned to the last `MATRIX_KEEP_RUNS` (20), sparing any touched in the last 24h. **Not frozen.** |
| `MATRIX_JOBS` | `scripts/test-matrix.sh:50+` | a whole number | performance cores − 2, less the vaelii JVMs already running (`scripts/lib/slots.sh`) | How many of the fourteen configurations run at once. One run is about one core of test work, so more slots than cores buys nothing and costs a JVM each. Unset, the running matrix re-reads that rule with its own JVMs left out, each time a configuration ends and every `MATRIX_SLOTS_EVERY` seconds. `lein test-matrix --set-jobs <n>` sets the running matrix's count and stops that re-read; its scheduler re-reads the set count every pass. Either way a raise launches more at once, and a lower launches nothing new until fewer are running. **Not frozen.** |
| `MATRIX_OWED_MAX` | `scripts/test-matrix.sh:50+` | a whole number; `0` disables | `4` | The most configurations `lein test-matrix --owed` starts: the ones a changed file names itself first, then the ones a group word brought in, each half in the (shuffled) launch order; the rest are on the `not run:` line. A queued owed run is capped the same way. **Not frozen.** |
| `MATRIX_RED_COOLDOWN` | `scripts/lib/slots.sh:200+` | seconds; `0` disables | `1800` | How long after a red `lein test-matrix` run no matrix starts or queues. The refusal (exit 75) names the red run's directory, its failing tests per configuration with a one-test re-run command each, who requested it, and the queued requests it dropped; the red run drops the queue, and a green run lifts the cooldown. **Not frozen.** |
| `MATRIX_YIELD` | `scripts/test-matrix.sh:50+` | `0` disables | `1` | Whether a running `lein test-matrix --owed` ends at its first configuration verdict when a request is queued behind it. On a green verdict it stops the configurations still running, queues its own baseline and exits 75, and the next matrix runs every queued baseline's owed set at the primary's HEAD; on a red one it halts as a red run. A configuration a yield leaves without a verdict runs first in the next owed run that owes it, and that run does not yield before the configuration has a verdict. A run named by group or configuration never yields. **Not frozen.** |
| `TEST_MATRIX_SEED` | `scripts/test-matrix.sh:50+` | a whole number | a fresh one per run | The seed the launch order is shuffled with. `lein test-matrix` shuffles by default, so a run stopped early — by `--fail-fast`, by ^C, by the box — has covered a random subset of the configurations rather than the same prefix every time; the seed is printed with the header and again with the verdict, and giving it back runs that order again. `--ordered` ignores it and schedules the longest configuration first instead, which is ~1 minute faster over the routine configuration set. **Not frozen.** |
| `MATRIX_JVM_OPTS` | `scripts/test-matrix.sh:50+` | JVM flags | unset | Extra `JVM_OPTS` for every configuration. `-XX:ActiveProcessorCount=2` is the one worth measuring on a loaded box — each JVM otherwise sizes its GC and JIT pools from every core while doing one core of work. It lands in each configuration's log header (`# env … lein test …`, under the revision header), so a run stays reproducible by copying that line. **Not frozen.** |
| `ALLOW_WORKTREE_RUN` | `scripts/lib/slots.sh:70+` | `release` | unset | Lets `lein test-matrix`, `test-backends`, `test-sweeps`, `test-shuffle` and `perf` run from a linked worktree, which each refuses otherwise (exit 3): a second fleet of JVMs beside the primary's drops every runner to one slot. It exists for the release agent's runs in a scratch worktree at the carved sha; any other value is refused, and every other run goes in the primary on main. **Not frozen.** |
| `MATRIX_SLOTS_EVERY` | `scripts/test-matrix.sh:50+` | seconds | `30` | How often a matrix started without `MATRIX_JOBS` or `--jobs` re-reads its slot count between configurations ending. **Not frozen.** |
| `MATRIX_HEARTBEAT` | `scripts/test-matrix.sh:50+` | seconds; `0` disables | `60` | How often `lein test-matrix` prints how far each running configuration has got. Fourteen interleaved per-namespace streams are not readable, so this is what replaces them. **Not frozen.** |

The rows marked **Not frozen** are the names the contract test does not freeze, and the reason is what a
regex can tell apart: `${VAELII_…}` in a shell script is name-shaped enough for one
pattern, and `${GATE_JOBS}` is indistinguishable from every local variable the script
has. A few names outside the net, named as such, is a better trade than a test that
parses shell. The scripts also honour `NO_COLOR`, `CI` and `TERM` — conventions, read as
inputs to the colour decision and not knobs of this project's.

### Bench

| Switch | Read at | Legal values | Default | What it decides |
|---|---|---|---|---|
| `VAELII_BENCH_STORE` | `bench/vaelii/bench/survey.clj:360+` | a directory holding a record log | `~/.vaelii/kbs/store` | The corpus the real-corpus benchmarks sample when the command line names none. |
| `VAELII_SURVEY_STORE` | `bench/vaelii/bench/survey.clj:20+` | a directory holding a record log | as above | A second name for the same directory, read when the row above is unset. |
| `VAELII_PYRAMID_CORPUS` | `bench/vaelii/bench/pyramid.clj:20+` | a directory holding `vaelii.txt` | none — a run without it is refused, naming itself | The join.1k corpus the pyramid benchmark reads. It is a field-harness artifact and is not in this repo, so a default could only name whoever wrote one. |
| `VAELII_RECOVER_CORPUS` | `bench/vaelii/bench/recoverphase.clj:570+` | a directory holding a `:disk` store of sentexes | none — a store-reading run without it is refused, naming itself | The corpus the recover benchmark's store-reading modes read when the command line names no path. A dev-box `:disk` store, not in this repo, so a default could only name whoever wrote one. |
| `vaelii.closure.limit` | `bench/vaelii/bench/recoverphase.clj:90+` | a whole number of closure terms | unset (the taxonomy's own bound, `closure-bound`) | The bound the recover benchmark sets on the taxonomy's closure cache while it recovers (`caches/set-limit :taxonomy-closures`), so the cache the phase runs under is a knob rather than the shipped default. |

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
