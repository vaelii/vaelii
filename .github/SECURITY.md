# Security Policy

## Reporting a vulnerability

Please don't open public issues for security vulnerabilities.

Report privately by **email**: support@vaelii.com, with "SECURITY" in the subject line.

If GitHub's "Report a vulnerability" button is present on this repository's Security
tab, that works too and threads the discussion for you. Email is documented first
because it is the channel that is always there.

Include what you can: affected version or commit, reproduction steps, and impact.
Please practice coordinated disclosure — report privately first and allow time for a
fix to land before publishing details.

## Supported versions

`main` and the latest release are the only versions in scope. Older releases are not
patched.

## Scope

Vaelii is a library first: `vaelii.core` over an in-memory or on-disk store, with no
network surface. Two optional processes put it on a socket. The **browser
authenticates nobody**, and the **daemon** holds one shared bearer token — required to
bind anything but loopback, optional on loopback itself. Neither has users, roles or
sessions, and that is a design position rather than an oversight: both are intended to
run where only their operator can reach them, and per-caller identity is a reverse
proxy's job. So the reports worth sending are about a boundary that fails to hold where
it claims to, not about the absence of a login on a tool that never offered one.

### The browser (`vaelii.browser.web`, default port 3000)

- **It binds loopback**, and reaching it from another machine is the deliberate
  `--listen` flag on `-main`. Nothing else exposes it.
- **Seventeen routes write** (every `POST` in `web/app`), and **nothing authenticates
  them**. Each compares the request's `Origin` (falling back to `Referer`) against its
  own `Host` and answers 403 on a mismatch, so another site's tab cannot drive the
  editor and a sandboxed frame's `Origin: null` is refused. That is a cross-origin
  defence, **not** an access control: a request carrying neither header is a
  non-browser client with no ambient context to ride, and it passes.
- **Write routes are serialized** on one process-wide monitor, as the daemon's ops are.
  Jetty serves them on a thread pool, and the storage layer beneath is single-writer.
- **Bodies are capped** at the same `VAELII_MAX_BODY_BYTES` (16 MiB) the daemon reads,
  and the check sits outside form parsing, so an oversized body is refused with 413
  before it is decoded.
- **Loopback is not an access control either.** Every local account can reach it, and
  `POST /kbs/export` writes a directory of dump files wherever the process can write.
  On a shared host, treat reaching the port as equivalent to holding the KB.
- **Every route, read or write, requires a recognised `Host`.** On a loopback bind the
  header must name loopback (`vaelii.host.guard`), which is what refuses a DNS-rebound
  page — against which the origin check above is useless, since the attacker controls
  `Origin` and `Host` alike and they agree. Binding an address with `--listen` drops
  the allowlist unless `VAELII_ALLOWED_HOSTS` names one.
- **Two routes write to the filesystem** rather than to a KB: `POST /kbs/export` takes
  the destination directory from the request, and `POST /kbs/load` will create a
  durable store at a client-named path. Both are origin- and `Host`-checked like any
  other write, and both are as reachable as the operator's browser is.
- **`POST /propose` reaches a language-model provider**, so it is the one route that
  causes outbound network traffic. It is a read of the KB and a write of nothing.
- **No destructive path is reachable by GET**, so a link, a prefetch or a crawler
  cannot change a KB.
- **`lein browser` is a development command and pairs the browser with an nREPL**, both
  pinned to `127.0.0.1` with no way to say otherwise from the profile. An nREPL is
  arbitrary code execution by design; a write route with no authentication beside one
  on a reachable interface is a remote shell. Never run `lein browser` on a machine
  where either port is exposed.
- **The `:repl` profile can serve a profiler UI** (clj-async-profiler, conventionally
  on 8080). Same rule: a development tool, loopback only.

### The daemon (`vaelii.host.serve`, default port 4200)

- **It binds loopback**, and `--listen` binds an address instead. A bind that names a
  non-loopback address **requires `VAELII_API_TOKEN`**: without one the daemon prints a
  line and exits 2, before it opens the KB. The flag that publishes `POST /op` is also
  the flag that drops the `Host` allowlist, so the exposed configuration must not be the
  least-defended one.
- **A shared bearer token authenticates every request** when `VAELII_API_TOKEN` is set —
  `Authorization: Bearer <token>`, compared in constant time, else 401 with a
  `WWW-Authenticate: Bearer` challenge. A missing, wrong or malformed credential is one
  refusal with one body, so nothing about it is an oracle. It is one token for the
  process: there are no users, no roles and no sessions, and TLS is a reverse proxy's
  job — the wire is plaintext.
- **On a loopback bind the token is optional**, and without one every local account can
  drive the write route. The daemon logs which posture it started in on every start.
- **`GET /health` answers without the token**, and it is the only route that does, so a
  container orchestrator can watch a daemon it holds no credential for. It reveals
  `{:ok true}` and nothing else.
- **`POST /op` refuses a body that is not `application/edn`, and refuses a
  cross-origin one.** Both matter on a loopback bind, because a page the operator
  merely visits is a local client: without the content-type requirement a cross-site
  `fetch` is a CORS-*simple* request that needs no preflight, and the write lands.
  As on the browser, a recognised `Host` is required too.
- **Bodies are capped** at `VAELII_MAX_BODY_BYTES` (16 MiB) and read incrementally, so
  a caller who reaches the port cannot spend the daemon's heap by streaming one.
- **Bodies are read with `clojure.edn/read-string`**, which has no reader-eval, so an
  untrusted body cannot run code. A way around that is a bug worth reporting.
- **Operations go through an allowlist** (`serve/ops`) of `vaelii.core` fns, so no
  client can reach an arbitrary var.
- **`:export` writes to the filesystem of the host the daemon runs on**, at a directory
  the client names. It refuses a directory that exists and is non-empty, and that is
  the only constraint on it — it will happily `mkdirs` a path that does not exist. It is
  therefore a file write for anyone holding the token, and on an open loopback daemon
  for every local account: the sharpest consequence of the points above.

### Everything else

- **A KB dump is trusted input.** `import` thaws nippy, and a dump directory is
  therefore code-adjacent in the way any deserialization format is: take one only from
  somewhere you would take a jar from. Nothing loads a dump on its own — discovery
  under `~/.vaelii/kbs/` only *lists* what it finds, and loading is an explicit,
  origin-checked action.
- **Untrusted KB content.** A KB may hold text from anywhere, and the browser renders
  it. Markup is escaped in body and attribute position alike (hiccup 2), and every
  response body is `str`-coerced where it is built. An injection that survives that is
  a bug.
- **Foreign-format readers are a separate repository.** This tree ships no reader and
  parses no third-party format; `foreign_contract_test.clj` pins that. Parser hardening
  reports belong to
  [`vaelii-foreign`](https://github.com/vaelii/vaelii-foreign/blob/main/.github/SECURITY.md),
  whose whole surface is untrusted input.
- **Language-model credentials** are read from the environment and never stored in a
  KB or a dump. `lein test` makes no model call: a test that could reach a provider
  carries `^:llm`, which the `:all` selector excludes, *and* is gated on
  `VAELII_LLM_LIVE=1`. A path that dials out without both is a bug.

## Dependencies

Runtime dependencies are declared in `project.clj` and resolved by Leiningen; nothing
is vendored except the browser assets inventoried in
[`licenses/THIRD-PARTY.md`](../licenses/THIRD-PARTY.md). Advisories against resolved
dependencies are tracked through GitHub's own Dependabot alerts on this repository
rather than restated here, where they would go stale.
