# Web browser

- **Covers:** what each browser route shows — terms, sentexes, justifications, proof
  trees, the constraint network — and how the editor, assert form and proposal panel
  write through `edit!`.
- **Not here:** which KB sources exist and how one loads or switches →
  [catalog.md](catalog.md); the model that proposes lines for the panel to render →
  [llm.md](llm.md).
- **Assumes:** sentex, context, handle, justification → [glossary.md](glossary.md).

`vaelii.browser.web`. A small [reitit](https://github.com/metosin/reitit)-ring browser for
inspecting a KB. The browser is an application over the public API: the namespaces under
`src/vaelii/browser/` require no `vaelii.impl` namespace, and
`public_api_test/browser-reaches-into-no-impl` fails on one. Run it with `lein run -m vaelii.web` (serves a starter-loaded KB
on `http://127.0.0.1:3000`).

```
lein run -m vaelii.web                            # loopback, a fresh starter KB
lein run -m vaelii.web --port 8080
VAELII_API_TOKEN=… lein run -m vaelii.web --listen 0.0.0.0   # off-machine (opt-in, and required)
lein run -m vaelii.web --attach HOST PORT [WEBPORT]

lein browser                                           # ...or a REPL with it running in it
VAELII_WEB_PORT=3010 lein browser
VAELII_WEB_PORT=3010 lein run -m vaelii.web            # the variable moves either one

scripts/start-vaelii-dev.sh [KB-DIR]                   # lein browser headless, profiler on :8080
scripts/start-vaelii.sh [KB-DIR] [--port N]            # the browser alone
scripts/start-vaelii-server.sh [KB-DIR] [PORT]         # the daemon, token required, no dev profile
```

**`VAELII_KB_DIR` names a KB directory to load at startup.** The browser opens on the
starter, loads the directory as a catalog job with belief recovered (`catalog/load-dir`),
and makes it the active KB when the load finishes; `/kbs` shows the progress until then.
A store is opened with `:recover? :background` **under `VAELII_DEV` only**, so a store whose
reasoning image an earlier engine build wrote is active once that image is installed, and
its belief is rebuilt under the running build behind it (docs/storage.md, "Rebuilding behind
an image") — a development prompt is browsable in seconds rather than after a recover. A
served browser opens with `:auto` and waits for the recover, so the KB it makes active holds
belief this build derived and refuses no write.
The directory is classified as discovery classifies one, so a store, a dump and a corpus
all load. A path holding no KB is logged and the browser stays on the starter. The three
start scripts set it to their `KB-DIR` argument, default `checkouts/kb` beside the
checkout, and set the heap from `VAELII_HEAP` (default `40g`).

`VAELII_WEB_PORT` is the default rather than an override: an explicit `--port` wins. Three
sources are read in order — the variable, the `vaelii.web.port` system property (what a
test sets, a JVM being unable to change its own environment), then 3000 — and a value that
does not parse falls through to the next one rather than refusing to start
([operations.md](operations.md) tabulates both).

`--listen` and `--attach` are independent axes: `--listen` says who may reach the
browser, `--attach` says whose KB it shows. The startup log names the network interface it
took.

**`--listen` naming a non-loopback address requires `VAELII_API_TOKEN`.** Without one the
browser prints a line and exits **2** before it opens a KB; with one, every request to
that bind carries `Authorization: Bearer <token>` or is answered 401. The routes on the
other side are why: `/edit` writes belief, and `/kbs/export` and `/kbs/load` write the
host filesystem at a path the request names. The **loopback** default is unchanged — no
token, no header, no 401 — and the daemon holds the identical rule through the identical
fn ([operations.md](operations.md)).
[why a refusal rather than a warning](defenses.md#what-a-server-binds-decides-what-it-requires)

**The browser also answers the daemon protocol**, `GET /health` and `POST /op`, over its
active KB. A native client such as the vaelii-apple apps connects to
`http://127.0.0.1:3000` with the same requests it sends `vaelii.serve`, and its writes
take this process's `write-monitor` like the browser's own write routes
([operations.md](operations.md), "The browser serves the protocol too").

### Working on it: `lein browser`

`lein run` gives you a page and no way in. **`lein browser`** is `lein repl` with the
browser already running: a prompt, a page, and a **reload channel** —
`(require 'vaelii.browser.web :reload)` at the prompt, or over nREPL through `.nrepl-port`,
reaches the running server. **`scripts/start-vaelii-dev.sh`** adds hot reload: **edit any
source file and refresh**, and the next request serves the new code with no REPL step at
all. The script is the only thing that turns hot reload on — it sets `VAELII_DEV=1` for
`lein browser` — and `start` and `-main` never reload.

That last part is the whole reason the command exists, because the failure it avoids is
silent. **A ring handler is a value, and Jetty holds the one it was started with**, so a
reload can redefine every var on the page and change nothing about what is served — the
namespace reloads, the page does not, and there is nothing to see. `lein browser` serves
through `reloading-handler`, which reads `#'app` per request: a reload gives the
var a new function object, an identity check misses once, the routes are rebuilt, and
every request after that is the new code. What reloads the namespace **from disk** in the
first place is `vaelii.browser.reload` (`hot-reloading`), layered over that handler when
`VAELII_DEV` is set: before each request it reloads the changed files under `src`,
together with every loaded namespace that requires one of them, transitively, in
dependency order. A plain file edit reaches the running server with no REPL, and an
engine edit does too.

**A KB loaded before an engine edit keeps answering after the reload.** Re-evaluating a
`defprotocol` defines a new interface and empties the protocol's extension map, and
re-evaluating a `defrecord`, `deftype` or `definterface` defines a new class. A reload that
reached them would leave the loaded KB's stores, records and belief network instances of
classes the reloaded code no longer recognizes. So the reloader loads a changed file form
by form and **leaves out every form whose protocol or class already exists**; everything
else in the file is evaluated. A record keeps its methods inline — protocol dispatch on it
is a direct interface call, which the engine's hot paths (the belief network, the stores,
the provers) depend on — and a method that calls a function reaches the reloaded function
through its var. An edit inside a record's definition is not loaded, and every page names
it (`ns/Name`) until the process restarts. The protocols and the method-less records sit in
**held namespaces** — `vaelii.impl.types.*`, `vaelii.impl.protocols`,
`vaelii.impl.jtms-protocol`, `vaelii.impl.tokens`, `vaelii.impl.roster`,
`vaelii.impl.settle-phases`, `vaelii.koinii.types` and `vaelii.host.llm.protocol` — whose ns
symbol carries `:clojure.tools.namespace.repl/load false`, which require only held
namespaces, and which the reloader never re-evaluates; an edit to one is named the same way.
The state a watched namespace keeps is in `defonce`. `the-engine-survives-a-reload`
(`public_api_test`) checks that for every watched file, and `reload_test` reloads the engine
under a loaded `:memory` and `:disk-snapshot` KB, checks no class the KB holds was
redefined, and then asserts, queries, explains and retracts against it.

**The reloader loads into the existing namespace, not through tools.namespace's `refresh`.** `refresh`
removes each namespace with `remove-ns` before it loads the file again, which
re-evaluates every `defonce` and empties the state a loaded KB keeps in them: the cache
registry, the change feed's listeners, the thaw guard's installed readers. Loading a file
into the existing namespace, as `require :reload` does, keeps a `defonce`'s value.
A held namespace's `:clojure.tools.namespace.repl/unload false` keeps a REPL `refresh`
(CIDER's included) from removing it; `refresh` still resets the state of every other
namespace it reloads.

(tools.namespace ships in the `:dev` profile only — resolved when the reloader is built,
absent from the served jar, like the profiler.) A namespace the browser merely *calls*
needs nothing beyond that reload — those
calls already go through vars, so a changed `vaelii.browser.svg` lands on the next request
with nothing rebuilt. A served process never reloads: `-main` and `start` serve `app` as
built.

**Both halves are loopback**, and the pairing is why it is not configurable from there
[why](defenses.md#loopback-only-for-the-browser-plus-nrepl-pairing) — the profile pins
nREPL to `127.0.0.1` rather than relying on Leiningen's default, and the browser binds
loopback with no way to say otherwise. Exposing the browser stays the deliberate
`--listen` on `-main`, which starts no REPL.

A port already in use is **reported, not thrown**: you asked for a REPL, and you get one
whether or not the port was free. `(vaelii.browser.web/dev-stop)` takes the server down
without leaving the prompt; `dev-repl` called again replaces it.

`-main` calls `fresh-starter-kb!`, which **clears the record + index stores first**
so each run starts from a clean, deterministic state — re-asserting the starter KB
over stale handles from an earlier run (or an earlier code version) would otherwise
fail. For a *persistent* KB, construct one against existing databases and call
`core/recover` instead of loading the starter. Startup logs go through
[Trove](https://github.com/taoensso/trove) (`trove/log!`), at the level
`VAELII_LOG_LEVEL` or `core/set-log-level` sets and Trove's own console default when
neither does; Jetty's own SLF4J logging is silenced by a NOP binding
(`org.slf4j/slf4j-nop`), so no "No SLF4J providers were found" warning appears — and no
request log either, which [operations.md](operations.md) states as the trade it is.

## Pages

| Route | Shows |
|-------|-------|
| `/` | the **upper ontology**: what the KB is in four numbers, then the genlCx context lattice, the genl type tree (from `thing`), the documented terms (the `comment` sentexes), and its disjointness. Every one of them is **bounded**, and where the whole is too long to read the page shows the top of a ranking rather than the first fifty of an order nobody chose — this is the first page opened against a KB whose size the reader did not choose (below) |
| `/stats` (`?clashes=1`) | **statistics**: headline counts (contexts, types, stored sentexes, and the contradiction / conflict / violation tallies), a contexts-by-size table ranked largest-first, and the actual dilemmas / conflicts / dropped-derivation violations when non-empty — each violation naming the run that dropped it. Every list on it is one screen and continues on scroll. `?clashes=1` additionally asks the **standing disjointness question** (below), which is computed on demand rather than filed |
| `/find?q=<pattern>` | **term search** over the KB's vocabulary: every term whose name matches (`re-find` semantics — a bare `dog` is a substring match, `^parent` anchors), each linked to its term page — the header search box points here. A pattern resolving to a single term (the only match, or an exact-name match) **jumps straight to that term's page** (`HX-Push-Url`) |
| `/term?q=<term>` | a **term**: a drawn picture of where it sits (below), its supertypes/subtypes/disjoint-with (if a type), then every sentex containing it grouped by the **index root** that reaches it — functor `[:functor-root]`, argument-position `[:argument-slot pos]` (the roster the predicate-agnostic read unions the scoped roots over), context `[:context-root]`, and the term-index `[:term-index]` remainder (rules, deeper nestings) — each group carrying its cheap count (O(1) for the roots; one O(1) read per predicate at the slot for the argument groups) |
| `/sentex/:id` | a **sentex** (atomic or rule): its **belief state** (IN, or the `why-not` reason — superseded / defeated / unsupported — with the restatement, contradictors, or missing antecedents that explain it), its supporting justifications (justifications concluding it), its dependents (justifications using it as an argument), and its terms |
| `/why/:id` | the **proof tree**: `vaelii.core/why` rendered whole — every justification down to the premises it rests on, collapsible, cycle-guarded, with rule sentences in the author's variable names |
| `/justification/:id` | a **justification**: its supports/arguments (antecedent sentexes) and its dependent sentex (the conclusion) |
| `/levels?q=<goal>&ctx=<context>` | the **lookup-to-query stack**: what each of the eight levels answers for a goal, which level first does, and — above them — the **query plan**: the provers bearing on the goal with their estimates and which one runs. A **vector** goal is a conjunctive query and gets the join plan instead (below). Links across to `/inference` for the same goal |
| `/inference?q=<goal>&ctx=<context>&d=<depth>` | the **inference debugger**: the run that plan predicted, one step past `/levels`. The **search tree** the node engine builds for a goal — every node the frontier reached (not only the path that answered), each with the itemized estimate that ordered it, the rewrite that produced it, and the answers that came off it — plus the same goal under several **tacticians side by side**, tabled by the work each did and the answers each found. The identity property (every complete tactician returns the same answer set) is **verified** on the page, not asserted: a differing row is marked. Reads through `search-tree` / `compare-tacticians`, both of which bound their own work (a node budget and a wall-clock), so the page holds no session and works under `--attach`. Needs a depth — the node engine's only termination |
| `/network?ctx=<context>&calc=<calculus>` | the **constraint network** a qualitative calculus computes over a context: the tightened matrix (a cell is what still holds of row-to-column), whether the believed facts are satisfiable at all, and one scenario out of it. With no context, the six calculi and their vocabularies |
| `/demo` (GET/POST) | the **non-monotonicity walkthrough**: three stepped writes to the reader's sandbox in which `(hasCapability Pingu flying)` is believed, stops being believed, and comes back — at a different handle. GET renders where the sandbox stands, POST runs one step. Every step writes, so every step is origin-checked (below) |
| `/reasoning` (GET/POST) | the **worked examples**: every kind of inference the shipped ontology performs, each a question with a live answer, the level that answered it, and links to the stored sentexes it reasoned from. GET computes every read-only card on render; POST establishes one example's premises in the reader's sandbox (below) |
| `/assert` (GET/POST) | the **new-sentex form**: sentences (one per line), a context, and the known-true switch. GET seeds it (`?q=<term>` from a term page); POST checks every line and applies them in one `edit!`, then says what followed (below) |
| `/edit` (GET/POST) | the **sentex editor**: GET seeds it for a set of handles (`?handles=1,2`) or for a term's most direct index group (`?q=<term>`), POST checks and applies the save. htmx fragments swapped into the editor panel, not standalone pages. |
| `/edit/preview` (POST) | what the open edit would do, through `vaelii.core/preview` — the same diff the save computes, and a read: the KB comes back at the same handles. Fills the lookahead under the editor's controls |
| `/complete` (GET) | the terms a prefix could become, as the list the editor drops under the caret. `find-terms`' prefix match over the term roster, twelve at a time |
| `/propose` (GET/POST) | the **proposal panel** at the foot of a term page: GET renders the instruction box (asking no model), POST runs one page-scoped turn through `vaelii.host.llm.session/propose-page` and swaps the lines it proposed into `#propose-result`. The turn writes nothing (below) |
| `/propose/level` (POST) | the **same proposal at another density** — the list's own originals reposted, every verdict re-derived, no second model turn. Writes nothing |
| `/propose/line` (POST) | one reviewed line, **re-rendered on the form the reader picked** — the numbered alternative is re-derived from `correct` and re-checked, so the chips are of the sentence that would actually be stored. Writes nothing |
| `/propose/preview` (POST) | what accepting the accepted lines would **mean** — the belief added, the belief withdrawn, the dilemmas opened, the refusals — through `vaelii.core/preview`. Writes nothing; the KB comes back at the same handles |
| `/propose/apply` (POST) | the accepted lines, checked whole and stored through `vaelii.core/edit!` in **one settle**. The panel's one write |
| `/retract` (GET/POST) | the **retract confirmation**: GET previews the teardown (the named handles and what the sweep would take with them) and writes nothing; POST performs it |
| `/chain` (POST) | run **forward chaining** as a job, up to the derivation bound the form names, and answer with the `/stats` page it changed — or, when the run outlasts 250 ms, with `/jobs` (below). POST-only: it derives and places conclusions |
| `/funnel` (GET/POST) | the **chaining funnel**: every forward rule and what chaining did with it — how many firings it **placed**, how many it **refused** and why (`exception` / `naf` / `post-join` / `hidden`), or whether it stayed **silent** (no antecedent set ever completed). Ranked by what is wrong: no-placement rules first, refusals descending, firing rules last; each rule links to its sentex and carries the `violations` it filed. The per-rule breakdown behind `/stats`' headline, read `O(rules)` off the standing refusal ledger and the justification graph — no per-run instrumentation. GET reads the current state; POST runs the same chaining job as `/chain` but lands back here so the funnel fills in front of the reader |
| `/jobs` | the **jobs screen**: every long run this process has made recently — a load, an export, a chaining run — with where it has got to, what it left behind, and the one control that stops it (below) |
| `/jobs/rows` | the job list, on the same self-terminating poll as the KB panels, carrying the header's running count as an out-of-band swap |
| `/jobs/cancel` (POST) | **stop** a running job at its next progress report. A write to this process's registry rather than to a KB, so it is origin-checked but not behind `writing` — cancelling a job has to stay reachable *because* one is running |
| `/kbs` | the **knowledge bases**: what is loaded (with counts, an estimated footprint, and a progress bar for one still loading) and what can be — the shipped ontologies, a generated corpus with a slider per parameter, and every corpus / dump / store the catalog found. See [docs/catalog.md](catalog.md) |
| `/kbs/load`, `/kbs/unload`, `/kbs/activate` (POST) | **load** a source, **unload** an entry (cancelling it if it is still loading), **switch** to one. Each changes what this process holds, so each is a write: POST-only and origin-checked |
| `/kbs/export`, `/kbs/export/cancel` (POST) | **write the active KB out** as a portable dump — a destination directory, the variant and the compression — and **stop** one that is running. POST-only and origin-checked, like every other write |
| `/kbs/rows` | the loaded-KB panel, refetched once a second **while a load is running** — the trigger is in the answer, so an idle page stops asking |
| `/kbs/export/rows` | the export panel, on the same self-terminating poll: the last job's report, and whether what it wrote is now offered under **Available** |
| `/kbs/banner` | the **provisional-KB strip** every page carries when the KB it reads is not finished (below). Like the memory strip it is a read of the *process* and swaps only itself; it answers with the empty element once there is nothing to say, which is what stops the polling |
| `/sandbox/reset` (POST) | **discard this session's sandbox** — every sentex in it and the `genlCx` edge that made it a context. The only control in the browser whose purpose is to destroy knowledge, so POST-only and origin-checked |
| `/caches` | what this **process** is holding beside the stores: every cache the engine keeps, its bound, its unit and — where anything counts them — its hit rate, plus the heap strip below reused rather than redrawn, and the profiler. A read of the process, so its numbers are O(1) apiece and it can be left open (below) |
| `/caches/rows` | the cache table, on the same self-terminating poll as the KB panels — it asks only while a job is running, which is when these numbers move |
| `/caches/clear` (POST) | **drop the derived caches** and say what went. Origin-checked like every write and deliberately not behind `writing`: it moves no belief, holds no writer, and is the one control here meant to be used *while* a load runs |
| `/kbs/memory` | the **memory strip** heading that panel, collapsed or (`?detail=1`) expanded into the per-KB breakdown. A read of the *process*, not of a KB, so it takes no view. Two requests reach it and they are different requests: the header line **toggles** (it asks for the state the panel is not in), while the panel **refreshes** at the state it is in, and only while a load is running — one element carrying both would poll the toggle and flip the breakdown open and shut every tick |
| `/tree/rows?rel=<genl\|genlCx>&node=<term>` | one **level of a hierarchy**: that node's direct children, fetched the first time its disclosure is opened, and paged like any other list. `rel` reaches the index as a functor, so it is checked against the two transitivity relations rather than trusted |
| `/term/rows`, `/find/rows`, `/levels/rows`, `/front/rows`, `/stats/rows` | **continuations**: one more page of rows for a capped list. Not pages — bare `<li>`s a list's sentinel fetches for itself (below). The last two take a `?section=` naming which list on the page is continuing |

Everything is cross-linked: terms → sentexes → justifications → terms, any sentex can
be traced through the stack, and any believed one has its whole proof a click away.

### A term's shape, drawn

A term page lists what the KB was told about the term — the `genl` sentexes, the facts it
takes part in, the rules that conclude about it — a row at a time. What a list never gives
is **position**: that `dog` sits under `mammal` under `animal`, that four things point at
it and it points at two, that it is a leaf or a hub. That is what a picture gives for free,
so a term page opens with one, above the rows.

**It renders live.** Server-drawn into the page, no click, no route, no state saying
whether it is shown
[why not a reveal button](defenses.md#the-term-graph-renders-live-not-behind-a-reveal-button):
the reads are nearly all ones the page already made (the relation flank comes off the
index groups it built, and the taxonomy is probed only in a direction the closures it
already read say has something in it), and no route means no `show=0`, no
collapsed-versus-expanded fragment, and no second entry point rendering the same thing
with different chrome. The whole feature is one function called from one place.

Being live is also what obliges the budget. **A picture nobody asked for may never be the
reason a term page is slow**, so the bound is part of the work and not a follow-up:

- **The graph adds at most 24 facade reads**, ever — twelve expansions, six per side, plus
  one O(1) count per row that actually elided. The radial view spends six. Every expansion
  is `(take (inc cap))` over a lazy pattern that pins an argument, so it costs the node's
  own fan-out and nothing more.
- **Measured** twice. Over the shipped schema plus the test-world cast: **2–10 reads** and
  **0.7–2.9 ms** a page (`dog` +3 reads / +0.7 ms, `animal` +10, a synthetic 5,000-subtype
  hub +9 / +2.9 ms). Over a generated 148k-sentex corpus — 44k terms, 4k types — a type
  page costs **+0.4 to +0.8 ms**, and the five widest individuals in it, up to ~12k
  incident facts each, cost **−0.4 to +2.5 ms**: inside the run-to-run noise of the page
  they sit on. A hub with 400 subtypes costs exactly what one with 40 does (`web_test`),
  which is the claim a render cap alone would never make.
- **Degrade, never defer.** A side that runs out of budget stops a row short and the
  caption says so. There is no fallback to a button.
- **Nothing new to reach it.** No route, no dependency, no access op — so the graph renders
  identically against `--attach`, and `docs/web.md` needs no row in the table above.

**Three outcomes, chosen by the term's own structure.**

- **Top-down**, when the term has subsumption structure. It sits in the middle; supertypes
  are rows above, subtypes rows below, and vertical position *is* the subsumption relation
  — every vertical arrow points at the more general term. Three hops up (enough to show
  where a term sits; past it the rows stack near `thing`), two down (subtype fan-out is
  wider than supertype fan-in), eight nodes a row, three per node past the first row so a
  row spreads across its parents. Non-subsumption relations flank it: things that point at
  it on the left, things it points at on the right, so the two kinds of edge are never
  confused for one another.
- **Radial**, when it has relations and no subsumption structure — an individual. The term
  at the origin, its neighbours on a ring whose radius is computed from the widest label so
  eight long names spread instead of overlapping, and the first three of *those*
  neighbours' own relations on short arcs outside them.
- **Nothing.** No structure, no relations: no picture, no empty frame, no "no graph
  available" box. The page renders as it otherwise would.

**A term is a context or it is not.** `genl` relates types and predicates, `genlCx`
relates contexts, `wff` refuses the mixture, and the naming invariants keep the two
vocabularies apart — so there is exactly one subsumption relation per term page and the
class on its edges says which. That is also what makes a context page worth opening: `genl`
says nothing about contexts, so the picture is the only thing on the page that shows the
lattice at all.

**What is and is not an edge**, stated rather than left to fall out of the code. Binary
facts only — a ternary `(arg parentOf 1 person)` relates three things and an arrow
between two of them drops the position it was about. Positive only — `(not (P a b))` says
the relation does not hold and an arrow says the opposite. **Believed** only, like the `/`
trees, which is why a defeated edge leaves the picture while its row stays in the list
below, dimmed. Symbols only — a number, `comment`'s text and a compound in argument
position are terms of a sentence rather than nodes of a graph. And **one node per term**: a
neighbour reached by two predicates is one node whose edge names both, because a node per
*fact* would put two `Ann`s on the page where the KB has one — the same defect drawing an
edge once per asserting context would be. One edge in two contexts is one edge; the graph
is not context-scoped and does not label an edge with a context.

**It says what it left out**, with the count, in a caption under the picture: *showing 8 of
up to 5,000 direct subtypes*. A truncated picture that does not announce itself is worse
than no picture and worse here than in a list, because a picture reads as complete. The
count is **exact** where the row was small enough to be read whole, and the
argument-root bound otherwise — an over-count across every binary predicate at that
position — which is why the wording differs. The centre term is never subject to a cap: a
stated root that is not drawn reads as orphans.

**Drawn with no library.** `vaelii.browser.svg` is a node, an edge, an arrowhead and the
arithmetic that lays out a row, a column or a ring — pure, KB-free, tested on hand-built
maps. No Graphviz shell-out (a page that renders by starting a process is a page that
cannot be served), no d3, no cytoscape, no build step, and nothing added to `project.clj`:
the client is two JavaScript files and a graph library would be the largest thing in it.
Node colour is `term-class`'s class resolving to the same `--t-type` … `--t-context` custom
properties the links beside it use, so the picture is theme-aware for free and cannot drift
from the text. Every node is an `<a href="/term?q=…">` — the graph is navigation, not
decoration — and clicking one is the whole interaction model: no pan, no zoom, no drag, no
physics.

**The text stays.** Every term the picture draws is a row in the index groups under it —
the `genl` sentexes an argument group lists are the edges it drew — so the rows are the
accessible equivalent of the picture and the exact answer it approximates. The `<svg>`
carries `role="img"` and an `aria-label` saying what it shows and that the same terms are
listed below as text. And the whole thing is wrapped: this is the
one part of the page that does arithmetic on KB-derived numbers, so a throw costs the
figure and nothing else — the page is still 200 and still complete.

### Somewhere safe to be wrong

Every browser session gets a **sandbox**: a scratch context of its own, hung below
`CxWell`. `vaelii.browser.sandbox`.

The asymmetry is the whole design, and it is not a permission check. `genlCx` already
decides what a context can see; hanging the sandbox at the bottom of the spindle means
everything shipped flows *in* — every type, every relation, every rule is usable — and
nothing flows *out*, because no shipped context names it. A reader can therefore be wrong
in any way they like without touching the ontology.

That also places the derived content correctly for free: a shipped rule firing over sandbox
facts concludes **into the sandbox**, because placement is the maximal common descendant of
the rule's context and the antecedents' ([contexts.md](contexts.md)), and the sandbox is the
only context below both. So a conclusion the reader never wrote is inside the thing they
can discard, with nothing arranging for it.

- **The context is created on the first write, not the first page.** A session token is
  minted into a cookie by `wrap-session` on the first request, but it only *names* a
  sandbox; `sandbox/open` is what creates it, and only a write calls it. A reader who
  merely looks costs the KB nothing.
- **The token is validated on the way in.** It is interpolated into a symbol, so a
  crafted cookie naming a shipped context would write straight into the ontology. Only
  the hex `mint-token` produces is accepted.
- **The assert form defaults its context to the sandbox**, so writing somewhere safe is
  what happens when the reader changes nothing. It is a default, not a lock: the field is
  editable, and anyone who knows they want `CxNaturalWorld` can type it.
- **Reset is a real teardown**, not a flag — every sentex in the extent through `edit!`'s
  `:remove`, then the `genlCx` edge, which is not in the extent because
  `genlCx` is forced-decontextualized and therefore stored in `CxUniverse`. The
  dependency-directed sweep takes the derived conclusions and their justifications, so the
  KB comes back to its pre-session sentex *and* justification sets exactly.
- **It appears in the chrome as a place, never as a context picker** — a `Sandbox` nav
  item leading to the assert page, which names the context and offers the reset.

Promotion — moving something out of a sandbox into a context that outlives it — is
deliberately absent. A dead end that cannot be half-escaped is easier to reason about than
one with an entry point in it.

One limit: a session cookie that is dropped (the browser closed) leaves its
sandbox in the KB with nothing pointing at it. For the default browser, whose `-main`
clears and reloads the starter each start, they cannot accumulate; against a persistent KB
they do, and nothing collects them.

### Belief that changes

`/demo` is the one page that argues rather than reports. Three clicks, in the reader's own
sandbox:

1. assert `(bird Pingu)` — `(hasCapability Pingu flying)` becomes believed, and nobody asserted it
2. assert `(penguin Pingu)` — `(hasCapability Pingu flying)` stops being believed, and nobody retracted it
3. retract the penguin claim — it is believed again

Nothing about the page is special-cased in the engine. Each step is an ordinary `v/edit!`
against the sandbox, the page is re-read from the KB *after* the write rather than rendered
from what it intended, and every handle on it links to the record it names — which is the
whole point, since the claim being made is that this is the engine and not a story about
one. Which step is offered comes from the KB too (`demo-state` reads what is stored), so a
reader who reloads, navigates away, or resets lands on the line that is actually true.

Two things it is careful to show rather than assert:

- **The cascade.** All five sentences the script touches are rendered at every step. A
  stored one shows its record and its live belief pill. The capability hierarchy answers
  `(hasCapability Pingu travelling)` at retrieval and stores no record, so its row shows
  what `ask?` answers: answerable in step 1, unanswerable once the flight goes in step 2,
  and answerable again in step 3. `(not (hasCapability Pingu flying))` appears in step 2 —
  the KB does not merely fail to conclude flight, it concludes flightlessness, which is a
  different statement.
- **The returning conclusion is a new record.** `exceptWhen` blocks rather than rebuts, so
  the blocked justification is *invalid*, groundability goes with it, and the
  dependency-directed sweep deletes the conclusion outright ([exceptions.md](exceptions.md)).
  Revival is therefore a re-derivation: step 3's sentex has a handle that never existed
  before, and step 1's handle resolves to nothing. The page names both side by side and
  links the new one, because that is the sharpest evidence on it — the engine did not hide
  the conclusion and put it back, it forgot it and re-earned it, and the proof being
  identical while the record is not is a thing a slideshow could not fake.

The individual is the only content the demo creates; the rules are `CxBiology`'s
shipped ones. Step 2 reads `why-not`'s **sentence** arity, which exists for exactly this
case: a blocked conclusion has no handle to ask about.

### What the ontology can work out

`/demo` argues one thing at length. `/reasoning` is the breadth: a card per kind of
inference the shipped ontology performs, each a real question with the answer the KB gave
when the page was drawn. The table is `vaelii.browser.examples`; the page is the rendering of
it.

Two properties keep it from being a brochure, and both are required:

- **Every card names the sentexes it reasons from**, and those are looked up (`handle-of`,
  find-*without*-create) before anything is claimed. So a card is *linked* to its
  dependencies rather than describing them, and on a KB that does not hold them — the
  catalog will happily activate OpenCyc — the card says **not available** instead of
  answering from vocabulary that is not there.
- **Every card declares what the ontology is supposed to answer**, and `examples_test`
  asserts all of them against the real KB. The ontology is edited far more often than the
  page is, so a rule removed or a declaration dropped turns a test red rather than leaving
  a card that confidently states a verdict the KB no longer gives.

The verdict names the **level** `escalate` stopped at, and the level *is* the claim: 3 is
context inheritance, 5 a cached closure, 6 the prover stack, 7 the rule chainers. A closure
answer carries **no handle** — nothing was materialized to reach it — and the card says so
rather than leaving a gap where a proof link would be; a derived one links its proof.

The split between the two kinds of card is about what the KB ships, not about
presentation. The starter is schema, so everything asked **of kinds** — the taxonomy,
`transitiveInArg`, disjointness, the predicate meta-ontology — is answerable with no write
at all, and those cards are computed on render. `looking-at-the-gallery-writes-nothing`
holds that: rendering three times leaves the sentex count identical. The cards that need
**individuals** bring their own and write them into the reader's sandbox on an explicit
click, one at a time.

One hazard worth naming, because it is the way a gallery like this rots: the reader's
sandbox holds every example they have run *at once*, so two cards sharing an individual
can silently falsify each other — establish a card that kills the animal another card says
is alive, and the second card starts contradicting its own text.
`the-examples-do-not-interfere-with-each-other` establishes every example first and only
then asks, which is the order the page actually creates.

### What followed from a commit

Both commit paths — the assert form and the proposal panel — write through
`v/edit-with-consequences!` rather than `v/edit!`, so each can end with the thing a commit
otherwise leaves unsaid:

> **You didn't say this, but it follows**
> `(mortal Muffet)` — because `(dog Muffet)` and the rule `(implies (living_thing ?x) (mortal ?x))` · _proof_
> `(mammal Muffet)` — because `(dog Muffet)`, and every `dog` is a `mammal`

Those two lines come from **different mechanisms**, and the callout keeps them apart rather
than blurring them into one list of "conclusions":

- a **rule fired**. There is a derived sentex with a justification, so it is believed in
  the JTMS sense, has a handle, and its whole proof is one click away. The `because` names
  the antecedent that actually matched and the rule — which is why the example above reads
  `(dog Muffet)` against a rule about `living_thing`: the match fanned out over the genl spec
  closure, and showing the matched antecedent is showing what happened.
- a **type subsumes**. `(genl dog animal)` plus `(dog Muffet)` makes Muffet an animal, and the
  engine deliberately never materializes `(animal Muffet)` — matching fans the functor out
  over the spec closure instead, which is what lets a hundred million facts avoid a hundred
  million more ([taxonomy.md](taxonomy.md)). So there is no record, no justification and
  nothing to link; the claim is answered on demand by `isa?` / `ask`. Calling it "derived"
  would teach a first-time reader something false, and the first thing they would do is go
  looking for the record.

Supertypes are listed nearest-first, `thing` is dropped (true of everything, informative
about nothing), and anything the same batch stated outright is left out — the reader wrote
it. Capped at three with the rest counted; a commit that derived nothing renders **no
callout at all**, because a box reading "0 new conclusions" makes the boring case as loud
as the interesting one.

### Reading a KB that is not finished

Any entry holding a KB can be the active one, a load still running included
([catalog.md](catalog.md)) — a corpus is browsable from its first thousand sentexes, and
a store that opens in seconds is browsable while `recover` rebuilds belief behind it. The
catalog's job is to allow that; the browser's is to make it honest, which is one element:

**`caveat-banner`**, at the top of `#main` on **every** page. Not in the header, because
`#main` is what every navigation and search swaps — put it in the chrome and it would
state the KB's condition as of whenever the document was first served. While a load runs
it polls `/kbs/banner` and swaps itself; when there is nothing left to say the endpoint
answers the empty element, which is what stops the polling, exactly as the entries list
and the memory strip do.

It reports the two conditions separately, because they are independent and the second is
the one that lasts:

- **A prefix.** The load is still running, or was cancelled, or failed. Everything on the
  page is drawn from what is stored *now*, so a term that has not arrived yet reads as
  absent — which is what an absent fact always means here, and never as false. This is
  the ordinary open-world condition, so the strip is deliberately not styled as an error.
- **No belief and no taxonomy.** With no truth-maintenance network every *believed*
  answer is empty; with no genl closures there is no type hierarchy, so `/` renders a
  fully stored KB as one holding no types and no contexts at all. That is the trap worth
  a banner: it is reachable with the job `:done` — a store opened without `:recover?`, a dump
  imported with `:belief? false` or `:belief? :stored` — so nothing about the KB's status
  hints at it, and a reader's obvious conclusion is that the import failed.
- **Belief from an earlier build.** A store opened with belief installs the image an
  earlier engine build wrote and rebuilds belief behind it. The banner says so while the
  rebuild runs, polls, and leaves the page when the rebuilt belief lands; a write in that
  window renders the "rebuilding belief" refusal instead of the "not recovered" one.

  The bullet ends with the repair, and **which repair depends on the store rather than on
  how it got here**. A KB holding justifications or premise marks needs a `recover` and
  nothing else, which is one pass over what is already stored. One holding neither has to
  be loaded again, because there is nothing for a recover to believe from — the state
  `:belief? false` leaves a foreign dialect in. The banner reads `:recoverable?` off the
  store and says the one that applies; telling the first case to reload would cost it the
  whole load a second time.

**And the second condition is read-only.** The banner explains an *answer*; a write into
the same state is a different matter, because an answer can be re-asked and a record the
store keeps cannot be taken back. Every definitional check the assert entry point runs — arity,
arg, genlArg, interArg, declaration consistency, disjointness, functionality,
asymmetry — reads `jtms/in?`, so over an empty network all of them match nothing and pass
vacuously, and nothing re-runs them afterwards: `recover` does not, and its closing settle
binds `settle/*rebuilding?*`, which turns the exposure pass off. So a KB in this state
**refuses writes by name** (`:unrecovered-kb`), naming the same repair the banner does —
`recover`, or `reindex` when the index is derived and so opened empty, which is also the
state in which every assert mints a second handle for a sentence already stored.
`vaelii.core/*write-unrecovered?*` is the opt for a caller who wants them anyway and has
read what it gives up. This is the browser's own rule one layer down: the caveat tells a
reader what is provisional, and `writing` below refuses the write rather than caveating it.

The entry cards on `/kbs` name what switching gets you rather than offering one button
for two different answers: *Switch to* for a finished KB, **Browse as it loads** for one
still arriving, **Browse what landed** for one that stopped part-way — which is usually
the reason to have stopped it.

**The reads open, the writes refused.** A KB can be read while a job fills it; it cannot
be *written* while one does. A store mutation lands atomically, so a reader beside the
job sees a consistent prefix — but two interleaved writers are not serializable at
all ([storage.md](storage.md), the single-writer contract), and the job is already
this process's writer. `write-refusal` asks a third question beside that one and the
origin check, and it is the banner's second condition arriving here: a KB whose belief
was never built is refused too, because the engine's entry points throw `:unrecovered-kb` for
one and a route that let the exception out would answer an error status — which is the
silent no-op the whole page shape exists to avoid. So every route that changes a KB's
content goes through **`writing`**: `/assert`,
`/edit`, `/retract`, `/demo`, `/reasoning`, `/sandbox/reset`, `/propose/apply` — and
`/propose/preview`, which reads by really asserting and rolling back, and is therefore a
writer for the duration. `/chain` and POST `/funnel` go through **`writing-job`**, the same
guard for a write that *is* a job (below); the two submit the same chaining run and differ
only in the page it lands on. `/kbs/load`, `/kbs/unload`, `/kbs/activate` and
`/jobs/cancel` are **not** guarded: they write this process's registry rather than a KB,
and cancelling a job has to stay reachable precisely *because* one is running. `/kbs/unload`
still hands `catalog/unload!` the write monitor, because *releasing* an entry is the end of
a KB's stores: a synchronous write already past the write entry points has to drain before they go
rather than interleave with the clear, exactly as the export route's does.

`/kbs/load` is the one KB write that runs outside this monitor altogether, and that is
deliberate: a loader opens brand-new stores nothing else can name yet, so there is no KB on
screen for it to interleave with, and its `:writes` claim in the job registry is what keeps
it the only writing job for as long as it runs.

The refusal renders as a **page**, not an error status, for the reason a catalog refusal
does: an error status leaves htmx not swapping at all, so the write would look like it
silently vanished. It **names the job holding the writer** and links to it, since
"something else is writing" is not an answer a reader can act on. The check is narrow on
purpose — it asks about the KB this request would actually write, so loading a second KB
in the background never stops you writing to the one on screen.

**And it names the KB it judged**, which is not the same as naming the active one. The
entry point derefs the holder once and hands that KB to the refusal and to the write, precisely
because `/kbs/activate` can re-point it at any moment — so the entry that is active by the
time the page renders is the one KB the refusal can be sure it is *not* about. Every arm
reads the resolved KB's own name.

`/kbs/export` is not guarded either, for a third reason: it writes the *filesystem*
rather than a KB, so a load filling some other KB is no reason to refuse it. What an
export cannot survive is the KB it is walking being written, and that exclusion runs
both ways: `catalog/export-entry!` refuses to start while a loader writes the KB, and
while the walk runs `write-refusal` refuses the write routes for that KB
(`catalog/exporting-kb?`, asked by identity — the job claims no writer, so the claim
registry cannot answer for it). The export job also takes the write monitor before it
walks, so a synchronous write already past the refusal drains first rather than
interleaving ([catalog.md](catalog.md)).

It takes it as a **barrier** and not as a hold, which is where it parts company with a
chaining job. A chain writes the KB, so it keeps the monitor for its whole run and every
synchronous write waits. An export writes no KB, and both `write-refusal` and `unload!`
already refuse for the walk's whole duration — so the only thing left to wait for is the
write that slipped past an entry point in the moment before the job was submitted. Holding it
across the walk instead parks every later `/kbs/unload` on a Jetty worker for the length
of a multi-minute dump, with no page and no progress, on ring-jetty's default pool of 50.

### A parameter the page cannot read is a 400, not a default

A request parameter arrives as a string, and reading an unreadable one as "absent" gives
every route a *second* meaning for a typo — one it then acts on without saying so.
`?max-derivations=abc` is the sharp case: absent, that parameter means **no bound**, so a
mistyped one ran the fixpoint unbounded. `?d=abc` took the search page's default depth,
`?calc=rcc9` drew a different algebra's matrix under the name that was asked for, and the
assert form's `strength` was tested for presence alone, so any value at all — including
`default`, which a caller could send meaning the opposite — asserted `{:strength
:monotonic}`.

So each is validated and each refusal is `bad-parameter`: **400**, rendered as a page (the
chrome is how a reader who hand-edited a URL gets back), naming the parameter, quoting the
value and saying what would have been legal. `?d=` is held to the range its own form
declares — `debug-depth-max`, the number the `<input max>` is written from — because a form
offering 12 beside a route accepting any depth is a control that describes nothing. An
*empty* control is the control not being submitted, and still takes the default: what is
refused is a value, never an absence.

`/levels` and `/levels/rows` refuse one more thing, and it is a value their own context box
will send: a **query context**. `CxEverything`, `CxInference` and `CxNothing` are readings
rather than places ([contexts.md](contexts.md)), and the levels read through entry points that do
not resolve one — so the engine answers `:unsupported-context`, which this handler stack
has no exception middleware to render, and Jetty answers 500. Checked before the read, it
is the same 400 page, naming the context and the three that are not places. The fragment
route answers it too rather than an empty list: htmx swaps only a 2xx, so a reader
scrolling keeps the rows they had.

`&offset=` is the other one, and it is capped rather than refused. A continuation cursor is
*arithmetic* — `/find/rows` asks the term roster for `offset + find-cap + 1` names — so an
unbounded one overflows that addition into an `ArithmeticException` and the same 500. One
ceiling in `->offset` covers all six continuation routes, a billion rows past anything a
sentinel writes. An offset past the end is not a bad request but a cursor pointing past the
last row, and the honest answer to that is the empty page it already gives.

## Long work as jobs

Three things here take minutes rather than milliseconds — filling a KB from a corpus,
writing one back out, and joining every rule over everything stored — and they are **one
mechanism** (`vaelii.browser.jobs`) with one status vocabulary, one progress reading and one
cancel. `/jobs` is that registry rendered; the `/kbs` panels are the same registry
filtered to the two kinds that belong beside a KB, which is why neither is a second list
of anything.

    :running → :cancelling → :done | :cancelled | :failed

`:cancelling` is the honest middle. `jobs/cancel!` sets a flag and returns; the work stops
at its next progress report, which for a phase that reports none (opening a large store
scans its whole record log before it says anything) can be a while. An entry on `/kbs`
wears its load's status, so the two never disagree about what a load is doing.

It answers **whether there was a run to stop**, which is not the same question as whether
the registry still holds the id: a settled job keeps its report there for an hour, so the
reader who clicks stop the moment a run finishes gets false, and `/jobs/cancel` says
nothing happened rather than reporting a cancellation over work already done.

**The 250 ms fast path is the detail that makes this usable.** A job that settles inside
`jobs/fast-path-ms` is answered with its *result* — `/chain` on the shipped schema still
answers with the `/stats` page and its derivation count, exactly as it did when it was a
synchronous request. Only a run that outlasts the window is answered with the jobs screen.
Without it every small operation acquires a spinner and a second round trip, and a tool
where that is true feels slower than the one it replaced.

**A job outlives the request that started it**, and that is the point: closing the tab
cancels nothing, and reopening `/jobs` finds the run still going. The list is watched by
the same self-terminating htmx poll every other panel uses — which survives a reload,
where a socket does not — and the header carries the running count as an out-of-band swap,
because the header sits outside the region a swap replaces. A finished job's report stays
for an hour, which is long enough to read what it did. Nothing **unsettled** is dropped, at
any age: forgetting a job releases its writer claim, and a thread that is still running is
still writing. So a wedged job keeps its place and keeps counting — the badge saying a
thread will never return is the truth about the process, and better than a store two
writers took turns on.

**One job writes at a time, and the second is refused rather than queued.** A load and a
chaining run each claim this process's writer, so a chaining run while a corpus loads is
refused with the holder named — a queue would make the second one's timings mean whatever
was in front of it. An export claims nothing: it writes the filesystem, so it runs beside
either. What stops a *request* interleaving with a job is `write-refusal`, above; what
stops two jobs interleaving is the claim.

**Cancellation never interrupts a job that writes a KB.** A thread interrupt landing
mid-cascade on a durable store surfaces as `ClosedByInterruptException` and can leave a
torn write, so a KB-writing job is flagged and left to notice, however long that takes.

Where a job *is* interruptible — one that writes nothing and says so — the interrupt is
fenced at both ends, because a job runs on a **pooled** thread and `cancel!` decides from
one read of the registry. The job's body publishes `:released` under the job's own monitor
as it unwinds, and `cancel!` re-reads it there: past that point the thread belongs to the
pool, and an interrupt sent then would land on whatever ran next — a task nobody cancelled,
unwinding on somebody else's request. The other end is the caller's: the bounded wait for a
job to publish its thread is itself interruptible, and clears the *canceller's* flag on the
way out, so `cancel!` restores it and answers rather than letting an
`InterruptedException` out into the handler that asked.
What a stopped run leaves is stated where the run is started: a cancelled chaining run
leaves the conclusions it had already placed, a cancelled load leaves the sentexes that
had already landed, and neither is a corrupt KB — it is the ordinary open-world prefix.

And the card says **how much** landed, because a stopped job has no summary to say it
with: it never reached its return value, so its last progress reading is the only account
of what is in the KB, and it is shown as a count reached rather than as a bar still
filling.

## Writing a KB out

The Export panel on `/kbs` is the return leg of the loop the Available list is the
outbound half of. It writes the **active** KB as a portable dump — a destination
directory, the variant (`records` or `records+index`) and the compression — as a job, so
the page keeps answering and the panel polls itself only while there is something to
watch. The report it shows is the registry's newest export job rather than a slot of its
own.

Two things it says that a bare progress bar would not. A finished job reports **where the
dump went and whether the catalog can see it there**, asked of `catalog/sources` rather
than assumed: a dump written outside `VAELII_KB_PATH` is a perfectly good dump this page
will never offer, and silently not appearing under Available is the confusing outcome. And
when the active entry is an **attached daemon** the form is replaced by a sentence saying
so — its dump would be written on that daemon's host, and a path field that quietly named
a directory on the wrong machine is the one failure mode here worth designing out.

## What this process is holding

`/kbs` measures **heap** and says exactly what kind of number that is: `catalog/memory`
reports the JVM's `{:used :committed :max}` as a measurement and each loaded KB's
`footprint` as an estimate, kept visibly apart because attributing heap to one of several
resident KBs would mean unloading it and diffing. `/caches` is the other half of the same
question — not what the stores cost, but what the engine holds *beside* them so a repeated
question is not recomputed — and it reuses that strip rather than drawing a second one.

The rows come from **one read**, `v/caches`, over a register every cache-holding namespace
declares itself in at load. Four things about a row, and each of them is there because its
absence would mislead:

- **`:scope` and `:counters` are separate**, and the literal cache is why. Its entries are
  this KB's and its hit counters are global `AtomicLong`s across every KB in the process,
  since they measure the mechanism rather than a store. The page renders the second as
  *rates: this process* under the first; without that, a reader takes another KB's work
  for this one's.
- **`:unit` is on every row.** One cache counts literals, another networks, another
  symbols, another records — a column of bare integers over the four compares nothing.
- **A blank entry count is a cache, not a gap.** The scope-bound ones — the stored-handle
  map, the search step's neighbour memo, the justification dedup index — are built inside
  one run and dropped when it returns, so there is nothing for a page to read between
  them. They are listed with the reason rather than left off, because a list that quietly
  omits them says the engine holds nothing else.
- **A cache in a namespace this process never loaded has no row at all.** No metric-time
  reasoner, no metric-closure row — which is the honest answer, where a row of zeroes
  would claim a cache exists that does not.

A KB also carries derived state that is deliberately **not** on the page, because it is
not a cache: the memory of a firing the chainer refused, the set awaiting a re-check, the
disjointness and negation ledgers, the reference counts that keep the rule index O(1).
The test is whether the engine could recompute an entry from what is stored — a cache
could, and each of those could not, so dropping one would change an answer rather than
cost a recomputation. The page says so, since a reader who knows they exist and sees no
mention of them cannot tell an omission from a judgement.

Every limit on the page is a **wholesale clear** rather than an eviction: past it the
cache is emptied and refilled by demand, because evicting exactly the right entry costs
more bookkeeping than the entry saves. That is the policy worth being able to watch — a
workload oscillating around a limit pays a full rebuild every time it crosses.

**The clear is a measuring instrument.** Clear, ask the same question again, and watch the
miss the second ask no longer gets to skip; nothing is destroyed, since every entry is
derived. So it is POST and origin-checked like any other write and is deliberately *not*
behind `writing` — it moves no belief and holds no writer, and a reader most wants it
while a load is running. It leaves the structural caches alone (the symbol pool, the
compiled relation algebras), and the page names which those are by asking the rows rather
than by hard-coding them.

**A clear reaches the KB it was pressed on, and no further.** The scope split is not only
a rendering question: a row whose rates belong to the process keeps them through a clear —
the entries dropped are this KB's alone, and the hit and miss counters every other KB's
page is reading keep running, since they are a measurement a second reader may be partway
through. The literal cache and the closure neighbours are those rows — their entries go for
this KB alone (or for the step holding them), their counters belong to every KB — and no
other KB loses an entry, a counter or a belief. Zeroing
the process-wide rates is `clear-caches`' `:counters?` option, which the button does not
pass. The page says which rows those are the same way it says which are left alone, by
asking the rows for `:clearable?` and `:counters` rather than by naming a cache in prose
that would outlive it.

**A row that cannot be read says so.** The register is open — any namespace may declare a
descriptor, and the read runs code the reader has never seen — so a read that throws costs
its own row and carries an `:error` the page prints in place of the note. Reported as a
cache that could not answer, never as one that is empty: in a column of dashes those are
indistinguishable, and a page whose worth is highest while something is already wrong must
not be the next thing to fail. A clear behaves the same way, entry by entry.

**A bound that is a dynamic var is read where it is read.** `:limit` accepts a thunk, and
the two rebindable bounds — the symbol pool's and the taxonomy's scoped memo budget — use
one. A descriptor is built once, at namespace load, so a constant captured into it is that
constant forever; that is right for a `def` and wrong for a var whose only reason to be
dynamic is that something rebinds it. Reporting the root bound while the engine enforced
another would misstate the one field a reader consults to ask whether a cache is about to
flush wholesale.

**The profiler** is folded in because it is the same subject — this process rather than
this KB. `VAELII_PROFILER` starts `clj-async-profiler`'s UI with the browser and
`VAELII_PROFILER_PORT` moves it off 8080; the call site is a `requiring-resolve`, so it
exists without the dependency, which ships in the `:repl` profile. With the class absent
the page says so plainly instead of rendering a link to a port nothing is listening on.

**One UI, whoever asks.** Both entry points call `start-profiler` and a namespace reload
calls it again, so the state is a `defonce` — and the claim on it is a
`compare-and-set!` rather than a read followed by a start, since two callers at once both
pass a read and then race for the port. A start that *fails* puts the state back: nothing
holds the port, so a later call is free to try again.

**Something links to it.** A diagnostics page with no anchor pointing at it is a page
nobody reads, so `/stats`, `/kbs` and `/jobs` each carry a line here — the three places a
reader asking "why is this slow" lands — and `web_caches_test` asserts all three rather
than leaving them to review.

## What a page costs

The browser is the standing test of the public read surface, so what a page *costs* is
part of what it demonstrates — every `v/…` call is a store read in-process and an HTTP
round-trip under `--attach`.

- **A page is answered as the fragment that lands.** `hx-boost` and the header search
  both swap `#main`, so a request carrying `HX-Request` is answered with the `#main`
  element and a `<title>` (htmx lifts a title out of a fragment to retitle the tab) —
  no head, no header, no editor panel. A request **without** it gets the whole
  document, which is what keeps the browser working with JavaScript off; so does an
  `HX-History-Restore-Request`, since htmx is repopulating a history entry and replaces
  the whole history element with it.
- **A `view` is built once per request** and threaded through every render fn in place
  of a bare KB. It holds the type set (one `v/types` for the page, not one per render),
  whether the answer is a fragment, and a **belief cache**: a listing calls
  `prime-belief!` with the handles it is about to render and `vaelii.core/believed`
  answers them in **one** read, so a page of 60 rows costs one belief read rather than
  60. A handle nobody primed still falls back to a single cached `in?`.
- **A row renderer takes the record, not the handle.** Every listing already holds the
  sentexes it is rendering; `sentex-ref` takes one. `handle-ref` is the variant for a
  caller that genuinely holds only a handle (a justification's antecedent, a
  contradictor, a `(sentexHandle N)` subterm), and it fetches exactly the one record it
  needs.
- **A rule is laid out across lines, one antecedent literal to a line.**

  ```
  (implies (and (weightOf ?x ?wx)
                (weightOf ?y ?wy)
                (quantityGreaterThan ?wx ?wy))
           (heavierThan ?x ?y))
  ```

  A rule read as one line is a rule read by counting parentheses: which literals are the
  conditions and which one is the conclusion is exactly what a single line runs together.
  One literal to a line separates them, and the indent says which side of the arrow each
  is on. The indent is counted in **characters**, which is exact rather
  than approximate because every sentence on this page is set in the monospace face
  (`--mono`) and the span holding the newlines is `white-space: pre-wrap`; it is the
  printed width of the functor and its parenthesis, the same arithmetic a Clojure editor
  does, and it survives a reader's own font size because both sides scale with it.
  `pre-wrap` rather than `pre` so a line too long for the viewport wraps instead of
  widening the page. Only `implies` and the n-ary connectives break; an antecedent
  literal is a unit, and breaking inside one would be indenting argument positions.

  **The editor lays the same rule out the same way** (`pretty-sentence`), through the
  wrapper that carries a rule's direction:

  ```
  CxSize
  (set/backwardRule (implies (and (weightOf ?x ?wx)
                                  (weightOf ?y ?wy)
                                  (quantityGreaterThan ?wx ?wy))
                             (heavierThan ?x ?y)))
  ```

  A rule opened for editing arrived as one long line where the row above it was laid
  out. The whitespace is not read back — `read-entries` reads EDN **forms** and the save
  diffs by content — so the layout is for the reader and the sentence reaching the KB is
  the one that was there.
- **Parens are coloured by how deep they are nested.** A sentence is a tree printed as a
  line, and the parens are the only thing saying where a subterm ends — `(implies (and
  (weightOf ?x ?wx) …` is three opening parens before the first argument. Every subterm
  is already coloured by its role, so the structure was the one thing on the page with no
  colour at all. The depth counts along the nine-step spectrum from `--rb1` and wraps at
  nine (`paren`, `rb-depths`), so a **matching pair is always one colour** and no pair is
  the colour of the one immediately inside it. vaelii.com's stylesheet draws the same
  nine in the same order and has been describing them as "the engine's browser draws
  them" since before the browser drew any.
- **A row is a circle and a sentence.** Every case the badge distinguishes is already
  one colour, so a word beside it says the colour twice: `backward rule` next to the
  purple circle adds nothing to a reader who has the scale and is two words of noise to
  one who is reading the sentence. The reading stays in the `title`, where it costs the
  row nothing; the handle is what `data-h`, the link and the `title` carry; and belief is
  `state-tag`'s, which names the *reason* a row is OUT and says nothing on a row that is
  IN.
- **The badge and the sentence are two boxes, not one run of inline content.** A rule is
  laid out with newlines, and a newline in inline content returns to the left edge of the
  containing block — so with one run that block is the *row*, every line after the first
  starts under the badge rather than under `(implies`, and the context and `[edit]` after
  the sentence ride up beside its first line. The sentence gets its own block
  (`sentex-row`, `.sx-body`), and the indent and the trailing context both count from
  where the sentence starts.
- **A handle inside a sentence renders as the sentence it names.** A meta-sentex points
  at a stored sentence by its handle — `(except (sentexHandle 41))` hides one,
  `(exceptWhen <query> (sentexHandle 41))` guards a rule — and a reader shown the integer
  has been told a sentex is hidden and not which one. `render-form` expands it through
  `handle-ref`, so one branch covers every surface that prints a meta-sentex: a term-page
  row, the sentex page, a proposal's `excepts` line. The expansion carries the ids
  already on the path, because the browser reads what is **stored** and a stored sentence
  naming a handle that reaches back to it is a stack overflow rather than a page.
- **A term page shows its taxonomy rather than restating it in prose.** There are no
  Supertypes / Subtypes / Disjoint-with lines. A supertype line renders `genl` sentexes
  the argument groups already list, which is saying twice what the page says once; the one
  reading of a taxonomy the rows cannot give is position, and that is the picture. On an
  imported ontology such a line is also the largest thing the page renders: `thing` has
  110,128 subtypes there and one NAT collection is disjoint from 79,638 types.
  `vaelii.core/describe` answers all six readings — the three closures and the three
  declarations, `:genls-direct` / `:specs-direct` / `:disjoint-maximal` — for a caller that
  wants them ([api.md](api.md)); the page reads one, and only to decide which picture to
  draw.
- **Disjointness is one pass, off the index.** `disjoint?` holds when some supertype of
  x and some different supertype of y are separated. `tax/separating-partners` is the
  enumeration `disjoint?` is the membership test of, so the two cannot disagree, and it
  covers all three ways a separation is declared — `(disjoint a b)`, a shared
  `disjoint_metatype`, and standing beside a sibling under a `(sibling_disjoint C)`
  parent. The types disjoint from the term are then those partners' spec closures: a
  closure read per partner (there are one or two) instead of a `disjoint?` per type in
  the KB. Asking the *store* instead — the `(disjoint ?y x)` and `(disjoint x ?y)`
  sentexes of each supertype, two pattern reads apiece — was 4.3 ms for `dog`, whose
  up-closure is eight, against **0.014 ms** here, and it was `describe`'s single largest
  cost; it also missed the sibling arm, which stores no pair to find. `describe` on `dog`
  went from 7.75 ms to 2.10 ms.
- **A large root extent is counted, not read.** Every group on a term page comes off an
  index read bounded by its answer — except the two extents. Reading a root materializes
  every handle under it before a single record can be taken off it: 0.9 s for the
  2,381,749 of `genl` on the audited 12.26M-sentex corpus, 4.6 s for the 9,040,392 of its
  largest context, to render sixty rows. So past `extent-defer-cap` (20,000) the group
  renders its O(1) stored count and **nothing else**, and its first page of rows arrives on
  the same `revealed` trigger every later page of it already used — which the largest-last
  extent order had put at the bottom of the page anyway. Under the cap the extent is read
  with the page, as every other group is: a term whose whole extent is six rows shows six
  rows. `/term?q=genl` went from 1.04 s to 0.09 s.
- **The remainder walk is bounded on counts, and a context belongs in them.** Only a walk
  can say what the roots did *not* claim, so the term index is walked for at most
  `remainder-scan` (50,000) records — guarded by a lower bound on that index built from
  counts already in hand, since a walk that is going to be truncated is a walk not worth
  taking. The term index is keyed on `kv/sentex-terms`, which is a sentex's indexable terms
  **plus its context**, so a context's own extent bounds its term index below exactly as a
  predicate's functor root does. Left out of the bound, `CxWell` spent 4.2 s a page reading
  50,000 records of a 9,040,399-entry index and discarded them as truncated;
  `/term?q=CxWell` went from 4.2 s to 0.07 s. Every term page of that corpus now renders
  under 100 ms.
- **The concept graph is bounded before its first read, not after.** Its relation flank is
  read off the index groups the term page built anyway, its taxonomy is probed only where
  the closures the page already read say there is something, and every expansion is spent
  from one hard budget — twelve, six a side — so the picture costs at most 24 reads
  whatever the fan-out. Capping what is *drawn* is not capping what is *read*, and a page
  that draws eight of forty thousand subtypes by reading forty thousand looks identical on
  the shipped schema. The radial view's second hop is bounded the same way twice over: it
  reads at most `ego-scan` (500) matches before ordering them, and it does not expand a
  neighbour whose own argument counts put it past `ego-expand-cap` (2,000) — that read
  unions the scoped roots over an open functor, which a prefix of the answer does not make
  cheaper, and one of them at `isa` took 851 ms.
- **A node label is a term, so it is set in the page's monospace face**, at `--g-label`
  (13.5px) raised by the sheet's `font-size-adjust`. `vaelii.browser.svg/char-w` is that
  used size times Hasklig's .6em advance, so a node's width is a width rather than the
  estimate an unknown proportional face forced; the CSS size, the x-height adjust and
  `char-w` move together or the boxes stop fitting their labels. A node is a **box** (a
  3px corner, `.g-box`) rather than a pill: a fully-rounded end eats the width a long term
  needs, and two adjacent nodes read as one capsule.
- **Search reads the vocabulary, never the sentexes.** `/find` filters the index's term
  roster through `vaelii.core/find-terms`, so it costs the number of distinct terms.
  A query carrying no regex metacharacter is matched as a **substring** — exactly what
  `re-find` of a literal means — so the type-ahead path compiles no pattern at all;
  only a query that is actually a pattern reaches `re-pattern`, and only up to a
  **128-character cap**, since the route is reachable per keystroke and, through the
  daemon, by whoever can reach it.

The result, over the starter plus the test-world cast: `/term?q=genl` renders in 11 KB
reads, `/find?q=do` in 2, and the `/find` fragment is 373 bytes against a 2.7K document.

## A sentex row

A row is an `.sx-item[data-h]` list item (the term, sentex, and justification pages),
and it is **text**. It carries no selection state, no roving tabindex and no script, so
a press-drag across a sentence selects that sentence and a copy takes the characters the
KB stores. `data-h` is there for one reason: an out-of-band swap after a save addresses
every copy of a row by it.

The one control a row carries is **`[edit]`**, shown on hover or keyboard focus and
holding its space either way, so a page of rows reads as sentences rather than as a
column of controls and nothing reflows as the pointer crosses one. It is an ordinary
htmx `GET /edit?handles=<h>` into the editor panel — a `<button>` rather than a link, so
`hx-boost` leaves it alone and the press beside it stays a text selection.

## Editing sentexes

The browser is not read-only: sentexes can be **asserted, edited, and retracted**. Every
write goes through `vaelii.core/edit!` via the access facade, so each is **one settle**
and works the same in-process or attached to a daemon.

A row's `[edit]` opens the **editor panel**, with **Save**, **Retract…** and Cancel. The
panel takes a *set* of handles, so `/edit?handles=1,2,3` edits a batch in one settle —
what a row's control hands it is a set of one. A **term** carries an `[edit]` of its own,
beside its name at the top of its page: `/edit?q=<term>` opens the panel on the head of
the term's most direct index group (`term-edit-cap`, 20), which is the group the page
renders first.

- **Contexts and sentences are interleaved; nothing is bracketed.** A bare symbol on a
  line of its own sets the context every sentence under it is in, a map sets the options
  they carry (`{:strength :monotonic}`, `{}` back to the default), and every list is a
  sentence in whatever is current:

  ```
  CxNaturalWorld
  (dog Muffet)
  (implies (and (parentOf ?x ?y)
                (parentOf ?y ?z))
           (grandparentOf ?x ?z))

  CxValuesGrammar
  (isa Kids life-direction)
  ```

  A page of one context's facts says that context once, and moving a sentence to another
  context is moving one line. A sentence with no context above it is a problem, not a
  guess. `seed-text` writes the panel that way — the handles in the order they were
  named, a context line wherever the context changes, an options map wherever the
  strength does. A rule is shown with its direction/defeasibility as `set/*Rule` wrappers
  (its `exceptWhen` guard is a separate meta-sentex and is *not* carried, so editing a
  guarded rule drops the guard; an `(unknown S)` antecedent is an ordinary literal in the
  rule body and round-trips).
- **The text is read as forms, not as lines.** `read-forms` reads successive EDN forms
  off a `LineNumberReader`, so a sentence may be laid out over as many lines as it needs
  and a problem still names the line the form opens on. Reading stops at the first form
  that does not read: everything after an unbalanced one is *inside* it, so going on
  would report one mistake many times. `read-entries` sorts the forms it answers into
  contexts, options and sentences. `/assert` reads its box the same way, with the form's
  **context field** seeding the first sentence — so a box holding nothing but sentences
  asserts them where the field says, and a context written in the box takes over from
  that line down.
- **Save** POSTs the edited text. The server diffs the sentences against the named handles
  **by content**: a sentence you left alone touches nothing (its handle is untouched, no
  churn), one you changed or deleted retracts its sentex, a new one is asserted. The batch
  that diff produces is then run past **`vaelii.core/check`** before `edit!` is called at
  all, so a save the engine would refuse comes back as a message *beside its line* —
  with the `:type` `assert` would have thrown — rather than as an exception. A line that
  does not parse blocks the save the same way. Either way nothing is written and your
  text comes back intact.
- **Assert** (`/assert`, linked from the menubar, the home page, and every term page)
  is the way in for knowledge the KB does not hold yet: sentences one per line, a
  context, and a checkbox for `{:strength :monotonic}`. Opened from a term page it
  arrives with that term already placed where its role belongs — a predicate or type as
  the functor, an individual as an argument, a context in the context field. Every line
  is checked first and the form is all-or-nothing: one bad line stores none of it, so
  the page is safe to retry.
- **Retract…** opens a confirmation that says what will go *before* it goes. Retraction
  is dependency-directed, so the panel lists the named handles **and** the believed sentexes
  that would lose their last witness — computed to a fixpoint from the justification
  graph, the same criterion the sweep applies (a datum goes when it is not a premise in
  its own right and every justification concluding it has an argument that is going).
  The walk stops at 200 and says so. Its GET writes nothing; only its POST retracts, and
  the answer deletes every row that is actually gone out of band.
- **Forward chaining** is a POST form on `/stats`, beside the run counter, the last
  run's derived count, and the violations ledger it fills — so what a load did and what
  it dropped read together.
- **A save re-renders what changed, not the page.** Each retracted handle's row is
  swapped **out of band** (`hx-swap-oob`) — replaced by the row its line became, or
  deleted when the line was deleted. Rows are addressed by their `data-h` attribute rather than by an id, because one
  handle can appear in more than one index group on a term page and htmx's selector form
  of `hx-swap-oob` swaps **all** the matches, so every copy of a row moves. A line is
  paired with a handle **by position** (sentences only — a context line is not one of
  them): the textarea is seeded one sentence per named
  handle, so a line rewritten in place retracts at that position and asserts at it. Only
  that exact coincidence pairs — a line you appended has no row to replace, so it is
  listed in the result panel instead of pretending to be one.
- The writes go through the access facade — `access/edit!` (Save, Retract),
  `access/edit-with-consequences!` (the assert form, an accepted proposal),
  `access/forward-chain`, and `access/preview`, which stores nothing but holds the
  single writer while it applies a batch and rolls it back. So they work both
  in-process and when the browser is **attached to a daemon** — the daemon is the
  single writer and serializes each one under its lock.
- **Every route checks `Host`, and every write additionally checks who asked.** The
  whole handler sits behind a `Host` allowlist derived from the interface it is bound
  to (`guard/wrap-host-allowed`, the same guard the daemon serves behind): on the
  loopback default only loopback names are answered, and anything else gets 400. That
  is what closes **DNS rebinding**, the attack an origin check cannot see — a rebound
  name is genuinely same-origin with the attacker's page — and it wraps the reads as
  well as the writes, because a rebound page reads a KB as happily as it writes to
  one, and reading it is what an attacker came for. `VAELII_ALLOWED_HOSTS`
  (comma-separated) overrides the list for a setup that legitimately presents another
  name — a reverse proxy preserving the original `Host`, a local alias. A request
  with **no** `Host` header passes: every browser sends one, so its absence marks a
  non-browser client with no ambient browser context to ride.
  The second layer is the write guard. Ten routes go through it: eight through
  `writing` above — `/edit`, `/assert`, `/retract`, `/demo`, `/reasoning`,
  `/sandbox/reset`, `/propose/apply` and `/propose/preview` (a writer for the length of
  the rollback it does) — and `/chain` and POST `/funnel` through `writing-job`, which
  submits the same run from either page. Nothing authenticates them, so each compares the request's
  `Origin` (falling back to `Referer`) to its own `Host` and answers 403 on a mismatch.
  A browser stamps that header on a form or fetch
  POST and a page on another site cannot forge it, so another tab cannot drive the
  editor. `Origin: null` — a sandboxed frame — is a real origin claim that matches
  nothing, and is refused. A request carrying **neither** header is a non-browser
  client with no ambient context to ride, and passes — the same carve-out for the
  same reason.
  A third, smaller one sits outside both: **a request body past
  `guard/max-body-bytes`** (`VAELII_MAX_BODY_BYTES`, 16 MiB by default) is refused with
  413. It is `guard/wrap-body-limit`, the same ceiling from the same variable the daemon
  holds ([operations.md](operations.md)), and it wraps *outside* `wrap-params`, which
  slurps a form body with no ceiling of its own.
  No destructive path is reachable by GET: `/retract`'s GET renders the *preview* and
  `/chain` has no GET at all, so a link, a prefetch, or a crawler cannot change the KB.

## Validating before writing

`vaelii.core/check` is `assert`'s own check chain run for its answer instead of its
effect — the same functions in the same order, reporting each failure under the `:type`
keyword `assert` would have thrown, storing nothing. The browser is its first caller:
every write form — the editor's Save, the assert form, the accepted-proposal commit
and the retract POST — runs `check-edit` over the batch it is about to apply and
renders the problems against the lines that produced them, so the reader sees
`line 2 · not-ground · not ground: (parentOf Tom ?x) contains a variable` instead of a
stack trace. It adds no work when the content is fine, and the alternative — attempt
the write and catch — writes the good half of a batch before failing on the bad half.

## Proposing knowledge

A term page says what the KB knows about a term. The panel at its foot is where a reader
asks a model what it is *missing* — `vaelii.host.llm.session/propose-page`, which is
shown the page's own sentexes and the vocabulary the term's `genl` neighbourhood
licenses, and answers with type-level assertions in that vocabulary. See
[docs/llm.md](llm.md) for the path itself.

The browser adds the bounds:

- **The turn writes nothing.** A model proposes; the lines come back as a list to read.
  What reaches the KB is what a reader **accepted**, through the same `edit!` every other
  write here goes through — so the model adds no write path and no trust boundary, and
  the last thing to touch a sentence before it is stored is a person.
- **A runaway generation cannot hang the page.** Every turn carries `:max-tokens`
  (Ollama's `num_predict`), because two of eight models measured degenerate into runaway
  generation — one wrote 8138 lines over 474 seconds. A wall-clock timeout is no answer
  to that: the host goes on generating and the GPU time is spent either way. The
  transport deadline is a *backstop under* the cap, for a host that has stopped
  answering rather than one answering too much.
- **The panel costs a page nothing.** Rendering it reads the configured backend's name
  and probes no host; resolving a provider — the part that opens a socket — happens on
  the POST that runs a turn.
- **No model configured is a first-class state.** With nothing set, `provider/provider`
  hands back the offline stub, which proposes nothing, and the panel says so rather than
  reporting a parse failure. `-main` warms a configured backend on a daemon thread at
  start (`warm-model`), because the latency of a local turn is model *load*: ~11 s, then
  ~0.4 s, then ~0.3 s for three identical turns ([llm.md](llm.md)).
- **POST, and origin-checked.** The turn writes nothing but it *spends* something — a
  model, and on a local host a GPU — so a page on another site must not be able to make
  this browser run one.
- **`--attach` cannot serve it.** A proposal reads the term's neighbourhood, its
  vocabulary and its checks through dozens of KB calls, which is not a thing to run a
  round-trip at a time against a daemon; `access/local-kb` answers nil there and the
  panel says so instead of degrading silently.

### The chip gutter

A proposed line has **four independent things** worth knowing, and prose buries all of
them. `vaelii.host.llm.verdict` gathers them per entry and the panel renders each as a
**chip** — a glyph and one word — in a gutter the eye reads down:

```
✓  (genl penguin aquatic_bird)
✓  (mortal penguin)      → (set/defaultRule (implies (penguin ?x) (mortal ?x)))  → shape  [genl]
!  (partOf penguin wing) → (partOfType penguin wing)                → lift  ! direction
+  (implies (penguin ?x) (swims ?x))                                + property
✗  (genl penguin Muffet)                                              ✗ malformed
```

- **What the KB says** — `check-edit`'s typed problems, each as its *reason* (`open`,
  `arity`, `disjoint`, `malformed`) and never as the checker's sentence. A message in
  the gutter is the one thing that cannot be scanned. A type nobody has written yet
  still renders as a chip: the fallback is the keyword's own name.
- **What shape it should have been in** — `vaelii.host.llm.correct`. The original is
  struck through and the rewrite follows it: **superseded, not replaced**, because
  hiding what the model wrote would hide the error class the correction pass exists to
  catch, and the choice between the two shapes is the author's. `[genl]` is the other
  defensible shape, named by its functor.
- **What vocabulary it invents** — `inventory/coined`, split into a one-place
  `property` and an n-place `relation`, which are different risks triaged differently.
  The measured failure mode of this whole path is a batch accepted without being read.
- **What the engine could not decide** — a `:confidence :low` correction is a judgement
  handed back, so it says which one (`direction` when both argument positions want the
  same type, `ambiguous` when no rule says which argument is surplus).

The verdict glyph is the **worst** of the four (refused ▸ uncertain ▸ coins ▸ ok), and
only the glyph is ranked — every axis is still reported beside it. A rewrite the engine
is *sure* of leaves the verdict alone: the line is admissible and the chip says the rest.
Explanations live under one `?` per row, never inline.

### Choosing a shape, and accepting

`correct` deliberately refuses to pick between `(genl penguin mortal)` and
`(set/defaultRule (implies (penguin ?x) (mortal ?x)))`, because the choice is
definitional versus defeasible and no engine can make it for the author. It is the
commonest decision in a review pass, so it costs **one key**.

Every shape a line could take is numbered — the sentence as the model wrote it is `1`,
the rewrite is `2`, its alternatives follow — and the **rewrite leads**, so the common
case needs no keystroke and getting back to the original costs one. The review list is a
second ARIA grid with its own keys: `j`/`k` move, `a`/`x` decide and step on, `1`–`9`
pick a shape.

- **A choice is re-derived, never trusted.** The numbered button posts back the
  *original* sentence and a number; the server re-runs `correct/apply-correction` and
  re-renders the row. A correction is a pure function of the KB and what the model wrote,
  so nothing can be smuggled into a row by editing the request.
- **The chosen shape is re-checked.** `correct` does not re-check its own output by
  contract, so the chips a reviewer commits against are computed from the structure that
  would actually be stored — while the correction chip stays, since it is *why* the line
  was restated and dropping it would erase the reason to change your mind.
- **Accepting is a disabled field flipped on.** The whole list is one form; a row's
  `[sentence context]` field is submitted only when accepted, so the browser assembles
  the payload and no script builds one. A line with nothing storable has no field at all
  — the two ways that happens are a correction that could only *report* (an arity surplus
  no rule can pick: `correct/apply-correction` answers nil) and a shape the KB refuses.
- **The server refuses a report-only line too.** The row renders no field for one, but
  the field is what the browser sends, and a check that only runs in the browser is not a
  check. Storing it would store the sentence the correction was warning about.
- **Applied whole or not at all.** `check-edit` runs over the batch first and one problem
  stores nothing — a half-applied review is an outcome nobody chose — and the adds go
  through `v/edit!` once, so they land in a single settle.

### One row, three densities

"Show the bad result and the fix", "show only the fix" and "let them edit" were never
three flows. They are one row at three **disclosure levels**, and the level belongs to
the view rather than to a preferences panel — a reader working through fifty lines wants
a gutter, a reader meeting their first refusal wants the sentence spelled out, and the
same reader is both within a session. So the switch sits above the list.

| Level | The row shows |
|---|---|
| `guided` | the fix, the reason **in words**, and what the line would mean — no context name, no handle, no engine vocabulary |
| `working` | the fix, the chip gutter, the reason folded behind `?` |
| `dense` | the gutter alone. The explanation is **absent, not folded** |

The default is a property of the entry point: a panel opened against the reader's own
sandbox opens `guided` (somewhere safe to be wrong), a term page opens `working`
(vocabulary being worked through). An explicit choice overrides both and rides the
request — a density that followed a reader from the sandbox onto a term page would be
the preferences panel this exists instead of.

**Changing the level asks no model.** `/propose/level` reposts the list's own hidden
originals and re-derives every verdict from the KB, which is what they were in the first
place — `verdict` is a pure function of the KB and the sentences. So a reader who opens
`guided`, works out what a refusal meant and drops to `dense` has asked the model exactly
once. It is three configurations of one renderer rather than three renderers, because
three renderers drift: the day the gutter learns a fifth axis, two of them forget.

### The gloss is composed, never generated

At `guided` a row says what the line would **mean**, and that sentence is built by
`vaelii.host.gloss` out of the KB's own `comment` sentexes — it reaches no model at all.

This is the one place in the panel where nothing verifies the output. Every other axis is
checked: `check-edit` says what the KB refuses, `correct` proposes a shape and the shape
is re-checked, `coined` counts vocabulary against the inventory. Nothing in the engine
can say that an English sentence describing `(genl penguin bird)` is wrong — so a fluent
gloss is a way to teach the reader most likely to believe it something false, through
their only window onto the formal content. Reading is the more dangerous direction here,
not the safer one.

The defence is to not write prose where the KB has already written it. The shipped
comments open with a template:

```clojure
(comment genl "(genl ?subtype ?supertype) means that every ?subtype is a ?supertype. …")
```

a **signature** naming the argument positions with variables, then a clause saying what
the predicate means *in those names*. Glossing `(genl penguin bird)` is a lookup and a
substitution — "Every penguin is a bird." — and everything past that first clause is
documentation for a reader rather than template. 210 of the 328 comments the starter
ships carry such a signature; the 118 that do not are read as descriptions instead. 111 of
those are types, units and dimensions, whose comments are noun phrases — which is what a
type gloss wants, since it reads "X is a dog" and the comment is the apposition after it.
The other seven declare a compound or variable-arity argument (`(implies (and ?antecedent
…) ?consequent)`, `(lessThan ?number1 ?number2 …)`), which cannot be substituted into
position by position. Measured over every believed sentex in the shipped schema, 1,839 of
1,843 gloss with zero model calls — **99.8%**. `gloss_test` holds the composition rate to
a **95% floor**, so the percentage is a reading of the schema as it stands and the floor
is what is guaranteed.

The variables are required twice over. A parameter spelled `?place` cannot be
mistaken for an individual the way `Place` can, so the comment is a better comment; and
because the name carries the sort, the clause needs no sortal noun leaning on it, so what
substitutes is "Paris lies due north of Lyon" rather than "place Paris lies due north of
place Lyon". A signature spelled the other way — `(eats Animal Food): Animal eats Food` —
still reads, since an imported vocabulary writes its own comments and they are not ours
to rewrite.

What the measurement does **not** say is that every gloss is worth reading. It counts
composition, not information: the gloss earns its place where the predicate name is opaque
(`genl` → "Every dog is an animal" teaches a reader what `genl` means) and adds nothing
where the predicate is already an English verb.

What it will not do is invent. A term the KB documents nothing about is **named, not
described** — `:source` comes back `:named` and the row says "no description on record"
rather than guessing. Two smaller refusals fall out of the same rule: a clause that never
names its own parameters (`(disjoint TypeA TypeB): the two types have no common
instance`) would substitute into a fluent sentence that has silently lost its arguments,
so the arguments are said and the clause follows as a description (`:partial`); and a
comment's own grammar is *finished* rather than rewritten — the article in "every SubType
is a SuperType" agrees with what lands after it, and the one in "the animal can fly" goes
when the animal becomes `Pingu`. The formal sentence is on the row above the gloss in
every case. `gloss/with-model` exists for a KB that documents nothing, is a separate
entry point so the ordinary path *cannot* reach a model, and marks its answer
`:generated` — the reader is entitled to know which they are reading.

### What accepting would do

The chips say whether a line would be **admitted**. Between the list and the commit
button sits the other question: what the accepted set would **mean**. It is
`vaelii.core/preview` ([preview.md](preview.md)), posted to `/propose/preview`.

```
  Consequences of accepting 6 lines
    ⚠ 1 refused        disjoint — Willy cannot be both fish and mammal · line 2
    ⚡ 1 now contested  (flies Tweety) ⟷ (not (flies Tweety))
    + 11 newly believed   (collapsed)
    − 2 no longer believed (collapsed)
```

- **The same payload the button posts.** `hx-include` names the commit form, so what is
  previewed is exactly the enabled `line` fields — one payload, assembled by the browser,
  read twice. A reconstruction could disagree with what lands; this cannot.
- **The refused group leads and opens itself.** It is the one a reader must not miss, and
  it is what catches a stratification cycle or a disjointness clash before anything is
  stored — including the case a per-line chip cannot see, where two lines are each
  admissible alone and refused together.
- **"Now contested" is its own group**, because a default against a default withdraws
  nothing: both sides stay believed and the pair is a represented dilemma
  ([nmtms.md](nmtms.md)). Reporting only the two diff halves would tell a reader the line
  simply arrived, which is the one thing that did not happen — so `preview` returns the
  dilemmas the batch would open, standing ones subtracted.
- **A created line has no handle to link.** `preview` reports nil rather than the number
  it briefly held, so what explains a derived line is the rule that would conclude it. A
  line that *already exists* — a withdrawal, a revival — keeps its handle and links to
  `/why/:id`.
- **Recomputed on the accepted set, debounced.** `vaelii.js` fires one
  `accepted-changed` event on `<body>` when the accepted *lines* change (re-choosing a
  shape on an accepted row counts; moving the cursor does not), and the panel's own
  `hx-trigger` carries `delay:400ms`. Holding `a` down the list costs one preview.
- **Report-only lines are held back**, since the commit refuses them: previewing one
  would promise a consequence the button will not deliver.
- **Bounded, and it says so.** Each half is capped at 50 rendered lines; `preview` sets
  `:bounded?` when the cap bit and the panel prints where it stopped.

Nothing here is stored — `preview` hands the KB back at the same handles — which is what
makes it affordable to run on every change of the accepted set rather than once, behind a
confirmation, at the end.

## The proof tree

`/sentex/:id` shows one hop: the justifications that conclude a handle.
`/why/:id` shows the whole argument — `vaelii.core/why` walks down to the premises,
lifting each justification's rule out of its antecedents and reading it back in the
author's variable names. Each derived node is a `<details>` (the first three levels
open, deeper branches one click away) whose branches are its justifications; a branch
ends at a **premise** (with the strength it was asserted at), at a **cycle** back-edge —
the justification graph may cycle, and `why` reports the edge rather than expanding it
again — or at a node that is not believed, which links back to the sentex page where
`why-not` answers instead.

## The levels page

`/levels` is the one page with an input box — a goal is a sentence, not a term, so
there is nothing to click your way to. With no goal it documents the stack; with
one it runs all eight levels and shows what each returns, headed by the `escalate`
verdict ("Answered at level 4 `typed`").

It is the clearest view of what the levels are *for*. Ask it `(genl dog thing)`
against the starter and you see the whole argument at once:

- level 1 returns 25+ unrelated `genl` facts — it retrieves by context and functor
  and **ignores the goal's arguments**, which is exactly why `escalate` starts at 2;
- levels 2–4 return nothing — the edge is not stored, only entailed;
- level 5 derives it from the cached `genl` closure.

Results that come from the store link to their sentex; levels 5–7 derive, so their
answers render inline with a `derived` tag and no handle.

The page shows 25 results per level at a time and takes only 26 from each — it relies
on [level laziness](levels.md#laziness) to stay bounded, which is why it calls
`v/lookup` per level rather than `v/explain-levels` (which counts, and so would realize
every answer of every level). The 26th is what tells it to end the list with a
continuation sentinel.

### The query plan sits above the levels

Same two inputs, complementary answer: the levels say what each mechanism *answers*,
the plan says what the engine would *do*. So it is a section on this page rather than a
second form asking for the same goal twice.

For a **single sentence** it is `query-plan`'s prover table — each applicable prover
with its `est-bindings`, its `cost` tier (`:lookup` < `:compute` < `:search`, a
qualitative first-answer tier and not a predicted duration) and its `completeness` *for
this goal*, and whether it actually runs. Applicable is not consulted: when one prover
is complete the engine runs it alone and every other row reads `shadowed by …`. Ask it
`(genl dog thing)` and `TransitivityProver` is the sole complete method, with
`FactProver` shadowed beneath it — which is the same argument the levels make from the
other side.

For a **vector** — the conjunctive goal `prove` takes — it is the join order `plan/order`
chose, each literal with the variables already bound when it starts and the three numbers
the decision turned on. **est. matches** is the sound upper bound on that literal's own
fan-out under those bindings, the one whose reading of 1 is a proof; **rows** is the
expected size of the relation it denotes on its own; **plan rows** is the expected size of
the whole plan up to and including it, which is what a join was actually costed in. Read
them together and a surprising order is diagnosable: a literal placed early on a small
*est. matches* whose *plan rows* then jumps is the cost model wrong about a join rather
than about a literal. None of the three is indistinguishable from a sorted column, and the first two
differ for a reason — an upper bound and an expectation answer different questions
([inference.md](inference.md)) — while *est. matches* is made *under the bindings the rows
above it produce*, which is sideways information passing and is the thing worth seeing.
**block** is the group of literals it moved with: literals sharing a variable are one
block and run together, and a whole block is held back the way a single literal is.
A literal whose position is operational rather than costed is
marked **pinned** — an evaluable may not outrun what binds it, and a recursive rule's
recursive literal stays last so right-recursion survives. A literal is marked
**cartesian** when it shares no variable with the rest *and* was ranked behind a block
that does: it multiplies the row count of everything after it wherever it runs, so the
estimate beside it is not what placed it — worth noting, since a selective one otherwise
is indistinguishable from a small number sitting last for no reason. The mark is the answer to "why is
this last", not a property of the literal, and it is why the two cases that are *not*
held back go unmarked: one matching at most once multiplies by at most one and leads like
any cheap literal, and one whose block the ranking put first was never held back at all —
a inexpensive enough disconnected block leads, which is the transposition law rather than an
exception to it ([inference.md](inference.md)). The eight levels answer about one literal, so a
conjunction gets the plan and stops there, and says so.

### The standing disjointness question

`/stats?clashes=1` runs `exposed-clashes`: every term holding two types some context can
see as disjoint, where each membership was admissible where it was written.

It is behind a control rather than in the page load, and the difference from the ledgers
above it is the point. `settle` reports a clash as it **arises** — the incremental
question, the one an author wants while writing — so a KB that *arrived all at once* has
nothing newly anything, the arising pass sits it out, and every clash it holds is
invisible until something asks. An imported corpus is exactly that case. The answer is
computed on demand and not filed, so the page says it was computed just now rather than
letting it read as one more accumulated ledger.

The violations list beside it names the **run** that dropped each conclusion, because the
ledger accumulates across runs and caps at the newest 1000 — which run a drop belongs to
is not something the reader can infer from its position in the list.

## Long lists continue

A capped list ends in a **sentinel row** that fetches its own next page —
`hx-trigger="revealed, click, keyup[key=='Enter']"`, replacing itself with the rows that
come back. So a tail nobody scrolls to adds no work, and one that is scrolled to is
reachable rather than reported as "N more not shown". `click` is the same request for a
reader who would rather ask, and for a viewport too tall to produce a scroll event;
Enter is that reader's keyboard, and the sentinel is focusable so they can reach it.

Every list caps, and every one of them continues: an index group on the term page (60
rows), the `/find` results (200), each level on `/levels` (25), one level of either
hierarchy (50), the documented-terms list (50), the disjointness pairs (50), the
contexts-by-size table (25), and each of the three reasoning ledgers (12). The
continuation routes answer bare rows, not pages — `<li>`s, or `<tr>`s where the list is a
real table, since a `<tbody>` may hold nothing else. `hx-target`/`hx-select` are set on the body so every boosted
link swaps `#main`, and both are inherited — so a sentinel says explicitly that it
targets **itself** and selects nothing, and so do the editor's own controls
(`hx-select="unset"`).

### The front page is bounded, and that is not a nicety

`/` is the first page anyone opens against a KB whose size they did not choose — the
catalog will load an ontology with hundreds of thousands of `genl` edges — so nothing on
it may be proportional to the KB.

The **hierarchy trees** open one level at a time. A node with children carries a caret
that fetches them on its first `change`; a level is read by pinning the parent
(`(genl ?sub node)`), which the index answers from the predicate-scoped argument root
(`[:argument-root genl 2 node]`), so the cost is that node's own fan-out rather than the
number of edges in the KB. Whether a node gets a disclosure at all is
`count-with-arg 2 node`, a cheap upper bound (one O(1) count per predicate at the slot):
it spans every binary predicate holding the node in second position, so it can offer a
disclosure that opens to nothing, and can never hide a real child.

The caret is a **checkbox and its label**, not a `<details>`/`<summary>`. A `<summary>`
consumes the click on whatever it contains, so the term inside one toggled the disclosure
instead of opening the term's page — and a term is a link to its page everywhere else on
the site. Here the caret is the only thing that toggles, the term beside it is an ordinary
link, and `.tree-tog:not(:checked) ~ ul.tree-kids { display: none }` does the opening, so
a reader with no script still works the tree. The checkbox's id keys on the edge
(`pred`, `node`), which is what a disclosure *is*: a type reachable by two parents is a
different disclosure under each.

The **flat lists** read their functor root rather than a wholly-open pattern. `(comment
?term ?text)` pins nothing, so the trie fans over every child token at every level: a
`take` would bound the records fetched and not the candidates enumerated, which is a walk
of the whole extent to show fifty rows. Sorting is bounded the same way — alphabetical
order is worth having and adds no work at the shipped schema's size, so a list sorts
when its O(1) count is under a thousand and is in index order, saying so, above it. The
same rule governs a tree level, and where a level was not sorted its sentinel says "show
more" rather than a count it did not pay for.

The **context lattice** is the one thing still read whole, because a root is a context no
edge makes a sub of anything and that is a property of the entire edge set — there is no
partial answer. Past `lattice-cap` edges the page cannot root a lattice, and what it shows
instead is the section below.

### A cap is not an answer: rank first, then cap

Bounding a list stops a page being megabytes. It does not make the page *useful*, and on a
real corpus — an OpenCyc import, whose figures are [kbs.md](kbs.md)'s — the two came apart
completely: fifty of ~13k contexts alphabetically, fifty of ~27k separated pairs, `thing`
→ fifty of ~6,000 subtypes in index order. Each was a short answer to nobody's question —
an arbitrary sample of a long one — and no amount of scrolling fixes it, because nobody
scrolls tens of thousands of pairs looking for the interesting one.

So where a **cheap ranking** exists, the page shows the top of it and says what the whole
is; where one does not, it caps and continues. Cheap is the constraint, and it is a real
one — the rankings taken are the ones the index already answers in O(1):

- **Contexts, by what they hold.** `count-in-context` is one set-size read each, so the whole
  ranking is `n` O(1) reads (~150 ms over ~13k contexts, and past `context-rank-cap` the
  page says it cannot rank rather than spending it). This is the ranking that earns its
  keep: a corpus's mass is not spread evenly over its contexts, and on that import the
  four largest name the subject outright — `CxUniversalVocabulary` around 600k sentexes,
  then `CxGeneOntologyContent`, `CxBaseKB` and `CxComputerSoftwareData` at roughly a
  fifth, a tenth and a twentieth of it. Fifty alphabetical context names said none of
  that. It is the front page's lattice fallback and the whole of the stats table.
- **Types, by how many things they are separated from.** One frequency pass over the pairs.
  Below the cap the pairs themselves are the answer and are listed as before; above it,
  what a reader can use is which types the ontology's partitions are *about*, each linking
  to its own page where its partners are now listed.

And one ranking deliberately **not** taken: ordering the type tree's ~6,000 children of
`thing` by subtree size reads far better than index order — `individual` and
`partially_intangible` instead of `aura_flight` — and measured **a couple of seconds**,
because it is a closure read per child rather than per row shown. The tree stays in index
order and stays lazy. A ranking that costs more than the page is not a ranking the page can have.

The front page also opens with **what the KB is** — sentexes, types, contexts, terms, four
O(1) reads, the question a reader landing on an unfamiliar corpus asks before anything
about its contents. The section titled "Core predicates" says "Documented terms" wherever the KB has more commented
terms than it can sort: on the shipped schema every one of them is engine vocabulary, and
on an imported corpus there are of the order of a hundred thousand, and calling those core
predicates is a claim the page cannot make.

Measured on an imported OpenCyc corpus of roughly a million sentexes — [kbs.md](kbs.md)
carries the import's figures, and the exact counts move with the profile and the plugin
version — `/` renders **tens of KB in a quarter of a second** and `/stats` **tens of KB in
under a tenth**. What the ranking and the cap buy is visible in what they decline to do:
sorting tens of thousands of separated pairs by name to show fifty of them is a second of
front page, and thousands of context rows beside fifty contradictions — each of those a
pair of whole sentences with every subterm linked — is a megabyte of stats page.

Measured against a synthetic wide taxonomy, the bounded front page holds flat where
reading the whole edge set does not:

| genl edges | reading every edge | `/` |
|---|---|---|
| 47 | ~2 ms | ~3 ms |
| 2,047 | ~19 ms | ~4 ms |
| 8,047 | ~78 ms | ~3 ms |
| 32,047 | ~360 ms | ~10 ms |

The middle column is the reads alone; drawing a node per edge grows the document with the
KB on top of that. The bounded page holds at ~15–22 KB throughout.

**This is the only pagination there is**, so it has to hold at any size — a term with
thousands of sentexes is walkable one sentinel at a time, every row reachable, none
served twice, and the walk terminates. `web_test` proves it over 2400 sentexes on one
predicate: 40 pages of 60, then the sentinel stops, and the handles the walk yields are
compared as a *set* against the group's extent rather than counted.

**A listing is ordered by handle, and that is the ordering by design.** Handle order is
allocation order, so a listing reads oldest-first; the sentex lists, the justification
lists and every index group on a term page share it (`group-order`), which leads with the
term's own `(comment …)` and then falls to context and handle. It is chosen for
exactly one property — paging is a re-slice of the same sequence at an offset, so the
order has to be one a later request reproduces exactly, and a content ordering moves under
every write, which would show a reader who scrolled past an offset a row twice or not at
all. Two things it is not. It is not a **ranking**: the previous section is where the page
ranks, and nothing about being asserted first makes a sentex more interesting. And it is
not a **cap**: nothing is dropped by it, the sentinel walks the whole group, and the count
beside a group's heading is its stored total rather than the page's.

**Past `group-sort-cap` (20,000) a group is not ordered at all** — it pages in the order
the index read it in, which is reproducible for an unchanged store and is therefore the
one property paging needs. Ordering means realizing the whole group and printing a context
per member to show sixty rows: at `genl`, whose functor root holds 2,381,749 sentexes,
that was 129 s, paid twice per page. The same cap governs the graph's flank window
(`flank-scan`), where the alternative was sorting millions of records to pick forty.

### A term page reads from what the term IS to what uses it

**The index groups are in one fixed order**, and the order is the claim the page makes
about them — not a ranking recomputed per term:

1. **the argument positions**, ascending — `(comment dog "…")`, `(genl dog mammal)`,
   `(arg parentOf 1 animal)`. A term sits in an argument of the sentences that *declare*
   it, and those are what a reader arriving at the page came for. Inside the first of
   them the term's own **comment sorts first**: it is what the term says it is, and
   allocation order would otherwise put it wherever it happened to be asserted. Part of
   the sort key, never a row lifted out of the sequence — paging re-slices that sequence
   at an offset, and a prepend would show the comment again at the top of every page;
2. **what a rule concludes about it**, then **what a rule requires of it**. A rule's two
   halves are two groups, because they say different things: the conclusion is about the
   term, and the condition is about whatever the rule concludes. A rule doing both is
   listed under the conclusion;
3. **the deeper nestings** — the term index minus what a root or a rule half claimed;
4. **the extents, last**. `[:functor-root]` is every fact written with the term as
   predicate (2,381,749 of them at `genl`) and `[:context-root]` is everything asserted
   in a context, each a list whose first sixty rows say nothing about the term itself.

**The extents are ordered largest-last**, the one place size decides rather than
directness. The bottom of the page is where a list goes on loading as a reader scrolls,
so an extent of millions there is a list they walk into, where the same list above a
short one is a wall to get past.

The `[edit]` beside the heading follows the same order — it opens on the head of the
group the page renders first (`term-main-handles`), which is now the declarations rather
than the extent.

### Hiding what the engine concluded

Most of what a term page lists on a settled ontology is **derived**: `dog` is told four
things and concluded five from them. **hide derived**, beside the "Sentexes by index"
heading, leaves the conclusions out of every group on the page. No belief moves and no
count changes — the heading still says how many sentexes are *stored* in the group — and
the discriminant costs no read of its own: an asserted record carries a `:strength` and a
derived one does not, which is the same thing the badge draws a ring for, so a row the
reader sees as derived is a row the filter leaves out. It is deliberately not
`vaelii.core/premise?`, which asks the network whether anything concludes the sentex — a
sentex can be asserted **and** derivable, and the two answers then disagree with each
other and with what the page drew.

It is one query parameter (`?derived=hide|show`), one cookie and a re-render: no script,
no per-row state, and a page that is the same page when its URL is shared. The cookie is
**persistent** (one year), unlike the sandbox's session cookie and unlike the proposal
panel's density switch, which deliberately rides the request: a sandbox is scoped to the
sitting, a density belongs to the entry point, and how much of a term page someone wants
to read is neither.

Two things it does not do. It does not make the page cheaper — the filter is over records
the group was going to read anyway. And it does not turn a page into a scan: the walk is
bounded at `derived-scan` (5,000) records per page, so a group holding one premise in a
million still fills its pages one bounded, resumable request at a time. An offset means
the same thing under either setting — it indexes the group's **records**, not the rows
that survived the filter — so a reader who toggles part way down a list neither sees a
row twice nor steps over one. The sentinel then carries no number: what is behind it is
records, and how many of them are premises is not known until they are read.

### A term page reads what it can count, and says when it did not look

Four of a term's groups come off roots with an **O(1) stored count** — the functor root,
the argument-position roots, the context root. The three remainder groups ("Rule
conclusion", "Rule condition", "Nested elsewhere") are the term index **minus**
what a root claimed, and no count answers
that: the only way to know a sentex is not in a root is to look at it. So:

- **Which argument positions a term sits at is asked of the counts**, not of the records.
  `count-with-arg` is one O(1) set-size read per predicate at the slot, so twelve of them
  (`arg-position-cap`) answer it without fetching anything. Reading it off the term's own
  sentexes meant walking the whole extent and looking at every argument of every one —
  17 s at `genl`, against 0 ms here.
- **Whether a root claimed a sentex is decided per record**, from the sentence's own
  shape, rather than against a set of every id the roots hold. Building that set *is* the
  extent read the walk exists to avoid.
- **The walk is bounded twice.** It stops after `remainder-scan` (50,000) entries, and it
  is not started at all when the widest root already holds more than that — every sentex a
  root holds contains the term, so a root past the cap proves the term index is past it
  too, and the walk would only be truncated. When it did not finish, the page **says so**
  and offers no remainder groups, rather than showing an empty one and implying there is
  nothing there.

Measured on a 12.26M-sentex import: `/term?q=genl` went from 207 s to ~0.75 s, `isa` from
2.9 s to 25 ms, and no other term page measured above 135 ms. What is left at `genl` is
the store's own first read of a 2.4M posting set.

## Rendering sentences

A sentence is rendered structurally, not as one opaque string:

- a **handle badge** stands before the sentence in place of the bare `#id` — one small
  circle that links to the sentex page. Colour is the whole of what it says, on a scale a
  reader learns once: **red** a negation, **white** a monotonic fact, **yellow** a default
  fact, **green** one the engine derived rather than was told, **blue** a forward rule,
  **purple** a backward rule, both halves for a rule running both ways, and **black** an
  inert rule — stored, and chaining in neither direction. A **filled** circle is asserted
  and a **ring** is derived, which is what keeps a derived negation distinguishable from
  an asserted one; a **dimmed** one is stored and not believed. Negation outranks every other case, because a reader who misses
  a `not` has the sentex backwards and no other confusion costs that. Its `title` carries
  the same reading in words and the handle, so the number and the scale are one hover
  away and lists stay scannable;
- **each subterm is its own link** to `/term?q=<subterm>` — click the predicate,
  an individual, or the context independently (nested compound subterms are also
  listed individually under a sentex's *Subterms*);
- terms are **colored by role** — type (green), individual (purple), predicate
  (blue), context (brown), number (red), variable (grey). A type is recognized by
  membership in the genl taxonomy, so `dog` colors as a type while `parentOf`
  colors as a predicate — and that membership is checked **before** the non-symbol
  fallback, because a type node need not be a symbol: an imported ontology names a type
  it has no atomic name for with a function term, and over ten thousand of the types in
  the OpenCyc import [kbs.md](kbs.md) is the route to are compounds.
  Reading those as numbers is a page in the wrong colour. A legend is shown
  on the home page.

### A reified term is never shown as its constant

A ground `(F a…)` under a `reifiable_function` is stored as an opaque constant in the
reserved `nat/` namespace ([nat.md](nat.md)) — that is how a function term gets indexed,
retracted and truth-maintained like any symbol. A `nat/`-namespaced gensym is not a name
anybody wrote and says nothing to a reader, so **no page shows one**. Every term goes through
`term-link`, and a reified one renders as the expression it was minted from:

> **(** `FruitFn` `AppleTree` **)**

The **bold parens are the whole of the notation**, and they are required rather than
decorative. A reified term is a *term* that happens to have structure, and it sits in
sentences beside ordinary compounds — on the constant's own page `(termOfUnit K E)`
renders K and E identically otherwise, so the constant and the literal expression it is
mapped to would read as the same thing said twice. Weight is what separates them. The
**opening paren links to the constant's page**, the one place its `termOfUnit` map, its
materialized result types and its uses are listed — so the reified term stays reachable
without ever being spelled out. Nesting works the same way at every level, and each
level's paren links to its own constant.

It reaches past the prose, because a leak anywhere is a reader seeing a gensym: the page
`<title>`, the concept graph's node label and its `aria-label`, the index key each group
displays, and the **assert form's textarea** — which matters most, since a textarea is
content on its way back *in* and `assert` reifies a ground NAT to the constant already
minted, where a hand-typed constant would be a reader writing about an opaque
identity. The constant is held by what a machine reads back: the `href` of
the link to its own page, and the hidden field the proposal panel posts.

Two things the display cannot assume, both tested by injecting at the access facade.
A constant whose `termOfUnit` map is **not believed** renders `(…)` rather than falling
back to the raw symbol — the map can be defeated while a use of the constant survives,
and the honest answer is that the page cannot say what it denotes. And the expansion
**carries the constants already on its path**: the write path cannot build a term that
reaches itself (inner NATs mint first), but a restored dump can, and an unguarded walk
over `(termOfUnit K (F K))` is a stack overflow rather than a page.

The cost is one `term-expression` read per **distinct** constant on the page, cached on
the view — there is no batched read for the map, so the cache is the whole budget, and a
page listing one reified NAT in a dozen rows is one round-trip under `--attach` rather than
twelve. A KB that has minted none never touches it: `reified-term?` is a pure test on the
symbol's namespace.

## Chrome & typography

The page is a **terminal**: a dark ground, square frames, one monospace face, and no
rounded corner anywhere (`* { border-radius: 0 }`, one reset rather than a zero per
rule). Light mode inverts the ground and the accent pair and changes nothing else.

- **A region is a framed box, titled in its own top border.** `panel` renders one — a
  `<section class="panel">` whose `<h2 class="panel-title">` is absolutely positioned
  onto the frame's top edge with the page ground showing through behind the letters, and
  which opens with the index the page counts it by (`.panel-n`, set as a superscript in
  the accent). The front page's five regions and each index group on a term page carry
  one; `.idxgrp` draws the same frame on the container that already existed, so the page
  is one shape repeated rather than two. A heading standing on its own — a page title, a
  subsection — is a name followed by a rule running to the right edge (`h2::after`), the
  divider a terminal monitor draws between two readouts in one box.
- **A region folds by its number.** The digit in a frame's top border is a `<button>`,
  and the digit key `1`–`9` pressed anywhere off a text field does the same thing: it sets
  `data-folded` on the nearest `[data-panel]`, which the sheet reads to hide everything in
  the frame but its title. The frame stays, holding its title and nothing else, so the
  same digit unfolds it and the page stays folded where a reader folded it. Which
  regions are folded is held in `localStorage` **per path**, and re-applied after every
  htmx swap — a region fetched into the page arrives unfolded, whatever the reader last
  said about a region with that number on another page. Both the front page's five
  regions and a term page's index groups carry one, since both draw the same frame.
- **The spectrum.** `--rb1` … `--rb9` are vaelii.com's nine-step scale in its order —
  red, orange, amber, green, teal, cyan, blue, violet, pink — declared once per mode
  beside the surfaces. Anything that counts (a paren's nesting depth, a badge's kind)
  counts along it **from `--rb1`**, so red is what a reader meets first at every one of
  them. The four palettes pick an accent *pair* out of their own values and leave the
  spectrum alone; only the rainbow palette's gradient treatments read the whole scale.
- **One control shape.** A `<button>` is a square frame around a label, filled only when
  it is the one that writes (`.primary`, accent outline filling on hover) or the one that
  tears down (`.danger`). Every page used to restate that rule; the base rule is the
  whole of it now, so a control added later takes the page's shape by being a button.
- A **header** carries the vaelii logo and monospace wordmark (a home link) at the
  left, then — pushed to the right — a **menubar** to the top-level tools (Ontology
  `/`, Reasoning `/reasoning`, Query `/levels`, Assert `/assert`, Sandbox `/assert` —
  the sandbox is reached as a place to write, never as a context to choose — Network
  `/network`, Stats `/stats`, and KB `/kbs` carrying the active KB's name; vaelii.js
  marks the one matching the current path active), a **search box**, the request
  indicator, and the colour controls. The search is an htmx *active search*: a debounced
  `hx-get` to `/find` swaps just the
  `#main` region, so it stays focused and no full reload happens. What you type reads as
  a **regular expression over term names** (`re-find`, so `dog` is a substring match and
  `^parentOf$` an exact one); the results link to each term's page. A pattern that
  resolves to a **single term** — the only match, or one it names exactly — jumps
  straight to that term's page (so `parentOf` lands on it even though it is a substring
  of `grandparentOf`), setting `HX-Push-Url` so the address bar follows.
- A **request indicator** — a hairline bar across the top of the window, which htmx
  marks `.htmx-request` for the life of a request (`hx-indicator`, set on the body and
  so inherited by every navigation, search, and continuation). It is `position: fixed`
  and takes no layout space, so nothing shifts when it appears, and it holds still under
  `prefers-reduced-motion`.
- **Two typefaces, one weight each, one job each.**
  [Hasklig](https://github.com/i-tu/Hasklig) (monospace, `--mono`) sets everything the KB
  stores or the terminal draws — sentences, terms, handles, index keys, frame titles,
  tables, buttons, the editor — so a KB is indistinguishable from the code it resembles.
  [Atkinson Hyperlegible Next](https://www.brailleinstitute.org/freefont/) (proportional,
  `--prose`) sets English written for a reader: a paragraph, a hint, a `comment` string
  off the KB. Body copy is the only place the two meet, and the sheet names what keeps
  `--mono` inside it — `.sx`, `.nat`, `code`, `pre`, a badge, a tag, a form control — so
  a quoted sentence inside a paragraph is still set as a sentence. **Mono is set one step
  larger**, by `font-size-adjust: .535` against Hasklig's own .486 x-height — about 10% up
  — because at one px size a monospace face reads smaller than a proportional one beside
  it. It is `font-size-adjust` rather than a second px size because it adjusts the *used*
  size and leaves the computed one alone: a rule that scales its subtree with `em` still
  scales it, and a mono span inside a mono span does not compound. Both are vendored
  under `resources/public/font/` and served self-hosted, and each ships its **regular
  only** — two files, 102K, the whole webfont budget. The heavier levels the sheet asks
  for (`font-weight: 600` on a frame title, the wordmark, a type term, an active menubar
  link, a table head) are **synthesized**. Declaring each family at 400 alone is
  what keeps synthesis available — a `400 700` range would claim the face covers bold
  and flatten emphasis instead.
- **htmx** ([vendored](https://htmx.org), `resources/public/htmx.min.js`, 2.0.9) drives
  the declarative interactivity. `hx-boost` on the body turns ordinary links and forms
  into ajax swaps with history (degrading to plain navigation when htmx is absent),
  scoped to `#main` — which is what lets the server answer with the fragment that lands,
  and what keeps the header and an open editor from being torn down by a navigation. Scoping it costs one thing back, which the swap pays explicitly: a
  boosted swap whose target is not the body scrolls that target *into view*, so `#main`
  alone would land every navigation with the header — logo, search box, menubar — scrolled
  off the top of a page the reader never scrolled. `show:window:top` says where to land
  instead, which is where an unboosted navigation lands. A continuation sentinel sets its
  own swap and so keeps the page still, which is the whole point of it. The active search
  is the one bespoke widget.

  **Most htmx attributes are inherited**, resolved by walking *up* the DOM until one is
  found — the targets, the swap, the selects, the indicator, `hx-include`,
  `hx-disabled-elt`. That is what makes one `hx-boost` on the body carry every link, and
  it is a trap of the same reach: an attribute written for the element that needs it
  quietly re-aims every request underneath. Three rules follow, and
  `web_htmx_test` rebuilds htmx's own resolution over each page's rendered HTML to hold
  them. **A poll is not a request the reader made** — the four panels that watch a
  running load or export set `hx-indicator` to `unset` (one `polling` helper renders all
  four, so they cannot drift), or each would sweep the top-of-page bar every second or
  two for the whole of a load and report the page as loading when nothing is in flight.
  **A relative selector belongs to the element that wrote it** — `find` and `closest`
  resolve from whichever element is *making* the request, so the review form's
  `hx-disabled-elt="find button[type='submit']"` carries `hx-disinherit`: the level
  buttons, the shape buttons and the consequence preview sit inside that form, contain no
  submit button, and would each disable nothing while logging that they matched nothing.
  **An id htmx addresses must be on exactly one element** — the entries panel refreshes
  the header's KB name out of band, so it emits that copy only when answering a swap; a
  whole document renders its own header, and shipping both would put two `#kb-label`s in
  the page, with every later target resolving against whichever came first.
- **One hand-written script**, `resources/public/vaelii.js` (vanilla, no build step, no
  dependency), for what htmx cannot express: the palette and theme dots below, marking
  the menubar link for the current path active, **folding a framed region** by its
  number, the `/kbs` sliders, and the proposal review's keys (`j`/`k`, `a`/`x`,
  `1`–`9`). The review holds a decision per row *index*
  rather than per element, because choosing a shape swaps the row out from under it;
  picking a shape only clicks the numbered button, and a change in the accepted set
  dispatches one `accepted-changed` event the consequence panel's own `hx-trigger`
  debounces — so both round-trips stay declarative like every other one. The header sits
  outside the swapped region, so the active menubar link is re-marked after every htmx
  swap; nothing else has state to re-sync.
- **Palette and theme.** Two header controls, both dots painted in what they control,
  both persisted in `localStorage` and applied by a tiny pre-paint `<head>` script so
  the page never flashes the wrong colours. They are vaelii.com's two controls, values
  included, so the browser and the site read as one system:
  - a **theme dot** — half the page's ink, half its ground — flipping **light against
    dark**. Every colour is a CSS variable; a `@media (prefers-color-scheme: dark)`
    block is the default and needs no JS, so a page that has never been clicked
    **follows the OS**. Clicking sets `:root[data-theme="dark"|"light"]`, which
    **overrides** the media query — so a pinned theme outranks the OS, and only a
    stored value counts as pinned. The click flips whatever is on screen, OS-chosen or
    not. A stored value the script does not **recognise** is ignored rather than written
    through: the media query is scoped by `:not([data-theme])`, so *any* attribute value
    switches it off, and one no rule matches would leave the page on the light base and
    deaf to the OS. `color-scheme: light dark` pulls scrollbars and native widgets along;
    the logo and favicon flip on the same signal.
  - a **palette dot** cycling **violet → red → green → rainbow** through
    `:root[data-palette]`, and painted in the pair it selects. A palette is an accent
    **pair**: `--accent` (the fill and emphasis hue), `--accent-2` (its deeper partner),
    `--accent-b` (the second tone the dot's gradient runs to), plus `--on-accent`, the
    text a filled accent carries. The wordmark, the selected-card tint, and more
    **derive** from `--accent` with `color-mix`, so one value re-colours the whole
    chrome. Rainbow keeps violet's accents and paints the wordmark, the primary button,
    and the header rule with a gradient (`--rainbow`) instead.
  Palette and theme are orthogonal: any palette works in light or dark. Each palette
  declares both modes' values in one place (`--lt-*` / `--dk-*`) and the mode blocks
  pick a side, so the two can't drift apart. Light accents are deep and carry white
  text; dark accents are pastel and carry near-black — which is what `--on-accent`
  names, and why no filled surface hard-codes `#fff`.
- The fonts, logo, favicons, htmx, and vaelii.js are static files under
  `resources/public`, served by a reitit `create-resource-handler` that catches
  whatever the page router did not match. The stylesheet keeps its own `/vaelii.css`
  route. Every static answer carries a **cache header**, and `VAELII_DEV` in the
  environment picks the policy: truthy (`1` / `true` / `on` / `yes`), the stylesheet is
  re-read per request and nothing is cached, so editing the sheet shows on a refresh with
  no restart; unset or falsy (`0` / `false` / `off` / `no`), it is read once and each
  asset is served `public, max-age=3600`, so a pageview is not a file read and a repeat
  visit is not a download. It is the *value* that decides, not the variable's presence,
  and anything outside those spellings is refused when the namespace loads. Nothing is loaded from a CDN: a CDN could change
  what runs in the operator's browser and would log every page they open. Each vendored
  asset's licence is recorded in [licenses/THIRD-PARTY.md](../licenses/THIRD-PARTY.md).

### The sentence editor

Every box that takes a sentence is the same component — the editor panel, `/assert`, and
the `/levels` goal box at one line. A `.ed` is three elements over one value: the
`<textarea>` that holds the text and takes the keys, the `<pre class="ed-hl">` painted
behind it (transparent text over a coloured copy, so the caret, the selection and the
undo stack are the browser's own), and the `<ul>` of completions under the field. **A
page with no script still has the textarea**, which is why the value lives there and
nowhere else.

Four jobs, all of them keyed on the caret and none of them htmx-expressible:

- **Rainbow parens.** Each delimiter is coloured by its nesting depth, cycling through
  six, and one with nothing to close is coloured as the error it is. Strings, numbers,
  `?variables`, `:keywords` and `;comments` take their own colour, and a symbol standing
  alone at the top level takes the **context** colour, because that is what the server
  reads it as. The six depth colours are six steps along the spectrum (`--rb1`, `--rb2`,
  `--rb3`, `--rb5`, `--rb7`, `--rb8`), counted from red, so a sentence's outermost paren
  is red and the editor follows the light/dark switch along with the sentences beside it.
- **Indentation.** Enter opens the next line under the enclosing form's **first
  argument** — Lisp's own rule — or one past its paren when the form has none yet; Tab
  re-indents the line the caret is on. Both walk the same scan the painter does, so the
  picture and the indentation can never disagree about where a string ends.
- **Completion.** The symbol before the caret is a prefix, and `/complete` answers the
  terms it could become — `find-terms`' prefix match over the **term roster**, so a
  keystroke costs the size of the vocabulary and never a scan of the KB. Twelve at a
  time, each in its role colour. Tab and Enter take the highlighted one, the arrows move,
  Escape closes the list without closing the editor. It is the one plain `fetch` on the
  page: the query is the symbol at the caret, which is not a field htmx can include.
- **Enter submits a one-line editor.** The goal box is a `rows="1"` editor, so Enter has
  to submit the form rather than open a line inside it.

**The lookahead.** Under the editor's controls, `/edit/preview` says what the open save
would do — the same diff `edit-post` computes, read through `v/preview` instead of
`v/edit!`. `preview` hands the KB back at the same handles, so it is a read, and it runs
on a 600 ms pause in the typing rather than behind a confirmation. A form that does not
read is reported there too: the reader is told while the caret is still in the form that
caused it, instead of on the far side of a save that did not go through. It posts through
`writing` because a preview holds the single writer for its duration, exactly as the
proposal panel's consequence preview does.

## Untrusted input

Two things reaching a page are attacker-controlled, and the first is easy to miss:

- **query params** — `?q=`, `?ctx=`, the handle list;
- **KB content** — a Clojure symbol may legally contain `<` and `>`, and a `comment`
  carries free text, so a term or a comment is markup unless something escapes it.
  Content arriving from an importer or an agent is as untrusted as a URL.

So rendering escapes **by default**: pages are built with `hiccup2.core/html`, which
escapes strings in body position as well as in attribute values, and a node that must
emit literal markup opts in with `h/raw` — exactly one does, the pre-paint theme
script. `html` returns a `RawString`, so `resp` / `frag` coerce it for the ring body.
The regression tests live in `test/vaelii/web_test.clj`.

Reading a term or a goal is likewise guarded: `?q=(` is an EDN parse away from an
uncaught exception, so `/term` and `/levels` both parse through `->form`, which
answers nil for anything unreadable and renders a message.

### The browser reads what is stored, not what would be admitted

Escaping is the *display* half of that second bullet. The other half is shape, and it
has bitten three times, so it matters as a rule rather than as three fixes.
`assert` refuses a great deal — `wff` will not store `(disjoint A A)`, the naming
invariants keep a type node a symbol — but **an import does not go through `assert`**.
`import-dump` stores re-canonicalized records directly, and a translated ontology
carries both of those: a type disjoint from itself (which is how it says the type has no
instances) and a NAT used as a collection (which is how it names a type it has no atomic
name for). So a page may not assume of stored content anything only the assert path
enforces:

- **No two-element set literal over KB terms.** `#{a b}` with non-constant elements is
  the *checked* `RT.set` and throws `Duplicate key` when they are equal. Pairs are
  name-ordered vectors.
- **No bare `sort` over KB terms.** `compare` throws on a `PersistentList`, and a type
  node need not be a symbol. Every list is `sort-by str` — the ordering the list is read
  in, and the only one that exists for every term a KB can hold.
- **No assumption that a fact is binary, positive, or symbol-argumented** where an arrow
  or a pair is being drawn from it; the concept graph states each of those as a filter
  rather than discovering it.

Each has a regression test that injects at the **access facade**, since by construction
there is no `assert` that would produce the content.

## Design

- Rendering is [hiccup](https://github.com/weavejester/hiccup) 2 (`hiccup2.core`);
  pages are plain server-rendered HTML linking one stylesheet, with `{:mode :html}`
  under the html5 doctype. Interactivity is declarative htmx (`hx-*` attributes) plus
  the one small `vaelii.js` module.
- Handlers are pure functions `request -> response` (`web/app target` builds the
  ring handler), so they are unit-tested with mock request maps — no live server
  needed (see `test/vaelii/web_test.clj`).
- **The target is resolved per request, not closed over.** `app` takes a KB, an access
  value, or a *holder* — anything deref-able, which is what `vaelii.browser.catalog/holder`
  gives it. That is the whole of the KB switch: activating another entry in `/kbs`
  re-points every page at once, with no restart and no handler rebuild. The header
  carries the active KB's name, swapped out of band when it changes.
- The justification/dependency data comes
  from the in-memory JTMS graph (`jtms/supports`, `jtms/dependents`,
  `jtms/justification`) surfaced through `core`'s introspection fns
  (`sentex`, `justification`, `supporting-justifications`, `dependent-justifications`,
  `why`).
- Term values are passed as an EDN `?q=` query param (so compound terms like a
  nested sentence work); handles are path params.

## What the browser does not do

- **The header term search completes nothing into its own box.** It re-runs the search
  as you type (`keyup changed delay:400ms`) and swaps the results into `#main`, so what
  you pick from is the results list; the input sets `autocomplete="off"`, so the browser
  offers no history either.
- **A group's `· N stored` count is read when the page renders**, so a write that
  changes it shows on the next navigation rather than updating the rows in place.
- **The retract preview walks the justification graph itself** rather than asking the
  JTMS for the set its sweep would take, so it is a second implementation of that walk
  rather than a reading of the first.
- **Editing covers atomic facts and simple rules.** A rule's `exceptWhen` guard is
  dropped on re-assert, and the assert form cannot write one, so a guarded rule is not
  editable through the browser without losing its guard. (`unknown` is not affected —
  it is a literal in the body, not a meta-sentex.)
