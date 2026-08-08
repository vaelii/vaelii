# Web browser

- **Covers:** what each browser route shows — terms, sentexes, justifications, proof
  trees, the constraint network — and how the editor, assert form and proposal panel
  write through `edit!`.
- **Not here:** which KB sources exist and how one loads or switches →
  [catalog.md](catalog.md); the model that proposes lines for the panel to render →
  [llm.md](llm.md).
- **Assumes:** sentex, context, handle, justification → [glossary.md](glossary.md).

`vaelii.impl.web`. A small [reitit](https://github.com/metosin/reitit)-ring browser for
inspecting a KB. Run it with `lein run -m vaelii.web` (serves a starter-loaded KB
on `http://127.0.0.1:3000`).

```
lein run -m vaelii.web                            # loopback, a fresh starter KB
lein run -m vaelii.web --port 8080
lein run -m vaelii.web --listen 0.0.0.0           # reachable off-machine (opt-in)
lein run -m vaelii.web --attach HOST PORT [WEBPORT]

lein browser                                           # ...or a REPL with it running in it
VAELII_WEB_PORT=3010 lein browser
VAELII_WEB_PORT=3010 lein run -m vaelii.web            # the variable moves either one
```

`VAELII_WEB_PORT` is the default rather than an override: an explicit `--port` wins, and
a value that does not parse falls back to 3000 rather than refusing to start.

`--listen` and `--attach` are independent axes: `--listen` says who may reach the
browser, `--attach` says whose KB it shows. The startup log names the interface it
took.

### Working on it: `lein browser`

`lein run` gives you a page and no way in. **`lein browser`** is `lein repl` with the
browser already running: a prompt, a page, and a **reload channel** — `(require
'vaelii.impl.web :reload)` at the prompt, or over nREPL from an editor through
`.nrepl-port`, and the next request serves the new code.

That last part is the whole reason the command exists, because the failure it avoids is
silent. **A ring handler is a value, and Jetty holds the one it was started with**, so a
reload can redefine every var on the page and change nothing about what is served — the
namespace reloads, the page does not, and there is nothing to see. `start`'s `:reload?`
serves through `reloading-handler`, which reads `#'app` per request: a reload gives the
var a new function object, an identity check misses once, the routes are rebuilt, and
every request after that is the new code. A namespace the browser merely *calls* needs no
help — those calls already go through vars, so reloading `vaelii.impl.svg` lands on the
next request with nothing rebuilt. `-main` does **not** use it: a served process pays for
a reload it will never do.

**Both halves are loopback**, and the pairing is why it is not configurable from there.
The browser has a write route and no authentication; an nREPL is arbitrary code execution
by design. Either alone is a considered risk on a shared interface — together they are a
remote shell, so the profile pins nREPL to `127.0.0.1` rather than relying on
Leiningen's default, and the browser binds loopback with no way to say otherwise.
Exposing the browser stays the deliberate `--listen` on `-main`, which starts no REPL.

A port already in use is **reported, not thrown**: you asked for a REPL, and you get one
whether or not the port was free. `(vaelii.impl.web/dev-stop)` takes the server down
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
| `/` | the **upper ontology**: what the KB is in four numbers, then the genlContext context lattice, the genl type tree (from `thing`), the documented terms (the `comment` sentexes), and its disjointness. Every one of them is **bounded**, and where the whole is too long to read the page shows the top of a ranking rather than the first fifty of an order nobody chose — this is the first page opened against a KB whose size the reader did not choose (below) |
| `/stats` (`?clashes=1`) | **statistics**: headline counts (contexts, types, stored sentexes, and the contradiction / conflict / violation tallies), a contexts-by-size table ranked largest-first, and the actual dilemmas / conflicts / dropped-derivation violations when non-empty — each violation naming the run that dropped it. Every list on it is one screen and continues on scroll. `?clashes=1` additionally asks the **standing disjointness question** (below), which is computed on demand rather than filed |
| `/find?q=<pattern>` | **term search** over the KB's vocabulary: every term whose name matches (`re-find` semantics — a bare `dog` is a substring match, `^parent` anchors), each linked to its term page — the header search box points here. A pattern resolving to a single term (the only match, or an exact-name match) **jumps straight to that term's page** (`HX-Push-Url`) |
| `/term?q=<term>` | a **term**: a drawn picture of where it sits (below), its supertypes/subtypes/disjoint-with (if a type), then every sentex containing it grouped by the **index root** that reaches it — functor `[:functor-root]`, argument-position `[:argument-slot pos]` (the roster the predicate-agnostic read unions the scoped roots over), context `[:context-root]`, and the term-index `[:term-index]` remainder (rules, deeper nestings) — each group carrying its cheap count (O(1) for the roots; one O(1) read per predicate at the slot for the argument groups) |
| `/sentex/:id` | a **sentex** (atomic or rule): its **belief state** (IN, or the `why-not` reason — superseded / defeated / unsupported — with the restatement, contradictors, or missing antecedents that explain it), its supporting justifications (justifications concluding it), its dependents (justifications using it as an argument), and its terms |
| `/why/:id` | the **proof tree**: `vaelii.core/why` rendered whole — every justification down to the premises it rests on, collapsible, cycle-guarded, with rule sentences in the author's variable names |
| `/justification/:id` | a **justification**: its supports/arguments (antecedent sentexes) and its dependent sentex (the conclusion) |
| `/levels?q=<goal>&ctx=<context>` | the **lookup-to-query stack**: what each of the eight levels answers for a goal, which level first does, and — above them — the **query plan**: the provers bearing on the goal with their estimates and which one runs. A **vector** goal is a conjunctive query and gets the join plan instead (below) |
| `/network?ctx=<context>&calc=<calculus>` | the **constraint network** a qualitative calculus computes over a context: the tightened matrix (a cell is what still holds of row-to-column), whether the believed facts are satisfiable at all, and one scenario out of it. With no context, the six calculi and their vocabularies |
| `/demo` (GET/POST) | the **non-monotonicity walkthrough**: three stepped writes to the reader's sandbox in which `(flies Pingu)` is believed, stops being believed, and comes back — at a different handle. GET renders where the sandbox stands, POST runs one step. Every step writes, so every step is origin-checked (below) |
| `/reasoning` (GET/POST) | the **worked examples**: every kind of inference the shipped ontology performs, each a question with a live answer, the level that answered it, and links to the stored sentexes it reasoned from. GET computes every read-only card on render; POST establishes one example's premises in the reader's sandbox (below) |
| `/assert` (GET/POST) | the **new-sentex form**: sentences (one per line), a context, and the known-true switch. GET seeds it (`?q=<term>` from a term page); POST checks every line and applies them in one `edit!`, then says what followed (below) |
| `/edit` (GET/POST) | the **multi-sentex editor**: GET seeds a textarea for a set of selected handles, POST checks and applies the save. htmx fragments swapped into the editor panel, not standalone pages. |
| `/propose` (GET/POST) | the **proposal panel** at the foot of a term page: GET renders the instruction box (asking no model), POST runs one page-scoped turn through `vaelii.impl.llm.session/propose-page` and swaps the lines it proposed into `#propose-result`. The turn writes nothing (below) |
| `/propose/level` (POST) | the **same proposal at another density** — the list's own originals reposted, every verdict re-derived, no second model turn. Writes nothing |
| `/propose/line` (POST) | one reviewed line, **re-rendered on the shape the reader picked** — the numbered alternative is re-derived from `correct` and re-checked, so the chips are of the sentence that would actually be stored. Writes nothing |
| `/propose/preview` (POST) | what accepting the accepted lines would **mean** — the belief added, the belief withdrawn, the dilemmas opened, the refusals — through `vaelii.core/preview`. Writes nothing; the KB comes back at the same handles |
| `/propose/apply` (POST) | the accepted lines, checked whole and stored through `vaelii.core/edit!` in **one settle**. The panel's one write |
| `/retract` (GET/POST) | the **retract confirmation**: GET previews the teardown (the selection and what the sweep would take with it) and writes nothing; POST performs it |
| `/chain` (POST) | run **forward chaining** and answer with the `/stats` page it changed. POST-only — it derives and places conclusions |
| `/kbs` | the **knowledge bases**: what is loaded (with counts, an estimated footprint, and a progress bar for one still loading) and what can be — the shipped ontologies, a generated corpus with a slider per parameter, and every corpus / dump / store the catalog found. See [docs/catalog.md](catalog.md) |
| `/kbs/load`, `/kbs/unload`, `/kbs/activate` (POST) | **load** a source, **unload** an entry (cancelling it if it is still loading), **switch** to one. Each changes what this process holds, so each is a write: POST-only and origin-checked |
| `/kbs/export`, `/kbs/export/cancel` (POST) | **write the active KB out** as a portable dump — a destination directory, the variant and the compression — and **stop** one that is running. POST-only and origin-checked, like every other write |
| `/kbs/rows` | the loaded-KB panel, refetched once a second **while a load is running** — the trigger is in the answer, so an idle page stops asking |
| `/kbs/export/rows` | the export panel, on the same self-terminating poll: the last job's report, and whether what it wrote is now offered under **Available** |
| `/kbs/banner` | the **provisional-KB strip** every page carries when the KB it reads is not finished (below). Like the memory strip it is a read of the *process* and swaps only itself; it answers with the empty element once there is nothing to say, which is what stops the polling |
| `/sandbox/reset` (POST) | **discard this session's sandbox** — every sentex in it and the `genlContext` edge that made it a context. The only control in the browser whose purpose is to destroy knowledge, so POST-only and origin-checked |
| `/kbs/memory` | the **memory strip** heading that panel, collapsed or (`?detail=1`) expanded into the per-KB breakdown. A read of the *process*, not of a KB, so it takes no view. Two requests reach it and they are different requests: the header line **toggles** (it asks for the state the panel is not in), while the panel **refreshes** at the state it is in, and only while a load is running — one element carrying both would poll the toggle and flip the breakdown open and shut every tick |
| `/tree/rows?rel=<genl\|genlContext>&node=<term>` | one **level of a hierarchy**: that node's direct children, fetched the first time its disclosure is opened, and paged like any other list. `rel` reaches the index as a functor, so it is checked against the two transitivity relations rather than trusted |
| `/term/rows`, `/find/rows`, `/levels/rows`, `/front/rows`, `/stats/rows` | **continuations**: one more page of rows for a capped list. Not pages — bare `<li>`s a list's sentinel fetches for itself (below). The last two take a `?section=` naming which list on the page is continuing |

Everything is cross-linked: terms → sentexes → justifications → terms, any sentex can
be traced through the stack, and any believed one has its whole proof a click away.

### A term's shape, drawn

The three type lines on a term page say a term's supertypes, subtypes and disjointness
exactly. What they cannot say is its **shape** — that `dog` sits under `mammal` under
`animal`, that four things point at it and it points at two, that it is a leaf or a hub.
Shape is what a picture gives for free and a list never gives at all, so a term page opens
with one, above everything it says in prose.

**It renders live.** Server-drawn into the page, no click, no route, no state saying
whether it is shown. That is not the obvious choice, so: the reads are nearly all ones the
page already made (the relation flank comes off the index groups it built, and the taxonomy
is probed only in a direction the closures it already read say has something in it); a
reveal button on a picture nobody has seen buys a saved read from the readers who do not
want it and costs a round-trip to everyone who does; and no route means no `show=0`, no
collapsed-versus-expanded fragment, and no second entry point rendering the same thing with
different chrome. The whole feature is one function called from one place.

Being live is also what obliges the budget. **A picture nobody asked for may never be the
reason a term page is slow**, so the bound is part of the work and not a follow-up:

- **The graph adds at most 24 facade reads**, ever — twelve expansions, six per side, plus
  one O(1) count per row that actually elided. The radial view spends six. Every expansion
  is `(take (inc cap))` over a lazy pattern that pins an argument, so it costs the node's
  own fan-out and nothing more.
- **Measured** twice. Over the shipped schema plus the test-world cast: **2–10 reads** and
  **0.7–2.9 ms** a page (`dog` +3 reads / +0.7 ms, `animal` +10, a synthetic 5,000-subtype
  hub +9 / +2.9 ms). Over a generated 148k-sentex corpus — 44k terms, 4k types — a type
  page costs **+0.4 to +0.8 ms**, and the five widest individuals in it, up to 12,093
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

**A term is a context or it is not.** `genl` relates types and predicates, `genlContext`
relates contexts, `wff` refuses the mixture, and the naming invariants keep the two
vocabularies apart — so there is exactly one subsumption relation per term page and the
class on its edges says which. That is also what makes a context page worth opening: `genl`
says nothing about contexts, so the three type lines there are empty and the picture is the
only thing on the page that shows the lattice at all.

**What is and is not an edge**, stated rather than left to fall out of the code. Binary
facts only — a ternary `(argIsa parentOf 1 person)` relates three things and an arrow
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

**Drawn with no library.** `vaelii.impl.svg` is a node, an edge, an arrowhead and the
arithmetic that lays out a row, a column or a ring — pure, KB-free, tested on hand-built
maps. No Graphviz shell-out (a page that renders by starting a process is a page that
cannot be served), no d3, no cytoscape, no build step, and nothing added to `project.clj`:
the client is two JavaScript files and a graph library would be the largest thing in it.
Node colour is `term-class`'s class resolving to the same `--t-type` … `--t-context` custom
properties the links beside it use, so the picture is theme-aware for free and cannot drift
from the text. Every node is an `<a href="/term?q=…">` — the graph is navigation, not
decoration — and clicking one is the whole interaction model: no pan, no zoom, no drag, no
physics.

**The text stays.** The Supertypes / Subtypes / Disjoint-with lines are unchanged and in
place; they are the accessible equivalent of the picture and the exact answer it
approximates. The `<svg>` carries `role="img"` and an `aria-label` saying what it shows and
that the same terms are listed below as text. And the whole thing is wrapped: this is the
one part of the page that does arithmetic on KB-derived numbers, so a throw costs the
figure and nothing else — the page is still 200 and still complete.

### Somewhere safe to be wrong

Every browser session gets a **sandbox**: a scratch context of its own, hung below
`WellContext`. `vaelii.impl.sandbox`.

The asymmetry is the whole design, and it is not a permission check. `genlContext` already
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
  editable, and anyone who knows they want `NaturalWorldContext` can type it.
- **Reset is a real teardown**, not a flag — every sentex in the extent through `edit!`'s
  `:remove`, then the `genlContext` edge, which is not in the extent because
  `genlContext` is forced-decontextualized and therefore stored in `UniverseContext`. The
  dependency-directed sweep takes the derived conclusions and their justifications, so the
  KB comes back to its pre-session sentex *and* justification sets exactly.
- **It appears in the chrome as a place, never as a context picker** — a `Sandbox` nav
  item leading to the assert page, which names the context and offers the reset.

Promotion — moving something out of a sandbox into a context that outlives it — is
deliberately absent. A dead end that cannot be half-escaped is easier to reason about than
one with a door in it.

One limit worth stating: a session cookie that is dropped (the browser closed) leaves its
sandbox in the KB with nothing pointing at it. For the default browser, whose `-main`
clears and reloads the starter each start, they cannot accumulate; against a persistent KB
they do, and nothing collects them.

### Belief that changes

`/demo` is the one page that argues rather than reports. Three clicks, in the reader's own
sandbox:

1. assert `(bird Pingu)` — `(flies Pingu)` becomes believed, and nobody asserted it
2. assert `(penguin Pingu)` — `(flies Pingu)` stops being believed, and nobody retracted it
3. retract the penguin claim — it is believed again

Nothing about the page is special-cased in the engine. Each step is an ordinary `v/edit!`
against the sandbox, the page is re-read from the KB *after* the write rather than rendered
from what it intended, and every handle on it links to the record it names — which is the
whole point, since the claim being made is that this is the engine and not a story about
one. Which step is offered comes from the KB too (`demo-state` reads what is stored), so a
reader who reloads, navigates away, or resets lands on the line that is actually true.

Two things it is careful to show rather than assert:

- **The cascade.** All five sentences the script touches are rendered at every step, with
  their live belief pills: `(canTravel Pingu)` disappears alongside `(flies Pingu)` and
  comes back with it, and `(not (flies Pingu))` appears in step 2 — the KB does not merely
  fail to conclude flight, it concludes flightlessness, which is a different statement.
- **The returning conclusion is a new record.** `exceptWhen` blocks rather than rebuts, so
  the blocked justification is *invalid*, groundability goes with it, and the
  dependency-directed sweep deletes the conclusion outright ([exceptions.md](exceptions.md)).
  Revival is therefore a re-derivation: step 3's sentex has a handle that never existed
  before, and step 1's handle resolves to nothing. The page names both side by side and
  links the new one, because that is the sharpest evidence on it — the engine did not hide
  the conclusion and put it back, it forgot it and re-earned it, and the proof being
  identical while the record is not is a thing a slideshow could not fake.

The individual is the only content the demo creates; the rules are `BiologyContext`'s
shipped ones. Step 2 reads `why-not`'s **sentence** arity, which exists for exactly this
case: a blocked conclusion has no handle to ask about.

### What the ontology can work out

`/demo` argues one thing at length. `/reasoning` is the breadth: a card per kind of
inference the shipped ontology performs, each a real question with the answer the KB gave
when the page was drawn. The table is `vaelii.impl.examples`; the page is the rendering of
it.

Two properties keep it from being a brochure, and both are load-bearing:

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
`argPreserving`, disjointness, the predicate meta-ontology — is answerable with no write
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
  a banner: it is reachable at `:ready` — a store opened without `:recover?`, a dump
  imported with `:belief? false` — so nothing about the KB's status hints at it, and a
  reader's obvious conclusion is that the import failed.

The entry cards on `/kbs` name what switching gets you rather than offering one button
for two different answers: *Switch to* for a finished KB, **Browse as it loads** for one
still arriving, **Browse what landed** for one that stopped part-way — which is usually
the reason to have stopped it.

**The reads open, the writes wait.** A KB can be read while a loader fills it; it cannot
be *written* while one does. A store mutation lands atomically, so a reader beside the
loader sees a consistent prefix — but two interleaved writers are not serializable at
all ([storage.md](storage.md), the single-writer contract), and the loader is already
this process's writer. So every route that changes a KB's content goes through
**`writing`**, which is the origin check and that question together: `/chain`, `/assert`,
`/edit`, `/retract`, `/demo`, `/reasoning`, `/sandbox/reset`, `/propose/apply` — and
`/propose/preview`, which reads by really asserting and rolling back, and is therefore a
writer for the duration. `/kbs/load`, `/kbs/unload` and `/kbs/activate` are **not**
guarded: they write this process's registry rather than a KB, and cancelling a load has
to stay reachable precisely *because* one is running.

The refusal renders as a **page**, not an error status, for the reason a catalog refusal
does: an error status leaves htmx not swapping at all, so the write would look like it
silently vanished. The check is narrow on purpose — it asks whether the *active* entry is
the loading one, so loading a second KB in the background never stops you writing to the
one on screen.

`/kbs/export` is not guarded either, for a third reason: it writes the *filesystem*
rather than a KB, so a load filling some other KB is no reason to refuse it. What an
export cannot survive is the KB it is walking being written, and that is
`catalog/export-entry!`'s own refusal to make ([catalog.md](catalog.md)).

## Writing a KB out

The Export panel on `/kbs` is the return leg of the loop the Available list is the
outbound half of. It writes the **active** KB as a portable dump — a destination
directory, the variant (`records` or `records+index`) and the compression — on the
catalog's own job thread, so the page keeps answering and the panel polls itself only
while there is something to watch.

Two things it says that a bare progress bar would not. A finished job reports **where the
dump went and whether the catalog can see it there**, asked of `catalog/sources` rather
than assumed: a dump written outside `VAELII_KB_PATH` is a perfectly good dump this page
will never offer, and silently not appearing under Available is the confusing outcome. And
when the active entry is an **attached daemon** the form is replaced by a sentence saying
so — its dump would be written on that daemon's host, and a path field that quietly named
a directory on the wrong machine is the one failure mode here worth designing out.

## What a page costs

The browser is the standing test of the public read surface, so what a page *costs* is
part of what it demonstrates — every `v/…` call is a store read in-process and an HTTP
round-trip under `--attach`.

- **A page is answered as the fragment that lands.** `hx-boost` and the header search
  both swap `#main`, so a request carrying `HX-Request` is answered with the `#main`
  element and a `<title>` (htmx lifts a title out of a fragment to retitle the tab) —
  no head, no header, no selection chrome. A request **without** it gets the whole
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
  contradictor), and it fetches exactly the one record it needs.
- **Disjointness is one pass.** `disjoint?` holds when some supertype of x and some
  different supertype of y are separated. Read from the term's side that inverts: the
  separated partners of the term's own supertypes are what matter, and the types
  disjoint from the term are exactly those partners' spec closures — a closure read per
  partner (there are one or two) instead of a `disjoint?` per type in the KB.
- **The three type lines are capped, and the widest of them is bounded before it is
  built.** Supertypes and subtypes come off cached closures, so their counts are free and
  exact and only the sort has to be given up past `sortable-cap`. The separation line is a
  *union* of the partners' closures, and building one to show fifty entries is the same
  defect the graph avoids: an imported ontology gives one NAT collection 43 partners
  spanning 289,947 subtypes, and a union over all of them costs a second and a half to
  produce a list nobody can read. The sum of the closure sizes is free — every closure is
  a cached set — so it is taken as an upper bound (it counts an overlap twice) and, past
  the budget, only the window is walked and the caption says "up to". The bound is what
  keeps a term page of a real ontology usable rather than merely slow: on that ontology
  `/term?q=thing` renders in **229 KB and 0.39 s**, the NAT collection's page in 19 KB and
  0.24 s. Unbounded, both are megabytes, and a browser cannot be clicked through either
  once it arrives.
- **The concept graph is bounded before its first read, not after.** Its relation flank is
  read off the index groups the term page built anyway, its taxonomy is probed only where
  the closures the page already read say there is something, and every expansion is spent
  from one hard budget — twelve, six a side — so the picture costs at most 24 reads
  whatever the fan-out. Capping what is *drawn* is not capping what is *read*, and a page
  that draws eight of forty thousand subtypes by reading forty thousand looks identical on
  the shipped schema.
- **Search reads the vocabulary, never the sentexes.** `/find` filters the index's term
  roster through `vaelii.core/find-terms`, so it costs the number of distinct terms.
  A query carrying no regex metacharacter is matched as a **substring** — exactly what
  `re-find` of a literal means — so the type-ahead path compiles no pattern at all;
  only a query that is actually a pattern reaches `re-pattern`, and only up to a
  **128-character cap**, since the route is reachable per keystroke and, through the
  daemon, by whoever can reach it.

The result, over the starter plus the test-world cast: `/term?q=genl` renders in 11 KB
reads, `/find?q=do` in 2, and the `/find` fragment is 373 bytes against a 2.7K document.

## Selecting sentexes

Selection is the most-touched interaction in the tool, so every route to it works. A
selectable row is an `.sx-item[data-h]` list item (the term, sentex, and justification
pages), and the list it sits in is a single-column ARIA **grid**:

- **Click** a row — its checkbox, or anywhere in it that is not a link — to toggle it.
  A click on a *link* inside the row still navigates, so the row is selectable without
  becoming a dead zone; the checkbox is there so the toggle target is never ambiguous.
- **Shift-click** anywhere in a row (link included) selects the contiguous run from the
  last row touched, in the order the page shows them.
- **Press-drag** a marquee across the rows for a sweep, shift+drag to add to what is
  already selected. A plain press is not a drag until the pointer moves 5px, so a click
  stays a click.
- **Keyboard.** The list is one Tab stop — a **roving tabindex** puts `tabindex="0"` on
  the row holding the keyboard's place and `-1` on the rest. From a focused row: ↑/↓
  move (Home/End jump to the ends), **shift**+↑/↓ extends the selection as they go,
  **space** or **enter** toggles, and **escape** clears the selection and closes an open
  panel. Escape works from anywhere; everything else is scoped to a focused row, so the
  page still scrolls and the search box still takes its own keys.
- **Select all in a group** — every index group on the term page, and every sentex list
  elsewhere, carries a control that takes the whole list at once and clears it on a
  second press (it says which it will do).
- **ARIA.** The `<ul>` is `role="grid" aria-multiselectable="true"`, each row a
  `role="row"` carrying `aria-selected`, its content a `role="gridcell"`. A grid rather
  than a listbox because a row is *made of* links, which a listbox option may not
  contain. The selection count is a live region (`role="status"`), so a change announces
  without the page moving, and the focused row takes a visible ring.

None of that is htmx-expressible, so it is the first of the five jobs
`resources/public/select.js` does (below).

## Editing sentexes

The browser is not read-only: sentexes can be **asserted, edited in bulk, and
retracted**. Every write goes through `vaelii.core/edit!` via the access facade, so each
is **one settle** and works the same in-process or attached to a daemon.

Once ≥1 sentex is selected an **action bar** appears, with **Edit**, **Retract…** and
Clear.

- **Edit** opens a textarea seeded with one `[sentence context]` line per selected
  handle — `[sentence context opts]` when the sentex is known-true, so its
  `:strength` survives. A rule is shown with its direction/defeasibility as `set/*Rule`
  wrappers (its `exceptWhen` guard is a separate meta-sentex and is *not* carried, so
  editing a guarded rule drops the guard; an `(unknown S)` antecedent is an ordinary
  literal in the rule body and round-trips).
- **Save** POSTs the edited text. The server diffs the lines against the selection **by
  content**: a line you left alone touches nothing (its handle is untouched, no churn),
  a line you changed or deleted retracts its sentex, a new line is asserted. The batch
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
  is dependency-directed, so the panel lists the selection **and** the believed sentexes
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
  deleted when the line was deleted — and the selection count is corrected the same way.
  Rows are addressed by their `data-h` attribute rather than by an id, because one
  handle can appear in more than one index group on a term page and htmx's selector form
  of `hx-swap-oob` swaps **all** the matches, so every copy of a row moves. A line is
  paired with a handle **by position**: the textarea is seeded one line per selected
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
  The second layer is the write guard. Nine routes go through
  `writing` above: `/edit`, `/assert`, `/retract`, `/chain`, `/demo`, `/reasoning`,
  `/sandbox/reset`, `/propose/apply` and `/propose/preview` (a writer for the length of
  the rollback it does). Nothing authenticates them, so each compares the request's
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
stack trace. It costs nothing when the content is fine, and the alternative — attempt
the write and catch — writes the good half of a batch before failing on the bad half.

## Proposing knowledge

A term page says what the KB knows about a term. The panel at its foot is where a reader
asks a model what it is *missing* — `vaelii.impl.llm.session/propose-page`, which is
shown the page's own sentexes and the vocabulary the term's `genl` neighbourhood
licenses, and answers with type-level assertions in that vocabulary. See
[docs/llm.md](llm.md) for the path itself.

What the browser adds is the bounds:

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
  start (`warm-model`), because the latency of a local turn is model *load*: 11.33 s,
  then 0.39 s, then 0.30 s for three identical turns.
- **POST, and origin-checked.** The turn writes nothing but it *spends* something — a
  model, and on a local host a GPU — so a page on another site must not be able to make
  this browser run one.
- **`--attach` cannot serve it.** A proposal reads the term's neighbourhood, its
  vocabulary and its checks through dozens of KB calls, which is not a thing to run a
  round-trip at a time against a daemon; `access/local-kb` answers nil there and the
  panel says so instead of degrading silently.

### The chip gutter

A proposed line has **four independent things** worth knowing, and prose buries all of
them. `vaelii.impl.llm.verdict` gathers them per entry and the panel renders each as a
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
- **What shape it should have been in** — `vaelii.impl.llm.correct`. The original is
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
  contract, so the chips a reviewer commits against are computed from the shape that
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
`vaelii.impl.gloss` out of the KB's own `comment` sentexes — it reaches no model at all.

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
documentation for a reader rather than template. 175 of the 277 comments the starter
ships carry such a signature; the 102 that do not are read as descriptions instead. 96 of
those are types, units and dimensions, whose comments are noun phrases — which is what a
type gloss wants, since it reads "X is a dog" and the comment is the apposition after it.
The other six declare a compound or variable-arity argument (`(implies (and ?antecedent
…) ?consequent)`, `(lessThan ?number1 ?number2 …)`), which cannot be substituted into
position by position. Measured over every believed sentex in the shipped schema, 1,317 of
1,321 gloss with zero model calls — **99.7%**. `gloss_test` holds the composition rate to
a **95% floor**, so the percentage is a reading of the schema as it stands and the floor
is what is guaranteed.

The variables are load-bearing twice over. A parameter spelled `?place` cannot be
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
- **Recomputed on the accepted set, debounced.** `select.js` fires one
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
chose, each literal with the fan-out it was estimated at and the variables already bound
when it starts. The estimates deliberately do not read as a sorted column: each is made
*under the bindings the ones above it produce*, which is sideways information passing and
is the thing worth seeing. A literal whose position is operational rather than costed is
marked **pinned** — an evaluable may not outrun what binds it, and a recursive rule's
recursive literal stays last so right-recursion survives. One is marked **cartesian**:
sharing no variable with the rest, it multiplies the row count of everything after it
wherever it runs, so it is held to the back on that structure and the estimate beside it
is not what placed it — which is worth saying, since a selective one otherwise reads as a
small number sitting last for no reason. A literal sharing no variable but matching at
most once multiplies by at most one, so it leads like any cheap literal and is not
marked. The eight levels answer about one literal, so a
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
come back. So a tail nobody scrolls to costs nothing, and one that is scrolled to is
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
(`hx-select="unset"`). A sentinel ending a *selectable* list is a `role="row"` of that
grid, since a grid's children must all be rows; the plain lists take the plain shape.

### The front page is bounded, and that is not a nicety

`/` is the first page anyone opens against a KB whose size they did not choose — the
catalog will load an ontology with hundreds of thousands of `genl` edges — so nothing on
it may be proportional to the KB.

The **hierarchy trees** open one level at a time. A node with children is a `<details>`
that fetches them on its first `toggle`; a level is read by pinning the parent
(`(genl ?sub node)`), which the index answers from the predicate-scoped argument root
(`[:argument-root genl 2 node]`), so the cost is that node's own fan-out rather than the
number of edges in the KB. Whether a node gets a disclosure at all is
`count-with-arg 2 node`, a cheap upper bound (one O(1) count per predicate at the slot):
it spans every binary predicate holding the node in second position, so it can offer a
disclosure that opens to nothing, and can never hide a real child.

The **flat lists** read their functor root rather than a wholly-open pattern. `(comment
?term ?text)` pins nothing, so the trie fans over every child token at every level: a
`take` would bound the records fetched and not the candidates enumerated, which is a walk
of the whole extent to show fifty rows. Sorting is bounded the same way — alphabetical
order is worth having and costs nothing at the shipped schema's size, so a list sorts
when its O(1) count is under a thousand and is in index order, saying so, above it. The
same rule governs a tree level, and where a level was not sorted its sentinel says "show
more" rather than a count it did not pay for.

The **context lattice** is the one thing still read whole, because a root is a context no
edge makes a sub of anything and that is a property of the entire edge set — there is no
partial answer. Past `lattice-cap` edges the page cannot root a lattice, and what it shows
instead is the section below.

### A cap is not an answer: rank first, then cap

Bounding a list stops a page being megabytes. It does not make the page *useful*, and on a
real corpus the two came apart completely: fifty of 13,196 contexts alphabetically, fifty
of 27,196 separated pairs, `thing` → fifty of 6,260 subtypes in index order. Each was a
short answer to nobody's question — an arbitrary sample of a long one — and no amount of
scrolling fixes it, because nobody scrolls 27,196 pairs looking for the interesting one.

So where a **cheap ranking** exists, the page shows the top of it and says what the whole
is; where one does not, it caps and continues. Cheap is the constraint, and it is a real
one — the rankings taken are the ones the index already answers in O(1):

- **Contexts, by what they hold.** `count-in-context` is one set-size read each, so the whole
  ranking is `n` O(1) reads (150 ms over 13,196, and past `context-rank-cap` the page says
  it cannot rank rather than spending it). This is the ranking that earns its keep: a
  corpus's mass is not spread evenly over its contexts, and the four largest name the
  subject outright — `UniversalVocabularyContext` 609,798, `GeneOntologyContentContext`
  119,192, `BaseKBContext` 63,497, `ComputerSoftwareDataContext` 32,469. Fifty alphabetical
  context names said none of that. It is the front page's lattice fallback and the whole
  of the stats table.
- **Types, by how many things they are separated from.** One frequency pass over the pairs.
  Below the cap the pairs themselves are the answer and are listed as before; above it,
  what a reader can use is which types the ontology's partitions are *about*, each linking
  to its own page where its partners are now listed.

And one ranking deliberately **not** taken: ordering the type tree's 6,260 children of
`thing` by subtree size reads far better than index order — `individual` and
`partially_intangible` instead of `aura_flight` — and measured **2.2 s**, because it is a
closure read per child rather than per row shown. The tree stays in index order and stays
lazy. A ranking that costs more than the page is not a ranking the page can have.

The front page also opens with **what the KB is** — sentexes, types, contexts, terms, four
O(1) reads, the question a reader landing on an unfamiliar corpus asks before anything
about its contents. The section titled "Core predicates" says "Documented terms" wherever the KB has more commented
terms than it can sort: on the shipped schema every one of them is engine vocabulary, and
on an imported corpus there are 105,882 and calling those core predicates is a claim the
page cannot make.

Measured on an imported OpenCyc corpus (1,173,442 sentexes — exact counts move with the
import profile), `/` renders **36,045 B in
250 ms** and `/stats` **24,759 B in 86 ms**. What the ranking and the cap buy is visible
in what they decline to do: sorting 27,196 separated pairs by name to show fifty of them
is a second of front page, and 4,721 context rows beside fifty contradictions — each of
those a pair of whole sentences with every subterm linked — is a megabyte of stats page.

Measured against a synthetic wide taxonomy, the bounded front page holds flat where
reading the whole edge set does not:

| genl edges | reading every edge | `/` |
|---|---|---|
| 47 | 1.9 ms | 2.9 ms |
| 2,047 | 19.3 ms | 3.7 ms |
| 8,047 | 77.7 ms | 3.4 ms |
| 32,047 | 357.7 ms | 9.8 ms |

The middle column is the reads alone; drawing a node per edge grows the document with the
KB on top of that. The bounded page holds at ~15–22 KB throughout.

**This is the only pagination there is**, so it has to hold at any size — a term with
thousands of sentexes is walkable one sentinel at a time, every row reachable, none
served twice, and the walk terminates. `web_test` proves it over 2400 sentexes on one
predicate: 40 pages of 60, then the sentinel stops.

## Rendering sentences

A sentence is rendered structurally, not as one opaque string:

- a **handle badge** stands before the sentence in place of the bare `#id` — a
  small colour-coded square that links to the sentex page and encodes, at a glance,
  what the handle *is*: **indigo** for a rule, **violet** for an asserted (premise)
  fact, **teal** for a derived one; its glyph is the rule's direction (`→` forward,
  `←` backward, `↔` both, `·` inert) or the fact's polarity (`•` positive, `¬`
  negative); a **dashed** border marks a defeasible (default) rule, and a **dimmed**
  badge a sentex that is stored but not believed. Its `title` carries the handle and
  a plain reading, so the number is a hover away and lists stay scannable;
- **each subterm is its own link** to `/term?q=<subterm>` — click the predicate,
  an individual, or the context independently (nested compound subterms are also
  listed individually under a sentex's *Subterms*);
- terms are **colored by role** — type (green), individual (purple), predicate
  (blue), context (brown), number (red), variable (grey). A type is recognized by
  membership in the genl taxonomy, so `dog` colors as a type while `parentOf`
  colors as a predicate — and that membership is checked **before** the non-symbol
  fallback, because a type node need not be a symbol: an imported ontology names a type
  it has no atomic name for with a function term, and 17,211 of OpenCyc's 132,352 are
  compounds. Reading those as numbers is a page in the wrong colour. A legend is shown
  on the home page.

### A reified term is never shown as its constant

A ground `(F a…)` under a `reifiableFunction` is stored as an opaque constant in the
reserved `nat/` namespace ([nat.md](nat.md)) — that is how a function term gets indexed,
retracted and truth-maintained like any symbol. A `nat/`-namespaced gensym is not a name
anybody wrote and says nothing to a reader, so **no page shows one**. Every term goes through
`term-link`, and a reified one renders as the expression it was minted from:

> **(** `FruitFn` `AppleTree` **)**

The **bold parens are the whole of the notation**, and they are load-bearing rather than
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
identity. What is left holding the constant is what a machine reads back: the `href` of
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

- A **header** carries the vaelii logo and monospace wordmark (a home link) at the
  left, then — pushed to the right — a **menubar** to the top-level tools (Ontology
  `/`, Reasoning `/reasoning`, Query `/levels`, Assert `/assert`, Sandbox `/assert` —
  the sandbox is reached as a place to write, never as a context to choose — Network
  `/network`, Stats `/stats`, and KB `/kbs` carrying the active KB's name; select.js
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
- **Two typefaces, one weight each.** [Hasklig](https://github.com/i-tu/Hasklig)
  (monospace) sets the *formal* content — sentences, terms, handles, index keys, the
  query inputs — so a KB reads like the code it resembles.
  [Atkinson Hyperlegible Next](https://www.brailleinstitute.org/freefont/)
  (proportional) is reserved for *natural-language* text only — headings, prose,
  section labels, the predicate comments; proportional never touches a sentence. Both
  are vendored under `resources/public/font/` and served self-hosted, and each ships
  its **regular only** — two files, 102K, the whole webfont budget. The heavier levels
  the sheet asks for (`font-weight: 600` on the wordmark, a type term, an active
  menubar link, a table head) are **synthesized**; headings sit at the regular weight
  and take their hierarchy from size and space. Declaring each family at 400 alone is
  what keeps synthesis available — a `400 700` range would claim the face covers bold
  and flatten emphasis instead.
- **htmx** ([vendored](https://htmx.org), `resources/public/htmx.min.js`, 2.0.9) drives
  the declarative interactivity. `hx-boost` on the body turns ordinary links and forms
  into ajax swaps with history (degrading to plain navigation when htmx is absent),
  scoped to `#main` — which is what lets the server answer with the fragment that lands,
  and what keeps the header, the selection bar, and an open editor from being torn down
  by a navigation. Scoping it costs one thing back, which the swap pays explicitly: a
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
- **One hand-written script**, `resources/public/select.js` (vanilla, no build step, no
  dependency), for what htmx cannot express: the selection above — click, shift-click,
  keyboard, group control, and the marquee drag — the palette and theme dots
  below, marking the menubar link for the current path active, the `/kbs` sliders, and
  the proposal review's keys (`j`/`k`, `a`/`x`, `1`–`9`). The review holds a decision per
  row *index* rather than per element, because choosing a shape swaps the row out from
  under it; picking a shape only clicks the numbered button, and a change in the accepted
  set dispatches one `accepted-changed` event the consequence panel's own `hx-trigger`
  debounces — so both round-trips stay declarative like every other one. It re-syncs
  after every htmx swap: a navigation replaces `#main`, which voids the selection; a
  save or a retract swaps individual rows out of band, which prunes it (a handle whose
  row has left the page is no longer selected); a continuation page of rows re-applies
  the highlights over whatever is now on the page. So the count, the action bar, the
  roving tabindex and each group control follow the page rather than drifting from it.
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
    text a filled accent carries. The wordmark, the selected-row tint, the marquee, and
    more **derive** from `--accent` with `color-mix`, so one value re-colours the whole
    chrome. Rainbow keeps violet's accents and paints the wordmark, the primary button,
    and the header rule with a gradient (`--rainbow`) instead.
  Palette and theme are orthogonal: any palette works in light or dark. Each palette
  declares both modes' values in one place (`--lt-*` / `--dk-*`) and the mode blocks
  pick a side, so the two can't drift apart. Light accents are deep and carry white
  text; dark accents are pastel and carry near-black — which is what `--on-accent`
  names, and why no filled surface hard-codes `#fff`.
- The fonts, logo, favicons, htmx, and select.js are static files under
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
has bitten three times, so it is worth stating as a rule rather than as three fixes.
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
  the one small `select.js` module.
- Handlers are pure functions `request -> response` (`web/app target` builds the
  ring handler), so they are unit-tested with mock request maps — no live server
  needed (see `test/vaelii/web_test.clj`).
- **The target is resolved per request, not closed over.** `app` takes a KB, an access
  value, or a *holder* — anything deref-able, which is what `vaelii.impl.catalog/holder`
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
