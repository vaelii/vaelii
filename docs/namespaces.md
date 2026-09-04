# Namespace layout

- **Covers:** which source file holds each namespace, and the split between the six public
  namespaces and `vaelii.impl.*`.
- **Not here:** the one-line summary of every subsystem doc → [README.md](README.md); the
  public API's function signatures → [api.md](api.md).
- **Assumes:** sentex, context, JTMS, canonical form → [glossary.md](glossary.md).

What lives where, one line per file. The public surface is **six namespaces** —
`vaelii.core` plus five thin entry points (`vaelii.client`, `vaelii.starter`,
`vaelii.web`, `vaelii.serve`, `vaelii.cli`) — and everything under `vaelii.impl.*` is
free to change — tests reach into `impl` freely, nothing outside this repo should
([api.md](api.md)). `vaelii.koinii.*` is neither: it is an **application** shipped in
this tree, a consumer of those six exactly as an outside caller is, which is why it sits
beside `impl/` rather than in it ([koinii.md](koinii.md)). The per-subsystem notes are
indexed in [README.md](README.md); this is the file map that sits under them.

```
src/vaelii/
  core.clj          THE PUBLIC API — KB; forward chaining + context placement;
                    checks; settle; every fn in docs/api.md
  client.clj        public shim over impl/client.clj: the thin daemon client, spelled
                    as vaelii.core spells it (bare assert / assert-rule, retract!)
  starter.clj       public shim over impl/starter.clj: load-into, the shipped
                    schema-only ontology into a KB you opened
  web.clj           public shim over impl/web.clj: handler / start / -main for the
                    browser (the dev-only affordances stay in impl)
  serve.clj         public shim over impl/serve.clj: the daemon — ops / app / start /
                    port / -main
  cli.clj           public shim over impl/cli.clj: open-kb-from / dispatch / -main

src/vaelii/koinii/
                      AN APP, not the engine: multi-agent coordination over one shared
                      KB, built on the six above and requiring nothing under impl/
                      ([koinii.md](koinii.md))
  identity.clj      per-agent contexts as the identity substrate and the write boundary;
                    the admin-only registry and the `authenticate` policy seam (D4/D8)
  speech_acts.clj   the CxSpeechActs vocabulary: origination (assert / pose-query) and
                    the response acts, each a meta-sentex on its target (D1/D5)
  channel.clj       the coordination library: the `Medium` protocol (wire / local), join,
                    the reply verbs, subscribe/unsubscribe, and the recovery reads (D7)
  dispute.clj       per-channel dispute reads over `argue`, plus the dispute id and the
                    four-state lifecycle vocabulary (D9)
  adjudication.clj  the three policies over those reads — leave-open-and-notify (the
                    default), arbiter ruling, majority vote — with the clock and sinks
  belief.clj        belief projection into an agent's own context, and own-statement
                    `disregard` through the `except` mask
  catchup.clj       CDC snapshot+tail for an agent that fell off the feed's ring, and the
                    client-side `CursorStore` (D6)
  deref.clj         the independent-seat topology: content-addressed locators, Merkle
                    commit ids, and untrusted-marker dereference

src/vaelii/impl/
  protocols.clj     RecordStore, IndexStore (trie + roots + rule index + exception re-check index + term index, the term roster beside it) —
                    declarations only, so cloverage can skip the file whole (see its docstring)
  capabilities.clj  the fallbacks beside the optional capabilities: count-sentexes / some-*-id,
                    sentex-sink, mark-premises, prefetcher + hinting — each the capability when the
                    store has it, else the loop it replaces
  reads.clj         the two named doors onto the index: `as-stored-*` (the index store, and each says what a stored-but-disbelieved answer is for) beside `believed-*` (the KB, filtered by `jtms/in?`); the cardinalities, the vocabulary roster and the watched-rule roster carry one door each and say why there is no second.  Every raw `protocols` index read outside the implementers comes through here, and `lein lint`'s E16 is what keeps that true ([nmtms.md](nmtms.md#belief-filtering-is-a-namespace-boundary))
  predicates.clj    what is *said* about each term of the engine's own grammar, in one place — shape, storage kind, the closed facet vocabulary naming which lanes read it, the mark family a spelling belongs to, and what a late-arriving declaration sweeps. Requires nothing but `clojure.*` and so sits below everything, which is the whole design: the arms need functions from four layers, so a namespace holding data *and* arms could only sit at the top, where `taxonomy` and `wff` could not read it. The functor-keyed rosters above are projections of this: `taxonomy`'s three (`closure-relations`, `arg-declaration-props`, `functional-family-marks`), `settle`'s eight clash and trigger rosters, `spec/::prop-kind` and `vocabulary/roster` are field reads of it, and `predicates_test` reconstructs the ones that have not moved yet. A roster that has moved states its value as a literal in the test instead, since reconstructing a derived var proves the wiring and nothing about what it holds. `check-families` refuses at load a family whose spellings disagree about the lane they sweep in, or one that sweeps at an arity it declares no shape for. The fields, the vocabularies they are written from and the sequence for adding a term are [predicates.md](predicates.md). `special/entries` is the join of these declarations with `special`'s arms — the order, each `:props` kind and each derivation-path flag come from here, so `special_table_test` freezes their values in a literal that nothing derives
  naming.clj        naming-invariant predicates + functor/args/arity
  sentex.clj        Literal / Rule records (connectives → polarity/antecedent/consequent), split so a fact drops the rule-only slots; canonical vars + varmap, literal order, symmetric args, comparison folding/chains; canon (+ symbol interning); α-renamed path; index-terms
  rules.clj         rule-as-sentex helpers (implies form, predicates, range check, exception closure, the two polycanonicalization expands — conjunctive consequent and disjunctive antecedent, with the width cap and the per-alternative range check ([canonicalization.md](canonicalization.md)) — the generator's hole split and its nesting — [generators.md](generators.md))
  taxonomy.clj      cached genl / genlCx closures, each read twice over — `genls` / `specs` / `genl?` / `context-up` walk the edges a context sees, and `genls-global` / `specs-global` / `genl?-global` / `context-up-global` walk every active edge, spelled out because on an unrestricted KB the two return the same object (E17 rosters the global callers); the equality partition (representative / equiv-class / deprecated?); maximal-common-descendant-contexts
  strength.clj      assumption strengths + defeat-class lattice (monotonic>default)
  kv.clj            KvBackend protocol + the one KvIndexStore over it: trie + context/functor/arg roots + rule predicate index + exception re-check index + term index; `index-layout-version`, the number that says which key shapes a build reads
  memory.clj        default backend: in-memory RecordStore + MemoryKvBackend, shared per space number
  dense_kv.clj      the :memory-dense index: IntPostings handle sets (sorted int[], promoted to RoaringBitmap past 128)
  dense_jtms.clj    the :tms :dense network: the same graph in bitmaps + primitive-keyed maps, behind jtms-protocol/Tms
  columnar.clj      the :memory-columnar index: a native int-token trie in parallel arrays — mutable, CSR-compactable by `compact!`
  dense_roots.clj   its roots + rule/exception/term indexes as one packed-long-keyed fastutil map, over the same dictionary
  tokens.clj        the path-token ↔ int dictionary those interned edges decode through (in RAM; disk/tokens.clj is the durable one)
  disk/files.clj    on-disk substrate: append-only nippy-framed logs + fixed-width idx slots; torn-tail (found from lengths, decoding nothing) + crash-safe-compaction recovery
  disk/record_store.clj  DiskRecordStore: per-kind log/idx pairs, records paged from disk by positional reads, behind a bounded hot-record LRU
  disk/codec.clj    what a record looks like in a frame: fields positionally (so the type tag + field names are not rewritten into all 100M of them), optionally with the body as token ids; reads every shape it has ever written
  disk/tokens.clj   the durable token dictionary those id bodies decode through: append-only, ordered ahead of the records by `fsync` rather than fsynced per token
  disk/kv.clj       DiskKvBackend: the in-RAM index map durably behind a write-ahead log; compacts on a clean close, since opening it is a replay
  disk/index_snapshot.clj  the columnar index written once and mapped back: the CSR sections raw on disk, skeleton resident and leaf/root postings mmap'd, stamped against the records and discarded to a reindex on any doubt
  disk/lock.clj     single-writer exclusive FileLock per directory
  disk/durability.clj  fsync scheduler + JVM shutdown hook
  disk/backend.clj  the durable-store selection seam: per-directory store sharing + open/close
  overlay/kv.clj    OverlayKv: a composite KvBackend — merged sets, copy-on-write counters, sticky tombstones; the one decorator that forks the whole KvIndexStore
  overlay/store.clj OverlayRecordStore: the record half — the id watermark that makes a low handle an override, tombstones, durable bookkeeping
  overlay/frozen.clj  the read-only mount: every read answered, every write refused, so base immutability is structural
  overlay/mount.clj   composing the two into a fork; which index has a KvBackend seam to fork at all, and where the bookkeeping lives
  jtms_protocol.clj    the Tms protocol alone (the representation seam both networks sit behind), in its own file so the rest of jtms.clj stays instrumentable under cloverage
  jtms.clj          the reference network (one atom, one persistent map) behind Tms: Justification (+strength/out); non-monotonic relabel; defeat; block; supersede; retract; sweep; and the public façade over the protocol
  resolution.clj    unify / type-aware match / matches-visible (belief-filtered) / prove (+ prove-from: bounded, resumable, and the *dead-end* sink abduction listens on)
  inference.clj     the second backward chainer: a frontier of whole conjunctions ordered by cost, rewritten one literal at a time into a rule's residual; every node a *canonicalized* conjunction with a namespace of its own (a rule is numbered past it, so the two are disjoint by construction and nothing needs renaming apart), `:answer-terms` pushed forward per rewrite so an answer reads out in the asker's names, the rewrite each node records in its parent's namespace so a walk up `:parent-id` replays the derivation, per-literal depth (which is also the termination condition), globally claimed keys, guards lifted into the node that asks them, the search tree left behind as a value.  `core/*query-engine*` routes to it; the default is :dfs
  tactics.clj       the node engine's search policy: one additive estimate (the plan's own per-literal cost, a size penalty, the rewriting allowance, the tree level) whose signs name a tactician; the child bias a productive node's children carry; the opt-in backchain estimate and the shape probe that picks a tactician without a caller.  Every tactician returns the same answer set — ordering is a cost decision
  abduce.clj        abduction: the scratch-context lifecycle, the gate on what may be assumed, and the mint/re-prove loop over the dead ends `prove` reports
  wff.clj           well-formedness of genl / genlCx / disjoint / arg / the equality relations (symbols only, no rewriteOf cycle, `different` not assertible); stratification (no rule-graph cycle through negation)
  provers.clj       Prover protocol (est-bindings + cost tier + completeness) + fact/transitivity/disjointness/metadata/evaluable/quantity/NAF/aggregate/arg/belief-projection + the `ask` engine; the completeness contract and what may shadow what; exceptWhen evaluation + rule guards; `candidate-rules` and `parse-rule`, which the two backward chainers read.  **No member of it expands a rule**, so `ask` never opens a proof search
  predall.clj       the predAll / predExists / predSpecified quantifier matrix's on-demand half: `specified-violations` (the *Specified* integrity audit — instances of the universal collection with no determinate filler, `indeterminate_term` members exempt) and `indeterminate-term?` (the extensible determinacy read the audit and the equality exemption share).  The *Instance* cells are CxCore rule generators and the *Exists* cells inert records — neither needs code here
  budget.clj        resource-bounded / anytime: bound a lazy answer stream (:max-ms/:max-results), the partial-result contract, the resumable tail
  plan.clj          conjunctive query planning: selectivity cost model + sideways information passing, with the cartesian factors (literals sharing no variable with the rest, and matching more than once, so they multiply it) held to the back on structure rather than on an estimate
  literal_cache.clj per-KB cache of matches-visible answers, keyed by the α-renamed (repetition-preserving) literal + context + retrieval strategy, stamped with the change clock; stores only what ran dry, so a bounded run leaves no prefix behind
  observe.clj       leaf seam (no require cycle): store add/remove hooks an incremental matcher installs into, and the coarse change clock a resident derived structure stamps itself with — plus the pin that holds one fixpoint step's reads still
  opts.clj          a third leaf with no requires but `clojure.string`: the option-map door every public entry point that takes trailing options runs through — a key outside the roster and a non-map `opts` both refused as `:unknown-option`, with the per-door sentence saying what taking the default in silence would have cost *there*.  One shape at every such door, because an option nothing reads is not a missing option but a run at a setting nobody chose
  caches.clj        the other leaf with no requires at all: the register every cache-holding namespace declares itself in at load, and the one read over it — entries, bound, unit, hit rate, and separately what the entries are about and what the counters are.  A cache in a namespace this process never loaded has no row, which is the honest answer rather than a zero
  feed.clj          the same seam one altitude up, for **belief** rather than storage: the KB's listener registry, the region a settle accumulates for them, the reentrancy claim that keeps listeners from nesting, and the two dynamics a preview and a teardown suppress it with.  `core` installs the renderer; a KB nobody watches pays one deref (docs/feed.md)
  wiring.clj        the other leaf seam, and the whole inventory of it: the two calls that run *up* the layering — the assert path (for `nat` and `skolem`) and the prover registry (for `resolution`) — plus `import-dump`, a layering inversion rather than a recursion, and the `*defer-settle?*` flag both sides read.  Each entry, and why the set is collected here instead of left at the call sites, is "The layering" at the foot of this file
  vantage.clj       CxInference: which readers can answer a goal, and the two ways of working that out — the reader fan (reference) and post-hoc placement, which must agree
  violations.clj    the dropped-conclusion ledger, below its two writers: the chainer files a conclusion it refused, the prover registry an aggregate's numeric error, and the chainer is built *on* the registry — so the ledger reads neither and both reach down to it.  A report, not a throw: it is written from inside a fixpoint that must not abort
  quality.clj       the seven readings about the **knowledge** rather than the engine — unfired rules (off the JTMS adjacency that already exists for retraction, never a scan of the justifications), extent skew, SCC-condensed chain depth over the rule graph, taxonomy coverage, the argument-constraint census, and the two rule-hygiene readings that pair the rules against each other (which rules another already covers, which pairs would contradict each other if both fired) — plus the Markdown emitter over the map it returns.  Nothing here is a gate ([quality.md](quality.md))
  profile.clj       the workload instrument: seven tallies behind one atom that is nil when off — the shape of every retrieval decision and the access path it took, every index read by family, every trie walk's node probes, the three widths of a set-algebra sift, every record fetch by kind, and what one assert wrote and one retraction unwrote per family.  Off, each seam is a deref and a `nil?` check ([profile.md](profile.md))
  skolem.clj        head existentials: the deterministic `(SkolemFn <rule-handle> <i> <frontier…>)` witness a rule head `(exists ?y C)` fires to, reified through `nat` so re-firing on one binding resolves to one constant.  Its own namespace because two layers call it — the assert path declares the reifiable function when such a rule is stored, the forward chainer mints at each firing ([skolem.md](skolem.md))
  rete.clj          opt-in TREAT alpha network: RAM alpha memories indexed by arg value; the `chain/*matcher*` swap
  levels.clj        the lookup-to-query stack: 8 levels raw-index → backchaining (`level-table`); lookup / escalate / explain, which `core/explain-levels` fronts
  qcn.clj           generic qualitative-constraint-network path consistency: the relation algebra is a parameter, the network is a value (no KB, no belief); PC-2 arc queue + the naive sweep it is proven against, the warm start that closes a narrowing off the previous answer, support-carrying derivation, bitmask relation sets over a flat long array
  qcn_kb.clj        the other half of that seam, written once for every algebra: a calculus {:name :algebra :denotation :narrowing}, the belief-filtered reader (positive AND negative facts) plus the optional second reader a narrowing is, the resident network + the two passes held in front of their content keys, the four goal shapes, entailment and refutation, the CalculusProver, and the violations report for an unsatisfiable network
  space.clj         RCC-8 over it: the 8 base + 6 derived region predicates, the composition table, and the opt-in entailment prover
  projection.clj    the algebra of nine relations that are two independent coordinates on two axes: the 1-D point tables, and the constructor that derives universe, identity, composition and converse from one projection table — refusing one that is not a bijection onto all nine pairs, since a gap composes to nil and a repeat is silently dropped by the inverse
  orientation.clj   cardinal direction over it: the 9 base + 4 derived direction predicates, composition COMPUTED by `projection` from an east-west and a north-south axis, same opt-in prover shape
  relative.clj      relative direction over it: 9 base + 4 derived, the same `projection` algebra over a left-right and a front-back axis; ternary in the literature, binary here because a CONTEXT is the frame of reference
  distance.clj      qualitative distance over it: 7 ordered classes tiling [0,∞), composition computed by the triangle inequality over the class bounds (exact, not merely sound); converse is identity, distance being symmetric
  interval.clj      Allen's interval algebra over it: the 13 base + 7 derived interval predicates, the transcribed 13×13 table (re-derived from endpoint inequalities by its test), same opt-in prover shape — and the one calculus with a NARROWING, `stp`'s metric closure read back as interval constraints, which is why this namespace requires `stp` and not the reverse
  point.clj         the point algebra over it: 3 base + 3 derived relations between instants, prefixed (`instantBefore`) because before/after are Allen's
  scenario.clj      one consistent base relation per pair, by fewest-possibilities-first backtracking — generic over every calculus, lazy (the count is exponential), deterministic (every tie breaks on content)
  duration.clj      the quantitative half: totalDuration / overlapDuration computed over stored (length I M) facts, on [lo hi] bounds, rendered as a point or an interval measure
  stp.clj           metric time, and NOT a relation algebra: bounds lo ≤ t(j)−t(i) ≤ hi closed by all-pairs shortest paths, unsatisfiable on a negative cycle; startOf/endOf bridge the numbers onto Allen's intervals — the narrowing `interval` reads, carrying the constraints behind each pair — and sharpen an overlap into a figure
  calendar.clj      the clock behind the calendar constructors: a term's half-open [start end) read off its fields, `startOf`/`endOf` answered with an `(InstantFn Y M D h m s)` moment nothing stores, and the Allen relation between two calendar terms classified straight from the bounds rather than through a network
  sign.clj          sign arithmetic over quantities with no figure attached: three values, three declared relations (sum / difference / product), the one ambiguous addition entry and the greaterInMagnitudeThan that resolves it, a derivativeOf edge making a trend the sign of a rate, and a greatest fixpoint over sets of possible signs carrying the facts behind each narrowing
  solve.clj         Solver protocol + Program + deterministic local-solver stub (ASP seam)
  asp/aspif.clj     pure ASPIF emitter (a program is a seq of plain maps) — the rule, minimize and output lines the engine's programs are built from, and no more: a statement type arrives with the caller that wants it, since an encoder nothing calls is text generation no test has ever run
  asp/atoms.clj     bidirectional atom-id table; labels are what a solver echoes back
  asp/clasp.clj     clasp subprocess backend: ASPIF on stdin, JSON out
  asp/clingo.clj    in-process libclingo through raw JNA — no JNI, no bindings
  asp/solver.clj    backend selector; lazy-resolves clingo so JNA stays optional
  asp/edge.clj      Program → ASPIF and back: the real edge solver
  asp/label.clj     brave/cautious classification (forced vs arbitrary); labeling contexts
  core_context.clj  CxCore: the vocabulary head (loads kb/CxCore.txt), documented via comment sentexes; read back with comment-of
  seed.clj          the shipped ontology's classpath side: read-sentences / load-context / layer-contexts (discovery of kb/*.txt); the format itself, reader and writer both, is io/text.clj
  starter.clj       schema-only common-sense KB: loads every kb/ context on start (Core, then upper, then middle), then the type→unary_predicate batch
  imperative.clj    the do/ imperative dispatch (do/labeling|label|classify): the one non-fact/non-rule shape `assert` takes, routed to asp.* labeling by lazy resolve
  io/generate.clj   synthesize a KB from numbers (types/individuals/rules, a fwd/backward mix, a seed): deterministic, stratified, Zipf-skewed — the shape a measurement needs
  io/frames.clj     the chunked nippy framing under both the dump and the snapshot: `[int32 length][compressed chunk]`, each chunk an independent window so the writer holds one chunk and the reader thaws one — constant memory both ways.  The one home for it, so the dump writer, the dump reader and the sink share a copy instead of three.  An independent window means an encoder per chunk, so `:xz` takes an LZMA2 dictionary sized to a chunk (`xz-dict-bytes`) rather than the preset's, for the same bytes at a quarter of the working set
  io/thaw.clj       the class-name door on every nippy thaw the engine runs over a file: nippy's record and deftype readers resolve a class name a *frame* states and build from it, and its `Serializable` reader is gated by a dynamic var a host may widen — so all three are held to one allowlist here, which is empty, because a dump frame is a field map and a log frame a positional vector.  `check-encodable` probes a leaf through the same thaw, so the front door and the readers hold one opinion ([storage.md](storage.md))
  io/text.clj       the text KB format — one Cx<Name>.txt per context, one s-expression per sentence — read and written: `write-kb!` (premises only, content-ordered, no handles), `read-forms` / `entries` / `load-entries!` (one order-insensitive pass, context topology first), and the `(set/monotonic S)` wrapper, the one thing the format spells that `assert` does not read
  io/export.clj     write a KB out as a portable dump: field-map frames (never a frozen record), chunked streams (`io/frames`), meta.edn written last as the completion marker; `:records+index` writes the index too, sourcing the `[key value]` projection from `io/snapshot` (`index-frames`) so a dump's index and a standalone image are one format
  io/import.clj     read one back — our own dialect natively and at the handles the dump gave (a foreign one is remapped, since re-canonicalizing can collapse two of its forms onto one record), a foreign one through the seam below; the dumped index is replayed only when handles are preserved and the layout+records core (`snapshot/index-mismatch`, shared with the image) checks out, else rebuilt with the reason said out loud
  io/fingerprint.clj  what makes a dumped index and its records provably the same KB: a commutative sum of per-record hashes over exactly what the index is a function of, accumulated in the storing pass rather than by a second walk
  io/snapshot.clj   a **snapshot** of derived state (the index today; the JTMS labels next) and the two-op sink it is written through: `SnapshotSink` streams a named section and commits a manifest-last, `SnapshotSource` reads them back; a `file-sink`/`file-source` over `io/frames` and a `memory-medium` that is both.  `decision` is the validate-or-discard lifted from `disk/index_snapshot.clj` — one reason per mismatch class, any doubt discards the whole image and the caller rebuilds.  Holds the `[key value]` projection and the layout+records validity core that the dump above now shares ([storage.md](storage.md))
  foreign.clj       THE SEAM for the formats we read and do not write, and the whole of them here: no reader ships in this tree, and a plugin declares `kind -> reader var` in one edn resource on the classpath, resolved by `requiring-resolve` so no compile-time reference to one exists ([foreign.md](foreign.md))
  catalog.clj       the KB catalog: sources (shipped / generated / corpus / dump / on-disk store, found on a search path), the background load with progress + cancel, and which loaded KB is active ([catalog.md](catalog.md))
  jobs.clj          the registry every long operation runs in — a load, an export, a chaining run: one status vocabulary, one progress reading, one cancel, and the claim that only one job writes at a time ([web.md](web.md))
  sandbox.clj       a scratch context per browser session, below CxWell: sees everything shipped, nothing shipped sees it; created on the first write, discarded whole
  examples.clj      the worked examples `/reasoning` renders: a table of questions, each naming the stored sentexes it reasons from and what the ontology should answer, plus the one fn that runs one
  svg.clj           the concept graph's drawing layer: a node, an edge, an arrowhead, and the arithmetic for a row / column / ring — pure, no KB, no graph library
  guard.clj         the HTTP guards both servers hold to: the Host allowlist that closes DNS rebinding (the bind interface decides; VAELII_ALLOWED_HOSTS overrides), the Origin/Referer same-origin check on writes and the EDN content-type preflight it leans on, the daemon's bearer token (VAELII_API_TOKEN) read in one place for both ends, and the request-body ceiling (VAELII_MAX_BODY_BYTES, 16 MiB) both servers share
  web.clj           reitit-ring browser: ontology / term / sentex / justification / knowledge-base pages
  serve.clj         headless EDN-over-HTTP daemon over vaelii.core: {:op :args}, allowlisted ops, single writer, sentex→map on the wire ([operations.md](operations.md))
  cli.clj           command-line driver: lein cli <cmd> … — the 25 words in `command-table` (assert / assert-rule / match / query / ask / prove / why / why-not / describe / retract / load / export / diff / repl …); --dir disk, --starter schema, --format text a text KB
  client.clj        thin java.net.http client for the daemon (zero-dep), conn threaded explicitly — the network mirror of the explicit-kb API
  subscribe.clj     the change feed with a cursor where the in-process one has a callback: the daemon's per-handler subscription registry, one bounded ring apiece, the lag count a reader that fell off it is told, and the park a long poll waits in — outside the write monitor, which is the whole constraint (docs/feed.md)
```

The **operational surface** (`serve` / `cli` / `client`, alongside the `web` browser)
drives a KB through `vaelii.core` alone — a shell CLI, a headless EDN-over-HTTP daemon
that is the single writer, and a thin client threading an explicit connection handle.
See [operations.md](operations.md).

The children's fables and the story-understanding ontology are **test-world** content
(`test/vaelii/world.clj` + `world_fables.clj` + `world_narrative.clj`), below
CxWell — contingent data, not shipped schema.

```
resources/
  kb/CxCore.txt     the vocabulary head; kb/upper/*.txt (definitional), kb/middle/*.txt (theories) — the shipped schema, term-centric text (vaelii.impl.seed)
  kb/koinii/*.txt   CxRegistry + CxSpeechActs, the app's own seed contexts — vaelii.koinii.identity loads them; the starter does not
  public/          the browser's static assets: vaelii.css (served at /vaelii.css), htmx.min.js, select.js, the favicons, logo.svg, and font/ with its two faces and their licenses
```

## Not glossed above

The map covers 113 of the 153 namespaces under `src/`. The other 40 are listed here by
name rather than left out, and the two lists together are every one of them — `lein
lint`'s **E18** fails on a file in neither and on a count that disagrees with them, so
the number above stays a measurement. Named here: the engine's write path (`integrate`,
`special`, `checks`, `chain`, `settle`), the store seam (`kb`, `access`, `reindex`), the
term layer (`nat`, `rewrite`, `inherit`, `gloss`, `spec`, plus `quasiquote`, the
metalinguistic constructor a firing builds a mentioned sentence with,
[argtypes.md](argtypes.md)), the two structural `genlCx` producers that read a context
NAT's own arguments — `context-nat` and, for the calendar dimension, `datetime`
([context-nat.md](context-nat.md)) — `modal`, which asks what an agent believes from
inside that agent's own context over the lattice already there
([belief.md](belief.md)), `roster`, the live-handle set `sentex-ids` and its two
siblings hand back at a scale where the shape of that set is itself the cost,
`belief-snapshot`, the certificate a clean close writes beside the records so the
next cold open's settle can skip its clash scan ([storage.md](storage.md)), the roster
saying which of the engine's own vocabulary anything reads (`vocabulary`), the two
process-wide dials — `config` (every environment variable and system property, read once
and refused by name at `open-kb`, [operations.md](operations.md)) and `logging` (the
level dial, which installs no backend unless asked) — the LLM stack
([llm.md](llm.md), with the reading path in [reading.md](reading.md) and the judge in
[commonsense.md](commonsense.md)):

```
impl/access.clj  impl/chain.clj  impl/checks.clj  impl/config.clj  impl/context_nat.clj
impl/datetime.clj  impl/gloss.clj  impl/inherit.clj  impl/integrate.clj  impl/kb.clj
impl/logging.clj  impl/modal.clj  impl/nat.clj  impl/quasiquote.clj  impl/reindex.clj
impl/rewrite.clj  impl/roster.clj  impl/settle.clj  impl/spec.clj  impl/special.clj
impl/vocabulary.clj
impl/asp/solve_context.clj  impl/disk/belief_snapshot.clj
impl/llm/{anthropic,correct,http,inventory,ollama,oracle,page,prompt,protocol,
          provider,score,selection,session,stub,text,tools,verdict}.clj
```

## The layering

Every edge in the engine is a static `require`, and the compiler checks all of them. They
run one way:

```
predicates <- kb <- checks <- special <- integrate <- chain <- settle <- vaelii.core
```

`predicates` is at the bottom because it requires nothing: it is what each term of the
engine's own grammar *says*, and the layers that need that answer — `taxonomy`, `wff`,
`checks`, `provers` — are all below the layer that holds the arms acting on it.
`special/entries` joins the two and refuses a disagreement at namespace load.

Exactly two calls run the other way, and a third is a layering inversion rather than a
recursion. All three live in `impl/wiring.clj` rather than at the call site that needs
them ([why they live here](defenses.md#the-layering-inversions-live-in-wiringclj-not-at-the-call-sites)).

- **`assert-sentence`** — the full assertion path, called from `impl/nat.clj` (a reified
  NAT stores its `(termOfUnit K E)` map and its materialized types) and from
  `impl/skolem.clj` (a firing mints its witness). Storing is a *whole* assert — naming,
  the definitional checks, the index, chaining, settle — so the write path runs chaining,
  and chaining calls back to mint a constant ([skolem.md](skolem.md)).
- **`solve-goal`** — the prover registry, called from `impl/resolution.clj` to discharge a
  deferred antecedent (`different` / `evaluate` / `unknown`). Backward chaining is a leaf
  the registry dispatches to, and `unknown` runs the registry back over its own argument,
  so negation-as-failure is mutually recursive with the chainer that asked for it
  ([naf.md](naf.md)).
- **`import-dump`** — `impl/io/import.clj` sits **above** `vaelii.core` and requires it,
  because reading a dump is asserting: it re-canonicalizes records, reindexes and recovers
  through the public write path. `core/import!` is `export!`'s inverse, and both run
  through that same path, so the delegation points up to reach it.

`lein lint`'s **E8** fails a literal `requiring-resolve` anywhere else under `src/`,
excepting the keyword-dispatch registries it names.

Each entry is a `delay`, so the resolve and the `require` behind it are paid once, on
first use. A delay rather than a dynamic var bound per call, because the var it caches has
to stay invokable from inside a lazy seq — `resolution/prove-seq` yields one solution per
pull, and a thread binding would be long gone by the time the seq is realized.
