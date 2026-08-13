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
([api.md](api.md)). The per-subsystem notes are indexed in [README.md](README.md); this
is the file map that sits under them.

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

src/vaelii/impl/
  protocols.clj     RecordStore, IndexStore (trie + roots + rule index + term index)
  naming.clj        naming-invariant predicates + functor/args/arity
  sentex.clj        Atomic / Rule records (connectives → truth/antecedent/consequent), split so a fact drops the rule-only slots; canonical vars + varmap, literal order, symmetric args, comparison folding/chains; canon (+ symbol interning); α-renamed path; index-terms
  rules.clj         rule-as-sentex helpers (implies form, predicates, range check, exception closure, conjunctive-consequent expand, the generator's hole split and its nesting — [generators.md](generators.md))
  taxonomy.clj      cached genl / genlCx closures; the equality partition (representative / equiv-class / deprecated?); maximal-common-descendant-contexts
  strength.clj      assumption strengths + defeat-class lattice (monotonic>default)
  kv.clj            KvBackend protocol + the one KvIndexStore over it: trie + context/functor/arg roots + rule predicate index + exception re-check index + term index; `index-layout-version`, the number that says which key shapes a build reads
  memory.clj        default backend: in-memory RecordStore + MemoryKvBackend, shared per space number
  dense_kv.clj      the :memory-dense index: IntPostings handle sets (sorted int[], promoted to RoaringBitmap past 128)
  dense_jtms.clj    the :tms :dense network: the same graph in bitmaps + primitive-keyed maps, behind jtms/Tms
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
  disk/backend.clj  the `:disk` selection seam: per-directory store sharing + open/close
  overlay/kv.clj    OverlayKv: a composite KvBackend — merged sets, copy-on-write counters, sticky tombstones; the one decorator that forks the whole KvIndexStore
  overlay/store.clj OverlayRecordStore: the record half — the id watermark that makes a low handle an override, tombstones, durable bookkeeping
  overlay/frozen.clj  the read-only mount: every read answered, every write refused, so base immutability is structural
  overlay/mount.clj   composing the two into a fork; which index has a KvBackend seam to fork at all, and where the bookkeeping lives
  jtms.clj          the Tms protocol + the reference network (one atom, one persistent map): Justification (+strength/out); non-monotonic relabel; defeat; block; supersede; retract; sweep
  resolution.clj    unify / type-aware match / matches-visible (belief-filtered) / prove (+ prove-from: bounded, resumable, and the *dead-end* sink abduction listens on)
  inference.clj     the second backward chainer: a frontier of whole conjunctions ordered by cost, rewritten one literal at a time into a rule's residual; every node a *canonicalized* conjunction with a namespace of its own (a rule is numbered past it, so the two are disjoint by construction and nothing needs renaming apart), `:answer-terms` pushed forward per rewrite so an answer reads out in the asker's names, the rewrite each node records in its parent's namespace so a walk up `:parent-id` replays the derivation, per-literal depth (which is also the termination condition), globally claimed keys, guards lifted into the node that asks them, the search tree left behind as a value.  `core/*query-engine*` routes to it; the default is :dfs
  tactics.clj       the node engine's search policy: one additive estimate (the plan's own per-literal cost, a size penalty, the rewriting allowance, the tree level) whose signs name a tactician; the child bias a productive node's children carry; the opt-in backchain estimate and the shape probe that picks a tactician without a caller.  Every tactician returns the same answer set — ordering is a cost decision
  abduce.clj        abduction: the scratch-context lifecycle, the gate on what may be assumed, and the mint/re-prove loop over the dead ends `prove` reports
  wff.clj           well-formedness of genl / genlCx / disjoint / argIsa / the equality relations (symbols only, no rewriteOf cycle, `different` not assertible); stratification (no rule-graph cycle through negation)
  provers.clj       Prover protocol (est-bindings + cost tier + completeness) + fact/transitivity/disjointness/metadata/evaluable/NAF/aggregate/argIsa + the `ask` engine; the completeness contract and what may shadow what; exceptWhen evaluation + rule guards; `candidate-rules` and `parse-rule`, which the two backward chainers read.  **No member of it expands a rule**, so `ask` never opens a proof search
  budget.clj        resource-bounded / anytime: bound a lazy answer stream (:max-ms/:max-results), the partial-result contract, the resumable tail
  plan.clj          conjunctive query planning: selectivity cost model + sideways information passing, with the cartesian factors (literals sharing no variable with the rest, and matching more than once, so they multiply it) held to the back on structure rather than on an estimate
  literal_cache.clj per-KB cache of matches-visible answers, keyed by the α-renamed (repetition-preserving) literal + context + retrieval strategy, stamped with the change clock; stores only what ran dry, so a bounded run leaves no prefix behind
  observe.clj       leaf seam (no require cycle): store add/remove hooks an incremental matcher installs into, and the coarse change clock a resident derived structure stamps itself with — plus the pin that holds one fixpoint step's reads still
  caches.clj        the other leaf with no requires at all: the register every cache-holding namespace declares itself in at load, and the one read over it — entries, bound, unit, hit rate, and separately what the entries are about and what the counters are.  A cache in a namespace this process never loaded has no row, which is the honest answer rather than a zero
  feed.clj          the same seam one altitude up, for **belief** rather than storage: the KB's listener registry, the region a settle accumulates for them, the reentrancy claim that keeps listeners from nesting, and the two dynamics a preview and a teardown suppress it with.  `core` installs the renderer; a KB nobody watches pays one deref (docs/feed.md)
  wiring.clj        the other leaf seam, and the whole inventory of it: the two calls that run *up* the layering — the assert path (for `nat` and `skolem`) and the prover registry (for `resolution`) — plus `import-dump`, a layering inversion rather than a recursion, and the `*defer-settle?*` flag both sides read.  Each entry, and why the set is collected here instead of left at the call sites, is "The layering" at the foot of this file
  violations.clj    the dropped-conclusion ledger, below its two writers: the chainer files a conclusion it refused, the prover registry an aggregate's numeric error, and the chainer is built *on* the registry — so the ledger reads neither and both reach down to it.  A report, not a throw: it is written from inside a fixpoint that must not abort
  quality.clj       the four readings about the **knowledge** rather than the engine — unfired rules (off the JTMS adjacency that already exists for retraction, never a scan of the justifications), extent skew, SCC-condensed chain depth over the rule graph, taxonomy coverage — plus the Markdown emitter over the map it returns.  Nothing here is a gate ([quality.md](quality.md))
  profile.clj       the workload instrument, and the third leaf: four tallies behind one atom that is nil when off — the shape of every retrieval decision and the access path it took, every index read by family, every trie walk's node probes, and what one assert wrote each family.  Off, each seam is a deref and a `nil?` check ([profile.md](profile.md))
  skolem.clj        head existentials: the deterministic `(SkolemFn <rule-handle> <i> <frontier…>)` witness a rule head `(exists ?y C)` fires to, reified through `nat` so re-firing on one binding resolves to one constant.  Its own namespace because two layers call it — the assert path declares the reifiable function when such a rule is stored, the forward chainer mints at each firing ([skolem.md](skolem.md))
  rete.clj          opt-in TREAT alpha network: RAM alpha memories indexed by arg value; the `chain/*matcher*` swap
  levels.clj        the lookup-to-query stack: 8 levels raw-index → backchaining; escalate/explain-levels
  qcn.clj           generic qualitative-constraint-network path consistency: the relation algebra is a parameter, the network is a value (no KB, no belief); PC-2 arc queue + the naive sweep it is proven against, the warm start that closes a narrowing off the previous answer, support-carrying derivation, bitmask relation sets over a flat long array
  qcn_kb.clj        the other half of that seam, written once for every algebra: a calculus {:name :algebra :denotation}, the belief-filtered reader (positive AND negative facts), the resident network + the two passes held in front of their content keys, the four goal shapes, entailment and refutation, the CalculusProver, and the violations report for an unsatisfiable network
  space.clj         RCC-8 over it: the 8 base + 6 derived region predicates, the composition table, and the opt-in entailment prover
  orientation.clj   cardinal direction over it: the 9 base + 4 derived direction predicates, composition COMPUTED from two independent axis projections, same opt-in prover shape
  relative.clj      relative direction over it: 9 base + 4 derived, composition computed from a left-right and a front-back axis; ternary in the literature, binary here because a CONTEXT is the frame of reference
  distance.clj      qualitative distance over it: 7 ordered classes tiling [0,∞), composition computed by the triangle inequality over the class bounds (exact, not merely sound); converse is identity, distance being symmetric
  interval.clj      Allen's interval algebra over it: the 13 base + 7 derived interval predicates, the transcribed 13×13 table (re-derived from endpoint inequalities by its test), same opt-in prover shape
  point.clj         the point algebra over it: 3 base + 3 derived relations between instants, prefixed (`instantBefore`) because before/after are Allen's
  scenario.clj      one consistent base relation per pair, by fewest-possibilities-first backtracking — generic over every calculus, lazy (the count is exponential), deterministic (every tie breaks on content)
  duration.clj      the quantitative half: totalDuration / overlapDuration computed over stored (length I M) facts, on [lo hi] bounds, rendered as a point or an interval measure
  stp.clj           metric time, and NOT a relation algebra: bounds lo ≤ t(j)−t(i) ≤ hi closed by all-pairs shortest paths, unsatisfiable on a negative cycle; startOf/endOf bridge the numbers onto Allen's intervals and sharpen an overlap into a figure
  solve.clj         Solver protocol + Program + deterministic local-solver stub (ASP seam)
  asp/aspif.clj     pure ASPIF emitter (a program is a seq of plain maps)
  asp/atoms.clj     bidirectional atom-id table; labels are what a solver echoes back
  asp/clasp.clj     clasp subprocess backend: ASPIF on stdin, JSON out
  asp/clingo.clj    in-process libclingo through raw JNA — no JNI, no bindings
  asp/solver.clj    backend selector; lazy-resolves clingo so JNA stays optional
  asp/edge.clj      Program → ASPIF and back: the real edge solver
  asp/label.clj     brave/cautious classification (forced vs arbitrary); labeling contexts
  core_context.clj  CxCore: the vocabulary head (loads kb/CxCore.txt), documented via comment sentexes; read back with comment-of
  seed.clj          text KB loader: read-sentences / load-context / layer-contexts (classpath discovery of kb/*.txt)
  starter.clj       schema-only common-sense KB: loads every kb/ context on start (Core, then upper, then middle), then the type→unaryPredicate batch
  imperative.clj    the do/ imperative dispatch (do/labeling|label|classify): the one non-fact/non-rule shape `assert` takes, routed to asp.* labeling by lazy resolve
  io/generate.clj   synthesize a KB from numbers (types/individuals/rules, a fwd/backward mix, a seed): deterministic, stratified, Zipf-skewed — the shape a measurement needs
  io/export.clj     write a KB out as a portable dump: field-map frames (never a frozen record), chunked streams, meta.edn written last as the completion marker; `:records+index` writes the index too, as the protocol's `[key value]` projection every backend shares
  io/import.clj     read one back — our own dialect natively and at the handles the dump gave (a foreign one is remapped, since re-canonicalizing can collapse two of its forms onto one record), a foreign one through the seam below; the dumped index is replayed only when layout + records fingerprint + preserved handles all check out, else rebuilt with the reason said out loud
  io/fingerprint.clj  what makes a dumped index and its records provably the same KB: a commutative sum of per-record hashes over exactly what the index is a function of, accumulated in the storing pass rather than by a second walk
  foreign.clj       THE SEAM for the formats we read and do not write, and the whole of them here: no reader ships in this tree, and a plugin declares `kind -> reader var` in one edn resource on the classpath, resolved by `requiring-resolve` so no compile-time reference to one exists ([foreign.md](foreign.md))
  catalog.clj       the KB catalog: sources (shipped / generated / corpus / dump / on-disk store, found on a search path), the background load with progress + cancel, and which loaded KB is active ([catalog.md](catalog.md))
  jobs.clj          the registry every long operation runs in — a load, an export, a chaining run: one status vocabulary, one progress reading, one cancel, and the claim that only one job writes at a time ([web.md](web.md))
  sandbox.clj       a scratch context per browser session, below CxWell: sees everything shipped, nothing shipped sees it; created on the first write, discarded whole
  examples.clj      the worked examples `/reasoning` renders: a table of questions, each naming the stored sentexes it reasons from and what the ontology should answer, plus the one fn that runs one
  svg.clj           the concept graph's drawing layer: a node, an edge, an arrowhead, and the arithmetic for a row / column / ring — pure, no KB, no graph library
  guard.clj         the HTTP guards both servers hold to: the Host allowlist that closes DNS rebinding (the bind interface decides; VAELII_ALLOWED_HOSTS overrides) and the Origin/Referer same-origin check on writes
  web.clj           reitit-ring browser: ontology / term / sentex / justification / knowledge-base pages
  serve.clj         headless EDN-over-HTTP daemon over vaelii.core: {:op :args}, allowlisted ops, single writer, sentex→map on the wire ([operations.md](operations.md))
  cli.clj           command-line driver: lein cli <cmd> … (assert/match/ask/prove/why/retract/load/repl); --dir disk, --starter schema
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
  public/vaelii.css      the browser's stylesheet, served at /vaelii.css
```

## Not glossed above

The map covers 88 of the 121 namespaces under `src/`. The rest are listed here by
name rather than left out — the engine's write path (`integrate`, `special`,
`checks`, `chain`, `settle`), the store seam (`kb`, `access`, `reindex`), the term
layer (`nat`, `rewrite`, `inherit`, `gloss`, `spec`), the roster saying which of the
engine's own vocabulary anything reads (`vocabulary`), the two process-wide dials —
`config` (every environment variable and system property, read once and refused by name
at `open-kb`, [operations.md](operations.md)) and `logging` (the level dial, which
installs no backend unless asked) — and the LLM stack
([llm.md](llm.md), with the reading path in [reading.md](reading.md) and the judge in
[commonsense.md](commonsense.md)):

```
impl/access.clj  impl/chain.clj  impl/checks.clj  impl/config.clj  impl/gloss.clj
impl/inherit.clj  impl/integrate.clj  impl/kb.clj  impl/logging.clj  impl/nat.clj
impl/reindex.clj  impl/rewrite.clj
impl/settle.clj  impl/spec.clj  impl/special.clj  impl/vocabulary.clj
impl/asp/solve_context.clj
impl/llm/{anthropic,correct,inventory,ollama,oracle,page,prompt,protocol,provider,
          score,selection,session,stub,text,tools,verdict}.clj
```

## The layering

Every edge in the engine is a static `require`, and the compiler checks all of them. They
run one way:

```
kb <- checks <- special <- integrate <- chain <- settle <- vaelii.core
```

Exactly two calls run the other way. Both live in `impl/wiring.clj` rather than at the
call site that needs them, and neither is a misplaced function that could be moved
somewhere better. A third entry sits in the same file for a related reason, below them.

- **`assert-sentence`** — the full assertion path, called from `impl/nat.clj` (a reified
  NAT stores its `(termOfUnit K E)` map and its materialized types) and from
  `impl/skolem.clj` (a firing mints its witness). Storing is a *whole* assert — naming,
  the definitional checks, the index, chaining, settle — so the write path runs chaining,
  and chaining calls back to mint a constant. The recursion is the feature
  ([skolem.md](skolem.md)): the cycle is in the **behaviour**, and no arrangement of the
  code removes it.
- **`solve-goal`** — the prover registry, called from `impl/resolution.clj` to discharge a
  deferred antecedent (`different` / `evaluate` / `unknown`). Backward chaining is a leaf
  the registry dispatches to, and `unknown` runs the registry back over its own argument,
  so negation-as-failure is mutually recursive with the chainer that asked for it
  ([naf.md](naf.md)).
- **`import-dump`** — a layering *inversion* rather than a recursion, which is why it is
  the third entry and not a third cut. `impl/io/import.clj` sits **above** `vaelii.core`
  and requires it, because reading a dump is asserting: it re-canonicalizes records,
  reindexes and recovers through the public write path. `core/import!` is `export!`'s
  inverse and `export!` is public, and a round trip whose two halves are not both public
  is not a round trip — so the delegation points up, and this is the file a call that
  points up is written down in.

They are collected because a `requiring-resolve` in whichever file happens to need it is
invisible: nothing counts them, nothing stops the next one, and the set of places the
layering is broken can only be recovered by grepping for it. Gathered, they are an
inventory — three entries, each owing the reason it cannot be an ordinary require — and
`lein lint`'s **E8** fails a literal `requiring-resolve` anywhere else under `src/`,
excepting the keyword-dispatch registries it names. A cut with a real fix is expected to
take the fix; one that lands in the inventory argues for itself in writing first.

Each entry is a `delay`, so the resolve and the `require` behind it are paid once, on
first use. A delay rather than a dynamic var bound per call, because the var it caches has
to stay invokable from inside a lazy seq — `resolution/prove-seq` yields one solution per
pull, and a thread binding would be long gone by the time the seq is realized.
