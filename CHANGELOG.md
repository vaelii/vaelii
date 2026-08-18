# Changelog

## 0.9.0 — 2026-08-17 — "the truth-maintenance network defaults to dense"

- **The dense truth-maintenance network is the default.** `open-kb`'s `:tms` now defaults
  to `:dense` (bitmaps + primitive-keyed maps) rather than `:reference` (the persistent-map
  network). `jtms_dense_oracle_test` proves the two belief-identical op by op, so no answer,
  match or ordering changes; what changes is resident RAM — measured flat per node from 20k
  to 1M, the JTMS holds in ~3.8× less memory at corpus scale (~9.1 → ~2.35 GB on an 11.5M-
  sentex corpus, a ~21% whole-KB cut), which an engine built for one large node holding 100M
  should take by default. Wall is unchanged: dense loads and recovers as fast as the
  reference, and at 10.19M both wall identically because the open-time cost is above the
  network. *Class:* **Breaking** — a documented default changes: a KB opened without `:tms`
  now runs the dense network, and `catalog/footprint`'s `:tms` estimate drops 467 → ~101
  B/sentex to match. No answer, match or ordering moves — only the representation and the
  footprint number. *Breaks:* the `:tms` default. *Migration:*
  pin `:tms :reference` to keep the persistent-map network and the old footprint figure. [docs/density.md](docs/density.md),
  [docs/nmtms.md](docs/nmtms.md)

- **The dense network gives a concurrent reader a consistent view.** A reader thread beside
  the writer — the web browser over a REPL's KB, the shape the single-writer contract calls
  supported — now sees belief either fully before or fully after a relabel, never a
  partially-applied one, matching the reference. The dense network coordinates through a
  `StampedLock`: writers take the exclusive stamp, the hot point reads (`in?`) run
  optimistically and validate, iterating reads take a shared stamp. Lock-free in the steady
  state, and the dense probe stays ~9× faster than the reference's hash-set lookup even so
  (≈19 ns against ≈180 ns per `in?`). *Class:* Additive — no answer, match or API changes;
  a race that could tear or fault a read on the new default now cannot. `jtms_concurrency_test`.
  [docs/density.md](docs/density.md), [docs/storage.md](docs/storage.md)

- **Four relation properties, enforced.** `irreflexive` refuses a self tuple `(P a a)` at
  the door (`:type` `:irreflexive`), the strict counterpart of `reflexive` and stronger
  than `asymmetric`, which admits the self tuple. `antiSymmetric` resolves by *merging*: a
  believed converse `(P b a)` beside `(P a b)` derives `(equals a b)` and unifies the two
  arguments, the antisymmetric twin of what `functional` does with two symbol values, over
  the same three arrival directions; a converse no equality could reconcile (two numbers)
  refuses instead (`:type` `:anti-symmetric`). `equivalenceRelation` needs no engine code —
  three shipped forward rules derive `symmetric`, `transitive` and `reflexive`, each
  enforced in turn (a subsumption `genl` edge would classify but not set the property the
  enforcement reads, so the rules are the minimal correct expression). `antiTransitive` is
  **declared and its chain conviction deferred**: `(P a b) ∧ (P b c) ⇒ ¬(P a c)` is a
  three-party nogood the settle machinery forms only pairwise, so what is enforced is its
  classification and `(disjoint transitive antiTransitive)` — no predicate is both. Each new
  property is one predicate on the collapsed model — `(genl X binaryPredicate)`, no derived
  twin — and the lattice sits on the bare marks: `(genl asymmetric irreflexive)`, `(genl
  asymmetric antiSymmetric)`, `(disjoint symmetric asymmetric)`, `(disjoint reflexive
  irreflexive)`, `(disjoint transitive antiTransitive)`. `(disjoint symmetric antiSymmetric)`
  is skipped — `equals` is both. *Class:* **Additive** — two new refusal `:type` keywords a
  caller may now meet, and vocabulary that was inert before is now read; no existing
  declaration changes behaviour. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/nmtms.md](docs/nmtms.md)

- **A subsumption rests on its strongest route, not its shortest.** When a fact reaches a
  rule antecedent of a different functor across the `genl` closure, the conclusion is
  capped at the defeat class of the path the match climbed. That path was chosen breadth-
  first — the *fewest* edges — so a conclusion read `:default` whenever the shortest route
  ran through a defeasible edge, even when a longer all-`:monotonic` route existed. The walk
  now takes the **widest bottleneck**: the route whose floor (the `min` defeat class along
  it) is highest, tie-broken by depth then content. So a conclusion over a `:monotonic`
  route holds `:monotonic`, and `kb/reach-strength` reads that floor directly. *Class:*
  **Breaking** — `defeat-class` of a conclusion reached across a taxonomy that offers two
  routes at different strengths can rise from `:default` to `:monotonic`; a caller that
  keyed on the old class must re-read it. No answer *set* changes — only the strength a
  conclusion is reported at. *Breaks:* `defeat-class`. *Migration:* re-read `defeat-class`
  on conclusions reached across such a taxonomy; if you want the old shortest-path witness
  for placement, it is unchanged — only the `genl` subsumption path a firing rests on moved.
  [docs/taxonomy.md](docs/taxonomy.md)

- **An algebraic property is one predicate, not a mark and a twin.** The derived predicate
  types `symmetricPredicate` / `asymmetricPredicate` / `transitivePredicate` /
  `reflexivePredicate` / `functionalPredicate` are removed, along with the `PredicateTypeProver`
  and the CxCore rules that materialized them. Each **mark** — `symmetric`, `asymmetric`,
  `transitive`, `reflexive`, `functional` — now carries the classification itself: through
  `(genl symmetric binaryPredicate)` in CxCore it *is* a `binaryPredicate` subtype, so
  `(symmetric siblingOf)` makes `isa? siblingOf symmetric` and `isa? siblingOf binaryPredicate`
  hold and `ask (symmetric ?p)` enumerates by ordinary retrieval. `genl` / `genlCx` are the
  taxonomy's `closure-relations`: `(transitive genl)` is stored and queryable but held out of
  the `:transitive` property machinery, so it never routes them to the generic prover. *Class:*
  **Breaking** — a query, rule or `isa?` naming a `…Predicate` type now answers nothing; and
  because the surviving mark is a `decontextualizedPredicate`, its membership is read KB-wide
  rather than only in the context that once derived the twin. *Breaks:* `symmetricPredicate`,
  `asymmetricPredicate`, `transitivePredicate`, `reflexivePredicate`, `functionalPredicate`.
  *Migration:* replace `(…Predicate P)` with the bare mark `(… P)`; the mark answers the same
  membership and now classifies `P` as a `binaryPredicate` directly.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A rule may conclude a variable predicate.** `(implies (holds ?p ?x ?y) (?p ?x ?y))`
  now asserts, fires, and answers backward, where it was refused `:not-indexable`. The
  split is by position: a variable functor in the **consequent** is bound by a concrete
  antecedent (range restriction guarantees it), so the rule fires forward with the
  predicate ground and its consequent is filed under one catch-all bucket that "what could
  conclude P?" unions in; a variable functor in an **antecedent** stays refused, because it
  names no predicate for an arriving fact to trigger and would join over whatever is stored
  when a concrete antecedent beside it arrives. The refusal message now says which side it
  is, and a var-consequent rule carrying an `unknown` / `exceptWhen` / aggregate antecedent
  is refused `:not-stratified` — it could conclude the very predicate whose absence it rests
  on. *Class:* **Additive**; no rule that asserted before is refused, and one class of rule
  refused before now runs. [docs/indexing.md](docs/indexing.md)

- **The search a query would run, as data — and a debugger over it.** Two new public
  reads open the node engine's search. `search-tree` returns the tree a bounded backward
  search actually builds for a goal — every node the frontier reached, not only the path
  that answered, each with the itemized estimate that ordered it, the rewrite that
  produced it, and the answers off it. `compare-tacticians` runs the same goal under each
  tactician and returns their work and answer *sets*, so a caller can verify that every
  complete ordering finds the same answers rather than trust it. Both bound their own work
  (a node budget and a wall-clock) and return serializable data, so the browser's new
  `/inference` page — the run beside `/levels`' plan — holds no session and works under
  `--attach`. *Class:* **Additive** — two public reads and one route; nothing existing
  changes. [docs/web.md](docs/web.md), [docs/inference.md](docs/inference.md)

- **Which of my rules actually do anything — the chaining funnel.** A new public read
  `chain-report` gives the per-rule breakdown behind `chain-stats`: for every forward rule,
  how many firings it **placed**, how many it **refused** and why (`exception` / `naf` /
  `post-join` / `hidden`), or whether it stayed **silent** because no antecedent set ever
  completed. It reads `O(rules)` off the standing refusal ledger (re-decided against current
  belief) and the justification graph, so it reflects the KB as it is now and needs no
  per-run instrumentation — the counters a live funnel might have kept would only restate
  what the ledger already holds. The browser's new `/funnel` page ranks the rules by what
  is wrong (no-placement first, refusals descending), folds in the `violations` each filed,
  and runs forward chaining as a job that lands back on itself. *Class:* **Additive** — one
  public read and one route; nothing existing changes.
  [docs/web.md](docs/web.md), [docs/exceptions.md](docs/exceptions.md)

- **A rule is asked before it fires, and a definitional read is taken from where it is
  asked.** One blind spot ran through several paths: a stored-but-OUT rule still fired, or
  a read answered from a vantage that could not see the declaration it rested on. The two
  re-join paths (`rejoin-qualitative`, `rejoin-preserving`) now ask `rule-believed?` as the
  trigger path always did, so a defeated rule reached off the storage-posted antecedent
  index no longer fires — and no longer files a `violations` entry against a rule the KB
  does not hold. A `watch` subsumes through the `genl`
  edges its own context sees rather than every edge; a functional-merge clash and ASP's
  auto-clash detectors read functionality, disjointness and same-class from the solving
  vantage; and `why-not` names the supersession the fact's own context elected rather than
  one a global rewrite returned. A refusal also keeps the depth bound its run set, so a
  release honours that bound over the default — live-session only, since a recovered KB
  rebuilds refusals at the default exactly as it resets derivation depths. No working caller
  relied on a rule firing unasked, or on a read that disagreed with itself across a context
  it could not see. [docs/inference.md](docs/inference.md),
  [docs/contexts.md](docs/contexts.md), [docs/exceptions.md](docs/exceptions.md)

- **A dotted-rest pattern retrieves the facts it matches.** A query or match whose
  sentence ends in a rest-splice — `(parentOf . ?args)`, `(?pred . ?args)` — returned
  `#{}`: its canonical trie path carries the `.` marker as a token no stored fact has, and
  no candidate branch diverted it. `res/candidate-handles` now routes a dotted pattern to
  the arity-spanning roots — a concrete functor (with any leading ground argument) reads
  its functor-scoped roots, an open functor with a leading argument the predicate-agnostic
  slot roster, and a fully-open `(?pred . ?args)` the whole fact extent — each a superset
  the existing `unify` filters to the exact set. *Class:* **Additive** — a pattern shape
  that silently matched nothing now matches; no other shape changes.
  [docs/indexing.md](docs/indexing.md)

- **A clean cold open can skip the contradiction scan.** With `vaelii.belief.snapshot` set
  (a system property, off by default), a full `recover` of a writable `:disk` KB leaves a small
  belief certificate beside the records (`<dir>/belief/`) recording whether the close found the
  store clean, and the next cold open reads it, checks that the record store's slot fingerprint
  still matches, and — if the certificate says the store closed clean — skips the closing
  settle's definitional-clash scan, whose cost is the count of standing clashes and runs to
  minutes at corpus scale, rederiving byte-identical belief. The certificate never *supplies*
  belief: it records only whether a clean close found no clash, so a moved record, a torn stamp
  or an unclean close makes the open ignore it and run the full scan it always did. With the
  property unset, `recover` computes nothing extra and is the recover it always was. *Class:* **Additive** — one opt-in switch; nothing existing changes.
  [docs/storage.md](docs/storage.md), [docs/operations.md](docs/operations.md)

- **A third durable records backend, `:sqlite`.** `open-kb` accepts `{:records :sqlite}` (the
  sugar `:sqlite`), a single-file `<dir>/records.sqlite` store the Apache-2.0
  `com.vaelii/sqlite` adapter provides — resolved lazily, so the engine carries no JDBC
  dependency and a KB that never asks for it loads none. Off the classpath, the backend
  refuses by name with the coordinate to add — the adapter is released separately, after
  this core version. `:memory` and `:disk` are unchanged, and a
  durable `:disk` index over `:sqlite` records is refused exactly as it is over `:memory`.
  *Class:* **Additive** — a new backend keyword; no existing pairing changes.
  [docs/storage.md](docs/storage.md)

- **`person` is a social agent, and `human` is the biological type.** The shipped ontology
  splits the two: `human` is `(genl human mammal)` and `(genl human person)`, while `person`
  is `(genl person physical_object)` — an entity with social agency that need not be alive. So
  `(isa X person)` no longer entails `mammal` or `animal`: a non-biological agent can be a
  `person`, which is what lets the social predicates (`friendOf`, `knows`, `marriedTo`)
  constrain their arguments to `person` and still admit it, while the biological predicates
  (`parentOf`, `birthYearOf`, `fatherOf`, `motherOf`) constrain to `animal` and refuse a
  `person` who is not one. *Class:* **Breaking** — a shipped taxonomy edge changed: `(genl
  person mammal)` and `(genl person animal)` no longer hold, so a query, rule or `isa?` that
  read a `person` as a `mammal`/`animal` answers differently. *Breaks:* the `person`
  membership entailment; the biological predicates now refuse a non-`animal` `person`.
  *Migration:* type biological individuals `(isa X human)` where you relied on `(isa X person)`
  implying `mammal` or `animal`; leave non-biological agents as `person`.
  [docs/commonsense.md](docs/commonsense.md)

- **`argPreserving` is renamed `transitiveInArg`.** The meta-predicate that declares an
  argument position preserved down a `genl` edge, and its inverse, are renamed across the
  shipped ontology, engine and docs: `argPreserving → transitiveInArg`, `argPreservingInverse
  → transitiveInArgInverse`. The semantics are identical; the spelling names what the property
  is — a predicate transitive in one argument — rather than a side effect of it. *Class:*
  **Breaking** — a shipped KB predicate name changed. *Breaks:* `argPreserving`,
  `argPreservingInverse`. *Migration:* rename both in your KB text; nothing else changes.
  [docs/inherit.md](docs/inherit.md)

- **`argIsa` / `argGenl` / `interArgIsa` answer up the `genl` cone.** `(ask (argIsa petMammal 1
  animal))` now answers when `(argIsa petMammal 1 mammal)` is stored and `(genl mammal animal)`
  holds: the predicate position descends and each type position ascends — a stored declaration
  on a super-predicate answers a sub-predicate query, and one on a sub-type a super-type query,
  matching what `check` already enforces. A bounded prover walks it on demand and materializes nothing, so
  `sentexes-matching` still shows only the stored declarations. `arity` is deliberately
  excluded — a sub-predicate may carry its own signature. Closes #20. *Class:* **Additive** —
  a query that answered nothing now answers; nothing stored or existing changes.
  [docs/argtypes.md](docs/argtypes.md), [docs/inherit.md](docs/inherit.md)

## 0.8.0 — 2026-08-14 — "predicates inherit down the hierarchy"

`arity`, `functional`, `asymmetric` and the three argument
constraints descend the predicate hierarchy now — at the door and on every retroactive
pass — so a claim spelled with a sub-predicate is held to what its supers declare, and
the six arrival orders of {declaration, fact, edge} reach one set of beliefs. Beside it
two structural gaps close: a KB whose derived state was never built refuses writes rather
than accepting them unchecked, and a firing rests on the `genlCx` edges its placement was
read over, so retracting one takes the conclusion back.

**Twenty entries are Breaking**, which is what makes this a minor rather than a point
release. Eight Refusal entries batch here rather than each forcing its own, which is what
§3.8 of `CONTRIBUTING.md` designates a minor for. Every Breaking and every Refusal entry
carries its *Migration* line, and every entry links the page that carries the mechanism —
an entry here says what moved and what to write instead, and the doc says how it works.

**Triage, for a 0.7.0 caller.** This is the index to what touches something you have
written.

| If your code… | Then |
|---|---|
| asserts a sub-predicate fact under a super's `argIsa` / `argGenl` / `interArgIsa` | refused `:arg-type`; widen the declaration, move it down, or drop the `genl` edge |
| declares an `arity` that disagrees with its super's | refused whichever sentence arrives second; give the two one arity, mark either end `variableArity`, or drop the edge |
| relies on `(functional P)` or `(asymmetric P)` binding P's exact functor alone | both convict a sub-predicate's tuples now, in either arrival order |
| reads an empty `violations` as a clean bill | `:arity` and `:constraint-exposure` entries appear in arrival orders that filed none, and a retraction no longer files `:no-placement` |
| branches on `violations`' `:violation` with a defaultless `case` | `:arity-truncated` and `:arity-report-truncated` are new kinds |
| counts `:arity` entries to size a problem | both retroactive passes file at most 8 and carry the totals on a truncation notice |
| writes to a KB opened `{:recover? false}`, or loaded `:belief? false` / `:belief? :stored` | refused `:unrecovered-kb`; call `recover` (or `reindex`) first, or bind `*write-unrecovered?*` |
| retracts against such a KB | refused, where it deleted the record and left its justifications dangling |
| spells one sentence as a top-level vector — `(assert kb '[likes Tom Ann])` | refused `:shape`; write the list, and ask a conjunction with `query` or `prove` |
| passes a non-map where an option map goes, `(open-kb :nope)` among them | `:unknown-option` by name, where it threw an unnamed error |
| reads `why`'s `:because`, `why-not`'s `:missing` or `preview`'s `:antecedents` | a cross-context firing lists the `genlCx` edges it was placed over, and a descended merge names each `genl` edge once rather than once per side |
| reads `defeat-class` on a cross-context conclusion | it caps on those edges, so a known-true fact read across a `:default` context edge answers `:default` |
| re-asserts known-true content over a `:monotonic` premise | the stronger class survives the re-assert; narrowing one is `retract!` and re-assert |
| asserts a rule concluding `(rewriteOf …)`, `(sameAs …)`, `(equals …)` or `(disjointMetatype …)` | it merges or separates while the KB runs, where only a restart saw it |
| lists a store directory through `catalog/classify` | classification reads `records/format.edn`; three disk backends classify as `:store` that did not, and a `records/`+`index/` pair alone no longer does |
| catches around `unload!` | a store that did not close reports `:unreleased`, where it reported silent success |
| runs `kb-quality` | a fifth reading, `:declarations`, names argument constraints that constrain nothing, and `:stranded-count` drops |
| matches an arity refusal on its `:message` | an inherited length reads "takes N arguments through P", not "is declared with N" |

### Writes over a KB whose derived state was never built

- **Breaking: such a KB refuses writes rather than accepting them unchecked.** Every
  definitional check bottoms out in `jtms/in?`, so over an empty network all ten match
  nothing and the assert lands — and nothing later catches it. `assert`, `assert-inert`,
  `retract!`, `edit!` and `preview` refuse by name (`:unrecovered-kb`), reporting
  `:hazards` and naming the call that clears them.
  *Class:* Breaking; writes that landed silently now throw.
  *Migration:* call `recover` (or `reindex`) before writing, which is what the content
  needed anyway; or bind `vaelii.core/*write-unrecovered?*` around the write, which now
  logs once per KB naming what is unchecked.
  *Breaks:* `:unrecovered-kb`, `:unrecovered-premise`, `*write-unrecovered?*`, `:recover?`
  [docs/storage.md](docs/storage.md), [docs/web.md](docs/web.md)

- **Breaking: a derived record's teardown is refused where belief was never built.**
  `retract-storage!` read "no TMS node" as "inert" and deleted a forward-chained record,
  leaving dangling the justifications that concluded it. Nothing per-handle separates the
  two cases, so the question is asked of the KB instead.
  *Class:* Breaking; a retraction that deleted a record now throws.
  *Migration:* call `recover` (or `reindex`) before retracting, which is what the sweep
  needed anyway.
  *Breaks:* `:unrecovered-kb`
  [docs/storage.md](docs/storage.md)

- **`check` and `check-edit` answer for the door they mirror.** `check-writable!` runs
  first at `assert` and was not in the stage list, so a batch validated against an
  unrecovered KB came back admissible and then refused on its first line. Both report
  `:unrecovered-kb` alone and first, and both go quiet under `*write-unrecovered?*`.
  *Class:* Additive; a new problem `:type` on two readers that report problems.
  *Migration:* none. A caller matching on the message rather than the `:type` sees
  "index was" where the index hazard stands alone.
  *Breaks:* `:unrecovered-kb`, `check`, `check-edit`
  [docs/storage.md](docs/storage.md)

- **Refusal: a declared hazard survives being read while the store is still empty.**
  `write-hazards` retired `import-dump`'s `{:no-belief true}` on any read taken before the
  records landed, handing the finished load a KB whose records are unbuilt and whose
  hazard is gone.
  *Class:* Refusal; writes a prematurely-released hazard let through are now refused by
  name.
  *Migration:* code clearing a store through `p/clear-records!` rather than `clear!`
  should call `kb/note-hazards!` with both keys false, as the suite's fixtures now do.
  *Breaks:* `write-hazards`, `note-hazards!`
  [docs/storage.md](docs/storage.md)

- **Refusal: `recover` stops believing a record the store does not hold.** A stored
  justification concluding a handle with no record minted a phantom and made it IN, so the
  KB came back believing a handle no query could return, and everything drawn from it.
  Such a justification is left out of the network and counted, logged once at `:warn`
  under `::justifications-unrooted`.
  *Class:* Refusal; the handle read absent and its belief read true, so the state it
  produced was not one anybody asked for.
  *Migration:* nothing to change; a store carrying such a justification now says so.
  *Breaks:* `recover`, `justifications-unrooted`
  [docs/storage.md](docs/storage.md)

### Loading a dump

- **`:belief? :stored` — store what rests on what, and settle it later.** Everything
  `true` does **except the `recover`**, for a corpus that cannot afford one; for a foreign
  dialect it is the only mode that keeps the justifications at all. The catalog carries the
  choice (`:rebuild` / `:stored` / `:skip`) rather than a checkbox, and `active-caveat`
  gained `:recoverable?` so the browser's banner names which repair applies.
  *Class:* Refusal for the `:belief?` **value** check; Additive for the mode itself.
  *Migration:* none — `true` is still the default. An unrecognised `:belief?` value is now
  refused by name (`:unknown-option`), since anything truthy would otherwise mean `true`
  and run the recover the caller asked to defer.
  *Breaks:* `:belief?`, `:unknown-option`
  [docs/catalog.md](docs/catalog.md), [docs/web.md](docs/web.md)

- **One frame a dump holds and this build will not construct stops taking the load with
  it.** A frame the structural checks refuse yields no record, and both import paths threw
  on it — while a dump is not a program being written, and the reading side cannot fix the
  writing side. It is counted in the summary's **`:refused`**, skipped, and logged, which
  is the policy the naming door has had all along.
  *Class:* Additive for `:refused` and `:frames`.
  *Migration:* a load that threw `:naf-not-closed` — or any other construction refusal —
  now finishes; assert `(zero? (:skipped (:refused summary)))` to keep the old strictness.
  [docs/naming.md](docs/naming.md)

- **A justification the import writes no longer rests on a record the import deleted.** A
  remapped load drops the meta-sentexes whose `(sentexHandle H)` will not resolve, but the
  dump-id map went on resolving their ids, so both deduction readers stored justifications,
  premise marks and provenance pointing at records that were no longer there.
  `forget-deleted` closes it, reporting **`:orphaned-ids`** and
  **`:dropped-justifications-orphaned`**.
  *Class:* Additive for both keys; a load that wrote a dangling justification now drops it
  and says so.
  *Migration:* none. A store already carrying them is repairable in place — delete every
  justification naming a handle `sentex-ids` does not yield.
  [docs/catalog.md](docs/catalog.md)

- **Refusal: an import frame that fills a justification's `:out` slot**
  (`:naf-justification`, a new `:type`). The slot is the NAF antecedent set — reserved,
  and empty in every KB the engine builds — but a justification frame in a dump is the
  record's own field map, which made that door the one way a filled one could reach a
  store. Three relabel invariants read the slot as empty rather than reading it.
  *Migration:* nothing — no dump the engine produced carries one.
  *Breaks:* `:naf-justification`, `import!`, `import-dump`
  [docs/naf.md](docs/naf.md)

- **A dump that fills that slot is refused before the import writes anything.** The check
  ran after the whole sentex phase had landed, and an import is not a transaction, so the
  refusal left a half-written store that `assert-empty-destination!` then refused to retry
  into. It streams the file in a pre-pass now; same `:type`, same message, same ex-data.
  *Class:* neither label; the refusal is the same refusal, and what changed is what the KB
  holds afterwards. [docs/catalog.md](docs/catalog.md), [docs/naf.md](docs/naf.md)

- **A restart stops answering through an edge nothing supports.** `rebuild-taxonomy`
  replays **stored** declarations, so a `genl` edge that is OUT from the moment its node is
  made still answered `isa?` — a restart believing a type the running KB did not. `recover`
  runs `refresh-beliefs` over the replay, before the settle.
  *Class:* neither label; a restart's answers move onto the running KB's.
  [docs/storage.md](docs/storage.md), [docs/taxonomy.md](docs/taxonomy.md)

### The predicate hierarchy descends

- **Breaking: `arity`, `asymmetric` and `functional` descend it.** Each read its mark off
  the exact functor while the machinery it convicts *with* already fanned down the
  hierarchy, so each was bypassable through a sub-predicate door. A predicate declaring no
  arity of its own takes the one its supers agree on; `(asymmetric parentOf)` convicts
  `(fatherOf a b)` beside `(parentOf b a)` in either order; `(functional parentOf)`
  reconciles two `fatherOf` fillers. **`arity` is the strict one:** two declared arities
  across one edge is refused. Supers that disagree bind nothing, a `variableArity` super
  releases the inheritance, and the generative marks descend nowhere.
  *Migration:* a specialization that genuinely reads a different number of arguments is
  `variableArity` on either end of the edge; a sub-predicate declaring a conflicting arity
  is refused, so give the two one arity or drop the `genl` edge.
  *Breaks:* `variableArity`, `asymmetric`, `functional`, `:arity`,
  *Breaks:* `binaryPredicate`, `functional-clashes`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/inherit.md](docs/inherit.md),
  [docs/equality.md](docs/equality.md)

- **Breaking: an argument constraint on a predicate binds its sub-predicates' tuples.**
  `(genl fatherOf parentOf)` says every `fatherOf` tuple *is* a `parentOf` tuple, so
  `(argIsa parentOf 1 person)` refuses `(fatherOf TheRock1 Mary)` exactly as it refuses the
  claim spelled `parentOf`; `argGenl` and `interArgIsa` descend by the same argument. The
  refusal was door-dependent and failed at the one job it exists for, the matcher fanning a
  goal's functor over its subtypes. Held to the writer's vantage: an edge a context cannot
  see imports no constraint.
  *Migration:* a KB using predicate-level `genl` for retrieval fan-out alone, relying on
  the specialized predicate being unconstrained, is refused where 0.7.0 accepted it; widen
  the declaration, move it down, or drop the edge.
  *Breaks:* `argIsa`, `argGenl`, `interArgIsa`, `:arg-type`
  [docs/taxonomy.md](docs/taxonomy.md)

- **`argIsa` read as an *inference* descends with it, and so does the entailment.** `ask`
  types an argument through a super-predicate's declaration, because a claim `assert`
  refuses for being ill-typed must not be one `ask` cannot type at all. Under
  `*assertive-arg-types?*` the minted type names the `genl` edges it descended, so
  retracting one takes the type back, and the entailment is drawn when the **edge** arrives
  last.
  *Class:* Additive; the entailment is opt-in and off by default.
  [docs/argtypes.md](docs/argtypes.md)

- **Three predicate-metadata kinds join `has-prop?` / `props`:** `:declares-arg-isa`,
  `:declares-arg-genl`, `:declares-inter-arg-isa`, marking a predicate that is the
  *subject* of an argument constraint. The descension asks per super whether it declares
  anything at all — off the index an argument-root probe per super on every assert, and a
  set membership once it is marked. *Class:* Additive.
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a `functional` or `asymmetric` mark reaches back down a `genl` edge, on both
  retroactive paths.** Under `:arbitrate` a mark or edge arriving *after* the facts left
  the clashing pair believed — permanently, the pair never entering `:clashes` for a later
  settle to re-derive. Both paths take their extent through the marked predicate's spec
  subtree now.
  *Class:* Breaking; a clashing pair that stood believed is now arbitrated.
  *Migration:* a caller reading `contradictions` or `violations` sees pairs the door has
  always refused when the mark arrived first — the two arrival orders agree now.
  *Breaks:* `contradictions`, `violations`, `:constraint-exposure`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: the cross-context exposure pass reads its marks down the hierarchy, as every
  check it gates already did.** It read the mark off the **exact functor** per sentex, so a
  pair whose only mark sits on a super-predicate was dropped before any check saw it.
  *Class:* Breaking; a KB holding such a pair files a `:constraint-exposure` entry where it
  filed nothing.
  *Migration:* nothing to write — the entry names both handles, so the pair is what to look
  at.
  *Breaks:* `violations`, `:constraint-exposure`
  [docs/contexts.md](docs/contexts.md), [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: the retroactive arity report descends the hierarchy, as the door it mirrors
  already does.** Fact, declaration and `genl` edge are three ingredients and any can
  arrive last; the report read only the predicate its trigger named, so a ternary
  `fatherOf` fact under a binary `parentOf` stood believed and unmentioned. It sweeps the
  **spec subtree** now, and entries carry `:via`.
  *Class:* Breaking; nothing new is refused, and a caller reading `violations` sees a
  finding it did not.
  *Migration:* nothing to write — read `:via` to tell an inherited length from a declared
  one.
  *Breaks:* `violations`, `:arity`, `:via`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: that report answers a `genlCx` edge, its fourth ingredient.** A visibility
  edge rebinds a predicate's length as a `genl` edge does, and `settle/arity-bound-by` knew
  three spellings and not that one. The pass triggers on the edge and sweeps whichever end
  `p/count-in-context` sizes smaller.
  *Class:* Breaking; `:arity` entries appear in two arrival orders that filed none.
  *Migration:* none for a KB whose contexts declare their own arities; one declaring in a
  super-context learns about facts that were already wrong.
  *Breaks:* `violations`, `:arity`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/contexts.md](docs/contexts.md)

- **Breaking: the arity door words an inherited length as inherited, as its retroactive
  half already did.** `fatherOf is declared with 2 arguments, declared of parentOf but has
  3` credited `fatherOf` with a declaration it never carried; it reads `fatherOf takes 2
  arguments through parentOf but has 3` now, with a self-declared length unchanged.
  *Class:* **Breaking** on §3.8's counterweight: only the `:message` string moves, which is
  the class-1 test.
  *Migration:* read `:expected`, `:actual` and `:via` off the ex-data rather than matching
  the message.
  *Breaks:* `is declared with`, `:opposing-handle`, `:arity`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a `variableArity` predicate may be given argument types past its declared
  length.** `arg-position-problem` was the one arm of the arity family that did not read
  `checks/variable-arity?`, so `(argIsa qRel 3 person)` was refused on a predicate whose
  3-argument facts the same KB admitted.
  *Class:* Breaking; input that was refused is now admitted, and `kb-quality`'s
  `:stranded-count` drops.
  *Migration:* nothing in the shipped ontology moves — none of its three `variableArity`
  predicates declares past its length.
  *Breaks:* `variableArity`, `argIsa`, `:stranded-count`, `kb-quality`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/quality.md](docs/quality.md)

- **`kb-quality` gains a fifth reading: argument constraints that constrain nothing.**
  `(argIsa parentOf 3 person)` is admitted while `parentOf` has no declared length; when
  one arrives, declared or inherited, the declaration is left naming a position the
  predicate provably does not have. `:declarations` names them and `quality-report` writes
  the section. **Deliberately not `violations`:** a stranded declaration is inert and reads
  the same an hour later.
  *Class:* Breaking for the `:arg-position` refusal message, which now splits on `:via` as
  the door and the report do; Additive for the reading itself.
  *Migration:* read `:via` and `:arity` off the ex-data rather than parsing `:message`.
  *Breaks:* `kb-quality`, `quality-report`, `:arg-position`, `is declared with`
  [docs/quality.md](docs/quality.md), [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: neither retroactive pass can file its way through the ledger, and
  `:arity-report-truncated` says when a cap stopped one.** The ledger keeps the newest
  1,000 entries and the arity report filed one per convicted predicate against a budget of
  4,096, so one binding over a wide subtree could evict every other violation in the KB.
  Both passes file at most the content-first **8** and say what the cap left out. Read the
  new kinds as *found, examined, and not named*.
  *Class:* Breaking for the cap, Additive for the kind and the keys.
  *Migration:* size a problem from `:predicates` and `:facts` on the notice rather than by
  counting `:arity` entries; past 8 the count is now visibly not the total.
  *Breaks:* `violations`, `:arity-report-truncated`, `:arity-truncated`,
  *Breaks:* `:constraint-exposure-truncated`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/nmtms.md](docs/nmtms.md)

- **The retroactive arity sweep says when its budget stopped it, including in the case that
  carries no finding.** The `:truncated` flag rode on a finding, so a predicate that spent
  the budget convicting nothing left every predicate after it examined zero facts deep in
  silence. One **`:arity-truncated`** entry is filed either way.
  *Class:* Additive; a new `:violation` kind, so a defaultless `case` over them has one
  more to admit. [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a descended merge names each `genl` edge once, not once per side.** Both
  sides of a functional clash reach their mark by their own path, and those paths are a
  **set**: two `fatherOf` fillers under `(functional parentOf)` descend one edge, which
  landed twice in the stored record and two or three times in the reports that read it.
  Belief never moved, but an antecedent list is the explanation a caller is handed.
  *Class:* **Breaking** on §3.8's counterweight: the list is shorter, deterministically so.
  *Migration:* nothing, unless you counted.
  *Breaks:* `why-not`, `preview`, `:because`, `:antecedents`
  [docs/nmtms.md](docs/nmtms.md)

### Contexts and placement

- **Breaking: a firing rests on the `genlCx` edges its placement was read over, and now
  names them.** A conclusion is placed in the maximal contexts that see the rule, the facts
  and the `genl` edges the match subsumed through, and each sighting is a reachability some
  ordinary sentex supports and somebody can take back. The justification named the
  ingredients and not the edges, so retracting one left the conclusion believed in a context
  that could no longer see any of its reasons — belief as a function of arrival order. The
  edges join the antecedent list, one shortest path per ingredient context.
  *Migration:* assert the `genlCx` wiring `{:strength :monotonic}` wherever a cross-context
  conclusion must stay indefeasible, and expect context edges among a justification's
  antecedents. Two things move for a caller who retracts nothing: antecedent lists are
  longer, and `defeat-class` caps on the edges like any other ground.
  *Breaks:* `genlCx`, `supporting-justifications`, `defeat-class`, `:monotonic`
  [docs/contexts.md](docs/contexts.md), [docs/nmtms.md](docs/nmtms.md)

- **Breaking: a retraction stops filing `:no-placement` entries about the rules it just
  took apart.** A conclusion that now has nowhere to be placed *is* the retraction the
  caller asked for, not a diagnosis of anything, and one per affected rule crowded the
  ledger a caller reads for what it did *not* mean to do. An ordinary firing that cannot
  place its conclusion still says so.
  *Class:* Breaking; a public reader returns fewer entries.
  *Migration:* none for a caller reading `violations` for problems. A caller counting
  entries across a retraction sees the count it would have had if the rules had never been
  asserted.
  *Breaks:* `violations`, `:no-placement`
  [docs/contexts.md](docs/contexts.md)

### Rules that conclude structure

- **A rule generator may stamp a generator, at any depth, and a variable an enclosing level
  fills may head a literal.** `(implies (typeVersion ?ipred ?tpred) (implies (?tpred ?type
  ?cap) …))` states a type-level/instance-level bridge once instead of once per predicate
  pair, and what reaches the index is still an ordinary rule over concrete functors. The
  scoping rule needed nothing added, and **a top-level rule antecedent is untouched**.
  *Class:* **Additive** — a shape that was refused is now accepted.
  [docs/generators.md](docs/generators.md)

- **Breaking: a rule concluding `(rewriteOf A B)` / `(sameAs A B)` / `(equals A B)`
  merges.** The conclusion reaches the arm an asserted equality reaches, so the closure
  learns the edge and every sentex naming the retired spelling gains a justified twin.
  Before, a running KB and its own restart disagreed about whether two terms were one thing.
  *Migration:* a KB with such a rule now merges where it did not, which moves matches,
  `different` answers and belief; if the rule meant something weaker than identity, restate
  it under a predicate of your own.
  *Breaks:* `rewriteOf`, `sameAs`, `equals`
  [docs/equality.md](docs/equality.md)

- **Breaking: a rule concluding `(disjointMetatype M)` separates M's members while the KB
  runs.** The mark reached the taxonomy only when a restart replayed it, so one store
  answered `disjoint?` two ways either side of one.
  *Migration:* a fact contradicting such a separation is refused `:disjoint` at assert time
  now, where it was stored unchallenged.
  *Breaks:* `disjointMetatype`, `:disjoint`, `disjoint?`
  [docs/taxonomy.md](docs/taxonomy.md)

### Belief, and reports that read as content

- **Breaking: a re-asserted fact keeps the stronger defeat class.** The premise mark was
  last-writer-wins, so a bare re-assert of known-true content retired it and the
  `:monotonic` negation then *defeated* the original — where the same three sentences
  without the re-assert in the middle leave an irreducible clash. The class resolves from
  content at the fact door as it already did at the rule door.
  *Migration:* narrowing a class is `retract!` and re-assert, as it is for a rule's
  `:direction`, `:defeasible` and `:strength`.
  *Breaks:* `:strength`, `defeat-class`
  [docs/nmtms.md](docs/nmtms.md), [docs/canonicalization.md](docs/canonicalization.md)

- **A justification reports as content, in both directions.** 0.6.0 closed every report and
  election that keyed on retrieval order; these are the two justification surfaces it left.
  `dependent-justifications` handed back an allocation-ordered id set unsorted, so two
  assertion orders of one KB listed the same dependents in opposite orders on a public API;
  and a firing's stored antecedent vector is ordered where it is **built**, since a firing
  is seeded by whichever antecedent triggered it. One carried from an earlier release keeps
  the order it was written with until it is re-derived.
  *Class:* neither label; the order it displaced was a function of how the KB was loaded, so
  nothing stable was there to depend on.
  [docs/nmtms.md](docs/nmtms.md), [docs/api.md](docs/api.md)

- **The wholesale wipe stops carrying the qualitative join baselines.** `clear!` left
  `:qcn-joined` standing beside the network cache it reset, describing a KB the call had
  just deleted. Hygiene rather than correctness — a stale baseline self-invalidates through
  its handle-subset check — but the wipe is the one thing that reaches a baseline.
  *Class:* none; resident engine state with no caller-visible surface.
  [docs/qcn.md](docs/qcn.md)

- **`why` builds its proof tree over an explicit work stack, not the JVM stack.** The walk
  was real recursion capped at a depth of 256 — but the cap is a ceiling on the *tree*, not
  a fix: a chain down a long transitive closure repeats no handle, so the cycle guard never
  fires, and a `{:max-depth n}` past the JVM's frame budget overflowed on a KB merely large.
  The walk is iterative now, so the cap bounds the size of the tree returned and nothing
  overflows however deep the derivation runs. A regression test pins it on a deliberately
  small stack, since the depth a recursion tolerates is the platform's and not the engine's.
  *Class:* neither label; the tree returned is identical, and the one input whose behaviour
  moves — a derivation deeper than the JVM's frame budget — returns its tree where recursion
  threw `StackOverflowError`.
  [docs/api.md](docs/api.md)

### Doors, catalogs and reports

- **Breaking: a top-level vector sentence is refused at both families of door** (`:shape`).
  A vector is `sequential?`, so `assert` flattened it to the list it looks like — while a
  vector goal is what every read door spells a **conjunction** with. One spelling, two
  doors, opposite answers, neither raising: `(assert kb '[likes Tom Ann])` stored the list
  and `ask` found it on the vector, while `prove` and `query` joined three symbols and
  answered nothing; and `ask` flattened the documented goal `[(dog ?y) (parentOf Tom ?y)]`
  into a sentence nothing matches and answered **false**. Nested vectors are untouched, as
  is `lookup`, whose level 0 reads a vector as an index path.
  *Class:* Breaking; a caller who wrote the vector spelling on both sides had code that did
  what its author believed, and it stops on upgrade.
  *Migration:* write one sentence as a list — `(likes Tom Ann)` — and ask a conjunction with
  `query` or `prove`, which are the doors that join.
  *Breaks:* `:shape`, `sentexes-matching`, `handle-of`, `ask-within`, `prove-within`,
  *Breaks:* `query-plan`, `provable?`, `query?`, `abduce`, `assert-inert`, `check-edit`
  [docs/api.md](docs/api.md), [docs/troubleshooting.md](docs/troubleshooting.md)

- **Refusal: a `nil` conjunct is a conjunct, not the absence of one.** The guard read the
  *value* of the first non-sentence member, so `[(dog ?x) nil]` passed it and the join then
  answered nothing — a real conjunct silently zeroed, which is the number nobody can check.
  It tests whether one exists now.
  *Migration:* nothing — the goal never did what whoever wrote it believed.
  *Breaks:* `:shape`, `:conjunct`
  [docs/api.md](docs/api.md)

- **Ten option doors word their refusal the same way, and `open-kb` gains the shape check.**
  The key check was written out at each door, so the wording drifted and one door was
  missing half of it: `(open-kb :nope)` came back as a bare `IllegalArgumentException` about
  creating an ISeq, where every other public entry point answers `:unknown-option`. With the
  doors sharing one refusal (`vaelii.impl.opts`) four messages change wording and `poll`'s
  ex-data gains the `:unknown` key the others carried; `:type` and every other ex-data key
  are unchanged at all ten. Separately, `query`'s non-map refusal reports the value it
  rejected under `:got` rather than under `:options`, which everywhere else is the roster.
  *Class:* Refusal for `open-kb`'s non-map, which previously threw an unnamed error.
  *Migration:* none for a caller discriminating on `:type`. A caller matching refusal text
  should match `:type :unknown-option` and read `:options` / `:unknown` instead.
  *Breaks:* `:unknown-option`, `open-kb`
  [docs/namespaces.md](docs/namespaces.md)

- **Breaking: a store on disk is recognised by the format marker it writes, not by a
  directory pair.** `catalog/classify` read a `records/` beside an `index/`, which three
  disk backends never write — so a store the browser could open listed as nothing at all,
  while a pair left by something else listed as a store and failed on open. It reads
  `records/format.edn` now.
  *Class:* Breaking; a directory's classification changes in both directions.
  *Migration:* none for a store this build wrote. A catalog entry pinned by a caller's own
  path should be re-listed.
  *Breaks:* `classify`, `:store`
  [docs/catalog.md](docs/catalog.md)

- **Refusal: `unload!` reports the release it actually performed, and gives way to the walk
  it would have emptied.** A `close-dir!` that threw was logged and the entry dropped, so an
  unload reported clean over a store whose index had not fsynced; the entry keeps its place
  with status **`:unreleased`** now, stops being the active KB, and a later unload retries.
  An entry whose KB a running export is still walking is refused **`:still-exporting`** —
  the walk has no snapshot.
  *Migration:* nothing for an unload nothing else is holding, which is every unload that
  succeeds; a caller catching around `unload!` sees `:unreleased` where a store that did not
  close reported silent success.
  *Breaks:* `unload!`, `:unreleased`, `:still-exporting`, `reset-registry!`
  [docs/catalog.md](docs/catalog.md)

- **Every kind `violations` can file has a row in the table consumers branch on.** It named
  six of the thirty, and all six rows carried `:detail` keys the entries no longer build.
  `violation_roster_test` scans the sources both ways.
  *Class:* neither label; no kind is new or moved. [docs/api.md](docs/api.md)

- **Refusal: a two-axis calculus checks its projection is a bijection.** The cardinal
  directions and the relative frame are one algebra — nine relations that are two
  independent coordinates on two axes — built now by `vaelii.impl.projection` from a single
  table each. A table that is not a bijection onto the nine axis pairs is refused where it is
  built (`:bad-algebra`) rather than composed: a missing pair composes to `nil` and stores it
  as a relation, and a repeated one still covers all nine while the inverse silently drops
  one.
  *Migration:* nothing — both shipped tables are bijections; a caller building their own
  calculus gains the refusal.
  *Breaks:* `:bad-algebra`
  [docs/qcn.md](docs/qcn.md)

### The shipped ontology

- **`asymmetric` stops claiming it hands you irreflexivity.** `CxCore`'s definition said the
  mark "makes ?predicate irreflexive too". It does not: conviction needs a *believed
  opposing claim*, and a self tuple `(?predicate a a)` is its own mirror, so there is no
  second claim to convict against and the door admits it. `CxSize`'s note on `largerThan`,
  which leaned on the same wrong step, is reworded to rest on preservation running downward.
  *Class:* neither label; ontology content, which §3.8 exempts from the Breaking label
  however far it moves an answer — and here it moves none, the engine having always behaved
  this way. What changed is a description that told a reader to expect a refusal nothing
  performs. [docs/taxonomy.md](docs/taxonomy.md)

### Performance

Three passes over the predicate hierarchy were quadratic in a *batch* of `genl` edges,
which is what a load writes. All three are measured and explained in
[docs/taxonomy.md](docs/taxonomy.md), "What a batch of edges costs the passes that read it";
the answers computed are identical, and all three are free where nothing is declared.

- **A settle reads its `functional` and `asymmetric` marks once, from the marked end.** Four
  gates asked the one question through `tax/props-over`, whose memo keys on the node a walk
  began at, so nested roots shared nothing. `settle/clash-marked-below` walks the marks
  **down** instead, once per pass. 1,000 askers over a 1,000-predicate chain go from 213 ms
  to 1.1. *Class:* neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **A batch of `genl` edges costs the union of its subtrees, not the sum of them.**
  `settle/report-arity-reach!` expanded each edge's spec subtree separately, and none of it
  was bounded — the instance budget counts facts examined and this examined none.
  `tax/specs-of-all` seeds one traversal with every root: 512 edges go from 60.6 ms to 1.0.
  *Class:* neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **The two retroactive `genl`-edge arms decide there is nothing to draw before reading the
  subtree, not once per fact inside it.** `special/equate-under-edge` had no gate at all, so
  every `genl` write on every KB materialized the subtree's extent to discover nothing was
  functional. **No curve moves** — `subsumption-seeds` walks the same subtree and must.
  *Class:* neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **A check for a shape the sentence does not hold stops building a seq to find out.** Seven
  readings descended every sentence with `tree-seq` hunting a form almost none contain;
  `sentex/some-form` and `forms-where` are the two walks they share now. 13x on a plain
  one-antecedent rule assert and 25x on a six.
  *Class:* neither label; same answers, same depth-first pre-order.
  [docs/canonicalization.md](docs/canonicalization.md)

- **A refused sentence stops paying to resolve a stack trace nobody prints.** A checked
  import counts what the front door refuses, so the throw is a reporting path taken a hundred
  thousand times in a load — and three quarters of it was `ex-info` materializing the trace
  to elide its own two frames. `check!` builds the `ExceptionInfo` directly.
  *Class:* neither label; same class, same message, same `:type :naming` ex-data.
  [docs/naming.md](docs/naming.md)

- **A justification listing builds its content key once per entry, not once per comparison.**
  `sort-by` calls its key fn from inside the comparator, and a rule handle is an antecedent
  of every firing it licenses, so `dependent-justifications` paid the multiple on the whole
  history. Decorate, sort, undecorate.
  *Class:* neither label; the same `compare` over the same keys, both sorts stable.
  [docs/nmtms.md](docs/nmtms.md)

### Tooling

- **The whole matrix at once.** `lein test-matrix` runs the eight storage backends and the
  five sweeps concurrently, one JVM per configuration: ~13 minutes against the ~55 the two
  single-axis scripts take in sequence, which is the difference between a check that gets run
  before landing and one that gets skipped. Each configuration records the revision it
  compiled and the report says whether they agree; a red run names the failing **tests**,
  rolled up across configurations. *Class:* neither label.
  [docs/operations.md](docs/operations.md)

- **Every verdict names the tree it is a verdict about.** `lein gate`, `test-backends`,
  `test-sweeps` and the sharded test stage print the revision and the `src/`/`test/` dirty
  state on their banner, every summary row and every log they write: a count read an hour
  later is only comparable against the tree it was taken on. Progress splits by reader —
  mark rows for a terminal, one line per namespace for a pipe or CI, forced either way with
  `SUITE_PROGRESS`. *Class:* neither label. [docs/operations.md](docs/operations.md)

## 0.7.0 — 2026-08-12 — "contexts get one spelling"

- **Breaking: a context name is `Cx`-prefixed, not `Context`-suffixed.** `CoreContext`
  is `CxCore`, `CxUniverse` is `CxUniverse`, and the `assert` front door refuses a
  `Context`-suffixed name by the same naming check that already refused a malformed
  predicate or type. *Migration:* respell every context name — in a stored KB, an
  `assert` call, and a saved dump — to the `Cx` form. `docs/naming.md`.

- **Breaking: the context-transitivity predicate is `genlCx`.** `(genlContext sub super)`
  is `(genlCx sub super)`, so the relation between two contexts is spelled the way the
  contexts it relates are. The `genl` closure over types keeps its name. *Migration:*
  respell the predicate wherever an edge is asserted, matched or retracted; a stored
  `genlContext` edge is a fact under a predicate nothing reads, so re-assert it rather
  than expecting the taxonomy to find it. `docs/taxonomy.md`.

## 0.6.0 — 2026-08-12 — "stored rules become first-class"

A rule can conclude a rule, a NAF guard written as a
conjunction guards instead of firing unconditionally, and every door that reaches a rule
reads **belief** rather than storage. Beside them, the arrival-order dependences left in
the belief loop are closed — a revived datum, an un-merged spelling, and every report,
digest and election that keyed on retrieval order — and two reads that grew with what the
KB *holds* rather than with what the write *touched* now read forward off the region.

**Three entries are Breaking**, which is what makes this a minor rather than a point
release: the daemon answers an export refusal 400 where it answered 500, the model's tool
surface drops two ops, and the CLI's refusals move to stderr. Seven Refusal entries batch
here rather than each forcing its own release, which is what §3.8 of `CONTRIBUTING.md`
designates a minor for. Every Breaking and every Refusal entry carries its *Migration*
line.

**Triage, for a 0.5.1 caller.** This is the index to what touches something you have
written.

| If your code… | Then |
|---|---|
| treats a 5xx from the daemon's `:export` op as a backend fault | the five destination refusals answer **400** now; retry logic keyed on 5xx stops retrying a caller mistake |
| drives `:preview` or `:clear-caches` through the LLM tool surface | they are no longer exposed to a model — call the op on the daemon or the API directly |
| writes `(ist Ctx S)` in an antecedent or an `exceptWhen` | refused `:not-well-formed`; say it with `decontextualizedPredicate` or a `genlCx` edge |
| passes `(ist Ctx S)` to a read | it answers now instead of returning empty, with the named context winning over the argument |
| writes `(unknown (and A B))` as a guard | it guards now; it fired unconditionally before. Under a quantifier the same shape is refused |
| branches on `violations`' `:violation` with a defaultless `case` | `:functional`, `:asymmetric` and `:constraint-exposure-truncated` are new kinds |
| runs `check` over `(not (implies …))` | refused `:not-well-formed` at both doors, where `check` passed it and `assert` threw |
| runs a `:refuse` KB and reads an empty `violations` as a clean bill | cross-context `functional` and `asymmetric` pairs are reported there now |
| passes `--strength` to the CLI's `assert-rule`, or reads CLI refusals off stdout | the flag is honoured now, and refusals print on stderr |
| forks a KB with an opts map naming neither `:space` nor `:dir` | the fork lands on its own space instead of the shared process default |
| asks a `symmetric` predicate about a claim that is inherited rather than stored | the mirror composes with the other provers now, so an `ask` can answer more |
| writes a kind-level `(hasCapability <kind> …)` against the shipped ontology | kind-level claims are `capabilityType`; `hasCapability` is the instance-level reading alone |

- **A capability claim about a *kind* is `capabilityType`, and about a *member* is
  `hasCapability`.** One symbol read at two levels gets one argument check, so seven facts
  the starter shipped were convicted by a declaration the starter also shipped — silently,
  the declaration and the facts sitting in different contexts. The kind-level content moves
  to `capabilityType`, a `typeRelationPredicate` carrying the `argPreserving` pair;
  `hasCapability` keeps `argIsa … 1 animal`. `argPreservingInverse` answers the six
  conclusions that vanish with the kind-level rule. Two new sweeps put every shipped
  sentence to `check` against the fully loaded KB and every stored fact to the declarations
  the same KB ships — either alone misses what the other finds. The `typeToInstancePred`
  pairing stays prose: `hasCapability` cannot carry the mark without changing its argument
  family. *Class:* none; `resources/kb/` is data rather than surface (§3.8).
  [docs/inherit.md](docs/inherit.md), [docs/taxonomy.md](docs/taxonomy.md)

- **A guard keyed on the operator instead of on what it reads.** An `exceptWhen` whose
  query is itself a query operator — `unknown`, a `thereExists`, an aggregate — was indexed
  under a functor no sentex carries, so no arriving fact could queue it: the exception was
  evaluated once and re-evaluated never, blocking forever including after the guard should
  have released, and the stratification graph read the same keys, so a cycle through one
  was refused nowhere. `rules/watched-predicates` peels the frames for all four sites that
  key on them. The settle-time narrowing peels them too, or the corrected key would have
  bought a quadratic — 48 → 192 level-6 evaluations for the same six triggers, against 0
  once peeled. And `check` predicts the NAF-literal refusals rather than only `assert`
  throwing them: they lived in the constructor, so the dry-run door could not see them.
  *Class:* neither label for the guard — belief moves for a rule of this shape, and the
  guard answered from arrival order rather than content; **Additive** for `check`.
  [docs/exceptions.md](docs/exceptions.md), [docs/naf.md](docs/naf.md)

- **A rule can conclude a rule.** `(implies <antes> (implies <antes'> <conseq'>))` is a
  **generator**: its firing stores the rule it concludes, holes filled. The hole split is
  computed rather than declared — a variable the generator's own antecedents mention is
  bound by the join and ground in the mint, every other survives as a variable — so there
  is no template vocabulary to disagree with the template it annotates, and a **hole may
  stand in functor position**, which is the point: one generator ranges over a family of
  predicates while every rule the index keys on has a concrete functor. A mint is derived
  content, justified by the firing rather than marked a premise, so retracting what
  licensed it un-believes it through the ordinary relabel. Rules follow belief now at all
  four chainer sites, which is what makes that work. Five refusals bound it: a generator
  generating a generator, an `exceptWhen` on the stamped rule, a `set/backwardRule`
  generator, one sharing no variable with what it stamps, and a generator **cycle** —
  refused outright rather than depth-capped, since a cap makes the KB's contents a function
  of how long the chainer ran. *Class:* **Additive**; shapes that were refused are accepted,
  and nothing could previously make a stored rule un-believed.
  [docs/generators.md](docs/generators.md)

- **A NAF guard written as a conjunction now guards.** `(unknown (and A B))` was accepted
  and inert in three places at once: no prover claims the functor `and`, so the goal came
  back unanswered and read as *not derivable* — the `unknown` holding, the rule firing
  unconditionally — while the re-check index posted it under a predicate no fact carries
  and the stratification check drew its negative edge from the same functor. An author who
  wrote a two-condition guard got a rule with no guard at all. `sentex/naf-query-conjuncts`
  is the one accessor all four readers share, so the conjuncts are evaluated by the
  exception's own block-if-all evaluator, each conjunct's predicate is watched, and each is
  a negative edge; conjuncts are sorted and flattened, as an exception's are. A conjunction
  **under a quantifier** is refused (`:quantified-conjunction`) — read flat, each conjunct
  would be satisfied by a different witness, so "has a sick child" would hold of anyone with
  a child while anyone at all was sick — and an empty conjunction with it.
  *Class:* neither label for the guard, no author's code having done what its author
  believed; **Refusal** for the two shapes. *Migration:* bind the witness with a generator
  antecedent and leave one literal under the `unknown`.
  [docs/naf.md](docs/naf.md), [docs/aggregate.md](docs/aggregate.md)

- **The strictest policy stops being the leakiest.** Under `:refuse` a cross-context
  `functional` or `asymmetric` clash was neither refused nor reported: the definitional
  checks are scoped to the writer's own cone, the vantages are deliberately withheld under
  that policy, and the exposure ledger had an entry kind for disjointness only.
  `settle/expose-constraint-clashes!` files `:functional` and `:asymmetric` entries shaped
  like the `:disjoint` one, re-deriving each clash from the vantages the refusal itself
  would ask from — so the report cannot drift from what the door would refuse, and closing
  the gap widened no vantage. It costs a KB declaring neither property two `seq`s, gated on
  the declared vocabulary; a `genlCx` edge is the one trigger reaching past the region,
  because visibility itself moves there. Entries are capped and never silently
  (`:constraint-exposure-truncated`), and keyed on the handle pair so both arrival orders
  file one entry. *Class:* **Additive** — a new entry kind in an accumulating ledger. A
  `:refuse` KB that saw an empty `violations` may now see entries, which is the point.
  [docs/nmtms.md](docs/nmtms.md)

- **A hidden set kept where the sentexes are, not rebuilt per placement.**
  `res/excepted-handles` fetched a record, re-derived a target and asked `jtms/in?` for
  every stored `except` in the KB, per placement and per candidate justification.
  `kb/note-excepted!` maintains `{context -> {hidden-handle -> #{except-handle}}}` at the
  store instead, rebuilt by `recover` because no store holds it; the roster holds what is
  **stored** and readers filter by belief, since an `except` can be defeated with no sentex
  arriving. On 400 facts and 380 derivations the read goes from 88.8% of the run to 3.1% at
  1,000 excepts, and 0 excepts is unmoved. `res/hidden-fn` hands back a predicate — nil when
  the vantage hides nothing — so callers with handles in hand stop materializing a set.
  The guard is an oracle: `meta_sentex_test` compares the roster against a full scan of
  storage after every kind of arrival, defeat, revival and removal, across a `recover`.
  *Class:* neither label; same arity, same contract, same answer set.
  [docs/contexts.md](docs/contexts.md)

- **The planner's subtype fan is made cheap rather than remembered.** `est-matches` cost a
  unary type literal over the type's whole subtype closure, once per pick per plan per
  firing attempt — **13.2%** of a chaining run on a 364-type hierarchy. For the shape that
  costs, `fan-of-roots` reads the trie counts directly and the fan halves to 6.8%; a deeper
  prefix still takes the general walk. Remembering the answer instead does not work and the
  harness says so on both paths: a memo stamped on the change clock measures 0.98–0.99x
  under chaining, the run's own placements retiring the entry between one plan and the next,
  and a finer stamp is unsound rather than fiddly. `lein perf` gains `visibility-reading`,
  the check that would have caught the walk above — flatness being a growth claim a ratio
  can see. *Class:* neither label; the number returned is identical by construction.
  [docs/inference.md](docs/inference.md)

- **`ist` places, and four layers had it half-reading.** An `(ist Ctx S)` in antecedent or
  `exceptWhen` position is refused `:not-well-formed`: the literal is matched under a
  functor no sentex carries, so it satisfies nothing — while the naming check, range
  restriction, canonicalization and well-formedness all read the frame as meaningful, so
  `check` reported no problems and `assert` returned a handle. A positive antecedent yields
  a rule that cannot fire; an `exceptWhen` never matches, so the conclusion it was written
  to block stands believed; an `(unknown (ist …))` fires unconditionally. The refusal names
  both repairs. On the read side the same form now **answers** — every door taking a
  sentence and a context asks S in Ctx, the named context winning over the argument, which
  is the resolution `assert` already makes. It grants no visibility a context argument did
  not already grant. A wrong-arity `ist` or one standing as a conjunct of a vector goal is
  refused rather than answered empty. *Class:* **Refusal** for the antecedent and the two
  read shapes, **Additive** for the reading. *Migration:* say a rule's premise with
  `(decontextualizedPredicate P)` or a `genlCx` edge into the rule's own cone.
  [docs/contexts.md](docs/contexts.md), [docs/api.md](docs/api.md)

- **A datum that comes back believed goes back on the agenda.** Two routes let belief
  arrive with nothing chaining behind it, so the same knowledge in one order concluded and
  in the other did not. A revived antecedent licenses the firing its defeat withheld — the
  firing that never happened left no justification to release and reached no placement to
  re-ask — so the trigger is read from `jtms/revived`, with `jtms/touched-new` naming the
  nodes the window created so a re-seed is not a second forward chain per settle. The
  equality door is the same defect where `revived` cannot see it: supersession moves belief
  with no relabel behind it, so `refresh-supersessions` feeds `*unmerged-sink*` and settle
  re-seeds, bounded by `max-unmerge-rounds`. *Class:* neither label; belief moves only
  toward conclusions the same knowledge already reached in another order. Guards: both
  un-merge routes and twenty orderings, six of which disagreed.
  [docs/nmtms.md](docs/nmtms.md), [docs/equality.md](docs/equality.md)

- **An answer picked from a fan is keyed on content, never on arrival.** Fourteen reads
  elected a survivor, a representative or a display line by retrieval order, which under the
  columnar index is assertion order. Two of the keys were also being elided by an ambient
  `*print-length*` — including a digest stored durably in `termOfUnit` content — so the
  print vars are bound off wherever EDN is written for something other than a human to read.
  The elections themselves span `dedup-constant`, clash reports, `one-supporter`, glosses,
  `rewrite-target`, `why-not`'s `:contradicted-by`, the quality rule line,
  `strongest-per-tuple`, ASPIF emission and `label-context`'s minted copies. And the handle
  cache stopped answering from another KB: `canon-stamp` carries the record store, two KBs
  declaring nothing symmetric having stamped one shared empty set. *Class:* neither label;
  the order displaced was not reproducible for the same knowledge.

- **A collected NAT leaves none of its bookkeeping behind.** `nat/bookkeeping-handles`
  answered lazily while its caller retracts what it hands back, so a tail forced after the
  `termOfUnit` map's own retraction found no expression and the result types stayed stored —
  in the retrieval orders that hand back the map first, and not in the others. The set and
  the orphan list are realized before the first retraction. *Class:* neither label.

- **A stored sentex is not a believed one, and five reads had it the wrong way round.** ASP
  grounding takes only believed assumption and constraint rules, a records-only import
  stores each record with its dump strength and premise mark so a later `recover` has
  premises to believe, the catalog's belief caveat probes for a believed datum rather than
  any node, and the generator reports `:stored` as storage. The converse correction is the
  reified-NAT sweep: uses count by **storage**, since a stored-but-OUT use revives and
  collecting the map from under one dangles the constant. *Class:* neither label; each read
  answers the question its docstring already claimed. [docs/nat.md](docs/nat.md)

- **Retrieval answers what the reference answers.** Four matching reads disagreed with the
  fan-out they are checked against, three of them silently: the mirror probe asks the
  candidate's own functor rather than mirroring whenever *some* predicate under the queried
  one is symmetric; `naf-query` unwraps an aggregate as it unwraps `thereExists`, so the
  count moving no longer leaves the old conclusion believed; the rete alpha matcher skips
  `exceptWhen` meta-sentexes; `aggregate-values` normalizes compound values, so two
  spellings of one merged measure count once; and the three pre-canon reads that gated on
  the list spelling take the vector spelling as the same sentence. *Class:* neither label;
  the answer withdrawn was one the two paths disagreed about.
  [docs/inference.md](docs/inference.md), [docs/canonicalization.md](docs/canonicalization.md)

- **A symmetric or inverse reading composes with what is derived.** The mirror answered off
  storage alone, so an *inherited* claim had no mirror; `(pred b a)` goes back through the
  registry minus `SymmetricProver` now, bounded at two levels by `*mirror-depth*`. A partner
  declared on a sub-predicate is the same edge (`tax/inverses-under`), the mirror licenses
  the forward door and the firing names the symmetry it read through, and a defeat inside
  arbitration re-joins what its sentence licensed over closures refreshed to what is
  believed now. *Class:* neither label — answers are added, none withdrawn.
  [docs/inherit.md](docs/inherit.md), [docs/taxonomy.md](docs/taxonomy.md)

- **A negated rule is refused at the door.** `(not (implies …))` built a `RuleSentex` whose
  key cannot be computed, so `check` answered admissible and `assert` threw a bare
  `IndexOutOfBoundsException` from inside the store; `connective-problems` refuses it
  `:not-well-formed` at both doors. **And a rule cannot be stored inert:** `assert-inert` is
  the labeling primitive, and what one bought was a rule that had never been through
  `index-rule-sentex` — believed, unreachable by any chainer, and unfixable by a later
  `assert` of the same rule. Refused `:not-indexable`, with the message naming the other
  inertness: `set/inertRule` is a rule that is believed, indexed, browsable and fires
  neither way. Beside them, five legal API calls stop failing under `clojure.spec`
  instrumentation. *Class:* **Refusal** for both — one shape reached a stack trace rather
  than storage, the other a rule nothing was firing. *Migration:* assert a negated rule as
  the positive rule with the negation in the consequent; a rule meant as documentation is
  `set/inertRule`, and one already stored inert is `retract!`ed and re-asserted.
  [docs/solving.md](docs/solving.md), [docs/inference.md](docs/inference.md)

- **Storage keeps no dead frames, and a torn dump refuses.** A round of durability fixes
  across the disk store, the overlay and both import paths — the class the gate's memory
  backend cannot see, which is why the matrix exists. **`:truncated-dump`** compares frames
  read against what `meta.edn` states on both import paths, and the records-only path
  refuses a dump naming a handle twice, where the second frame silently destroyed the first
  record and counted both. No frame whose only fate is a tombstone: `unmark-premise!`
  re-stores only a record carrying a strength, and the overlay's set insert removes a
  removal record only when one exists. Two reads at open: `validate-idx-tail!` rides the
  chunked walk instead of a seek per slot, and `rebuild-premises!` tombstones crash damage
  only, rethrowing `:unknown-frame` — a build that cannot read a log must not delete it.
  Index entries are normalized at the export frame, so one logical index stops dumping
  byte-differently per backend. *Class:* **Refusal** for the two new kinds — one input is a
  truncated file, the other loses a record it reports as loaded. *Migration:* re-export.

- **The uberjar loads the ontology it ships.** Layer discovery listed a directory, which a
  packaged jar need not carry, so an uberjar started with `CxCore` alone and no upper or
  middle layer — silently, the KB simply being smaller than the same tree run from source.
  Discovery lists the jar's own entries now, anchored on `kb/CxCore.txt`, and an unlistable
  protocol is refused rather than answered nil. *Class:* neither label; a caller running
  from source saw every layer already.

- **ASP routes to a solver that can actually run.** `AUTO` handed off past the size cutoff
  on `available?` alone, so a machine carrying `libclingo` and no `clasp` binary solved
  small programs and threw on large ones — the failure arriving with the workload rather
  than at the probe. The handoff is gated on a once-per-JVM probe that runs the binary; a
  missing one is `:solver-unavailable`, `clingo`'s aspif temp file is deleted on any exit,
  and `dense-roots`' reserved family throws `:reserved-family` rather than pinning a
  three-element decode for a four-element key. *Class:* **Refusal** for the two new `:type`s.
  *Migration:* install `clasp` if you relied on the large-program path, which was throwing.

- **The daemon answers a caller's mistake with 400, and the model's tool surface loses two
  ops.** `:export`'s five destination refusals join `serve/client-error-types`, so a
  directory that exists and is not empty stops counting as a backend fault at every reverse
  proxy between the caller and the daemon; and `:preview` and `:clear-caches` are excluded
  from the tool surface a model reaches, neither being a read whatever its name suggests.
  A cancel can no longer unsettle a finished job. *Class:* **Breaking** — a status code, and
  a removal from the exposed tool set. *Migration:* a client that retries on 5xx will report
  these instead of retrying, which is the intent; call either op on the daemon or through
  `vaelii.core` directly.

- **The browser writes what it shows, and shows what the ledger holds.** Four ledger kinds
  are about a pair or a budget rather than a dropped sentence, so each row printed "nil"
  beside a live link to `/term?q=nil`, while `:message` at the top level went unread on the
  two kinds that put it there — both renderers read either now, and `core/violations` states
  that `:sentence` and `:context` are not on every entry. The editor survives a
  conjunction-concluding line, which was refused `:bad-handle` *after* the write had landed;
  a write is refused while an export walks the KB; `unload!` waits for a `:cancelling`
  loader as for a running one; and a repeat source's key suffix is one past the highest
  still loaded. A fork with an opts map naming neither `:space` nor `:dir` lands on its own
  space rather than the shared process default, where two forks saw each other's writes.
  A KB whose store cannot be counted renders `:unreadable` rather than as a healthy empty
  one. *Class:* neither label. [docs/overlay.md](docs/overlay.md), [docs/web.md](docs/web.md)

- **CLI flags mean what they say.** `assert-rule` passes the `--strength` it parsed —
  accepted-and-dropped stored a known-true rule at `:default` — and asserting a rule that is
  already stored now marks the premise, which matters more: a generator's stamped rule is a
  conclusion, so asserting it returned a handle for a rule that retracting the generator
  took away. The class resolves from content, as `:direction` and `:defeasible` do. A value
  flag refuses a following flag as its value instead of opening a directory literally named
  `--starter`; a flag belongs to the commands that read it, and one carried elsewhere is
  refused rather than dropped; and refusals print on **stderr**, so a script reading stdout
  as EDN gets data. *Class:* **Breaking** for the stream move and the per-command roster,
  **Refusal** for the flag-as-value. *Migration:* redirect with `2>&1` if you read refusals
  off stdout; drop the flags your commands were ignoring; re-assert any rule whose
  `--strength` was dropped. [docs/canonicalization.md](docs/canonicalization.md)

- **Three more costs read the change rather than the KB.** The overlay's removal record asks
  the base `kv-member?` instead of materializing the whole posting per probe;
  `refresh-equality` walks the moved handles through a reverse map instead of re-asking
  belief of every supporter per merge; the qualitative join baselines live in their own
  bounded map, so the resident cache clearing at its limit no longer degrades every later
  delta join to a full one; and `settle`'s `clash-candidates` sorts the moved region only
  when something reads the order — a `:refuse` KB, the default, paid two sorts per settle to
  feed a pass that was never going to run. `core/check`'s docstring says what it predicts
  and what it does not. *Class:* neither label; each answers what it answered.


## 0.5.1 — 2026-08-11 — "faster writes, more to watch"

A run of costs that grew with what the
KB *holds* rather than with what the write *touched* — the taxonomy reconcile, the five
flat caches, the reified-NAT orphan sweep, a retraction's teardown, the standing-clash
ordering, a context-cycle repair, a repeated closure ask and a query plan's child count —
each now reads forward off the region a settle moved, and each has a `lein perf` check
standing where the claim is. Four places where **arrival order decided an answer** are
closed. Beside them the process gained instruments for the rest: the change feed crosses
the process boundary as a subscription with a cursor, long work is a job registry with a
screen that watches it, `kb-quality` reads the knowledge where every other instrument
reads the engine, and the conjunctive planner costs a join rather than a column of
literals.

**No entry is Breaking**, which is why this is a patch. Three carry a *Migration* line
anyway, because a caller can observe them and should be told what to expect.

**Triage, for a 0.5.0 caller.** This is the index to what touches something you have written.

| If your code… | Then |
|---|---|
| reads the first N of `preview` / `edit-with-consequences!`'s `:believed-added` or `:believed-removed` | you get a different N — the halves are content-ordered now, and were handle-ordered |
| calls `clear-caches` and expects the literal cache's hit rate to zero | pass `{:counters? true}`; the reset is off by default |
| walks a `declared-transitive` predicate that also declares an `inverse` | the walk sees the inverse-recorded hops too, so an `ask` can answer more |
| branches on `violations`' `:violation` with a defaultless `case` | `:arbitration-truncated` is a new kind |
| builds on the shipped Space or Time vocabulary | an argument position that held `thing` now names a type, so an assert 0.5.0 accepted can meet an `:arg-type` refusal — widen the convicting declaration it names, or state the argument at a type the position admits |

- **A settle pays for the region it moved, not for what the KB holds.** Eight reads were
  charging the second. `refresh-relation` walked every supporter to decide whether to run
  and recomputed every edge's believed-supporter set — 176.6 ms in a 64k-edge relation,
  6.87x across 8x the edges the flip is not about — where `:handle-edge`, the transpose of
  `:support`, reads the scope forward off the moved handles: 9.2 µs, 0.61x. The five flat
  caches read `:cache-support` backward, so every settle paid the declared vocabulary to
  learn it had nothing to do: 5.0 ms at 32k declarations to find nothing, 95 ms for a flip,
  against 5 µs and 1 µs read forward off `:cache-handle-keys`. `record-clashes!` ordered
  every standing clash report on the settle path, so an assert into a KB holding 800
  dilemmas paid for a reading nobody asked for — stored in arrival order and ordered at the
  read by `settle/ranked`, 1.60 → 1.07 ms against 1.05 before the ordering existed. A
  `genl` edge with nothing above or below it cost 800 `arbitrable-violations` calls and a
  `genlCx` edge re-derived 400 opposed bodies; both cost zero now, weighed per pair.
  `refresh-supersessions` re-examined every displaced spelling every settle — 400 calls and
  9.06x against 400 standing merges, now 0 and 1.70x — and a negated exception conjunct
  registered under `not`, hiding the predicate it is about, waved the recheck through to
  `:all`: 1,600 exception evaluations and 10.16x become 0 and 0.91x. What the scoping
  removed was a whole-KB rescan four writers leaned on, so a writer touching a shared edge
  records it in `:dirty` / `:cache-dirty` and the reconcile takes those whether or not
  belief moved there. Gates: `taxonomy-belief-flip`, `flat-cache-belief-flip`,
  `standing-clash-reading`, `taxonomy-edge-arbitration`, `context-edge-arbitration`.
  *Class:* neither label; every reading answers what it answered.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/equality.md](docs/equality.md)

- **The arbitrating half of a bounded pass says when its budget stopped it.** The reporting
  half filed `:exposure-truncated`; the half that spends the same budget *before anything
  is decided* said nothing, so a KB could leave standing a pair a finished sweep would have
  defeated and show a clean ledger. **`:arbitration-truncated`** (`:triggers` `:sample`
  `:budget` `:message`), one entry per settle; pairs past a cut go undecided rather than
  decided the other way, and discovery accumulates in `:clashes` so a later settle can
  surface them. *Class:* Additive — a new `:violation` kind.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A `disjointMetatype`'s membership is vocabulary, not a roster.** `(disjointMetatype M)`
  separates M's members by being consulted, so `(M b_t)` leaving stopped separating the
  pair while the mark still stood, no closure moved, and neither member was in the region —
  the KB kept reporting a dilemma the oracle does not. Only the departure was silent.

- **Four places where arrival order decided an answer.** A predicate's **second declared
  inverse** hid its first: the taxonomy held one partner per predicate, so
  `(transitive beforeEv)` proved a chain with `afterEv` declared second and failed with it
  declared first, and retracting one dropped the whole entry. `:inverse` is
  `{predicate -> #{partners}}` now, maintained in both directions; `inverse-of` keeps its
  shape and answers the lexicographically smallest. **`kb-quality` ranked its capped lists
  on the handle**, so two loads of one KB reported the same `:never-count` over a different
  `:never` — they rank on content now. **A preview's capped diff** was built off a region
  sorted numerically, so the browser's 50-row panel showed a different fifty depending on
  load order, with `:bounded?` true either way; both halves rank on sentence then context
  at the point each caller caps. And **an LLM prompt** was cut before it was sorted, so a
  term past the cap was shown a prefix of arrival order — the sort precedes the cut at all
  four sites, the scan above it is sorted rather than left in the index's hash order, and
  the heading tells the model it is looking at a sample. *Migration:* a caller reading the
  first N of either preview half gets a different N — a different, better-defined N.
  *Class:* neither label; nothing documented which of two declarations won, and a sequence
  that moved with load order was never a contract.
  [docs/preview.md](docs/preview.md), [docs/taxonomy.md](docs/taxonomy.md),
  [docs/llm.md](docs/llm.md)

- **A card's cut is a count, including the cut that was not counted.** `used-with` claimed
  everything its scan missed was still offered under a later tier, which is false for
  exactly the predicates it exists to find; `:dropped` gains `:unscanned`, one O(1) read per
  position. Beside it, `correct.clj` took `first` of a position's `argIsa` declarations, so
  two contexts declaring one position decided by index order whether a reversed-argument
  alternative was offered — it ranks by specificity now. A declaration's supporters were
  being lost the same way: the `disjointMetatype` sweep walked *believed* memberships where
  it records *supporters*, so a membership defeated at that moment could never be revived,
  and `derive-functional-equalities` took `first` of a `(functional P)` stated in two
  contexts, so retracting one withdrew a merge the other still licensed.

- **The model backends refuse by name, never by value, and a turn that ran out of tokens is
  not a deletion.** The JDK rejects a bad header character by quoting the value verbatim,
  and the browser renders that onto the proposal panel — so a `.env` ending in CRLF was one
  hop from putting an API key on a page; it is `{:type :llm-bad-credential}` carrying no
  value. A streamed body reads under a watchdog (`:llm-timeout`), a 200 whose body is not
  JSON raises `:llm-bad-response` with a bounded excerpt rather than escaping as the JSON
  library's own exception, and eleven sites catch `Throwable` — a `StackOverflowError` on
  deeply nested model text read as *the model proposed nothing*, `canon` overflowing around
  500 nestings against the EDN reader's 5,000. `:stop-reason` is read before the diff, so a
  truncated turn is `:truncated` rather than every row the model never reached coming back
  as a `:remove`. `apply-proposal!` calls `edit!`, which is not a transaction, so it returns
  `{:result :applied :failed-at :error}` and runs the settle by hand on the failure path.
  The `^:llm` consent gate follows the call graph to a fixpoint, one namespace having
  defined a `live-model` that was a bare provider constructor. *Class:* Additive for the
  three new `:type`s.

- **The taxonomy's closures terminate, scope their repairs, and read a repeat.** A `genlCx`
  edge out of a context that sees another one back never returned: the depth potential ranks
  the condensation, and `raise-depth` lifted a single node, which put it above its own mate
  round the cycle without end — the lift moves whole components now. Retracting one edge of
  a context cycle rebuilt every component (11.19x across 16x a background the retraction is
  not about); an edge merely *incident* on a cycle is left alone, and the same retraction
  reads 0.97x. `TransitivePredicateProver` holds the reach per
  `[direction predicate node context]` stamped with the change clock — 0.10–0.14x on a
  repeat over a 2,000- to 8,000-node chain, with no record read at all — and a closed goal
  reads the cache without filling it. `(P ?x ?x)` cost a closure per node to answer nothing
  and is one Tarjan condensation. And a transitive predicate's hops are the believed
  matches, the **inverse spelling among them**: `(transitive before)` walked stored `before`
  facts alone, so an `(inverse before after)` chain broke mid-walk and answered negative
  with no diagnostic. *Migration:* such an `ask` returns at least what it did and never
  less, so the only caller affected is one that counted on an inverse-recorded hop being
  invisible. *Class:* Additive for the cache; neither label for the rest.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/storage.md](docs/storage.md)

- **A unary fact about a reified NAT was deleted with the constant, silently.** One clause
  of the orphan sweep matched on **arity alone**, so `(prime (PrimeFn Seven))` — a claim
  somebody asserted — made the constant look orphaned once its other uses went, and the
  sweep retracted the claim with it. No error, no report. Bookkeeping is decided by
  **authorship** now: `nat/minted-for` re-derives what `mint-nat!` wrote, and everything
  else naming the constant is somebody's assertion whatever its arity. The sweep also cost
  what the whole KB had ever reified — matching `(termOfUnit ?k ?e)` after every teardown
  and to a fixpoint, 16.70x across 16x the NATs the retraction is not about, which on a
  corpus of OpenCyc's order is seconds per retraction — and asks only about the constants
  the teardown's own removals named: 1.22x, gated by `retract-nat-scaling`. A teardown
  records only what that sweep will read, so a KB that reifies nothing pays nothing.
  *Class:* neither label; a caller whose unary claim was being deleted underneath them was
  not getting what they believed.

- **The change feed crosses the process boundary, as a subscription with a cursor.** `watch`
  takes a function and a function does not cross an EDN wire, so the daemon's half is
  `:watch` / `:poll` / `:unwatch` / `:watchers` over a ring and an integer cursor — all four
  in `serve/feed-ops` rather than `serve/ops`, which is what keeps a subscription out of the
  model's tool set. A parked long poll held a thread nothing counted, so 55 concurrent polls
  drove the 50-thread pool to 50/50 busy and `/health` from 62 ms to 25,997 ms:
  `max-parked` (16) bounds how many may wait, and a poll that does not ask to wait is never
  refused. `{:wait-ms 1e300}` answered 500 and `##NaN` made the poll answer instantly
  forever — it is `nat-int?`, capped before coercion — and a subscription dropped while it
  was being registered took the whole feed down permanently. What one caller can allocate is
  bounded three ways, nothing authenticating `POST /op` on the loopback default: 64
  subscriptions, 256 events per ring, and one unpolled for five minutes reaped at the next
  call. The ceilings bound the event count and not the bytes, and the docs say so.
  *Class:* neither label — the feed is new in this release. [docs/feed.md](docs/feed.md)

- **A conjunction is costed as a join rather than as a column of literals.** `plan/est-rows`
  answers what `est-matches` does not — not *can* this literal fan out, a sound upper bound,
  but *how much*, an expectation wrong in both directions and composing for exactly that
  reason — returning the relation's shape and threading it through the planner's fold, so
  the *k*-th pick is costed against the rows reaching it. **No statistics table**: every
  number is already in the count-aware trie, and where neither side read a count the model
  falls back on a proxy rather than calling the join a cartesian product. Generators are
  split into connected blocks and ranked by adjacent transposition, with two placements
  outside the law because they are claims an estimate cannot make. Planning one fixed
  conjunction is now flat in the size of the KB — the cost model asked for a distinct-value
  count once per literal per plan and `(count (children …))` materialized the child set,
  25x more against 32x the facts — and `plan-scaling` reads flat with `p/count-children`
  against 24.6x without. `lein bench-plan` reports the q-error per join depth: 1.00 at every
  depth through six literals, 1.00 / 2.75 / 2.87 on a corpus built to break the independence
  assumption where a compounding model would read about 7.5 at depth 3, and 1.13x the best
  of all 24 permutations against 2.18x before. `query-plan` carries `:est-rows`,
  `:est-prefix` and `:block` beside `:est-matches`. *Class:* **Additive**; a new
  `IndexStore` read, owed by both implementations.
  [docs/inference.md](docs/inference.md), [docs/indexing.md](docs/indexing.md)

- **Long work is one mechanism: a job registry, and the screen that watches it.**
  `vaelii.impl.jobs` holds every operation that takes minutes rather than milliseconds, with
  one status vocabulary, one progress reading and one cancel; `/jobs` watches them, a job
  survives the request that started it, and nothing unsettled is ever dropped, since
  forgetting a job releases its writer claim while a thread still running is still writing.
  The catalog's load and export moved onto the registry rather than beside it, and
  `POST /chain` became a job — a fixpoint over a corpus was minutes of this process's one
  writer inside a request, with nothing on screen and no way to stop it. A second writing
  job is refused `:job-busy`, naming the job that holds the writer. *Class:* not Breaking;
  `:busy` was thrown at one impl site and read by one impl namespace.
  [docs/web.md](docs/web.md)

- **What this process is holding, on a page — caches, heap, and the profiler.** Nothing
  measured what the engine holds *beside* the store, which is a dozen derived structures
  whose whole purpose is that a repeated question is not recomputed. `caches` is one read
  over all of them — entries, the bound they are cleared at, what one entry counts, and the
  hit rate where anything counts one. A row carries `:scope` and `:counters` because the two
  differ: the literal cache's entries are one KB's and its counters are global. Every
  cache-holding namespace declares itself into a register at load, so there is no central
  list to forget, and a row that throws costs its own row and no other. The clear is a
  measuring instrument rather than an edit — bare rather than `!`, moving no belief, usable
  while a load runs — and it no longer zeroes the process-wide hit counters every other KB
  in the JVM was reporting: that is `{:counters? true}`, off by default. *Class:* neither
  label; both are new in this release. [docs/web.md](docs/web.md)

- **The shipped ontology declares its positions, and decontextualizes predicate metadata
  and nothing else.** `CxSociety` declared `(decontextualizedPredicate marriedTo)` — the one
  *domain* relation carrying a mark the rest of the ontology reserves for claims about a
  predicate — so a marriage stated anywhere became a claim of the whole KB, and a rule
  firing on the lifted copy put `knows` within reach of every data context. 227 `argIsa` /
  `argGenl` declarations fill the positions that carried none, at `thing` throughout, and
  six new upper types narrow them where a constraint should refuse something: Space takes
  `spatial_thing` on all 100 of its positions, Time `temporal_thing` on 46 and `time_point`
  on 16. Flight becomes a capability of a kind rather than a verb-shaped one-place
  predicate, with the exception written twice because there are two things to except.
  `::prop-kind` accepts every kind the engine marks, six of ten having been specced — so
  `:asymmetric`, which `has-prop?`'s own docstring lists, was a documented call
  instrumentation refused. *Class:* no label — ontology content (§3.8); what it owes is the
  roster that pins the shipped set. *Migration:* a KB built on the shipped Space or Time
  vocabulary can be refused where 0.5.0 accepted it — the refusal names its convicting
  declaration. [docs/argtypes.md](docs/argtypes.md), [docs/contexts.md](docs/contexts.md)

- **A bulk load is decomposed, and the index write is 57% of it.** `lein bench-loadphase`
  loads one corpus repeatedly with one more phase stubbed out from the outside in, so
  consecutive runs differ by one phase and the deltas **sum to the baseline**: at 1,000,000
  distinct binary facts on `:memory`, 43.4 µs/fact and 23,100 facts/s, the index write is
  56.8%, the JTMS node and premise mark 21.5%, the special-predicate suite 10.5%. Postings
  are 35–39% of the load and count maintenance 6–10%, so **the counts are priced and are not
  the lever**. Two write-side tricks measured worse and are reported rather than built. The
  one write on that path that grew with the corpus is guarded — the negation memo's `:dirty`
  set took a `conj` per fact — which does not move the wall clock but removes a structure
  proportional to the corpus. `lein bench-profile` grows the two arms no reasoning workload
  runs: an interactive arm whose read table is the inverse of every other's (88%
  `:term-index`), and a churn arm, the only way `unindex-sentex!` runs at all.
  [docs/storage.md](docs/storage.md), [docs/profile.md](docs/profile.md)

- **Eleven checks join the perf gate, and 27 in the vector all judge.** A read of the
  standing clash set is Ω(n log n) by construction, so `standing-clash-reading` is calibrated
  from both ends — 85.4x and 80.9x healthy over a floor near 66x, 937.8x with the read
  filtering by cross product — and ships at 175x. `retract-merge-scaling` reads 5.66x alone
  and 10.49x in place and ships at 18x: `lein perf` runs one JVM over the whole vector, so
  that position dependence is a property of the harness rather than of the engine.


## 0.5.0 — 2026-08-07 — "operating the engine as a service"

Operating the engine, in the two senses a running process needs: what it will let a caller
do, and what it will tell an operator it is doing. The daemon authenticates and refuses to
bind an address without a credential, ships as a container image, and says which posture it
started in; every switch the build reads has a row in a table a test keeps honest; the log
level is a dial a running process turns; and the failures that look like answers each
gained something that says so. Nine entries are **Breaking**; the three **Refusal** entries
(§3.8) cover input where what 0.4.0 did with it was run a configuration nobody asked for
and report a clean pass.

**Triage, for a 0.4.0 caller.** Every Breaking and Refusal entry carries its own one-line
*Migration*; this is the index to the ones that touch something you have written or
deployed.

| If your code… | Then |
|---|---|
| names `:record-space` / `:index-space` | one `:space` — keep the record number, drop the index one |
| runs a daemon on a non-loopback `--listen` | export `VAELII_API_TOKEN` there and in every client, or it exits 2 |
| reads a daemon 401, or branches on the wire `:type` | `:unauthorized` is a new one; `GET /health` is the only route without the token |
| relies on `VAELII_RETE=0` running the sweep | it means off now; unset, or `=1` for on |
| sets `VAELII_NOHIER` | it is `VAELII_HIER`, the other way up — `VAELII_NOHIER=1` becomes `VAELII_HIER=0` |
| sets `VAELII_QUERY_ENGINE` / `VAELII_QUERY_STRATEGY` | a name outside the roster is refused rather than silently running the default |
| sets `VAELII_WEB_PORT` for `lein browser` while `-main` stayed on 3000 | it moves both; pass `--port 3000` to pin `-main` |
| lists KBs out of a search-path directory holding more than 200 | name the ones that matter in the catalog file |
| depends on vaelii and has no SLF4J provider of its own | add one — `org.slf4j/slf4j-nop` no longer arrives transitively |
| branches on what `term-role` answers | `:sense` and `:lexeme` are two new answers — add arms, or a `default` |
| writes a `lex`-namespaced predicate | it names a lexeme now, and a lexeme names no relation |
| calls `core/context-size`, or sends the daemon `:context-size` | both are `count-in-context` — same arguments, same answer |
| compares two compound terms with `different` | a merged symbol inside one now makes them equal, where it did not |
| sets `VAELII_ASP_SOLVER` to a name outside `clingo`/`clasp` | it is refused at `open-kb` rather than silently running auto |

- **Breaking: a name can carry two more roles — a sense, and a lexeme.** `term-role`
  answers `:sense` for a disambiguated type and `:lexeme` for a symbol in the `lex`
  namespace, so its documented domain gains two values a total `case` has no arm for; a
  lowercase dashed name is a legal unary type where it was refused, and a lexeme applied to
  arguments is refused (`:lexeme-functor`). *Migration:* add `:sense` and `:lexeme` arms or
  a `default`; a `lex`-namespaced predicate names a lexeme now and cannot be applied.
  `docs/naming.md`.
- **Breaking: `context-size` is `count-in-context`.** The three O(1) cardinality readers are
  one family and two of them said so. *Migration:* `(v/context-size kb ctx)` becomes
  `(v/count-in-context kb ctx)` and `{:op :context-size}` becomes `{:op :count-in-context}`
  — same arguments, same answer, old spellings gone rather than deprecated.
  `docs/api.md`, `docs/indexing.md`.
- **Breaking: `different` descends into compound arguments.** It normalized each argument
  with one lookup in the symbol-keyed equality closure, so a compound was never found in it
  and `(different (QuantityFn 5 Kilogram) (QuantityFn 5 Kg))` answered *different* with
  `(sameAs Kilogram Kg)` believed. *Migration:* a goal comparing two compounds can newly
  answer false where a merge reaches inside one; comparing symbols is unchanged.
  `docs/equality.md`.
- **Breaking: one space number names a KB's stores, `:space`.** A `:disk` KB's derived
  directory is `space-<n>`, and the suite owns a block of two db numbers rather than four.
  *Migration:* `{:record-space 2 :index-space 3}` becomes `{:space 2}`; either retired key
  is refused by name (`:unknown-option`) rather than ignored, and `:dir` names a durable
  directory the derived spelling does not reach.
  *Breaks:* `:record-space`, `:index-space`
  `docs/storage.md`.
- **Breaking: the daemon authenticates, and refuses to bind an address without a token.**
  With `VAELII_API_TOKEN` set every request carries `Authorization: Bearer <token>` or is
  answered 401 `{:type :unauthorized}`, with `GET /health` the only route that answers
  without it. `--listen` naming a non-loopback address without a token is one line on
  stderr and exit 2, where 0.4.0 logged a warning and served the whole write block to
  anything that could reach the port. *Migration:* export `VAELII_API_TOKEN` for a daemon
  that names an address and give the same value to every client; nothing changes on the
  loopback default. `docs/operations.md`.
- **Every switch the build reads has a row, and a test keeps the roster honest.**
  `docs/operations.md` gains a configuration table — 56 environment variables and system
  properties, each with where it is read, its legal values, its default and the one thing it
  decides. `config_surface_test` pins the names in both directions and checks each
  `file:line` citation against the line it names, so the table cannot drift without a
  failing test.
- **Refusal: the four harness switches read a value instead of a presence.** They were
  membership tests, so `=0` ran the sweep it names, and the two query switches took a bare
  `(keyword …)`, so a misspelt engine ran the *default* and reported a clean pass for a
  configuration nothing exercised — the worst shape a test switch can have, since the result
  reads as evidence. *Migration:* none for a value in the vocabulary; a job relying on `=0`
  meaning *on* now gets the sweep off. `docs/operations.md`.
- **Refusal: the ASP backend switches are read against their domains, at the door.** A
  misspelt `VAELII_ASP_SOLVER` matched no arm and ran auto, so a run pinned to clasp could
  use clingo and report a clean pass; `VAELII_CLINGO_MAX_BYTES` threw from the first ASP
  solve rather than from the configuration that was wrong. Both go through `config/check!`,
  refused at `open-kb` by name. *Migration:* none for a legal value. `docs/operations.md`.
- **Breaking: `VAELII_NOHIER` is `VAELII_HIER`, and the sense is the other way up.** A
  switch carrying the negation in its own name makes `=0` mean *on*, and the entry above had
  just made the value load-bearing. `VAELII_HIER` defaults true. *Migration:*
  `VAELII_NOHIER=1` becomes `VAELII_HIER=0`; a `VAELII_NOHIER` left set is simply unread,
  since a variable cannot be refused by name. `docs/operations.md`.
- **The log level is a dial a running process turns.** `set-log-level` takes one of
  `:error :warn :info :debug :trace` and installs Trove's console backend at it; `log-level`
  reads back what is in force, and `VAELII_LOG_LEVEL` says it at startup. Unset, the engine
  installs **no** backend at all, so an application holding its own `*log-fn*` keeps it.
  Three `:debug` statements are what make turning it up worth doing. `docs/operations.md`.
- **Breaking: `VAELII_WEB_PORT` moves `-main`'s port, and not only `lein browser`'s.** Both
  read one `default-port`: the variable, else the `vaelii.web.port` property, else 3000, and
  an explicit `--port` still wins. *Migration:* a deployment that set the variable for `lein
  browser` while relying on `-main` ignoring it now moves both; pass `--port 3000` to pin it.
- **Breaking: a search-path directory is probed for its first 200 entries.** `sources` is
  recomputed per request, which is what lets a corpus appear with no restart and what made
  the scan unbounded. The cut is named on the page and in the log, since a list that quietly
  ends early reads as "this machine has no other KBs". *Migration:* name the ones that
  matter in the catalog file to list them regardless of the count. `docs/catalog.md`.
- **The front door says what a legal-but-wrong sentence should have been.** `(isa Muffet
  Dog)` breaks no naming invariant, so it stored a two-place relation nothing reads while
  `isa?` answered false with nothing to search for. `nm/advice` reads intent where
  `problems` reads the invariants, logging `:warn` once per process with the rewrite that
  was meant; a `:no-placement` drop names `genlCx` beside the entry's own keys.
  `docs/naming.md`.
- **A second `open-kb` defaulting onto the shared in-RAM space now warns**, naming both
  fixes — give the KB its own number, or name `{:space 0}` to say the sharing is meant. A
  warning rather than a refusal, since sharing the space is how `recover` sees the same
  records and how a base is mounted. `docs/storage.md`.
- **Refusal: the CLI checks each command's argument count before it dispatches.** `dispatch`
  reached into `args` with `nth`, so a short line answered `error:
  IndexOutOfBoundsException` and a long one dropped the extra operand in silence. One table
  carries every command's arity, operands and gloss, so `check-arity!` and the usage text
  cannot go out of step. *Migration:* none at the right arity; `lein cli help` prints the
  count each command takes. `docs/operations.md`.
- **`docs/troubleshooting.md` is a new page, indexed by symptom rather than by subsystem.**
  The engine's hardest failures are the ones where nothing goes wrong — a query answers
  `()`, an `assert` returns a handle — so a reader has to already know the cause to find the
  page explaining it. Nine symptoms, each with what you would have observed, how to confirm
  it in one call, and the fix.
- **`lein lint` gains a versions check, and the kondo row notes a local/CI mismatch.** The
  0.4.0 bump left the `:with-foreign` pin naming `0.3.0`, so every
  `lein with-profile +with-foreign` command failed to resolve; `lint-versions` reads that
  pair and the `lein-cloverage` version stated twice.
- **Three doc samples now print what they actually produce, and `prove`'s docstring says it
  counts proofs, not answers.** A goal reachable both as a materialized fact and as the rule
  concluding it comes back twice with equal maps — wrap in `distinct`, or reach for `query`
  / `ask`, which project to the goal's variables.
- **The daemon ships as a container image**, with a two-stage `Dockerfile` and
  `docker-compose.yml`. The container binds an address, so the token is required — an image
  run without `VAELII_API_TOKEN` does not start rather than serving unauthenticated — and
  one container per volume, a second opener being refused `:disk-locked` rather than scaled,
  which is why the compose file carries no `replicas:`. `docs/operations.md`.
- **A reflection warning and an uncalled public var now stop the build.** Both signals were
  already emitted and neither was read: `reflect` compiles `src` and `bench` and fails on
  any reflection, auto-boxing or primitive-recur warning, and `unused` fails on a public
  definition with no usage against a baseline. Ten warnings had to go first, none in `src`.
- **Breaking: `org.slf4j/slf4j-nop` no longer reaches a consumer's classpath.** It sat in
  top-level `:dependencies`, where it could win SLF4J's provider race against a consuming
  application's own backend and silence it — the one thing a library must not do on a
  consumer's behalf. *Migration:* an application that had no provider of its own and relied
  on vaelii's now sees SLF4J's "no providers" line again — add one as its own dependency.
  `docs/operations.md`.
- **A public `--listen` bind with no `VAELII_ALLOWED_HOSTS` now warns.** Naming an address
  drops the `Host` allowlist to every `Host` answered — deliberate, since a reverse proxy
  sets its own — but nothing said so at startup. `host-posture` names the policy beside the
  token question, apart from the TLS line so a reader knows which check is missing.
- **`docs/troubleshooting.md` and `docs/storage.md` name `:type :unknown-backend`.**
  `open-kb` throws it from five call sites and none carried a line in either doc; the entry
  reads the other key each throw's ex-data carries to say which of the five it is.


## 0.4.0 — 2026-08-05 — "correctness fixes against the invariants"

Correctness fixes found by reading the engine against its own stated invariants, in the
places 0.2.0 and 0.3.0 did not reach: a backward-chaining loop guard that made a
conjunctive query answer nothing, doors that disagreed about what they would accept, an
index trusted without being checked against the records it describes, slots and keys that
let arrival order decide belief, and derived caches a settle read one revival out of date.
Thirteen entries are **Breaking**, which is why this is 0.4.0. The **Refusal** entries
(§3.8) cover input where what 0.3.0 did with it was corrupt state or answer a different
question in silence.

**Triage, for a 0.3.0 caller.** Every Breaking and Refusal entry carries its own one-line
*Migration*; this is the index to the ones that touch source you have written.

| If your code… | Then |
|---|---|
| hands `assert` text it did not read as EDN | it is refused (`:shape`) — fix the producer |
| writes `exceptWhen` literals like `(lives_in ?x cold_place)` | spell them to the invariants; re-check any rule 0.3.0 left bare |
| spells an `edit!` batch `{:adds …}` | spell it `{:add […] :remove […]}` — the old key wrote nothing |
| names one of `:record-space` / `:index-space` | name both, or neither, in every opts map |
| passes `:direction` to `assert` on a non-rule | it is refused; a rule takes it and now acts on it |
| states one rule two ways (bare `implies` after a `set/*Rule`) | the slots join by content; `retract!` and re-assert to narrow one |
| calls `edit` or `edit-with-consequences` | they are `edit!` and `edit-with-consequences!` — the wire op stays `:edit` |
| matches `:bad-opt`, or a `:shape` from a non-map `opts` | match `:unknown-option` |
| reads a dump's `meta.edn` dialect | it is `:vaelii` |
| stores skolem witness names across runs | the names moved; rebuild from the assertions rather than carrying both spellings |
| parses a daemon 500 for a client mistake | it is a 400 with a `:type` |
| writes `(ist Ctx S)` with other than three elements | it is refused with `:shape` |

- **A conjunctive query could answer nothing while each of its conjuncts answered.**
  `[(anc Tom ?y) (anc Tom ?z)]` was empty where `(anc Tom ?y)` answered twice: the per-path
  loop guard grew for a whole frame, and a queued conjunct is a sibling of the expansion
  rather than a descendant. Silent in every direction — forward chaining and the node engine
  both answered, `provable?` said false, and `prove-within` reported `:status :complete`.
  `docs/inference.md`.
- **Breaking: `assert` refuses a sentence that is not an s-expression.** A string — what a
  failed EDN read hands back — was stored, indexed and believed as an object no query can
  match; `nil` likewise; a symbol, number or map threw an untyped
  `UnsupportedOperationException`. `check` refused all five, so the door built to predict
  `assert` disagreed with it. *Migration:* nothing a working caller sent is refused; fix the
  producer that handed `assert` unread text, and discriminate on `:shape`.
- **Breaking: an `exceptWhen` query's literals are held to the naming invariants.** A
  literal `docs/naming.md` says is refused was stored as an exception no query could match,
  so the rule read as guarded and fired as bare. Both doors read each conjunct before the
  rule is stored. *Migration:* spell the exception's literals to the invariants, and
  re-check any rule 0.3.0 left bare.
- **Breaking: an `edit!` batch key nothing reads is refused.** `{:adds […]}` bound nil, so
  `edit!` wrote nothing and reported a success, while `check-edit` — whose job is to predict
  exactly that — reported no problem; over the daemon it was a `200 {:ok true}` for a write
  that did not happen. *Migration:* spell the batch `{:add […] :remove […]}`.
- **Breaking: naming one in-RAM space number and not the other is refused.** The two default
  independently, so `{:backend :memory :record-space 77}` paired a private record store with
  the process-default index every other in-memory KB writes: `assert` found the other KB's
  handle, read it as a duplicate, **stored nothing**, and returned a handle `in?` answered
  true for. *Migration:* name both or neither, in every opts map.
- **A durable index is checked against the records it claims to describe.** `layout.edn`
  gated the index's key shape and nothing gated its coverage, so a short index opened clean,
  answered short forever and re-cemented its own stamp — and re-asserting a fact it could
  not find minted a second handle for a sentence already stored. Three ways in: a torn
  `kv.log` tail, a directory grown under a derived-index mode, and a crash between the
  record write and the index batch. `docs/storage.md`.
- **Breaking: `assert` acts on `:direction` instead of accepting and dropping it.** Only
  `assert-rule` read the key, so a rule asserted `{:direction :backward}` stored `:both` and
  forward-chained, materializing the cross product a backward-only rule exists to avoid. A
  `:direction` on a non-rule, one contradicting the sentence's own wrapper, and a value
  outside the roster are refused. *Migration:* spell the direction; a `check` caller matching
  `:shape` for a non-map opts matches `:unknown-option` now.
- **Breaking: a re-asserted rule's direction and defeasibility resolve by content.** Neither
  slot is in the identity key, so a rule stated two ways resolved to one record and the
  second spelling was dropped — arrival order deciding a slot that decides belief. A bare
  `implies` after a `set/inertRule` stayed inert and never fired. The resolution reaches
  conclusions already derived, a justification baking the rule's contribution in at fire
  time. *Migration:* the join only widens a slot; to narrow one, `retract!` and re-assert.
  `docs/canonicalization.md`.
- **The derived caches are reconciled with what `clear-defeats!` revived.** A settle lifts
  last settle's defeats at its top while the cached closures were refreshed only in
  `settle-finish` — after `constraint-nogoods` had read them — so discovery asked its
  question against a vocabulary one settle out of date, and a `P`/`¬P` pair made visible by
  a revived `genlCx` edge went unarbitrated in a state `recover` disagrees with.
- **The disk KV index reads and publishes its RAM map under the lock.** `apply-ops!` read
  `@data` before acquiring and published after releasing while `compact!` runs on the
  durability daemon's executor — a thread the single-writer contract says nothing about — so
  a compaction in either window rewrote the log from a map missing the in-flight write.
  `kv-clear!` was sharper: a compaction between its truncate and its publish wrote the whole
  pre-clear map back over the log just emptied.
- **Breaking: a client's mistake answers 400 with a `:type`, not 500 with none.** An
  unreadable body, a wrong argument count and an unknown op all answered untyped, the first
  two as 500s — which count as backend faults at every reverse proxy and 5xx alarm. The
  engine's whole refusal vocabulary answers 400, unlogged. *Migration:* branch on `:type`
  rather than on the status code; every `{:ok false}` carries a non-nil keyword.
- **The browser's `/propose/*` EDN read catches `Throwable`**, as every other untrusted-EDN
  read in the namespace already does: a deeply nested form raises `StackOverflowError`,
  which an `Exception` catch let escape, and the browser has no exception middleware.
- **Refusal: `query` refuses a non-map `opts` and a negative or non-integer `:max-depth`.**
  Both read as "no depth", which is not an error condition but a *different question* — the
  no-rule-expansion answer, returned as if it were the bounded one asked for.
  `{:max-depth 0}` is admitted: it is that answer asked for by name. *Migration:* none for a
  working caller.
- **Breaking: `edit!` refuses what `check-edit` reports, before applying anything.** The two
  disagreed in both directions: a 4-element `:add` entry applied with the extra silently
  dropped where the dry run reported `:shape`, and a non-sequential entry threw a bare
  `ISeq` error from every door. An unknown `:remove` handle is refused before any entry is
  applied, so a checked-clean batch cannot half-apply. *Migration:* a remove-if-present batch
  filters its handles through `in?` first.
- **The recursive-literal hold-back keys on the peeled predicate.** A `not`- or `ist`-headed
  consequent read its own frame as the predicate, so every frame-headed antecedent was "the
  recursive literal" — two orderings of a negated-head rule minted two handles, and a
  genuinely recursive rule with a negated head lost the hold-back, turning right-recursion
  left-recursive.
- **Breaking: a skolem witness is a function of its rule's content, not its handle.**
  Retracting and re-asserting the same rule re-fired to a *different* witness, so a fact
  stated about the old one silently stopped co-referring — and two KBs holding the same
  knowledge in different orders stored different `termOfUnit` content, a handle in stored
  content that order independence rules out. *Migration:* rebuild the KB from its assertions
  (`export!` / `import!` replays firings) rather than carrying both spellings.
  `docs/skolem.md`.
- **Breaking: `edit` is `edit!`, and `edit-with-consequences` is
  `edit-with-consequences!`.** The batch's `:remove` half runs the same `retract-storage!`
  sweep `retract!` runs, while the name read as additive — the one gap in the `!` roster the
  convention exists to close. *Migration:* rename the calls; the wire op stays `:edit`.
- **Breaking: `:bad-opt` is retired, and one compression spelling survives.** Two keywords
  split one failure class on no rule a reader could predict — seven sites said `:bad-opt`
  where thirty-four said `:unknown-option`. *Migration:* discriminate on `:unknown-option`
  and `:unsupported-compression`.
- **Breaking: the dump's `meta.edn` names its dialect `:vaelii`.** Decorative on the read
  side, but it is a value in the frozen format and a documented key of `import-dump`'s
  return, so the name it carries is now-or-never. *Migration:* a reader matching the old
  value matches `:vaelii`; `import-dump` reads dumps written either way.
- **The node engine's claimed-key reads each guard's identity, not the guard count.** Two
  distinct rules, each carrying its own `exceptWhen`, can rewrite one goal to the same
  canonical residual through the `genl` fan; keyed on the count the two children were one
  key, so the second was dropped before it was enqueued and every answer only its exception
  admits was lost — silently, on the path `query` routes to whenever `:max-depth` is given.
  `docs/inference.md`.
- **A belief flip on a visibility `except` queues the same re-check as its arrival.** Only
  the store and removal chokepoints called `recheck-except`, so an except *defeated* by a
  settle's resolution revived nothing it hid: backward proving answered yes while the store
  held nothing, and which belief set the KB ended with depended on the order the except and
  its defeater arrived.
- **`recover` reads only positive, atomic declarations into the taxonomy.**
  `sentexes-with-functor` returns both polarities and the rebuild arms destructure the
  positive shape positionally, so a stored `(not (genl a b))` bound its inner sentence as a
  taxonomy node and nil as the other — poisoning every cache on any recover, the default
  `{:recover? :auto}` reopen included.
- **A `:neg` nogood is an at-least-one in every reader.** The ASP translation's soft branch
  emitted only the positive body atoms, so a `:neg`-only nogood — what `set/softConstraint`
  over negated choice literals produces — emitted its violation witness as an unconditional
  fact: no steering pressure, and `:violated` reported a satisfied at-least-one as broken.
  `docs/solving.md`.
- **`conflicts` and `contradictions` are content-ordered.** Each report's sides were already
  ordered by content; the *list* came off a hash set of handle-keyed nogoods, so which pair
  `(first (contradictions kb))` returned was an answer about which was typed first.
  `docs/nmtms.md`.
- **Refusal: the connective frames are shape-checked at every door.** An `implies` at arity
  2 threw a bare `IndexOutOfBoundsException` while arity 4 stored a silently truncated rule
  `check` read as clean; `(not A B)` stored as a positive fact whose record and index
  disagreed; a bare symbol passed as a rule literal was accepted, unmatchable; and a
  non-finite measure magnitude stored cleanly, then threw out of every later duration goal
  in the context. *Migration:* nothing a working caller sent is refused — every one of these
  stored an object no query could match.
- **Refusal: the last open rosters close.** `find-terms` and `abduce` take key rosters (a
  misspelt `:keep?` tore down the scratch context whose handles the caller meant to commit),
  the CLI refuses a flag outside its roster, `escalate` refuses a floor outside 0–7, and
  `import-dump` refuses an unknown `:framing` where it guessed a reader and failed as a
  `ZipException`. *Migration:* spell the key or flag as the refusal's roster lists it.
- **Refusal: the web and serve entry points refuse what their grammars do not know.**
  `vaelii.web --listen` with no address parsed to a nil host — Jetty's wildcard bind, with
  the Host allowlist reading nil as *any* — so a truncated command line put the browser's
  unauthenticated write routes on every interface with the rebinding guard off. `serve` read
  its positionals as a prefix, so a misplaced flag ran a disk daemon in memory.
  *Migration:* none beyond completing the command line.
- **Refusal: the opts and shape rosters reach the remaining doors.** The roster guard held
  at `assert`, `why`, `query` and `open-kb`, and every other door took the misspelt key in
  silence — answering a different question than the one asked. *Migration:* spell the key as
  the refusal's roster lists it.
- **Refusal: the operator's mistakes answer in one line.** A CLI flag missing its value bound
  nil in silence — `lein cli assert '(dog Muffet)' Ctx --strength` stored known-true content
  at `:default` — and now exits 1 naming the flag; `--memory --dir` is refused as a
  contradiction. *Migration:* none beyond completing the command line.
- **The browser and CLI survive what they read.** The repl loop and the CLI command arm
  catch `Throwable`, so a deeply nested form answers `error:` and a next prompt; the
  browser's retract POST makes the `check-edit` round-trip `docs/operations.md` promises, so
  a stale handle answers the problem panel rather than a success-styled "Retracted 0
  sentexes".
- **Refusal: every durability switch is read against a domain, and a value outside it fails
  the open.** Each of the thirteen checkable switches was a membership test or an equality
  against one spelling, so none of them had a wrong value — every misspelling was the *other
  branch*, silently: `vaelii.disk.auto-compact=disabled` read as compaction on, and
  `vaelii.disk.fsync=always` as the three-second tick, the level the operator was trying to
  leave. *Migration:* none for a working setup, but two spellings now *act* where they were
  ignored. Spell what you mean. `docs/storage.md`.
- **Refusal: the mapped index image refuses the platform it corrupts on.** The image
  publishes by renaming a new file over the live one while it is mapped, which is what put
  `vaelii.index.snapshot` on macOS and Linux only — `docs/storage.md` said so and nothing
  enforced it, so on Windows the publish failed part-way through a four-file commit.
  *Migration:* none — the property never worked where it is now refused.
- **Breaking: `assert-rule` refuses a rule literal whose predicate is a variable.** Such a
  rule was indexed under `?var0`, which no arriving fact and no goal can spell, so it
  answered no backward goal at all and fired forward only when the concrete-predicate
  antecedent beside it arrived: two arrival orders, two answers, from a rule the engine
  reported as accepted. An `:inert` rule is exempt. *Migration:* assert the instantiated
  rules, one per predicate the metarule ranged over.


## 0.3.0 — 2026-08-04 — "a type on every refusal"

Correctness fixes across the durable index, the snapshot, the JTMS, the export dump
and the bounded prover, a sweep that gives every refusal a `:type`, the one wire
contract 0.2.0's own sweep left qualified, and the serialization both servers' storage
layer already assumed. Then a run of **inference and belief** work: two orders that
reached two answers, the two doors that disagreed about an inherited claim, and two
enumerations that grew with the vocabulary rather than with their own answer. Eight
entries are marked **Breaking** — they refuse input 0.2.0 accepted or change an
observable contract, which is why this is 0.3.0 and not 0.2.1; the rest are compatible.

- **Breaking: the daemon's refusal `:type` keywords are plain** — `:not-edn`,
  `:cross-origin`, `:bad-host`, `:body-too-large`, where the namespace serving them
  qualified each one. This finishes tree-wide what 0.2.0's own breaking entry claimed.
- **Breaking: both servers hold one request-body ceiling.** The cap and its
  `VAELII_MAX_BODY_BYTES` override (16 MiB) live in `vaelii.impl.guard`, which both
  read, so the browser answers **413** for an oversized form body where only the daemon
  did. A daemon read is also fully realized **inside** the write monitor — `wire-safe`'s
  walk is what realizes a lazy answer, so running it after the monitor released let a
  `:query` straddle a concurrent `:assert`.
- **Breaking: the browser serializes its writes.** Jetty serves the write routes on a
  thread pool, so two POSTs were two writers — where the storage layer is written on the
  promise that they are not. Interleave two and the WAL holds both frames while the RAM
  map holds one, so the running index and the one replayed on the next open disagree.
  The browser now takes one process-wide monitor around every content write, as the
  daemon always did; a concurrent write waits rather than racing.
- **Every `ex-info` the engine throws carries a `:type`.** Twenty refusals threw an
  untyped map, so a caller had to guess from which keys were present. Two forms that
  threw a raw Java exception now answer instead: `(genl ?x ?x)` / `(disjoint ?x ?x)`
  answer the question one variable in both positions asks.
- **Breaking: an `ist` form must have exactly three elements.** 0.2.0 read `assert` and
  `check` positionally, so `(ist Ctx S junk)` asserted with the extra silently ignored
  and `(ist Ctx)` raised a raw `IndexOutOfBoundsException`. Both refuse with `:shape`.
- **The durable index is gated on its key layout at open.** A log whose stamp does not
  match `kv/index-layout-version` is cleared, rebuilt from the records and restamped,
  `:recover?` notwithstanding; without the gate such a log replays cleanly and then
  misses every read whose key shape moved. **A 0.2.0 durable store carries no stamp, so
  its first open under 0.3.0 pays one automatic reindex**: O(records), logged at `:warn`,
  paid once. `docs/storage.md`.
- **Breaking: `open-kb` refuses a `:base` whose durable index is at an older key
  layout** (`:stale-index-layout`). The repair is a write and a base is mounted
  read-only, so the refusal names the one place the rebuild can happen: open that
  directory as a KB, then mount the fork over it.
- **Breaking: `(fork (fork base))` is refused** (`:stacked-fork`), which is what
  `docs/overlay.md` has always stated.
- **Breaking: `open-kb` refuses a `:recover?` setting it does not name.** `:auto` is the
  default, `true` an alias for it, `:warn` and `false` the rest; any other value read as
  the warn branch and handed back an empty TMS over a store that is not empty, which
  answers `[]` to everything. A stale derived index is dropped on open whatever
  `:recover?` says.
- **Breaking: `close!` releases a durable fork's own directory.** A fork's writable half
  takes the same exclusive lock as any durable KB, so without its own `:dir` it could
  never be handed to another process short of exiting the JVM. 0.2.0's docstring promised
  the opposite, so code that closed a fork in a `finally` and kept reading it worked and
  now does not.
- **A failed compaction takes its temporary files with it.** A rewrite that threw closed
  its handles and left `<log>.compact` behind, and the next compaction in the same
  session opened that temp and appended to it — its replay then put back records deleted
  in between. The cleanup is scoped to the pre-commit phase: past the marker the temps
  are the only complete copy.
- **A failed open gives back the directory lock with no handles still on it.**
  `open-kv-backend` and `open-token-log` replayed their logs outside any guard, so a torn
  frame propagated to a caller that answers a failed open by releasing the lock —
  leaving it released while this JVM still held an open handle.
- **A fork's merged `kv-entries` is realized under its monitor.** Both halves were lazy,
  so the seq handed back from inside the lock realized outside it. An export of a fork
  taken while anything wrote it projected two states at once.
- **The rete alpha registry is synchronized.** It is JVM-lifetime shared state reached
  from the store observer hooks, which fire on whichever thread is writing, and a
  `HashMap` racing its own rehash can leave a reader spinning on a probe loop that never
  terminates. Its check-then-put is one step too, so two callers cannot leave the loser's
  alpha permanently unmaintained.
- **`load-source` claims the catalog under one monitor.** The busy test, the
  already-loaded test and the registration were three separate reads, so two requests
  arriving together each passed all three and spawned a loader.
- **The browser reads untrusted EDN under `Throwable`, as the daemon does.** A deeply
  nested form overflows the reader's stack with a `StackOverflowError`, which an
  `Exception` catch lets escape — a 500 where an unreadable term is the ordinary answer.
- **The index snapshot's roots-fallback blob is validated like the sections beside it.**
  `roots-fallback.nippy` carries argument-root postings, which are primary index truth,
  and a missing or torn blob loaded as `[]` behind a warning while every argument-root
  read answered `#{}` out of a snapshot that opened clean. The meta records the blob's
  count and byte length, and the load thaws strictly.
- **The mapped index snapshot survives a JVM shutdown, and a failed save leaves the
  previous image intact.** The stamp is taken against the records before a byte moves,
  durability registrants close in phases, and every section lands in a `.tmp` until the
  swap. A failed *open* likewise gives back the handles it took.
- **An export dump carries every provenance stamp, and `export → import → export` is
  byte-stable.** The provenance walk covers justification handles as well as sentex ones,
  and import stores a justification's antecedents as a **vector**, the shape the engine's
  own write path stores.
- **The JTMS dedup index carries the identity of the TMS it mirrors.** A nested chain
  over a second KB — legal from an `:on-progress` callback, with overlapping handle
  spaces — could answer one KB's dedup question out of the other's supports. Keys coerce
  fixnum boxing to `Long` at the boundary, since the map compares with Java `equals`
  where the scan compares with `=`.
- **`prove-within` prepares its goal**, through the same `prepare-goal-for-read` every
  other read path takes, so a reifiable NAT or a merge-retired spelling is the same
  question under the bounded prover that it is under `ask`.
- **The rete forward matcher fans over predicate-`genl` sub-predicates at every arity**,
  as the reference `res/match-pattern` does. Fanning only for a two-element sentence gave
  the opt-in matcher a different belief set on any rule whose antecedent had another
  arity.
- **A firing refused at derive time comes back when its exception releases.**
  `place-conseq` does not place a firing whose `exceptWhen` exception already holds, and
  such a firing left no justification and nothing in `jtms/blocked` — so a settle pass
  could not see it and the conclusion stayed suppressed after the block lifted. The same
  knowledge in the other order concluded it. The refusal is recorded as `[rule handle,
  bindings]`, capped at 4096 entries per rule. `docs/exceptions.md`.
- **Five order-independence repairs.** `contradictions` names the same side of a clash
  whatever order the two arrived in; the two settle sweeps sharing one exposure-instance
  budget walk their moved region in content order; `query` with `{:proof? true
  :portfolio? true}` returns each answer once; `negation-nogoods` writes with a
  compare-and-set; and the node engine's inline join plans with the `:est-override`
  belonging to its registry leaf.
- **A forward rule fires on a claim argument-position preservation licenses**, so
  `sentexes-matching` and `ask` stop disagreeing about the same knowledge.
  `(argPreserving largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, which `ask` reached while the fixpoint fired only
  on the claims that were written — so the conclusion it never drew had no `why`, no
  retraction path and no way to be an antecedent. The join contributes the handles the
  inherited claim was read from, so retracting any of them withdraws the conclusion. One
  asymmetry is left: a justification confers the weakest class it rests on, so a
  `:monotonic` claim declared preserved by a `:default` declaration draws a `:default`
  conclusion. `docs/inherit.md`.
- **A head-existential rule carrying an aggregate mints a ground witness.**
  `skolem/frontier-vars` subtracts a post-join literal's output, so the Skolem NAT no
  longer takes a variable into its argument list.
- **An open `disjoint` goal is enumerated from the declarations rather than from the
  vocabulary.** A separation convicts two subtrees, so the answers are the subtypes of
  what a *visible* declaration names and the cost is the answer's own size; 0.2.0 asked
  `taxonomy/disjoint?` once per type, and once per **pair** with both arguments open. On
  4,000 types carrying one separation that is 15.4 ms to 0.13 ms with an argument bound —
  flat where it grew linearly — and at 1,000 types the two-variable goal goes from 2.5 s
  to 4 ms. `lein perf`'s `disjoint-enumeration` check is the claim.
- **A definitional clash is arbitrated from a context that can see both halves.** The
  checks are scoped to the context they are asked in, so a pair whose halves sit either
  side of a `genlCx` edge was answerable from exactly one of the two, and only when
  that half was the one the settle moved. `settle/clash-askers` runs the check from the
  candidate's own context and from the maximal common descendant of it and each context
  holding a sentex it could pair with; nothing is widened.
- **A pair per opposing sentex, not per opposing type.** One sentence stated in a general
  context and again in one that sees it is two sentexes, of possibly different strength,
  and a claim that denies it denies both — where the checks named one handle each, so the
  content-first of the two was weighed and the other left believed beside content that
  contradicts it.

## 0.2.0 — 2026-08-03 — "the public API boundary, drawn"

**Not a drop-in upgrade from 0.1.0.** Several of the changes below refuse input
0.1.0 accepted or change an observable contract — each such entry is marked
**Breaking** — which is why this is 0.2.0 and not 0.1.1. Entries between here and
the 0.1.0 header are in it, newest first.

- **The argument roots are scoped by predicate** (`[:argument-root pred pos
  term]`), so a materialising join reads one literal's postings rather than
  wading through every functor's at a shared slot. An `[:argument-slot pos
  term]` roster, reference-counted off those postings, keeps the
  predicate-agnostic reads answerable as a union over the predicates present.
  The packed long has no room for a fourth key part, so the dense roots route
  the family to their boxed fallback. `index-layout-version` is **2**: an index
  written by 0.1.0 reads as `:layout-changed` and is rebuilt on first open —
  no action needed, but a large durable store pays a reindex for it.
- **Breaking: every handle-taking fn refuses a non-handle** (`:bad-handle`) —
  the vector `assert` returns for a conjunctive rule included, which 0.1.0's
  `retract!` silently answered with `{:removed-sentexes 0}`. `nil` stays a
  question with an answer (`in?` false, `why` `{:stored? false}`,
  `add-provenance` a no-op), and `check-edit` reports what `edit!` throws. `why`
  also takes `{:max-depth n}` (default 256), marks a capped branch
  `{:truncated? true}` instead of overflowing, and refuses bad opts
  (`:unknown-option`).
- **`close!` releases a durable KB's directory** without waiting for JVM exit,
  and `import!` is `export!`'s inverse. An unclean close still releases the
  lock and registry; the first component failure is rethrown after.
- **An `argIsa` / `interArgIsa` / `argGenl` refusal names its convicting
  declaration in content order**, not in whichever order retrieval enumerated.
- **The five sweeps run in CI** — dense TMS, incremental matcher, node query
  engine, its tacticians, reference retrieval — each failing-set-identical
  with the default it replaces. Nothing ran them before.
- **Breaking: `assert` refuses a non-map `opts`** (`:unknown-option`) —
  `(assert kb s ctx :monotonic)` stored a defeasible sentence in 0.1.0.
  `check` already reported the same request; the two agree now.
- **Breaking: `open-kb` recovers by default** (`:recover? :auto`). The old
  `:warn` default handed back a KB that answered wrongly from a reopened
  store. The cost moves to construction — O(records) on a populated store —
  and `{:recover? false}` defers it. `:warn` and `false` remain.
- **The public surface is six namespaces**, where it was one: `vaelii.core`
  plus thin shims `vaelii.client`, `vaelii.starter`, `vaelii.web`,
  `vaelii.serve` and `vaelii.cli` over the `impl` namespaces they front. The
  boundary is now what the docs said it was.
- **Breaking: `vaelii.client`'s `assert` and `assert-rule` are spelled bare**,
  without the `!` 0.1.0 gave them. A `!` marks a fn that destroys stored
  knowledge and neither does — both are additive, and `retract!` is what takes
  one back — so the client now spells them exactly as `vaelii.core` does. A call
  site writing `c/assert!` or `c/assert-rule!` no longer resolves.
- **A clash names the sentex that states the membership**, not one that merely
  entails it, under either retrieval strategy.
- **An auto-compaction queued for a closed store is dropped**, so the next
  open no longer replays it as a crash-interrupted compaction.
- **Breaking: error `:type` keywords are plain across the tree**
  (`:unknown-source`, not `:vaelii.impl.catalog/unknown-source`), and
  `open-kb`'s backend refusals carry one. Swept in the same pass: the settle
  re-check queue no longer drops entries queued by a concurrent thread, and
  `foreign/register` refuses with `ex-info` rather than an elidable `{:pre}`.
- **Leiningen 2.10 is the minimum**: `:preserve-eval-meta` needs it, and 2.9
  ignores the key silently.
- **Breaking: `POST /op` requires `Content-Type: application/edn`.** The type
  is not CORS-simple, so a browser must preflight and the daemon answers no
  CORS headers — which closes cross-site request forgery against a loopback
  daemon. A client that sent no content-type is refused; add the header.
- **Breaking: a request body over 16 MiB is refused** (413) before it reaches
  the heap; `VAELII_MAX_BODY_BYTES` adjusts the cap.
- **Breaking: DNS rebinding is closed on both servers.** Every route requires
  a `Host` naming the interface the server was started on. A request with no
  `Host` still passes (a non-browser client carries no ambient browser
  context); a reverse proxy or local alias sets `VAELII_ALLOWED_HOSTS`.
- **`+with-foreign` names a coordinate that exists**
  (`com.vaelii/vaelii-foreign`); the bare id it carried resolved nothing.

## 0.1.0 — 2026-07-31 — "the first release"

The first release. What follows is the development log that produced it, newest
first; every entry below is in 0.1.0.

## 2026-07-30 — "declarations re-check what they change"

- A declaration re-checks the exceptions it moves: `(symmetric P)`,
  `(transitive P)`, `(inverse P Q)` and the `argPreserving` forms change what
  may be concluded with no fact arriving; `(functional P)` sweeps the extent
  when it lands.
- An equality restates a fact for each reader rather than once for the KB, and
  is itself a re-check trigger for `exceptWhen`, `unknown` and census reads.
- A change feed: the region a settle already computes is handed to a listener
  instead of discarded.
- English in — a sentence read into candidates a person still has to accept.
- A qualitative relation two contexts entail together fires a forward
  rule; a believed negative reaches the wiring a positive does; "some context"
  means the union of what the readers answer.
- Three readers of one question agree over a cyclic hierarchy, and settle
  repairs the context ranking after reconciling belief as well as before it.

## 2026-07-29 — "one entry point for backward chaining"

- One front door for backward chaining: the four paths measured, then
  consolidated to two chainers behind one entry point with one dial. A proof
  of an ephemeral answer reads the way `why` does.
- The goal frontier's order is a policy measured on time-to-first-answer,
  `:ground-first` by default; the goal-stack chainer drives one solution at a
  time and level 7 streams its search.
- Foreign formats arrive as a classpath plugin, so a reader ships and retires
  without touching the engine.
- A constraint declaration may name a second sentex it must not weigh, and a
  depth bound has no default because there is no defensible one.

## 2026-07-28 — "the gate: lint, suite, and scaling"

- `lein gate`: lint, the suite, and the scaling claims, measured and failed on
  rather than asserted; five checks added for costs that grow with what they
  must not.
- The columnar index is written once and mapped back; backend names read
  `<records>-<index>`, all seven.
- A literal's matches are remembered and retired on a clock; converging
  branches share one rule expansion; a third backward chainer whose state is
  a frontier.
- The naming invariants belong to the knowledge base, and the bulk door counts
  what it skips.

## 2026-07-27 — "aggregation over query results"

- Aggregation: a count is a query operator, and a firing that rests on one is
  maintained like any other — gated by a permutation test. A census counts
  distinctness through the representative the asking context elects.
- `argIsa` entails as well as constrains, behind a toggle, retroactively too.
- A definitional clash names a second sentex, making it a nogood, and the
  arbitrating sweep asks the taxonomy rather than a fixed functor set.
- The qualitative network lives on the knowledge base and warm-starts off its
  own previous answer; a violation ledger is a claim about one KB.
- The browser draws term shapes, composes English at three densities, and
  gained `lein browser`; OpenCyc loading went from 378s to 277s.

## 2026-07-26 — "reads scoped to the asking context"

- Contexts got a vantage: every taxonomy supporter records the context it
  asserts from, so disjointness, matching fan-out and settle all read only
  what the asking context can see.
- A firing names the `genl` edges it subsumed through — belief and strength
  run through them like any antecedent, checked against all 24 orderings.
- Records and index became two independent choices, plus an overlay backend:
  a private writable fork over a shared read-only base.
- A knowledge base is readable before it finishes loading, and the suite runs
  on every backend from one script.

## 2026-07-25 — "OpenCyc in the engine's own format"

- OpenCyc, read and re-expressed: every constant given back its role, 1.1M
  sentexes in the engine's own format, on the machine that reads it. Nothing
  of Cycorp's is redistributed.
- An export format no rename can break, with `xz`, an importer, and an oracle
  comparing two knowledge bases; a dump lands every record at its handle.
- Qualitative spatial and temporal reasoning: RCC-8 and three more spatial
  algebras, Allen intervals, durations and instants, behind one glue.
- One gap written in two units is one constraint: both spellings snap to the
  tolerance grid, and a unit given two conversion factors is its own base.
- A knowledge-base catalog with a browser that switches between KBs;
  `inherit` declared rather than assumed; definitional checks reach every
  term; `argGenl` constrains one level up.

## 2026-07-24 — "denser storage, measured first"

- The scale program opened with measurement first: the truth-maintenance
  wall, a posting-encoding bake-off on a real corpus, and a rule audit.
- Three dense representations, each measured: `:memory-dense` integer
  postings, the `:memory-columnar` int-token trie with CSR compaction (3.18x
  whole-index), and a bitmapped TMS behind a protocol.
- The disk side got dense too: positional record reads with a hot-record LRU,
  a positional frame codec, tokenized bodies over a durable dictionary — all
  behind a backend parity gate.
- Recursive forward chaining went O(n³) → O(n log n); a term roster
  enumerates vocabulary in O(terms).
- The web browser was hardened — escape by default, guard the parse, bind
  loopback, refuse cross-origin writes — and a pluggable LLM proposes edits
  and never applies them.

## 2026-07-23 — "performance fixes, and an operational surface"

- A performance review, its findings fixed: the disk log records operations
  rather than grown values (killing an O(N²) write amplification), settle
  keeps a coincidence set, re-checks narrow to the moved cone, region
  fixpoints became semi-naive worklists, compaction is copy-on-write.
- Symbolic equational reasoning: pure oriented rewriting with full
  Knuth-Bendix orientation, order-independent normalization, and
  non-confluence surfaced; `rewriteOf` extended over predicates and types.
- An operational surface: an EDN-over-HTTP daemon, a command-line driver, a
  thin client, and a browser that attaches to a daemon — with the public API
  closing every hole the browser tracked.
- Existential rule heads with deterministic skolemization; an occurs check;
  closures answered on demand; the record split into atomic and rule shapes
  with interned symbols; a bulk-load fast path.

## 2026-07-22 — "sound negation as failure"

- Negation as failure, at top level and in antecedents, with block, sweep and
  revive, and stratification to keep it sound.
- Resource-bounded anytime inference with qualitative cost tiers and a
  cost-ordered forward-chain join; `ask-within` normalizes its goal.
- Reification of non-atomic terms; structural subterm indexing,
  oracle-proven, then on by default.
- The storage seam: index logic onto one key-value protocol, an in-memory
  backend, then the on-disk substrate — files, lock, durability, record
  store, index store.
- The index benchmark harness, and a per-handle provenance side map.

## 2026-07-21 — "equality lands, and a sudoku solved"

- `exceptWhen` canonicalized into the record, blocking excepted conclusions
  with only reachable firings re-checked; its query reified the way a fact
  is.
- Equality landed: the closure, the `different` prover, a specification
  suite, and wiring into assert; stratification is checked on edge change.
- The engine split out of one namespace into five, and the knowledge base
  restructured into a layered tree loaded on start.
- `assumptionRules` with persistent solve and labeling contexts, proven on a
  sudoku.
- Retrieval got sharper: argument roots, multi-column narrowing, predicate
  subsumption, set-algebra retrieval, an opt-in incremental matcher.
- Truth-maintenance mutations are atomic; lint arrived.

## 2026-07-20 — "order independence, made an invariant"

- Canonical rule form — canonical variables with a varmap, literal order,
  comparison direction — so rules alike up to renaming share one handle.
- The eight-level lookup-to-query stack, lazy throughout, with a browser page
  showing which level answered.
- Order independence and locality pinned as invariants: region-local
  relabelling, belief-following closures, content-keyed tie-breaks.
- The answer-set layer wired to the edge-solver seam, with a labeling
  materialized as a context; the defeasible layer made sound, six bugs
  pinned as failing tests first; `exceptWhen` began as a failing suite.
- Everything but `core` moved under `vaelii.impl.*`; `!` reserved for
  irreversible operations; tests became net-neutral, and a second concurrent
  run fails fast rather than corrupting the first.

## 2026-07-19 — "the whole stack, day one"

The first day: a contextualized common-sense knowledge base with a trie
index, inference and truth maintenance.

- Sentexes — a sentence plus the context it holds in — stored as records
  behind protocols with nippy serialization; rules are sentexes too, with
  built-in transitivity for types and contexts.
- Forward chaining with dependency-directed retraction, and a backward
  chainer; a non-monotonic TMS with strengths, soft prioritized
  contradictions, and a solver seam.
- An inverted term index, directed rules, disjointness, well-formedness
  checks, and a pluggable prover query engine; structural connectives
  canonicalize into the record; evaluable arithmetic.
- A web browser over the whole thing, over a starter ontology with every
  term documented.
