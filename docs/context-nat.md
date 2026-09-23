# Reified-NAT contexts and structural genlCx

- **Covers:** how a `Cx*Fn` function application reifies to a **context** — a `cx/`
  constant a sentex can be stored in and a `genlCx` node — how a declared argument
  ordering makes one such context a computed **spec** of another with nobody asserting the
  edge, and when the orphan sweep collects one.
- **Not here:** object-denoting NATs, which reify to a `nat/` constant that is a *term* and
  never a context → [nat.md](nat.md); the `genlCx` closure the produced edges feed →
  [contexts.md](contexts.md); the lexical conventions the roles rest on →
  [naming.md](naming.md).
- **Assumes:** sentex, context, `genlCx`, reification, the `termOfUnit` map →
  [glossary.md](glossary.md), [nat.md](nat.md), [contexts.md](contexts.md).

A context is normally a `Cx`-prefixed name — `CxTime`, `CxUniverse`. A **reified-NAT
context** is denoted instead by a function application: `(CxTimeFn CxMonad (DatetimeFn
"2000"))` is "the year 2000, along the `CxMonad` dimension". The value of it is that the
context hierarchy can then be **computed**: `(CxTimeFn CxMonad (DatetimeFn "2000-01"))` is a
*spec* (sub-)context of the year — January 2000 is inside 2000 — so a fact asserted in the
year is visible from the month, and **nobody asserts that `genlCx` edge**. This is the
shape Cyc gives a context keyed by a term (its `MtTimeWithGranularityDimFn` and kin).

Two records earlier established the opposite for *object* NATs: a `nat/` constant is a
term, refused as a context by the naming and `genlCx` well-formedness gates
([nat.md](nat.md)). Context NATs are the deliberate exception, carried by a distinct
namespace so the refusal stays exact.

## The representation: reify the outer function, keep the argument structural

A `Cx*Fn` is declared `(context_denoting_function CxTimeFn)`. A ground application reifies —
like any NAT, *before* the index sees it — but to an opaque **`cx/`**-namespaced constant
rather than a `nat/` one:

```clojure
(assert kb '(holiday NewYear) '(CxTimeFn CxMonad (DatetimeFn "2000")))
;; stored: the sentex's context slot is a bare symbol  cx/g42
;; map:    (termOfUnit cx/g42 (CxTimeFn CxMonad (DatetimeFn "2000")))
```

Only the **outer** function reifies. Its arguments are left alone by the mint, so an
`unreifiable_function` argument — `(DatetimeFn "2000")` — stays **structural inside the
stored expression**, exactly as `(QuantityFn 5 Meter)` does in an object NAT
([nat.md](nat.md), reifiable vs unreifiable). That is what lets the producer below read the
time term's shape to decide containment: reifying it away would collapse `"2000"` into an
opaque atom and lose the very structure the ordering needs.

Reifying the outer function is what keeps **"a context slot is a bare symbol"** true
everywhere — the trie index, `sentexes-in-context`, `matches-visible`, the `genlCx` graph
nodes all key on a symbol, and none of them changes. The alternative, a compound in the
context slot, would touch every one of those; the reified constant is one token by the time
they see it.

### The `cx/` namespace carries the context role

Role-reading is **spelling-only** and never consults belief ([naming.md](naming.md)), so a
reified context cannot be marked a context by a `(context K)` fact a `context?` would have
to look up. It is marked by its **namespace**: `naming/context?` is true for a `cx/` symbol
as it is for a `Cx…` name, and false for a `nat/` object constant. `term-role` follows, and
so — because they call `context?` — do the two gates that refuse an object NAT:

- `wff/genlCx-problems` admits a `cx/` constant as a `genlCx` argument;
- `naming/problems*` admits it as a sentex's context slot.

`nat/reified-nat-symbol?` recognizes both namespaces (everything that asks "is this an
opaque reified constant" — display, the `K → E` lookup — wants both); `reified-context-symbol?`
and `reified-object-symbol?` are the discriminants where the kind matters (the mint's
namespace choice, and the orphan sweep below).

### Write and read are symmetric

The context slot is *not* on the sentence-reify walk — it is a separate argument to
`assert` — so `maybe-reify-context` reifies it explicitly: on the write path (`assert`,
minting) and on every read entry point (`ist-goal`, dedup-only, never minting). A query scoped to
`(CxTimeFn …)` therefore resolves to the same `cx/` constant the write minted and meets the
facts stored there; a never-seen NAT context resolves to the `no-match` sentinel and the
read is scoped to nothing, answering empty rather than minting a context to ask about.

## The structural genlCx producer

`(contextArgSubrelation F pos R)` declares the ordering: two `F`-contexts identical except
at argument `pos` are ordered by the sub-relation `R` on that argument — the one whose
argument is `R`-**below** the other's is the spec, and `genlCx` the more general.

```clojure
(assert kb '(context_denoting_function CxTimeFn) 'CxUniverse)
(assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
(assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) 'CxUniverse)  ; arg 2 = the datetime
```

`vaelii.impl.context-nat` reads the declarations and the context NATs of `F` from the
store, groups the contexts into **siblings** (same expression but for argument `pos`), and
for each sibling pair whose `pos` arguments stand in `R` **materializes** the `genlCx` edge.
The edge is a **justified** derived sentex, made the way `special/deduce-lift` makes a
decontextualized copy — `find-or-create-sentex`, `special/derived-sentex-added` (which
reaches the `genlCx` closure and posts the re-check triggers), then a JTMS justification
under the `contextArgSubrelation` informant. It is **never a premise anyone asserted**.

Justified is the whole point: the edge belief-follows for free. Retract a context (its
`termOfUnit` map), the declaration, or — for the stored-fact oracle below — the `R`-fact,
and the ordinary JTMS relabel withdraws the edge and `sees?` flips. Nothing hunts it down,
and the taxonomy's depth/SCC potential and witness support are the derivation path's, not a
second mechanism ([contexts.md](contexts.md), the consumers).

**A computed edge widens what a merge can see, exactly as a stated one does.** A `genlCx`
edge is not only a visibility fact: it decides which sentexes an equality restates and
which pairs a `functional` / `functionalInArg` / `anti_symmetric` mark can reconcile
([equality.md](equality.md), the third and fourth arrival orders). Those three
reconcilers were written out at the assert entry point and at the rule-conclusion entry point and at no
third one, so a calendar edge posted the re-check triggers and ran no merge at all —
whether two fillers of one functional slot merged came down to whether the year's fact was
written before January existed (vaelii#56). The producer calls
`special/reconcile-context-edge`, the one entry point all three paths share, on the
**transition into belief**: after the justification, because the sweeps read the
belief-filtered closure and a line earlier the edge supports nothing, and only on the
transition, because this producer is idempotent and re-runs over every context of a
declared function — an edge owes exactly one sweep in its life, and a second route to one
already believed widens no ancestor set and owes none. What it merges is carried back out to
`assert`, which gives it the same follow-through an asserted edge's merges get: the
retired spellings reconciled, the twins chained, the violations reported, one settle.

**Every arrival order converges.** Three things can arrive last, and each has an arm. A
declaration arriving after the contexts sweeps them (`reconcile-function`); a context
arriving after a declaration is swept when it is stored into; and an `(R a b)` **evidence
fact** arriving after both sweeps the functions declared to order by `R`
(`functions-ordered-by`), which is the arm a comparator dimension never needs and a
stored-fact one cannot do without. The maintenance hook sits beside the correspondence
reconcile at the tail of `assert` and behind the same free in-memory reifiable gate — a
`context_denoting_function` is a reify-kind, so any KB with a context NAT to order already
passes it, and a KB that reifies nothing pays neither the hook nor the
`any-context-subrelations?` index read.

### The bounded R oracle — no proof inside the relabel loop

The producer feeds the `genlCx` closure, which a relabel loop reads, so it may **not** start
a prover search to decide `R` ([naf.md](naf.md)). `R` is resolved only by a **bounded**
oracle:

- a registered **pure structural comparator**, keyed on the sub-relation — the datetime one
  answers `subintervalOf` between two `DatetimeFn` terms by reading their shape; or
- a **believed stored `(R a b)` fact**, when no comparator applies.

A comparator answer is a pure function of the two expressions, already carried by the
`termOfUnit` antecedents, so it contributes no extra supporter; a stored fact contributes
its own handle, so defeating it withdraws the edge.

## The calendar dimension

`vaelii.impl.datetime` is the first shipped dimension, and it reads **two spellings of one
interval**.

`DatetimeFn` is an `unreifiable_function` taking a reduced-precision **ISO 8601** string:
`"2000"` the year, `"2000-01"` its January, `"2000-01-15"` a day, down through hour,
minute, second. `YearFn` / `MonthFn` / `DayFn` are the **calendar constructors** over the
same three coarsest fields, written as numbers rather than as a string — `(YearFn 2000)`,
`(MonthFn 2000 1)`, `(DayFn 2000 1 15)`. Each takes one field per argument, coarsest
first, so **its arity is its precision** and there is no string to parse or to mis-parse;
each is unreifiable for the reason `DatetimeFn` is, since the fields are exactly what the
ordering reads and a minted constant would hide them.

Containment is **field nesting** — a more-precise interval is inside a less-precise one it
shares every field with, whichever spelling each was written in:

```
(MonthFn 2000 1)  ⊆ (YearFn 2000)     ; January is inside the year
(DayFn 2000 1 15) ⊆ (MonthFn 2000 1)  ; the day is inside January
(MonthFn 2000 2)  ⊄ (MonthFn 2000 1)  ; siblings nest neither way
"2000-01"         ⊆ (YearFn 2000)     ; the two spellings order against each other
"2001"            ⊄ "2000"            ; different year
"2000"            ⊄ "2000-01"         ; the year is the COARSER interval, so it contains the month
```

`subinterval?` reads each term to a vector of integer fields and tests prefix equality —
pure, total (it declines any term that is neither), and bounded, so the producer may call
it inside the settle loop. **One field vector for both spellings** is the whole of the
bridge between them: the comparator never learns which constructor it was handed, so
`(MonthFn 2000 1)` and `(DatetimeFn "2000-01")` name the same interval, and a KB told the
year one way and the month the other still orders the two contexts. Fields are numeric, so
`"2000-1"`, `"2000-01"` and `(MonthFn 2000 1)` are one month.

Three constructors and not six: a year, a month and a day are the granularities somebody
writes a holiday or a policy *for*, and each finer field is a spelling ISO already gives.
The three are declared in `resources/kb/upper/CxTime.txt` — they are about time, and CxTime
is the upper context that owns time — each with a `(result … temporal)`, so a
calendar term is an interval and not an instant. That is also why it cannot stand in an
`instantBefore`, and why the moments it lies between are a separate term with a separate
constructor: see [What this does not cover](#what-this-does-not-cover).

## Orphan collection: a context is a place as well as a name

A context NAT is collected at the gate an object NAT is ([nat.md](nat.md), "Rename and
remove") — `remove-orphaned-nats!` on the `retract!` / `edit!` sweep, over the region the
teardown removed. The liveness question is what differs, because a `cx/` constant is
somewhere sentexes *are* as well as something sentences name. It is orphaned when all
three of these are empty:

- **its extent** — nothing is stored in its context slot;
- **its mentions** — no stored sentence names it as a term;
- **its edges** — no stored `genlCx` edge mentions it.

Stored, not believed, for the reason an object NAT's uses are counted that way: a defeated
fact still sits in the slot and a relabel can restore it.

**A computed edge is not one of the three.** The structural edges above are derived from
the two contexts' own `termOfUnit` maps, so reading one as a reference makes an ordered
pair immortal — each end held up by an edge read off the other. The discriminant is
**authorship**, as it is for an object NAT's materialized result types: the producer
deduces under the `contextArgSubrelation` informant and nothing else does, so an edge that
is no premise and whose every support carries that informant is the engine's own wiring.
An edge somebody **asserted** is a premise and holds its contexts up; one a rule concluded
carries that rule's informant and holds them up too.

The map is a context's whole bookkeeping — the mint writes no result types for one — so
the collection retracts the `termOfUnit` and stops there. The computed edges are derived,
so withdrawing that one premise takes them through the ordinary dependency-directed sweep,
and *their* removal is what puts the far end of each edge in the next round's candidate
set. A chain of ordered contexts collapses by the rule that collapsed the first, and an
object NAT standing inside a collected context's expression is the round after that.

An **empty** context goes even while a spec of it is live, and that is the reading and not
an edge case: a year holding nothing, named by nothing and wired only by what the producer
computed answers no reader, and stating a fact for it again re-mints it and recomputes the
edge down to its January.

### What triggers it, and what it costs

The sweep is the teardown's, so a removal is what makes a candidate. A context is
referenced **two** ways, and `nat/orphans-named-by` reads both off each removed sentex:
in its **sentence**, at any nesting, and as its own **context slot** — which is how the
last fact leaving an empty context is the removal that orphans it. Whichever of the three
sources goes last is the retraction that collects, and the end state is the same in every
order.

Each candidate costs one **`count-in-context`**, an O(1) secondary-root read on every
backend ([indexing.md](indexing.md)), and — only when that is zero — one inverted-term-index
read over the constant's own footprint. So a live context holding a million facts costs a
count rather than a million record fetches, and a KB that declares no
`context_denoting_function` mints no `cx/` constant and pays nothing: the sweep sits behind
the free in-memory reifiable gate, which a context function turns on.

Nothing here can reach a context that is not a `cx/` constant. The three **query contexts**
([contexts.md](contexts.md)) are `Cx…` names for a way of reading, refused at every write
entry point and never minted, so no `termOfUnit` maps one and the candidate set cannot hold one —
a query holding one holds a symbol the sweep cannot name. An **agent or channel** context
([koinii.md](koinii.md)) is a `Cx…` name computed from an id, in the same position. In a
**fork** the sweep runs through the ordinary `retract!`, which tombstones an inherited
record rather than deleting it, so a context the fork empties is collected in the fork's
view and stands in the base ([overlay.md](overlay.md), base immutability).

### Re-minting after a sweep

Re-minting a swept expression dedups to **one** constant, exactly as it does when nothing
was collected: the mint's dedup probe reads the `termOfUnit` map, the map is gone, so a
fresh constant is minted and every later occurrence of the expression finds that one. The
KB that results is indistinguishable from one the sweep never touched — one constant per
expression, the same computed edges, the same answers through the compound context at
every read entry point.

The `cx/` **symbol** and the **handle** are not part of that, and nothing may read them as
though they were. A reified constant is opaque and minted per KB, handles are allocated in
assertion order, and belief may never tie-break on one — so a caller holding the old symbol
across a sweep holds a name for nothing, and gets its answer back by naming the expression,
which is the only spelling the map is keyed by.

## What this does not cover

- **One dimension ships.** The calendar — `DatetimeFn` / `YearFn` / `MonthFn` / `DayFn`
  under `subintervalOf` — is the worked example; other dimensions are added by declaring a
  `context_denoting_function`, a `contextArgSubrelation`, and either registering a comparator
  or asserting the `R` facts.
- **A calendar term's endpoints are somebody else's job.** `(YearFn 2000)` is a
  `temporal`, so it takes the interval relations and not `instantBefore`, which is a
  claim about moments. The moments it lies between are computed — half-open, so 2000 ends
  where 2001 begins — by the calendar clock, which answers `startOf` / `endOf` with an
  `(InstantFn Y M D h m s)` term and stores nothing ([time.md](time.md), "The calendar
  clock"). Nothing here reads them: the two mechanisms share the field reader in
  `vaelii.impl.datetime` and nothing else, and they agree exactly — `b`'s fields being a
  prefix of `a`'s is the same claim as `a`'s bounds lying inside `b`'s, so the `genlCx`
  edge this page produces and the `subintervalOf` the clock answers hold of the same pairs.

## Where it lives

- `vaelii.impl.nat` — `context-namespace`, the `cx/` mint path (`mint-nat!` picks the
  namespace and skips result-types for a context), `maybe-reify-context`,
  `context-denoting-ground-nat?` (what the context-slot shape check admits — a *declared,
  ground* context function, so the check does not depend on the naming policy), the
  `reified-context-symbol?` / `reified-object-symbol?` discriminants, and the orphan
  question's context arm — `orphan?`'s extent gate, `computed-genlCx-edge?` (the
  authorship test), and `orphans-named-by`'s reading of a removed sentex's context slot.
- `vaelii.impl.naming` — `context?` (the `cx/` namespace).
- `vaelii.core` — the context-arg reify in `assert` and the read entry points (`ist-goal`),
  and the context-slot shape gate (`context-shape-problem`).
- `vaelii.impl.nat-maintenance` — the producer's call site on the assert path
  (`reconcile-assert`), its revival re-run on `retract!` / `edit!`
  (`reconcile-revivals!`), the merges a computed or revived edge licenses, and
  `collect-orphans!`, which collects both kinds of constant at one gate.
- `vaelii.impl.special` / `wff` — the `context_denoting_function` prop mark and the
  `contextArgSubrelation` well-formedness check.
- `vaelii.impl.context-nat` — the producer, the comparator registry, and
  `functions-ordered-by`, the evidence-arrived-last arm of the stored-fact oracle.
- `vaelii.impl.datetime` — the calendar containment comparator, over the ISO strings and
  the three calendar constructors alike, and beside it the half-open `bounds` the calendar
  clock reads a term's two moments out of ([time.md](time.md)).
- `resources/kb/CxCore.txt` — the two declarations documented in the KB's own representation.
- `resources/kb/upper/CxTime.txt` — `YearFn` / `MonthFn` / `DayFn`, each with its `result`.
