# Reified-NAT contexts and structural genlCx

- **Covers:** how a ground application in a sentex's context slot reifies to a
  **context** — a `cx/` constant a sentex can be stored in and a `genlCx` node — when a read
  names that context through the application, how a declared argument
  ordering makes one such context a computed **spec** of another with nobody asserting the
  edge, and when the orphan sweep collects one.
- **Not here:** object-denoting NATs, which reify to a `nat/` constant that is a *term* and
  never a context → [nat.md](nat.md); the `genlCx` closure the produced edges feed →
  [contexts.md](contexts.md); the lexical conventions the roles rest on →
  [naming.md](naming.md).
- **Assumes:** sentex, context, `genlCx`, reification, the `natFormula` map →
  [glossary.md](glossary.md), [nat.md](nat.md), [contexts.md](contexts.md).

A context is normally a `Cx`-prefixed name — `CxWell`, `CxUniverse`. A **reified-NAT
context** is denoted instead by a function application: `(CxTimeFn CxMonad (DatetimeFn
"2000"))` is "the year 2000, along the `CxMonad` dimension". The value of it is that the
context hierarchy can then be **computed**: `(CxTimeFn CxMonad (DatetimeFn "2000-01"))` is a
*spec* (sub-)context of the year — January 2000 is inside 2000 — so a fact asserted in the
year is visible from the month, and **nobody asserts that `genlCx` edge**. This is the
shape Cyc gives a context keyed by a term (its `MtTimeWithGranularityDimFn` and kin).

An object NAT is the other case: a `nat/` constant is a term, refused as a context by the
naming and `genlCx` well-formedness checks ([nat.md](nat.md)). A context NAT carries a
distinct namespace so that refusal stays exact.

## The representation: reify the outer function, keep the argument structural

**Position picks the namespace.** A ground application in a sentex's **context slot**
reifies — like any NAT, *before* the index sees it — to an opaque **`cx/`**-namespaced
constant, whatever is declared about its head:

```clojure
(assert kb '(holiday NewYear) '(CxTimeFn CxMonad (DatetimeFn "2000")))
;; stored: the sentex's context slot is a bare symbol  cx/a…
;; map:    (natFormula cx/a… (CxTimeFn CxMonad (DatetimeFn "2000")))
```

The write reads no declaration (`nat/context-application?`), so the stored set is a
function of the offered set: a fact stored before, after or without any declaration about
`CxTimeFn` lands in the same `cx/` context. A non-ground slot `(CxTimeFn CxMonad ?x)` is
refused for `:shape`, since the sentence alone shows it names no context, and so is a
query context.

**A read names the context through the application only while CxUniverse believes
`(result CxTimeFn context)`** (`nat/context-function-believed?`): the declaration that
`CxTimeFn`'s applications are contexts. `context` is the `core.txt` type, and `result` is the
ordinary result declaration ([argtypes.md](argtypes.md)), so one declaration says what the
function denotes in both positions. Otherwise the read refuses the slot for `:shape`, and
the message names the missing `(result CxTimeFn context)`. A fact stored while CxUniverse
does not believe the declaration is inert: the fact sits in its `cx/` context, a read
naming that constant answers it, and a read naming the application refuses until
CxUniverse believes the declaration.

The check reads the declaration in CxUniverse, the context every reader reads the slot's
`natFormula` map in ([nat.md](nat.md#what-reification-does-not-cover)). A declaration
stated in CxUniverse admits the slot. A declaration stated in any other context admits
no read, since CxUniverse sees no other context
([contexts.md](contexts.md#cxuniverse-is-the-implicit-root)), and an `except` or a denial
at CxUniverse hides the declaration (`res/supporter-visible?`). An `except` in a
sub-context leaves the declaration believed at CxUniverse, and the slot reads. The check
does not read the context the slot names.

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
to look up, and the mint writes none: a `(result F context)` is not materialized on a `cx/`
constant. It is marked by its **namespace**: `naming/context?` is true for a `cx/` symbol
as it is for a `Cx…` name, and false for a `nat/` object constant. `term-role` follows, and
so — because they call `context?` — do the two checks that refuse an object NAT:

- `wff/genlCx-problems` admits a `cx/` constant as a `genlCx` argument;
- `naming/problems*` admits it as a sentex's context slot.

`nat-read/reified-nat-symbol?` recognizes both namespaces (everything that asks "is this an
opaque reified constant" — display, the `K → E` lookup — wants both); `reified-context-symbol?`
and `reified-object-symbol?` are the discriminants where the kind matters (the orphan
sweep below).

### One constant per expression per namespace

The `natFormula` map is 1:1 **within** a namespace. One expression written in a context
slot and in argument position maps twice: to a `cx/` constant `K′` from the slot, and to a
`nat/` constant `K` from the argument when its head is a `reifiable_function`
([nat.md](nat.md)). Every read from expression to constant takes the namespace it wants
(`nat-read/in-namespace?`, which splits the map by `naming/context?`): `dedup-constant`,
`rewrite-target`, the collision grouping behind `merge-colliding-nats!`, and the
applications a late `result` or correspondence declaration reaches. So the two constants
are no collision, and neither read resolves to the other's constant. A function that is no
`reifiable_function` leaves its argument-position application structural, as an
`unreifiable_function` does. A `rewriteOf` target resolves a context slot only when it is a
context by spelling, and a correspondence value never does: the value of a corresponding
predicate names an object.

**An argument-position application of a function declared `(result F context)` is a
context by content.** Its `nat/` constant `K` is minted with the result types every object
constant gets, so `(context K)` is stored and believed, and nothing refuses or contradicts
it: no stored disjointness separates `context` from what a `nat/` constant is, and a clash
read off the spelling is not placed. The constant is a term in a sentence, so the naming
check refuses it in a context slot and `wff/genlCx-problems` refuses it as a `genlCx`
argument. Nothing equates `K` with `K′`.

### Write and read are symmetric

The context slot is *not* on the sentence-reify walk — it is a separate argument to
`assert` — so `maybe-reify-context` reifies it explicitly: on the write path (`assert`,
minting) and on every read entry point (`ist-goal`, dedup-only, never minting, behind the
declaration check above). A query scoped to `(CxTimeFn …)` therefore resolves to the same
`cx/` constant the write minted and meets the facts stored there. A read mints no context
for a never-seen application either. When the producer would order the application below
contexts that exist (`context-nat/unminted-supers`), the read runs over a read copy of the
KB whose taxonomy holds those computed `genlCx` edges from the content-named constant
(`kb/with-context-edges`), so a slice nobody wrote into sees what its supers see. The read
copy is held among the resident values under the change clock (`context-nat/unwritten-read`),
so the reads between two writes build one. The first read after a write reads the contexts
the slice could be ordered below at one declared position, the one whose terms hold fewer
postings beside the function (`context-nat/above-candidates`). At a position no comparator
answers, it reads the contexts holding a term the position's sub-relations relate the
slice's term to. At a position a comparator answers, it reads the contexts holding a
calendar term containing the slice's time in each spelling (`datetime/containing-terms`), a
`DatetimeRangeFn` range, a symbol with a stated bound, or the other end of a stored fact. It
reads a calendar term by the term's own term-index key, which a store indexed at
`sx/*min-indexed-depth*` 2 or less holds. `lein perf`'s
`context-nat-read-unwritten-slice-after-write` and
`context-nat-read-unwritten-slice-beside-monads` measure the read. Otherwise the application
resolves to the `no-match` sentinel, and the read is scoped to nothing and answers empty.
`assert-inert`, which never mints, resolves the slot the same way and refuses one with no
stored constant (`:unminted-nat`). `check` reads the slot as the `cx/` constant `assert`
stores in, the stored one or the one the expression's content names, and mints none
(`nat/context-for-check`), so `check` reports what `assert` refuses for a compound slot as
for a symbol.

## The structural genlCx producer

`(contextArgSubrelation F pos R)` declares the ordering: two `F`-contexts identical except
at argument `pos` are ordered by the sub-relation `R` on that argument — the one whose
argument is `R`-**below** the other's is the spec, and `genlCx` the more general.

```clojure
(assert kb '(result CxTimeFn context) 'CxUniverse)
(assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
(assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) 'CxUniverse)  ; arg 2 = the datetime
```

The upper layer's `time.txt` states all three, so a KB that loads it reads `CxTimeFn`
contexts with no declaration of its own ([time.md](time.md#a-context-at-a-time-cxtimefn-and-the-monad)).
It also states `(contextArgSubrelation CxTimeFn 1 genlMonad)`, so two applications that
differ only in the first argument are ordered by `genlMonad` between the two contexts
there. Two contexts that differ at several declared positions are ordered by the
**product**: the one whose every differing argument is below the other's is the spec, and
no third context differing from each at one position takes part. `(CxTimeFn CxA (MonthFn
2000 1))` is a spec of `(CxTimeFn CxB (YearFn 2000))` when `CxA` is `genlMonad`-below
`CxB`, whether or not `(CxTimeFn CxA (YearFn 2000))` exists. Two contexts that differ at a
position no declaration names are not ordered.
A function of the user's own takes the same declarations, stated by the user.

`vaelii.impl.context-nat` reads the declarations and the context NATs of `F` from the
store, groups the contexts that agree on every undeclared argument, and for each ordered
pair whose differing arguments each stand in a declared `R` **materializes** the `genlCx`
edge. Its justification names the two `natFormula` maps, the declaration at each differing
position and the evidence there, one justification per choice of declaration.
The edge is a **justified** derived sentex, made the way `special/deduce-lift` makes a
decontextualized copy — `find-or-create-sentex`, `special/derived-sentex-added` (which
reaches the `genlCx` closure and posts the re-check triggers), then a JTMS justification
under the `contextArgSubrelation` informant. It is **never a premise anyone asserted**.

Justified is the whole point: the edge belief-follows for free. Retract a context (its
`natFormula` map), the declaration, or — for the stored-fact oracle below — the `R`-fact,
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
written before January existed (vaelii#56). The producer settles once it has built an
edge, and the settle's drain runs the sweeps for it as for an asserted or a concluded edge
([contexts.md](contexts.md#one-context-move)). The producer is idempotent, and a
declaration or a revival re-runs it over every pair of a function's contexts; a second
route to an edge already believed moves no label and is no move.

**Every arrival order converges within eight levels of slice nesting**, the producer's
round cap below. Five things can arrive last, and each has an arm
(`reconcile-arrival`). A declaration arriving after the contexts sweeps every pair of them;
a context arriving after a declaration is swept when it is minted, over the pairs it is in;
a **stated bound**, `(startOf X t)` or `(endOf X t)`, sweeps the pairs of each context
naming `X`; a **stated order**, `(instantBefore a b)` or its converse `(instantAfter b a)`,
pairs each context holding a time at or before `a` with each holding a time at or after
`b`, both ways (`reconcile-order`). The first set is `a`, each moment a chain of stated
orders places before it, and each time with a stated bound among those moments
(`bounded-along`), and the second is the same after `b`; every pair the fact can newly order
has one side in each. A comparison of a moment of the first set with `a` or with one of the
second, or of `b` with one of the second, is read off the two walks, and any other walks
from both of its ends at once (`graph/reaches?`); the path behind a comparison is read only
for a pair whose comparisons all hold (`lein perf`'s `context-nat-instant-order-append`).
An `(R a b)` **evidence fact** arriving after both sweeps the pairs ordered `a` below `b` in
the functions declared to order by `R` (`functions-ordered-by`), which is the arm a
comparator dimension never needs and a stored-fact one cannot do without. A `genlCx` edge
from `a` to `b` is the evidence of the closure oracle below: it sweeps the pairs whose
argument at a `genlMonad`-ordered position is at or below `a` on one side and at or above
`b` on the other.

An arrival is an assert or a belief move. A write entry point binds
`special/*producer-moves*`, which collects the `genlCx` edges its settles' context-move
drain reads, the datums a settle pass revives, and each derived sentex by its functor.
Once the write has settled, `context-nat/reconcile-moves` reads the edges and the
believed sentences whose functor the producer reads (`declared-heads`). An
edge a rule concludes is therefore swept as an asserted one is, and so is a declaration or
an evidence fact a rule concludes or a retraction revives. The settle after a `formula`
declaration releases or holds a rule (`nat-maintenance/reconcile-formula-positions`) is read
the same way. A computed edge that leaves belief has
its pair asked again, since a second route can hold it. A computed edge that enters belief
sweeps as an asserted one does: an edge from `k1` to `k2` orders a context whose argument
is `k1` below the one with `k2` there. Each level of nesting takes one more round, and the
producer reads the moves of at most eight settles per pass
(`nat-maintenance/max-producer-rounds`), and a write that also moves a `formula` position
runs a second pass. A pass that reaches the cap logs
`:vaelii.impl.nat-maintenance/producer-rounds`, and the slices nested below the last level
it ordered stay unordered. An `except` or a `defeat` a teardown removes gives its target
back with no relabel, so its target is read as an arrival.

A fact stored into a context that already exists creates no pair and sweeps nothing
(`lein perf`'s `context-nat-existing-context`), and a retraction that moves no context and
revives nothing reads no context NAT (`context-nat-retract-beside-slices`). A mint and an
edge read the contexts they can order through the term index. A mint reads, at the least
declared position no comparator orders, the contexts holding a term the closure or a stored
fact relates to its own (`context-nat-mint-beside-monads`), and then costs one oracle call
per differing position for each of them that agrees with it at every undeclared position;
a function whose every declared position a comparator orders has all of its contexts read.
An edge reads the contexts holding a term at or below its sub, and only when there are
some, those at or above its super (`context-nat-edge-beside-slices`). The maintenance hook sits beside the correspondence
reconcile at the tail of `assert` and behind the same presence check, `nat/any-reified-constants?`:
the in-memory `reifiable_function` marks, then one O(1) `natFormula` functor count, since a
context slot mints with no declaration. A KB that has minted nothing pays that count and
neither the hook nor the `any-context-subrelations?` index read.

### The bounded R oracle — no proof inside the relabel loop

The producer feeds the `genlCx` closure, which a relabel loop reads, so it may **not** start
a prover search to decide `R` ([naf.md](naf.md)). `R` is resolved only by a **bounded**
oracle:

- a registered **pure structural comparator**, keyed on the sub-relation — the datetime
  ones answer `subintervalOf` between two calendar terms or ranges, and `subtimeOf` from an
  `InstantFn` moment into an interval, by reading their shape. A comparator that answers is
  the position's only route;
- for `subintervalOf` and `subtimeOf`, the **stated bounds** of a named time: each
  believed `(startOf X t)` beside a believed `(endOf X u)`, each bound an `(InstantFn …)`
  moment or a named one, gives `X` an extent, which the containment test reads against the
  other argument's extent. Each stated start is also read alone, as an extent with no end,
  which holds its start under `subtimeOf` and no other time: an interval is half-open and
  nonempty, so it holds its start whatever its end. That reading rests on the start alone,
  so an end stated at or before the start leaves it standing, while `IncludesInstantProver`
  reads the two bounds as contradicting each other and answers neither polarity. A symbol
  with no stated bound is read as a named moment, the extent `[t t]`. Two `InstantFn` bounds
  compare by their fields. Any other pair of bounds compares by the believed stated orders
  along one path from the first to the second, each `instantAfter` fact read as its converse
  `instantBefore`: the path a breadth-first walk reaches first, each moment's facts read in
  content order (`instant-path`). The bound facts and the path's facts are the route's
  supporters, so retracting one withdraws the route;
- else the **`genlCx` closure**, for `genlMonad`. A monad's time is `Forever`, so a monad
  that sees another is `genlMonad`-below it. The oracle reads one path from the first
  argument up to the other, as the first argument sees it (`tax/reach-support`, which
  expands neighbours in name order), and the supporters of its edges justify the computed
  edge. The implicit edge to CxUniverse has no supporter, so no monad is `genlMonad`-below
  CxUniverse through it, and a read of a slice leaves CxUniverse out of the terms it looks
  up (`tax/context-routed-global`); and
- each **believed stored `(R a b)` fact**. A stated `(genlMonad A B)` orders the slices
  along `A` and `B` this way, and places neither monad under the other, so two stated
  `genlMonad` facts in a row order no slice along the first monad below one along the
  third.

Each route that holds gives the edge its own justification (`r-evidence`), so the arrival
order of a path and a stated fact decides none of them, and retracting one leaves the edge
believed under its handle. A comparator answer is a pure function of the two expressions,
already carried by the `natFormula` antecedents, so it contributes no extra supporter; a
stored fact contributes its own handle, so defeating it withdraws its route.

A backward rule answers a query and not the oracle. `time.txt`'s rules put
`(TimeIntersectionFn A B)` inside `A` and inside `B` by `subintervalOf`, so a query asks
and gets that answer, but the slice at the intersection is a spec of the slice at `A` only
once `(subintervalOf (TimeIntersectionFn A B) A)` is stored
([time.md](time.md#a-slice-of-a-slice)).

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

A `(DatetimeRangeFn FROM TO)` range and an `(InstantFn Y M D h m s)` moment are read by
extent. `datetime/extent` gives a range the half-open span from the start of `FROM`'s
interval to the end of `TO`'s, and none when that span is empty, and `subinterval?` tests
extent containment whenever either side is a range. `time.txt` also declares
`(contextArgSubrelation CxTimeFn 2 subtimeOf)`, whose comparator `instant-within?` places
a moment at or after an interval's start and before its end. It answers only for a moment,
so a pair of intervals has one comparator route. A time with a UTC offset or a
`ZonedDatetimeFn` zone is read by its UTC extent and ordered against absolute times only
([time.md](time.md#absolute-time-utc-offsets-and-named-zones)).

Three constructors and not six: a year, a month and a day are the granularities somebody
writes a holiday or a policy *for*, and each finer field is a spelling ISO already gives.
The three are declared in `resources/kb/upper/time.txt`, the upper file that owns time,
each with a `(result … time_interval)`, so a
calendar term is an interval and not an instant. That is also why it cannot stand in an
`instantBefore`, and why the moments it lies between are a separate term with a separate
constructor: see [What this does not cover](#what-this-does-not-cover).

## Orphan collection: a context is a place as well as a name

A context NAT is collected by the same sweep an object NAT is ([nat.md](nat.md), "Rename
and remove") — `remove-orphaned-nats!` on the `retract!` / `edit!` sweep, over the region the
teardown removed. The liveness question is what differs, because a `cx/` constant is
somewhere sentexes *are* as well as something sentences name. It is orphaned when all
three of these are empty:

- **its extent** — nothing is stored in its context slot;
- **its mentions** — no stored sentence names it as a term;
- **its edges** — no stored `genlCx` edge mentions it.

Stored, not believed, for the reason an object NAT's uses are counted that way: a defeated
fact still sits in the slot and a relabel can restore it.

**A computed edge is not one of the three.** The structural edges above are derived from
the two contexts' own `natFormula` maps, so reading one as a reference makes an ordered
pair immortal — each end held up by an edge read off the other. The discriminant is
**authorship**, as it is for an object NAT's materialized result types: the producer
deduces under the `contextArgSubrelation` informant and nothing else does, so an edge that
is no premise and whose every support carries that informant is the engine's own wiring.
An edge somebody **asserted** is a premise and holds its contexts up; one a rule concluded
carries that rule's informant and holds them up too.

The map is a context's whole bookkeeping — the mint writes no result types for one — so
the collection retracts the `natFormula` and stops there. The computed edges are derived,
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
count rather than a million record fetches. The sweep sits behind
`nat/any-reified-constants?`, so a KB that has minted no constant pays one `natFormula`
functor count per teardown and nothing else.

Nothing here can reach a context that is not a `cx/` constant. The three **query contexts**
([contexts.md](contexts.md)) are `Cx…` names for a way of reading, refused at every write
entry point and never minted, so no `natFormula` maps one and the candidate set cannot hold one —
a query holding one holds a symbol the sweep cannot name. An **agent or channel** context
([koinii.md](koinii.md)) is a `Cx…` name computed from an id, in the same position. In a
**fork** the sweep runs through the ordinary `retract!`, which tombstones an inherited
record rather than deleting it, so a context the fork empties is collected in the fork's
own contents and stands in the base ([overlay.md](overlay.md), base immutability).

### Re-minting after a sweep

Re-minting a swept expression gives back the constant the sweep collected. The mint's
dedup probe finds no `natFormula` map, so the mint writes one, and `constant-for` names the
constant by the content of the expression ([nat.md](nat.md#write-path)), so the `cx/`
symbol is the one it had before. The KB that results is indistinguishable from one the
sweep never touched: one constant per expression, the same computed edges, and the same
answers through the compound context at every read entry point.

The re-minted sentexes take new **handles**, allocated in assertion order, and belief never
tie-breaks on one. A caller holding the `cx/` symbol across a sweep holds a name for
nothing until the expression is used again.

## What this does not cover

- **One dimension ships.** The calendar — `DatetimeFn` / `YearFn` / `MonthFn` / `DayFn` /
  `DatetimeRangeFn` under `subintervalOf`, and `InstantFn` under `subtimeOf` — is the
  worked example; other dimensions are added by declaring a
  `(result F context)`, a `contextArgSubrelation`, and either registering a comparator or
  asserting the `R` facts.
- **A calendar term's endpoints are somebody else's job.** `(YearFn 2000)` is a
  `time_interval`, so it takes the interval relations and not `instantBefore`, which is a
  claim about moments. The moments it lies between are computed — half-open, so 2000 ends
  where 2001 begins — by the calendar clock, which answers `startOf` / `endOf` with an
  `(InstantFn Y M D h m s)` term and stores nothing ([time.md](time.md), "The calendar
  clock"). Nothing here reads the clock's answers, and the oracle reads stated bounds only:
the two mechanisms share the field reader in
  `vaelii.impl.datetime` and nothing else, and they agree exactly — `b`'s fields being a
  prefix of `a`'s is the same claim as `a`'s bounds lying inside `b`'s, so the `genlCx`
  edge this page produces and the `subintervalOf` the clock answers hold of the same pairs.
- **The closure oracle reads one path, and so does the walk over stated orders.** A second
  `genlCx` path between the same monads, or a second chain between two bounds, adds no
  route to a slice edge, so retracting the path the oracle read re-derives the edge under a
  new handle. Belief is the same in either arrival order within the round cap.

## Where it lives

- `vaelii.impl.nat` — `context-namespace`, the `cx/` mint path (`mint-nat!` takes the
  namespace and skips result-types for a context), `maybe-reify-context`,
  `context-application?` (what the context-slot shape check admits — a *ground*
  application, so the check does not depend on the naming policy or on a declaration),
  `context-function-believed?` and `readable-context-application?` (what a read admits),
  `context-for-check` (the context `check` reads a slot as, minting nothing),
  `in-namespace?` (the per-namespace split of the map), the `reified-context-symbol?` /
  `reified-object-symbol?` discriminants, and the orphan question's context arm —
  `orphan?`'s extent check, `computed-genlCx-edge?` (the authorship test), and
  `orphans-named-by`'s reading of a removed sentex's context slot.
- `vaelii.impl.naming` — `context?` (the `cx/` namespace).
- `vaelii.core` — the context-arg reify in `assert` and the read entry points (`ist-goal`,
  whose `read-context` reads an unwritten slice over a read copy), and the context-slot shape checks (`context-shape-problem` on a write,
  `read-context-shape-problem` on a read).
- `vaelii.impl.nat-maintenance` — the producer's call site on the assert path
  (`reconcile-assert`), its re-run over a teardown's belief moves on `retract!` / `edit!`
  (`reconcile-revivals!`) and at a deferred batch's close (`reconcile-moves!`), the merges
  a computed or revived edge licenses, and
  `collect-orphans!`, which collects both kinds of constant in one sweep.
- `vaelii.impl.wff` — the `contextArgSubrelation` well-formedness check.
- `vaelii.impl.context-nat` — the producer, the comparator registry, the stated-bounds
  route (`bounds-routes`), `reconcile-arrival` and `reconcile-moves`,
  `functions-ordered-by`, the evidence-arrived-last arm of the stored-fact oracle, and
  `unwritten-read`, the held read copy over the contexts an unwritten slice reads up from.
- `vaelii.impl.kb` — `with-context-edges`, the read copy whose detached taxonomy holds an
  unwritten slice's edges.
- `vaelii.impl.special` — `*producer-moves*`, the belief moves a write records for the
  producer.
- `vaelii.impl.datetime` — the calendar containment comparators, over the ISO strings, the
  three calendar constructors and ranges (`extent`) alike, the moment comparator
  `instant-within?`, and beside them the half-open `bounds` the calendar
  clock reads a term's two moments out of ([time.md](time.md)).
- `resources/kb/upper/core.txt` — `contextArgSubrelation`, and `result`'s comment on
  `(result F context)`, documented in the KB's own representation.
- `resources/kb/upper/time.txt` — `YearFn` / `MonthFn` / `DayFn`, each with its `result`.
