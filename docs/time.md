# Temporal reasoning — intervals, instants, and metric time

- **Covers:** Allen's thirteen interval relations and the three-relation point
  algebra, the two qualitative temporal algebras, their composition tables, the three
  calendar constructors that *name* an interval for them to relate, the clock that reads a
  calendar term's two bounding **instants** out of its fields, the UTC offsets and named
  zones that make a term absolute, and the shipped event calculus that says what holds
  when.
- **Not here:** the generic path-consistency engine both algebras run on →
  [qcn.md](qcn.md); how long an interval lasts, and how long two overlap →
  [duration.md](duration.md); the numeric gap between two instants →
  [stp.md](stp.md); how a calendar term keys a **context** rather than filling an argument
  → [context-nat.md](context-nat.md).
- **Assumes:** base relation, relation algebra, constraint network, fluent, inertia →
  [glossary.md](glossary.md); negation as failure, which inertia is stated with →
  [naf.md](naf.md).

The namespaces, most qualitative first:

| Namespace | Unit | Says | Doc |
|-----------|------|------|-----|
| `vaelii.impl.interval` | intervals | how two stretches of time are ordered and overlap | this page |
| `vaelii.impl.point` | instants | which of two moments came first | this page |
| `vaelii.impl.timepoint` | both | the six points of a temporal thing, and the order the terms fix | this page |
| `vaelii.impl.calendar` | both | where a calendar term begins and ends, and how two of them are ordered | this page |
| `vaelii.impl.fluent` | instants | a moment where two values of one fluent function hold | this page |
| `vaelii.impl.stp` | instants | how *far apart* two moments are, in real units | [stp.md](stp.md) |
| `vaelii.impl.duration` | intervals | how *long* one lasts, and how long two overlap | [duration.md](duration.md) |

The interval and point algebras are relation algebras over the constraint-network engine
in [qcn.md](qcn.md), which documents the reader, the entailment reading and the prover
shape for both. `startOf` / `endOf` relate an interval to its two bounding instants, which
is where the metric layers attach and where a calendar term's fields supply the instants.

Every prover here is **opt-in**; none of the vocabulary is. `instantBefore` and
`instantAfter` are declared **transitive** in `time.txt`, so a chain of strict orderings
composes off the taxonomy with no prover registered ([taxonomy.md](taxonomy.md)), and
`CxChange`'s `clipped` rule reads that closure. The point network adds an ordering through
an `instantEqual`, the three derived relations, and an unsatisfiable network reported as a
contradiction.

## The interval algebra (`vaelii.impl.interval`)

The unit is an **interval**: a meeting, a reign, a journey. Two intervals can meet, overlap
or nest, which a point calculus cannot say. The interval relations are declared `(arg …
temporal)` and the instant relations `(arg … time_point)`. `time_point` and
`time_interval` partition `uninterrupted_time`, which sits under `time` and so under
`temporal`, so `startOf` and `endOf` relate the two units by declaration. A temporal
relation between two predicates is refused rather than stored. The algebra reads order and
containment only; the calendar constructors below name intervals for it and compute no
relation of their own.

## The thirteen base relations

Jointly exhaustive and pairwise disjoint, so exactly one holds of any two intervals.
Writing an interval as `[start end]` with `start < end`, each is a claim about how the
four endpoints compare:

| Keyword | Predicate | Endpoints | Converse |
|---------|-----------|-----------|----------|
| `:before` | `before` | `a-end < b-start` | `:after` |
| `:meets` | `meets` | `a-end = b-start` | `:met-by` |
| `:overlaps` | `overlaps` | `a-start < b-start < a-end < b-end` | `:overlapped-by` |
| `:finished-by` | `finishedBy` | `a-start < b-start`, `a-end = b-end` | `:finishes` |
| `:contains` | `contains` | `a-start < b-start`, `a-end > b-end` | `:during` |
| `:starts` | `starts` | `a-start = b-start`, `a-end < b-end` | `:started-by` |
| `:equal` | `intervalEqual` | `a-start = b-start`, `a-end = b-end` | itself |
| `:started-by` | `startedBy` | `a-start = b-start`, `a-end > b-end` | `:starts` |
| `:during` | `during` | `a-start > b-start`, `a-end < b-end` | `:contains` |
| `:finishes` | `finishes` | `a-start > b-start`, `a-end = b-end` | `:finished-by` |
| `:overlapped-by` | `overlappedBy` | `b-start < a-start < b-end < a-end` | `:overlaps` |
| `:met-by` | `metBy` | `a-start = b-end` | `:meets` |
| `:after` | `after` | `a-start > b-end` | `:before` |

`:equal` is the algebra's identity and its own converse; the other twelve are six converse
pairs. `intervalEqual` is not spelled `equals`, because two distinct meetings can run
start to finish together without being one meeting: the claim is about extent in time and
must not reach the equality closure.

Seven **derived** predicates each name a disjunction:

| Predicate | Denotation |
|-----------|-----------|
| `precedes` | before, meets |
| `precededBy` | after, met-by |
| `subintervalOf` | during, starts, finishes, equal |
| `properSubintervalOf` | during, starts, finishes |
| `hasSubinterval` | contains, started-by, finished-by, equal |
| `sharesTimeWith` | the nine relations under which two intervals share time |
| `temporallyDisjoint` | before, after, meets, met-by |

`precedes` is the ordering that does not care whether the two touch, which is what people
usually mean by "before". `subintervalOf` contains `:equal`, so it holds of an interval
and itself, where `properSubintervalOf` does not. The last two are exact complements.

`subintervalOf` and `properSubintervalOf` take two time intervals, and the other eighteen
take any temporal thing. The network answers the two only over arguments that hold no
type disjoint from `time_interval`. So `(during S1 S2)` between two situations answers
`(hasSubinterval S2 S1)`, and answers neither `(subintervalOf S1 S2)` nor
`(properSubintervalOf S1 S2)`. An argument with no type is admitted.

All twenty are declared `instance_relation_predicate` in `resources/kb/upper/time.txt`,
each with its `comment` sentex, beside the six instant predicates and the metric ones.

## The composition table, and why it is checked

`allen-composition` is the 13×13 table: `[r1 r2]` gives the relations possible between A
and C given `r1`(A,B) and `r2`(B,C). `compose` lifts it to relation *sets* by union.

The cardinal directions compute composition from two independent axis projections; this
table is **transcribed**. A mistyped entry would not crash and would not return nothing:
it would be a wrong entailment, about a pair nobody asserted anything for, that nothing
downstream detects. So `interval_test` states the thirteen relations a second time as
their **endpoint inequalities** and derives the whole table from them. It lays out three
intervals every way three intervals can be laid out, over six points since a layout is a
weak ordering of six endpoints, records which outer relation each layout admits, and
asserts the derived table equals the transcribed one entry for entry.

The table is written out of thirteen named blocks rather than 169 loose sets. Composing two
relations determines some of the four endpoint comparisons between the outer intervals and
leaves the rest free, and each block is the set of relations agreeing on the determined
comparisons: `ends-first` is the five relations with `a-end < c-end`, `same-start` the
three with `a-start = c-start`, `concurrent` the nine that share any time. An entry
therefore names the comparison that survived, and reads back against the endpoint
definitions.

Three entries are the whole universe, each two intervals positioned against a third that
constrains neither against the other: A before B with B after C, its converse, and A
during B with B containing C.

## Reading the KB, and reading an answer back

`core/qualitative-network kb :allen ctx` reads every asserted interval relation visible
from a context into a network, and the registered `:allen` prover answers a goal by
entailment, in the shape [qcn.md](qcn.md) describes. So `(before A B)` and `(before B C)`
entail `(before A C)`, and `(during A B)` with `(during B C)` entails `(during A C)` and the
weaker `(subintervalOf A C)` and `(sharesTimeWith A C)` with it.

A derived predicate can be entailed where no base predicate is. `(meets A B)` and `(metBy
B D)` force A and D to end at the same moment and say nothing about where they start,
leaving `#{:finishes :finished-by :equal}`: no base predicate is entailed, and
`sharesTimeWith` is.

`core/possible-relations kb :allen ctx i1 i2` returns the base relations still possible
between two intervals, `#{}` when the network is inconsistent. A singleton is a determined
ordering, and several members are an open one. `vaelii.impl.scenario` picks one relation
per pair out of the tightened network, for any calculus ([scenario.md](scenario.md)).

## The point algebra (`vaelii.impl.point`)

A moment has no extent, so the only question about two instants is which came first. Three
base relations, jointly exhaustive and pairwise disjoint:

| Keyword | Predicate | Holds when | Converse |
|---------|-----------|-----------|----------|
| `:before` | `instantBefore` | `t(a) < t(b)` | `:after` |
| `:equal` | `instantEqual` | `t(a) = t(b)` | itself |
| `:after` | `instantAfter` | `t(a) > t(b)` | `:before` |

Three **derived** predicates are each the complement of one base relation, and over a
jointly exhaustive triple a complement is a negation:

| Predicate | Denotation | Reads as |
|-----------|-----------|----------|
| `instantNotAfter` | before, equal | at or before, the ≤ of time |
| `instantNotBefore` | after, equal | at or after, the ≥ |
| `instantNotEqual` | before, after | a different moment |

The vocabulary names every disjunction the algebra can express except the universe, which
is the absence of a claim. Every name carries the `instant` prefix because `before` and
`after` belong to the intervals, and `instantEqual` is not `equals` for the reason
`intervalEqual` is not.

The composition table has nine entries. Two of them are the universe: a before b with b
after c, and its converse, put a and c on the same side of b in either order. Every other
entry is a singleton, so a chain of strict orderings composes to a strict ordering however
long it is. `point_test` derives all nine a second time from numeric instants.

For three relations path consistency is **complete** as well as sound: the point algebra's
full disjunctive form is tractable, and a network of it that survives the pass has a
model. So an emptied constraint is unsatisfiability, and a cycle of strict `instantBefore`
facts is a reported contradiction.

`vaelii.impl.projection` holds the same three relations as `:lt` / `:eq` / `:gt` in its
own copy of the table, for the cardinal directions and the relative frame
([space.md](space.md), [defenses.md](defenses.md#the-point-algebras-table-is-copied-not-shared-with-vaeliiimplprojection)).

## The points of a temporal thing

Every temporal thing has six named points, each a structural `unreifiable_function`
application declared in `time.txt` and handled in `vaelii.impl.timepoint`:

| Term | Names |
|---|---|
| `(StartFn X)`, `(EndFn X)` | where X begins and ends |
| `(EarliestStartFn X)`, `(LatestStartFn X)` | the range the start falls in |
| `(EarliestEndFn X)`, `(LatestEndFn X)` | the range the end falls in |

The four bounds are for a start or an end known only to lie in a range — "he became
president sometime in 2008" — and for a thing with no sharp boundary, a period like the
Renaissance. A bound is a point of the thing, not a reading of what is known about it, so a
fact can relate one thing's bound to another thing's point: "the Baroque began within the
Renaissance's closing period" is `(EarliestEndFn Renaissance) ≤ (StartFn Baroque) ≤
(LatestEndFn Renaissance)`.

**Facts are instant relations over the points.** `(instantBefore (EndFn Trick1) (StartFn
Trick2))` is an ordinary fact the point network reads, with the point term as a node.
Nothing is minted and nothing is stored beyond what was stated. A point is a node only
when a fact or a goal mentions it, and a thing any of whose points is a node brings its
start and end in with it.

**The terms fix an order nobody states.** `timepoint/constraints-over` is the point
network's second reader, a function of the node set alone:

- one thing's points: `ES ≤ S ≤ LS`, `EE ≤ E ≤ LE`, `S < E`, `ES ≤ EE`, `LS ≤ LE`, over the
  ones present. `S < E` gives every thing extent.
- a moment's points: an `(InstantFn …)` term and a point term name a moment, and each of a
  moment's six points is the moment, so `(StartFn (InstantFn 2000 1 1 0 0 0))` is that
  instant and `(EndFn (StartFn X))` is `(StartFn X)`.
- calendar moments: an `(InstantFn …)` term, or a point of a calendar term, is placed by
  its fields. The ones present are sorted and each is ordered against the next, so
  `(EndFn (YearFn 2008))` falls before `(InstantFn 2009 1 20 12 0 0)` and `(EndFn (YearFn
  1999))` equals `(StartFn (YearFn 2000))`. A calendar term's bounds are sharp: its earliest
  and latest start are its start.

**The reader tells a moment from a thing by the spelling of the argument.** A symbol
argument is a thing and has extent, even when a `time_point` membership says the symbol is
a moment. So a moment named by a symbol has no points: stating that `(StartFn Noon)` and
`(EndFn Noon)` are `Noon` is the network's ordinary inconsistency, and
`inconsistency-culprits` names those two facts. A fact about a symbol moment relates the
moment itself ([defenses.md](defenses.md#a-symbol-moment-keeps-its-extent)).

`qcn-kb` also runs the reader over the nodes a **goal** names and no fact does, so a
question about a calendar moment nobody stated is ordered against the ones they did. The
constraints it adds carry no support, since the terms fix them and no retraction moves
them; an entailment through one rests on the stated facts it also used.

So a story's own order, dated clues and a period's uncertain boundaries are one network.
"While president in 2009, he received the Nobel Peace Prize" puts the prize inside both the
presidency and 2009, and a handful of such clues bound when the presidency began and ended
with no date for either stated. A clue that cannot fit closes a cycle, the point network's
ordinary `:qualitative-inconsistency` report, and `qcn-kb/inconsistency-culprits` names the
facts behind the pair that emptied.

**A thing against a moment.** `(includesInstant X t)` holds when t is at or after X's start
and before its end, the calendar terms' half-open convention, and its negation when t falls
before the start or at or after the end. `IncludesInstantProver` answers both off the point
network (`add-reasoner :includes-instant`) and answers a stored `includesInstant` fact as
well, so `argue` answers `:true`, `:false`, or `:unknown` for a moment inside a range a bound
leaves open: 1450 is inside a Renaissance that began by 1400 and unknown for one that began
sometime between 1400 and 1450. A believed `startOf` or `endOf` of X naming a node is a
second reading of that side, and the answer's support names the fact. A thing holds its
start, so a stated start alone places its own moment inside X with no end known. An open
argument ranges over what the network names: `?x`
over the things with a point in it or a stated bound visible from the context, `?t` over
its nodes. A calendar moment no fact names can
still fall inside a thing, so the prover reports an open argument as maximally unselective,
and a conjunction or a forward rule binds it first ([inference.md](inference.md),
"Conjunctive query planning").

**Allen relations follow.** The interval network's second narrowing reads, for every pair of
things with points in the point network, which of the four endpoint comparisons the network
still allows, and keeps the Allen relations whose endpoint signature fits
(`stp/endpoint-signature`). A pair's support is the four comparisons'. A thing is read
too when its stated `startOf` and `endOf` name two named moments that are nodes of the
network, as an interval between two moments a stated `instantBefore` chain orders does:
those nodes are readings of its start and end beside its own point terms, an endpoint
comparison is the intersection of the comparisons of every reading, and a pair's support
adds the stated endpoint facts. Each comparison is
read on its own, so the reading is sound but not sharp, as the metric one is. All of them
are read off one closed point network and one support-carrying pass
([defenses.md](defenses.md#the-point-narrowing-reads-one-closed-network-not-a-goal-per-comparison)).
An unsatisfiable component of the point network makes the interval network unsatisfiable
too, supported by that component's culprits. The intervals whose endpoints lie in the
component join one unsatisfiable Allen component, so the Allen firings over those intervals
are withdrawn and no Allen goal naming one of them is answered until the cycle is
retracted. `qualitative-network` over `:allen` names the clash as a `:point` source, with
the component's point pairs and those culprits. A cycle of instants that bounds no interval
leaves the Allen network satisfiable
([qcn.md](qcn.md#unsatisfiability-is-per-component)).

**An Allen fact orders the points.** The point network's stated-fact reader
(`point/allen-fact-constraints`) reads each believed Allen fact between two symbols visible
from the context. `(P A B)` narrows each of the four endpoint comparisons of A and B to the
union, over P's denotation, of the ordering `stp/endpoint-signature` gives it, and each
narrowed comparison rests on the fact. So `(before A B)` and `(instantBefore (StartFn B)
(StartFn C))` entail `(instantBefore (EndFn A) (StartFn C))`. The reading is exact for a
base relation and sound for any denotation. An Allen fact moves both networks
(`qkb/calculi-triggered-by` names both calculi), so it re-joins the rules on either. Allen
facts that contradict each other leave the point network over their endpoints unsatisfiable
too, and the violations ledger holds an entry for each network.

What it does not do:

- **A composed Allen relation does not reach the points.** The reader takes stored Allen
  facts and not the interval network, which reads the point network, so building one never
  builds the other. The point network composes the stated facts' endpoint comparisons
  itself; what the interval network composes beyond what four comparisons express stays
  on the interval side.
- **A calendar term is not an Allen node.** The narrowing reads things named by a symbol, so
  the relation between a thing and `(YearFn 2013)` is asked through their points.
- **No durations.** "After seven years" is metric, and point facts do not reach the
  `temporalDistance` network ([stp.md](stp.md)).
- **The culprits name one derivation.** They are the support of the pair that emptied, which
  contains every fact whose removal alone restores consistency but may name more.

## The time a thing occupies

`(TimeOfFn X)` names the time X occupies: the moment or the stretches of time over which X
exists, holds or happens. It is a `time`, and a `reifiable_function` with one value per
temporal thing. `timeOf` is its corresponding predicate, so `(timeOf X T)` and
`(TimeOfFn X)` name one time. A time is its own time: a rule in `time.txt` concludes
`(timeOf T T)` of every `time` T, so `(TimeOfFn T)` is T.

`time` divides into `uninterrupted_time`, a moment or one unbroken stretch, and
`intermittent_time`, a time with a gap. `temporal` divides the same way into
`uninterrupted` and `intermittent`.

## Naming an interval: the calendar constructors

Three constructors name the interval a calendar already picks out:

```clojure
(YearFn 2000)        ; the whole of 2000
(MonthFn 2000 1)     ; its January
(DayFn 2000 1 15)    ; the fifteenth of that January
```

Each takes one integer field per argument, coarsest first, and each is an
`unreifiable_function` declared `(result … time_interval)`, so a calendar term is an
argument of `before`, `during` or `subintervalOf` and **not** of `instantBefore`. The
constructors, the `DatetimeFn` ISO spelling of the same intervals, and their field-nesting
containment are [context-nat.md](context-nat.md)'s "The calendar dimension". That
containment is a computed `genlCx` edge, so a fact asserted for the year is visible from
the month, which is the one way this engine time-indexes a fact.

A calendar term's **endpoints** are computed rather than stated: `(YearFn 2000)` begins at
`(InstantFn 2000 1 1 0 0 0)` and ends at `(InstantFn 2001 1 1 0 0 0)`, and a prover answers
`startOf` / `endOf` from the fields with nothing stored ([The calendar
clock](#the-calendar-clock)). An ordinary interval such as `Breakfast` has no fields to
read, so its endpoints are the facts somebody states.

A **range** that no calendar unit names, such as January through June 2000, is
`(DatetimeRangeFn "2000-01" "2000-06")`: two reduced-precision ISO strings, beginning when
the first one's interval begins and ending when the second one's ends. Calendar units nest
or are disjoint, so a range is how two stretches that partially overlap are written as
terms. It is `unreifiable_function` like `DatetimeFn`, and two backward rules in `time.txt`
give it its endpoints from the two `DatetimeFn` intervals, so `startOf` and `endOf` answer
for a range wherever the calendar clock answers for a `DatetimeFn` term. `datetime/extent`
reads the two strings as the range's half-open bounds, so the calendar clock relates a
range to a calendar term or to another range, and a slice at a range is ordered against a
slice at either. A range whose start is not before its end has no extent, and neither
reads it.

The time **before** and the time **after** a moment W are `(IntervalBeforeFn W)` and
`(IntervalAfterFn W)`. Every interval includes its start and excludes its end, so
`(IntervalBeforeFn W)` is every moment before W and excludes W, and `(IntervalAfterFn W)`
is W and every moment after it. The two meet at W: they share no moment and leave no gap
between them, and W belongs to the after side alone. Each is an `unreifiable_function` from
a `time_point` to a `time_interval`, with `intervalBeforeOf` and `intervalAfterOf` as the
corresponding predicates, and each has one bound: a backward rule in `time.txt` gives
`(endOf (IntervalBeforeFn W) W)` and `(startOf (IntervalAfterFn W) W)` when W is a
`time_point`. The rule reads a believed `(time_point W)`, which a symbol stated to be a
`time_point` has and an `(InstantFn …)` term does not: `InstantFn`'s result type is
checked at assert time and is not answered by a query, so for an `InstantFn` moment the
bound is stated.

## A context at a time: `CxTimeFn` and the monad

A context has two parts: its **monad**, the world, story or theory it is a context of,
and its **time**. `(CxTimeFn CxStory (YearFn 2000))` is the year 2000 of `CxStory`.
`time.txt` declares it as [context-nat.md](context-nat.md) describes: `(result CxTimeFn
context)`, so an application written in a sentex's context slot reifies to a `cx/`
constant, and `(contextArgSubrelation CxTimeFn 2 subintervalOf)`, so the application at
the narrower time is a subcontext of the one at the wider time with the same monad.
`(contextArgSubrelation CxTimeFn 2 subtimeOf)` orders the slice at an `InstantFn` moment
below the slice at each interval holding the moment. A read of a slice nobody wrote into
sees what the slices it would be ordered below see
([context-nat.md](context-nat.md#write-and-read-are-symmetric)).
`(contextArgSubrelation CxTimeFn 1 genlMonad)` orders the other way round: with
`(genlMonad CxSubStory CxStory)` stated, the application along `CxSubStory` is a
subcontext of the one along `CxStory` at the same time. Two applications that differ in
both arguments are ordered by the product: `(CxTimeFn CxSubStory (MonthFn 2000 1))` is a
subcontext of `(CxTimeFn CxStory (YearFn 2000))`, and no slice between them need exist.

`time.txt` states `(result CxTimeFn time_slice_context)` and `(genl time_slice_context
context)`. A `cx/` mint writes no result type
([context-nat.md](context-nat.md#the-cx-namespace-carries-the-context-role)), so neither
`query` nor `ask` answers `(time_slice_context k)` of a slice `k` the engine minted.
`CxTimeFn`'s first argument is any `context`, so a slice can be sliced, and its second is a
`time`. A `monad_context` is a context that is not a slice, such as `CxStory` taken over
all of its time. No declaration types `CxTimeFn`'s first argument by it, and `(not (arg CxTimeFn 1
monad_context))` says so: a declared argument type entails membership, so that
declaration would make every context written in the first argument a `monad_context`.
`monad_context` is derived and never stated. A backward rule concludes it of a believed
`context` that no `CxTimeFn` `natFormula` names and that is not a believed
`time_slice_context`, both read by `unknown` ([naf.md](naf.md)). The `natFormula` conjunct
covers the slices the engine mints. A query answers `(monad_context CxRealWorld)`, since `core.txt` states `(context CxRealWorld)`.
`ask` expands no rule and does not answer it.
`CxMonadOfFn` and `CxTimeOfFn` take a context apart, with
`cxMonadOf` and `cxTimeOf` as their corresponding predicates: the monad of `(CxTimeFn
CxStory (YearFn 2000))` is `CxStory` and its time is `(YearFn 2000)`. `genlMonad` orders
two contexts by their monads alone, as `subintervalOf` orders times alone. A monad's
time is `Forever`, so the producer orders the slices along two monads by a `genlCx` path
between them as by a stated `genlMonad`
([context-nat.md](context-nat.md#the-bounded-r-oracle--no-proof-inside-the-relabel-loop)).
A stated `genlMonad` orders `CxTimeFn` applications, and not the two contexts themselves.

`Forever` is the time interval that contains every time, and the time of every
`monad_context`. Backward rules answer `(subintervalOf ?interval Forever)` for each
`time_interval`, `(includesInstant Forever ?instant)` for each `time_point`, and
`(cxTimeOf ?monad Forever)` for each `monad_context`. They are answered on demand rather
than stored, so the qualitative network and open enumerations over it list `Forever` only
when a stated fact relates something to it.

### A slice of a slice

`(CxTimeFn (CxTimeFn CxStory A) B)` is the slice of `CxStory` at the time `A` and `B`
have in common, `(TimeIntersectionFn A B)`. `subtimeOf` relates one time to another it
lies within, whatever the two kinds of time: an interval inside an interval, an instant
inside an interval, a piece of an intermittent time inside the whole. It is reflexive,
`(genl subtimeOf partOf)` and `(genl subintervalOf subtimeOf)` place it, and a backward
rule makes an instant a time includes a subtime of it. `TimeIntersectionFn` is the meet
over `subtimeOf`: an `unreifiable_function` from two times to a time, with
`timeIntersectionOf` as its corresponding predicate. Two times that share no time have no
intersection. Backward rules make the intersection a `subtimeOf` each argument when both
are believed times, and a `subintervalOf` each when both are believed `time_interval`s. A
query asks and gets that answer; the genlCx producer reads only a comparator, a stated
bound or a stored fact
([context-nat.md](context-nat.md#the-bounded-r-oracle--no-proof-inside-the-relabel-loop)),
so the slice at an intersection is not ordered under the slice at each argument.

Backward rules over `cxMonadOf` and `cxTimeOf` state the slice's two parts:

```clojure
(cxMonadOf ?monad ?monad)            ; a monad_context is its own monad
(cxMonadOf ?slice ?monad)            ; a slice has the monad of the context it slices
(cxTimeOf ?slice ?time)              ; a slice of a monad_context covers its own time
(cxTimeOf ?slice (TimeIntersectionFn ?outer ?time))
                                     ; a slice of a slice: the inner time and its own
```

Each rule reads the `natFormula` of the slice's `cx/` constant. A slice written with the
inner slice's `cx/` constant, `(CxTimeFn S B)` where `S` names `(CxTimeFn CxStory A)`,
answers through them: a depth-6 `query (cxTimeOf K ?t)` gives `(TimeIntersectionFn A B)`.
An inner slice spelled as a `CxTimeFn` application is a term inside the `natFormula`,
not a constant, and answers nothing. A further backward rule states that `(CxTimeFn
(CxTimeFn C A) B)` equals `(CxTimeFn C (TimeIntersectionFn A B))`; it concludes about two
applications, so it answers no goal ([nat.md](nat.md#a-rule-or-a-goal-that-names-an-open-application)),
and the two spellings reify to two `cx/` constants that no reader equates.

## Change over time: events, fluents, and inertia

`CxChange` is a simple event calculus, shipped as a **middle theory**: rules over vocabulary
`time.txt` declares, read and edited like the rest of the ontology. A theory the KB states
in its own representation is not a subsystem, so it is documented here.

A narrative states four things and nothing else:

```clojure
(happens CatFallsAsleep ThreeOClock)                      ; an event, at a moment
(initiates CatFallsAsleep (AsleepFn Whiskers) ThreeOClock) ; what it starts
(terminates CatWakes (AsleepFn Whiskers) FiveOClock)       ; what it stops
(initially (IndoorsFn Whiskers))                           ; what was already the case
```

Two questions follow, and neither is ever stated. `(clipped T1 F T2)` asks whether `F` was
ended between the two moments, and `(clippedBefore F T)` whether a fluent that held from
the outset was ended before `T`. `(holdsAt F T)` asks whether `F` is the case at `T`, and
is **inertia**, one literal of negation as failure:

```clojure
(set/backwardRule
  (implies (and (happens ?e ?t1) (initiates ?e ?f ?t1) (instantBefore ?t1 ?t2)
                (unknown (clipped ?t1 ?f ?t2)))
           (holdsAt ?f ?t2)))
```

A second `holdsAt` rule reads `initially`, with `(time_point ?t2)` as the generator that
binds the moment before the `unknown` runs. Its `unknown` joins `clippedBefore`'s
antecedents when the question is asked, because the moment asked about may be one no
stored fact names, and a forward `clippedBefore` derives nothing about such a moment
([defenses.md](defenses.md#inertia-joins-the-terminating-event-under-unknown-not-a-stored-clipped)). So the cat is asleep at four
because something put it to sleep at three and nothing woke it in between, and it is not
asleep at six because something did.

**A fluent is a term, not a sentence.** `(AsleepFn Whiskers)` is a reified NAT, one
constant per subject, the bounded shape [nat.md](nat.md) reserves `reifiable_function` for,
so `holdsAt` is an ordinary binary predicate over two terms
([defenses.md](defenses.md#a-fluent-is-a-term-not-a-quoted-sentence)).

### The two directions

`clipped` and `clippedBefore` chain **forward**. An `(unknown S)` antecedent is answered
over the registry, which **expands no rule** ([naf.md](naf.md)), so a `set/backwardRule`
`clipped` would be invisible to the antecedent that consults it, and every fluent would
persist for ever. Forward, it is a stored fact the registry reads, and its extent is
bounded by the terminating events times the instant pairs the narrative wrote down.

`holdsAt` is **backward**. A fluent holds at every moment between its start and its end, so
forward chaining would store one fact per moment per fluent. Ask it with `query` / `prove`
rather than `ask`: level 6 is the registry and expands no rule, and `holdsAt` is a rule
([levels.md](levels.md)).

### Stratified, and admitted as written

Simple event calculus is **predicate-stratified**: `holdsAt` depends negatively on
`clipped`, `happens`, `terminates` and `instantBefore`, and none of those depends on
`holdsAt`. The assert-time
check is predicate-level ([exceptions.md](exceptions.md), "Stratification"), so it admits
the theory as written, and a cycle through negation would have been refused.

Inertia is **undercutting**, like an `exceptWhen` and unlike a defeat: a clipped fluent has
no conclusion for the KB to arbitrate. So an event heard of *later* that terminates a
fluent takes the answer back, and retracting that event gives it again.

### When an input and an output exist

Four forward rules in `CxChange` order an event's participants against the event, each
concluding a point relation over `(StartFn X)` and `(EndFn X)`:

| Antecedent | Conclusion |
|---|---|
| `(output ?e ?x)` | `?x` starts at or after `?e` starts and at or before `?e` ends |
| `(destroyedInput ?e ?x)` | `?x` ends at or after `?e` starts and at or before `?e` ends |
| `(input ?e ?x)` | `?x` starts at or before `?e` ends |
| `(preservedInput ?e ?x)` | `?x` ends after `?e` ends |

With `:point` registered, a stated order that contradicts a conclusion is a
`:qualitative-inconsistency`, and with `:includes-instant` registered `argue` answers
whether a participant exists at a moment (`input_output_timing_test`).

### Functionality at an instant

`functional` enforces at most one value over a predicate's **bare** literals. A value
carried as a fluent under `initiates` never becomes a bare literal, so that closure never
sees it: a service that provides one namespace at three o'clock and another at four is two
truthful snapshots, not a clash. `(functional_at_instant F)` states that `F` has at most one
value for one subject at a **single** instant.
`vaelii.core/functional-at-instant-violations` reads it on demand and reports a moment where
two values of one subject hold: a merge for two symbols, a contradiction for two numbers, the
split `functional` makes. It reports rather than merges, because whether two fluents overlap
at an instant follows from the clipping closure and is not known when a fluent is asserted,
the shape `specified-violations` uses. The candidate moments are the `time_point` members
`ask` answers in the context and the later moment of each `instantBefore` pair it answers
there. An `(InstantFn …)` moment is no `time_point` member, and inertia holds a started
fluent only at a moment some `instantBefore` places after its start, so the second set
holds every such moment. See [equality.md](equality.md).

### What `clipped` can see

A forward join over an antecedent on a transitive predicate reads the closure as well as
the stored edges ([taxonomy.md](taxonomy.md), [inference.md](inference.md)). So a
narrative writes down the consecutive links and `clipped` sees the order they imply: three
o'clock before six follows from three-before-four, four-before-five and five-before-six,
and the derived `clipped` rests on those three edges.

An ordering **no stored edge carries** reaches `clipped` only through the point prover. The
walk crosses believed stored `instantBefore` edges and the spellings `genl` and `inverse`
make equivalent. With `:point` registered, the prover answers the join's `instantBefore`
antecedent from the network with support, so `clipped` fires through an `instantEqual`
(`temporal_capability_test/clipped-reads-an-order-the-point-prover-entails-once-it-is-registered`).
Without it, a pair the network narrowed to `:before` reaches no rule.

A calendar moment is the same case. A narrative may be written at computed instants:
`(happens RexSleeps (InstantFn 2000 1 15 15 0 0))` is an ordinary `happens`, `(InstantFn
…)` being a `time_point`. Its `instantBefore` edges are then written down exactly as an
afternoon of named moments needs them. The calendar clock supplies none, and both halves of
the theory stop at the same place: `clipped`'s forward join and inertia's backward one each
reach `instantBefore` with one end **open**, and the clock refuses an open end (["What the
clock does not reach"](#what-the-clock-does-not-reach)). The `initially` rule's `unknown`
reaches `instantBefore` with both ends bound, and the clock orders the terminating event
against the moment asked
(`calendar_test/an-initially-fluent-stops-at-an-event-the-clock-orders`). So a fluent is never reported as
persisting past an event the clock could have ordered and the narrative did not. Which end
is open depends on the conjunction's ranking ([inference.md](inference.md), "Where the
ranking is required"). State the links, and `clipped` fires over `InstantFn` moments,
`holdsAt` answers, and retracting a link takes both back.

An event happens at a **moment**, so a calendar term is not one: `(happens E (DayFn 2000 1
15))` is refused by the argument check, a day being a `time_interval` and `happens`' second
argument a `time_point`. `(happens E (InstantFn 2000 1 15 0 0 0))` is the moment that day
begins, and `(startOf (DayFn 2000 1 15) ?i)` names it.

### Two readings of one cat

`CxBiology` says an animal is awake unless it is known to be asleep, a default with an
exception and no notion of time. The same cat's afternoon written as events and fluents
answers *when*. Neither derives the other. `weightOf` and `heightOf` are `functional` in
`measure.txt` and say nothing about when; a fluent is what a time-varying weight would
take.

## Where the layers meet

`(startOf I P)` and `(endOf I P)` name an interval's two bounding instants. They let a
metric constraint stated over instants narrow an Allen relation between intervals, and let
`overlapDuration` compute a real overlap instead of a bound. [stp.md](stp.md) documents that
boundary, which runs one way: metric narrows qualitative.

The interval algebra declares the metric narrowing as its calculus's second reader
([qcn.md](qcn.md), "A network can have a second reader"), so a KB that writes down two
meetings' endpoints and the gap between them answers `(before Standup Review)` with no
interval relation stated, and a forward rule resting on that answer is withdrawn when any
fact behind it is retracted. The interval algebra takes a second narrowing from the point
network ([The points of a temporal thing](#the-points-of-a-temporal-thing)), and the point
network takes one from its own node terms; the other four calculi read stored facts alone.

### The calendar clock

For a **calendar** term the endpoints come from arithmetic: `(YearFn 2000)` says which year
it is, and a year has a first moment whatever anybody wrote down. `vaelii.impl.calendar` is
the prover that reads them, registered by name (`add-reasoner kb :calendar`) and answering
three families, and the negation of an instant ordering or an interval relation between two
terms it reads:

```clojure
(startOf (YearFn 2000) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)
(endOf   (YearFn 2000) ?i)      ; ?i = (InstantFn 2001 1 1 0 0 0)
(instantBefore (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 1 1 0 0 0))
(during (MonthFn 2000 3) (YearFn 2000))
```

**A moment is `(InstantFn Y M D h m s)` — six integer fields, always.** It is a
`time_point` where the calendar constructors are `time_interval`s, declared in `time.txt`
and `unreifiable_function` so the ordering reads its fields. Every moment has exactly one
term ([defenses.md](defenses.md#a-moment-is-six-integers-not-a-full-precision-datetimefn)).

**The convention is half-open, `[start, end)`.** A term's end is the *first* moment of
the next term at the same precision, so the end of 1999 and the start of 2000 are the same
term
([defenses.md](defenses.md#a-calendar-term-ends-where-the-next-one-starts)):

```clojure
(endOf   (YearFn 1999) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)
(startOf (YearFn 2000) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)   — the same term
```

So **consecutive calendar terms `meet`, they are not `before`.** Allen's `before` is strict
and requires a gap, and there is no gap between 1999 and 2000. `precedes` is the ordering
"1999 comes before 2000" means.

| Goal | Holds | Why |
|------|-------|-----|
| `(meets (YearFn 1999) (YearFn 2000))` | yes | 1999's end *is* 2000's start |
| `(precedes (YearFn 1999) (YearFn 2000))` | yes | `precedes` is before-or-meets |
| `(before (YearFn 1999) (YearFn 2000))` | **no** | no gap |
| `(before (YearFn 1999) (YearFn 2001))` | yes | 2000 is the gap |
| `(during (MonthFn 2000 3) (YearFn 2000))` | yes | March sits inside with room either side |
| `(starts (MonthFn 2000 1) (YearFn 2000))` | yes | same start, earlier end |
| `(finishes (MonthFn 2000 12) (YearFn 2000))` | yes | same end, later start |
| `(subintervalOf (MonthFn 2000 1) (YearFn 2000))` | yes | the disjunction over all three |
| `(intervalEqual (MonthFn 2000 1) (DatetimeFn "2000-01"))` | yes | one interval, two spellings |

**The relation is read from the fields, not through the endpoints.** Two calendar terms'
bounds fix which of the thirteen holds, so `calendar/relation` classifies it with four
comparisons of two six-field vectors, and builds no network. Between two calendar terms two
of the thirteen never come out: calendar terms are aligned, so two of them nest, coincide,
touch or are disjoint, and neither `overlaps` nor `overlappedBy` holds between a year, a
month and a day. A range is not aligned, so `overlaps` holds between January through June
and April through September.

**A named interval is read through its stated bounds.** For an interval relation with a
named interval on either side, the clock reads the believed `startOf` and `endOf` facts
visible in the goal's context, one `InstantFn` moment each (`stp/endpoints-with-support`),
and classifies the relation from those fields as it does for two terms. So an interval
stated to run from `(InstantFn 2000 1 1 0 0 0)` to `(InstantFn 2000 7 1 0 0 0)` `overlaps`
one stated to run from April to October, with no relation between the two stated. A named
interval with two stated starts, or with a start not before its end, has no extent here.
The clock answers the negation of an interval relation only between two terms.

**Answered, never stored.** No sentex, no handle, no justification, no minted constant: a
computed endpoint is not a belief, needs no retraction, and leaves no orphan for the NAT
sweep ([nat.md](nat.md)). The prover implements `Prover` and *not* `SupportingProver`.
Between two terms that is the claim that its answer reads nothing stored and no retraction
can invalidate it ([inference.md](inference.md), "What a computed answer rests on"). An
answer read through a named interval's stated bounds is a query-time answer, which the
forward join drops for its empty support (below). So `why` has no handle to
show; `query … {:proof? true}` shows a computed relation as a `:leaf`. Order independence
and locality hold for the same reason: there is no state to accumulate and nothing to
relabel.

**Cost, and what it claims.** `:lookup`: a bounded ground computation on at most six
integers per term, with no closure and no network. A pair of terms reads no index, and a
named interval adds one visible-match read per stated bound. `est-bindings` is 1: a
check has the one empty solution or none, and an endpoint is a function of its interval.
`completeness` is **50**. A KB may state `startOf` facts about a calendar term or interval
relations between two of them, and the calculus provers entail more from those than the
fields say, so the registry unions this prover in cheapest-first:

```clojure
(v/assert kb '(startOf (YearFn 2000) MillenniumMidnight) 'CxUniverse)
(v/ask kb '(startOf (YearFn 2000) ?i) 'CxUniverse)
;; => ({?i MillenniumMidnight} {?i (InstantFn 2000 1 1 0 0 0)})
```

The guard in the other direction is `provers/shadowing-channels`' **`:calendar`** channel:
a term's field structure is a source no fact-reading prover has, so a goal naming a
calendar term moves the interval or point calculus off the sole-prover path and into the
union, however complete it claims to be over the network it reads
([inference.md](inference.md), "Running alone takes two conditions"). `query-plan` shows it
as `:guarded-by #{:calendar}`.

**Scoping** is one cached, belief-following taxonomy read, taken only after the goal's own
structural test has passed: `(transitive instantBefore)` is `time.txt`'s declaration and
nothing else states it, so the clock answers exactly where the vocabulary its goals are
written in can be seen.

**It agrees with the context ordering.** [context-nat.md](context-nat.md) orders
time-keyed **contexts** by field nesting; the clock answers **sentences** about the terms.
`datetime/subinterval?` holds of `a` and `b` exactly when the Allen relation between them
is one of `subintervalOf`'s four, because `b`'s fields being a prefix of `a`'s is the same
claim as `a`'s bounds lying inside `b`'s. For a range the comparator tests that bound
containment directly. The context producer never asks the clock, the
clock never materializes a `genlCx` edge, and the two share the field reader in
`vaelii.impl.datetime`.

#### What the clock does not reach

- **Both terms must be bound.** An open variable on either side of an interval relation or
  an instant ordering would ask the clock to enumerate the calendar, so `applicable?`
  refuses it, as the point algebra answers nothing for a pair of open variables. The one
  variable it binds is a `startOf` / `endOf` **result**, which is a function of the
  interval. Enumerating the calendar terms a KB happens to mention instead would make the
  relation between two calendar terms a function of the store.
- **So a conjunction has to reach it ground, and the join planner does not know that.**
  `[(holiday ?m) (during ?m (YearFn 2000))]` answers nothing: the planner costs a literal
  by the stored facts it matches ([inference.md](inference.md), "Conjunctive query
  planning"), a KB storing no `during` facts counts zero, and the `during` literal is placed
  first, where its open argument answers nothing. Ask the relation of two terms already in
  hand. A transitive walk with both ends open answers nothing in the same way.
- **A calendar relation is not a constraint in the interval network.** The clock answers a
  goal about a *pair*; the terms it speaks of appear in no stored fact and so are nodes of
  no network. So a stated `(before Breakfast (MonthFn 2000 1))` does not compose with the
  clock's `(before (MonthFn 2000 1) (MonthFn 2000 3))` to answer `(before Breakfast
  (MonthFn 2000 3))`.
- **With the interval calculus registered, a relation between two named intervals is the
  calculus's alone.** The Allen calculus claims completeness over its literals, and the
  `:calendar` channel tests the goal's arguments for calendar terms, which a named interval
  is not. So with `:allen` beside `:calendar`, `(overlaps JanJun AprSep)` over two
  intervals with stated `InstantFn` bounds answers what the interval network entails, and
  that network reads a stated bound only when it is a named moment a point fact names.
- **A forward join cannot reach it.** A prover answers a forward antecedent only through
  `chain/solve-computed`, which drops an answer with **empty** support rather than building
  a justification that names the rule alone. The clock's support is empty by construction.
  So a calendar relation discharges a rule antecedent under `query` at a `:max-depth`, where
  the leaf is the registry, and derives nothing forward.
- **`totalDuration` does not follow.** The duration prover reads a stated length, and
  nothing gives it one off a calendar term's fields ([duration.md](duration.md)).
  `temporalDistance` does follow: the metric network places a calendar moment at an offset
  from an epoch node ([stp.md](stp.md#calendar-moments)).
- **Three edges of the calendar itself.** A term whose end would leave the four-digit year
  has no endpoints, so `(endOf (YearFn 9999) ?i)` answers nothing. A date the calendar does
  not have is stricter here than in the containment reader, which bounds a day at 31
  whatever the month: `(DayFn 2000 2 30)` nests inside February by fields and has no
  endpoints. Leap seconds are not represented: a minute is sixty seconds.

### Absolute time: UTC offsets and named zones

A `DatetimeFn` string with a time may end in a UTC offset, `Z` or `±hh:mm`, so
`(DatetimeFn "2000-01-15T13:00-07:00")` is the minute that begins at 20:00 UTC and is the
interval `(DatetimeFn "2000-01-16T01:30+05:30")` names. `(ZonedDatetimeFn
"2000-03-26T02:30" "Europe/London")` writes a wall-clock time in a named zone, whose second
argument is a `timezone`, an IANA identifier string. `datetime/utc-extent` reads either
form, and a range of two such strings, to its half-open UTC bounds, taking a named zone's
offset at each bound from the zone's `java.time` rules.

- **Two frames.** A term with no offset is wall-clock time in no zone. The calendar
  prover, the point network's calendar moments and the context ordering relate it only to
  another term in no zone, and an absolute term only to another absolute one
  (`datetime/paired-extents`). So whether `(DatetimeFn "1999-12-31T21-08:00")` lies inside
  `(DatetimeFn "2000-01-01")` is unknown, and the day is not read as UTC.
- **No endpoint terms.** An `InstantFn` moment is in no zone, so the clock answers no
  `startOf` or `endOf` for an absolute term. Its `StartFn` and `EndFn` are moments of the
  point network, ordered against the points of other absolute terms.
- **A term inside a skipped or repeated hour names no interval.** London's clocks skip
  01:30 on 26 March 2000 and repeat 01:30 on 29 October 2000, so neither `ZonedDatetimeFn`
  term relates to anything. Written with its offset as a `DatetimeFn` string, each
  occurrence of the repeated time is an interval. A term that starts or ends on a clock
  change spans the instants the zone's clock reads inside it: São Paulo's clocks went from
  00:00 to 01:00 on 4 November 2018, so that day is 23 hours from 03:00 UTC, and from 24:00
  back to 23:00 on 16 February 2019, so that day is 25 hours. An identifier the zone
  database does not hold names no interval either.
- Precision ends at the second, as for a term in no zone.
