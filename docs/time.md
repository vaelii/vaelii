# Temporal reasoning — intervals, instants, and metric time

- **Covers:** Allen's thirteen interval relations and the three-relation point
  algebra, the two qualitative temporal algebras, their composition tables, the three
  calendar constructors that *name* an interval for them to relate, the clock that reads a
  calendar term's two bounding **instants** out of its fields, and the shipped event
  calculus that says what holds when.
- **Not here:** the generic path-consistency engine both algebras run on →
  [qcn.md](qcn.md); how long an interval lasts, and how long two overlap →
  [duration.md](duration.md); the numeric gap between two instants →
  [stp.md](stp.md); how a calendar term keys a **context** rather than filling an argument
  → [context-nat.md](context-nat.md).
- **Assumes:** base relation, relation algebra, constraint network, fluent, inertia →
  [glossary.md](glossary.md); negation as failure, which inertia is stated with →
  [naf.md](naf.md).

Time is the one subject in this tree with layers. Five namespaces, most qualitative first:

| Namespace | Unit | Says | Doc |
|-----------|------|------|-----|
| `vaelii.impl.interval` | intervals | how two stretches of time are ordered and overlap | this page |
| `vaelii.impl.point` | instants | which of two moments came first | this page |
| `vaelii.impl.calendar` | both | where a calendar term begins and ends, and how two of them are ordered | this page |
| `vaelii.impl.stp` | instants | how *far apart* two moments are, in real units | [stp.md](stp.md) |
| `vaelii.impl.duration` | intervals | how *long* one lasts, and how long two overlap | [duration.md](duration.md) |

The first two are relation algebras over the constraint-network engine in [qcn.md](qcn.md).
The engine, the reader, the entailment reading and the prover shape are all documented there
and are identical for both; this page is the two algebras. The bottom two put numbers on
them, and `startOf` / `endOf` are what let the numbers and the orderings be about the same
thing. The middle one is where those two endpoints stop having to be stated: a calendar
term carries its own, and the clock reads them off its fields.

Every prover here is **opt-in**; none of the vocabulary is. One thing about instants does
answer without a prover: `instantBefore` and `instantAfter` are declared **transitive** in
`CxTime`, so a chain of strict orderings composes off the taxonomy alone
([taxonomy.md](taxonomy.md)) — and a forward join reads it, which is what `CxChange`'s
inertia is built on. What the network adds over that is everything a walk over edges
cannot reach: an ordering through an `instantEqual`, the three derived relations, and an
unsatisfiable network reported as a contradiction.

## The interval algebra (`vaelii.impl.interval`)

The unit is an **interval**, not an instant. A meeting, a reign, a journey — something
with a start and an end — so two of them can meet, overlap or nest, which is exactly the
structure a point calculus throws away. The interval relations are declared `(arg …
temporal)` and the instant relations `(arg … time_point)`, `time_point` sitting
under `temporal` (through `uninterrupted_time`, which `time_point` and `time_interval`
partition, and `time`),
so `startOf` and `endOf` bridge the two by declaration as well as by meaning. A
temporal relation between two predicates is refused rather than stored. The algebra
itself knows nothing of clocks or calendars — only order and containment; the calendar
constructors below *name* intervals for it, and compute no relation of their own.

How *long* an interval is, and how long two of them overlap, is the quantitative half:
[duration.md](duration.md), which consumes the relation sets this page produces.

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
pairs. `intervalEqual` is deliberately not spelled `equals`: it is a claim about extent in
time, not about the identity of two terms, so it must not reach the equality closure —
two distinct meetings can run start to finish together without being one meeting.

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

`precedes` is the ordering that does not care whether the two touch — the thing people
usually mean by "before". `subintervalOf` contains `:equal`, so it holds of an interval
and itself, where `properSubintervalOf` does not. The last two are exact complements.

All twenty are declared `binary_predicate` in `resources/kb/upper/CxTime.txt`, beside the
six instant predicates and the metric ones, each with its own `comment` sentex — an **upper**
context rather than the vocabulary head, because they are *about* time and CxCore holds
only the grammar they are stated in.

## The composition table, and why it is checked

`allen-composition` is the canonical 13×13 table: `[r1 r2]` gives the relations possible
between A and C given `r1`(A,B) and `r2`(B,C). `compose` lifts it to relation *sets* by
union — a disjunction on either side admits every combination.

Unlike the cardinal directions, which compute composition from two independent axis
projections and so cannot disagree with themselves, this table is **transcribed**. A
mistyped entry would not crash and would not return nothing: it would be a wrong
entailment, reported with full confidence, about a pair nobody asserted anything for.
Nothing downstream could catch it.

So the table is written twice. The source holds the table; `interval_test` holds the
thirteen relations as their **endpoint inequalities** and derives the whole table from
them, by laying out three intervals every way three intervals can be laid out and
recording which outer relation each layout admits. Six points suffice: a layout is a weak
ordering of six endpoints, so it needs at most six distinct values. The test asserts the
derived table equals the transcribed one, entry for entry. The two representations share
nothing, so they can only agree by both being right — which is what makes a mistyped cell
a test failure rather than a wrong answer.

The table is written out of thirteen named blocks rather than 169 loose sets, because that
is what its entries are. Composing two relations pins some of the four endpoint
comparisons between the outer intervals and leaves the rest free; each block is the set of
relations agreeing on what got pinned. `ends-first` is the five relations with
`a-end < c-end`, `same-start` the three with `a-start = c-start`, `concurrent` the nine
that share any time at all. An entry therefore says *which comparison survived*, and can
be read back against the endpoint definitions instead of merely trusted.

Only three entries are the whole universe, and they are the same shape twice over: two
intervals positioned against a third that constrains neither against the other. A before B
with C after B says nothing — both sit on the far side of B, in either order — and neither
does A during B with B containing C, where A and C are both loose inside B.

## Reading the KB, and reading an answer back

`core/qualitative-network kb :allen ctx` reads every asserted interval relation visible
from a context into a network, and the registered `:allen` prover answers a goal by
entailment; both are exactly the shape [qcn.md](qcn.md) describes. So `(before A B)` and `(before B C)` entail `(before A C)`,
and `(during A B)` with `(during B C)` entails `(during A C)` and the weaker
`(subintervalOf A C)` and `(sharesTimeWith A C)` with it.

The derived predicates entail something no base predicate does in a network that pins
something without pinning a base relation. `(meets A B)` and `(metBy B D)` force A and D
to end at the same moment and say nothing about where they start, leaving
`#{:finishes :finished-by :equal}`: no base predicate is entailed, and `sharesTimeWith` is.

`core/possible-relations kb :allen ctx i1 i2` is the algebra read directly rather than
through a goal — the base relations still possible between two intervals, `#{}` when the
network is inconsistent. That is the call for a consumer that needs to know *how much* is
pinned down rather than whether one named relation is entailed: a singleton is a pinned
ordering, and several members are a genuinely open one.

For one concrete arrangement rather than the sets — a timeline to draw, an example to show —
`vaelii.impl.scenario` picks a single relation per pair out of the tightened network. It is
calculus-generic, so it runs over the point algebra below and the spatial ones alike. See
[scenario.md](scenario.md).

## The point algebra (`vaelii.impl.point`)

The other unit, and the smaller one. A moment has no extent, so the only question about two
instants is which came first — three base relations, jointly exhaustive and pairwise
disjoint:

| Keyword | Predicate | Holds when | Converse |
|---------|-----------|-----------|----------|
| `:before` | `instantBefore` | `t(a) < t(b)` | `:after` |
| `:equal` | `instantEqual` | `t(a) = t(b)` | itself |
| `:after` | `instantAfter` | `t(a) > t(b)` | `:before` |

Three **derived** predicates, each the complement of one base relation — and over a
jointly-exhaustive triple a complement *is* a negation, so the names are literal:

| Predicate | Denotation | Reads as |
|-----------|-----------|----------|
| `instantNotAfter` | before, equal | at or before, the ≤ of time |
| `instantNotBefore` | after, equal | at or after, the ≥ |
| `instantNotEqual` | before, after | a different moment |

With them the vocabulary names every disjunction the algebra can express bar the universe,
which is the absence of a claim and needs no name.

Every name carries the `instant` prefix because `before` and `after` already belong to the
intervals, and a moment ordered against a moment is a different claim from a stretch ordered
against a stretch. `instantEqual` is not `equals` for the reason `intervalEqual` is not: it
is a claim about time, not about the identity of two terms.

The composition table is nine entries, and only two of them lose information — a before b
with b after c puts both a and c on the far side of b, in either order, so nothing at all
follows. Everything else is a singleton, which is why a chain of strict orderings composes to
a strict ordering however long it is. `point_test` derives all nine a second time from
numeric instants.

For three relations path consistency is not merely sound but **complete**: the point
algebra's full disjunctive form is tractable, and a network of it that survives the pass has
a model. So an emptied constraint means genuine unsatisfiability — a cycle of strict
`instantBefore` facts is a reportable contradiction and not a suspicion.

**The same algebra appears twice in this tree.** `vaelii.impl.projection` builds a
nine-relation algebra out of two independent one-dimensional projections — the cardinal
directions and the relative frame are both that shape ([space.md](space.md)) — and each
projection is exactly these three relations under the spellings `:lt` / `:eq` / `:gt`. The
table is duplicated rather than shared: there the three relations are a position on an axis
and an implementation detail of the two nine-relation algebras built over them, here they
are an order in time with their own vocabulary. Nine identical entries are cheaper than the
coupling, and either copy is checkable against its own definitions.

## The points of a temporal thing

Every temporal thing has six named points, each a structural `unreifiable_function`
application declared in `CxTime` and handled in `vaelii.impl.timepoint`:

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
Trick2))` is an ordinary fact the point network reads; the network takes a point term as a
node as it takes a symbol. Nothing is minted and nothing is stored beyond what was stated. A
point is a node only when a fact or a goal mentions it, and a thing any of whose points is a
node brings its start and end in with it.

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
argument is a thing, and has extent, even when a `time_point` membership says the symbol is
a moment. A narrowing only narrows ([qcn.md](qcn.md#a-network-can-have-a-second-reader)):
a fact arriving never loosens a pair, and the delta join relies on that. A reader that
dropped `S < E` when a membership arrived would loosen the pair, and a conclusion drawn from
`S < E` would outlive the membership that withdrew it. An `arg` declaration cannot refuse
the case either. A declaration demands a type, and `time_point` is below `temporal`, so no
type admits every thing with extent and excludes a moment. So a moment named by a symbol
has no points. Stating that `(StartFn Noon)` and `(EndFn Noon)` are `Noon` is the
network's ordinary inconsistency, and `inconsistency-culprits` names those two facts. A
fact about a symbol moment relates the moment itself.

Because the reader needs no KB, `qcn-kb` also runs it over the nodes a **goal** names and no
fact does, so a question about a calendar moment nobody stated is ordered against the ones
they did. The constraints it adds carry no support — the terms fix them and no retraction
moves them — and an entailment through one still rests on the stated facts it also used.

So a story's own order, dated clues and a period's uncertain boundaries are one network.
"While president in 2009, he received the Nobel Peace Prize" puts the prize inside both the
presidency and 2009, and a handful of such clues bound when the presidency began and ended
with no date for either stated. A clue that cannot fit closes a cycle, which is the point
network's ordinary `:qualitative-inconsistency` report, and `qcn-kb/inconsistency-culprits`
names the facts behind the pair that emptied.

**A thing against a moment.** `(includesInstant X t)` holds when t is at or after X's start
and before its end — the calendar terms' half-open convention — and its negation when t falls
before the start or at or after the end. `IncludesInstantProver` answers both off the point
network (`add-reasoner :includes-instant`) and answers a stored `includesInstant` fact as
well, so `argue` answers `:true`, `:false`, or `:unknown` for a moment inside a range a bound
leaves open: 1450 is inside a Renaissance that began by 1400 and unknown for one that began
sometime between 1400 and 1450. An open argument ranges over what the network names: `?x`
over the things with a point in it, `?t` over its nodes. A calendar moment no fact names can
still fall inside a thing, so the prover reports an open argument as maximally unselective,
and a conjunction or a forward rule binds it first ([inference.md](inference.md), "The cost
model").

**Allen relations follow.** The interval network's second narrowing reads, for every pair of
things with points in the point network, which of the four endpoint comparisons the network
still allows, and keeps the Allen relations whose endpoint signature fits
(`stp/endpoint-signature`). A pair's support is the four comparisons'. The comparisons are
read independently of each other, so the reading is sound but not sharp, as the metric one
is. All of them
are read off one closed point network and one support-carrying pass, so an Allen read after
a write costs those two passes and a lookup per comparison. An
unsatisfiable point network makes the interval network unsatisfiable too, supported by the
point network's culprits, so a cycle of instants anywhere in a context withdraws the Allen
firings the points licensed there. `qualitative-network` over `:allen` names the clash as a
`:point` source, with the point pairs unsatisfiable as written and those culprits. With two or more things in the point network, no Allen
goal is answered there until the cycle is retracted.

What it does not do:

- **An Allen fact does not constrain the points.** The narrowing runs from points to
  intervals only; `(before A B)` stated outright says nothing about `(EndFn A)`.
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
`(TimeOfFn X)` name one time. A time is its own time: a rule in `CxTime` concludes
`(timeOf T T)` of every `time` T, so `(TimeOfFn T)` is T.

`time` divides into `uninterrupted_time`, a moment or one unbroken stretch, and
`intermittent_time`, a time with a gap. `temporal` divides the same way into
`uninterrupted` and `intermittent`.

## Naming an interval: the calendar constructors

Everything above relates intervals a KB has *names* for — `Breakfast`, `Reign2`. Three
constructors give a name to the interval a calendar already picks out:

```clojure
(YearFn 2000)        ; the whole of 2000
(MonthFn 2000 1)     ; its January
(DayFn 2000 1 15)    ; the fifteenth of that January
```

Each takes one integer field per argument, coarsest first, so **its arity is its
precision**, and each is an `unreifiable_function` — the application stays structural, so
the fields are readable inside the term rather than collapsed into an opaque constant. Each
declares `(result … temporal)`, which is what makes a calendar term an ordinary
argument of `before`, `during` or `subintervalOf` and **not** of `instantBefore`: a year is
a stretch, not a moment.

Their reason for existing is the containment: a reader can see from the fields alone that
January 2000 sits inside 2000 and that February sits inside neither. That is what
[context-nat.md](context-nat.md) turns into a computed `genlCx` edge, so a fact asserted
for the year is visible from the month with nobody stating the edge — the one way this
engine time-indexes a fact. `vaelii.impl.datetime` reads a calendar term and a
reduced-precision ISO string (`(DatetimeFn "2000-01")`) to the same field vector, so the
two spellings name the same intervals and order against each other.

A calendar term's **endpoints** are computed rather than stated: `(YearFn 2000)` begins at
`(InstantFn 2000 1 1 0 0 0)` and ends at `(InstantFn 2001 1 1 0 0 0)`, and a prover answers
`startOf` / `endOf` from the fields with nothing stored. That is what puts a calendar term
in the point algebra as well as the interval one, and it is [The calendar
clock](#the-calendar-clock) below. `Breakfast` is unchanged — an ordinary interval has no
fields to read, so its endpoints are still the facts somebody states.

## Change over time: events, fluents, and inertia

The algebras above order time. `CxChange` is what makes time *carry* anything: a simple
event calculus, shipped as a **middle theory** — four rules over vocabulary `CxTime`
declares, and data rather than code, so it is read and edited like the rest of the
ontology. It lives here rather than on a page of its own for that reason: a theory the KB
states in its own representation is not a subsystem.

A narrative states four things and nothing else:

```clojure
(happens CatFallsAsleep ThreeOClock)                      ; an event, at a moment
(initiates CatFallsAsleep (AsleepFn Whiskers) ThreeOClock) ; what it starts
(terminates CatWakes (AsleepFn Whiskers) FiveOClock)       ; what it stops
(initially (IndoorsFn Whiskers))                           ; what was already the case
```

Two questions follow, and neither is ever stated. `(clipped T1 F T2)` — was `F` ended
between the two moments? `(holdsAt F T)` — is `F` the case at `T`? The second is
**inertia**, and it is one line of negation as failure:

```clojure
(set/backwardRule
  (implies (and (happens ?e ?t1) (initiates ?e ?f ?t1) (instantBefore ?t1 ?t2)
                (unknown (clipped ?t1 ?f ?t2)))
           (holdsAt ?f ?t2)))
```

So the cat is asleep at four because something put it to sleep at three and nothing woke
it in between, and it is not asleep at six because something did.

**A fluent is a term, not a sentence.** `(AsleepFn Whiskers)` is a reified NAT — one
constant per subject, the bounded shape [nat.md](nat.md) reserves `reifiable_function` for
— which keeps `holdsAt` an ordinary binary predicate over two terms. A quoted sentence
would put a *mention* in argument position and have to be held opaque to identity
congruence to mean anything; the term does not.

### The two directions, and why each is what it is

`clipped` and `clippedBefore` are left to chain **forward**. That is not a preference: an
`(unknown S)` antecedent is answered over the registry, which **expands no rule**
([naf.md](naf.md)), so a `set/backwardRule` `clipped` would be invisible to the one
antecedent that exists to consult it — and every fluent would persist for ever, silently.
Forward, it is a stored fact the registry reads, and the extent it materializes is bounded
by the terminating events times the instant pairs the narrative actually wrote down.

`holdsAt` is **backward**. A fluent holds at every moment between its start and its end, so
forward chaining would store one fact per moment per fluent — an extent nothing bounds, for
a question anybody can ask directly. Ask it with `query` / `prove` rather than `ask`: level
6 is the registry and expands no rule, and `holdsAt` is a rule ([levels.md](levels.md)).

`clipped` is its own predicate rather than a conjunction inside the `unknown` for a third
reason: `unknown` takes **one literal**, and a conjunction under it would be read as
independent ground checks sharing no witness. Naming the condition keeps it one literal and
keeps its meaning.

### Stratified, and admitted as written

Simple event calculus is **predicate-stratified**: `holdsAt` depends negatively on
`clipped` and `clippedBefore`, and neither of those depends on `holdsAt` at all. The
assert-time check is predicate-level ([exceptions.md](exceptions.md), "Stratification"), so
it admits the theory as written — nothing had to be shaped around it, and a cycle through
negation would have been refused rather than quietly answered.

Inertia is **undercutting**, like an `exceptWhen` and unlike a defeat: a clipped fluent has
no conclusion for the KB to arbitrate. So an event heard of *later* that terminates a
fluent simply takes the answer back, and retracting that event gives it again — order
independence on a question with no stored answer.

### Functionality at an instant

`functional` enforces at most one value over a predicate's **bare** literals; a value carried
as a fluent under `initiates` never becomes a bare literal, so that closure never sees it — a
service that provides one namespace at three o'clock and another at four is two truthful
snapshots, not a clash. `(functional_at_instant F)` states the residual invariant the fluent
lane still owes: `F` has at most one value for one subject at a **single** instant.
`vaelii.core/functional-at-instant-violations` reads it on demand and reports a moment where
two values of one subject hold — a merge for two symbols, a contradiction for two numbers, the
split `functional` makes. It reports rather than merges, because whether two fluents overlap at
an instant follows from the clipping closure and is not known when a fluent is asserted, the
shape `specified-violations` uses. See [equality.md](equality.md).

### What `clipped` can see

`instantBefore` and `instantAfter` are declared **transitive** in `CxTime`, and a forward
join over an antecedent on a transitive predicate reads the closure as well as the stored
edges ([taxonomy.md](taxonomy.md), [inference.md](inference.md)). So a narrative writes
down the consecutive links and `clipped` sees the order they imply: three o'clock before
six follows from three-before-four, four-before-five and five-before-six, and the derived
`clipped` rests on those three edges — retract any of them and it goes.

What `clipped` still cannot see is an ordering **no stored edge carries**. The walk crosses
believed stored `instantBefore` edges (and the spellings `genl` and `inverse` make
equivalent); a bound the constraint network narrowed to `:before` without anybody stating
it is a prover answer over a network, and is not one of them. The calculus is opt-in
besides.

A calendar moment is the second case of that, and it is the same case. A narrative may be
written at computed instants — `(happens RexSleeps (InstantFn 2000 1 15 15 0 0))` is an
ordinary `happens`, `(InstantFn …)` being a `time_point` where a calendar term is not —
and it then needs its `instantBefore` edges written down exactly as an afternoon of named
moments does. The calendar clock supplies none of them, and **both** halves of the theory
stop at the same place, so neither half answers a question the other refuses:
`clipped`'s forward join and inertia's backward one each reach `instantBefore` with one
end **open** — "what happened before six", not "is three before six" — and an open end is
what the clock refuses (["What the clock does not reach"](#what-the-clock-does-not-reach)).
So a fluent is never reported as persisting past an event the clock could have ordered but
the narrative did not. State the links, and the whole theory reads them: `clipped` fires
over `InstantFn` moments, `holdsAt` answers, and retracting a link takes both back.

An event happens at a **moment**, so a calendar term is not one: `(happens E (DayFn 2000 1
15))` is refused by the argument check, a day being a `temporal` and `happens`'
second argument a `time_point`. `(happens E (InstantFn 2000 1 15 0 0 0))` is the moment
that day begins, and `(startOf (DayFn 2000 1 15) ?i)` is how to name it.

### Two readings of one cat, on purpose

`CxBiology` already says an animal is awake unless it is known to be asleep — a default
with an exception, and no notion of time at all. The same cat's afternoon written as events
and fluents answers *when*. Neither derives the other, and the pair is what the timeless
reading costs: `weightOf` and `heightOf` are `functional` precisely because nothing in them
says when ([quantity.md](quantity.md)), and a fluent is what that would take.

## Where the layers meet

`(startOf I P)` and `(endOf I P)` name an interval's two bounding instants. They are what
lets a metric constraint stated over instants narrow an Allen relation between intervals, and
what lets `overlapDuration` compute a real overlap instead of a bound. Both directions of
that boundary lives in [stp.md](stp.md), and it runs one way only: metric narrows qualitative.

The narrowing is **wired**, not offered: the interval algebra declares it as its calculus's
second reader ([qcn.md](qcn.md), "A network can have a second reader"), so a KB that writes
down two meetings' endpoints and the gap between them answers `(before Standup Review)` off
the measures with no interval relation stated. The entailment names the constraints, the
endpoint facts and the unit rows behind it, so a forward rule resting on it is withdrawn
when any of them is retracted — an ordinary firing, on a relation nobody stored. The
interval algebra takes a second narrowing from the point network, over a thing's
`StartFn` / `EndFn` points ([The points of a temporal thing](#the-points-of-a-temporal-thing)),
and the point network takes one from its own node terms; the other four calculi read
stored facts alone.

### The calendar clock

The machinery above runs on facts. For a **calendar** term it runs on arithmetic instead:
`(YearFn 2000)` says which year it is, and a year has a first moment whatever anybody
wrote down. `vaelii.impl.calendar` is the prover that reads them, registered by name like
every other reasoner here (`add-reasoner kb :calendar`) and answering three families:

```clojure
(startOf (YearFn 2000) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)
(endOf   (YearFn 2000) ?i)      ; ?i = (InstantFn 2001 1 1 0 0 0)
(instantBefore (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 1 1 0 0 0))
(during (MonthFn 2000 3) (YearFn 2000))
```

**A moment is `(InstantFn Y M D h m s)` — six integer fields, always.** It is a
`time_point` where the calendar constructors are `time_interval`s, declared in `CxTime`
beside them and `unreifiable_function` for their reason: the fields are what the ordering
reads. Six fields and not a reduced-precision spelling, because a term is identified by
its shape and one moment must have exactly **one** term — `"2000-01-01T00:00:00"` and
`"2000-1-1T0:0:0"` are two shapes for one moment where six integers are one. That is also
why it is not `DatetimeFn` at full precision: `(DatetimeFn "2000-01-01T00:00:00")` denotes
the one-*second* interval, the whole `DatetimeFn` / `YearFn` / `MonthFn` / `DayFn` family
naming stretches, and a stretch is not the moment that opens it.

**The convention is half-open, `[start, end)`.** A term's end is the *first* moment of
the next term at the same precision, so the end of 1999 and the start of 2000 are the same
term:

```clojure
(endOf   (YearFn 1999) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)
(startOf (YearFn 2000) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)   — the same term
```

The alternative — the end of 2000 being the *last representable* moment inside it — has to
name a smallest tick before it can name anything, so the end of a year would move when
somebody read the clock more finely, and the two terms above would be a second apart
instead of identical. Half-open needs no tick.

One thing follows from it, and read it before writing a rule over calendar terms:
**consecutive calendar terms `meet`, they are not `before`.** Allen's `before` is strict
and requires a gap, and there is no gap between 1999 and 2000.

| Goal | Holds | Why |
|------|-------|-----|
| `(meets (YearFn 1999) (YearFn 2000))` | yes | 1999's end *is* 2000's start |
| `(precedes (YearFn 1999) (YearFn 2000))` | yes | `precedes` is before-or-meets |
| `(before (YearFn 1999) (YearFn 2000))` | **no** | no gap; `precedes` is the ordering meant |
| `(before (YearFn 1999) (YearFn 2001))` | yes | 2000 is the gap |
| `(during (MonthFn 2000 3) (YearFn 2000))` | yes | March sits inside with room either side |
| `(starts (MonthFn 2000 1) (YearFn 2000))` | yes | same start, earlier end |
| `(finishes (MonthFn 2000 12) (YearFn 2000))` | yes | same end, later start |
| `(subintervalOf (MonthFn 2000 1) (YearFn 2000))` | yes | the disjunction over all three |
| `(intervalEqual (MonthFn 2000 1) (DatetimeFn "2000-01"))` | yes | one interval, two spellings |

`precedes` is what "1999 comes before 2000" means in this vocabulary, and the page already
says so where the derived relations are listed: it is the ordering that does not care
whether the two touch.

**The relation is read from the fields, not through the endpoints.** Two calendar terms'
bounds fix which of the thirteen holds, so the prover classifies it directly — four
comparisons of two six-field vectors, against a network build and a path-consistency pass.
The endpoints stay answerable because they are what joins this to the metric layer and to
the point algebra, not because the interval relation needs them. Two of the thirteen never
come out: the calendar's terms are aligned, so two of them nest, coincide, touch or are
disjoint, and neither `overlaps` nor `overlappedBy` can hold between a year, a month and a
day.

**Answered, never stored.** No sentex, no handle, no justification, no minted constant —
so a computed endpoint is not a belief, needs no retraction, and leaves no orphan for the
NAT sweep ([nat.md](nat.md)). The prover implements `Prover` and *not*
`SupportingProver`, which is the exact claim that its answer reads nothing stored and no
retraction can invalidate it ([inference.md](inference.md), "What a computed answer rests
on"). So `why` has no handle to show and is not the entry point: a computed relation is explained
by `query … {:proof? true}`, where it appears as a `:leaf`, and by this page — the term and
the convention are the whole of what it rests on. Order independence and locality are
free for the same reason: there is no state to accumulate and nothing to relabel.

**Cost, and what it claims.** `:lookup` — a bounded ground computation on at most six
integers per term, with no closure, no network and no index read. `est-bindings` is 1: a
check has the one empty solution or none, and an endpoint is a function of its interval.
`completeness` is **50** — it *augments*. A KB may state `startOf` facts about a calendar
term or interval relations between two of them, and the calculus provers entail more from
what it stated than the fields alone say, so the registry unions this in cheapest-first
rather than running it alone:

```clojure
(v/assert kb '(startOf (YearFn 2000) MillenniumMidnight) 'CxUniverse)
(v/ask kb '(startOf (YearFn 2000) ?i) 'CxUniverse)
;; => ({?i MillenniumMidnight} {?i (InstantFn 2000 1 1 0 0 0)})
```

The guard in the other direction is `provers/shadowing-channels`' fourth channel,
**`:calendar`**: a term's field structure is a source no fact-reading prover has, so a goal
naming a calendar term moves the interval or point calculus off the sole-prover path and
into the union, however complete it correctly claims to be over the network it reads
([inference.md](inference.md), "Running alone takes two conditions"). `query-plan` shows
it as `:guarded-by #{:calendar}`.

**Scoping** is one cached, belief-following taxonomy read, taken only after the goal's own
structural test has passed: `(transitive instantBefore)` is `CxTime`'s declaration and
nothing else states it, so the clock answers exactly where the vocabulary its goals are
written in can be seen.

**It agrees with the context ordering, and neither does the other's job.**
[context-nat.md](context-nat.md) orders time-keyed **contexts** by field nesting, so that a
fact stated for the year is visible from the month; the clock answers **sentences** about
the terms. The two readings coincide exactly — `datetime/subinterval?` holds of `a` and `b`
precisely when the Allen relation between them is one of `subintervalOf`'s four — because
`b`'s fields being a prefix of `a`'s is the same claim as `a`'s bounds lying inside `b`'s.
Nothing is computed twice: the context producer never asks the clock, the clock never
materializes a `genlCx` edge, and the one thing they share is the field reader in
`vaelii.impl.datetime`.

#### What the clock does not reach

- **Both terms must be bound.** An open variable on either side of an interval relation or
  an instant ordering asks the clock to enumerate the calendar, which is not an answer but
  a process that does not come back — so `applicable?` refuses it, exactly as the point
  algebra answers nothing for a pair of open variables. The one variable it binds is a
  `startOf` / `endOf` **result**, which is a function of the interval and so exactly one
  term. There is no set of stored calendar terms to enumerate instead, and enumerating the
  ones a KB happens to mention would make the relation between two calendar terms a
  function of the store, which it is not.
- **So a conjunction has to reach it ground, and the join planner does not know that.**
  `[(holiday ?m) (during ?m (YearFn 2000))]` answers nothing: the planner costs a literal
  by the stored facts it matches ([inference.md](inference.md), "The cost model"), a KB
  storing no `during` facts counts zero, and the `during` literal is therefore placed first
  — where its open argument answers nothing and the generator that would have bound it
  never runs. Ask the relation of two terms already in hand. The same shape and the same
  guidance hold for a transitive walk, which also answers nothing with both ends open.
- **A calendar relation is not a constraint in the interval network.** The clock answers a
  goal about a *pair*; it does not fold its relations into the Allen network the way the
  metric narrowing does, because the terms it speaks of appear in no stored fact and so are
  nodes of no network. So a stated `(before Breakfast (MonthFn 2000 1))` does not compose
  with the clock's `(before (MonthFn 2000 1) (MonthFn 2000 3))` to answer
  `(before Breakfast (MonthFn 2000 3))`.
- **A forward join cannot reach it**, and the mechanism says why: a prover answers a
  forward antecedent only through `chain/solve-computed`, which drops an answer with
  **empty** support rather than building a justification that names the rule alone while
  looking as though it named facts. The clock's support is empty by construction. So a
  calendar relation discharges a rule antecedent under `query` at a `:max-depth`, where the
  leaf is the registry, and derives nothing forward.
- **`temporalDistance` does not follow.** The metric prover's nodes are atomic terms
  (`stp/node-term?`), and a calendar term and an `InstantFn` moment are both structural, so
  neither is a node in a metric network — the gap between two calendar terms is not asked
  of the clock and is not answered by the numbers either. Nothing here converts a field
  vector to a magnitude ([stp.md](stp.md), [duration.md](duration.md)).
- **Three edges of the calendar itself.** A term whose end would leave the four-digit year
  has no endpoints, so `(endOf (YearFn 9999) ?i)` answers nothing — one moment past the
  last year ISO 8601 spells. A date the calendar does not have is stricter here than in the
  containment reader, which bounds a day at 31 whatever the month: `(DayFn 2000 2 30)`
  still nests inside February by fields and simply has no endpoints. And leap seconds are
  not represented — a minute is sixty seconds, which is what a proleptic Gregorian calendar
  of six fields can say.
