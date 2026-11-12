# 35. Change over time

- **Covers:** choosing between a fluent and a time slice for a state that changes;
  stating a state that holds over some stretches of time as a fluent; the four sentences a
  narrative states; the inertia rules of `CxChange` and the direction each one runs; the
  ordering of instants a narrative writes down; and the per-instant functionality a
  fluent-valued function declares.
- **Not here:** the event types and their participant roles →
  [ch. 20](20-events.md); a reified function and its result type →
  [ch. 22](22-functions.md); the `unknown` literal inertia is built from →
  [ch. 32](32-negation.md); the context a theory lives in →
  [ch. 23](23-contexts.md); stating a fact in a time slice →
  [ch. 39](39-time.md#time-from-the-slice).
- **Assumes:** [ch. 20](20-events.md), [ch. 22](22-functions.md),
  [ch. 32](32-negation.md).

`CxChange.txt` is a simple event calculus over the vocabulary `time.txt` declares. It is a
middle theory: CxWell sees it, and its rules are KB sentences, read and edited as any
others are. A KB that states change in this vocabulary gets inertia from those rules. A
time slice ([ch. 39](39-time.md#time-from-the-slice)) is the other way to state a fact
that holds at some times and not at others, and the first section says which to use.

## A fluent or a time slice

**Practice.** When the source gives the time a fact holds over, state the fact in the time
slice for that time. When the source gives the events that start and end a state, and an
application asks whether the state holds at a moment between them, state the state as a
fluent and the events as a narrative. State one state one way.

**Example.** A status the source dates by month goes in two slices, as
[ch. 39](39-time.md#time-from-the-slice) states it. A cat that falls asleep at three and
wakes at five is a narrative: the source names the two events, and the question is
whether the cat sleeps at four.

**Why.**

- Logical: a slice states what holds during a time the source bounds. A narrative
  states what starts and ends a state, and inertia concludes that the state holds at every
  moment between its start and the next event that ends it.
- Engine: a slice carries nothing forward, so a read at a time no slice covers is
  unknown. Inertia carries a fluent forward to every moment the narrative orders after its
  start, until an event ordered between its start and that moment ends it.
- Engine: a narrative goes in a context under CxWell, which sees `CxChange` and its
  inertia rules.

**Why not the other ways.** A state stated both ways has two sources, and the two
disagree when one is revised (**state it once**, [ch. 4](04-economy.md)). A dated status
written as a narrative needs an event per boundary that the source does not name, and a
narrative written as slices loses the inertia an application asks for.

**Audit.** For each state in the change that holds at some times, name what the source
gives: a time, or the events. Confirm the change states the state in the matching form,
and in one form only.

*In development:* a narrative written into a time slice is in development. A slice does
not see `CxChange`, so its inertia rules do not run over the narrative
(`temporal_capability_test/a-narrative-in-a-time-slice-gets-the-event-calculus`, red).

## A state that changes is a fluent

**Practice.** When a state holds over some stretches of time and not others, and an
application asks when, and the source gives the events that start and end the state,
state the state as a fluent: a term built by a reifiable function whose result is
`fluent`. Ask whether it holds at a moment with `holdsAt`. When no
application asks when, a timeless default with an exception states the state without a
time ([ch. 30](30-exceptions.md)).

**Example.** A composed fluent function over temporaries:

```clojure composed
(reifiable_function TmpAsleepFn)
(unary_function TmpAsleepFn)
(result TmpAsleepFn fluent)
```

`(TmpAsleepFn TmpWhiskers)` is one constant: the state of that cat being asleep.

**Why.**

- Logical: a bare `(asleep TmpWhiskers)` states the cat asleep with no time, and its
  denial states the cat awake with no time. The two are a contradiction, though each was
  true at some moment. A fluent separates the state from the moments it holds at, so the
  KB holds both truthful snapshots.
- Engine: a fluent is a term, not a quoted sentence. The reified NAT is one constant per
  subject, so `holdsAt` is an ordinary binary predicate over two terms, and `initiates`
  and `terminates` index on the fluent constant like any argument.
- Engine: `functional` closes over a predicate's bare literals. A value carried as a
  fluent never becomes a bare literal, so two values that hold at different instants are
  never merged or reported as a clash.

**Why not the other ways.** `CxBiology.txt` states the timeless reading, "an animal is
awake unless it is known to be asleep", and it answers no question about when. Neither
reading derives the other. A time argument added to each state predicate makes every
state a new relation that needs its own persistence rules, where a fluent reuses the two
`holdsAt` rules for every state.

**Audit.** For each predicate in the change whose truth depends on the moment, name the
application question that asks when. With such a question, state the state as a fluent
or in time slices, as [the first section](#a-fluent-or-a-time-slice) chooses; without
one, leave it timeless.

## The narrative states four things

**Practice.** State a narrative with `happens`, `initiates`, `terminates` and
`initially`, and state each ordering of its moments that the source gives with
`instantBefore` or `instantEqual`. Register `:point` so that the orderings those entail
are read. Do not state `holdsAt`, `clipped` or `clippedBefore`.

**Example.** A composed narrative over temporaries:

```clojure composed
(happens TmpFallsAsleep TmpThree)
(initiates TmpFallsAsleep (TmpAsleepFn TmpWhiskers) TmpThree)
(happens TmpWakes TmpFive)
(terminates TmpWakes (TmpAsleepFn TmpWhiskers) TmpFive)
(instantBefore TmpThree TmpFour)
(instantBefore TmpFour TmpFive)
(instantBefore TmpFive TmpSix)
```

`(holdsAt (TmpAsleepFn TmpWhiskers) TmpFour)` is proved: an event started the fluent at
three and nothing ended it before four. The same goal at six is not, because the waking
at five clipped it.

**Why.**

- Logical: `initiates` says what an event starts and says nothing about whether the
  event occurred; `happens` says that. Both are needed, and the same event can start one
  fluent and end another. `initially` states a fluent that was the case before the
  narrative starts, with no event named as starting it. A fluent that is neither
  initially the case nor initiated holds nowhere.
- Engine: `instantBefore` is transitive, and a forward join over an antecedent on a
  transitive predicate reads the closure. A narrative writes the consecutive links, and
  `clipped` sees three-before-six from the three links between them. Inertia's
  `unknown` reads the same closure when `holdsAt` is asked, and with `:calendar`
  registered the clock orders `InstantFn` moments with no link stated.
- Engine: with `:point` registered, the join also reads an ordering the point network
  entails, and the answer carries the facts it rests on. A moment ordered before a second
  that is `instantEqual` to a third is ordered before the third, and `clipped` fires on
  that ordering
  (`temporal_capability_test/clipped-reads-an-order-the-point-prover-entails-once-it-is-registered`).
- Engine: `happens` types its second argument `time_point`, so a calendar day is refused
  by the argument check. `(InstantFn 2000 1 15 0 0 0)` is the moment that day begins.

**Why not the other ways.** A stated `(holdsAt F T)` is a fact that no terminating event
takes back, so a narrative that later learns of the waking still holds the cat asleep at
six. A stated `clipped` repeats what the forward rule derives from the events, stays
when the event is retracted, and is not what inertia reads.

**Audit.** `git grep -n 'holdsAt\|clipped' <file>` over the change's test-world returns
only queries. Each ordering of moments the source gives is stated, and no ordering the
source does not give.

*In development:* an ordering of two `InstantFn` moments that only the calendar clock
computes is in development as an antecedent of a forward rule. A clock answer rests on no
stored fact, so `clipped` does not fire on it
(`temporal_capability_test/a-forward-rule-fires-on-a-clock-answer-about-moments`, red).

## Inertia and its two directions

**Practice.** Leave the inertia rules as `CxChange` states them, and ask `holdsAt` with
`query` or `prove`, not `ask`.

**Example.** `CxChange.txt` derives `clipped` forward:

```clojure
(set/forwardRule
 (implies (and (happens ?event ?instant)
               (terminates ?event ?fluent ?instant)
               (instantBefore ?instant1 ?instant)
               (instantBefore ?instant ?instant2))
          (clipped ?instant1 ?fluent ?instant2)))
```

and proves `holdsAt` backward, with one literal of negation as failure on `clipped`
([ch. 32](32-negation.md)).

**Why.**

- Engine: an `unknown` antecedent is answered over the registry, which expands no rule. A
  backward `clipped` rule would be invisible to the `unknown` that consults it, and every
  fluent would persist without end. Forward, `clipped` is a stored fact the registry
  reads, bounded by the terminating events times the instant pairs the narrative states.
- Engine: a fluent holds at every moment between its start and its end, so a forward
  `holdsAt` would store one fact per moment per fluent. Backward, `holdsAt` is proved when
  asked. `ask` runs the registry, which expands no rule, so `ask` answers a `holdsAt` goal
  false.
- Logical: inertia is undercutting. A clipped fluent has no conclusion, so nothing is
  arbitrated. An event heard of later that terminates a fluent takes the answer back, and
  retracting that event gives it again.
- Stratification: `holdsAt` depends negatively on `clipped` and `clippedBefore`, and
  neither depends on `holdsAt`, so the assert-time check admits the theory as written.
- Naming the condition `clipped` keeps the inertia rule's negated antecedent one
  literal, and the forward rule stores each clipping as a fact with its own
  justification, so `why` shows which event ended the fluent.

**Why not the other ways.** A rule that concludes `holdsAt` from `clipped` in a context
that also states a rule concluding `clipped` from `holdsAt` is a cycle through negation
and is refused `:not-stratified`.

**Audit.** A change that adds a rule reading `holdsAt` concludes no predicate that
`clipped` or `clippedBefore` read.

## One value at an instant

**Practice.** When a fluent-valued function has at most one value for one subject at any
single instant, declare `(functional_at_instant F)`, and run
`functional-at-instant-violations` over a narrative that uses it.

**Why.**

- Engine: `functional` compares the bare literals one context sees. A fluent's value
  never becomes a bare literal, so two values that hold at three and at four are two
  truthful snapshots, and the mark reads neither. A value stated in a time slice is a bare
  literal, and the values of two sibling slices are never compared
  ([ch. 19](19-relation-properties.md#functional)).
- Engine: `functional-at-instant-violations` reads the declaration on demand and reports
  a moment at which two values of one subject hold: a merge for two symbols, a
  contradiction for two numbers. It reports and does not merge, because whether two
  fluents overlap at an instant follows from the clipping closure and is not known when a
  fluent is asserted.
- Engine: the check tries a fixed set of candidate moments: the `time_point` members
  `ask` answers in the context, and the later moment of each `instantBefore` pair it
  answers there. Two values that overlap only at a moment outside that set are not
  reported. The set is a limitation of the check, and the narrative states the moments
  its source names and no others.

**Why not the other ways.** `(functional F)` over a function whose values are fluents
closes over bare literals the fluents never become, so it reports nothing.

**Audit.** `all-functional-at-instant-violations` returns an empty map over the change's
test-world, or each entry has its fix.
