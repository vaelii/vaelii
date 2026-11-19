# 20. Events

- **Covers:** the argument position an event takes; the participant relations
  (`doneBy`, `performedBy`, `input`, `output`, …); keeping an event encoding and an n-ary
  relation for the same happening, and the rule that bridges them; abilities as kinds of
  event.
- **Not here:** fluents, `holdsAt` and inertia → [ch. 35](35-change-over-time.md);
  a rule whose consequent names a new event → [ch. 33](33-existentials.md); claims about a
  kind of event → [ch. 21](21-claims-about-kinds.md).
- **Assumes:** [ch. 4](04-economy.md) (**DRY**), [ch. 18](18-argument-types.md).

`core.txt` partitions `situation` into `fluent` and `happening`, and states `(intersection
event uninterrupted happening)`: an event is a happening with no gap in it. An event is a term of its own, so the KB can say who did
it, what went into it, what it left behind and when it happened, each as a separate
sentence.

## event arg1
*The Davidsonian convention: the event goes in argument 1*

**Practice.** Every relation of arity 2 or more that takes an event takes it as argument
1. The participant comes second.

**Example.** `abstract.txt` states each participant relation with the happening first:

```clojure
(arg doneBy 1 happening)
(arg doneBy 2 thing)   ;; an event's doer: a person, an animal, a machine or a process
(arg input 1 happening)
(arg output 1 happening)
(arg tangibleOutput 2 tangible)
```

The comment above `input` and `output` reads "Each relation takes the happening first."
The rule that concludes an artifact from its making joins two of them on argument 1:

```clojure
(set/forwardRule (implies (and (tangibleOutput ?e ?x) (performedBy ?e ?d)) (made ?x)))
```

**Why.**

- *Logical.* Each participant relation is a statement about the event, and the event is
  its subject. With the subject in one place, `(output ?e ?x)` and `(doneBy ?e ?d)` read
  the same way, and a reader predicts the position of the event in a relation they have
  not opened.
- *Engine.* The participant relations sit in one predicate hierarchy: `doneBy`,
  `thingPerceived`, `input` and `output` are each under `actor`, and `performedBy` is under
  `doneBy`. A predicate `genl` makes each child tuple a parent tuple with the arguments in
  the same order, so the hierarchy holds together only when every member puts the event
  in the same position. Mixing the positions would need `genlInverse` edges for the
  relations written the other way round.
- *Maintenance.* A rule over several participant relations joins on the event variable,
  and with one convention every such rule is written the same way. A relation added with
  the event second needs every rule that touches it written differently.

**Why not the other ways.** A relation spelled with the participant first, such as a
"product of" relation from a thing to the event that made it, says what `output` says
with the arguments reversed. The KB then holds two spellings of one relationship, and
**DRY** asks for one.

**Audit.** For every relation with an argument typed `happening`, `event` or a spec of
either, the event is argument 1.

## Event encodings beside n-ary relations

**Practice.** Represent a happening once when one encoding serves. When an event term and
a direct n-ary relation are both needed, keep both, bridge them with an explicit rule, and
say in a `;;` note which dimension forced two encodings and which direction the bridge
runs.

**Example.** `CxTra.txt` states `seeImage` as a direct relation between a seer and an
image, and `image_viewing` as a kind of event; its note says "image_viewing pairs with
seeImage the way flying pairs with flies: the relation states who is looking, the event
kind states the ability to be its doer." A bridge from the event encoding to the direct
relation, written in the vocabulary `abstract.txt` and `CxTra.txt` ship, is:

```clojure composed
(set/forwardRule
  (implies (and (image_viewing ?e) (doneBy ?e ?x) (thingPerceived ?e ?y))
           (seeImage ?x ?y)))
```

This rule is composed for the chapter; the shipped files state no bridge.

**Why.**

- *Logical.* The two encodings put time in different places. A `(seeImage Ann Img)` fact
  holds in the context it is asserted in, and the context fixes when. An event's time is
  stated about the event itself, through `timeOf` or `TimeOfFn`, so two viewings in one
  context can have two times. A merge of the two encodings would lose one of the two
  placements, which is why **DRY** keeps both and bridges them.
- *Engine.* The bridge's conclusions rest on the event facts, so retracting the event's
  membership or a participant fact withdraws the `seeImage` it supported. The reverse
  bridge, from `seeImage` to an event, needs a new event term for each fact, which is an
  existential consequent ([ch. 33](33-existentials.md)).
- *Maintenance.* Two encodings with no bridge drift: a query in one encoding misses every
  fact stated in the other, and the two can contradict each other with nothing to report
  the clash.

**Why not the other ways.** Keeping only the direct relation gives up the event's own
time, its other participants, and the event hierarchy's rules. Keeping only the event
encoding makes every simple statement of who saw what into four sentences. Keeping both
without a bridge stores the same knowledge twice with no link between the copies.

**Audit.** For each pair of encodings, the file states the bridge rule and a `;;` note
naming the dimension that forced two encodings.

## Abilities are kinds of event

**Practice.** Represent an ability as the ability to be the doer of a kind of event. Use
the event hierarchy for the hierarchy of abilities. Do not mint a separate type of ability.

**Example.** `abstract.txt` places flying under travelling, and `life.txt` types the second
argument of `able` as a kind of happening and carries the claim up that
hierarchy:

```clojure
(genl flying travelling)
(genl travelling causal_event)
(genlArg able 2 happening)
(transitiveInArg able 2 genl)
```

`CxBiology.txt` states the consequence in a note: "(transitiveInArg able 2 genl)
with (genl flying travelling) answers (able ?x travelling) at retrieval for
anything believed to fly, and stores no record."

**Why.**

- *Logical.* An ability is an ability to take part in a kind of event as its doer, so the
  structure abilities need is the structure of the event kinds.
- *Engine.* The preservation declaration carries a stored `able` claim up the
  `genl` hierarchy of happening kinds at query time and stores nothing. When the flying
  claim is defeated, as for a penguin, the travelling answer has no believed claim to
  reach from and is not answered.
- *Maintenance.* `(genl flying travelling)` serves the events and the abilities together,
  and `travelling` being a `causal_event` is stated once for both. A separate ability type
  would need a parallel hierarchy kept in step with the events by hand.

**Why not the other ways.** `oe-defenses.md` weighs an `ability` type whose instances are
abilities, related to their holders by `able`, and rejects it: every "can fly
implies can travel" would need a second edge in the ability hierarchy that copies the
event edge.

**Audit.** For each new ability, name the event kind it is the ability to do, and confirm
that kind sits under the right parent in the event hierarchy.
