;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.world-narrative
  "A story-understanding ontology — test-world data below the shipped schema (see
  vaelii.world).  A schema of narrative concepts (agents, actions,
  events, goals) and the relations that connect them (wants, does, brings, achieves,
  causes, beforeEvent), annotated with metadata so the generic provers do more than
  the plain fables can:

    * causal reasoning — `causes` is transitive, so a chain of small causes is read
      as one cause (the flattery ultimately causes the fox to get the cheese);
    * temporal reasoning — `beforeEvent` is transitive, so events order themselves
      along the chain; a *direct* link also reads backwards via its inverse
      `afterEvent` (a transitively-derived order does not, since the inverse prover
      inverts stored facts only).  A story that dates its events gets the ordering
      for nothing: a rule reads `beforeEvent` off two `happens` facts and the
      instants' own order;
    * change over time — the Tortoise and the Hare is retold in CxRaceClock as events
      and fluents, so CxChange's inertia answers whether the hare is asleep while the
      tortoise goes past, and whether the tortoise is ahead at the finish, with
      neither stated;
    * goal reasoning — an agent that wants a goal and brings about an event that
      achieves it is deduced to *achieve its goal* (a joined forward rule); an agent
      is *responsible for* what its action directly causes.

  It is worked on one new story (the Fox and the Crow) and retrofitted onto an
  existing fable (the Tortoise and the Hare) to show the schema generalizes.  The
  schema lives in CxStories, seen by every fable."
  (:require [vaelii.core :as v]))

;; ---- the narrative schema -----------------------------------------------

(def type-hierarchy
  '[(genl agent        thing)
    (genl event        thing)
    (genl action       event)          ; an action is an event an agent performs
    (genl mental_state thing)
    (genl goal         mental_state)])

(def type-docs
  '[(comment agent        "A being that acts with intent — the doer of a story.")
    (comment event        "Something that happens in the story's world.")
    (comment action       "An event an agent deliberately performs.")
    (comment mental_state "An agent's inner state — a belief, a wish, a goal.")
    (comment goal         "A state of affairs an agent wants to bring about.")])

(def predicate-metadata
  ;; afterEvent is deliberately NOT declared transitive: it exists only to read a
  ;; direct beforeEvent link backwards (the inverse prover inverts stored facts), so
  ;; it has no base edges of its own for a transitive closure to compose.
  '[(transitive causes)                 ; a chain of causes is itself a cause
    (transitive beforeEvent)            ; temporal precedence composes
    (inverse    beforeEvent afterEvent)])

(def predicate-docs
  '[(comment wants         "(wants ?agent ?goal) means that ?agent desires ?goal.")
    (comment does          "(does ?agent ?action) means that ?agent performs ?action.")
    (comment brings        "(brings ?agent ?event) means that ?agent brings ?event about.")
    (comment achieves      "(achieves ?event ?goal) means that ?event realizes ?goal.")
    (comment causes        "(causes ?event1 ?event2) means that ?event1 brings ?event2 about. Transitive, so a chain of causes is itself a cause.")
    (comment beforeEvent   "(beforeEvent ?event1 ?event2) means that ?event1 happens before ?event2. Transitive, and the inverse of afterEvent.")
    (comment afterEvent    "(afterEvent ?event1 ?event2) means that ?event1 happens after ?event2. The inverse of beforeEvent, and deliberately not transitive: it has no base edges of its own, existing only to read a beforeEvent link backwards.")
    (comment achievesGoal  "(achievesGoal ?agent ?goal) means that ?agent got what it wanted. Derived, when the agent brings about an event that achieves the goal.")
    (comment responsibleFor "(responsibleFor ?agent ?event) means that ?agent's action directly caused ?event. Derived from does and causes.")])

(def predicate-constraints
  '[(arg wants   1 agent) (arg wants   2 goal)
    (arg does    1 agent) (arg does    2 action)
    (arg brings  1 agent) (arg brings  2 event)
    (arg achieves 1 event) (arg achieves 2 goal)
    (arg causes  1 event) (arg causes  2 event)
    (arg beforeEvent 1 event) (arg beforeEvent 2 event)
    (arg responsibleFor 1 agent) (arg responsibleFor 2 event)])

(def predicate-types
  '[(binary_predicate wants)   (binary_predicate does)        (binary_predicate brings)
    (binary_predicate achieves) (binary_predicate causes)     (binary_predicate beforeEvent)
    (binary_predicate afterEvent) (binary_predicate achievesGoal) (binary_predicate responsibleFor)])

;; ---- worked story: the Fox and the Crow ---------------------------------

(def fox-and-crow
  "The fox flatters the crow; flattery makes the crow sing; singing drops the cheese;
  the fox gets it.  Types first (so the arg checks bind), then the facts."
  '[(agent FoxF) (agent CrowF)
    (goal HasCheese)
    (action Flatter1) (causal_event Flatter1)    ; a cause is causal (arg causes 1 causal)
    (causal_event CrowSings) (causal_event CheeseFalls) (event FoxGetsCheese)
    (wants FoxF HasCheese)
    (does FoxF Flatter1)
    (causes Flatter1 CrowSings)          ; the causal chain, link by link
    (causes CrowSings CheeseFalls)
    (causes CheeseFalls FoxGetsCheese)
    (beforeEvent Flatter1 CrowSings)     ; the same links, temporally
    (beforeEvent CrowSings CheeseFalls)
    (beforeEvent CheeseFalls FoxGetsCheese)
    (brings FoxF FoxGetsCheese)
    (achieves FoxGetsCheese HasCheese)])

(def tortoise-timeline
  "The Tortoise and the Hare on a clock, so CxChange's inertia can be asked about it.
  Five moments in order, and three events: the hare lies down, the tortoise goes past, the
  hare wakes.  Nobody writes down that the hare is asleep while the tortoise passes — that
  is what a state persisting until something ends it *means*, and it is the one thing the
  fable turns on.

  In **CxRaceClock**, a context of its own below CxTortoiseHare, rather than in the fable,
  so the fable context holds the tale as it is told and nothing about instants and
  orderings.  Below it, the timeline sees the fable's facts and every character keeps its
  name.

  The four consecutive links are stated and no more: `instantBefore` is transitive, and a
  forward join over a transitive antecedent reads the closure, so the race's beginning
  comes before its end without anybody writing that down (CxChange).  Each event is an
  `event`, which reaches `temporal` through `happening` and `situation` in CxCore, so it
  satisfies both `happens`, whose first argument is a temporal, and `beforeEvent`, whose
  arguments are events."
  '[(time_point RaceBegins) (time_point HareLiesDown) (time_point TortoisePasses)
    (time_point HareWakes)  (time_point RaceEnds)

    (instantBefore RaceBegins HareLiesDown)     (instantBefore HareLiesDown TortoisePasses)
    (instantBefore TortoisePasses HareWakes)    (instantBefore HareWakes RaceEnds)

    (event HareNaps) (event TortoiseGoesPast) (event HareStirs)

    (happens HareNaps HareLiesDown)
    (initiates HareNaps (AsleepFn HareA) HareLiesDown)

    (happens TortoiseGoesPast TortoisePasses)
    (initiates TortoiseGoesPast (AheadOfFn TortoiseA) TortoisePasses)

    (happens HareStirs HareWakes)
    (terminates HareStirs (AsleepFn HareA) HareWakes)])

;; the Tortoise and the Hare, re-read with the same schema (its context already exists)
(def tortoise-goal
  '[(agent TortoiseA)
    (goal WinRace)
    (event TortoiseFinishes)
    (wants TortoiseA WinRace)
    (brings TortoiseA TortoiseFinishes)
    (achieves TortoiseFinishes WinRace)])

(defn- assert-all [kb ctx forms] (doseq [s forms] (v/assert kb s ctx)))

(defn load-into
  "Load the story-understanding ontology and its worked examples.  Requires the
  starter (and its stories) to be loaded first, so CxStories exists.  Returns kb."
  [kb]
  (v/assert kb '(genlCx CxFoxCrow CxStories) 'CxUniverse)
  (v/assert kb '(context CxFoxCrow) 'CxUniverse)
  ;; `inverse` is stored in CxUniverse, and its argument declaration types afterEvent there
  (v/assert kb '(predicate afterEvent) 'CxUniverse)
  ;; the timed retelling hangs below the fable rather than in it — see `tortoise-timeline`
  (assert-all kb 'CxStories type-hierarchy)
  (assert-all kb 'CxStories type-docs)
  (assert-all kb 'CxStories predicate-metadata)
  (assert-all kb 'CxStories predicate-docs)
  (assert-all kb 'CxStories predicate-constraints)
  (assert-all kb 'CxStories predicate-types)
  (doseq [t '[agent event action mental_state goal]]     ; uphold the unary_predicate invariant
    (v/assert kb (list 'unary_predicate t) 'CxStories))
  ;; goal reasoning: wanting a goal + bringing about an event that achieves it ⇒ success
  (v/assert-rule kb '[(wants ?a ?g) (brings ?a ?e) (achieves ?e ?g)]
                 '(achievesGoal ?a ?g) 'CxStories {:direction :forward})
  ;; agency: an agent is responsible for what its action directly causes
  (v/assert-rule kb '[(does ?a ?act) (causes ?act ?e)] '(responsibleFor ?a ?e) 'CxStories {:direction :forward})
  ;; and the two ways of ordering events are one claim: an event whose moment comes first
  ;; happens first.  beforeEvent stays the story-level spelling and keeps its transitivity;
  ;; this is what lets a story that dates its events get the ordering for nothing.
  (v/assert-rule kb '[(happens ?e1 ?t1) (happens ?e2 ?t2) (instantBefore ?t1 ?t2)]
                 '(beforeEvent ?e1 ?e2) 'CxStories {:direction :forward})
  (assert-all kb 'CxFoxCrow fox-and-crow)
  (v/assert kb '(comment CxFoxCrow
                         "The Fox and the Crow — moral: do not trust flatterers; the flattery serves the flatterer.")
            'CxStories)
  (assert-all kb 'CxTortoiseHare tortoise-goal)          ; the same schema on an existing fable
  (v/assert kb '(genlCx CxRaceClock CxTortoiseHare) 'CxUniverse)
  (v/assert kb '(context CxRaceClock) 'CxUniverse)
  (assert-all kb 'CxRaceClock tortoise-timeline)         ; and the same fable on a clock
  (v/assert kb '(comment CxRaceClock
                         "The Tortoise and the Hare, dated: the same race written as events and fluents, so what holds when is inertia's answer rather than the story's.")
            'CxStories)
  kb)
