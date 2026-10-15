;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.world
  "The test-world: the individuals, facts, and worked fables the shipped schema no
  longer carries.  The starter (vaelii.host.starter) ships schema only — types,
  relations, and the theory rules — so the reasoning it demonstrates needs data to
  run on.  That data lives here, in the tests, below CxWell.

  Topology — the data contexts hang off CxWell, which sees every middle context,
  so each sees the whole ontology (every middle theory and CxUniverse) but not its
  siblings:

      CxWell
        CxNaturalWorld   the cast's type memberships + natural-world facts
        CxSocialWorld    social-world facts
        CxStories        the Aesop fables + story-understanding schema

  The cast is told twice over about one of its animals.  `(asleep Whiskers)`
  is the timeless reading CxBiology's awake-until-told-otherwise default handles; the same
  cat's afternoon is also written as events and fluents, which is what CxChange's inertia
  reads to answer whether it is asleep at four and awake at six.  The two say different
  things and neither derives the other.

  The cast's type memberships live in CxNaturalWorld, so the biology and kinship
  theories — which every CxWell descendant sees — place their conclusions back in
  CxNaturalWorld, where the tests query them.  Social facts sit in a sibling
  CxSocialWorld, so a rule joining an owns-fact with a natural-world tangiblePartOf-fact
  finds no shared context and does not fire — the placement isolation the tests check.

  `load-into` layers onto a KB that already has the starter schema."
  (:require [vaelii.core :as v]
            [vaelii.world-fables :as fables]
            [vaelii.world-narrative :as narrative]))

(def topology
  '[(genlCx CxNaturalWorld CxWell)
    (genlCx CxSocialWorld  CxWell)])

(def contexts
  "The memberships `genlCx`'s argument declarations require of the data contexts, in
  CxUniverse, where every `genlCx` edge is stored."
  '[(context CxNaturalWorld) (context CxSocialWorld)])

(def individuals
  "The cast's type memberships — in CxNaturalWorld, so the biology and kinship
  conclusions over them land there for the tests to query."
  '[(human Tom) (human Bob) (human Ann) (human Carol) (human Dave)
    (human Eve) (human Nancy)
    (dog Muffet) (cat Whiskers) (penguin Tweety) (eagle Sam) (sparrow Jack)
    (fish Nemo) (tree Oak1) (flower Rose1) (vehicle Car1) (food Kibble)
    (building Garage1) (building House1)
    (food Bone1) (tangible Engine1) (tangible Piston1)])

(def natural-facts
  '[(parentOf Tom Bob) (parentOf Bob Ann) (parentOf Bob Carol) (parentOf Dave Eve)
    (siblingOf Ann Carol)
    (eats Muffet Kibble) (eats Muffet Bone1)
    (tangiblePartOf Engine1 Car1) (tangiblePartOf Piston1 Engine1)
    (locatedIn Car1 Garage1) (locatedIn Garage1 House1)])

(def fluent-functions
  "The fluents the timed narratives below run over, as **reified NATs** — one constant per
  animal, which is the bounded shape `reifiable_function` is for (docs/nat.md).  A fluent is
  a term rather than a sentence, so `holdsAt` stays an ordinary binary predicate over two
  terms and nothing has to be held opaque to identity congruence.

  In CxWell, the bottom anchor, because two data contexts use them: the cat's afternoon in
  CxNaturalWorld and the hare's nap in CxTortoiseHare, which are siblings and see each
  other not at all."
  '[(reifiable_function AsleepFn)  (result AsleepFn fluent)
    (reifiable_function AwakeFn)   (result AwakeFn fluent)
    (reifiable_function IndoorsFn) (result IndoorsFn fluent)
    (reifiable_function AheadOfFn) (result AheadOfFn fluent)])

(def timed-day
  "Whiskers' afternoon, as CxChange reads it: four moments, two events, and what each
  event starts and stops.  Nobody states that the cat is asleep at four — that is
  inertia's answer, and the whole point of writing the afternoon this way rather than as
  the timeless `(asleep Whiskers)` CxBiology already handles.

  The ordering is four moments and the three links between them.  `instantBefore` is
  declared transitive, and a forward join over a transitive antecedent reads the closure,
  so `clipped` sees three o'clock before six without the narrative saying so (CxChange)."
  '[(time_point ThreeOClock) (time_point FourOClock)
    (time_point FiveOClock)  (time_point SixOClock)

    (instantBefore ThreeOClock FourOClock) (instantBefore FourOClock FiveOClock)
    (instantBefore FiveOClock SixOClock)

    ;; before the afternoon starts the cat is awake and indoors; nothing ever puts it out
    (initially (AwakeFn Whiskers))
    (initially (IndoorsFn Whiskers))

    (causal_event CatFallsAsleep) (causal_event CatWakes)

    (happens CatFallsAsleep ThreeOClock)
    (initiates CatFallsAsleep (AsleepFn Whiskers) ThreeOClock)
    (terminates CatFallsAsleep (AwakeFn Whiskers) ThreeOClock)

    (happens CatWakes FiveOClock)
    (initiates CatWakes (AwakeFn Whiskers) FiveOClock)
    (terminates CatWakes (AsleepFn Whiskers) FiveOClock)])

(def social-facts
  '[(person Ann) (person Bob) (person Nancy) (person Tom)
    (animal Bob) (animal Tom)
    (tangible Car1) (tangible Chimney1) (tangible House1) (tangible Roof1)

    (marriedTo Bob Nancy)
    (owns Tom Car1) (owns Tom House1)
    (tangiblePartOf Roof1 House1) (tangiblePartOf Chimney1 House1)
    (likes Ann Muffet)
    (birthYearOf Tom 1970) (birthYearOf Bob 1995)])

(defn load-cast
  "Assert the cast — topology, type memberships, and facts — into `kb` (already
  carrying the starter schema). Returns kb."
  [kb]
  (doseq [s topology]         (v/assert kb s 'CxWell))
  (doseq [s contexts]         (v/assert kb s 'CxUniverse))
  (doseq [s fluent-functions] (v/assert kb s 'CxWell))
  (doseq [s individuals]      (v/assert kb s 'CxNaturalWorld))
  (doseq [s natural-facts]    (v/assert kb s 'CxNaturalWorld))
  (doseq [s timed-day]        (v/assert kb s 'CxNaturalWorld))
  (doseq [s social-facts]     (v/assert kb s 'CxSocialWorld))
  kb)

(defn load-into
  "Populate `kb` (already carrying the starter schema) with the whole test-world: the
  cast, the four Aesop fables, and the story-understanding examples. Returns kb."
  [kb]
  (load-cast kb)
  (fables/load-into kb)
  (narrative/load-into kb)
  kb)
