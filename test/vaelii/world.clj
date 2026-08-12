;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.world
  "The test-world: the individuals, facts, and worked fables the shipped schema no
  longer carries.  The starter (vaelii.impl.starter) ships schema only — types,
  relations, and the theory rules — so the reasoning it demonstrates needs data to
  run on.  That data lives here, in the tests, below CxWell.

  Topology — the data contexts hang off CxWell, the bottom of the shipped
  spindle, so each sees the whole ontology (every middle theory, every upper
  definition) but not its siblings:

      CxWell
        CxNaturalWorld   the cast's type memberships + natural-world facts
        CxSocialWorld    social-world facts
        CxStories        the Aesop fables + story-understanding schema

  The cast's type memberships live in CxNaturalWorld, so the biology and kinship
  theories — which every CxWell descendant sees — place their conclusions back in
  CxNaturalWorld, where the tests query them.  Social facts sit in a sibling
  CxSocialWorld, so a rule joining an owns-fact with a natural-world partOf-fact
  finds no shared context and does not fire — the placement isolation the tests check.

  `load-into` layers onto a KB that already has the starter schema."
  (:require [vaelii.core :as v]
            [vaelii.world-fables :as fables]
            [vaelii.world-narrative :as narrative]))

(def topology
  '[(genlCx CxNaturalWorld CxWell)
    (genlCx CxSocialWorld  CxWell)])

(def individuals
  "The cast's type memberships — in CxNaturalWorld, so the biology and kinship
  conclusions over them land there for the tests to query."
  '[(human Tom) (human Bob) (human Ann) (human Carol) (human Dave)
    (human Eve) (human Nancy)
    (dog Muffet) (cat Whiskers) (penguin Tweety) (eagle Sam) (sparrow Jack)
    (fish Nemo) (tree Oak1) (flower Rose1) (vehicle Car1) (food Kibble)
    (building Garage1) (building House1)])

(def natural-facts
  '[(parentOf Tom Bob) (parentOf Bob Ann) (parentOf Bob Carol) (parentOf Dave Eve)
    (siblingOf Ann Carol)
    (eats Muffet Kibble) (eats Muffet Bone1)
    (partOf Engine1 Car1) (partOf Piston1 Engine1)
    (locatedIn Car1 Garage1) (locatedIn Garage1 House1)])

(def social-facts
  '[(marriedTo Bob Nancy)
    (owns Tom Car1) (owns Tom House1)
    (partOf Roof1 House1) (partOf Chimney1 House1)
    (likes Ann Muffet)
    (birthYearOf Tom 1970) (birthYearOf Bob 1995)])

(defn load-cast
  "Assert the cast — topology, type memberships, and facts — into `kb` (already
  carrying the starter schema). Returns kb."
  [kb]
  (doseq [s topology]      (v/assert kb s 'CxWell))
  (doseq [s individuals]   (v/assert kb s 'CxNaturalWorld))
  (doseq [s natural-facts] (v/assert kb s 'CxNaturalWorld))
  (doseq [s social-facts]  (v/assert kb s 'CxSocialWorld))
  kb)

(defn load-into
  "Populate `kb` (already carrying the starter schema) with the whole test-world: the
  cast, the four Aesop fables, and the story-understanding examples. Returns kb."
  [kb]
  (load-cast kb)
  (fables/load-into kb)
  (narrative/load-into kb)
  kb)

(defn starter+world
  "A one-call loader for a `tu/loaded` fixture: the starter schema plus the whole
  test-world.  Requires vaelii.impl.starter — passed in to avoid a compile-time cycle
  from a test-support ns into an impl ns."
  [load-starter kb]
  (load-starter kb)
  (load-into kb))
