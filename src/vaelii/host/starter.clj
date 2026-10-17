;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.starter
  "A starter common-sense KB: a documented, **schema-only** upper + middle ontology.
  It loads the upper ontology into CxUniverse (vaelii.host.core-context), then the
  middle contexts, each a KB file on the classpath under resources/kb/:

    * upper (`kb/upper/`, every file in CxUniverse): what things *are*, always true, like
      `genl`.  Split by domain, one file each:
        - core.txt       — the vocabulary the engine interprets and the top of the
                                ontology.
        - abstract.txt   — the abstract type skeleton (physical/intangible and
                                their kinds) + the structural relations tangiblePartOf/locatedIn.
        - organism.txt   — the biological taxonomy + its disjointness.
        - life.txt       — the organism relations (parentOf, siblingOf, flies,
                                mortal, birthYearOf, olderThan, …) with arg + metadata.
        - society.txt    — the social relations (marriedTo, likes, owns).
        - measure.txt    — the theory of measurement: the two measure terms, the
                                dimensionOf/conversionFactor table with the units that
                                fill it, the comparisons, weightOf / heightOf, and the
                                sign vocabulary for the quantities nobody has a figure
                                for (signOf / trendOf / the qualitative* arithmetic).
        - reflection.txt — the expression lattice (atomic and non-atomic, open and
                                closed, well-formed and ill-formed expressions) and the
                                use/mention vocabulary (proposition, means, denotes,
                                expresses).
        - space.txt      — qualitative space, four independent calculi: RCC-8
                                topology (eight base + six derived), cardinal direction
                                (nine + four), relative direction over a frame's own axes
                                (nine + four, the frame being the context), and
                                qualitative distance (seven + three).
        - time.txt       — qualitative time: Allen's interval relations (thirteen
                                base + seven derived), the point algebra over instants,
                                the three calendar constructors and the InstantFn moment
                                a calendar term's startOf and endOf are computed as, plus
                                the length / totalDuration / overlapDuration vocabulary
                                the arithmetic computes over.
    * middle (`kb/middle/`, one context per file, between CxUniverse and CxWell): how the
      definitional things *interrelate*, where several overlapping theories can coexist.
        - CxAnatomy.txt   — what kinds of thing have what kinds of part.
        - CxBiology.txt   — birds fly by default except penguins; organisms
                                 are mortal; flight enables travel; sleep is what the
                                 theory is willing to assume.
        - CxChange.txt    — a simple event calculus: a state persists until an
                                 event ends it, so holdsAt is inertia over what
                                 initiates and terminates say.
        - CxComputing.txt — relations over software tools, their invocations and
                                 receipts, media resources and DNS names, and
                                 the kinds the relations are typed over.
                                 Opt-in: it sees CxUniverse and CxWell does not
                                 see it.
        - CxKinship.txt   — grandparentOf, ancestorOf, olderThan, and parenthood
                                 from maternity and paternity.
        - CxMereology.txt — a part is located where its whole is; owning a whole
                                 entails owning its parts.
        - CxNormalPhysicalConditions.txt — the states of matter at room temperature
                                 and pressure: stone, wood and glass are solid,
                                 mercury is liquid, a metal is solid by default.
                                 Opt-in: it sees CxUniverse and CxWell does not
                                 see it.
        - CxPerception.txt — perception relations: perceives, sees, seeImage,
                                 watchVideo. Opt-in: it sees CxUniverse and CxWell
                                 does not see it.
        - CxSize.txt      — comparative size: stated between kinds, computed
                                 between objects from their measures.
        - CxSocial.txt    — what acquaintance follows from; employment as one way
                                 of belonging; the general relationship and
                                 dwelling vocabulary over two persons.
        - CxSocialExtension.txt — relationship and plural-identity vocabulary
                                 narrower than CxSocial's own. Opt-in: it sees
                                 CxSocial and CxWell does not see it. The
                                 Extension suffix names a theory that extends
                                 an existing starter theory with vocabulary
                                 most contexts under the base theory have no
                                 occasion to see.

  The topology, most general (top) to most specific (bottom): CxUniverse holds the upper
  ontology; each middle context sees CxUniverse and not the other middle contexts; and
  CxWell sees every middle context but the opt-in ones.  Each middle file wires itself in
  with its own `genlCx` edges, so the topology is data.  **No cast and no contingent facts
  ship**: the starter is a schema, and
  contingent data (a cast, worked examples, the Aesop fables) belongs below CxWell
  and lives in the tests that need it.

  The unit table is the one place individuals ship, and it applies that rule rather
  than excepting itself from it: a minute is sixty seconds by stipulation, so the
  factor is vocabulary and not a measurement anybody took.  measure.txt states
  the test it holds a unit to.

  What stays in code here is the *order the layers* load in — loading order is logic,
  the definitional layer must precede the theories that reason over it — and the one
  computed batch (every type is also a unary_predicate).  Within a layer, every file
  present is loaded (discovered from the classpath), so adding a domain or a theory is
  dropping a file in kb/upper/ or kb/middle/, no code change."
  (:require [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.sentex :as sx]))

(defn load-into
  "Populate `kb` with the starter schema — every file under resources/kb/upper/ and
  resources/kb/middle/, loaded on kb start by default. Returns kb.

  `loaded`, when given, is called with each load's context right after it is asserted —
  `CxUniverse` after the upper ontology, then each middle context in load order — and
  with `:unary-predicates` after the closing batch, which no file states.
  `vaelii.host.sync` reads it to learn which load each premise came from."
  ([kb] (load-into kb nil))
  ([kb loaded]
   (let [loaded (or loaded (fn [_]))]
     ;; The whole starter is one batch: belief settles once at the end, not once per
     ;; sentence (`v/with-deferred-settle`, belief computed from current state, so the
     ;; single closing reconciliation reaches the same beliefs as N per-assert ones).  The
     ;; nested `core-context/load-into` defers into this batch — its own wrapper is a no-op
     ;; and this one's settle reconciles both.
     (v/with-deferred-settle kb
       (core-context/load-into kb)
       (loaded sx/root-context)
       (doseq [c (seed/layer-contexts "middle")]
         (seed/load-context kb c "middle")
         (loaded c)))
     ;; The subtypes of thing are unary types. Other genl components may relate
     ;; predicates of any arity and do not imply unary membership.  `specs` is read after the
     ;; batch above settles, so its extent is the believed one; a second batch stores the marks.
     (v/with-deferred-settle kb
       (doseq [t (nm/by-print-key (v/specs kb 'thing))]
         (v/assert kb (list 'unary_predicate t) sx/root-context)))
     (loaded :unary-predicates)
     kb)))
