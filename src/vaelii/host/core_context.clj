;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.core-context
  "The CxCore ontology — Vaelii's vocabulary context.  It defines and
  documents the core predicates the engine interprets, as sentexes in CxCore:
  the special-predicate surface (types/contexts, arg, disjoint, the `set/*Rule`
  wrappers, the predicate metadata, negation, `ist`, the evaluables) and the
  predicate meta-ontology.  Documentation rides on `comment` sentexes,
  `(comment <term> \"...\")` — ordinary sentexes (stored, indexed, queryable) — so the
  KB documents itself in its own representation.

  The content is a KB file, `resources/kb/CxCore.txt` (read by
  vaelii.host.seed); this namespace loads it and reads the docs back.

  CxCore is the spindle **head**: the root every context sees, and the only
  layer a core-only KB has.  The layers below it — the definitional `upper`
  contexts (between Core and Universe) and the theory `middle` contexts (between
  Universe and Well) — are the starter's, not the core KB's, and each wires itself
  into the spindle in its own KB file (see vaelii.host.starter)."
  (:require [vaelii.core :as v]
            [vaelii.host.seed :as seed]
            [vaelii.impl.naming :as nm]))

(defn load-into
  "Assert the CxCore vocabulary into `kb` from its KB file
  (resources/kb/CxCore.txt). Returns kb.

  The topology edge `(genlCx CxUniverse CxCore)` is asserted **before** the file, and
  it is here rather than in the file because of *when* it has to hold.  A
  `decontextualized_predicate` declaration lifts the facts already present into
  CxUniverse, and a rule stated in CxCore fires on the copy — so the two contexts must
  already be comparable for that firing to be placed on arrival.  The file is read
  term-centrically in natural sort order, which puts `genlCx` after `functional`; a firing
  that finds no placement is re-joined when the edge arrives, so the KB is the same
  either way, and asserting the edge first is what spares the load that second pass.

  The `(forced_decontextualized_predicate genlCx)` declaration goes in ahead of the edge,
  so the edge is stored in CxUniverse, where the file's own edges are."
  [kb]
  ;; One settle at the end, not one per sentence: the whole vocabulary is a batch, and
  ;; `settle` computes belief from current state, so N per-assert reconciliations reach
  ;; the same beliefs as one closing reconciliation (`v/with-deferred-settle`).  The
  ;; `genlCx` edge is still asserted first — edges live on store, ahead of the deferred
  ;; settle — so its ordering role (below) is unchanged.
  (v/with-deferred-settle kb
    ;; the declaration that stores every `genlCx` edge in CxUniverse goes first, so the
    ;; bootstrap edge lands where the file's own edges and a later re-assert of it do
    (v/assert kb '(forced_decontextualized_predicate genlCx) 'CxCore)
    (v/assert kb '(genlCx CxUniverse CxCore) 'CxCore)
    (seed/load-context kb 'CxCore)))

(defn comment-of
  "The documentation attached to `term` by `comment` sentexes, in **content order**.

  Ordered because every caller takes the first one — the vocabulary card, the prompt's
  predicate lines, a selection's gloss.  `sentexes-matching` promises the *set* and not
  an order, so a term carrying two comments (the shipped ontology gives each one; a KB
  that adds a gloss of its own gives two) would otherwise be displayed with whichever
  the index happened to yield first, and the same knowledge loaded in two orders would
  read differently.  A vector, since the ranking realizes the matches either way.

  Ranked through `nm/name-key` rather than on the value: `comment`'s second argument is a
  string by convention and nothing refuses another type, and a comparison of a string
  against a number throws where this only has to be total.  `name-key` is `str` for the
  scalar the convention promises and the guarded `print-key` for anything else, so a
  comment written as a compound cannot collapse two entries into one key under an ambient
  `*print-length*`."
  [kb term]
  (into [] (sort-by nm/name-key
                    (map (comp #(nth % 2) :sentence)
                         (v/sentexes-matching kb (list 'comment term '?text) '?ctx)))))
