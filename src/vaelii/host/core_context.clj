;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.core-context
  "The upper ontology: every KB file under `resources/kb/upper/`, loaded into CxUniverse.
  `core.txt` is the vocabulary — the special-predicate surface the engine interprets
  (types/contexts, arg, disjoint, the `set/*Rule` wrappers, the predicate metadata,
  negation, `ist`, the evaluables), the predicate meta-ontology and the ontology's top;
  `interface-rules.txt` is interface sugar (`args` stored as `argAndRest`, also loaded
  by `tu/fresh`); each other file is one domain (abstract, life, measure, organism,
  reflection, society, space, structure, time).  Documentation rides on `comment`
  sentexes, ordinary stored ones, so the KB documents itself in its own representation.

  CxUniverse is the root: every context the middle layer wires in sees it, and a KB built
  for vocabulary alone holds exactly this load.  The middle contexts below it are the
  starter's (see vaelii.host.starter)."
  (:require [vaelii.core :as v]
            [vaelii.host.seed :as seed]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.sentex :as sx]))

(defn upper-files
  "The file names under `kb/upper/`, `core.txt` first and the domain files after it in
  sorted order."
  []
  (let [fs (seed/layer-files "upper")]
    (into ["core.txt"] (remove #{"core.txt"}) fs)))

(defn load-into
  "Assert the upper ontology into `kb`: every file of `upper-files`, all into CxUniverse,
  as one `seed/load-sentences` batch, so a sentence one file states over a term another
  file defines is retried until that term arrives.  Returns kb."
  [kb]
  ;; One settle at the end, not one per sentence: the whole upper ontology is a batch, and
  ;; `settle` computes belief from current state, so N per-assert reconciliations reach
  ;; the same beliefs as one closing reconciliation (`v/with-deferred-settle`).
  (v/with-deferred-settle kb
    (seed/load-sentences kb (let [fs (upper-files)]
                              (with-open [r (progress/start ::upper-files
                                                            "starter: read the upper files"
                                                            (count fs))]
                                (into [] (mapcat (fn [f]
                                                   (progress/tick! r)
                                                   (seed/read-sentences f "upper")))
                                      fs)))
                         sx/root-context)))

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
