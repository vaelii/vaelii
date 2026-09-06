;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.starter
  "The bundled starter knowledge base — the shipped schema-only ontology, loaded into a
  KB you already opened.

  Public because the README's first example uses it: `vaelii.core` is the engine, and
  this is the one piece of *content* that ships beside it.  The implementation is
  `vaelii.impl.starter`, which is free to change."
  (:require [vaelii.impl.starter :as starter]))

(defn load-into
  "Load the starter ontology into `kb` and return it.

    (load-into (v/open-kb {}))

  About 3,310 sentexes: the vocabulary head, the definitional upper band, and the
  middle theories.  No individuals — it is a schema to build on, not a world."
  [kb]
  (starter/load-into kb))
