;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.starter
  "The bundled starter knowledge base — the shipped schema-only ontology, loaded into a
  KB you already opened.

  Public because the README's first example uses it: `vaelii.core` is the engine, and
  this is the one piece of *content* that ships beside it.  The implementation is
  `vaelii.host.starter`, which is free to change."
  (:require [vaelii.host.starter :as starter]))

(defn load-into
  "Load the starter ontology into `kb` and return it.

    (load-into (v/open-kb {}))

  Over 1,600 asserted sentexes — the spindle head, the upper spindle's members
  and the middle spindle's — which the rules take to 3,200+ stored once they have fired.  No
  individuals: the starter is a schema to build on, not a world.  Loaded in any order the
  same sentences build the same KB (`absent_type_order_test`)."
  [kb]
  (starter/load-into kb))
