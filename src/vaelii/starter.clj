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
  "Load the starter ontology into `kb`, then each text KB `{:layers [path …]}` names
  (`vaelii.core/load-text!`), and return kb: `(load-into (v/open-kb {}))`.  Over a durable
  store nothing has written to since the last call, the sources before the first whose
  files changed are skipped, and the rest load once the contexts they wrote hold only the
  facts the layers state (docs/operations.md, \"Restarting over a built store\").  The
  starter is over 3,700 asserted sentexes, a schema with no individuals, and loaded in any
  order the same sentences build the same KB (`absent_type_order_test`)."
  ([kb] (load-into kb nil))
  ([kb opts] (starter/load-starter-and-layers kb opts)))
