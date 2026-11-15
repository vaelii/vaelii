;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.shared-dumps-test
  "Builds the starter and upper-ontology dumps `tu/load-starter!` and `tu/load-core!`
  restore from, so their one-time cost is billed to this namespace's row and no other.

  A test JVM builds each dump once, in whichever namespace loads it first, and
  `scripts/lib/ns-timings.sh` times a namespace as the gap to the next `lein test` line.
  `scripts/ci-shard.sh` runs this namespace first in every shard for that reason
  (vaelii#265).  On failure a dump did not restore into a fresh KB, and every namespace
  loading that dump fails for the same reason."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))

(tu/deftest-kb the-starter-restores-into-a-fresh-kb
  (is (tu/holds-ask '(binary_predicate able) 'CxUniverse)))

(deftest the-upper-ontology-restores-into-a-fresh-kb-on-the-isolated-space
  (let [kb (doto (tu/isolated-fresh) (tu/load-core!))]
    (try (is (v/ask? kb '(genl tangible uninterrupted) 'CxUniverse))
         (finally (tu/clear-kb! kb)))))
