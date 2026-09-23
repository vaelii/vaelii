;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.witness-shortfall-test
  "No firing is placed below a route another context has.

  A reachability with two routes carries one witness, and the witness decides where the
  conclusion lives (docs/contexts.md, \"The consumers, and what each of them may reach\").
  `inherit_forward_test`'s `the-witness-is-the-route-that-places-the-conclusion-highest`
  is the lattice case, one firing read from three contexts.  This is the corpus case
  beside it: many chains, each with a long route stated in the general context and a
  short one in a specific context, read by `vaelii.witness-reading/report` — the same
  reading `lein bench-witness` prints — and held at zero `above` for every witness kind,
  and at zero `silent` where a long-route edge per chain is scoped-defeated.

  Two corpora, one per witness search: over `genl`, where `tax/general-reach-supports`
  picks the route, and over a declared-transitive fact relation, where `inherit/fact-paths`
  picks it.  Each also asserts that it names a preservation witness at all, since a
  corpus that fires nothing reads zero on a broken engine.

  The starter and the test world are **not** held here.  Neither holds a preservation
  firing, so both read zero on a broken engine, and a shipped corpus that grows one would
  move the count for a reason that is not a defect.  They stay a reading, in the bench."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.test-util :as tu]
            [vaelii.witness-reading :as wr]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private chains 3)
(def ^:private depth 4)

(defn- holds-at-zero [report]
  (testing "the corpus names a preservation witness"
    (is (some (fn [[kind counts]]
                (and (re-find #"/preserve$" (str kind)) (pos? (:named counts 0))))
              report)
        (pr-str report)))
  (doseq [[kind counts] report]
    (testing (str kind " — no witness placed a firing below a route a more general context has")
      (is (zero? (:above counts 0)) (pr-str counts)))))

(tu/deftest-kb a-genl-witness-places-each-firing-as-high-as-its-routes-allow
  (holds-at-zero (wr/report (wr/generated kb tu/fresh-term chains depth))))

(tu/deftest-kb a-fact-relation-witness-places-each-firing-as-high-as-its-routes-allow
  (holds-at-zero (wr/report (wr/generated-fact kb tu/fresh-term chains depth))))

(defn- none-silent
  "Every firing a reader reads as withdrawn while it still reaches is believed there
  through another sentex — the one the settle re-derived over the reader's own route.
  `lost` stays at one per chain, since the firing over the defeated route is still
  stored; `silent` is the reading a caller sees."
  [report]
  (testing "the corpus names a preservation witness"
    (is (some (fn [[kind counts]]
                (and (re-find #"/preserve$" (str kind)) (pos? (:named counts 0))))
              report)
        (pr-str report)))
  (doseq [[kind counts] report]
    (testing (str kind " — no reader that still reaches loses the sentence")
      (is (zero? (:silent counts 0)) (pr-str counts)))))

(tu/deftest-kb a-reader-below-a-scoped-defeat-keeps-each-firing-over-its-own-route
  ;; One long-route edge per chain scoped-defeated in the short route's context, which
  ;; still reaches each chain's ends over its own edge (settle/lost-firing-seeds).
  (let [r (wr/report (wr/generated kb tu/fresh-term chains depth {:defeated? true}))]
    (none-silent r)
    (is (pos? (get-in r ['genl/preserve :lost] 0)) "the corpus withdraws a firing at all"))
  (let [r (wr/report (wr/generated-fact kb tu/fresh-term chains depth {:defeated? true}))]
    (none-silent r)
    (is (some #(pos? (:lost (val %) 0)) r) "the corpus withdraws a firing at all")))
