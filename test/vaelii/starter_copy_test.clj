;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.starter-copy-test
  "`tu/load-starter!` produces the KB `starter/load-into` produces.

  The suite's `:once` fixtures restore the starter from an export dump built once per
  JVM instead of re-asserting it, because the write path is not linear in the ontology's
  size — `tu/starter-dump` states the measurement.  That trade is only sound while the
  two routes agree, and nothing else in the suite would notice them diverging: a
  namespace loading a subtly different baseline still passes its own tests, and the
  difference surfaces later as a test that fails for a reason nobody can place.

  So this compares the two KBs on everything a test can read off one — the stored
  sentences with their contexts, truth and strength, what is believed, the taxonomy
  closures, and the justification graph.  Content, never handles: a handle is minted in
  assertion order and `import!` preserves the dump's, so comparing them would pin
  something no caller may depend on (README, \"Order independence\").

  ## On failure

  A route grew something the other did not.  Check `export!`'s variant coverage first: a
  dump holds what the record store holds, so this test breaks when some *derived* state
  is added that `recover` does not rebuild.  Do not repair it by narrowing the
  comparison — the difference this reports is a difference in the fixtures' baseline."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.starter :as starter]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- content
  "Every stored sentex as content: its sentence, context, truth, strength and whether the
  KB believes it.  A set, so neither storage order nor handle order can enter the
  comparison."
  [kb]
  (into #{}
        (map (fn [h]
               (let [sx (p/get-sentex (:records kb) h)]
                 [(:sentence sx) (:context sx) (:truth sx) (:strength sx) (v/in? kb h)])))
        (v/handles kb)))

(defn- justification-content
  "The justification graph as content: each conclusion's sentence and context against the
  set of its antecedents' sentences and contexts, with the informant.  Handles are
  resolved to sentences on both sides for `content`'s reason, and an informant that is a
  rule handle is resolved to the rule's sentence and context the same way; an informant
  that is a symbol is compared as written."
  [kb]
  (let [recs (:records kb)
        of   (fn [h] (let [sx (p/get-sentex recs h)] [(:sentence sx) (:context sx)]))
        inf  (fn [i] (if (integer? i) (of i) i))]
    (into #{}
          (mapcat (fn [h]
                    (for [j (v/supporting-justifications kb h)]
                      [(of h) (inf (:informant j)) (set (map of (:antecedents j)))])))
          (v/handles kb))))

(defn- taxonomy-content
  "The two cached closures a reader sees: the type hierarchy and the context spindle."
  [kb]
  (let [t (reasoning/taxonomy kb)]
    {:types    (into {} (for [x (tax/types t)]    [x (set (tax/genls-global t x))]))
     :contexts (into {} (for [c (tax/contexts t)] [c (set (tax/context-up t c))]))}))

(deftest a-restored-starter-is-the-asserted-one
  ;; two spaces of this namespace's own, and neither is `tu/starter-build-space` — the
  ;; dump's own build KB lives there and `clear-kb!` on it would wipe the dump's source
  ;; mid-comparison.  Cleared on open for `tu/fresh`'s reason.
  (let [space    (fn [k] (assoc tu/starter-build-space :space [::copy k]))
        built    (doto (v/open-kb (space :built))    (tu/clear-kb!) (starter/load-into))
        restored (doto (v/open-kb (space :restored)) (tu/clear-kb!) (tu/load-starter!))]
    (try
      (testing "the same sentexes are stored"
        (is (= (v/sentex-count built) (v/sentex-count restored))))
      (testing "sentence, context, truth, strength and belief agree, sentex for sentex"
        (is (= (content built) (content restored))))
      (testing "the justification graph agrees"
        (is (= (justification-content built) (justification-content restored))))
      (testing "the taxonomy closures agree"
        (is (= (taxonomy-content built) (taxonomy-content restored))))
      (finally
        (tu/clear-kb! built)
        (tu/clear-kb! restored)))))
