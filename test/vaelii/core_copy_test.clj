;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.core-copy-test
  "`tu/load-core!` produces the KB `core-context/load-into` produces.

  The suite's `neutral-fresh` fixtures restore the upper layer from an export dump built
  once per JVM instead of re-asserting it, because `load-into` runs every `kb/upper/` file
  through the full write path on every fresh vocabulary KB — `tu/core-context-dump` states
  why.  That trade is only sound while the two routes agree, and nothing else in the suite would
  notice them diverging: a namespace loading a subtly different baseline still passes its
  own tests, and the difference surfaces later as a test that fails for a reason nobody
  can place.

  So this compares the two KBs on everything a test can read off one — the stored
  sentences with their contexts, truth and strength, what is believed, the taxonomy
  closures, and the justification graph.  Content, never handles: a handle is minted in
  assertion order and `import!` preserves the dump's, so comparing them would assert
  something no caller may depend on (README, \"Order independence\").

  ## On failure

  A route grew something the other did not.  Check `export!`'s variant coverage first: a
  dump holds what the record store holds, so this test breaks when some *derived* state
  is added that `recover` does not rebuild.  Do not repair it by narrowing the
  comparison — the difference this reports is a difference in the fixtures' baseline."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
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
  resolved to sentences on both sides for `content`'s reason, and a rule's handle as an
  informant is one of them."
  [kb]
  (let [recs (:records kb)
        of   (fn [h] (let [sx (p/get-sentex recs h)] [(sx/sentence-of sx) (:context sx)]))
        by   (fn [i] (if (integer? i) (of i) i))]
    (into #{}
          (mapcat (fn [h]
                    (for [j (v/supporting-justifications kb h)]
                      [(of h) (by (:informant j)) (set (map of (:antecedents j)))])))
          (v/handles kb))))

(defn- taxonomy-content
  "The two cached closures a reader sees: the type hierarchy and the context hierarchy."
  [kb]
  (let [t (reasoning/taxonomy kb)]
    {:types    (into {} (for [x (tax/types t)]    [x (set (tax/genls-global t x))]))
     :contexts (into {} (for [c (tax/contexts t)] [c (set (tax/context-up t c))]))}))

(deftest a-restored-core-context-is-the-asserted-one
  ;; two spaces of this namespace's own, and neither is `tu/core-build-space` — the
  ;; dump's own build KB lives there and `clear-kb!` on it would wipe the dump's source
  ;; mid-comparison.  Cleared on open for `tu/fresh`'s reason.
  (let [space    (fn [k] (assoc tu/core-build-space :space [::copy k]))
        built    (doto (v/open-kb (space :built))    (tu/clear-kb!) (core-context/load-into))
        restored (doto (v/open-kb (space :restored)) (tu/clear-kb!) (tu/load-core!))]
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

(deftest a-dump-is-built-under-the-root-reading-whatever-its-first-caller-binds
  ;; A dump is built once per JVM by whichever fixture asks first, and a namespace may
  ;; force the other argument-type reading around its fixture (`inter_args_test` forces the
  ;; constraint-only one).  The dump is still the KB `build` makes under the root
  ;; reading, or every later restore inherits the first caller's binding.
  (let [space  (fn [k] (assoc tu/core-build-space :space [::dump-reading k]))
        build  (fn [kb]
                 (v/assert kb '(genl dr_kind thing) 'CxUniverse)
                 (v/assert kb '(arg drHolds 1 dr_kind) 'CxUniverse)
                 (v/assert kb '(drHolds DrOne DrTwo) 'CxUniverse))
        direct (doto (v/open-kb (space :direct)) (tu/clear-kb!) (build))
        dumped (doto (v/open-kb (space :dumped)) (tu/clear-kb!))]
    (try
      (binding [argument/*assertive-arg-types?* (not argument/*assertive-arg-types?*)]
        (tu/load-dumped! dumped ::dump-reading build))
      (is (= (content direct) (content dumped)))
      (finally
        (tu/clear-kb! direct)
        (tu/clear-kb! dumped)))))

(deftest a-dump-built-under-an-altered-root-is-not-restored-once-the-root-is-back
  ;; `web_jobs_test` alters the root reading around its namespace, and a dump its fixture
  ;; builds first is built under that root.  A restore under the other root reads a dump
  ;; of its own, or the namespaces after it start from a KB missing the mints their
  ;; settles then write, and `neutral`'s teardown reports them as leaked.
  (let [space   (fn [k] (assoc tu/core-build-space :space [::root-reading k]))
        build   (fn [kb]
                  (v/assert kb '(genl rr_kind thing) 'CxUniverse)
                  (v/assert kb '(arg rrHolds 1 rr_kind) 'CxUniverse)
                  (v/assert kb '(rrHolds RrOne RrTwo) 'CxUniverse))
        direct  (doto (v/open-kb (space :direct)) (tu/clear-kb!) (build))
        altered (doto (v/open-kb (space :altered)) (tu/clear-kb!))
        dumped  (doto (v/open-kb (space :dumped)) (tu/clear-kb!))
        root    (.getRawRoot #'argument/*assertive-arg-types?*)]
    (try
      (alter-var-root #'argument/*assertive-arg-types?* not)
      (try (tu/load-dumped! altered ::root-reading build)
           (finally (alter-var-root #'argument/*assertive-arg-types?* (constantly root))))
      (tu/load-dumped! dumped ::root-reading build)
      (is (= (content direct) (content dumped)))
      (finally
        (run! tu/clear-kb! [direct altered dumped])))))
