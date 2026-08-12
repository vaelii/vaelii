;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.starter-test
  "The starter schema loads and, with the test-world's cast beneath it, its rules and
  taxonomy behave."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.seed :as seed]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(defn- authored-sentences
  "Every sentence the shipped ontology's own source files contain, paired with the context
  whose file holds it — `CxCore.txt` plus every discovered file under `kb/upper/` and
  `kb/middle/`.  Read from the classpath the way the starter reads them, so a file added
  to a layer is swept with no edit here."
  []
  (concat (for [s (seed/read-sentences 'CxCore nil)] ['CxCore s])
          (for [dir ["upper" "middle"]
                c   (seed/layer-contexts dir)
                s   (seed/read-sentences c dir)]
            [c s])))

(tu/deftest-kb every-sentence-the-starter-ships-is-well-formed-once-it-is-all-loaded
  ;; **Loading is not checking**, and the gap between the two is where the shipped
  ;; ontology can go wrong quietly.  `seed/load-sentences` asserts in file order and
  ;; retries, so a sentence is judged against whatever had arrived when its turn came —
  ;; and the argument checks are open-world, abstaining on a term the KB cannot yet place.
  ;; `(hasCapability bird flying)` was admitted exactly that way: `argIsa … 1 animal` had
  ;; nothing to say about `bird` before `(genl bird animal)` landed, and once it landed
  ;; nothing went back to look.  There is no retroactive `:arg-type` report, so
  ;; `violations` stayed empty and the KB shipped seven facts its own checker convicts.
  ;;
  ;; This is the check that closes it: every sentence an author wrote, put to `check`
  ;; against the FULLY loaded KB, where every declaration and every placement is in.  The
  ;; ordering that admitted it cannot hide it here.
  ;;
  ;; Authored sentences rather than stored ones, which is what lets this cover the rules:
  ;; a rule reaches the store split into slots and an `exceptWhen` as a `sentexHandle`
  ;; reference, both engine encodings that no `.txt` contains.  The stored side is swept
  ;; by `ontology-test/every-fact-the-starter-ships-satisfies-the-declarations-it-ships`,
  ;; which catches what a rule *derives* — six of those seven facts — and the two together
  ;; cover what either alone would miss.
  (let [authored (authored-sentences)
        guilty   (for [[c s] authored
                       :let  [ps (try (v/check kb s c)
                                      (catch clojure.lang.ExceptionInfo e
                                        [{:type (:type (ex-data e) :threw)
                                          :message (ex-message e)}]))]
                       :when (seq ps)]
                   [s c (mapv :type ps) (:message (first ps))])]
    (is (< 1000 (count authored))
        "the sweep found the shipped files — an empty read would pass vacuously")
    (is (empty? guilty)
        (str "shipped sentences their own KB convicts: " (vec guilty)))))

(tu/deftest-kb starter-loads-and-reasons
  (testing "the universal rule fires on natural-world facts, landing in CxNaturalWorld"
    (is (seq (v/sentexes-matching kb '(grandparentOf Tom Ann) 'CxNaturalWorld)))
    (is (empty? (v/sentexes-matching kb '(grandparentOf Tom Ann) 'CxUniverse))))
  (testing "the genl taxonomy answers isa? queries"
    (is (v/isa? kb 'Muffet 'animal))
    (is (v/isa? kb 'Tom 'thing))
    (is (v/isa? kb 'Tweety 'animal))                  ; penguin -> bird -> animal
    (is (not (v/isa? kb 'Tom 'dog)))))

(tu/deftest-kb starter-common-sense-reasoning
  (testing "defeasible flight: eagles fly by default, penguins (flightless birds) do not"
    (is (seq   (v/sentexes-matching kb '(hasCapability Sam flying) 'CxNaturalWorld)))
    (is (empty? (v/sentexes-matching kb '(hasCapability Tweety flying) 'CxNaturalWorld)))
    (is (seq   (v/sentexes-matching kb '(not (hasCapability Tweety flying)) 'CxNaturalWorld)))
    (is (empty? (v/conflicts kb))))                   ; the strict exception resolves cleanly
  (testing "the mortality default reaches every living individual"
    (is (seq (v/sentexes-matching kb '(mortal Tom) 'CxNaturalWorld)))
    (is (seq (v/sentexes-matching kb '(mortal Muffet) 'CxNaturalWorld))))
  (testing "predicate metadata answers via the generic provers"
    (is (v/ask? kb '(ancestorOf Tom Ann)))            ; transitive closure of parentOf
    (is (v/ask? kb '(childOf Bob Tom)))               ; inverse of parentOf
    (is (v/ask? kb '(siblingOf Carol Ann)))           ; symmetric
    (is (v/ask? kb '(partOf Piston1 Car1))))          ; transitive
  (testing "functional birthYearOf rejects a second, different value"
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb '(birthYearOf Tom 1971) 'CxSocialWorld)))))

(tu/deftest-kb every-stored-sentence-satisfies-the-naming-invariants
  ;; `nm/problems` checks a functor per *literal*, so tightening it can invalidate
  ;; content that passes at the top level and not below it.  This is the gate on that: the
  ;; shipped schema (`resources/kb/**`) plus the whole test-world, every sentex the
  ;; load actually stored — **derived** conclusions included, which `assert` never
  ;; name-checks because they come out of the chainer rather than from a caller.
  (let [offenders (for [h  (p/sentex-ids (:records kb))
                        :let [sx (p/get-sentex (:records kb) h)
                              ps (nm/problems (:sentence sx) (:context sx))]
                        :when (seq ps)]
                    [h (:sentence sx) (:context sx) (vec ps)])]
    (is (< 500 (count (p/sentex-ids (:records kb)))) "the load is the size it should be")
    (is (= [] (vec offenders)))))

(tu/deftest-kb starter-documents-its-vocabulary
  (testing "every ontology type carries exactly one comment"
    (doseq [t '[thing intangible physical_object attribute temporal_thing relation_type
                substance artifact body_part food living_thing vehicle tool building
                animal plant mammal bird fish reptile insect human person dog cat
                lion mouse hare wolf tortoise ant grasshopper
                penguin eagle sparrow tree flower]]
      (is (= 1 (count (core-context/comment-of kb t))) (str "type " t))))
  (testing "every domain relation is documented"
    (doseq [p '[parentOf grandparentOf childOf ancestorOf siblingOf marriedTo
                motherOf fatherOf
                likes eats owns partOf locatedIn hasCapability capabilityType
                mortal birthYearOf olderThan
                weightOf heightOf heavierThan tallerThan]]
      (is (seq (core-context/comment-of kb p)) (str "relation " p)))))

(tu/deftest-kb every-shipped-unit-converts-to-a-base-in-its-own-dimension
  ;; The unit table is the one place the schema ships individuals, and a half-stated
  ;; unit is worse than an absent one: the provers read `dimensionOf` to decide
  ;; comparability and `conversionFactor` to normalize, so a unit with one and not the
  ;; other silently answers nothing rather than failing.  This is the gate on that.
  (let [dimension  (into {} (map (fn [sx] (let [[_ u d] (:sentence sx)] [u d])))
                         (v/sentexes-with-functor kb 'dimensionOf {:believed? true}))
        conversion (into {} (map (fn [sx] (let [[_ u b f] (:sentence sx)] [u [b f]])))
                         (v/sentexes-with-functor kb 'conversionFactor {:believed? true}))]
    (is (seq dimension) "the table is not empty")
    (is (= (set (keys dimension)) (set (keys conversion)))
        "every unit states both its dimension and its factor")
    (doseq [[unit [base factor]] conversion]
      (is (= (dimension unit) (dimension base))
          (str unit " converts to a base of another dimension"))
      (is (number? factor) (str unit "'s factor is a number"))
      (is (pos? factor) (str unit "'s factor is positive")))
    (testing "each dimension's base unit is its own base, at factor 1"
      (doseq [[_ [base _]] conversion]
        (is (= [base 1] (conversion base))
            (str base " is a base unit, so it converts to itself unchanged"))))))
