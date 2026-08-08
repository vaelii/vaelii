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
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb starter-loads-and-reasons
  (testing "the universal rule fires on natural-world facts, landing in NaturalWorldContext"
    (is (seq (v/sentexes-matching kb '(grandparentOf Tom Ann) 'NaturalWorldContext)))
    (is (empty? (v/sentexes-matching kb '(grandparentOf Tom Ann) 'UniverseContext))))
  (testing "the genl taxonomy answers isa? queries"
    (is (v/isa? kb 'Muffet 'animal))
    (is (v/isa? kb 'Tom 'thing))
    (is (v/isa? kb 'Tweety 'animal))                  ; penguin -> bird -> animal
    (is (not (v/isa? kb 'Tom 'dog)))))

(tu/deftest-kb starter-common-sense-reasoning
  (testing "defeasible flight: eagles fly by default, penguins (flightless birds) do not"
    (is (seq   (v/sentexes-matching kb '(flies Sam) 'NaturalWorldContext)))
    (is (empty? (v/sentexes-matching kb '(flies Tweety) 'NaturalWorldContext)))
    (is (seq   (v/sentexes-matching kb '(not (flies Tweety)) 'NaturalWorldContext)))
    (is (empty? (v/conflicts kb))))                   ; the strict exception resolves cleanly
  (testing "the mortality default reaches every living individual"
    (is (seq (v/sentexes-matching kb '(mortal Tom) 'NaturalWorldContext)))
    (is (seq (v/sentexes-matching kb '(mortal Muffet) 'NaturalWorldContext))))
  (testing "predicate metadata answers via the generic provers"
    (is (v/ask? kb '(ancestorOf Tom Ann)))            ; transitive closure of parentOf
    (is (v/ask? kb '(childOf Bob Tom)))               ; inverse of parentOf
    (is (v/ask? kb '(siblingOf Carol Ann)))           ; symmetric
    (is (v/ask? kb '(partOf Piston1 Car1))))          ; transitive
  (testing "functional birthYearOf rejects a second, different value"
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb '(birthYearOf Tom 1971) 'SocialWorldContext)))))

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
                animal plant mammal bird fish reptile insect person dog cat
                lion mouse hare wolf tortoise ant grasshopper
                penguin eagle sparrow tree flower]]
      (is (= 1 (count (core-context/comment-of kb t))) (str "type " t))))
  (testing "every domain relation is documented"
    (doseq [p '[parentOf grandparentOf childOf ancestorOf siblingOf marriedTo
                motherOf fatherOf
                likes eats owns partOf locatedIn flies canTravel mortal birthYearOf olderThan
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
