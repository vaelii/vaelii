;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ontology-folk-taxonomy-test
  "The folk taxonomy of organisms the shipped ontology states: species under classes,
  classes under vertebrate, invertebrate and plant, and every pair of organism kinds
  related by subsumption or separated.  The KB is `ontology-test`'s, the starter and the
  test-world.  The tests are a namespace apart from `ontology-test` so that
  scripts/ci-shard.sh can put the pairwise sweep on a different CI shard."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private B 'CxBiology)

;; ---- the folk taxonomy of organisms ----------------------------------------
;; Species under classes, classes under vertebrate, invertebrate and plant, and a
;; disjoint_metatype at each level: the separations are consulted, not stated per pair.

(def ^:private folk-species
  '[ant bee cat cow crow dog duck eagle fox frog grasshopper hare horse human lion mouse
    oak owl penguin rabbit rose sheep snake sparrow spider tortoise wolf])

(tu/deftest-kb vertebrates-and-invertebrates-partition-animal
  (is (true? (v/disjoint? kb 'vertebrate 'invertebrate)))
  (doseq [c '[amphibian bird fish mammal reptile]]
    (is (true? (v/genl? kb c 'vertebrate)) (str c " has a backbone")))
  (doseq [c '[arachnid insect]]
    (is (true? (v/genl? kb c 'invertebrate)) (str c " has none")))
  (is (true? (v/disjoint? kb 'insect 'mammal)) "so an insect is never a mammal")
  (is (true? (v/disjoint? kb 'spider 'owl)) "and the separation reaches the species")
  (testing "an animal denied a backbone is an invertebrate — the coverage half"
    (tu/with-terms [Limpet]
      (v/assert kb (list 'animal Limpet) 'CxUniverse)
      (v/assert kb (list 'not (list 'vertebrate Limpet)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'invertebrate Limpet) 'CxUniverse))))))

(tu/deftest-kb the-folk-classes-separate-their-kinds
  (is (true? (v/disjoint? kb 'tree 'flower)) "plant_class separates the plant classes")
  (is (true? (v/disjoint? kb 'oak 'rose)) "and the kinds below them")
  (is (true? (v/disjoint? kb 'insect 'arachnid)) "invertebrate_class separates its classes")
  (doseq [m '[vertebrate_class invertebrate_class plant_class]]
    (is (true? (v/genl? kb m 'folk_biological_class)) (str m " is a folk_biological_class")))
  (is (true? (v/disjoint? kb 'vertebrate_class 'plant_class))
      "and no class is of two of them"))

(tu/deftest-kb no-organism-is-of-two-folk-species
  (is (true? (v/disjoint? kb 'cat 'cow)))
  (is (true? (v/disjoint? kb 'crow 'owl)))
  (is (true? (v/disjoint? kb 'human 'horse)))
  (is (true? (v/disjoint? kb 'folk_biological_class 'folk_species))
      "and a species is never a class")
  (tu/with-terms [Bessie]
    (v/assert kb (list 'cow Bessie) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'horse Bessie) 'CxUniverse)))))

(tu/deftest-kb the-folk-taxonomy-settles-every-pair-of-organism-kinds
  ;; Every pair of the kinds below organism is subsumption-related or separated.  grass is
  ;; a plant_class beside tree and flower, so it is apart from each and from oak and rose.
  ;; The seven biology properties life.txt places under biological, organism and animal are
  ;; states and capacities of an organism rather than kinds of one, so they are left out: each
  ;; crosses the folk taxonomy, and its pairs with it stay unknown.  Two life stages of one
  ;; kind (caterpillar and butterfly) are neither: one organism is both, one after the other,
  ;; so their pair is left unknown on purpose and only pairs of stages of a kind are skipped.
  (let [props   '#{alive dead mortal asleep awake breathes_air warm_blooded}
        org     (set (remove props (filter #(v/genl? kb % 'organism) (v/types kb))))
        stage-of (fn [s] (set (for [r '[larvalFormOf adultFormOf]
                                    k org
                                    :when (v/ask? kb (list r s k) B)]
                                k)))
        same-kind-stages? (fn [a b] (boolean (some (stage-of a) (stage-of b))))
        unknown (for [{:keys [a b status]} (:pairs-data (v/disjointness-audit kb))
                      :when (and (org a) (org b) (= :unknown status)
                                 (not (same-kind-stages? a b)))]
                  (set [a b]))]
    (is (every? org folk-species) "every species is an organism")
    (is (true? (v/disjoint? kb 'grass 'oak)) "grass is not a tree, so not an oak")
    (is (= [] (vec unknown)))))

;; ---- folk_species is forced-monotonic ------------------------
;; A species membership is definitional, so CxUniverse writes each :monotonic and a rule
;; concluding a forced-monotonic literal from one alone fires as a forced-monotonic rule.

(tu/deftest-kb a-folk-species-membership-is-held-monotonic
  (is (= :monotonic (v/defeat-class kb (v/handle-of kb '(folk_species dog) 'CxUniverse))))
  (testing "a denial of one loses to it"
    (let [d (v/assert kb '(not (folk_species dog)) 'CxUniverse)]
      (is (not (v/in? kb d)))
      (is (true? (v/ask? kb '(folk_species dog) 'CxUniverse))))))

(tu/deftest-kb a-rule-from-folk-species-to-orthogonal-is-a-forced-monotonic-rule
  ;; A rule that declares every species orthogonal to a kind of tangible thing: its one
  ;; antecedent is a forced-monotonic literal, and its firings are believed with no
  ;; :forced-conclusion entry.
  (tu/with-terms [tended]
    (v/assert kb (list 'genl tended 'tangible) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies '(folk_species ?s) (list 'orthogonal '?s tended)))
              'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal 'dog tended) 'CxUniverse)))
    (is (= :orthogonal (v/subsumption-status kb 'dog tended)))
    (is (not-any? #(= :forced-conclusion (:violation %)) (v/violations kb)))))

(tu/deftest-kb a-warm-blooded-animal-is-a-vertebrate-by-default
  (let [edges (filter #(v/premise? kb (:id %)) (v/sentexes-matching kb '(genl warm_blooded vertebrate) 'CxUniverse))]
    (is (= 1 (count edges)) "(genl warm_blooded vertebrate) is stated in CxUniverse")
    (is (= :default (:strength (first edges))) "at default strength"))
  (tu/with-terms [Warm1 Cat1 Trout1]
    (v/assert kb (list 'warm_blooded Warm1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'vertebrate Warm1) 'CxUniverse)))
    (testing "and the class rules that derive and deny warm_blooded raise no clash"
      (v/assert kb (list 'mammal Cat1) 'CxBiology)
      (v/assert kb (list 'fish Trout1) 'CxBiology)
      (is (true? (v/ask? kb (list 'warm_blooded Cat1) 'CxBiology)))
      (is (true? (v/ask? kb (list 'not (list 'warm_blooded Trout1)) 'CxBiology)))
      (is (empty? (v/conflicts kb))))))
