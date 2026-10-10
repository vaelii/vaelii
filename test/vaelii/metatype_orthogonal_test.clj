;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.metatype-orthogonal-test
  "The higher-order type relations that state many pairs at once: `typeOrthogonal`
  makes every member of a classifier orthogonal to one type, `orthogonalMetatypes`
  makes every member of each named metatype orthogonal to every member of the others,
  and `partitionedByType` places every member of a classifier under a whole and
  separates the members.  Each is a CxCore rule generator, so the pairs it concludes
  are derived and the KB does not state them.  The upper types `logical` and
  `quantitative` and the documentation predicate `implementationNote` are pinned here
  too."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- derived-not-stated?
  "Is `(pred a b)` believed in `ctx` with no premise stating it in any context?"
  [kb pred a b ctx]
  (and (true? (v/ask? kb (list pred a b) ctx))
       (not-any? #(v/premise? kb (:id %))
                 (concat (v/sentexes-matching kb (list pred a b) '?ctx)
                         (v/sentexes-matching kb (list pred b a) '?ctx)))))

(defn- forced-conclusions-naming
  "The :forced-conclusion violations whose sentence names one of `terms`: a firing the
  roster held void.  Filtered by term, since the violation log outlives the test that
  filed an entry."
  [kb terms]
  (filter #(and (= :forced-conclusion (:violation %))
                (some terms (flatten (seq (:sentence %)))))
          (v/violations kb)))

;; ---- typeOrthogonal ---------------------------------------------------------

(tu/deftest-kb a-member-of-the-classifier-is-orthogonal-to-the-type
  (tu/with-terms [origin_kind crafted grown edible]
    (doseq [t [crafted grown edible]] (v/assert kb (list 'genl t 'tangible) 'CxUniverse))
    (v/assert kb (list 'metatype origin_kind) 'CxUniverse)
    (v/assert kb (list 'forced_monotonic_predicate origin_kind) 'CxUniverse)
    (v/assert kb (list origin_kind crafted) 'CxUniverse)
    (v/assert kb (list 'typeOrthogonal origin_kind edible) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal crafted edible) 'CxUniverse)))
    (is (= :orthogonal (v/subsumption-status kb crafted edible)))
    (testing "a member that arrives later is concluded orthogonal too"
      (v/assert kb (list origin_kind grown) 'CxUniverse)
      (is (true? (v/ask? kb (list 'orthogonal grown edible) 'CxUniverse))))
    (is (empty? (forced-conclusions-naming kb #{crafted grown edible})))))

(def ^:private origin-crossers
  "The types every origin_type member (made, natural) is orthogonal to."
  '[organism biological body_part substance food animal])

(tu/deftest-kb what-cuts-across-made-and-natural-is-derived-from-origin-type
  (is (true? (v/ask? kb '(origin_type made) 'CxAbstract)))
  (is (true? (v/ask? kb '(origin_type natural) 'CxAbstract)))
  (doseq [t origin-crossers, o '[made natural]]
    (is (true? (v/ask? kb (list 'typeOrthogonal 'origin_type t) 'CxAbstract)))
    (is (derived-not-stated? kb 'orthogonal t o 'CxAbstract)
        (str "(orthogonal " t " " o ") is derived and not stated"))
    (is (= :orthogonal (v/subsumption-status kb t o)))))

(tu/deftest-kb made-and-natural-cut-across-plant
  ;; origin_type is CxAbstract's and plant CxOrganism's, so the fact and the pairs it
  ;; derives are read from the collector.
  (is (true? (v/ask? kb '(typeOrthogonal origin_type plant) 'CxUniverse)))
  (doseq [o '[made natural]]
    (is (derived-not-stated? kb 'orthogonal 'plant o 'CxUniverse)
        (str "(orthogonal plant " o ") is derived and not stated"))
    (is (= :orthogonal (v/subsumption-status kb 'plant o)))))

(tu/deftest-kb abducibility-is-orthogonal-to-every-arity-type
  (doseq [a '[unary binary ternary fixed_arity variable_arity bounded_arity unbounded_arity
              at_least_binary at_least_ternary]]
    (is (true? (v/ask? kb (list 'arity_type a) 'CxCore)) (str a " is an arity_type"))
    (is (derived-not-stated? kb 'orthogonal a 'abducible_predicate 'CxCore)
        (str "(orthogonal " a " abducible_predicate) is derived"))
    (is (= :orthogonal (v/subsumption-status kb a 'abducible_predicate)))))

(tu/deftest-kb a-type-of-each-order-may-be-empty-or-nonempty
  (doseq [o '[type metatype meta_metatype], e '[empty nonempty]]
    (is (derived-not-stated? kb 'orthogonal o e 'CxCore)
        (str "(orthogonal " o " " e ") is derived from (typeOrthogonal type_type_by_order " e ")"))))

;; ---- orthogonalMetatypes ----------------------------------------------------

(tu/deftest-kb two-orthogonal-metatypes-cross-every-member-pair
  (tu/with-terms [shape_kind hue_kind round square red blue]
    (doseq [t [round square red blue]] (v/assert kb (list 'genl t 'tangible) 'CxUniverse))
    (doseq [m [shape_kind hue_kind]]
      (v/assert kb (list 'metatype m) 'CxUniverse)
      (v/assert kb (list 'forced_monotonic_predicate m) 'CxUniverse))
    (doseq [[m t] [[shape_kind round] [shape_kind square] [hue_kind red] [hue_kind blue]]]
      (v/assert kb (list m t) 'CxUniverse))
    (v/assert kb (list 'orthogonalMetatypes shape_kind hue_kind) 'CxUniverse)
    (doseq [s [round square], h [red blue]]
      (is (true? (v/ask? kb (list 'orthogonal s h) 'CxUniverse))))
    (is (not (v/ask? kb (list 'orthogonal round square) 'CxUniverse))
        "two members of one metatype are not made orthogonal")))

(tu/deftest-kb three-orthogonal-metatypes-cross-every-pair-of-metatypes
  (tu/with-terms [shape_kind hue_kind size_kind round red big]
    (doseq [t [round red big]] (v/assert kb (list 'genl t 'tangible) 'CxUniverse))
    (doseq [[m t] [[shape_kind round] [hue_kind red] [size_kind big]]]
      (v/assert kb (list 'metatype m) 'CxUniverse)
      (v/assert kb (list 'forced_monotonic_predicate m) 'CxUniverse)
      (v/assert kb (list m t) 'CxUniverse))
    (v/assert kb (list 'orthogonalMetatypes shape_kind hue_kind size_kind) 'CxUniverse)
    (doseq [[a b] [[round red] [round big] [red big]]]
      (is (true? (v/ask? kb (list 'orthogonal a b) 'CxUniverse))
          (str a " and " b " are orthogonal")))))

(tu/deftest-kb location-in-space-and-location-in-time-cross
  (is (true? (v/ask? kb '(orthogonalMetatypes spatiality_type temporality_type) 'CxCore)))
  (doseq [s '[spatial aspatial], t '[temporal atemporal]]
    (is (derived-not-stated? kb 'orthogonal s t 'CxCore)
        (str "(orthogonal " s " " t ") is derived"))))

;; ---- partitionedByType ------------------------------------------------------

(tu/deftest-kb a-classifier-partitioning-a-whole-places-and-separates-its-members
  (tu/with-terms [stuff_whole stuff_kind wet dry]
    (v/assert kb (list 'genl stuff_whole 'tangible) 'CxUniverse)
    (v/assert kb (list 'metatype stuff_kind) 'CxUniverse)
    (v/assert kb (list stuff_kind wet) 'CxUniverse)
    (v/assert kb (list stuff_kind dry) 'CxUniverse)
    (v/assert kb (list 'partitionedByType stuff_whole stuff_kind) 'CxUniverse)
    (is (true? (v/genl? kb wet stuff_whole 'CxUniverse)))
    (is (true? (v/genl? kb dry stuff_whole 'CxUniverse)))
    (is (true? (v/disjoint? kb wet dry 'CxUniverse)) "the separation reads the derived clique mark")
    (is (true? (v/ask? kb (list 'disjoint_metatype stuff_kind) 'CxUniverse)))
    (is (empty? (forced-conclusions-naming kb #{wet dry})))))

(tu/deftest-kb the-shipped-partitions-by-type-are-binary
  (doseq [[w c members ctx] '[[tangible origin_type [made natural] CxAbstract]
                              [thing spatiality_type [spatial aspatial] CxCore]
                              [thing temporality_type [temporal atemporal] CxCore]
                              [fixed_order_type type_type_by_order [type metatype meta_metatype] CxCore]]]
    (is (true? (v/ask? kb (list 'partitionedByType w c) ctx)))
    (doseq [m members]
      (is (true? (v/genl? kb m w ctx)) (str m " is under " w)))
    (doseq [a members, b members :when (neg? (compare a b))]
      (is (true? (v/disjoint? kb a b ctx)) (str a " and " b " are disjoint")))))

(tu/deftest-kb the-order-ladder-genls-are-derived-from-the-partition-by-type
  (doseq [o '[type metatype meta_metatype]]
    (is (derived-not-stated? kb 'genl o 'fixed_order_type 'CxCore)
        (str "(genl " o " fixed_order_type) is derived"))))

;; ---- logical and quantitative -------------------------------------------------

(tu/deftest-kb logical-linguistic-and-quantitative-are-separated-under-nowhere-never
  (doseq [t '[logical linguistic quantitative]]
    (is (true? (v/genl? kb t 'nowhere_never 'CxCore))))
  (doseq [[a b] '[[logical linguistic] [logical quantitative] [linguistic quantitative]]]
    (is (true? (v/disjoint? kb a b 'CxCore))))
  (doseq [t '[relation context]]
    (is (true? (v/genl? kb t 'logical 'CxCore))))
  (is (true? (v/genl? kb 'proposition 'logical 'CxReflection)))
  (is (true? (v/genl? kb 'measure 'quantitative 'CxCore)))
  (doseq [t '[unit_of_measure physical_dimension sign_value]]
    (is (true? (v/genl? kb t 'quantitative 'CxMeasure))))
  (is (not (v/genl? kb 'quantity 'quantitative)) "a quantity is temporal and not quantitative"))

;; ---- the orthogonal pairs the disjointness audit ruled -------------------------

(tu/deftest-kb the-audited-overlapping-pairs-read-orthogonal
  (doseq [[a b] '[[made vertebrate] [made invertebrate] [made solid]
                  [animal mortal] [animal dead] [animal alive] [animal food]
                  [biological container] [literal wff_expression]]]
    (is (= :orthogonal (v/subsumption-status kb a b)) (str a " and " b " read orthogonal"))))

;; ---- implementationNote ------------------------------------------------------

(tu/deftest-kb an-implementation-note-is-a-sibling-of-comment
  (is (true? (v/ask? kb '(binary_predicate implementationNote) 'CxCore)))
  (is (true? (v/ask? kb '(termsRelated comment implementationNote) 'CxCore)))
  (is (not (v/genl? kb 'implementationNote 'comment)))
  (is (not (v/genl? kb 'comment 'implementationNote)))
  (doseq [t '[formula sentence non_atomic_term unrepresented_term symbol logical_constant]]
    (is (seq (v/sentexes-matching kb (list 'implementationNote t '?note) 'CxCore))
        (str t " carries an implementation note"))))

(tu/deftest-kb the-rules-stated-for-some-arities-name-the-issue-for-the-rest
  (doseq [t '[orthogonalMetatypes partitionedByType]]
    (let [notes (map (comp #(nth % 2) :sentence)
                     (v/sentexes-matching kb (list 'implementationNote t '?note) 'CxCore))]
      (is (some #(re-find #"github\.com/vaelii/vaelii/issues/\d+" %) notes)
          (str t " carries an implementation note naming its issue"))))
  (doseq [t '[typeOrthogonal partitionedByType spatiality_type temporality_type]]
    (let [notes (map (comp #(nth % 2) :sentence)
                     (v/sentexes-matching kb (list 'implementationNote t '?note) 'CxCore))]
      (is (some #(re-find #"issues/173" %) notes)
          (str t " names the order-dependence issue its workaround waits on")))))
