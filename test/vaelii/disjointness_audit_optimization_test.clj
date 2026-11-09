;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjointness-audit-optimization-test
  "Row-prepared audit reads preserve the unprepared pair reading on small KBs."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.integrity :as integrity]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/empty-kb))

(defn- reference-rows
  "Read the public audit's pairs through the unprepared classifier."
  [kb context]
  (let [ts (vec (remove #(v/relation? kb % context) (nm/by-print-key (v/types kb context))))
        rd (#'v/instance-reads kb context)]
    (vec (for [i (range (count ts)), j (range (inc i) (count ts))
               :let [a (nth ts i), b (nth ts j)
                     {ss :statuses w :witness t :via}
                     (integrity/subsumption-reading kb a b context rd)]]
           (cond-> {:a a :b b :statuses ss
                    :status (case (count ss) 0 :unknown 1 (first ss) :inconsistent)}
             w (assoc :witness w)
             t (assoc :via t))))))

(defn- pair-row [audit a b]
  (first (filter #(= #{a b} (hash-set (:a %) (:b %))) (:pairs-data audit))))

(defn- assert-reference [kb context]
  (let [audit (v/disjointness-audit kb context)]
    (is (= (reference-rows kb context) (:pairs-data audit)))
    (is (= (quot (* (:types audit) (dec (:types audit))) 2) (:pairs audit)))
    (is (= (frequencies (map :status (:pairs-data audit))) (:by-status audit)))
    audit))

(tu/deftest-kb empty-and-single-type-audits-prepare-no-row
  (tu/with-terms [alone_kind]
    (let [prepare @#'v/audit-row-reads
          calls (atom 0)]
      (with-redefs-fn {#'v/audit-row-reads (fn [& args] (swap! calls inc) (apply prepare args))}
        (fn []
          (is (= {:types 0 :pairs 0 :by-status {} :pairs-data []}
                 (v/disjointness-audit kb 'CxUniverse)))
          (v/bulk-assert-facts! kb [(list 'genl alone_kind alone_kind)] 'CxUniverse)
          (is (= {:types 1 :pairs 0 :by-status {} :pairs-data []}
                 (v/disjointness-audit kb 'CxUniverse)))
          (is (zero? @calls)))))))

(tu/deftest-kb the-public-audit-builds-one-separation-frame-per-nonempty-row
  (tu/with-terms [root_kind first_kind second_kind third_kind]
    (doseq [t [first_kind second_kind third_kind]]
      (v/assert kb (list 'genl t root_kind) 'CxUniverse))
    (let [frame @#'tax/separation-frame
          calls (atom 0)
          audit (with-redefs-fn
                  {#'tax/separation-frame (fn [& args] (swap! calls inc) (apply frame args))}
                  #(v/disjointness-audit kb 'CxUniverse))]
      (is (= 4 (:types audit)))
      (is (= 6 (:pairs audit)))
      (is (= 3 @calls) "six pair decisions prepare three actual taxonomy frames")
      (is (= (reference-rows kb 'CxUniverse) (:pairs-data audit)))
      (is (= 3 (get (:by-status audit) :unknown))
          "the three unrelated leaves have neither a declaration nor an overlap"))))

(tu/deftest-kb declared-contradictions-and-retraction-retain-complete-status-sets
  (tu/with-terms [root_kind first_kind second_kind]
    (doseq [t [first_kind second_kind]]
      (v/assert kb (list 'genl t root_kind) 'CxUniverse))
    (v/assert kb '(symmetric orthogonal) 'CxUniverse)
    (let [separation (v/assert kb (list 'disjoint first_kind second_kind) 'CxUniverse)]
      (v/assert kb (list 'orthogonal first_kind second_kind) 'CxUniverse)
      (let [row (pair-row (assert-reference kb 'CxUniverse) first_kind second_kind)]
        (is (= #{:disjoint :orthogonal} (:statuses row)))
        (is (= :inconsistent (:status row)))
        (is (= :declared (:witness row))))
      (v/retract! kb separation)
      (is (= #{:orthogonal}
             (:statuses (pair-row (assert-reference kb 'CxUniverse) first_kind second_kind)))))))

(tu/deftest-kb global-subtypes-and-contextual-empty-reads-retain-their-vantages
  (tu/with-terms [root_kind first_kind second_kind both_kind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (doseq [t [first_kind second_kind]]
        (v/assert kb (list 'genl t root_kind) 'CxUniverse))
      (doseq [t [first_kind second_kind]]
        (v/assert kb (list 'genl both_kind t) cx))
      (let [row (pair-row (assert-reference kb 'CxUniverse) first_kind second_kind)]
        (is (= #{:orthogonal} (:statuses row)))
        (is (= :unwitnessed-spec (:witness row)))
        (is (= both_kind (:via row))))
      (v/assert kb (list 'empty both_kind) cx)
      (is (= #{:orthogonal}
             (:statuses (pair-row (assert-reference kb 'CxUniverse) first_kind second_kind))))
      (is (= #{} (:statuses (pair-row (assert-reference kb cx) first_kind second_kind)))))))

(tu/deftest-kb witness-priority-and-content-order-survive-row-preparation
  (tu/with-terms [root_kind first_kind second_kind wide_kind leaf_kind narrow_kind Zed Abe]
    (doseq [t [first_kind second_kind]]
      (v/assert kb (list 'genl t root_kind) 'CxUniverse))
    (doseq [t [wide_kind narrow_kind], parent [first_kind second_kind]]
      (v/assert kb (list 'genl t parent) 'CxUniverse))
    (v/assert kb (list 'genl leaf_kind wide_kind) 'CxUniverse)
    (let [row (pair-row (assert-reference kb 'CxUniverse) first_kind second_kind)]
      (is (= [:unwitnessed-spec wide_kind] ((juxt :witness :via) row))))
    (v/assert kb (list 'nonempty narrow_kind) 'CxUniverse)
    (let [row (pair-row (assert-reference kb 'CxUniverse) first_kind second_kind)]
      (is (= [:shared-spec narrow_kind] ((juxt :witness :via) row))))
    (doseq [member [Zed Abe], t [first_kind second_kind]]
      (v/assert kb (list t member) 'CxUniverse))
    (let [row (pair-row (assert-reference kb 'CxUniverse) first_kind second_kind)]
      (is (= [:shared-instance Abe] ((juxt :witness :via) row))))))

(tu/deftest-kb the-scoped-reader-ignores-global-row-callbacks
  (tu/with-terms [root_kind first_kind second_kind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (doseq [t [first_kind second_kind]]
        (v/assert kb (list 'genl t root_kind) 'CxUniverse))
      (v/assert kb (list 'genl first_kind second_kind) cx)
      (let [rd (#'v/instance-reads kb 'CxUniverse)
            fail (fn [& _] (throw (ex-info "a scoped read used a global row callback" {})))
            prepared (assoc rd :genl? fail :specs fail :disjoint? fail)]
        (is (= #{} (:statuses (integrity/subsumption-reading kb first_kind second_kind
                                                            'CxUniverse prepared true))))
        (is (= #{:genl} (:statuses (integrity/subsumption-reading kb first_kind second_kind
                                                                'CxUniverse rd))))))))

(tu/deftest-kb ambient-query-depth-does-not-turn-a-rule-into-an-overlap-witness
  (tu/with-terms [root_kind a_kind z_kind Member]
    (doseq [t [a_kind z_kind]]
      (v/assert kb (list 'genl t root_kind) 'CxUniverse))
    (v/assert kb (list z_kind Member) 'CxUniverse)
    (v/assert-rule kb [(list z_kind '?x)] (list a_kind '?x) 'CxUniverse
                   {:direction :backward})
    (binding [v/*query-options* {:max-depth 9}]
      (is (= #{} (:statuses (pair-row (assert-reference kb 'CxUniverse) a_kind z_kind)))))))

(tu/deftest-kb compound-type-nodes-retain-the-reference-order-and-global-reads
  (tu/with-terms [root_kind first_kind collectionFn Item]
    (v/assert kb (list 'genl first_kind root_kind) 'CxUniverse)
    (let [nat (list collectionFn Item)]
      (v/bulk-assert-facts! kb [(list 'genl nat first_kind)] 'CxUniverse)
      (let [audit (assert-reference kb 'CxUniverse)
            rd (#'v/audit-row-reads kb 'CxUniverse (#'v/instance-reads kb 'CxUniverse) nat)]
        (is (some #(= nat (:a %)) (:pairs-data audit)))
        (is (true? ((:genl? rd) nat root_kind)))
        (is (true? ((:genl? rd) nat nat)))
        (is (true? ((:genl? rd) root_kind root_kind)))
        (is (false? ((:genl? rd) first_kind nat)))))))
