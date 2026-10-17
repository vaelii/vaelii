;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjointness-audit-test
  "`subsumption-status` classifies a pair of types, and `disjointness-audit` runs it
  over every unordered pair. The status cases: :genl / :spec (one subsumes the other),
  :coextensional (mutual), :disjoint (a declaration, closed under genl), :orthogonal
  (a provable shared instance, or a shared subtype not separated from itself, with no
  subsumption or disjointness), and :unknown."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- well-over-core
  "A KB holding the upper layer alone, with CxWell below CxUniverse as the starter places
  it, so the default vantage sweeps CxUniverse's types and a test's own.  A test that reads
  one pair off the audit runs here: the sweep is 102 types against the starter's 221."
  []
  (doto (tu/isolated-fresh)
    (tu/load-core!)
    (v/assert '(genlCx CxWell CxUniverse) 'CxUniverse {:strength :monotonic})))

;; ---- subsumption-status, one case each ------------------------------------

(tu/deftest-kb genl-and-spec-are-converse
  (tu/with-terms [animal dog]
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (is (= :genl (v/subsumption-status kb dog animal))
        "(genl dog animal) holds — dog is a subtype of animal")
    (is (= :spec (v/subsumption-status kb animal dog))
        "the converse — animal is a supertype of dog")))

(tu/deftest-kb disjoint-pair-reads-disjoint
  (tu/with-terms [plant mineral]
    (v/assert kb (list 'genl plant 'thing) 'CxUniverse)
    (v/assert kb (list 'genl mineral 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint plant mineral) 'CxUniverse)
    (is (= :disjoint (v/subsumption-status kb plant mineral)))))

(tu/deftest-kb orthogonal-needs-a-shared-instance-without-subsumption
  (tu/with-terms [striped aquatic Nemo]
    (v/assert kb (list 'genl striped 'thing) 'CxUniverse)
    (v/assert kb (list 'genl aquatic 'thing) 'CxUniverse)
    (is (= :unknown (v/subsumption-status kb striped aquatic))
        "no relation and no shared instance yet")
    (v/assert kb (list striped Nemo) 'CxUniverse)
    (v/assert kb (list aquatic Nemo) 'CxUniverse)
    (is (= :orthogonal (v/subsumption-status kb striped aquatic))
        "a provable shared instance, with neither subsuming nor disjoint")))

;; ---- a shared subtype is an overlap witness unless it is provably empty ----

(deftest a-shared-subtype-with-no-instance-reads-orthogonal
  (tu/with-neutral-kb [kb well-over-core]
    (tu/with-terms [spatialKind temporalKind bothKind]
      (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
      (is (= :unknown (v/subsumption-status kb spatialKind temporalKind))
          "no relation, no shared instance and no shared subtype yet")
      (v/assert kb (list 'genl bothKind spatialKind) 'CxUniverse)
      (v/assert kb (list 'genl bothKind temporalKind) 'CxUniverse)
      (is (= #{:orthogonal} (v/subsumption-statuses kb spatialKind temporalKind))
          "a subtype of both, not separated from itself, shows the two overlap")
      (is (= :orthogonal (v/subsumption-status kb temporalKind spatialKind)))
      (let [e (first (filter #(= #{spatialKind temporalKind} (hash-set (:a %) (:b %)))
                             (:pairs-data (v/disjointness-audit kb))))]
        (is (= [:orthogonal :unwitnessed-spec bothKind] ((juxt :status :witness :via) e))
            "a subtype not known nonempty is an overlap with no witness")))))

(deftest a-nonempty-shared-subtype-is-a-witness
  (tu/with-neutral-kb [kb well-over-core]
    (tu/with-terms [spatialKind temporalKind bothKind]
      (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl bothKind spatialKind) 'CxUniverse)
      (v/assert kb (list 'genl bothKind temporalKind) 'CxUniverse)
      (v/assert kb (list 'nonempty bothKind) 'CxUniverse)
      (let [e (first (filter #(= #{spatialKind temporalKind} (hash-set (:a %) (:b %)))
                             (:pairs-data (v/disjointness-audit kb))))]
        (is (= [:orthogonal :shared-spec bothKind] ((juxt :status :witness :via) e))
            "the audit names the witness kind and the subtype")))))

(deftest a-nonempty-shared-subtype-is-named-ahead-of-a-wider-one
  (tu/with-neutral-kb [kb well-over-core]
    ;; wideKind has a subtype of its own and is not known nonempty; narrowKind is nonempty
    (tu/with-terms [spatialKind temporalKind wideKind wideLeaf narrowKind]
      (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl wideKind spatialKind) 'CxUniverse)
      (v/assert kb (list 'genl wideKind temporalKind) 'CxUniverse)
      (v/assert kb (list 'genl wideLeaf wideKind) 'CxUniverse)
      (v/assert kb (list 'genl narrowKind spatialKind) 'CxUniverse)
      (v/assert kb (list 'genl narrowKind temporalKind) 'CxUniverse)
      (v/assert kb (list 'nonempty narrowKind) 'CxUniverse)
      (let [e (first (filter #(= #{spatialKind temporalKind} (hash-set (:a %) (:b %)))
                             (:pairs-data (v/disjointness-audit kb))))]
        (is (= [:shared-spec narrowKind] ((juxt :witness :via) e)))))))

(deftest a-shared-subtype-with-a-nonempty-subtype-is-a-witness
  (tu/with-neutral-kb [kb well-over-core]
    ;; nonempty climbs genl, so a nonempty subtype below the shared subtype makes it nonempty
    (tu/with-terms [spatialKind temporalKind bothKind leafKind]
      (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl bothKind spatialKind) 'CxUniverse)
      (v/assert kb (list 'genl bothKind temporalKind) 'CxUniverse)
      (v/assert kb (list 'genl leafKind bothKind) 'CxUniverse)
      (v/assert kb (list 'nonempty leafKind) 'CxUniverse)
      (let [e (first (filter #(= #{spatialKind temporalKind} (hash-set (:a %) (:b %)))
                             (:pairs-data (v/disjointness-audit kb))))]
        (is (= [:shared-spec bothKind] ((juxt :witness :via) e)))))))

(tu/deftest-kb a-shared-subtype-below-an-empty-type-is-no-witness
  ;; empty descends genl, so a shared subtype below an empty type is empty
  (tu/with-terms [spatialKind temporalKind bothKind emptyKind]
    (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl emptyKind 'thing) 'CxUniverse)
    (v/assert kb (list 'empty emptyKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind spatialKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind temporalKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind emptyKind) 'CxUniverse)
    (is (= :unknown (v/subsumption-status kb spatialKind temporalKind)))))

(tu/deftest-kb a-shared-subtype-stated-empty-is-no-witness
  (tu/with-terms [spatialKind temporalKind bothKind]
    (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl bothKind spatialKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind temporalKind) 'CxUniverse)
    (v/assert kb (list 'empty bothKind) 'CxUniverse)
    (is (= :unknown (v/subsumption-status kb spatialKind temporalKind))
        "an empty subtype is below every pair, so it shows no overlap")))

(deftest a-shared-subtype-with-an-instance-reads-as-a-shared-instance
  (tu/with-neutral-kb [kb well-over-core]
    (tu/with-terms [spatialKind temporalKind both_kind Thing1]
      (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl both_kind spatialKind) 'CxUniverse)
      (v/assert kb (list 'genl both_kind temporalKind) 'CxUniverse)
      (v/assert kb (list both_kind Thing1) 'CxUniverse)
      (is (= :orthogonal (v/subsumption-status kb spatialKind temporalKind)))
      (let [e (first (filter #(= #{spatialKind temporalKind} (hash-set (:a %) (:b %)))
                             (:pairs-data (v/disjointness-audit kb))))]
        (is (= [:shared-instance Thing1] ((juxt :witness :via) e))
            "the member found is reported ahead of the subtype it belongs to")))))

(tu/deftest-kb the-shared-instance-reported-is-the-same-in-every-assertion-order
  ;; two shared instances, asserted Zed first under one pair and Abe first under the
  ;; other: both pairs report the content-least, whichever the index returns first
  (tu/with-terms [one two three four Zed Abe]
    (doseq [t [one two three four]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [[[a b] ms] [[[one two] [Zed Abe]] [[three four] [Abe Zed]]]
            m ms t [a b]]
      (v/assert kb (list t m) 'CxUniverse))
    (let [via #(:via (#'v/subsumption-reading kb %1 %2 'CxUniverse (#'v/instance-reads kb 'CxUniverse)))]
      (is (= Abe (via one two) (via three four))))))

(tu/deftest-kb a-shared-subtype-below-two-separated-types-is-no-witness
  ;; bothKind is also below upperX and upperY, which are disjoint, so it has no member
  (tu/with-terms [spatialKind temporalKind bothKind upperX upperY]
    (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl upperX 'thing) 'CxUniverse)
    (v/assert kb (list 'genl upperY 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint upperX upperY) 'CxUniverse)
    (v/assert kb (list 'genl bothKind spatialKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind temporalKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind upperX) 'CxUniverse)
    (v/assert kb (list 'genl bothKind upperY) 'CxUniverse)
    (is (true? (v/disjoint? kb bothKind bothKind)) "the subtype is separated from itself")
    (is (= :unknown (v/subsumption-status kb spatialKind temporalKind))
        "an empty subtype is below every pair, so it shows no overlap")))

(tu/deftest-kb a-shared-subtype-of-a-genl-related-pair-reads-genl
  (tu/with-terms [outerKind innerKind bothKind]
    (v/assert kb (list 'genl outerKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl innerKind outerKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind innerKind) 'CxUniverse)
    (is (= #{:genl} (v/subsumption-statuses kb innerKind outerKind)))))

(tu/deftest-kb a-shared-subtype-of-a-disjoint-pair-reads-disjoint
  ;; a type below both halves of a disjoint pair is empty, so the pair stays consistent
  (tu/with-terms [plantKind mineralKind bothKind]
    (v/assert kb (list 'genl plantKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl mineralKind 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint plantKind mineralKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind plantKind) 'CxUniverse)
    (v/assert kb (list 'genl bothKind mineralKind) 'CxUniverse)
    (is (= #{:disjoint} (v/subsumption-statuses kb plantKind mineralKind)))))

(tu/deftest-kb a-known-starter-disjoint-pair
  ;; function and predicate are separated by (partition relation function predicate) in
  ;; CxUniverse.
  (is (= :disjoint (v/subsumption-status kb 'function 'predicate))))

;; ---- subsumption-statuses and inconsistency --------------------------------

(tu/deftest-kb subsumption-statuses-returns-singleton-for-consistent-pair
  (tu/with-terms [plant mineral]
    (v/assert kb (list 'genl plant 'thing) 'CxUniverse)
    (v/assert kb (list 'genl mineral 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint plant mineral) 'CxUniverse)
    (is (= #{:disjoint} (v/subsumption-statuses kb plant mineral))
        "a consistent disjoint pair yields a singleton set")))

(tu/deftest-kb inconsistent-pair-is-both-genl-and-disjoint
  (tu/with-terms [alphaKind betaKind]
    ;; Use bulk-assert-facts! to construct the inconsistent snapshot:
    ;; the production WFF guard correctly refuses (disjoint X Y) when
    ;; X and Y are genl-related, so the trusted bulk path is the
    ;; narrow existing bypass for testing inconsistency detection.
    (v/bulk-assert-facts! kb
                          [(list 'genl alphaKind 'thing)
                           (list 'genl betaKind 'thing)
                           (list 'genl alphaKind betaKind)
                           (list 'disjoint alphaKind betaKind)]
                          'CxUniverse)
    (is (= #{:genl :disjoint} (v/subsumption-statuses kb alphaKind betaKind))
        "the set contains both relationships")
    (is (= :inconsistent (v/subsumption-status kb alphaKind betaKind))
        "subsumption-status returns :inconsistent for a contradictory pair")))

;; ---- the audit ------------------------------------------------------------

(deftest audit-covers-every-unordered-pair-with-a-status
  (tu/with-neutral-kb [kb well-over-core]
    (let [a (v/disjointness-audit kb)
          n (:types a)]
      (is (pos? n) "CxUniverse has types")
      (is (= (:pairs a) (/ (* n (dec n)) 2)) "every unordered distinct pair")
      (is (= (:pairs a) (reduce + (vals (:by-status a)))) "every pair got exactly one status")
      (is (every? #{:genl :spec :coextensional :disjoint :orthogonal :unknown :inconsistent}
                  (keys (:by-status a)))
          "only the defined statuses appear")
      (is (contains? (:by-status a) :disjoint) "CxUniverse has some disjoint pairs"))))

(deftest the-audit-sweeps-types-not-the-relations-a-genl-edge-names
  (tu/with-neutral-kb [kb well-over-core]
    ;; `genl` also specializes one relation by another — (genl performedBy doneBy),
    ;; (genl partition covering) — and such a relation is a node of the genl closure without
    ;; being a type: it has no instances to share or keep apart, so every pair it entered
    ;; read :unknown.  A declared arity of two or more says so, read from the same
    ;; declarations the arity check reads, and so does a variable_arity declaration.
    (tu/with-terms [doneBy performedBy coverOf partitionOf agentKind]
      (v/assert kb (list 'binary_predicate doneBy) 'CxUniverse)
      (v/assert kb (list 'binary_predicate performedBy) 'CxUniverse)
      (v/assert kb (list 'genl performedBy doneBy) 'CxUniverse)
      (v/assert kb (list 'variable_arity_predicate coverOf) 'CxUniverse)
      (v/assert kb (list 'variable_arity_predicate partitionOf) 'CxUniverse)
      (v/assert kb (list 'genl partitionOf coverOf) 'CxUniverse)
      (v/assert kb (list 'genl agentKind 'thing) 'CxUniverse)
      (is (every? (set (v/types kb)) [doneBy coverOf]) "the relations are nodes of the genl closure")
      (let [a     (v/disjointness-audit kb)
            swept (into #{} (mapcat (juxt :a :b)) (:pairs-data a))]
        (is (contains? swept agentKind) "a type is swept")
        (is (not-any? swept [doneBy performedBy]) "a binary predicate is not")
        (is (not-any? swept [coverOf partitionOf]) "a variable-arity predicate is not")
        (is (= (:pairs a) (/ (* (:types a) (dec (:types a))) 2))
            ":types counts the nodes swept, not every genl node")))))

(deftest the-audit-reads-a-relations-arity-stated-below-the-vantage-context
  (tu/with-neutral-kb [kb well-over-core]
    ;; CxArityProbe sees CxUniverse, and CxUniverse does not see it.  Each exact-arity
    ;; membership has a copy in CxUniverse (`decontextualized_predicate`).
    (tu/with-terms [heldBy keptBy]
      (v/assert kb (list 'genlCx 'CxArityProbe 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl heldBy keptBy) 'CxUniverse)
      (v/assert kb (list 'binary_predicate heldBy) 'CxArityProbe)
      (v/assert kb (list 'binary_predicate keptBy) 'CxArityProbe)
      (let [swept (fn [ctx] (into #{} (mapcat (juxt :a :b))
                                  (:pairs-data (v/disjointness-audit kb ctx))))]
        (is (not-any? (swept 'CxUniverse) [heldBy keptBy])
            "CxUniverse sees the copies of both arities, so neither is swept there")
        (is (not-any? (swept 'CxArityProbe) [heldBy keptBy])
            "CxArityProbe sees both arities, so neither is swept there")))))

;; ---- the shared-instance witness is read from a vantage context ----------

(tu/deftest-kb orthogonal-witness-is-read-from-the-vantage-context
  (tu/with-terms [striped aquatic Nemo]
    ;; a fresh context below CxUniverse: it sees CxUniverse, and CxUniverse does not see it.
    (v/assert kb (list 'genlCx 'CxOrthoProbe 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl striped 'thing) 'CxUniverse)
    (v/assert kb (list 'genl aquatic 'thing) 'CxUniverse)
    (v/assert kb (list striped Nemo) 'CxOrthoProbe)
    (v/assert kb (list aquatic Nemo) 'CxOrthoProbe)
    (is (= :unknown (v/subsumption-status kb striped aquatic))
        "the default CxUniverse vantage cannot see the sub-context's shared instance")
    (is (= :orthogonal (v/subsumption-status kb striped aquatic 'CxOrthoProbe))
        "read from CxOrthoProbe, the shared instance settles the pair as orthogonal")))

(deftest the-audit-defaults-its-vantage-to-cxwell
  (tu/with-neutral-kb [kb well-over-core]
    (is (= (v/disjointness-audit kb)
           (v/disjointness-audit kb 'CxWell))
        "the no-context audit passes CxWell, the context below every middle context, as its
        vantage — every type and declaration CxWell sees, and no opt-in theory's")))

;; ---- the swept type set is read from the same vantage as its coverage -----

(deftest a-type-declared-only-in-an-opt-in-context-is-outside-the-default-sweep
  (tu/with-neutral-kb [kb well-over-core]
    ;; A fresh context below CxUniverse, the way an opt-in theory sits: it sees CxUniverse,
    ;; and CxWell does not see it, since no `genlCx CxWell ...` edge names it.
    (tu/with-terms [optInKind]
      (v/assert kb (list 'genlCx 'CxOptInProbe 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl optInKind 'thing) 'CxOptInProbe)
      (let [swept (fn [ctx] (into #{} (mapcat (juxt :a :b)) (:pairs-data (v/disjointness-audit kb ctx))))]
        (is (not (contains? (swept 'CxWell) optInKind))
            "CxWell does not see CxOptInProbe, so a type declared only there is outside the audit's type set")
        (is (contains? (swept 'CxOptInProbe) optInKind)
            "read from CxOptInProbe itself, the type is in scope")
        (is (not (contains? (swept 'CxUniverse) optInKind))
            "CxUniverse does not see CxOptInProbe either — the opt-in direction is the same at both vantages")))))

;; ---- a type node need not be a symbol ------------------------------------

(deftest the-audit-orders-a-nat-type-node-by-print-key-not-bare-sort
  (tu/with-neutral-kb [kb well-over-core]
    ;; A type node need not be a symbol: a NAT standing for a collection an imported ontology
    ;; has no atomic name for is a list, and `compare` throws on a list — so the N² sweep,
    ;; sorting `(types kb)` with bare `sort`, threw a bare ClassCastException on such a KB.
    ;; `by-print-key` orders it, as `disjoint-line` already does.  The bulk path is the bypass
    ;; that injects a compound genl node the WFF guard would refuse at `assert`.
    (tu/with-terms [collectionFn Foo]
      (v/bulk-assert-facts! kb [(list 'genl (list collectionFn Foo) 'thing)] 'CxUniverse)
      (is (some (complement symbol?) (v/types kb))
          "a list-shaped type node is present")
      (let [a (v/disjointness-audit kb)]
        (is (pos? (:types a)))
        (is (= (:pairs a) (reduce + (vals (:by-status a))))
            "every unordered pair got a status — the sweep ordered the list node, not threw")))))

;; `:coextensional` is two distinct types each `genl` the other — a `genl` cycle, which
;; `wff` refuses at assertion. It appears only from a belief-state cycle or an equality
;; merge, neither of which a net-neutral fixture stages safely, so it has no constructive
;; case here; the allowed-status assertion above pins it as a legal outcome.

;; ---- coverage ratchet -------------------------------------------------------
;;
;; The thresholds are the starter KB's current values, so a change that removes a
;; separation fails here. The pair count floor catches a removal that a new
;; well-separated type would hide in the percentages. Raise each number when coverage
;; grows. Lower one only in the commit that removes the separation, and name the
;; removed pairs in that commit.
;;
;; The audit sweeps the nodes of the genl hierarchy visible from its vantage (default
;; CxWell, the context below every middle context) less each `relation?` there, so the five
;; relations CxUniverse puts under a `genl` edge (`orthogonal`, `siblingDisjointException`
;; and the three arity-class predicates) are not swept: 231 types, 26,565 pairs, 22,156
;; of them disjoint (83.4%) and 1,616 unknown (6.1%). core.txt's `physical` is among the
;; 231. No opt-in theory's type is among them: CxWell does not see one, so the
;; sweep does not either.

(tu/deftest-kb disjointness-coverage-ratchet
  (let [a          (v/disjointness-audit kb)
        pairs      (:pairs a)
        by-status  (:by-status a)
        disjoint   (get by-status :disjoint 0)
        unknown    (get by-status :unknown 0)
        disjoint-% (* 100.0 (/ disjoint pairs))
        unknown-%  (* 100.0 (/ unknown pairs))]
    (is (>= disjoint 22156)
        (format "disjoint pairs must not fall below 22156 (got %d)" disjoint))
    (is (>= disjoint-% 83.40)
        (format "disjoint coverage must not regress below 83.40%% (got %.2f%%)" disjoint-%))
    (is (<= unknown-% 6.09)
        (format "unknown pairs must not grow above 6.09%% (got %.2f%%)" unknown-%))))
