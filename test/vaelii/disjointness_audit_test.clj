;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjointness-audit-test
  "`subsumption-status` classifies a pair of types, and `disjointness-audit` runs it
  over every unordered pair. The status cases: :genl / :spec (one subsumes the other),
  :coextensional (mutual), :disjoint (a declaration, closed under genl), :orthogonal
  (a provable shared instance with no subsumption or disjointness), and :unknown."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; ---- subsumption-status, one case each ------------------------------------

(tu/deftest-kb genl-and-spec-are-converse
  (tu/with-terms [animal dog]
    (v/assert kb (list 'genl 'animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'dog 'animal) 'CxUniverse)
    (is (= :genl (v/subsumption-status kb 'dog 'animal))
        "(genl dog animal) holds — dog is a subtype of animal")
    (is (= :spec (v/subsumption-status kb 'animal 'dog))
        "the converse — animal is a supertype of dog")))

(tu/deftest-kb disjoint-pair-reads-disjoint
  (tu/with-terms [plant mineral]
    (v/assert kb (list 'genl 'plant 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'mineral 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint 'plant 'mineral) 'CxUniverse)
    (is (= :disjoint (v/subsumption-status kb 'plant 'mineral)))))

(tu/deftest-kb orthogonal-needs-a-shared-instance-without-subsumption
  (tu/with-terms [striped aquatic Nemo]
    (v/assert kb (list 'genl 'striped 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'aquatic 'thing) 'CxUniverse)
    (is (= :unknown (v/subsumption-status kb 'striped 'aquatic))
        "no relation and no shared instance yet")
    (v/assert kb (list 'striped 'Nemo) 'CxUniverse)
    (v/assert kb (list 'aquatic 'Nemo) 'CxUniverse)
    (is (= :orthogonal (v/subsumption-status kb 'striped 'aquatic))
        "a provable shared instance, with neither subsuming nor disjoint")))

(tu/deftest-kb a-known-starter-disjoint-pair
  ;; function and predicate are declared disjoint in CxCore.
  (is (= :disjoint (v/subsumption-status kb 'function 'predicate))))

;; ---- subsumption-statuses and inconsistency --------------------------------

(tu/deftest-kb subsumption-statuses-returns-singleton-for-consistent-pair
  (tu/with-terms [plant mineral]
    (v/assert kb (list 'genl 'plant 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'mineral 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint 'plant 'mineral) 'CxUniverse)
    (is (= #{:disjoint} (v/subsumption-statuses kb 'plant 'mineral))
        "a consistent disjoint pair yields a singleton set")))

(tu/deftest-kb inconsistent-pair-is-both-genl-and-disjoint
  (tu/with-terms [alphaKind betaKind]
    ;; Use bulk-assert-facts! to construct the inconsistent snapshot:
    ;; the production WFF guard correctly refuses (disjoint X Y) when
    ;; X and Y are genl-related, so the trusted bulk path is the
    ;; narrow existing bypass for testing inconsistency detection.
    (v/bulk-assert-facts! kb
                          [(list 'genl 'alphaKind 'thing)
                           (list 'genl 'betaKind 'thing)
                           (list 'genl 'alphaKind 'betaKind)
                           (list 'disjoint 'alphaKind 'betaKind)]
                          'CxUniverse)
    (is (= #{:genl :disjoint} (v/subsumption-statuses kb 'alphaKind 'betaKind))
        "the set contains both relationships")
    (is (= :inconsistent (v/subsumption-status kb 'alphaKind 'betaKind))
        "subsumption-status returns :inconsistent for a contradictory pair")))

;; ---- the audit ------------------------------------------------------------

(tu/deftest-kb audit-covers-every-unordered-pair-with-a-status
  (let [a (v/disjointness-audit kb)
        n (:types a)]
    (is (pos? n) "the starter has types")
    (is (= (:pairs a) (/ (* n (dec n)) 2)) "every unordered distinct pair")
    (is (= (:pairs a) (reduce + (vals (:by-status a)))) "every pair got exactly one status")
    (is (every? #{:genl :spec :coextensional :disjoint :orthogonal :unknown :inconsistent}
                (keys (:by-status a)))
        "only the defined statuses appear")
    (is (contains? (:by-status a) :disjoint) "the starter has some disjoint pairs")))

;; ---- the shared-instance witness is read from a vantage context ----------

(tu/deftest-kb orthogonal-witness-is-read-from-the-vantage-context
  (tu/with-terms [striped aquatic Nemo]
    ;; a fresh context below CxUniverse: it sees CxUniverse, and CxUniverse does not see it.
    (v/assert kb (list 'genlCx 'CxOrthoProbe 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl 'striped 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'aquatic 'thing) 'CxUniverse)
    (v/assert kb (list 'striped 'Nemo) 'CxOrthoProbe)
    (v/assert kb (list 'aquatic 'Nemo) 'CxOrthoProbe)
    (is (= :unknown (v/subsumption-status kb 'striped 'aquatic))
        "the default CxUniverse vantage cannot see the sub-context's shared instance")
    (is (= :orthogonal (v/subsumption-status kb 'striped 'aquatic 'CxOrthoProbe))
        "read from CxOrthoProbe, the shared instance settles the pair as orthogonal")))

(tu/deftest-kb the-audit-defaults-its-vantage-to-cxuniverse
  (is (= (v/disjointness-audit kb)
         (v/disjointness-audit kb 'CxUniverse))
      "the no-context audit passes CxUniverse as the shared-instance vantage"))

;; `:coextensional` is two distinct types each `genl` the other — a `genl` cycle, which
;; `wff` refuses at assertion. It appears only from a belief-state cycle or an equality
;; merge, neither of which a net-neutral fixture stages safely, so it has no constructive
;; case here; the allowed-status assertion above pins it as a legal outcome.

;; ---- coverage ratchet -------------------------------------------------------
;;
;; Every PR either maintains or improves the disjointness coverage of the starter
;; KB.  These thresholds are the floor locked in after vaelii#94 (25%→64% disjoint).
;; Raise them when new disjoint declarations land; never lower them
;; unless it's to add legitimately orthogonal collections to the upper ontology.

(tu/deftest-kb disjointness-coverage-ratchet
  (let [a          (v/disjointness-audit kb)
        pairs      (:pairs a)
        by-status  (:by-status a)
        disjoint   (get by-status :disjoint 0)
        unknown    (get by-status :unknown 0)
        disjoint-% (* 100.0 (/ disjoint pairs))
        unknown-%  (* 100.0 (/ unknown pairs))]
    (is (>= disjoint-% 63.0)
        (format "disjoint coverage must not regress below 63%% (got %.1f%%)" disjoint-%))
    (is (<= unknown-% 29.0)
        (format "unknown pairs must not grow above 29%% (got %.1f%%)" unknown-%))))
