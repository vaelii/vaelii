;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.social-test
  "CxSocial's general relationship and dwelling vocabulary: kinOf,
  romanticPartnerOf, coworkerOf and roommateOf, each a spec of knows or
  friendOf except kinOf, which reads knows by default; originatorOf, read from blood-qualified parenthood;
  relationshipLabel, a perspectival label; and dwelling/dwellsIn, whose
  co-dwelling rule derives roommateOf. CxSocial is a starter theory, so CxWell
  sees all of it with no opt-in step."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- holds-query    [s ctx]         (boolean (v/query? tu/*kb* s ctx {:max-depth 5})))
(defn- holds-disjoint [a b ctx]       (boolean (v/disjoint? tu/*kb* a b ctx)))

(tu/deftest-kb the-relationship-vocabulary-genls-into-knows-and-friendof
  (is (not (tu/holds-genl 'kinOf 'knows 'CxWell))
      "no edge: a relative may never have met you, so a default rule reads knows instead")
  (is (tu/holds-genl 'coworkerOf 'knows 'CxWell))
  (is (tu/holds-genl 'roommateOf 'knows 'CxWell))
  (is (not (tu/holds-genl 'originatorOf 'kinOf 'CxWell)))
  (is (tu/holds-genl 'romanticPartnerOf 'friendOf 'CxWell))
  (is (not (tu/holds-genl 'marriedTo 'romanticPartnerOf 'CxWell))
      "no edge: it would carry marriedTo's own knows-rule under friendOf's and cover it")
  (is (tu/holds-genl 'dwellsIn 'livesIn 'CxWell))
  (is (tu/holds-genl 'dwelling 'container 'CxWell))
  (is (not (tu/holds-genl 'dwelling 'building 'CxWell)) "an apartment is a dwelling and not a building")
  (is (tu/holds-genl 'dwelling 'tangible 'CxWell) "container carries dwelling to tangible"))

(tu/deftest-kb dwelling-is-disjoint-from-organism-substance-and-person
  (doseq [t '[organism substance person clothing furniture]]
    (is (holds-disjoint 'dwelling t 'CxWell) (str "dwelling and " t)))
  (doseq [t '[building vehicle]]
    (is (= :orthogonal (v/subsumption-status tu/*kb* 'dwelling t 'CxWell)) (str "dwelling and " t))))

(tu/deftest-kb originatorof-is-read-from-blood-parenthood
  (tu/with-terms [Parent Child]
    (v/assert kb (list 'plant Parent) 'CxWell)
    (v/assert kb (list 'plant Child) 'CxWell)
    (v/assert kb (list 'parentOf Parent Child) 'CxWell)
    (is (not (holds-query (list 'originatorOf Parent Child) 'CxWell)))
    (v/assert kb (list (list 'BloodKinFn 'parentOf) Parent Child) 'CxWell)
    (is (holds-query (list 'originatorOf Parent Child) 'CxWell))
    (is (not (holds-query (list 'person Parent) 'CxWell)))
    (is (not (holds-query (list 'person Child) 'CxWell)))))

(tu/deftest-kb co-dwelling-derives-roommateof
  (tu/with-terms [Resident1 Resident2 Unit]
    (v/assert kb (list 'dwellsIn Resident1 Unit) 'CxWell)
    (testing "one dweller alone derives no roommateOf (red)"
      (is (not (tu/holds-ask (list 'roommateOf Resident1 Resident2) 'CxWell))))
    (v/assert kb (list 'dwellsIn Resident2 Unit) 'CxWell)
    (testing "two different dwellers of the same dwelling derive roommateOf (green)"
      (is (tu/holds-ask (list 'roommateOf Resident1 Resident2) 'CxWell))
      (is (tu/holds-ask (list 'knows Resident1 Resident2) 'CxWell) "roommateOf genls knows"))))

(tu/deftest-kb relationshiplabel-is-a-plain-ternary-fact
  (tu/with-terms [Namer Named]
    (v/assert kb (list 'person Namer) 'CxWell)
    (v/assert kb (list 'person Named) 'CxWell)
    (v/assert kb (list 'relationshipLabel Namer Named "mentor") 'CxWell)
    (is (tu/holds-ask (list 'relationshipLabel Namer Named "mentor") 'CxWell))))

(tu/deftest-kb a-relative-is-known-by-default
  ;; Kinship holds of two relatives who never met, so knows follows from kinOf by
  ;; a default rule a stated denial overrides, and the rule-macro suggestion to make it
  ;; a genl edge is recorded declined.
  (is (tu/holds-ask '(declined_rule_macro (Quote (genl kinOf knows))) 'CxSocial))
  (is (seq (v/ask tu/*kb* '(implementationNote kinOf ?note) 'CxSocial)))
  (tu/with-terms [Aunt Niece Cousin1 Cousin2]
    (doseq [p [Aunt Niece Cousin1 Cousin2]]
      (v/assert kb (list 'human p) 'CxWell))
    (v/assert kb (list 'kinOf Aunt Niece) 'CxWell)
    (is (holds-query (list 'knows Aunt Niece) 'CxWell) "a relative is known by default")
    (v/assert kb (list 'kinOf Cousin1 Cousin2) 'CxWell)
    (v/assert kb (list 'not (list 'knows Cousin1 Cousin2)) 'CxWell {:strength :monotonic})
    (is (not (holds-query (list 'knows Cousin1 Cousin2) 'CxWell))
        "two relatives who never met stay relatives")
    (is (tu/holds-ask (list 'kinOf Cousin1 Cousin2) 'CxWell))))
