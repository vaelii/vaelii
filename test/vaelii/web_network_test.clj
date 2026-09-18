;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-network-test
  "The /network page — the constraint network a qualitative calculus computes over one
  context, exercised as a pure request -> response with no live server.

  What the page is for is what these check: that the matrix, the satisfiability verdict
  and the scenario each say something the stored facts alone do not.  A relation nobody
  asserted has to appear in the matrix, or the page is only echoing the KB back."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- GET
  ([kb uri] (GET kb uri nil))
  ([kb uri qs]
   ((web/app kb) (cond-> {:request-method :get :uri uri}
                   qs (assoc :query-string qs)))))

(defn- nest
  "Assert a chain of nested regions in a fresh context, and answer that context."
  [kb ctx & regions]
  (doseq [[a b] (partition 2 1 regions)]
    (v/assert kb (list 'nonTangentialProperPart a b) ctx {:strength :monotonic}))
  ctx)

(tu/deftest-kb the-network-page-lists-every-calculus-without-a-context
  (let [r (GET kb "/network")]
    (is (= 200 (:status r)))
    (testing "all six shipped algebras are offered, prover registered or not"
      (doseq [nm ["rcc8" "cardinal" "relative" "distance" "allen" "point"]]
        (is (re-find (re-pattern nm) (:body r)) (str nm " is listed"))))
    (testing "each is described by its base-relation count and its vocabulary"
      (is (re-find #"base" (:body r)))
      (is (re-find #"nonTangentialProperPart|partOfRegion" (:body r))))))

(tu/deftest-kb the-matrix-shows-a-relation-nobody-asserted
  (tu/with-terms [RegA RegB RegC CxSpaceStory]
    (v/assert kb (list 'genlCx CxSpaceStory 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (nest kb CxSpaceStory RegA RegB RegC)
    (let [r (GET kb "/network" (str "ctx=" CxSpaceStory "&calc=rcc8"))]
      (is (= 200 (:status r)))
      (testing "the network is satisfiable and names its three regions"
        (is (re-find #"satisfiable" (:body r)))
        (doseq [t [RegA RegB RegC]]
          (is (re-find (re-pattern (str t)) (:body r)))))
      (testing "the A-to-C entailment is on the page, and it was never asserted"
        (is (nil? (v/handle-of kb (list 'nonTangentialProperPart RegA RegC)
                               CxSpaceStory))
            "the transitive relation is genuinely not stored")
        (is (= #{:ntpp} (v/possible-relations kb :rcc8 CxSpaceStory RegA RegC))))
      (testing "the scenario section renders one arrangement"
        (is (re-find #"One scenario" (:body r)))
        (is (re-find #"ntpp" (:body r)))))))

(tu/deftest-kb a-calculus-name-no-algebra-answers-to-is-refused
  ;; The fallback picks the first calculus with a populated network, so `?calc=rcc9` drew a
  ;; matrix — a *different* algebra's, with nothing on the page to say so.  A reader
  ;; comparing two calculi by editing the URL is exactly who that misleads.
  (tu/with-terms [RegA RegB CxSpaceRefuse]
    (v/assert kb (list 'genlCx CxSpaceRefuse 'CxWell) 'CxUniverse {:strength :monotonic})
    (nest kb CxSpaceRefuse RegA RegB)
    (let [r (GET kb "/network" (str "ctx=" CxSpaceRefuse "&calc=rcc9"))]
      (is (= 400 (:status r)))
      (is (re-find #"<code>calc</code>" (:body r)))
      (is (re-find #"rcc9" (:body r)))
      (testing "and the refusal names every calculus that would have been legal"
        (doseq [nm (map (comp name :calculus) (v/calculi))]
          (is (re-find (re-pattern nm) (:body r)) (str nm " is offered by the refusal")))))
    (testing "a real one still renders, and so does the page with no calculus named"
      (is (= 200 (:status (GET kb "/network" (str "ctx=" CxSpaceRefuse "&calc=rcc8")))))
      (is (= 200 (:status (GET kb "/network" (str "ctx=" CxSpaceRefuse)))))
      (is (= 200 (:status (GET kb "/network" (str "ctx=" CxSpaceRefuse "&calc="))))
          "an empty control is the control not being submitted"))))

(tu/deftest-kb an-unsatisfiable-network-says-so-rather-than-answering
  (tu/with-terms [RegA RegB CxSpaceClash]
    (v/assert kb (list 'genlCx CxSpaceClash 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (v/assert kb (list 'nonTangentialProperPart RegA RegB) CxSpaceClash
              {:strength :monotonic})
    (v/assert kb (list 'spatiallyDisconnected RegA RegB) CxSpaceClash
              {:strength :monotonic})
    (let [r (GET kb "/network" (str "ctx=" CxSpaceClash "&calc=rcc8"))]
      (is (= 200 (:status r)))
      (testing "the verdict is reported, not swallowed"
        (is (re-find #"unsatisfiable" (:body r))))
      (testing "and the pair to blame is named, since one pair carries the clash"
        (is (re-find (re-pattern (str RegA)) (:body r)))
        (is (false? (:consistent? (v/qualitative-network kb :rcc8 CxSpaceClash)))))
      (testing "no scenario is offered for a world that cannot exist"
        (is (nil? (v/qualitative-scenario kb :rcc8 CxSpaceClash)))))))

(tu/deftest-kb a-context-with-no-qualitative-facts-says-nothing-rather-than-erroring
  (tu/with-terms [CxEmptySpace]
    (v/assert kb (list 'genlCx CxEmptySpace 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (let [r (GET kb "/network" (str "ctx=" CxEmptySpace))]
      (is (= 200 (:status r)))
      (is (re-find #"No calculus relates anything|relates nothing" (:body r))))))

(tu/deftest-kb the-menubar-reaches-the-page
  (let [r (GET kb "/")]
    (is (= 200 (:status r)))
    (is (re-find #"href=\"/network\"" (:body r)))
    (is (re-find #">Network<" (:body r)))))
