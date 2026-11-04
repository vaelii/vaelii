;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cxtra-test
  "CxTra: the opt-in middle context for vocabulary that is generally useful but
  domain-specific, shipped below CxUniverse and CxSocial.  CxTra holds the computing
  relations and kinds, hosts, access, file paths and pull requests, the perception relations, and
  relationship and plural-identity vocabulary narrower than CxSocial's.  CxWell does not see CxTra, so a context below
  CxWell reads none of that vocabulary, and a user's own context opts in by placing
  itself under CxTra.  `computing_test` and `perception_test` hold each vocabulary's own
  claims."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.seed :as seed]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(tu/deftest-kb cxtra-is-a-shipped-middle-context
  (testing "kb/middle/CxTra.txt is discovered as a middle context"
    (is (some #{'CxTra} (seed/layer-contexts "middle"))))
  (testing "CxUniverse states the context membership of CxTra as a premise"
    (is (some #(v/premise? kb (:id %))
              (v/sentexes-matching kb '(context CxTra) 'CxUniverse))))
  (testing "CxTra carries one comment"
    (is (= 1 (count (v/sentexes-matching kb '(comment CxTra ?c) 'CxTra))))))

(tu/deftest-kb cxtra-sees-cxuniverse-and-cxwell-does-not-see-cxtra
  (is (tu/holds-sees 'CxTra 'CxUniverse))
  (is (tu/holds-sees 'CxTra 'CxSocial) "its relationship terms specialize CxSocial's")
  (is (not (tu/holds-sees 'CxSocial 'CxTra)))
  (is (not (tu/holds-sees 'CxWell 'CxTra)))
  (is (not (tu/holds-sees 'CxUniverse 'CxTra))))

(tu/deftest-kb cxtra-holds-the-computing-and-the-perception-vocabulary
  (testing "a computing kind's placement holds in CxTra"
    (is (tu/holds-genl 'software_tool 'computational_system 'CxTra)))
  (testing "the perception chain holds in CxTra"
    (is (tu/holds-genl 'sees 'perceives 'CxTra)))
  (testing "neither placement holds in CxWell"
    (is (not (tu/holds-genl 'software_tool 'computational_system 'CxWell)))
    (is (not (tu/holds-genl 'sees 'perceives 'CxWell)))))

(tu/deftest-kb a-context-under-cxwell-and-cxtra-reads-both-vocabularies
  (tu/with-terms [CxDesk]
    (v/assert kb (list 'genlCx CxDesk 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxDesk 'CxTra) 'CxUniverse)
    (is (tu/holds-genl 'software_tool 'computational_system CxDesk))
    (is (tu/holds-genl 'sees 'perceives CxDesk))))
