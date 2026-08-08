;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reindex-test
  "The index is derived state: `reindex` must rebuild all of it — trie, roots, term
  index, rule index — from the records alone, such that every read answers as it
  did before the index was destroyed."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex]
            [vaelii.test-util :as tu]))

(deftest reindex-rebuilds-a-destroyed-index
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [dog animal barksAt growls Muffet Rex]
      (v/assert kb (list 'genl dog animal) 'UniverseContext)
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (v/assert kb (list barksAt Muffet Rex) 'UniverseContext)
      (v/assert-rule kb [(list dog '?x)] (list growls '?x) 'UniverseContext)
      (let [snap (fn []
                   {:dog-extent    (count (v/sentexes-matching kb (list dog '?x) 'UniverseContext))
                    :functor-count (v/count-with-functor kb barksAt)
                    :arg-count     (v/count-with-arg kb 1 Muffet)
                    :term-find     (count (v/find-sentexes kb Muffet))
                    :isa?          (v/isa? kb Muffet animal)
                    :derived?      (boolean (seq (v/sentexes-matching kb (list growls Muffet) 'UniverseContext)))
                    :backward?     (v/provable? kb (list growls Muffet) 'UniverseContext)})
            before (snap)]
        (testing "the content is really there before the damage"
          (is (:derived? before) "the rule fired forward")
          (is (:isa? before)))
        (p/clear-index! (:index kb))
        (testing "the damage is real: an empty index answers nothing"
          (is (zero? (v/count-with-functor kb barksAt))))
        (let [{:keys [sentexes rules]} (reindex/reindex kb)]
          (is (pos? sentexes))
          (is (= 1 rules) "the one rule was re-registered in the rule index"))
        (v/recover kb)
        (testing "every read answers as before the index was destroyed"
          (is (= before (snap))))))))
