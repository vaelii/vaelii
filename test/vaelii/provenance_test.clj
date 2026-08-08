;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.provenance-test
  "Per-handle provenance: a bookkeeping map (creator + creation date, plus arbitrary
  application fields) kept beside the record, stamped on `assert`, first-writer-wins
  on creation, extensible with `add-provenance`, and torn down with the record.  The
  clock and default creator are dynamic vars so a test can pin them; belief never
  reads provenance, so nothing here touches order independence."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb assert-stamps-creator-and-created
  (tu/with-terms [dog Muffet FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      (let [h (v/assert kb (list dog Muffet) FarmContext)]
        (is (= {:creator "alice" :created 1000} (v/provenance kb h)))))))

(tu/deftest-kb opts-creator-overrides-the-default
  (tu/with-terms [dog Muffet FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      (let [h (v/assert kb (list dog Muffet) FarmContext {:creator "bob"})]
        (is (= "bob" (:creator (v/provenance kb h))))
        (is (= 1000 (:created (v/provenance kb h))))))))

(tu/deftest-kb opts-provenance-map-is-merged-in
  (tu/with-terms [dog Muffet FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      (let [h (v/assert kb (list dog Muffet) FarmContext
                        {:provenance {:source "import" :confidence 0.9}})]
        (is (= {:creator "alice" :created 1000 :source "import" :confidence 0.9}
               (v/provenance kb h)))))))

(tu/deftest-kb creation-is-first-writer-wins
  (tu/with-terms [dog Muffet FarmContext]
    (let [h1 (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
               (v/assert kb (list dog Muffet) FarmContext))
          ;; re-assert the SAME sentex later, different creator/clock
          h2 (binding [v/*creator* "bob" v/*clock* (constantly 2000)]
               (v/assert kb (list dog Muffet) FarmContext))]
      (is (= h1 h2) "re-asserting resolves to the same handle")
      (testing "the original creation stamp is preserved, not overwritten"
        (is (= {:creator "alice" :created 1000} (v/provenance kb h1)))))))

(tu/deftest-kb re-assert-still-merges-new-application-fields
  (tu/with-terms [dog Muffet FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      (let [h (v/assert kb (list dog Muffet) FarmContext)]
        ;; a later assert of the same sentex carrying extra provenance adds it,
        ;; without disturbing the original creator/created
        (v/assert kb (list dog Muffet) FarmContext {:provenance {:reviewed true}})
        (is (= {:creator "alice" :created 1000 :reviewed true} (v/provenance kb h)))))))

(tu/deftest-kb add-provenance-layers-application-fields
  (tu/with-terms [dog Muffet FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      (let [h (v/assert kb (list dog Muffet) FarmContext)]
        (v/add-provenance kb h {:confidence 0.7 :tags #{:animal}})
        (is (= {:creator "alice" :created 1000 :confidence 0.7 :tags #{:animal}}
               (v/provenance kb h)))
        (testing "creator/created only change if add-provenance names them"
          (v/add-provenance kb h {:creator "curator"})
          (is (= "curator" (:creator (v/provenance kb h))))
          (is (= 1000 (:created (v/provenance kb h)))))))))

(tu/deftest-kb retract-removes-provenance
  (tu/with-terms [dog Muffet FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      (let [h (v/assert kb (list dog Muffet) FarmContext)]
        (is (some? (v/provenance kb h)))
        (v/retract! kb h)
        (is (nil? (v/provenance kb h)) "provenance dies with the record")))))

(tu/deftest-kb default-creator-is-nil-and-created-is-always-present
  (tu/with-terms [dog Muffet FarmContext]
    ;; no *creator* bound -> nil creator, but a :created stamp is always recorded
    (binding [v/*clock* (constantly 4242)]
      (let [h (v/assert kb (list dog Muffet) FarmContext)
            p (v/provenance kb h)]
        (is (contains? p :creator))
        (is (nil? (:creator p)))
        (is (= 4242 (:created p)))))))

(tu/deftest-kb conjunctive-consequent-stamps-every-handle
  (tu/with-terms [p a b c FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      ;; a rule concluding (and C1 C2) is polycanonicalized into two rules; assert
      ;; returns the vector, and each stored rule gets provenance
      (let [hs (v/assert kb (list 'implies (list p '?x)
                                  (list 'and (list a '?x) (list b '?x)))
                         FarmContext)]
        (is (vector? hs))
        (is (< 1 (count hs)))
        (doseq [h hs]
          (is (= {:creator "alice" :created 1000} (v/provenance kb h))))))))

(tu/deftest-kb provenance-is-metadata-not-belief
  (tu/with-terms [dog Muffet FarmContext]
    (binding [v/*creator* "alice" v/*clock* (constantly 1000)]
      (let [h (v/assert kb (list dog Muffet) FarmContext)]
        (testing "stamping provenance does not disturb belief or query"
          (is (v/in? kb h))
          (is (seq (v/sentexes-matching kb (list dog Muffet) FarmContext))))))))
