;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.catbus-test
  "The fiction witness for CxRealWorld (resources/kb/CxRealWorld.txt): CxUniverse
  states (disjoint animal vehicle) at the default strength, and CxRealWorld restates
  the same separation monotonic. CxTotoro, a context under CxWell siblinged with
  CxRealWorld rather than placed below it, holds a catbus — a term that is both a cat
  and a bus — as a represented dilemma, neither side defeated. The same pair of
  memberships in CxRealWorld loses a monotonic clash instead, and an ordinary animal
  in CxWell is not a vehicle with no overlap asserted at all."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb a-catbus-holds-in-fiction-and-loses-in-the-real-world
  (v/assert kb '(genlCx CxTotoro CxWell) 'CxUniverse)
  (v/assert kb '(context CxTotoro) 'CxUniverse)
  (tu/with-terms [tu_bus Catbus OrdinaryCat Catbus2]
    ;; bus does not exist upstream, so this is the test's own :monotonic spec of vehicle.
    (v/assert kb (list 'genl tu_bus 'vehicle) 'CxUniverse {:strength :monotonic})

    (testing "CxTotoro holds the catbus as both a cat and a bus"
      (v/assert kb (list 'cat Catbus) 'CxTotoro)
      (v/assert kb (list tu_bus Catbus) 'CxTotoro)
      (is (v/ask? kb (list 'cat Catbus) 'CxTotoro) "the catbus is a cat")
      (is (v/ask? kb (list tu_bus Catbus) 'CxTotoro) "and a bus — neither side lost")
      (is (v/ask? kb (list 'animal Catbus) 'CxTotoro))
      (is (v/ask? kb (list 'vehicle Catbus) 'CxTotoro))
      (is (seq (filter #(contains? (:nogood %)
                                   (v/handle-of kb (list tu_bus Catbus) 'CxTotoro))
                       (v/contradictions kb)))
          "the overlap is reported as a dilemma, which is a clash that does not win"))

    (testing "the same pair in CxRealWorld loses the monotonic clash instead"
      (v/assert kb (list 'cat Catbus2) 'CxRealWorld {:strength :monotonic})
      (is (v/assert kb (list tu_bus Catbus2) 'CxRealWorld)
          "a write is never refused — the attempt is stored")
      (is (v/ask? kb (list 'cat Catbus2) 'CxRealWorld) "the monotonic membership stands")
      (is (not (v/ask? kb (list tu_bus Catbus2) 'CxRealWorld))
          "the vehicle membership loses the monotonic clash — the real world never
           holds the overlap"))

    (testing "the same Catbus2 is both a cat and a bus in CxTotoro"
      (v/assert kb (list 'cat Catbus2) 'CxTotoro)
      (v/assert kb (list tu_bus Catbus2) 'CxTotoro)
      (is (v/ask? kb (list 'cat Catbus2) 'CxTotoro) "Catbus2 is a cat in the fiction")
      (is (v/ask? kb (list tu_bus Catbus2) 'CxTotoro) "and a bus in the fiction")
      (is (not (v/ask? kb (list tu_bus Catbus2) 'CxRealWorld))
          "while CxRealWorld, a sibling of CxTotoro, still does not hold it as a bus"))

    (testing "in plain CxWell an ordinary animal is not a vehicle by default"
      (v/assert kb (list 'cat OrdinaryCat) 'CxWell)
      (is (not (v/ask? kb (list 'vehicle OrdinaryCat) 'CxWell)))
      (is (not (v/ask? kb (list tu_bus OrdinaryCat) 'CxWell))))))

(defn- reported?
  "Whether the clash a membership is in is reported: as a dilemma, as a conflict, or as
  the defeat that took the membership OUT."
  [kb h]
  (boolean
   (or (some #(contains? (:nogood %) h) (concat (v/contradictions kb) (v/conflicts kb)))
       (= :defeated (:reason (v/why-not kb h))))))

(tu/deftest-kb an-overlap-under-a-provable-separation-is-always-reported
  ;; Where (disjoint animal vehicle) is provable and both memberships are visible, the
  ;; clash is reported whatever strengths the memberships were written at.
  (tu/with-terms [tu_bus DefaultBoth MonoCat MonoBoth]
    (v/assert kb (list 'genl tu_bus 'vehicle) 'CxUniverse {:strength :monotonic})
    (doseq [[term cat-strength bus-strength] [[DefaultBoth :default :default]
                                              [MonoCat :monotonic :default]
                                              [MonoBoth :monotonic :monotonic]]]
      (v/assert kb (list 'cat term) 'CxRealWorld {:strength cat-strength})
      (v/assert kb (list tu_bus term) 'CxRealWorld {:strength bus-strength})
      (testing (str "cat " cat-strength ", bus " bus-strength " in CxRealWorld")
        (is (reported? kb (v/handle-of kb (list tu_bus term) 'CxRealWorld)))))))

(tu/deftest-kb a-default-separation-yields-to-a-fiction-that-states-the-overlap
  ;; The five separations are not forced-monotonic. CxUniverse states
  ;; (disjoint animal vehicle) at the default strength, so a fiction's monotonic denial of
  ;; it defeats that copy there, and the membership nogood resting on the separation is
  ;; hidden at the fiction instead of standing as an irreducible conflict. The membership
  ;; verdict weighs only the two memberships, so the denial is what states the overlap.
  (v/assert kb '(genlCx CxTotoro CxWell) 'CxUniverse)
  (v/assert kb '(context CxTotoro) 'CxUniverse)
  (tu/with-terms [tu_bus Catbus3]
    (v/assert kb (list 'genl tu_bus 'vehicle) 'CxUniverse)
    (v/assert kb '(not (disjoint animal vehicle)) 'CxTotoro {:strength :monotonic})
    (v/assert kb (list 'cat Catbus3) 'CxTotoro {:strength :monotonic})
    (v/assert kb (list tu_bus Catbus3) 'CxTotoro {:strength :monotonic})
    (let [cat-h (v/handle-of kb (list 'cat Catbus3) 'CxTotoro)
          bus-h (v/handle-of kb (list tu_bus Catbus3) 'CxTotoro)]
      (is (v/ask? kb (list 'cat Catbus3) 'CxTotoro))
      (is (v/ask? kb (list tu_bus Catbus3) 'CxTotoro))
      (is (not-any? #(or (contains? (:nogood %) cat-h) (contains? (:nogood %) bus-h))
                    (v/conflicts kb))
          "the default separation loses; nothing is left irreducible")
      (is (not (v/ask? kb '(disjoint animal vehicle) 'CxTotoro))
          "the denial defeats the CxUniverse copy at the fiction")
      (is (v/ask? kb '(disjoint animal vehicle) 'CxWell)
          "the defeat is CxTotoro's: CxWell, which holds no catbus, still believes it")
      (is (v/ask? kb '(disjoint animal vehicle) 'CxRealWorld)
          "and CxRealWorld's monotonic copy stands"))))
