;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nmtms-edge-test
  "Edge cases for the non-monotonic TMS beyond the headline scenarios in
  `nmtms_test`: defeat propagating through a downstream strict rule, strength +
  defeat surviving `recover`, disjoint/functional staying HARD after negation
  went soft, independent contradictions resolving without interference, a default
  defeated in one context yet holding in a genlCx sibling, and plain support loss
  (retracting the premise a default rested on) versus defeat."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- 1. defeat propagates through a downstream strict rule --------------

(tu/deftest-kb defeating-a-default-withdraws-its-strict-consequence
  ;; A default draws (flies Sky); a strict rule then draws (airborne Sky) FROM it.
  ;; Defeating the default with a later monotonic negation must also drop the
  ;; strict conclusion — its only support runs through the now-OUT default.
  (let [bird (tu/tmp-type) animal (tu/tmp-type)
        flies (tu/tmp-pred) airborne (tu/tmp-pred) sky (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxUniverse)
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
    (v/assert-rule kb [(list flies '?x)] (list airborne '?x) 'CxUniverse {:direction :forward})   ; strict, feeds off the default
    (v/assert kb (list bird sky) 'CxUniverse)
    (testing "the default and its strict consequence both hold"
      (is (seq (v/sentexes-matching kb (list flies sky) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list airborne sky) 'CxUniverse))))
    (testing "a later monotonic negation of the default also withdraws the strict consequence"
      (v/assert kb (list 'not (list flies sky)) 'CxUniverse {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list flies sky) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list airborne sky) 'CxUniverse)))
      (is (empty? (v/conflicts kb))))))

;; ---- 2. strength + defeat survive recover ------------------------------

(tu/deftest-kb strength-and-defeat-survive-recover
  ;; monotonic (happy Tom) defeats default (not (happy Tom)); after a fresh KB
  ;; recovers from the same durable stores, both the belief and its resolution
  ;; must be reconstructed — the persisted premise strengths decide the tie again.
  (let [happy (tu/tmp-pred) tom (tu/tmp-ind)]
    (v/assert kb (list happy tom) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list happy tom)) 'CxUniverse)                  ; default, gets defeated
    (is (seq   (v/sentexes-matching kb (list happy tom) 'CxUniverse)))
    (is (empty? (v/sentexes-matching kb (list 'not (list happy tom)) 'CxUniverse)))
    (let [kb2 (tu/test-kb)]
      (testing "before recover the fresh in-memory graph believes nothing"
        (is (empty? (v/sentexes-matching kb2 (list happy tom) 'CxUniverse))))
      (v/recover kb2)
      (testing "after recover the monotonic belief and the default's defeat both survive"
        (is (seq   (v/sentexes-matching kb2 (list happy tom) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb2 (list 'not (list happy tom)) 'CxUniverse)))
        (is (empty? (v/conflicts kb2)))))))

;; ---- 3. disjoint / functional are arbitrated as negation is -------------

(tu/deftest-kb disjoint-and-functional-clashes-are-arbitrated-as-negation-is
  ;; Disjointness and functionality are stored and weighed exactly as `S` against
  ;; `(not S)` is: an equal `:default` pair is a dilemma, and an equal `:monotonic`
  ;; pair is a conflict, whichever arrived last.
  (let [dog (tu/tmp-type) cat (tu/tmp-type) muffet (tu/tmp-ind) felix (tu/tmp-ind)
        birthYearOf (tu/tmp-pred) tom (tu/tmp-ind)]
    (testing "a disjoint type membership is a dilemma at :default"
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (v/assert kb (list dog muffet) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list cat muffet) 'CxUniverse))
      (is (= [:disjoint] (mapv :kind (v/contradictions kb))))
      (is (empty? (v/conflicts kb))))
    (testing "and a conflict at :monotonic"
      (v/assert kb (list dog felix) 'CxUniverse {:strength :monotonic})
      (is (tu/stored-in-clash? kb (list cat felix) 'CxUniverse {:strength :monotonic}))
      (is (= [:disjoint] (mapv :kind (v/conflicts kb)))))
    (testing "a functional clash between two numbers is a dilemma too"
      (v/assert kb (list 'functional birthYearOf) 'CxNaturalWorld)
      (v/assert kb (list birthYearOf tom 1980) 'CxNaturalWorld)
      (is (tu/stored-in-clash? kb (list birthYearOf tom 1990) 'CxNaturalWorld)))))

;; ---- 4. two independent contradictions resolve independently ------------

(tu/deftest-kb independent-contradictions-resolve-independently
  ;; Two unrelated negation clashes in one KB, weaker side on opposite sides;
  ;; the settle loop must defeat each weaker member without touching the other.
  (let [happy (tu/tmp-pred) tom (tu/tmp-ind) sad (tu/tmp-pred) ann (tu/tmp-ind)]
    (v/assert kb (list happy tom) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list happy tom)) 'CxUniverse)                  ; default loses here
    (v/assert kb (list sad ann) 'CxUniverse)                         ; default loses there
    (v/assert kb (list 'not (list sad ann)) 'CxUniverse {:strength :monotonic})
    (testing "each clash defeats its own weaker (default) side"
      (is (seq   (v/sentexes-matching kb (list happy tom) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list 'not (list happy tom)) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list sad ann) 'CxUniverse)))
      (is (seq   (v/sentexes-matching kb (list 'not (list sad ann)) 'CxUniverse))))
    (testing "both resolved: nothing reported"
      (is (empty? (v/conflicts kb))))))

;; ---- 5. a default defeated in one context but holding in a sibling ------

(tu/deftest-kb default-defeated-in-one-context-holds-in-sibling
  ;; CxA and CxB both see CxRoot but not each other.  The default rule lives in
  ;; CxRoot; the same bird fact in each leaf derives (flies Tweety) into that leaf.
  ;; A monotonic negation asserted only in CxA reaches CxA's up-closure, so it
  ;; defeats the CxA conclusion while the sibling CxB conclusion stands.
  (let [bird (tu/tmp-type) flies (tu/tmp-pred) tweety (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxA 'CxRoot) 'CxUniverse)
    (v/assert kb (list 'genlCx 'CxB 'CxRoot) 'CxUniverse)
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxRoot)
    (v/assert kb (list bird tweety) 'CxA)
    (v/assert kb (list bird tweety) 'CxB)
    (testing "the default fires into both sibling contexts"
      (is (seq (v/sentexes-matching kb (list flies tweety) 'CxA)))
      (is (seq (v/sentexes-matching kb (list flies tweety) 'CxB))))
    (testing "a negation local to CxA defeats only the CxA conclusion"
      (v/assert kb (list 'not (list flies tweety)) 'CxA {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxA)))              ; defeated here
      (is (seq   (v/sentexes-matching kb (list flies tweety) 'CxB)))              ; untouched in the sibling
      (is (seq   (v/sentexes-matching kb (list 'not (list flies tweety)) 'CxA)))
      (is (empty? (v/conflicts kb))))))

;; ---- 6. support loss (retract the premise) is not defeat ----------------

(tu/deftest-kb retracting-a-defaults-premise-removes-it-outright
  ;; A defeated default is RETAINED (OUT but still stored) for possible revival.
  ;; Losing the premise it rested on is different: the conclusion is solely
  ;; supported by that premise, so retraction SWEEPS it from the stores entirely.
  (let [bird (tu/tmp-type) animal (tu/tmp-type) flies (tu/tmp-pred) sky (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxUniverse)
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
    (let [bird-h (v/assert kb (list bird sky) 'CxUniverse)]
      (is (seq (v/sentexes-matching kb (list flies sky) 'CxUniverse)))
      (let [flies-h (v/handle-of kb (list flies sky) 'CxUniverse)]
        (v/retract! kb bird-h)
        (testing "the conclusion is gone with its support — swept, not merely defeated"
          (is (empty? (v/sentexes-matching kb (list flies sky) 'CxUniverse)))
          (is (not (v/believed? kb flies-h)))
          (is (nil? (v/sentex kb flies-h)))                          ; physically removed
          (is (empty? (v/conflicts kb))))))))
