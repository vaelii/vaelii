;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.scenario-test
  "Scenario extraction (`vaelii.impl.scenario`): turning the relation *sets* path consistency
  leaves into one concrete arrangement that everything believed permits.

  What the tests watch is the three properties a scenario has to have.  It is **complete** —
  every pair, including the ones no fact reaches, gets a single base relation.  It is
  **consistent** — running path consistency over it empties nothing, which is the only
  independent check there is, since the search and the pass are the two halves of the same
  claim.  And it is **deterministic** — the same believed facts give the same scenario, in
  repeated calls and after the same facts are retracted and re-asserted in another order, so
  the answer cannot be reading a handle."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.scenario :as scen]
            [vaelii.impl.space :as sp]
            [vaelii.test-util :as tu]))

;; A fresh KB per test carrying two calculi's vocabularies, since what is being tested is
;; that the search knows about neither.  No prover is registered: a scenario is read off the
;; network directly, so it needs no query engine.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxTime "upper"] [CxSpace "upper"]]))))

(def ^:private C 'CxUniverse)

(defn- consistent?
  "Does `scen` survive path consistency — is it an arrangement rather than a wish?  The
  independent check on the search: it re-runs the pass over the scenario as a network of its
  own, which is exactly what the search claimed it had already established."
  [calc scen]
  (let [nodes (qkb/nodes scen)]
    (not= :inconsistent (qcn/path-consistent scen nodes (:algebra calc)))))

(defn- complete?
  "Is every pair of `n` nodes decided, both directions written, each to a single relation?"
  [scen n]
  (and (= (* n (dec n)) (count scen))
       (every? #(= 1 (count %)) (vals scen))))

;; ---- a network with nothing left to choose -------------------------------

(tu/deftest-kb a-fully-determined-network-has-exactly-one-scenario
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (testing "every pair is pinned by the facts and their composition, so the scenario is
              the network itself and there is no second one"
      (let [ss (scen/scenarios iv/allen kb C {:limit 5})]
        (is (= 1 (count ss)))
        (is (= {[A B] #{:before} [B A] #{:after}
                [B D] #{:before} [D B] #{:after}
                [A D] #{:before} [D A] #{:after}}
               (first ss)))))
    (testing "and it reads as one relation per pair"
      (is (= {[A B] :before [B A] :after
              [B D] :before [D B] :after
              [A D] :before [D A] :after}
             (scen/relations (scen/scenario iv/allen kb C)))))))

;; ---- a network with choices left -----------------------------------------

(tu/deftest-kb an-underdetermined-network-yields-a-consistent-arrangement
  (tu/with-terms [A B D]
    ;; meets ∘ metBy pins the two ends together and says nothing about the two starts
    (v/assert kb (list 'meets A B) C)
    (v/assert kb (list 'metBy B D) C)
    (is (= #{:finishes :finished-by :equal} (iv/possible-allen-relations kb C A D))
        "three relations remain, so a scenario has to choose")
    (let [s (scen/scenario iv/allen kb C)]
      (testing "the choice is a single relation on every pair, both ways round"
        (is (complete? s 3)))
      (testing "and it is one path consistency accepts — nothing empties"
        (is (consistent? iv/allen s)))
      (testing "the pairs the facts pinned keep what they were given"
        (is (= #{:meets} (get s [A B])))
        (is (= #{:met-by} (get s [B D]))))
      (testing "and the open pair takes one of the three that were left"
        (is (contains? #{#{:finishes} #{:finished-by} #{:equal}} (get s [A D])))))))

(tu/deftest-kb a-network-nothing-constrains-still-has-a-scenario
  (tu/with-terms [A B]
    (v/assert kb (list 'sharesTimeWith A B) C)   ; nine relations, no composition to help
    (let [s (scen/scenario iv/allen kb C)]
      (is (complete? s 2))
      (is (consistent? iv/allen s))
      (is (contains? (iv/interval-denotation 'sharesTimeWith) (first (get s [A B])))))))

;; ---- inconsistency -------------------------------------------------------

(tu/deftest-kb an-inconsistent-network-has-no-scenario-at-all
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (v/assert kb (list 'after A D) C)
    (testing "the facts cannot all hold, so no arrangement satisfies them"
      (is (nil? (scen/scenario iv/allen kb C)))
      (is (empty? (scen/scenarios iv/allen kb C))))
    (testing "retracting the offending fact gives an arrangement back"
      (v/retract! kb (v/handle-of kb (list 'after A D) C))
      (is (some? (scen/scenario iv/allen kb C))))))

;; ---- bounded enumeration -------------------------------------------------

(tu/deftest-kb the-enumeration-is-lazy-and-honours-its-limit
  (tu/with-terms [A B D]
    ;; nothing at all is stated about A, B and D beyond one loose pair, so the search tree
    ;; is wide — which is the case a caller must not enumerate eagerly
    (v/assert kb (list 'sharesTimeWith A B) C)
    (v/assert kb (list 'sharesTimeWith B D) C)
    (testing ":limit takes what was asked for and no more"
      (is (= 3 (count (scen/scenarios iv/allen kb C {:limit 3}))))
      (is (= 1 (count (scen/scenarios iv/allen kb C {:limit 1})))))
    (testing "the unbounded sequence is lazy, so a caller can take a prefix of it"
      (is (= 4 (count (take 4 (scen/scenarios iv/allen kb C))))))
    (testing "every scenario it hands back is complete and consistent"
      (doseq [s (scen/scenarios iv/allen kb C {:limit 6})]
        (is (complete? s 3))
        (is (consistent? iv/allen s))))
    (testing "and they are all different — an enumeration, not a repetition"
      (let [ss (scen/scenarios iv/allen kb C {:limit 6})]
        (is (= (count ss) (count (set ss))))))))

;; ---- determinism ---------------------------------------------------------

(tu/deftest-kb the-same-facts-give-the-same-scenario
  (tu/with-terms [A B D]
    (let [facts [(list 'sharesTimeWith A B)
                 (list 'sharesTimeWith B D)
                 (list 'precedes D A)]]
      (doseq [f facts] (v/assert kb f C))
      (let [first-run  (scen/scenario iv/allen kb C)
            second-run (scen/scenario iv/allen kb C)
            ;; taken before the reorder below, which is the whole comparison: a prefix
            ;; read after it and compared with itself would agree whatever the search did
            first-four (scen/scenarios iv/allen kb C {:limit 4})]
        (testing "repeated calls agree"
          (is (= first-run second-run)))
        (testing "and so does the same content asserted the other way round, at fresh
                  handles — the choice keys on what is written, never on a handle id"
          (doseq [f facts] (v/retract! kb (v/handle-of kb f C)))
          (is (empty? (qkb/nodes (qkb/network kb iv/allen C))))
          (doseq [f (reverse facts)] (v/assert kb f C))
          (is (= first-run (scen/scenario iv/allen kb C))))
        (testing "the prefixes of the enumeration agree too, not merely its first element"
          ;; and there is a prefix to agree about: two empty enumerations are equal
          ;; whatever the reorder did to the search
          (is (seq first-four) "the network admits no arrangement at all")
          (is (= first-four (scen/scenarios iv/allen kb C {:limit 4}))))))))

(tu/deftest-kb five-nodes-in-four-orders-give-one-enumeration
  ;; Five nodes leave the search ties at more than one depth, where three nodes leave it
  ;; one.  Each order is asserted at fresh handles, and the comparison is the public
  ;; enumeration's eight-scenario prefix.
  (tu/with-terms [A B D E F]
    (doseq [[calc facts] {:allen [(list 'sharesTimeWith A B) (list 'sharesTimeWith B D)
                                  (list 'precedes D E) (list 'sharesTimeWith E F)
                                  (list 'precedes A F)]
                          :rcc8  [(list 'regionOverlaps A B) (list 'regionOverlaps B D)
                                  (list 'nonTangentialProperPart D E)
                                  (list 'regionOverlaps E F) (list 'regionOverlaps A F)]}]
      (let [orders [facts (reverse facts) (concat (drop 2 facts) (take 2 facts))
                    (concat (take-last 1 facts) (butlast facts))]
            prefix (fn [order]
                     (doseq [f order] (v/assert kb f C))
                     (let [ss (v/qualitative-scenarios kb calc C 8)]
                       (doseq [f order] (v/retract! kb (v/handle-of kb f C)))
                       ss))
            [p & ps] (map prefix orders)]
        (testing (name calc)
          (is (< 1 (count p)) "the network leaves no choice to tie-break")
          (is (every? #{p} ps)))))))

;; ---- calculus-generic ----------------------------------------------------

(tu/deftest-kb the-same-search-runs-over-a-spatial-network
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "RCC-8 composition pins the whole network, so there is one arrangement"
      (let [ss (scen/scenarios sp/rcc8 kb C {:limit 5})]
        (is (= 1 (count ss)))
        (is (= #{:ntpp} (get (first ss) [A D])))))
    (testing "a looser spatial fact leaves a real choice, and it is made consistently"
      (tu/with-terms [E]
        (v/assert kb (list 'regionOverlaps A E) C)
        (let [s (scen/scenario sp/rcc8 kb C)]
          (is (complete? s 4))
          (is (consistent? sp/rcc8 s))
          (is (contains? (sp/spatial-denotation 'regionOverlaps) (first (get s [A E])))))))
    (testing "and the two calculi never see each other's facts, so the interval network of
              a KB holding only spatial ones has nothing in it to arrange"
      (is (empty? (qkb/nodes (qkb/network kb iv/allen C))))
      (is (= [{}] (scen/scenarios iv/allen kb C {:limit 3}))))))

(tu/deftest-kb a-context-with-nothing-in-it-has-the-empty-scenario
  (tu/with-terms [CxEmpty]
    (v/assert kb (list 'genlCx CxEmpty C) C)
    (testing "no nodes means no pairs to decide, which is one arrangement and not none"
      (is (= [{}] (scen/scenarios iv/allen kb CxEmpty {:limit 3})))
      (is (= {} (scen/scenario iv/allen kb CxEmpty))))))
