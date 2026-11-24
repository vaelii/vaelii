;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nmtms-test
  "The non-monotonic truth-maintenance system: a default conclusion is withdrawn
  when a stronger contradiction *arrives later* and revived when the contradiction
  is retracted; an irreducible (known-true) clash is reported, not thrown.

  A default/default rebuttal is a dilemma: both sides stay believed and `contradictions`
  reports the pair (docs/nmtms.md, \"There is no second axis\").  Undercutting is an
  `exceptWhen`, which `except_test` covers."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the headline: order independence -----------------------------------

(tu/deftest-kb default-withdrawn-when-negation-arrives-later
  (let [bird (tu/tmp-type) animal (tu/tmp-type) flies (tu/tmp-pred) sky (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxUniverse)
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
    (v/assert kb (list bird sky) 'CxUniverse)
    (testing "the default conclusion holds first"
      (is (seq (v/sentexes-matching kb (list flies sky) 'CxUniverse))))
    (testing "a stronger negation asserted LATER withdraws it (a monotone JTMS cannot)"
      (v/assert kb (list 'not (list flies sky)) 'CxUniverse {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list flies sky) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'not (list flies sky)) 'CxUniverse)))
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb defeated-default-revives-when-defeater-retracted
  (let [bird (tu/tmp-type) animal (tu/tmp-type) flies (tu/tmp-pred) sky (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxUniverse)
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
    (v/assert kb (list bird sky) 'CxUniverse)
    (let [no-fly (v/assert kb (list 'not (list flies sky)) 'CxUniverse {:strength :monotonic})]
      (is (empty? (v/sentexes-matching kb (list flies sky) 'CxUniverse)))       ; defeated
      (v/retract! kb no-fly)
      (testing "removing the defeater revives the default conclusion"
        (is (seq (v/sentexes-matching kb (list flies sky) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (list 'not (list flies sky)) 'CxUniverse)))))))

;; ---- penguins, now order-independent ------------------------------------

(tu/deftest-kb penguin-asserted-after-the-default-still-does-not-fly
  (let [penguin (tu/tmp-type) bird (tu/tmp-type) animal (tu/tmp-type)
        flies (tu/tmp-pred) robin (tu/tmp-ind) tweety (tu/tmp-ind)]
    (v/assert kb (list 'genl penguin bird) 'CxUniverse)
    (v/assert kb (list 'genl bird animal)  'CxUniverse)
    (v/assert-rule kb [(list penguin '?x)] (list 'not (list flies '?x)) 'CxUniverse {:direction :forward})   ; bare rule
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)  ; defeasible default
    (v/assert kb (list bird robin) 'CxUniverse)
    (testing "Robin flies by default"
      (is (seq (v/sentexes-matching kb (list flies robin) 'CxUniverse))))
    (testing "Tweety, learned to be a penguin AFTER the default fired, does not fly"
      ;; Known-true, so the bare rule concludes at :monotonic and out-ranks the
      ;; :default flight conclusion.  This asserts that the *withdrawal* happens
      ;; even though the default fired first — belief is recomputed, not accumulated.
      (v/assert kb (list penguin tweety) 'CxUniverse {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'not (list flies tweety)) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list flies robin) 'CxUniverse))))))         ; Robin unaffected

(tu/deftest-kb retracting-the-support-of-a-defeated-default-sweeps-it
  ;; a defeated default is kept for revival only while something still derives it
  (let [foo (tu/tmp-pred) bar (tu/tmp-pred) x (tu/tmp-ind)]
    (v/assert kb (list foo x) 'CxUniverse)
    (v/assert kb (tu/default-rule [(list foo '?x)] (list bar '?x)) 'CxUniverse)
    (v/assert kb (list 'not (list bar x)) 'CxUniverse {:strength :monotonic})   ; defeats (bar X)
    (let [handle-of (fn [sen] (:id (first (filter #(= sen (:sentence %))
                                                  (v/find-sentexes kb x)))))
          foo-h (handle-of (list foo x))
          bar-h (handle-of (list bar x))]
      (is (some? bar-h))
      (is (not (v/believed? kb bar-h)))                                      ; defeated, OUT
      (let [result (v/retract! kb foo-h)]
        (testing "the defeated conclusion had no surviving derivation and is swept"
          (is (nil? (v/sentex kb bar-h)))                              ; gone from the store
          (is (nil? (handle-of (list bar x))))                          ; and the term index
          ;; foo X, bar X, and the contradicts and defeat its negation pair placed
          (is (= 4 (:removed-sentexes result))))))))

;; ---- the dilemma the engine declines to decide --------------------------

(tu/deftest-kb nixon-diamond-is-reported-as-a-dilemma-not-decided
  ;; `except_test` asserts that both sides coexist; this asserts the report
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind)]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))       'CxUniverse)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    (let [pos (v/handle-of kb (list pacifist nixon)             'CxUniverse)
          neg (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)]
      (testing "both sides survive settle — neither is defeated"
        (is (true? (v/believed? kb pos)))
        (is (true? (v/believed? kb neg)))
        (is (= :default (v/defeat-class kb pos)))
        (is (= :default (v/defeat-class kb neg))))
      (testing "the pair is reported once, as a dilemma"
        (let [ds (v/contradictions kb)]
          (is (= 1 (count ds)))
          (is (= #{pos neg} (:nogood (first ds))))
          (is (= 'contradicts (first (:sentence (first ds)))))))
      (testing "and both arguments are handed over, for the application to rank"
        (let [sides (:sides (first (v/contradictions kb)))]
          (is (= 2 (count sides)))
          (is (every? #(seq (:justifications %)) sides))
          (is (every? #(= :default (:defeat-class %)) sides))))
      (testing "a dilemma is not a conflict — nothing here is irreducible"
        (is (empty? (v/conflicts kb))))
      (testing "and nothing was handed to the edge solver"
        (is (nil? (v/last-program kb)))))))

(tu/deftest-kb irreducible-clash-is-reported-not-thrown
  (let [happy (tu/tmp-pred) tom (tu/tmp-ind)]
    (v/assert kb (list happy tom) 'CxUniverse {:strength :monotonic})
    (is (some? (v/assert kb (list 'not (list happy tom)) 'CxUniverse {:strength :monotonic})))
    (let [conflicts (v/conflicts kb)]
      (testing "the clash surfaces as a prioritized contradiction sentence"
        (is (= 1 (count conflicts)))
        (is (= 'contradicts (first (:sentence (first conflicts))))))
      (testing "neither known-true belief was silently dropped"
        (is (seq (v/sentexes-matching kb (list happy tom) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list 'not (list happy tom)) 'CxUniverse)))))))

(tu/deftest-kb hard-clash-reported-once-even-alongside-a-dilemma
  ;; hard clashes are collected at the terminal round, not once per round
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind) happy (tu/tmp-pred) tom (tu/tmp-ind)]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))       'CxUniverse)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)                       ; default/default → dilemma
    (v/assert kb (list happy tom) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list happy tom)) 'CxUniverse {:strength :monotonic}) ; irreducible clash
    (testing "the hard clash is reported exactly once, and only it"
      (is (= 1 (count (v/conflicts kb))))
      (is (= #{(v/handle-of kb (list happy tom)             'CxUniverse)
               (v/handle-of kb (list 'not (list happy tom)) 'CxUniverse)}
             (:nogood (first (v/conflicts kb))))
          "the dilemma's handles must not appear in the conflict report"))
    (testing "and the dilemma is reported exactly once, on the other reader"
      (is (= 1 (count (v/contradictions kb))))
      (is (seq (v/sentexes-matching kb (list pacifist nixon) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'not (list pacifist nixon)) 'CxUniverse))))))

(tu/deftest-kb contradiction-detected-when-positive-sits-in-a-more-specific-context
  (let [flies (tu/tmp-pred) sky (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxSpecific 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'not (list flies sky)) 'CxUniverse {:strength :monotonic})  ; general
    (v/assert kb (list flies sky) 'CxSpecific)                              ; specific sees general
    (testing "CxSpecific sees both, so the default is defeated there"
      (is (empty? (v/sentexes-matching kb (list flies sky) 'CxSpecific)))
      (is (empty? (v/conflicts kb))))))

;; ---- the report is republished each settle, and must not go stale -------

(tu/deftest-kb a-dilemmas-report-names-every-justification-behind-each-side
  ;; A report is carried forward while its handles stay out of the region.  A second
  ;; derivation of one side relabels nothing, so a memo keyed on the region alone would
  ;; carry a report naming fewer justifications than the KB holds.
  (tu/with-terms [quaker pacifist republican churchgoer Nixon]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))            'CxUniverse)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker Nixon)     'CxUniverse)
    (v/assert kb (list republican Nixon) 'CxUniverse)
    (let [pos (v/handle-of kb (list pacifist Nixon) 'CxUniverse)]
      (is (= 1 (count (v/contradictions kb))) "the dilemma is reported")
      ;; a second rule reaching the same conclusion: no belief moves, no label moves
      (v/assert kb (tu/default-rule [(list churchgoer '?x)] (list pacifist '?x)) 'CxUniverse)
      (v/assert kb (list churchgoer Nixon) 'CxUniverse)
      (is (= 2 (count (v/supporting-justifications kb pos)))
          "the KB now holds two derivations of the positive side")
      (let [c   (some (fn [c] (when (some #(= pos (:handle %)) (:sides c)) c))
                      (v/contradictions kb))
            ids (fn [js] (set (map :id js)))]
        (is (some? c) "the dilemma is still reported")
        (is (= (into {} (for [s (:sides c)]
                          [(:handle s) (ids (v/supporting-justifications kb (:handle s)))]))
               (into {} (for [s (:sides c)] [(:handle s) (ids (:justifications s))])))
            "and the report names both of them, not the one it named last settle")))))

;; ---- a plain rebuttal never reaches the `Solver` protocol ---------------------

(tu/deftest-kb an-installed-solver-is-never-asked-to-decide-a-plain-rebuttal
  ;; the solver would defeat the positive side if asked, and counts the asks, so only a
  ;; solver that is never consulted passes
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind) called (atom 0)]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))       'CxUniverse)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/set-solver kb
                  (reify vaelii.impl.types.solve/Solver
                    (solve [_ {:keys [assumptions contradictions]}]
                      (swap! called inc)
                      {:defeat (into #{} (comp (mapcat :nogood)
                                               (filter assumptions)
                                               (filter #(= pacifist (first (:sentence (v/sentex kb %))))))
                                     contradictions)
                       :violated []})))
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    (testing "the solver was never invoked"
      (is (zero? @called))
      (is (nil? (v/last-program kb))))
    (testing "so belief is what the engine decided, not what the plugin would have"
      (is (seq (v/sentexes-matching kb (list pacifist nixon) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'not (list pacifist nixon)) 'CxUniverse)))
      (is (= 1 (count (v/contradictions kb)))))))
