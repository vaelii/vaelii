;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nmtms-test
  "The non-monotonic truth-maintenance system: a default conclusion is withdrawn
  when a stronger contradiction *arrives later* and revived when the contradiction
  is retracted; an irreducible (known-true) clash is reported, not thrown.

  What the engine does **not** do is arbitrate a default/default rebuttal.  Two rules
  concluding `P` and `¬P` with neither naming the other's case, and neither more
  specific, is a genuine dilemma: both sides stay believed, nothing is defeated, and
  the pair is reported by `contradictions` for the application to rank
  (docs/exceptions.md, \"What surfaces where\").  Deciding it would be an arbitrary
  pick dressed up as an inference, and it would destroy the two arguments an
  application wants to weigh.  Undercutting — \"this rule does not apply here\" — is
  written as an `exceptWhen` on the rule instead, and `except_test` covers it."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

;; ---- the headline: order independence -----------------------------------

(tu/deftest-kb default-withdrawn-when-negation-arrives-later
  (let [bird (tu/tmp-type) animal (tu/tmp-type) flies (tu/tmp-pred) sky (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxUniverse)
    (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
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
    (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
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
    (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)  ; defeasible default
    (v/assert kb (list bird robin) 'CxUniverse)
    (testing "Robin flies by default"
      (is (seq (v/sentexes-matching kb (list flies robin) 'CxUniverse))))
    (testing "Tweety, learned to be a penguin AFTER the default fired, does not fly"
      ;; Known-true, so the bare rule concludes at :monotonic and out-ranks the
      ;; :default flight conclusion.  What this pins is that the *withdrawal* happens
      ;; even though the default fired first — belief is recomputed, not accumulated.
      (v/assert kb (list penguin tweety) 'CxUniverse {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'not (list flies tweety)) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list flies robin) 'CxUniverse))))))         ; Robin unaffected

(tu/deftest-kb retracting-the-support-of-a-defeated-default-sweeps-it
  ;; A defeated default kept "for revival" must still be swept when the SAME
  ;; retraction removes its only derivation — otherwise it leaks an unrevivable
  ;; orphan into the stores (regression for the retract* groundability sweep).
  (let [foo (tu/tmp-pred) bar (tu/tmp-pred) x (tu/tmp-ind)]
    (v/assert kb (list foo x) 'CxUniverse)
    (v/assert kb (default-rule [(list foo '?x)] (list bar '?x)) 'CxUniverse)
    (v/assert kb (list 'not (list bar x)) 'CxUniverse {:strength :monotonic})   ; defeats (bar X)
    (let [handle-of (fn [sen] (:id (first (filter #(= sen (:sentence %))
                                                  (v/find-sentexes kb x)))))
          foo-h (handle-of (list foo x))
          bar-h (handle-of (list bar x))]
      (is (some? bar-h))
      (is (not (v/in? kb bar-h)))                                      ; defeated, OUT
      (let [result (v/retract! kb foo-h)]
        (testing "the defeated conclusion had no surviving derivation and is swept"
          (is (nil? (v/sentex kb bar-h)))                              ; gone from the store
          (is (nil? (handle-of (list bar x))))                          ; and the term index
          (is (= 2 (:removed-sentexes result))))))))                     ; foo X + bar X

;; ---- the dilemma the engine declines to decide --------------------------

(tu/deftest-kb nixon-diamond-is-reported-as-a-dilemma-not-decided
  ;; Two equally-specific defaults collide with no strength and no specificity to
  ;; separate them.  `except_test` pins that both sides coexist; what this adds is the
  ;; *reporting* contract — a dilemma surfaces through `contradictions`, carrying both
  ;; handles and both sides' justifications, and never through `conflicts`.
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind)]
    (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))       'CxUniverse)
    (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    (let [pos (v/handle-of kb (list pacifist nixon)             'CxUniverse)
          neg (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)]
      (testing "both sides survive settle — neither is defeated"
        (is (true? (v/in? kb pos)))
        (is (true? (v/in? kb neg)))
        (is (= :default (v/defeat-class kb pos)))
        (is (= :default (v/defeat-class kb neg))))
      (testing "the pair is reported once, as a dilemma"
        (let [ds (v/contradictions kb)]
          (is (= 1 (count ds)))
          (is (= #{pos neg} (:nogood (first ds))))
          (is (= 'contradicts (first (:sentence (first ds)))))))
      (testing "and both arguments are handed over, which is the point of not deciding"
        ;; an application ranks the dilemma from the justifications; a decision made
        ;; here would have thrown one of them away
        (let [sides (:sides (first (v/contradictions kb)))]
          (is (= 2 (count sides)))
          (is (every? #(seq (:justifications %)) sides))
          (is (every? #(= :default (:defeat-class %)) sides))))
      (testing "a dilemma is not a conflict — nothing here is irreducible"
        (is (empty? (v/conflicts kb))))
      (testing "and nothing was handed to the edge solver"
        (is (nil? (v/last-program kb)))))))

(tu/deftest-kb irreducible-clash-is-reported-not-thrown
  ;; Two known-true facts contradict: nothing can defeat either, so the
  ;; contradiction sentence IS the result — reported, never an exception.
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
  ;; A persistent hard clash reappears in every settle round; it must be reported
  ;; ONCE, not once per round.  A coexisting dilemma sits in the same settle without
  ;; being swept up into the conflict report, and vice versa: the two readers must
  ;; stay separate even when both have something to say about the same settle.
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind) happy (tu/tmp-pred) tom (tu/tmp-ind)]
    (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))       'CxUniverse)
    (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
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
  ;; Detection is context-symmetric: the negation is in the general context, the
  ;; positive in a context that sees it — the clash still surfaces (and is resolved).
  (let [flies (tu/tmp-pred) sky (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxSpecific 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'not (list flies sky)) 'CxUniverse {:strength :monotonic})  ; general
    (v/assert kb (list flies sky) 'CxSpecific)                              ; specific sees general
    (testing "CxSpecific sees both, so the default is defeated there"
      (is (empty? (v/sentexes-matching kb (list flies sky) 'CxSpecific)))
      (is (empty? (v/conflicts kb))))))

;; ---- the report is republished each settle, and must not go stale -------

(tu/deftest-kb a-dilemmas-report-names-every-justification-behind-each-side
  ;; The readings are recomputed on every settle, so a pair whose handles the settle's
  ;; region did not hold has its report **carried forward** — that memo is what keeps
  ;; republishing the standing dilemmas off the per-assert cost.
  ;;
  ;; A *second derivation of one side* is the case that breaks a memo keyed on the
  ;; region alone, and the one belief itself gives no sign of: a redundant
  ;; justification (an already-believed conclusion gaining another witness that confers
  ;; no stronger a class) is precisely the write the JTMS declines to relabel for, so
  ;; the side's supporting set grows while its handle never enters a region.  A carried
  ;; report then hands the application fewer reasons than the KB holds — and the reasons
  ;; are exactly what it is being asked to rank in a dilemma the engine declines to
  ;; decide.
  (tu/with-terms [quaker pacifist republican churchgoer Nixon]
    (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))            'CxUniverse)
    (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker Nixon)     'CxUniverse)
    (v/assert kb (list republican Nixon) 'CxUniverse)
    (let [pos (v/handle-of kb (list pacifist Nixon) 'CxUniverse)]
      (is (= 1 (count (v/contradictions kb))) "the dilemma is reported")
      ;; a second rule reaching the same conclusion: no belief moves, no label moves
      (v/assert kb (default-rule [(list churchgoer '?x)] (list pacifist '?x)) 'CxUniverse)
      (v/assert kb (list churchgoer Nixon) 'CxUniverse)
      (is (= 2 (count (v/supporting-justifications kb pos)))
          "the KB now holds two derivations of the positive side")
      (let [side (some (fn [c] (some #(when (= pos (:handle %)) %) (:sides c)))
                       (v/contradictions kb))]
        (is (some? side) "the dilemma is still reported")
        (is (= (count (v/supporting-justifications kb pos))
               (count (:justifications side)))
            "and the report names both of them, not the one it named last settle")))))

;; ---- a plain rebuttal never reaches the `Solver` protocol ---------------------

(tu/deftest-kb an-installed-solver-is-never-asked-to-decide-a-plain-rebuttal
  ;; `set-solver` is public and the protocol exists — arbitration is the right answer for
  ;; nogoods that are *not* plain rebuttals.  What is never routed there is a
  ;; default/default rebuttal: the engine represents it as a dilemma, so it is not
  ;; offered to any solver at all.
  ;;
  ;; The solver installed here would happily defeat the positive side if asked.  That
  ;; is the point: the guarantee is not "a solver behaves well", it is "a solver is
  ;; never consulted", which only a solver that *records being called* can witness.
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind) called (atom 0)]
    (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))       'CxUniverse)
    (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
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

;; ---- the solver split, guarded at both ends -----------------------------
;;
;; Only `:default` content is ever decided; `:monotonic` is the fixed background a solve
;; reasons *from*.  `decide-nogood` already guarantees the input half — a tie is
;; contested only when every member is defeasible and equal in class — and the test
;; above guarantees a rebuttal never reaches a solver at all.  The two guards are what
;; stands between a *third-party* solver and known-true content, since `set-solver`
;; takes any implementation, and the cost of a regression here is not a wrong answer: it
;; is the engine handing away something it knows to be true.

(tu/deftest-kb the-input-guard-refuses-a-contested-handle-that-is-not-defeasible
  ;; The classes are read before any defeat lands, because `defeat-class` reports nil
  ;; once a datum is OUT — after the fact the question cannot be asked at all.
  (let [happy (tu/tmp-pred) maybe (tu/tmp-pred) tom (tu/tmp-ind)]
    (v/assert kb (list happy tom) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list maybe tom) 'CxUniverse)
    (let [mono (v/handle-of kb (list happy tom) 'CxUniverse)
          dflt (v/handle-of kb (list maybe tom) 'CxUniverse)]
      (testing "a plain :default handle is eligible"
        (is (nil? (#'settle/check-solver-eligible kb #{dflt}))))
      (testing "a known-true one is refused, and the refusal names it"
        (let [e (try (#'settle/check-solver-eligible kb #{mono dflt})
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (instance? clojure.lang.ExceptionInfo e))
          (is (= :not-defeasible (:type (ex-data e))))
          (is (= [mono] (:handles (ex-data e))))
          (is (= [:monotonic] (:classes (ex-data e))))
          (is (= :default (:expected (ex-data e)))))))))

(deftest the-output-guard-drops-a-defeat-the-program-never-offered
  ;; An overreaching defeat is a bug in the solver, and the engine should neither obey
  ;; it nor fail because of it — so it is dropped with a warning rather than thrown.
  ;; No KB: a Program is a self-contained value, which is the whole point of the protocol.
  (let [prog (solve/program #{1 2}
                            [{:nogood #{1 2} :priority 1 :sentence '(contradicts (a) (b))}]
                            {1 {:sentence '(a) :context 'CxUniverse}
                             2 {:sentence '(b) :context 'CxUniverse}})]
    (is (= #{1 2} (:assumptions prog)) "the program really does offer only these two")
    (is (= #{1} (#'settle/accepted-defeat prog #{1 9}))
        "the offered half is kept and the handle outside the program is dropped")
    (is (= #{} (#'settle/accepted-defeat prog #{9})))
    (is (= #{} (#'settle/accepted-defeat prog nil)) "and a solver that decided nothing")))
