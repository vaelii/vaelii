;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.why-not-nearest-test
  "`why-not`'s `{:nearest n}`: which rule nearly fired, and what it was still waiting for.

  `:not-stored` is the emptiest answer the entry point has — no handle, no support, no defeat —
  and it is the one a reader whose rule was *supposed* to conclude the goal gets.  What
  they need next is the antecedent they have not asserted, and these tests are about
  getting that named.

  Two contracts beside the answer itself.  The search is **off unless asked for**, since
  `why-not` is called in a loop over a conflict list and a backward search per call would
  change what the entry point costs.  And the ranking keys on **content** — how many antecedents
  are satisfied, then the rule's own sentence — never on the rule's handle, which is
  assertion order."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.cli :as cli]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the answer -----------------------------------------------------------

(tu/deftest-kb a-two-antecedent-rule-with-one-satisfied-names-the-other
  ;; The everyday case: a grandparent rule, one parent link asserted and the other not.
  ;; `:not-stored` on its own says the KB has never heard of the conclusion; `:nearest`
  ;; says which half of the reason it is still waiting for.
  (tu/with-terms [parentOf grandparentOf Ann Bob Cid CxKin]
    (v/assert kb (list 'genlCx CxKin 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxKin)
    (v/assert kb (list parentOf Ann Bob) CxKin)
    (let [goal (list grandparentOf Ann Cid)
          r    (v/why-not kb goal CxKin {:nearest 3})
          near (first (:nearest r))]
      (testing "the goal is still not stored — `:nearest` adds to that answer, it does not replace it"
        (is (= :not-stored (:reason r)))
        (is (false? (:believed? r))))
      (testing "one rule came close, and it is the one that concludes this predicate"
        (is (= 1 (count (:nearest r))))
        (is (integer? (:rule near)))
        (is (= (list grandparentOf '?x '?z) (last (:rule-sentence near)))))
      (testing "the antecedent the KB can satisfy, written in the rule's own variables"
        (is (= [(list parentOf Ann '?y)] (:satisfied near))))
      (testing "and the one it cannot — the fact to assert"
        (is (= [(list parentOf '?y Cid)] (:missing near))))
      (testing "with the bindings the goal forced on the rule, ready to hand to `query`"
        (is (= {'?x Ann '?z Cid} (:bindings near))))
      (testing "the search reports which of its bounds it ran into, if any"
        (is (= :node-engine (:engine (:nearest-search r))))
        (is (= :complete (:status (:nearest-search r))))
        (is (= v/default-nearest-depth (:max-depth (:nearest-search r))))
        (is (= v/default-nearest-ms (:max-ms (:nearest-search r))))))))

(tu/deftest-kb antecedents-satisfied-under-different-bindings-of-an-open-variable-are-not-all-satisfied
  ;; `?t` is shared by all three antecedents and the goal does not bind it.  Each
  ;; antecedent holds for some `?t` on its own (Dover, Dover or Calais, Calais), and no one
  ;; `?t` satisfies all three, so the rule does not fire for Ann.
  (tu/with-terms [livesIn coastal_town ferryTo reachable_by_ferry Ann Bob Dover Calais CxTravel]
    (v/assert kb (list 'genlCx CxTravel 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list livesIn '?a '?t) (list coastal_town '?t) (list ferryTo Dover '?t)]
                   (list reachable_by_ferry '?a) CxTravel)
    (doseq [f [(list livesIn Ann Dover) (list livesIn Bob Calais) (list coastal_town Dover)
               (list coastal_town Calais) (list ferryTo Dover Calais)]]
      (v/assert kb f CxTravel))
    (is (seq (v/query kb (list reachable_by_ferry Bob) CxTravel {:max-depth 1}))
        "the control: Bob's ?t joins")
    (let [near (first (:nearest (v/why-not kb (list reachable_by_ferry Ann) CxTravel {:nearest 1})))]
      (is (= 2 (count (:satisfied near))))
      (is (= 1 (count (:missing near))) "an antecedent is missing although each holds alone")
      (is (seq (v/query kb (:satisfied near) CxTravel)) "the satisfied antecedents join")
      (is (empty? (v/query kb (into (:satisfied near) (:missing near)) CxTravel))
          "and the missing one breaks the join"))))

(tu/deftest-kb the-rule-that-is-closest-is-reported-first
  ;; Two rules concluding one goal, one of them a step further from firing.  The ranking
  ;; is what makes the report readable — and it is on how much is satisfied, never on
  ;; which rule was asserted first, which is what a handle tie-break would be.
  (tu/with-terms [likes trusts knows friendOf Ann Bob CxSoc]
    (v/assert kb (list 'genlCx CxSoc 'CxUniverse) 'CxUniverse)
    ;; the near one: one of two antecedents holds
    (v/assert-rule kb [(list likes '?a '?b) (list trusts '?a '?b)]
                   (list friendOf '?a '?b) CxSoc)
    ;; the far one: neither of its two holds
    (v/assert-rule kb [(list knows '?a '?b) (list knows '?b '?a)]
                   (list friendOf '?a '?b) CxSoc)
    (v/assert kb (list likes Ann Bob) CxSoc)
    (let [r    (v/why-not kb (list friendOf Ann Bob) CxSoc {:nearest 5})
          rows (:nearest r)]
      (is (= 2 (count rows)) "both rules are candidates")
      (testing "the one with an antecedent already satisfied comes first"
        (is (= 1 (count (:satisfied (first rows)))))
        (is (= 0 (count (:satisfied (second rows))))))
      (testing "and each names what it is missing"
        (is (= [(list trusts Ann Bob)] (:missing (first rows))))
        (is (= 2 (count (:missing (second rows)))))))))

(tu/deftest-kb the-report-is-a-function-of-the-knowledge-and-not-of-its-arrival-order
  ;; Two rules asserted in either order rank identically: the tie-break is the rule's own
  ;; sentence, never its handle.  Handles are allocated in assertion order, so a ranking
  ;; keyed on one would make this report a fact about how the KB was loaded.
  (tu/with-terms [p q goal A B CxOrd]
    (v/assert kb (list 'genlCx CxOrd 'CxUniverse) 'CxUniverse)
    (let [one  #(v/assert-rule kb [(list p '?x '?y)] (list goal '?x '?y) CxOrd)
          two  #(v/assert-rule kb [(list q '?x '?y)] (list goal '?x '?y) CxOrd)
          ;; the handles differ between the two arms — they are allocated in assertion
          ;; order, which is the whole point — so what is compared is what the report
          ;; *says*: the missing antecedents, in the order they are ranked
          read #(mapv :missing (:nearest (v/why-not kb (list goal A B) CxOrd {:nearest 5})))
          arm  (fn [fs] (let [hs (mapv (fn [f] (f)) fs)
                              r  (read)]
                          (run! #(v/retract! kb %) hs)
                          r))
          forward  (arm [one two])
          backward (arm [two one])]
      (is (= 2 (count forward)))
      (is (= forward backward)
          "the same two rules, ranked the same way, whichever was asserted first"))))

;; ---- off unless asked for -------------------------------------------------

(tu/deftest-kb the-search-runs-only-when-nearest-asks-for-it
  (tu/with-terms [p goal A B CxOff]
    (v/assert kb (list 'genlCx CxOff 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list p '?x '?y)] (list goal '?x '?y) CxOff)
    (testing "the plain sentence arity carries neither key"
      (let [r (v/why-not kb (list goal A B) CxOff)]
        (is (= :not-stored (:reason r)))
        (is (not (contains? r :nearest)))
        (is (not (contains? r :nearest-search)))))
    (testing "and so does the option map that names no search"
      (let [r (v/why-not kb (list goal A B) CxOff {})]
        (is (not (contains? r :nearest)))))
    (testing "a zero asks for nothing and runs nothing"
      (is (not (contains? (v/why-not kb (list goal A B) CxOff {:nearest 0}) :nearest))))))

(tu/deftest-kb a-nearest-that-is-not-a-count-is-refused-rather-than-read-as-no-request
  ;; `{:nearest "3"}` read as no request answered the ordinary `:not-stored`, which is
  ;; exactly what a goal no rule concludes gives — the silence the key check refuses for a
  ;; misspelt key, here for a mistyped value.  Zero stays the request for nothing.
  (tu/with-terms [p goal A B CxOff]
    (v/assert kb (list 'genlCx CxOff 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list p '?x '?y)] (list goal '?x '?y) CxOff)
    (doseq [bad ["3" -1 1.5 :three]]
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (v/why-not kb (list goal A B) CxOff {:nearest bad}))
                  (pr-str bad))]
        (is (= :unknown-option (:type (ex-data e))) (pr-str bad))))
    (testing "nil is the absent key"
      (is (not (contains? (v/why-not kb (list goal A B) CxOff {:nearest nil}) :nearest))))))

(tu/deftest-kb nearest-is-attached-to-not-stored-alone
  ;; Every other reason already names the thing that stopped the sentence, so a search
  ;; for near misses would be work with nothing to report.
  (tu/with-terms [flies Tweety CxBird]
    (v/assert kb (list 'genlCx CxBird 'CxUniverse) 'CxUniverse)
    (v/assert kb (list flies Tweety) CxBird)
    (let [r (v/why-not kb (list flies Tweety) CxBird {:nearest 3})]
      (is (true? (:believed? r)))
      (is (not (contains? r :nearest))))))

(tu/deftest-kb the-two-bounds-are-the-callers-to-move
  (tu/with-terms [p goal A B CxB]
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list p '?x '?y)] (list goal '?x '?y) CxB)
    (let [s (:nearest-search (v/why-not kb (list goal A B) CxB
                                        {:nearest 1 :max-depth 1 :max-ms 50}))]
      (is (= 1 (:max-depth s)))
      (is (= 50 (:max-ms s)))
      (is (contains? #{:complete :bounded :timeout} (:status s))))))

(tu/deftest-kb the-shell-flag-belongs-to-the-goal-form-and-is-refused-on-a-handle
  ;; `why-not` takes a goal *or* a handle, and `--nearest` belongs to the first: a stored
  ;; handle is stored, so `:not-stored` is not an answer it can get and there are no near
  ;; misses to look for.  Honoured for one operand shape and dropped for the other, the
  ;; flag would read identically from outside either way.
  (tu/with-terms [p goal A B C CxShell]
    (v/assert kb (list 'genlCx CxShell 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list p '?x '?y)] (list goal '?x '?y) CxShell)
    ;; `(p A B)` fires the rule and gives a stored handle to ask the other form about;
    ;; `(goal A C)` is the one nothing concludes
    (let [h (v/assert kb (list p A B) CxShell)]
      (testing "the goal form runs the search"
        (let [r (cli/dispatch kb "why-not" [(list goal A C) CxShell] {:nearest "3"})]
          (is (= :not-stored (:reason r)))
          (is (= 1 (count (:nearest r))))))
      (testing "the handle form is refused rather than answered without the search"
        (is (= :unknown-option
               (try (cli/dispatch kb "why-not" [h] {:nearest "3"})
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))))

(tu/deftest-kb an-option-the-entry-point-does-not-read-is-refused
  ;; A misspelt `:nearset` would answer the ordinary `:not-stored`, which is exactly what
  ;; a goal no rule concludes gives — so the failure is invisible unless it is refused.
  (tu/with-terms [goal A B CxR]
    (v/assert kb (list 'genlCx CxR 'CxUniverse) 'CxUniverse)
    (is (= :unknown-option
           (try (v/why-not kb (list goal A B) CxR {:nearset 3})
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
    (is (= v/why-not-opt-keys #{:nearest :max-depth :max-ms :content?}))))

;; ---- what a bound costs ---------------------------------------------------

(tu/deftest-kb a-rule-deeper-than-the-depth-bound-is-not-reported-and-the-answer-says-so
  ;; The node engine's termination *is* the depth bound, so a chain longer than it is not
  ;; searched.  The answer reports the bound that was in force rather than an
  ;; empty `:nearest` that reads like "no rule concludes this".
  (tu/with-terms [a b c goal A B CxDeep]
    (v/assert kb (list 'genlCx CxDeep 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list a '?x '?y)] (list b '?x '?y) CxDeep)
    (v/assert-rule kb [(list b '?x '?y)] (list c '?x '?y) CxDeep)
    (v/assert-rule kb [(list c '?x '?y)] (list goal '?x '?y) CxDeep)
    (let [shallow (v/why-not kb (list goal A B) CxDeep {:nearest 5 :max-depth 1})
          deeper  (v/why-not kb (list goal A B) CxDeep {:nearest 5 :max-depth 3})]
      (is (= 1 (count (:nearest shallow))) "one rewrite reaches one rule")
      (is (< (count (:nearest shallow)) (count (:nearest deeper)))
          "and a deeper bound reaches the chain behind it")
      (is (= 1 (:max-depth (:nearest-search shallow)))
          "the bound in force is part of the answer, so an empty list is readable"))))

(tu/deftest-kb a-rule-the-search-proved-through-is-not-a-near-miss
  ;; a backward rule answers the goal, so it is not stored and the search finds a
  ;; productive branch beside the dead one; only the dead branch's rule is reported
  (tu/with-terms [goal_t pe qe re Ann]
    (v/assert-rule kb [(list pe '?x)] (list goal_t '?x) 'CxUniverse {:direction :backward})
    (v/assert-rule kb [(list qe '?x) (list re '?x)] (list goal_t '?x) 'CxUniverse
                   {:direction :backward})
    (v/assert kb (list pe Ann) 'CxUniverse)
    (v/assert kb (list qe Ann) 'CxUniverse)
    (let [r (v/why-not kb (list goal_t Ann) 'CxUniverse {:nearest 3})]
      (is (= :not-stored (:reason r)))
      (is (= [[(list re Ann)]] (mapv :missing (:nearest r))))
      (is (= [3 1] ((juxt :nodes :dead) (:nearest-search r)))
          "the productive node and its parent are live, the other rule's node dead"))))
