;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-rule-visibility-test
  "A visibility `(except (sentexHandle R))` whose target is a **rule**.

  docs/contexts.md says the removal is total — reads and derivations both.  A firing
  rests on its rule exactly as it rests on its facts (the stored justification
  carries the rule handle among its antecedents), and every arm of the machinery has
  to honor that, including the two whose triggers cannot come for free:

  * **Revival.**  `special/recheck-except` re-chains a rule target on departure,
    because its other arms are keyed on a *fact* target — `dependents` is empty once
    the firing is swept, and the predicate fan never matches a rule sentence — so
    without the rule arm nothing re-derives what the except was hiding.
  * **Backward chaining.**  `provers/candidate-rules` drops a rule the visibility
    hidden set hides from the asking context, so a goal in the ancestor set cannot rebuild
    through a hidden rule what forward chaining sweeps.

  Each test asserts one arm: the sweep of an existing firing, the block of a late one,
  the revival on retraction, the backward chainer's candidate filter, and the
  dispute-resolution shape (a justified dispute whose defeated side must vanish from
  every read surface, not only from the argue tree).  House rules as everywhere
  else: gensym'd temporaries via `tu/with-terms`, engine vocabulary literal, the
  neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- 1. sweeping ---------------------------------------------------------
;; DECISION (contexts.md, "The removal is total"): a late except sweeps what already
;; fired.  The except tests assert the fact arm of this; this asserts the rule arm —
;; the conclusion's own handle is never an except target here, so an empty read below
;; can only mean belief actually moved, not that a read filter hid it.

(tu/deftest-kb excepting-a-rule-sweeps-the-conclusions-it-derived
  (tu/with-terms [bird flies Tweety CxBird]
    (let [rh (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) CxBird)]
      (v/assert kb (list bird Tweety) CxBird)
      (testing "the rule fired before the except arrived"
        (is (seq (v/sentexes-matching kb (list flies Tweety) CxBird))))
      (v/assert kb (list 'except (sx/sentex-handle rh)) CxBird)
      (testing "a conclusion resting on a rule the ancestor set cannot see is swept"
        (is (empty? (v/sentexes-matching kb (list flies Tweety) CxBird))))
      (testing "and the backward chainer does not rebuild it through the hidden rule"
        (is (empty? (v/query kb (list flies Tweety) CxBird {:max-depth 2})))))))

;; ---- 2. blocking ---------------------------------------------------------
;; The placement-side twin: a firing that arrives after the except is never placed in
;; the ancestor set, for a hidden rule exactly as for a hidden antecedent.

(tu/deftest-kb a-fact-arriving-after-the-rule-was-excepted-concludes-nothing
  (tu/with-terms [bird flies Opus CxBird]
    (let [rh (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) CxBird)]
      (v/assert kb (list 'except (sx/sentex-handle rh)) CxBird)
      (v/assert kb (list bird Opus) CxBird)
      (testing "the hidden rule does not fire into the ancestor set"
        (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird)))))))

;; ---- 3. revival ----------------------------------------------------------
;; Belief-following, like every other fact: retracting the except restores the hidden
;; rule, and what it was deriving comes back.

(tu/deftest-kb retracting-the-except-re-derives-what-the-rule-concluded
  (tu/with-terms [bird flies Tweety CxBird]
    (let [rh (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) CxBird)]
      (v/assert kb (list bird Tweety) CxBird)
      (let [eh (v/assert kb (list 'except (sx/sentex-handle rh)) CxBird)]
        (is (empty? (v/sentexes-matching kb (list flies Tweety) CxBird)))
        (v/retract! kb eh)
        (testing "the rule is visible again and its conclusion is re-derived"
          (is (seq (v/sentexes-matching kb (list flies Tweety) CxBird))))))))

(tu/deftest-kb retracting-the-except-re-joins-a-rule-derived-from-its-target
  (tu/with-terms [marked relOf outOf Tom CxHid]
    (let [U 'CxUniverse M {:strength :monotonic}]
      (v/assert kb (list 'genlCx CxHid U) U)
      (v/assert kb (list 'implies (list marked '?p)
                         (list 'set/forwardRule (list 'implies (list '?p '?x '?y) (list outOf '?x '?y))))
                U M)
      (let [mh (v/assert kb (list marked relOf) U M)]
        (doseq [late-fact? [false true]]
          (let [fact #(v/assert kb (list relOf Tom 'Ann) CxHid)
                fh   (when-not late-fact? (fact))
                eh   (v/assert kb (list 'except (sx/sentex-handle mh)) CxHid M)
                fh   (or fh (fact))]
            (is (not (v/ask? kb (list outOf Tom 'Ann) CxHid)))
            (v/retract! kb eh)
            (is (v/ask? kb (list outOf Tom 'Ann) CxHid) (str "fact before the except: " (not late-fact?)))
            (v/retract! kb fh)))))))

;; ---- 4. backward chaining ------------------------------------------------
;; `provers/candidate-rules` filters direction, belief, and context inheritance; a rule
;; hidden from the asking context by a believed except must not be a candidate either.
;; A `set/backwardRule` isolates this arm: it never forward-fires, so the only path to
;; an answer is the one the filter guards.

(tu/deftest-kb a-hidden-backward-rule-is-not-a-candidate
  (tu/with-terms [rained wet Lawn CxYard]
    (let [rh (v/assert kb (list 'set/backwardRule
                                (list 'implies (list rained '?d) (list wet '?d)))
                       CxYard)]
      (v/assert kb (list rained Lawn) CxYard)
      (testing "the goal answers through the rule while it is visible"
        (is (seq (v/query kb (list wet Lawn) CxYard {:max-depth 2}))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle rh)) CxYard)]
        (testing "hidden from the asking context, the rule is not a candidate"
          (is (empty? (v/query kb (list wet Lawn) CxYard {:max-depth 2}))))
        (v/retract! kb eh)
        (testing "and it answers again once the except is retracted"
          (is (seq (v/query kb (list wet Lawn) CxYard {:max-depth 2}))))))))

;; ---- 5. dispute resolution -----------------------------------------------
;; The shape the bug was found in: a genuine dilemma (two default rules concluding
;; opposite literals — the engine represents it rather than deciding it), then a
;; visibility except lands on one side's *rule*.  Defeat must land on support, and
;; once it does, every read surface has to agree: the defeated conclusion is gone,
;; the survivor stands, and the contradiction is resolved — not just the argue tree,
;; but belief, the stored matches, and the conflict list.

(tu/deftest-kb excepting-one-side-of-a-dispute-resolves-it-on-every-read-surface
  (tu/with-terms [quaker republican pacifist Nixon CxDispute]
    (let [_r1 (v/assert kb (tu/default-rule [(list quaker '?x)] (list pacifist '?x))
                        CxDispute)
          r2  (v/assert kb (tu/default-rule [(list republican '?x)]
                                            (list 'not (list pacifist '?x)))
                        CxDispute)]
      (v/assert kb (list quaker Nixon) CxDispute)
      (v/assert kb (list republican Nixon) CxDispute)
      (testing "the dilemma is real before the except: both sides stored, reported"
        (is (seq (v/sentexes-matching kb (list pacifist Nixon) CxDispute)))
        (is (seq (v/sentexes-matching kb (list 'not (list pacifist Nixon)) CxDispute)))
        (is (seq (v/contradictions kb))))
      (v/assert kb (list 'except (sx/sentex-handle r2)) CxDispute)
      (testing "the defeated side's conclusion is swept"
        (is (empty? (v/sentexes-matching kb (list 'not (list pacifist Nixon)) CxDispute))))
      (testing "the surviving side stands"
        (is (seq (v/sentexes-matching kb (list pacifist Nixon) CxDispute))))
      (testing "and the dilemma is resolved, not merely re-rendered"
        (is (empty? (v/contradictions kb)))))))
