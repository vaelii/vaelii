;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.soundness-test
  "Five soundness invariants, pinned.

  Each came from a confirmed bug, and the namespace is regression cover: the comment
  above each test names the defect it guards against and the invariant it holds the
  engine to.

  House rules apply as everywhere else: gensym'd temporaries via `tu/with-terms`,
  engine vocabulary literal, and the neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

;; ---- 1. a specific exception wins by blocking, not by out-ranking -------
;; A default/default collision is not arbitrated by *specificity* — scoring each rule
;; by the genl up-closure size of its antecedent predicates so that `penguin ⇒ ¬flies`
;; out-ranks `bird ⇒ flies` (docs/nmtms.md, "There is no second axis").  `exceptWhen`
;; makes the relation structural instead, so the general rule states its own exception
;; and never fires.
;;
;; That makes this a *stronger* claim than arbitration could support.  Arbitration
;; leaves both conclusions derived and then withdraws one; blocking means the general
;; conclusion is never created at all.  So the assertion is not merely "the specific
;; side is believed and the general side is not" — it is that nothing was ever
;; contradictory: `contradictions` is empty, and the general conclusion has no sentex
;; in any context.
;;
;; Both polarities are here on purpose, and neither half may be deleted.  Blocking
;; must not care which side carries the `not` — do not arbitrate by reading the
;; printed sentence, which is exactly the mechanism that would care.

(tu/deftest-kb a-specific-exception-blocks-the-general-default-rather-than-defeating-it
  (tu/with-terms [penguin bird flies swims Opus]
    (v/assert kb (list 'genl penguin bird) 'CxUniverse)
    (v/assert kb (list 'genl bird 'thing)  'CxUniverse)
    ;; general: birds fly, *except* penguins.  specific: penguins do not.
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (default-rule [(list bird '?x)] (list flies '?x)))
              'CxUniverse)
    (v/assert kb (default-rule [(list penguin '?x)] (list 'not (list flies '?x)))  'CxUniverse)
    ;; the same shape with the polarities swapped: birds do not swim, except
    ;; penguins; penguins do.  Blocking must behave identically.
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (default-rule [(list bird '?x)] (list 'not (list swims '?x))))
              'CxUniverse)
    (v/assert kb (default-rule [(list penguin '?x)] (list swims '?x))              'CxUniverse)
    (v/assert kb (list penguin Opus) 'CxUniverse)
    (testing "only the excepted rule's conclusion survives"
      (is (seq    (v/sentexes-matching kb (list 'not (list flies Opus)) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list flies Opus) 'CxUniverse))))
    (testing "and identically when the specific rule is the positive one"
      (is (seq    (v/sentexes-matching kb (list swims Opus) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list 'not (list swims Opus)) 'CxUniverse))))
    (testing "the blocked conclusion was never created, so there is nothing to arbitrate"
      ;; `sentexes-with-functor` is raw — it sees defeated and unsupported sentexes
      ;; too, and a negative fact roots under its positive body's functor.  So each
      ;; of these is exactly one sentex, and it is the specific rule's conclusion.
      (is (= [(list 'not (list flies Opus))]
             (map :sentence (v/sentexes-with-functor kb flies))))
      (is (= [(list swims Opus)]
             (map :sentence (v/sentexes-with-functor kb swims))))
      (is (empty? (v/contradictions kb)))
      (is (empty? (v/conflicts kb))))))

;; ---- 2. the definitional constraints reach the derivation path ----------
;; `checks/disjoint-problems` / `checks/functional-problems` guard `assert-one`; a
;; forward rule firing goes through `place-conclusion`, which runs them too.  What it
;; does with the
;; answer is not a *drop*: a disjointness or functionality clash names a second
;; believed sentex, so it is a **nogood**, and a firing has no caller to refuse.
;; The conclusion is placed and `settle` arbitrates the pair like any other
;; contradiction — which is what leaves the loser a `why-not` instead of no record
;; at all (docs/nmtms.md, 04-constraint-nogoods).
;;
;; So the invariant is not "the two cannot both be believed" — at equal defeat class
;; that is a represented dilemma, exactly as it is for `S` against `(not S)`.  It is
;; that the clash is *represented*: reported, attributable, and resolved the moment
;; one side outranks the other.

(tu/deftest-kb a-derived-conclusion-that-breaks-disjointness-is-arbitrated
  (tu/with-terms [dog fish Rex]
    (v/assert kb (list 'disjoint dog fish) 'CxUniverse)
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list fish '?x) 'CxUniverse {:direction :forward})
    (testing "the direct assertion of the derived sentence is still refused"
      ;; the assert path keeps its guardrail: a writer is told no
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list fish Rex) 'CxUniverse))))
    (testing "the derived one is placed, and the clash is a represented dilemma"
      (is (seq (v/sentexes-matching kb (list dog Rex)  'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list fish Rex) 'CxUniverse)))
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)))
        (is (= #{(v/handle-of kb (list dog Rex)  'CxUniverse)
                 (v/handle-of kb (list fish Rex) 'CxUniverse)}
               (:nogood (first cs)))
            "both handles, so an application can rank the two")
        (is (= 2 (count (:sides (first cs)))))))
    (testing "and it is no longer a silent drop in the violations ledger"
      (is (empty? (filter #(= :disjoint (:violation %)) (v/violations kb)))))))

(tu/deftest-kb a-derived-conclusion-against-known-true-content-is-defeated
  ;; the other half of the same rule: the pair is arbitrated on defeat class, so a
  ;; :default conclusion against a :monotonic membership loses rather than tying
  (tu/with-terms [dog fish Rex]
    (v/assert kb (list 'disjoint dog fish) 'CxUniverse)
    (v/assert kb (list dog Rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list dog '?x)] (list fish '?x))))
              'CxUniverse)
    (testing "the known-true membership stands and the derived one is defeated"
      (is (seq (v/sentexes-matching kb (list dog Rex) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list fish Rex) 'CxUniverse))))
    (testing "the loser is stored and disbelieved, so it has a reason"
      (let [h (v/handle-of kb (list fish Rex) 'CxUniverse)]
        (is (integer? h) "arbitrated, not dropped — there is a record to ask about")
        (is (not (v/in? kb h)))
        (is (= :defeated (:reason (v/why-not kb h))))))
    (testing "a decided clash is not also a dilemma"
      (is (empty? (v/contradictions kb))))))

(tu/deftest-kb a-derived-conclusion-that-breaks-functionality-is-arbitrated
  (tu/with-terms [birthYearOf bornIn Tom]
    (v/assert kb (list 'functional birthYearOf) 'CxUniverse)
    (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
    (v/assert kb (list bornIn Tom 1990) 'CxUniverse)
    (v/assert-rule kb [(list bornIn '?x '?y)] (list birthYearOf '?x '?y) 'CxUniverse {:direction :forward})
    (testing "the direct assertion of the derived sentence is still refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse))))
    (testing "the derived second value is placed and the pair reported"
      ;; two *numbers*: no equality could reconcile them, so this is the clash
      ;; `mergeable-values?` keeps hard rather than merging away
      (is (seq (v/sentexes-matching kb (list birthYearOf Tom 1980) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list birthYearOf Tom 1990) 'CxUniverse)))
      (is (= 1 (count (v/contradictions kb)))))))

;; ---- 3. a derivation confers a class its antecedents never had ----------
;; BUG: `fire-rule` / `fire-rules-for` handed `derive-conclusion` a hard-coded
;; strong class, so a bare rule over a merely :default premise yielded a
;; conclusion outranking its own grounds.  A conclusion can be no stronger than
;; the weakest thing it rests on, and `jtms/conferred-class` now caps it.

(tu/deftest-kb a-derived-conclusion-is-capped-by-its-weakest-antecedent
  (tu/with-terms [smoker unhealthy Bob]
    (v/assert-rule kb [(list smoker '?x)] (list unhealthy '?x) 'CxUniverse {:direction :forward})  ; bare rule: confers :monotonic
    (v/assert kb (list smoker Bob) 'CxUniverse)                              ; :default premise
    (let [derived (v/handle-of kb (list unhealthy Bob) 'CxUniverse)]
      (is (v/in? kb derived) "the rule fired at all")
      (testing "a :default premise cannot yield a conclusion that outranks a default"
        (is (= :default (v/defeat-class kb derived))))
      (testing "so a directly-asserted default negation is a genuine tie, not a loss"
        ;; Neither side out-ranks the other and neither rule names the other's case,
        ;; so this is a **dilemma**: both stay believed and the pair is represented.
        ;; Were the conclusion still conferred a class above `:default`, the negation
        ;; would simply lose and there would be no pair to report.
        (v/assert kb (list 'not (list unhealthy Bob)) 'CxUniverse)           ; :default premise
        (is (seq (v/sentexes-matching kb (list unhealthy Bob) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list 'not (list unhealthy Bob)) 'CxUniverse)))
        (is (= 1 (count (v/contradictions kb))))
        (is (empty? (v/conflicts kb)))))))

;; ---- 4. a non-ground sentence is stored as if it were a fact -----------
;; BUG: `assert` range-restricts rules but never checks that a *fact* is ground,
;; so `(mortal ?x)` is stored, indexed, and marked a believed :default premise —
;; an open sentence entered into the KB as though it stated something.
;; `assert` now refuses it.

(tu/deftest-kb a-fact-containing-a-variable-is-rejected
  (tu/with-terms [mortal human]
    (testing "a non-ground sentence is not a fact and must be refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list mortal '?x) 'CxUniverse))))
    (testing "positive control: a rule, where variables belong, still asserts"
      (is (some? (v/assert-rule kb [(list human '?x)] (list mortal '?x) 'CxUniverse {:direction :forward}))))))

;; ---- 5. contradiction detection misses incomparable contexts -----------
;; BUG: `negation-nogoods` pairs S with (not S) only when one of their contexts
;; `sees?` the other.  Two incomparable contexts with a common *descendant* both
;; reach the pair, so the clash is real from that descendant — but neither
;; direction of `sees?` holds between them, so nothing is detected.
;; `negation-nogoods` now tests for a common descendant instead.

(tu/deftest-kb a-contradiction-visible-from-a-common-descendant-is-detected
  (tu/with-terms [flies Zed CxLeft CxRight CxBoth]
    (v/assert kb (list 'genlCx CxBoth CxLeft)  'CxUniverse)
    (v/assert kb (list 'genlCx CxBoth CxRight) 'CxUniverse)
    (v/assert kb (list flies Zed) CxLeft)
    (v/assert kb (list 'not (list flies Zed)) CxRight)
    (testing "CxBoth sees both, so the clash is detected across the incomparable pair"
      ;; Both premises are `:default`, so the clash is a **dilemma** rather than a
      ;; conflict — but it must be *found*, which is what `sees?` alone could not do.
      ;; Detection is the invariant here; what the engine then does with the pair is
      ;; test 3's subject.
      (is (= 1 (count (v/contradictions kb)))
          "S and (not S) share a descendant context and the pair was not detected")
      (is (empty? (v/conflicts kb))))
    (testing "and a known-true side wins outright at the common descendant, and only there"
      ;; CxBoth is the vantage, so the defeat reaches CxBoth and nothing above it: CxLeft
      ;; never sees the denial and keeps its own claim (docs/nmtms.md, "A defeat is scoped
      ;; to its vantage")
      (v/assert kb (list 'not (list flies Zed)) CxRight {:strength :monotonic})
      (is (not (v/ask? kb (list flies Zed) CxBoth)))
      (is (v/ask? kb (list 'not (list flies Zed)) CxBoth))
      (is (v/ask? kb (list flies Zed) CxLeft))
      (is (empty? (v/contradictions kb))))))
