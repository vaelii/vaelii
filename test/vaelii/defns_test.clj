;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.defns-test
  "Definitional collection relations: `defnNecessary` / `defnSufficient` / `defnIff`
  tie a collection's membership to a condition on the member `?x`, and expand into
  ordinary forward rules at assert.

  What the tests hold to is that the expansion is *into the existing machinery* — the
  conclusion is a materialized, justified sentex, not a prover's ephemeral answer — so
  it retracts, belief-follows, recovers and scopes to a context exactly as any derived
  fact does.  And that the reading is **open-world**: nothing closes the collection's
  complement, so a thing the condition is merely silent about is neither a member nor a
  non-member.  See docs/defns.md."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- believes?
  "Is `sentence` a **believed** sentex in `ctx` — stored and IN?  Read through
  `sentexes-matching` (belief-sensitive) rather than `ask`, because what is new about a
  `defn*` conclusion is that it is a *record*: a defeated one drops out of this."
  [kb sentence ctx]
  (boolean (seq (v/sentexes-matching kb sentence ctx))))

(defn- a-context
  "Hang `ctx` under CxUniverse, so a `defn*` and the facts written there see the
  universal vocabulary — and two such contexts are siblings that cannot see each
  other, which is what the scoping test needs."
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse))

;; ---- necessary: membership entails the condition -------------------------

(tu/deftest-kb necessary-a-member-satisfies-the-condition
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)
    (v/assert kb (list bachelor Tom) 'CxUniverse)
    (is (believes? kb (list unmarried Tom) 'CxUniverse)
        "every bachelor is unmarried, so Tom the bachelor is unmarried")
    (is (v/ask? kb (list unmarried Tom) 'CxUniverse)
        "and the derived membership is queryable")))

(tu/deftest-kb necessary-does-not-run-the-other-way
  ;; a necessary condition is member => condition, never condition => member
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)
    (v/assert kb (list unmarried Tom) 'CxUniverse)
    (is (not (believes? kb (list bachelor Tom) 'CxUniverse))
        "being unmarried does not make Tom a bachelor under a necessary condition")))

;; ---- sufficient: the condition entails membership ------------------------

(tu/deftest-kb sufficient-satisfying-the-condition-makes-a-member
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnSufficient bachelor (list unmarried '?x)) 'CxUniverse)
    (v/assert kb (list unmarried Tom) 'CxUniverse)
    (is (believes? kb (list bachelor Tom) 'CxUniverse)
        "anything unmarried is a bachelor, so unmarried Tom is a bachelor")))

(tu/deftest-kb sufficient-does-not-run-the-other-way
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnSufficient bachelor (list unmarried '?x)) 'CxUniverse)
    (v/assert kb (list bachelor Tom) 'CxUniverse)
    (is (not (believes? kb (list unmarried Tom) 'CxUniverse))
        "a sufficient condition draws no necessary consequence of membership")))

;; ---- iff: both directions ------------------------------------------------

(tu/deftest-kb iff-runs-in-both-directions
  (tu/with-terms [bachelor Tom Sam unmarried]
    (v/assert kb (list 'defnIff bachelor (list unmarried '?x)) 'CxUniverse)
    (v/assert kb (list bachelor Tom) 'CxUniverse)     ; member => condition
    (v/assert kb (list unmarried Sam) 'CxUniverse)    ; condition => member
    (is (believes? kb (list unmarried Tom) 'CxUniverse) "the necessary half")
    (is (believes? kb (list bachelor Sam) 'CxUniverse) "the sufficient half")))

;; ---- retraction removes the entailment -----------------------------------

(tu/deftest-kb retracting-the-definition-withdraws-what-it-concluded
  (tu/with-terms [bachelor Tom unmarried]
    (let [dh (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)]
      (v/assert kb (list bachelor Tom) 'CxUniverse)
      (is (believes? kb (list unmarried Tom) 'CxUniverse))
      ;; the companion rule is derived, justified by the defn* fact alone
      (let [rh (v/handle-of kb (list 'implies (list bachelor '?x) (list unmarried '?x))
                            'CxUniverse)]
        (is (and rh (v/believed? kb rh)) "the companion rule is believed while the defn* is")
        (v/retract! kb dh)
        (is (not (believes? kb (list unmarried Tom) 'CxUniverse))
            "retracting the definition withdraws the conclusion it licensed")
        (is (not (v/believed? kb rh))
            "and the companion rule is no longer believed")))))

(tu/deftest-kb retracting-the-member-withdraws-only-its-own-conclusion
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)
    (let [mh (v/assert kb (list bachelor Tom) 'CxUniverse)]
      (is (believes? kb (list unmarried Tom) 'CxUniverse))
      (v/retract! kb mh)
      (is (not (believes? kb (list unmarried Tom) 'CxUniverse))
          "with no bachelor there is nothing to be unmarried")
      ;; the definition itself still stands, so a later member re-fires it
      (tu/with-terms [Sam]
        (v/assert kb (list bachelor Sam) 'CxUniverse)
        (is (believes? kb (list unmarried Sam) 'CxUniverse)
            "the definition survived the member's retraction")))))

;; ---- order independence --------------------------------------------------

(tu/deftest-kb the-two-arrival-orders-agree
  (testing "definition before the member"
    (tu/with-terms [bachelor Tom unmarried]
      (v/assert kb (list 'defnSufficient bachelor (list unmarried '?x)) 'CxUniverse)
      (v/assert kb (list unmarried Tom) 'CxUniverse)
      (is (believes? kb (list bachelor Tom) 'CxUniverse))))
  (testing "member before the definition"
    (tu/with-terms [bachelor Tom unmarried]
      (v/assert kb (list unmarried Tom) 'CxUniverse)
      (v/assert kb (list 'defnSufficient bachelor (list unmarried '?x)) 'CxUniverse)
      (is (believes? kb (list bachelor Tom) 'CxUniverse)
          "the definition seeds chaining over the facts already stored"))))

;; ---- two definitions that differ only in where `?x` sits ------------------
;; `(kin ?x ?y)` and `(kin ?y ?x)` are two conditions on the member — `?x` is the
;; distinguished variable — and their trie keys coincide (the key α-renames, the lookup
;; reads a variable as a wildcard), so the dedup must read the stored sentence or the
;; second definition resolves to the first.

(tu/deftest-kb two-definitions-transposing-the-member-variable-are-two-definitions
  (tu/with-terms [parent Ann Bea kin]
    (let [as-first  (v/assert kb (list 'defnSufficient parent (list kin '?x '?y)) 'CxUniverse)
          as-second (v/assert kb (list 'defnSufficient parent (list kin '?y '?x)) 'CxUniverse)]
      (is (not= as-first as-second) "each definition has its own handle")
      (is (= as-second (v/assert kb (list 'defnSufficient parent (list kin '?y '?x)) 'CxUniverse))
          "and re-asserting one resolves to its own handle")
      (v/assert kb (list kin Ann Bea) 'CxUniverse)
      (is (believes? kb (list parent Ann) 'CxUniverse) "the first definition makes Ann a member")
      (is (believes? kb (list parent Bea) 'CxUniverse) "the second makes Bea one")
      (v/retract! kb as-second)
      (is (believes? kb (list parent Ann) 'CxUniverse) "retracting the second leaves the first's conclusion")
      (is (not (believes? kb (list parent Bea) 'CxUniverse)) "and withdraws only its own"))))

;; ---- context scoping -----------------------------------------------------

(tu/deftest-kb the-definition-is-scoped-to-its-context
  (tu/with-terms [bachelor Tom Sam unmarried CxHome CxAway]
    (a-context kb CxHome)
    (a-context kb CxAway)                       ; a sibling CxHome cannot see
    (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) CxHome)
    (v/assert kb (list bachelor Tom) CxAway)    ; invisible to the definition
    (v/assert kb (list bachelor Sam) CxHome)    ; visible to it
    (is (believes? kb (list unmarried Sam) CxHome)
        "a member in the definition's own context fires the rule")
    (is (not (believes? kb (list unmarried Tom) CxAway))
        "a member in a context the definition cannot see does not")
    (is (not (believes? kb (list unmarried Tom) CxHome))
        "and CxHome never saw Tom to begin with")))

;; ---- belief following: retract and re-assert -----------------------------

(tu/deftest-kb the-conclusion-follows-the-definitions-belief
  (tu/with-terms [bachelor Tom unmarried]
    (let [dh (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)]
      (v/assert kb (list bachelor Tom) 'CxUniverse)
      (is (believes? kb (list unmarried Tom) 'CxUniverse))
      (v/retract! kb dh)
      (is (not (believes? kb (list unmarried Tom) 'CxUniverse)))
      ;; assert it again — the entailment returns, arrival order unchanged
      (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)
      (is (believes? kb (list unmarried Tom) 'CxUniverse)
          "re-asserting the definition brings the conclusion back"))))

(tu/deftest-kb a-rebuild-from-the-store-agrees
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)
    (v/assert kb (list bachelor Tom) 'CxUniverse)
    (is (believes? kb (list unmarried Tom) 'CxUniverse))
    (v/recover kb)
    (is (believes? kb (list unmarried Tom) 'CxUniverse)
        "recover rebuilds the derived rule and its conclusion from the records")))

;; ---- NOT closed-world ----------------------------------------------------

(tu/deftest-kb an-unevidenced-thing-is-neither-a-member-nor-a-non-member
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnIff bachelor (list unmarried '?x)) 'CxUniverse)
    ;; Tom is mentioned nowhere; the definition says nothing about him
    (is (not (v/ask? kb (list bachelor Tom) 'CxUniverse))
        "silence about the condition does not make Tom a member")
    (is (not (v/ask? kb (list unmarried Tom) 'CxUniverse))
        "nor does it assert the condition of him")
    (is (not (v/ask? kb (list 'not (list bachelor Tom)) 'CxUniverse))
        "and it draws no non-membership from the absence of the condition")
    (is (not (v/ask? kb (list 'not (list unmarried Tom)) 'CxUniverse))
        "condition-absence concludes no negation either")))

(tu/deftest-kb the-sufficient-direction-needs-the-condition-actually-met
  (tu/with-terms [bachelor Tom unmarried]
    (v/assert kb (list 'defnSufficient bachelor (list unmarried '?x)) 'CxUniverse)
    (is (not (believes? kb (list bachelor Tom) 'CxUniverse))
        "with no evidence that Tom is unmarried, he is not concluded a bachelor")))

;; ---- conjunctive conditions ----------------------------------------------

(tu/deftest-kb a-necessary-conjunction-entails-each-conjunct
  (tu/with-terms [bachelor Tom male unmarried]
    (v/assert kb (list 'defnNecessary bachelor
                       (list 'and (list male '?x) (list unmarried '?x)))
              'CxUniverse)
    (v/assert kb (list bachelor Tom) 'CxUniverse)
    (is (believes? kb (list male Tom) 'CxUniverse)     "the first conjunct")
    (is (believes? kb (list unmarried Tom) 'CxUniverse) "the second conjunct")))

(tu/deftest-kb a-sufficient-conjunction-needs-every-conjunct
  (tu/with-terms [bachelor Tom male unmarried]
    (v/assert kb (list 'defnSufficient bachelor
                       (list 'and (list male '?x) (list unmarried '?x)))
              'CxUniverse)
    (v/assert kb (list male Tom) 'CxUniverse)
    (is (not (believes? kb (list bachelor Tom) 'CxUniverse))
        "one conjunct is not enough — the join is open-world")
    (v/assert kb (list unmarried Tom) 'CxUniverse)
    (is (believes? kb (list bachelor Tom) 'CxUniverse)
        "with both conjuncts met, membership is concluded")))

(tu/deftest-kb a-sufficient-condition-no-stored-conjunct-binds-expands-to-no-rule
  ;; The condition is computed, so no join can bind the member; evaluation answers
  ;; membership at query time.
  (tu/with-terms [short_word]
    (let [before (v/sentex-count kb)]
      (v/assert kb (list 'defnSufficient short_word (list 'matchesPattern '?x "[a-z]{1,4}"))
                'CxUniverse)
      (is (= (inc before) (v/sentex-count kb)) "the defn fact alone is stored")
      (is (empty? (v/violations kb)) "and no companion rule was minted and dropped")
      (is (v/ask? kb (list short_word "cat") 'CxUniverse))
      (is (not (v/ask? kb (list short_word "giraffe") 'CxUniverse))))))

;; ---- well-formedness -----------------------------------------------------

(tu/deftest-kb a-condition-that-ignores-the-member-is-refused
  (tu/with-terms [bachelor male]
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'defnNecessary bachelor (list male '?y)) 'CxUniverse))
        "the condition must mention the member ?x")
    (is (empty? (v/sentexes-matching
                 kb (list 'defnNecessary bachelor (list male '?y)) 'CxUniverse))
        "and nothing is stored by the refused assertion")))
