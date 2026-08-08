;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.introspection-test
  "The read-only public API: what the KB reports about itself.

  `violations`, `settle-stats` / `reset-settle-stats!`, `types-of`, `justification` and
  `dependent-justifications` are all part of `vaelii.core`'s published surface and none
  of them had a single test reference.  Several carry load-bearing contracts —
  `violations` is the *only* way to see a conclusion forward chaining silently
  dropped, and `settle-stats` is the instrument behind the documented claim that one
  exception pass suffices — so a wrong answer from any of them is invisible rather
  than noisy."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

;; ---- violations: what chaining dropped ----------------------------------

(tu/deftest-kb a-derived-conclusion-that-breaks-an-argument-constraint-is-dropped
  ;; The argument constraints hold of derived content too, but the derivation path
  ;; cannot throw — a fixpoint that aborted mid-run would make belief depend on firing
  ;; order.  An `argIsa` conviction rests on the *absence* of a path from the
  ;; argument's types to the constraint type, so there is no second believed sentex to
  ;; weigh it against and nothing for `settle` to arbitrate: the conclusion is dropped
  ;; and lands here.  (Disjointness, functionality and asymmetry each *do* name an
  ;; opposing sentex, and are arbitrated instead — see `soundness_test`.)
  (tu/with-terms [person rock parentOf looksLike Boulder Muffet]
    (v/assert kb (list 'genl person 'thing) 'UniverseContext)
    (v/assert kb (list 'genl rock 'thing) 'UniverseContext)
    (v/assert kb (list 'argIsa parentOf 1 person) 'UniverseContext)
    (v/assert kb (list rock Boulder) 'UniverseContext)
    (v/assert kb (fwd [(list looksLike '?x)] (list parentOf '?x Muffet)) 'UniverseContext)
    (v/assert kb (list looksLike Boulder) 'UniverseContext)
    (testing "the inadmissible conclusion is not believed"
      (is (empty? (v/sentexes-matching kb (list parentOf Boulder Muffet) 'UniverseContext))))
    (let [vs (filter #(= :arg-type (:violation %)) (v/violations kb))]
      (testing "and it is reported, rather than dropped silently"
        (is (= 1 (count vs)) "exactly one conclusion was dropped")
        (let [{:keys [violation sentence context rule detail]} (first vs)]
          (is (= :arg-type violation))
          (is (= (list parentOf Boulder Muffet) sentence))
          (is (= 'UniverseContext context))
          (is (integer? rule) "the firing rule's handle, so the drop is attributable")
          (is (map? detail))
          (is (string? (:message detail))))))))

(tu/deftest-kb the-violations-ledger-accumulates-across-chaining-runs
  ;; The ledger **accumulates**, each entry stamped with its run id (`chain-stats`
  ;; counts runs), and `clear-violations!` is the one way to empty it.  Clearing at the
  ;; start of each chaining run instead would make a bulk load's drops unobservable by
  ;; its end — assert #38 erasing what #37 dropped.
  (tu/with-terms [person rock parentOf looksLike Boulder Muffet Other]
    (v/assert kb (list 'genl person 'thing) 'UniverseContext)
    (v/assert kb (list 'genl rock 'thing) 'UniverseContext)
    (v/assert kb (list 'argIsa parentOf 1 person) 'UniverseContext)
    (v/assert kb (list rock Boulder) 'UniverseContext)
    (v/assert kb (fwd [(list looksLike '?x)] (list parentOf '?x Muffet)) 'UniverseContext)
    (v/assert kb (list looksLike Boulder) 'UniverseContext)
    (is (= 1 (count (v/violations kb))))
    (testing "an unrelated later assert re-runs chaining and the drop is still reported"
      (v/assert kb (list rock Other) 'UniverseContext)
      (is (= 1 (count (v/violations kb))))
      (is (integer? (:run (first (v/violations kb))))
          "stamped with the run that dropped it, so \"current\" is decidable"))
    (testing "clear-violations! empties it"
      (v/clear-violations! kb)
      (is (empty? (v/violations kb))))))

(tu/deftest-kb every-definitional-check-reports-through-the-same-ledger
  ;; `place-conclusion` runs four checks on the derivation path — the three
  ;; definitional constraints plus structural well-formedness — and drops rather than
  ;; throws, because a fixpoint cannot abort halfway through one.  Only `:disjoint`
  ;; was covered; a check that stopped reporting (or reported under the wrong key)
  ;; would be invisible, since the conclusion is absent either way.
  (testing "an argIsa violation"
    (tu/with-terms [parentOf person rock looksLike Boulder Muffet]
      (v/assert kb (list 'genl rock 'thing) 'UniverseContext)
      (v/assert kb (list 'argIsa parentOf 1 person) 'UniverseContext)
      (v/assert kb (list rock Boulder) 'UniverseContext)
      (v/assert kb (fwd [(list looksLike '?x)] (list parentOf '?x Muffet)) 'UniverseContext)
      (v/assert kb (list looksLike Boulder) 'UniverseContext)
      (is (= [:arg-type] (map :violation (v/violations kb))))
      (is (empty? (v/sentexes-matching kb (list parentOf Boulder Muffet) 'UniverseContext)))))

  ;; No `:functional` case here on purpose.  `functional` is mid-redesign: a clash
  ;; between two *symbol* values now derives `(equals V1 V2)` and merges them rather
  ;; than being rejected (docs/equality.md), so a derived second value is not a
  ;; violation at all — only a clash between non-symbols is.  Pinning either
  ;; reading here would just be a hostage to that work.

  (testing "a derived genl edge that would cycle the taxonomy"
    (v/clear-violations! kb)          ; the ledger accumulates; scope to this stage
    (tu/with-terms [dog animal relates]
      (v/assert kb (list 'genl dog animal) 'UniverseContext)
      (v/assert kb (fwd [(list relates '?x '?y)] (list 'genl '?x '?y)) 'UniverseContext)
      (v/assert kb (list relates animal dog) 'UniverseContext)
      (is (= [:not-well-formed] (map :violation (v/violations kb))))
      (is (not (v/genl? kb animal dog)) "and the closure is intact"))))

(tu/deftest-kb a-clean-run-reports-no-violations
  (tu/with-terms [bird flies Robin]
    (v/assert kb (fwd [(list bird '?x)] (list flies '?x)) 'NaturalWorldContext)
    (v/assert kb (list bird Robin) 'NaturalWorldContext)
    (is (seq (v/sentexes-matching kb (list flies Robin) 'NaturalWorldContext)))
    (is (empty? (v/violations kb)) "nothing was dropped, so nothing is reported")))

;; ---- settle-stats: the exception fixpoint's own meter -------------------

(tu/deftest-kb settle-stats-counts-passes-and-productive-iterations
  (tu/with-terms [bird penguin flies Opus]
    (v/reset-settle-stats! kb)
    (is (= {:iterations 0 :passes 0 :histogram {}} (v/settle-stats kb))
        "reset clears the counters and the histogram")

    (v/assert kb (list 'genl penguin bird) 'UniverseContext)
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/defaultRule (vr/rule-sentence [(list bird '?x)]
                                                                (list flies '?x))))
              'NaturalWorldContext)
    (v/assert kb (list penguin Opus) 'NaturalWorldContext)

    (let [{:keys [iterations passes histogram]} (v/settle-stats kb)]
      (testing "the loop always runs at least a confirming pass"
        (is (pos? passes))
        (is (>= passes iterations) ":passes counts every pass, :iterations only productive ones"))
      (testing "and the exception resolves without the fixpoint needing to iterate"
        (is (<= iterations 1) "docs claim one pass suffices; more would be news"))
      (testing "the histogram accumulates across settles"
        (is (map? histogram))
        (is (pos? (reduce + 0 (vals histogram))))
        (is (every? int? (keys histogram)))))

    (testing "the exception did its job — the penguin does not fly"
      (is (empty? (v/sentexes-matching kb (list flies Opus) 'NaturalWorldContext))))))

;; ---- types-of ------------------------------------------------------------

(tu/deftest-kb types-of-reports-believed-unary-memberships-only
  (tu/with-terms [dog pet parentOf Muffet Rex]
    (v/assert kb (list dog Muffet) 'NaturalWorldContext)
    (v/assert kb (list pet Muffet) 'NaturalWorldContext)
    (v/assert kb (list parentOf Muffet Rex) 'NaturalWorldContext)
    (let [ts (set (v/types-of kb Muffet))]
      (testing "every unary predicate asserted of the individual"
        (is (contains? ts dog))
        (is (contains? ts pet)))
      (testing "but not a binary relation it merely fills argument 1 of"
        (is (not (contains? ts parentOf))
            "(parentOf Muffet Rex) does not make parentOf a *type* of Muffet")))
    (testing "and not a type of some other individual"
      (is (empty? (v/types-of kb Rex))))))

(tu/deftest-kb types-of-does-not-report-a-defeated-membership
  ;; The belief filter.  A membership that lost a contradiction is still *stored*,
  ;; so a version reading the index without consulting the TMS still finds it.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'NaturalWorldContext {:strength :default})
    (is (contains? (set (v/types-of kb Muffet)) dog))
    (v/assert kb (list 'not (list dog Muffet)) 'NaturalWorldContext {:strength :monotonic})
    (testing "the defeated membership drops out of types-of"
      (is (not (contains? (set (v/types-of kb Muffet)) dog))
          "known-true negation beats the default, so dog is no longer believed of Muffet"))))

(tu/deftest-kb types-of-is-scoped-to-what-the-context-sees
  (tu/with-terms [dog Muffet AlphaContext BetaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext BetaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list dog Muffet) AlphaContext)
    (testing "the default arity sees any context"
      (is (contains? (set (v/types-of kb Muffet)) dog)))
    (testing "the asserting context sees its own membership"
      (is (contains? (set (v/types-of kb Muffet AlphaContext)) dog)))
    (testing "a sibling context does not"
      (is (not (contains? (set (v/types-of kb Muffet BetaContext)) dog))
          "Beta does not see Alpha, so Alpha's membership is invisible from it"))))

;; ---- justification / dependent-justifications -----------------------------------

(tu/deftest-kb dependent-justifications-walks-the-opposite-edge-from-supporting-justifications
  ;; The two are three-line twins over `jtms/dependents` and `jtms/supports`.  With
  ;; only one of them tested, a copy-paste that returned supports from both would be
  ;; undetectable — and this is the API a caller uses for impact analysis before a
  ;; retract.
  (tu/with-terms [bird flies Robin]
    (v/assert kb (fwd [(list bird '?x)] (list flies '?x)) 'NaturalWorldContext)
    (let [fact  (v/assert kb (list bird Robin) 'NaturalWorldContext)
          concl (:id (first (v/sentexes-matching kb (list flies Robin) 'NaturalWorldContext)))]
      (is (integer? concl) "the rule fired")
      (testing "the conclusion is supported by a justification, and depends on nothing"
        (is (seq (v/supporting-justifications kb concl)))
        (is (empty? (v/dependent-justifications kb concl))))
      (testing "the antecedent fact is the mirror image — it supports nothing, and is used"
        (is (empty? (v/supporting-justifications kb fact)) "an asserted premise has no support")
        (is (seq (v/dependent-justifications kb fact))))
      (testing "and the two name the same justification from opposite ends"
        (is (= (set (map :id (v/supporting-justifications kb concl)))
               (set (map :id (v/dependent-justifications kb fact)))))))))

(tu/deftest-kb justification-looks-a-justification-up-by-id
  (tu/with-terms [bird flies Robin]
    (v/assert kb (fwd [(list bird '?x)] (list flies '?x)) 'NaturalWorldContext)
    (v/assert kb (list bird Robin) 'NaturalWorldContext)
    (let [concl (:id (first (v/sentexes-matching kb (list flies Robin) 'NaturalWorldContext)))
          d     (first (v/supporting-justifications kb concl))]
      (is (= d (v/justification kb (:id d))) "round-trips by id")
      (is (= concl (:consequence d)))
      (is (nil? (v/justification kb -1)) "an unknown id is nil, not a throw"))))

;; ---- retroactive universal lift -----------------------------------------

(tu/deftest-kb declaring-a-universal-predicate-lifts-facts-already-asserted
  ;; `(decontextualizedPredicate P)` deduces every `(P ...)` into UniverseContext so it is
  ;; visible everywhere.  The forward path — declare, then assert — is what the
  ;; starter does and the only one covered.  The retroactive sweep runs when the
  ;; declaration arrives *after* the facts, and had no test at all: a broken sweep
  ;; looks like it works for everything asserted later and silently fails for
  ;; everything already there.
  (tu/with-terms [marriedTo Ann Bob Cid Dee AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list marriedTo Ann Bob) AlphaContext)
    (testing "before the declaration the fact is confined to its own context"
      (is (empty? (v/sentexes-matching kb (list marriedTo Ann Bob) 'UniverseContext))))

    (v/assert kb (list 'decontextualizedPredicate marriedTo) 'UniverseContext)
    (testing "declaring it lifts the fact that was already there"
      (is (seq (v/sentexes-matching kb (list marriedTo Ann Bob) 'UniverseContext))))

    (testing "and facts asserted afterwards are lifted too"
      (v/assert kb (list marriedTo Cid Dee) AlphaContext)
      (is (seq (v/sentexes-matching kb (list marriedTo Cid Dee) 'UniverseContext))))))

;; ---- rule idempotency covers defeasibility, not just direction ----------

(tu/deftest-kb re-asserting-a-rule-keeps-its-first-defeasibility
  ;; First-writer-wins is documented for direction *and* defeasibility.  Only
  ;; direction was tested.  If find-or-create ever mutated `:defeasible`, conclusions
  ;; already placed at :monotonic would keep a strength the rule no longer confers.
  (tu/with-terms [bird flies Robin]
    (let [bare (vr/rule-sentence [(list bird '?x)] (list flies '?x))
          h1   (v/assert kb bare 'NaturalWorldContext)
          h2   (v/assert kb (list 'set/defaultRule bare) 'NaturalWorldContext)]
      (is (= h1 h2) "an α-equivalent rule resolves to the existing sentex")
      (is (not (:defeasible (v/sentex kb h1)))
          "it keeps the non-defeasible reading it was first given")
      (testing "and its conclusions still carry the bare rule's strength"
        (v/assert kb (list bird Robin) 'NaturalWorldContext {:strength :monotonic})
        (let [concl (:id (first (v/sentexes-matching kb (list flies Robin) 'NaturalWorldContext)))]
          (is (= :monotonic (v/defeat-class kb concl))
              "a bare rule over a known-true fact concludes known-true"))))))
