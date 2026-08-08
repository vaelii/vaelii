;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-test
  "`exceptWhen`: a rule that states its own exception.  Every test here holds against
  the shipped feature — the evaluator is `provers/exception-holds?`, the fixpoint that
  re-runs it is `vaelii.impl.settle`, and the stratification the loop relies on is
  checked at assert time by `checks/check-stratified`.

  Each test pins one decision from [docs/exceptions.md](../../docs/exceptions.md)
  and carries a comment naming it.  The shape under test is

    (exceptWhen <query> (set/defaultRule (implies <antecedents> <consequent>)))

  and the four claims that shape makes are: the exception **blocks** rather than
  deriving a competing negation; it is any closed **level-6** query (no rule
  backchaining); **one answer suffices**; and **nothing about it is stored**.

  House rules apply as everywhere else: gensym'd temporaries via `tu/with-terms`,
  engine vocabulary (`genl`, `set/defaultRule`, `exceptWhen`, `transitive`,
  contexts) literal, and the neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (vr/rule-sentence antes conseq)))

(defn- except-rule
  "The form docs/exceptions.md writes: an exception query wrapping a defeasible
  rule.  `exceptWhen` is split off at the assert layer and stored as a separate
  belief-following `(exceptWhen <query> (sentexHandle H))` meta-sentex naming the
  rule H it qualifies, rather than folded into the rule record."
  [exception antes conseq]
  (list 'exceptWhen exception (default-rule antes conseq)))

;; ---- 1. blocking ---------------------------------------------------------
;; DECISION (Semantics): "`exceptWhen` **blocks**.  When the exception holds for a
;; binding, the rule does not conclude for that binding — there is no conclusion
;; to defeat and nothing to arbitrate."  The unexcepted binding is here as a
;; control, so a run in which the rule never fires at all cannot pass vacuously.

(tu/deftest-kb an-exception-that-holds-blocks-the-conclusion-for-that-binding
  (tu/with-terms [bird penguin flies Tweety Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Tweety) BirdContext)
    (v/assert kb (list bird Opus)   BirdContext)
    (v/assert kb (list penguin Opus) BirdContext)
    (testing "the binding whose exception does not hold concludes normally"
      (is (seq (v/sentexes-matching kb (list flies Tweety) BirdContext))))
    (testing "the binding whose exception holds concludes nothing"
      (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))
    (testing "blocking is not rebutting — no competing negation was derived"
      (is (empty? (v/sentexes-matching kb (list 'not (list flies Opus)) BirdContext))))
    (testing "and nothing was arbitrated, because there was never a contradiction"
      (is (empty? (v/conflicts kb))))))

;; ---- 2. firing -----------------------------------------------------------
;; DECISION (Semantics): an exception constrains a rule, it does not disable one.
;; With the exception unsatisfied the rule is an ordinary defeasible rule, and its
;; conclusion is derived and believed at :default.

(tu/deftest-kb an-exception-that-does-not-hold-leaves-the-rule-firing-normally
  (tu/with-terms [bird penguin flies Tweety BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Tweety) BirdContext)
    (let [h (v/handle-of kb (list flies Tweety) BirdContext)]
      (testing "the conclusion is stored, believed, and derived (not a premise)"
        (is (some? h))
        (is (true? (v/in? kb h)))
        (is (false? (v/premise? kb h)))
        (is (seq (v/supporting-justifications kb h))))
      (testing "a defeasible rule confers :default"
        (is (= :default (v/defeat-class kb h)))))))

;; ---- 3. incremental removal is garbage collection, not defeat ------------
;; DECISION (Garbage collection, not defeat): "a blocked justification is simply
;; invalid, the conclusion is unsupported, and the existing dependency-directed
;; sweep **deletes** it."  Belief alone would not pin this — a *defeated* datum
;; also fails `query` while staying stored — so storage is asserted directly.

(tu/deftest-kb asserting-the-exception-later-deletes-the-conclusion-from-the-store
  (tu/with-terms [bird penguin flies Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus) BirdContext)
    (let [h (v/handle-of kb (list flies Opus) BirdContext)]
      (testing "the conclusion exists before the exception arrives"
        (is (some? h))
        (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext))))
      (v/assert kb (list penguin Opus) BirdContext)
      (testing "belief is gone"
        (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))
      (testing "and so is the storage — swept, not merely disbelieved"
        (is (nil? (v/sentex kb h))
            "the sentex record survived; exceptWhen sweeps, it does not defeat")
        (is (nil? (v/handle-of kb (list flies Opus) BirdContext))
            "handle-of still finds it, so it is stored-but-out rather than deleted"))
      (testing "its justification went with it"
        (is (empty? (v/supporting-justifications kb h)))))))

;; ---- 4. revival is a re-derivation ---------------------------------------
;; DECISION (Garbage collection, not defeat): "Reviving costs a re-derivation
;; rather than flipping a bit: retract the exception and the conclusion is chained
;; again, not restored."  So the conclusion must come back — but the old handle
;; need not, and this test deliberately does not require it.

(tu/deftest-kb retracting-the-exception-re-derives-the-conclusion
  (tu/with-terms [bird penguin flies Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus) BirdContext)
    (let [ph (v/assert kb (list penguin Opus) BirdContext)]
      (testing "while the exception holds there is no conclusion"
        (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))
      (v/retract! kb ph)
      (testing "retracting it chains the conclusion again"
        (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext)))
        (let [h (v/handle-of kb (list flies Opus) BirdContext)]
          (is (some? h))
          (is (true? (v/in? kb h)))
          (is (seq (v/supporting-justifications kb h))
              "revived by re-derivation, so it carries a fresh justification"))))))

;; ---- 5. the sweep cascades ----------------------------------------------
;; DECISION (Garbage collection, not defeat): the sweep "**deletes** it along with
;; everything solely resting on it."  A second, unexcepted rule builds on the
;; excepted conclusion; blocking the first must take the second's output too.

(tu/deftest-kb sweeping-an-excepted-conclusion-takes-its-consequences-with-it
  (tu/with-terms [bird penguin flies airborne Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (default-rule [(list flies '?b)] (list airborne '?b)) BirdContext)
    (v/assert kb (list bird Opus) BirdContext)
    (let [fh (v/handle-of kb (list flies Opus)    BirdContext)
          ah (v/handle-of kb (list airborne Opus) BirdContext)]
      (testing "both links of the chain are derived first"
        (is (some? fh))
        (is (some? ah)))
      (v/assert kb (list penguin Opus) BirdContext)
      (testing "blocking the first rule removes the conclusion that rested on it"
        (is (empty? (v/sentexes-matching kb (list flies Opus)    BirdContext)))
        (is (empty? (v/sentexes-matching kb (list airborne Opus) BirdContext))))
      (testing "the cascade is a sweep, so neither is stored any more"
        (is (nil? (v/sentex kb fh)))
        (is (nil? (v/sentex kb ah))
            "the consequence outlived its sole support")))))

;; ---- 6. a conjunctive exception -----------------------------------------
;; DECISION (The exception is a query, not a literal): "A conjunction is a vector,
;; spelled the way core/prove spells one."  Closure makes the conjuncts independent
;; ground checks, so all must hold and one alone must leave the rule firing.

(tu/deftest-kb a-conjunctive-exception-blocks-only-when-every-conjunct-holds
  (tu/with-terms [bird penguin young flies Opus BirdContext]
    (v/assert kb (except-rule [(list penguin '?b) (list young '?b)]
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus) BirdContext)
    (testing "with neither conjunct, the rule fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext))))
    (v/assert kb (list penguin Opus) BirdContext)
    (testing "one conjunct is not the exception — the rule still fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext))))
    (v/assert kb (list young Opus) BirdContext)
    (testing "both conjuncts hold, so the exception holds and the conclusion goes"
      (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext)))
      (is (nil? (v/handle-of kb (list flies Opus) BirdContext))))))

;; ---- 7. the exception is a level-6 query, not a literal lookup ----------
;; DECISION (The exception is a query, not a literal): "an exception may reach
;; through genl specificity, the genlContext visibility closure, transitive /
;; symmetric / inverse metadata, disjointness, and evaluable arithmetic."  These
;; two are what distinguish the feature from matching a stored fact: in neither
;; case is the exception sentence itself ever asserted.

(tu/deftest-kb an-exception-holding-only-through-genl-specificity-blocks
  (tu/with-terms [bird penguin flightless flies Opus BirdContext]
    (v/assert kb (list 'genl penguin flightless) BirdContext)
    (v/assert kb (except-rule (list flightless '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus)    BirdContext)
    (v/assert kb (list penguin Opus) BirdContext)
    (testing "no (flightless Opus) fact exists — only the subtype membership"
      (is (empty? (v/lookup kb 2 (list flightless Opus) BirdContext))))
    (testing "but level 6 answers it through the spec walk, so the rule is blocked"
      (is (seq (v/lookup kb 6 (list flightless Opus) BirdContext)))
      (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))))

(tu/deftest-kb an-exception-holding-only-through-a-transitive-closure-blocks
  (tu/with-terms [widget shiny insideOf Gem Box Vault VaultContext]
    (v/assert kb (list 'transitive insideOf) VaultContext)
    (v/assert kb (except-rule (list insideOf '?x Vault)
                              [(list widget '?x)] (list shiny '?x))
              VaultContext)
    (v/assert kb (list widget Gem)        VaultContext)
    (v/assert kb (list insideOf Gem Box)  VaultContext)
    (v/assert kb (list insideOf Box Vault) VaultContext)
    (testing "the exception is nowhere stored — it exists only in the closure"
      (is (empty? (v/lookup kb 2 (list insideOf Gem Vault) VaultContext)))
      (is (seq    (v/lookup kb 6 (list insideOf Gem Vault) VaultContext))))
    (testing "so the closure blocks the rule"
      (is (empty? (v/sentexes-matching kb (list shiny Gem) VaultContext))))))

;; ---- 8. a taxonomy edge is a re-check trigger ---------------------------
;; DECISION (Taxonomy changes re-check everything): "An exception like
;; `(flightlessBird ?b)` can flip because someone asserted `(genl penguin
;; flightlessBird)` — no fact with a matching predicate ever arrives."  So the
;; conclusion must be swept on the *edge*, with the predicate-keyed re-check index
;; never firing.

(tu/deftest-kb a-genl-edge-that-makes-the-exception-true-removes-the-conclusion
  (tu/with-terms [bird penguin flightless flies Opus BirdContext]
    (v/assert kb (except-rule (list flightless '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus)    BirdContext)
    (v/assert kb (list penguin Opus) BirdContext)
    (testing "penguin is not yet a flightless bird, so the rule fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext))))
    ;; the only thing that changes is a genl edge — no (flightless ...) fact,
    ;; and nothing with the exception's predicate is ever asserted
    (v/assert kb (list 'genl penguin flightless) BirdContext)
    (testing "the edge alone makes the exception hold, and the conclusion is swept"
      (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext)))
      (is (nil? (v/handle-of kb (list flies Opus) BirdContext))))))

;; ---- 9. no backchaining -------------------------------------------------
;; DECISION (The exception is a query, not a literal): "**No backchaining.**  An
;; exception that is only derivable by running rules (level 7) does not hold" —
;; and "**An unanswerable exception does not hold**, and the rule fires."  The
;; exception here is reachable only through a backward-only rule, so level 6 has
;; no answer and the conclusion must be derived.

(tu/deftest-kb an-exception-derivable-only-by-backchaining-does-not-block
  (tu/with-terms [dog pet loud scary Muffet PetContext]
    ;; backward-only, so forward chaining never materializes (scary Muffet)
    (v/assert-rule kb [(list loud '?x)] (list scary '?x) PetContext {:direction :backward})
    (v/assert kb (except-rule (list scary '?x)
                              [(list dog '?x)] (list pet '?x))
              PetContext)
    (v/assert kb (list dog Muffet)  PetContext)
    (v/assert kb (list loud Muffet) PetContext)
    (testing "the exception is a level-7 answer and nothing less"
      (is (empty? (v/lookup kb 6 (list scary Muffet) PetContext)))
      (is (seq    (v/lookup kb 7 (list scary Muffet) PetContext))))
    (testing "so it does not hold, and the rule fires (the open-world reading)"
      (is (seq (v/sentexes-matching kb (list pet Muffet) PetContext))))))

;; ---- 10. backward inference and why-not ---------------------------------
;; DECISION (Semantics): "under backward chaining the argument is constructed and
;; then reported as excepted, so `why-not` can say *'rule R applies via (bird
;; Opus), but its exception (flightlessBird Opus) holds'* instead of recomputing a
;; contradiction it never recorded."

(tu/deftest-kb backward-inference-does-not-return-an-excepted-conclusion
  (tu/with-terms [bird penguin flies Tweety Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Tweety)  BirdContext)
    (v/assert kb (list bird Opus)    BirdContext)
    (v/assert kb (list penguin Opus) BirdContext)
    (testing "the unexcepted binding is provable both ways"
      (is (true? (v/provable? kb (list flies Tweety) BirdContext)))
      (is (true? (v/ask?      kb (list flies Tweety) BirdContext))))
    (testing "the excepted one is not — blocking is not a forward-chaining artifact"
      (is (false? (v/provable? kb (list flies Opus) BirdContext)))
      (is (false? (v/ask?      kb (list flies Opus) BirdContext))))
    (testing "and an open goal returns only the unexcepted binding"
      (is (= #{Tweety} (set (map #(get % '?who)
                                 (v/ask kb (list flies '?who) BirdContext))))))))

;; SPEC NOTE — this test cannot be written against today's API and is written in
;; the form it must take.  `why-not` takes a **handle**, and an excepted
;; conclusion has none: nothing is stored (decision "the exception is never
;; stored"), so the question can only be asked of a sentence in a context.  The
;; doc requires the *answer* but does not name the arity or the reason keyword;
;; `:excepted` and `:exception` are this suite's choice.  Expect an ArityException
;; until `why-not` grows the sentence arity.

(tu/deftest-kb why-not-reports-an-excepted-conclusion-as-excepted-not-unsupported
  (tu/with-terms [bird penguin flies Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus)    BirdContext)
    (v/assert kb (list penguin Opus) BirdContext)
    (testing "there is no handle to ask about — the conclusion was never stored"
      (is (nil? (v/handle-of kb (list flies Opus) BirdContext))))
    (let [wn (v/why-not kb (list flies Opus) BirdContext)]
      (testing "the reason names the exception, not a missing support"
        (is (false? (:believed? wn)))
        (is (= :excepted (:reason wn))
            "an excepted conclusion is not :unsupported and not :defeated")
        (is (= (list penguin Opus) (:exception wn))
            "the ground exception that held, with the rule's bindings substituted")))))

;; ---- 11. rebutting dilemmas still coexist -------------------------------
;; DECISION (Semantics): "two rules concluding `P` and `¬P` with neither naming the
;; other's case is a genuine dilemma (the Nixon diamond), and the engine represents
;; it rather than deciding it.  Coexisting `P`/`¬P` at `:default` is therefore the
;; signature of a real dilemma, not of a badly-written exception."  This guards the
;; feature against over-reaching into rebutting defeat.

(tu/deftest-kb two-unexcepted-rules-concluding-opposites-remain-a-dilemma
  (tu/with-terms [quaker republican pacifist Nixon PolContext]
    (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))              PolContext)
    (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x)))  PolContext)
    (v/assert kb (list quaker Nixon)     PolContext)
    (v/assert kb (list republican Nixon) PolContext)
    (let [pos (v/handle-of kb (list pacifist Nixon)              PolContext)
          neg (v/handle-of kb (list 'not (list pacifist Nixon))  PolContext)]
      (testing "both conclusions are derived"
        (is (some? pos))
        (is (some? neg)))
      (testing "and both stay believed — neither rule named the other's case"
        (is (true? (v/in? kb pos)))
        (is (true? (v/in? kb neg)))
        (is (seq (v/sentexes-matching kb (list pacifist Nixon)             PolContext)))
        (is (seq (v/sentexes-matching kb (list 'not (list pacifist Nixon)) PolContext))))
      (testing "both at :default — the dilemma is represented, not decided"
        (is (= :default (v/defeat-class kb pos)))
        (is (= :default (v/defeat-class kb neg)))))))

;; ---- 12. the exception is evaluated where the conclusion lives ----------
;; DECISION (The exception is a query, not a literal): "**The exception is
;; evaluated in the conclusion's placement context**, not the rule's.  ...  an
;; exception invisible from where the conclusion would live has no business
;; blocking it."

(tu/deftest-kb an-exception-invisible-from-the-placement-context-does-not-block
  (tu/with-terms [bird penguin flies Opus HomeContext FarContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              HomeContext)
    (v/assert kb (list bird Opus) HomeContext)
    ;; FarContext is unrelated to HomeContext: no genlContext edge either way
    (is (not (v/sees? kb HomeContext FarContext)) "test precondition")
    (v/assert kb (list penguin Opus) FarContext)
    (testing "the conclusion is placed in HomeContext, which cannot see FarContext"
      (is (= HomeContext (:context (v/sentex kb (v/handle-of kb (list flies Opus)
                                                             HomeContext))))))
    (testing "so the far exception does not block"
      (is (seq (v/sentexes-matching kb (list flies Opus) HomeContext))))
    (testing "the same exception asserted where the conclusion lives does block"
      (v/assert kb (list penguin Opus) HomeContext)
      (is (empty? (v/sentexes-matching kb (list flies Opus) HomeContext)))
      (is (nil? (v/handle-of kb (list flies Opus) HomeContext))))))

;; ---- 13. the exception is not materialized per-instance -----------------
;; DECISION (The exception is never materialized): materializing the ground
;; exception "stores the negative space" — a probe `(penguin X)` for every
;; individual the exception does *not* apply to.  The exception is a single stored
;; meta-sentex `(exceptWhen <query> (sentexHandle H))`, re-evaluated on demand; no
;; per-instance probe is ever recorded.

(tu/deftest-kb an-exception-that-does-not-hold-materializes-nothing
  (tu/with-terms [bird penguin flies Tweety Robin Wren BirdContext]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              BirdContext)
    (doseq [b [Tweety Robin Wren]] (v/assert kb (list bird b) BirdContext))
    (testing "every bird flies"
      (is (= 3 (count (v/sentexes-matching kb (list flies '?b) BirdContext)))))
    (testing "not one penguin *fact* was stored for the birds that are not one"
      (is (zero? (v/count-with-functor kb penguin)))
      (is (empty? (v/sentexes-with-functor kb penguin))))
    (testing "the exception is one meta-sentex, whatever the number of birds"
      (is (= 1 (count (filter #(= 'exceptWhen (first (:sentence %)))
                              (v/find-sentexes kb penguin))))))))

;; DECISION (Amend in place): an exceptWhen is a separate belief-following meta-sentex
;; naming the rule by handle, so a rule and its unexcepted twin share **one** handle —
;; asserting the exception amends that rule in place rather than forking a second one,
;; and retracting the exception restores it.

(tu/deftest-kb an-exception-amends-the-rule-in-place-sharing-one-handle
  (tu/with-terms [bird penguin flies Opus BirdContext]
    (let [rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
          plain (v/assert kb (default-rule [(list bird '?b)] (list flies '?b)) BirdContext)
          exc   (v/assert kb (except-rule (list penguin '?b)
                                          [(list bird '?b)] (list flies '?b))
                          BirdContext)]
      (testing "the exceptWhen is a separate meta-sentex, not the rule"
        (is (not= plain exc)))
      (testing "the rule keeps its one handle; the exception names it"
        (is (= plain (v/handle-of kb rule-form BirdContext))))
      (v/assert kb (list bird Opus)    BirdContext)
      (v/assert kb (list penguin Opus) BirdContext)
      (testing "the exception amends the one rule, so the penguin does not fly"
        (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))
      (v/retract! kb exc)
      (testing "retract the exception and the one rule concludes again"
        (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext)))))))

;; DECISION (Stratification): "a rule set with a cycle through negation is
;; **rejected at assert time**, as a well-formedness check over the rule dependency
;; graph alongside the `genl` cycle check."  Here rule A's exception is what rule B
;; concludes and vice versa.

(tu/deftest-kb a-cycle-through-negation-across-two-rules-is-rejected-at-assert-time
  (tu/with-terms [base p q CycContext]
    (v/assert kb (except-rule (list q '?x) [(list base '?x)] (list p '?x)) CycContext)
    (testing "the second rule closes a cycle through negation and must be refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (except-rule (list p '?x) [(list base '?x)] (list q '?x))
                             CycContext))))))
