;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-test
  "`exceptWhen`: a rule that states its own exception.  Every test here holds against
  the shipped feature — the evaluator is `provers/exception-holds?`, the fixpoint that
  re-runs it is `vaelii.impl.settle`, and the stratification the loop relies on is
  checked at assert time by `checks/check-stratified`.

  Each test asserts one decision from [docs/exceptions.md](../../docs/exceptions.md)
  and carries a comment naming it.  The shape under test is

    (exceptWhen <query> (set/defaultRule (implies <antecedents> <consequent>)))

  and the four claims that shape makes are: the exception **blocks** rather than
  deriving a competing negation; it is any closed **level-6** query (no rule
  backchaining); **one answer suffices**; and it is stored **once**, as a meta-sentex,
  never per instance.

  House rules apply as everywhere else: gensym'd temporaries via `tu/with-terms`,
  engine vocabulary (`genl`, `set/defaultRule`, `exceptWhen`, `transitive`,
  contexts) literal, and the neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- except-rule
  "The form docs/exceptions.md writes: an exception query wrapping a defeasible
  rule.  `exceptWhen` is split off at the assert layer and stored as a separate
  belief-following `(exceptWhen <query> (sentexHandle H))` meta-sentex naming the
  rule H it qualifies, rather than folded into the rule record."
  [exception antes conseq]
  (list 'exceptWhen exception (tu/default-rule antes conseq)))

;; ---- 1. blocking ---------------------------------------------------------
;; DECISION (Semantics): "`exceptWhen` **blocks**.  When the exception holds for a
;; binding, the firing at that binding supports nothing, and no nogood arbitrates it."
;; The unexcepted binding is here as a control, so a run in which the rule never fires
;; at all cannot pass vacuously.

(tu/deftest-kb an-exception-that-holds-blocks-the-conclusion-for-that-binding
  (tu/with-terms [bird penguin flies Tweety Opus CxBird]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Tweety) CxBird)
    (v/assert kb (list bird Opus)   CxBird)
    (v/assert kb (list penguin Opus) CxBird)
    (testing "the binding whose exception does not hold concludes normally"
      (is (seq (v/sentexes-matching kb (list flies Tweety) CxBird))))
    (testing "the binding whose exception holds concludes nothing"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
    (testing "blocking is not rebutting — no competing negation was derived"
      (is (empty? (v/sentexes-matching kb (list 'not (list flies Opus)) CxBird))))
    (testing "and nothing was arbitrated, because there was never a contradiction"
      (is (empty? (v/conflicts kb))))))

;; ---- 2. firing -----------------------------------------------------------
;; DECISION (Semantics): an exception constrains a rule, it does not disable one.
;; With the exception unsatisfied the rule is an ordinary defeasible rule, and its
;; conclusion is derived and believed at :default.

(tu/deftest-kb an-exception-that-does-not-hold-leaves-the-rule-firing-normally
  (tu/with-terms [bird penguin flies Tweety CxBird]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (let [bh (v/assert kb (list bird Tweety) CxBird)
          rh (v/handle-of kb (tu/default-rule [(list bird '?b)] (list flies '?b)) CxBird)
          h  (v/handle-of kb (list flies Tweety) CxBird)]
      (testing "the conclusion is stored, believed, and derived (not a premise)"
        (is (some? h))
        (is (true? (v/believed? kb h)))
        (is (false? (v/premise? kb h)))
        (is (= [[[bh] rh]] (map (juxt :antecedents :informant) (v/supporting-justifications kb h)))
            "one justification: the bird fact, through the rule"))
      (testing "a defeasible rule confers :default"
        (is (= :default (v/defeat-class kb h)))))))

;; ---- 3. a holding exception stores the conclusion with a guard defeat ----
;; A blocker of either class, `:default` or `:monotonic`, is one a placed defeat hides,
;; so the firing is stored, in either order, with `(defeat (sentexHandle F))`
;; resting on the blocker at the firing's own context, and the read walk decides belief.

(tu/deftest-kb a-blocker-stores-the-conclusion-with-a-defeat-resting-on-it
  (doseq [strength [:monotonic :default]
          blocker-first? [false true]]
    (tu/with-terms [bird penguin flies Opus CxBird]
      (let [block #(v/assert kb (list penguin Opus) CxBird {:strength strength})
            ph    (when blocker-first? (block))
            _     (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
                            CxBird)
            _     (v/assert kb (list bird Opus) CxBird)
            ph    (or ph (block))
            h     (v/handle-of kb (list flies Opus) CxBird)
            d     (when h (v/handle-of kb (list 'defeat (list 'sentexHandle h)) CxBird))]
        (testing (str strength " blocker first: " blocker-first?)
          (is (some? h))
          (is (some? d))
          (is (seq (v/supporting-justifications kb h)) "the firing's justification stays")
          (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird)))
          (is (some #{ph} (mapcat :antecedents (v/supporting-justifications kb d))))
          (v/retract! kb ph)
          (is (= [h] (mapv :id (v/sentexes-matching kb (list flies Opus) CxBird)))))))))

;; ---- 5. the defeat reaches the consequences -----------------------------
;; A second, unexcepted rule builds on the excepted conclusion; the guard defeat of the
;; first hides the second's output too, since every route to it rests on the defeated
;; conclusion.

(tu/deftest-kb a-defeated-conclusion-hides-its-consequences-with-it
  (tu/with-terms [bird penguin flies airborne Opus CxBird]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (tu/default-rule [(list flies '?b)] (list airborne '?b)) CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (let [fh (v/handle-of kb (list flies Opus)    CxBird)
          ah (v/handle-of kb (list airborne Opus) CxBird)]
      (testing "both links of the chain are derived first"
        (is (some? fh))
        (is (some? ah)))
      (v/assert kb (list penguin Opus) CxBird {:strength :monotonic})
      (testing "blocking the first rule removes the conclusion that rested on it"
        (is (empty? (v/sentexes-matching kb (list flies Opus)    CxBird)))
        (is (empty? (v/sentexes-matching kb (list airborne Opus) CxBird))))
      (testing "both stay stored, read through the defeat"
        (is (some? (v/sentex kb fh)))
        (is (some? (v/sentex kb ah)))))))

;; ---- 6. a conjunctive exception -----------------------------------------
;; DECISION (The exception is a query, not a literal): "A conjunction is a vector,
;; spelled the way core/prove spells one."  Closure makes the conjuncts independent
;; ground checks, so all must hold and one alone must leave the rule firing.

(tu/deftest-kb a-conjunctive-exception-blocks-only-when-every-conjunct-holds
  (tu/with-terms [bird penguin young flies Opus CxBird]
    (v/assert kb (except-rule [(list penguin '?b) (list young '?b)]
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (testing "with neither conjunct, the rule fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))
    (v/assert kb (list penguin Opus) CxBird {:strength :monotonic})
    (testing "one conjunct is not the exception — the rule still fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))
    (v/assert kb (list young Opus) CxBird {:strength :monotonic})
    (testing "both conjuncts hold, so the exception holds and the conclusion goes"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))))

;; DECISION (Closure is enforced, not assumed): a variable a `thereExists` binds inside
;; the exception is the query's own, not one an antecedent owes — the closure check reads
;; free variables, as `unknown`'s does.  The witness is searched for; the rule's
;; variables are still bound before the query runs.

(tu/deftest-kb an-existential-exception-blocks-when-a-witness-exists
  (tu/with-terms [bird childOf sick flies Opus Kid Stranger CxBird]
    (v/assert kb (except-rule (list 'thereExists '?c (list 'and (list childOf '?b '?c) (list sick '?c)))
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (v/assert kb (list childOf Opus Kid) CxBird)
    (v/assert kb (list sick Stranger) CxBird)
    (testing "a child who is not sick and a sick non-child are no witness: one ?c takes both"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))
    (let [sh (v/assert kb (list sick Kid) CxBird)]
      (testing "a sick child is a witness, so the conclusion goes"
        (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
      (v/retract! kb sh)
      (testing "and retracting the witness re-derives it"
        (is (seq (v/sentexes-matching kb (list flies Opus) CxBird)))))))

(tu/deftest-kb an-existential-exception-revives-when-a-fact-ends-every-witness
  ;; the arriving fact names no rule variable — it is about the witness alone
  (tu/with-terms [bird childOf vaccinated flies Opus Kid CxBird]
    (v/assert kb (except-rule (list 'thereExists '?c (list 'and (list childOf '?b '?c)
                                                           (list 'unknown (list vaccinated '?c))))
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (v/assert kb (list childOf Opus Kid) CxBird)
    (testing "an unvaccinated child is a witness"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
    (v/assert kb (list vaccinated Kid) CxBird)
    (testing "vaccinating the only one ends the exception, and the rule fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))))

(tu/deftest-kb a-count-exception-an-arrival-imposed-is-released-by-the-next
  ;; an exception blocks while it holds, so a count — like an `unknown` — can stop
  ;; holding when a fact arrives; the block one arrival imposed, the next releases
  (tu/with-terms [bird childOf flies Opus K1 K2 CxBird]
    (v/assert kb (except-rule (list 'agg/count 1 '?c (list childOf '?b '?c))
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (testing "no child: the rule fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))
    (v/assert kb (list childOf Opus K1) CxBird)
    (testing "exactly one: the conclusion is not believed"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
    (v/assert kb (list childOf Opus K2) CxBird)
    (testing "the second child releases it"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))))

(tu/deftest-kb a-forall-exception-is-the-nested-naf-it-desugars-to
  ;; a `forall` conjunct is desugared at the entry point, as a `forall` antecedent is,
  ;; so the re-check index watches what is under it and the NAF spelling is one meta
  (tu/with-terms [bird childOf sick flies Opus Kid CxBird]
    (let [h (v/assert kb (except-rule (list 'forall '?c (list 'implies (list childOf '?b '?c) (list sick '?c)))
                                      [(list bird '?b)] (list flies '?b))
                      CxBird)]
      (v/assert kb (list bird Opus) CxBird)
      (testing "no child: the universal holds vacuously"
        (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
      (v/assert kb (list childOf Opus Kid) CxBird)
      (testing "a child who is not sick ends it"
        (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))
      (v/assert kb (list sick Kid) CxBird)
      (testing "every child sick restores it"
        (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
      (is (= h (v/assert kb (except-rule (list 'unknown (list 'thereExists '?d
                                                              (list 'and (list childOf '?b '?d)
                                                                    (list 'unknown (list sick '?d)))))
                                         [(list bird '?b)] (list flies '?b))
                         CxBird))))
    (let [bad (except-rule (list 'forall '?c (list sick '?c)) [(list bird '?b)] (list flies '?b))]
      (is (= :not-well-formed (:type (ex-data (try (v/assert kb bad CxBird)
                                                   (catch clojure.lang.ExceptionInfo e e))))))
      (is (= [:not-well-formed] (mapv :type (v/check kb bad CxBird)))))))

(tu/deftest-kb a-count-exception-compares-under-a-thereExists
  ;; the conjuncts of a vector share no variable, so a count is compared inside a
  ;; quantifier that binds it
  (tu/with-terms [bird childOf flies Opus K1 K2 CxBird]
    (v/assert kb (except-rule (list 'thereExists '?n (list 'and (list 'agg/count '?n '?c (list childOf '?b '?c))
                                                           (list 'lessThan 1 '?n)))
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (v/assert kb (list childOf Opus K1) CxBird)
    (testing "one child: the rule fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))
    (v/assert kb (list childOf Opus K2) CxBird)
    (testing "two: the exception holds"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))))

(tu/deftest-kb an-existential-exception-dedups-across-binder-names
  ;; canonical form: two exceptions identical up to the bound variable's name are one
  (tu/with-terms [bird childOf sick flies CxBird]
    (let [exc  #(list 'thereExists % (list 'and (list childOf '?b %) (list sick %)))
          h1   (v/assert kb (except-rule (exc '?c) [(list bird '?b)] (list flies '?b)) CxBird)
          h2   (v/assert kb (except-rule (exc '?d) [(list bird '?b)] (list flies '?b)) CxBird)]
      (is (= h1 h2)))))

(tu/deftest-kb an-existential-exception-binder-a-rule-variable-names-is-refused
  ;; the binder would be substituted with the rule's binding, so the quantifier would
  ;; quantify over a constant — refused, as a leaking antecedent `thereExists` is
  (tu/with-terms [bird childOf sick flies CxBird]
    (let [rule (except-rule (list 'thereExists '?b (list sick '?b))
                            [(list bird '?b)] (list flies '?b))]
      (is (= :quantifier-not-local
             (:type (ex-data (try (v/assert kb rule CxBird)
                                  (catch clojure.lang.ExceptionInfo e e))))))
      (is (= [:quantifier-not-local] (mapv :type (v/check kb rule CxBird)))))))

;; ---- 7. the exception is a level-6 query, not a literal lookup ----------
;; DECISION (The exception is a query, not a literal): "an exception may reach
;; through genl specificity, the genlCx visibility closure, transitive /
;; symmetric / inverse metadata, disjointness, and evaluable arithmetic."  These
;; two are what distinguish the feature from matching a stored fact: in neither
;; case is the exception sentence itself ever asserted.

(tu/deftest-kb an-exception-holding-only-through-genl-specificity-blocks
  (tu/with-terms [bird penguin flightless flies Opus CxBird]
    (v/assert kb (list 'genl penguin flightless) CxBird)
    (v/assert kb (except-rule (list flightless '?b)
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus)    CxBird)
    (v/assert kb (list penguin Opus) CxBird)
    (testing "no (flightless Opus) fact exists — only the subtype membership"
      (is (empty? (v/lookup kb 2 (list flightless Opus) CxBird))))
    (testing "but level 6 answers it through the spec walk, so the rule is blocked"
      (is (seq (v/lookup kb 6 (list flightless Opus) CxBird)))
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))))

(tu/deftest-kb an-exception-holding-only-through-a-transitive-closure-blocks
  (tu/with-terms [widget shiny insideOf Gem Box Vault CxVault]
    (v/assert kb (list 'transitive insideOf) CxVault)
    (v/assert kb (except-rule (list insideOf '?x Vault)
                              [(list widget '?x)] (list shiny '?x))
              CxVault)
    (v/assert kb (list widget Gem)        CxVault)
    (v/assert kb (list insideOf Gem Box)  CxVault)
    (v/assert kb (list insideOf Box Vault) CxVault)
    (testing "the exception is nowhere stored — it exists only in the closure"
      (is (empty? (v/lookup kb 2 (list insideOf Gem Vault) CxVault)))
      (is (seq    (v/lookup kb 6 (list insideOf Gem Vault) CxVault))))
    (testing "so the closure blocks the rule"
      (is (empty? (v/sentexes-matching kb (list shiny Gem) CxVault))))))

;; ---- 8. a taxonomy edge is a re-check trigger ---------------------------
;; DECISION (Taxonomy changes are keyed on what the closure moved): "An exception like
;; `(flightless_bird ?b)` can flip because someone asserted `(genl penguin
;; flightless_bird)` — no fact with a matching predicate ever arrives."  So the edge
;; must withdraw the conclusion, with the predicate-keyed re-check index never firing.

(tu/deftest-kb a-genl-edge-that-makes-the-exception-true-removes-the-conclusion
  (tu/with-terms [bird penguin flightless flies Opus CxBird]
    (v/assert kb (except-rule (list flightless '?b)
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus)    CxBird)
    (v/assert kb (list penguin Opus) CxBird {:strength :monotonic})
    (testing "penguin is not yet a flightless bird, so the rule fires"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))))
    ;; the only thing that changes is a genl edge — no (flightless ...) fact,
    ;; and nothing with the exception's predicate is ever asserted
    (v/assert kb (list 'genl penguin flightless) CxBird {:strength :monotonic})
    (testing "the edge alone makes the exception hold, and the conclusion is defeated"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))))

;; ---- 9. no backchaining -------------------------------------------------
;; DECISION (The exception is a query, not a literal): "**No backchaining.**  An
;; exception that is only derivable by running rules (level 7) does not hold" —
;; and "**An unanswerable exception does not hold**, and the rule fires."  The
;; exception here is reachable only through a backward-only rule, so level 6 has
;; no answer and the conclusion must be derived.

(tu/deftest-kb an-exception-derivable-only-by-backchaining-does-not-block
  (tu/with-terms [dog pet loud scary Muffet CxPet]
    ;; backward-only, so forward chaining never materializes (scary Muffet)
    (v/assert-rule kb [(list loud '?x)] (list scary '?x) CxPet {:direction :backward})
    (v/assert kb (except-rule (list scary '?x)
                              [(list dog '?x)] (list pet '?x))
              CxPet)
    (v/assert kb (list dog Muffet)  CxPet)
    (v/assert kb (list loud Muffet) CxPet)
    (testing "the exception is a level-7 answer and nothing less"
      (is (empty? (v/lookup kb 6 (list scary Muffet) CxPet)))
      (is (seq    (v/lookup kb 7 (list scary Muffet) CxPet))))
    (testing "so it does not hold, and the rule fires (the open-world reading)"
      (is (seq (v/sentexes-matching kb (list pet Muffet) CxPet))))))

;; ---- 10. backward inference and why-not ---------------------------------
;; DECISION (Semantics): "under backward chaining the argument is constructed and
;; then reported as excepted, so `why-not` can say *'rule R applies via (bird
;; Opus), but its exception (flightless_bird Opus) holds'* instead of recomputing a
;; contradiction it never recorded."

(tu/deftest-kb backward-inference-does-not-return-an-excepted-conclusion
  (tu/with-terms [bird penguin flies Tweety Opus CxBird]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Tweety)  CxBird)
    (v/assert kb (list bird Opus)    CxBird)
    (v/assert kb (list penguin Opus) CxBird)
    (testing "the unexcepted binding is provable both ways"
      (is (true? (v/provable? kb (list flies Tweety) CxBird)))
      (is (true? (v/ask?      kb (list flies Tweety) CxBird))))
    (testing "the excepted one is not — blocking is not a forward-chaining artifact"
      (is (false? (v/provable? kb (list flies Opus) CxBird)))
      (is (false? (v/ask?      kb (list flies Opus) CxBird))))
    (testing "and an open goal returns only the unexcepted binding"
      (is (= #{Tweety} (set (map #(get % '?who)
                                 (v/ask kb (list flies '?who) CxBird))))))))

(tu/deftest-kb why-not-reports-an-excepted-conclusion-as-excepted-not-unsupported
  ;; A blocker of either class stores the conclusion with a guard defeat, so the sentence
  ;; arity and the handle arity answer alike.
  (doseq [strength [:monotonic :default]]
    (tu/with-terms [bird penguin flies Opus CxBird]
      (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b)) CxBird)
      (v/assert kb (list bird Opus) CxBird)
      (v/assert kb (list penguin Opus) CxBird {:strength strength})
      (let [h   (v/handle-of kb (list flies Opus) CxBird)
            wns (cond-> [(v/why-not kb (list flies Opus) CxBird)] h (conj (v/why-not kb h)))]
        (testing (str strength)
          (is (some? h))
          (is (= (repeat (count wns) [false :excepted (list penguin Opus)])
                 (map (juxt :believed? :reason :exception) wns))))))))

;; ---- 11. rebutting dilemmas still coexist -------------------------------
;; DECISION (Semantics): "two rules concluding `P` and `¬P` with neither naming the
;; other's case is a genuine dilemma (the Nixon diamond), and the engine represents
;; it rather than deciding it.  Coexisting `P`/`¬P` at `:default` is therefore the
;; signature of a real dilemma, not of a badly-written exception."  This guards the
;; feature against over-reaching into rebutting defeat.

(tu/deftest-kb two-unexcepted-rules-concluding-opposites-remain-a-dilemma
  (tu/with-terms [quaker republican pacifist Nixon CxPol]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))              CxPol)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x)))  CxPol)
    (v/assert kb (list quaker Nixon)     CxPol)
    (v/assert kb (list republican Nixon) CxPol)
    (let [pos (v/handle-of kb (list pacifist Nixon)              CxPol)
          neg (v/handle-of kb (list 'not (list pacifist Nixon))  CxPol)]
      (testing "both conclusions are derived"
        (is (some? pos))
        (is (some? neg)))
      (testing "and both stay believed — neither rule named the other's case"
        (is (true? (v/believed? kb pos)))
        (is (true? (v/believed? kb neg)))
        (is (seq (v/sentexes-matching kb (list pacifist Nixon)             CxPol)))
        (is (seq (v/sentexes-matching kb (list 'not (list pacifist Nixon)) CxPol))))
      (testing "both at :default — the dilemma is represented, not decided"
        (is (= :default (v/defeat-class kb pos)))
        (is (= :default (v/defeat-class kb neg)))))))

;; ---- 12. the exception is evaluated where the conclusion lives ----------
;; DECISION (The exception is a query, not a literal): "**The exception is
;; evaluated in the conclusion's placement context**, not the rule's.  ...  an
;; exception invisible from where the conclusion would live has no business
;; blocking it."

(tu/deftest-kb an-exception-invisible-from-the-placement-context-does-not-block
  (tu/with-terms [bird penguin flies Opus CxHome CxFar]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              CxHome)
    (v/assert kb (list bird Opus) CxHome)
    ;; CxFar is unrelated to CxHome: no genlCx edge either way
    (is (not (v/sees? kb CxHome CxFar)) "test precondition")
    (v/assert kb (list penguin Opus) CxFar)
    (testing "the conclusion is placed in CxHome, which cannot see CxFar"
      (is (= CxHome (:context (v/sentex kb (v/handle-of kb (list flies Opus)
                                                        CxHome))))))
    (testing "so the far exception does not block"
      (is (seq (v/sentexes-matching kb (list flies Opus) CxHome))))
    (testing "the same exception asserted where the conclusion lives does block"
      (v/assert kb (list penguin Opus) CxHome {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxHome))))))

;; The exception's **own** context is scoped the same way.  An `exceptWhen` is a
;; sentex, so a context reasons with the exceptions its genlCx ancestor set holds and no
;; others: one stated in a context below the conclusion's blocks nothing there, even
;; when the query it asks holds in the conclusion's context.

(tu/deftest-kb an-exception-stated-below-the-placement-context-does-not-block
  (tu/with-terms [bird penguin flies Opus CxGen CxSpec CxSide]
    (let [rule (v/assert kb (tu/default-rule [(list bird '?b)] (list flies '?b)) CxGen)]
      (v/assert kb (list 'genlCx CxSpec CxGen) 'CxUniverse)
      (v/assert kb (list bird Opus) CxGen)
      (v/assert kb (list penguin Opus) CxGen)
      (is (not (v/sees? kb CxGen CxSpec)) "test precondition")
      (v/assert kb (list 'exceptWhen (list penguin '?b) (sx/sentex-handle rule)) CxSpec)
      (testing "the query holds in CxGen, but CxGen cannot see the exception"
        (is (seq (v/sentexes-matching kb (list flies Opus) CxGen)))
        (is (seq (v/query kb (list flies Opus) CxGen {:max-depth 2}))))
      (testing "an exception in an unrelated context blocks once a genlCx edge exposes it"
        (v/assert kb (list 'exceptWhen (list penguin '?b) (sx/sentex-handle rule)) CxSide)
        (is (seq (v/sentexes-matching kb (list flies Opus) CxGen)))
        (let [edge (v/assert kb (list 'genlCx CxGen CxSide) 'CxUniverse)]
          (is (empty? (v/sentexes-matching kb (list flies Opus) CxGen)))
          (v/retract! kb edge)
          (is (seq (v/sentexes-matching kb (list flies Opus) CxGen))))))))

;; ---- 13. the exception is not materialized per-instance -----------------
;; DECISION (The exception is a meta-sentex, not a materialized extent): materializing
;; the ground exception would store a probe `(penguin X)` for every individual the
;; exception does *not* apply to.  The exception is a single stored
;; meta-sentex `(exceptWhen <query> (sentexHandle H))`, re-evaluated on demand; no
;; per-instance probe is ever recorded.

(tu/deftest-kb an-exception-that-does-not-hold-materializes-nothing
  (tu/with-terms [bird penguin flies Tweety Robin Wren CxBird]
    (v/assert kb (except-rule (list penguin '?b)
                              [(list bird '?b)] (list flies '?b))
              CxBird)
    (doseq [b [Tweety Robin Wren]] (v/assert kb (list bird b) CxBird))
    (testing "every bird flies"
      (is (= 3 (count (v/sentexes-matching kb (list flies '?b) CxBird)))))
    (testing "not one penguin *fact* was stored for the birds that are not one"
      (is (zero? (v/count-with-functor kb penguin)))
      (is (empty? (v/sentexes-with-functor kb penguin))))
    (testing "the exception is one meta-sentex, whatever the number of birds"
      (is (= 1 (count (filter #(= 'exceptWhen (first (:sentence %)))
                              (v/find-sentexes kb penguin))))))))

;; DECISION (Storage and identity): an exceptWhen is a separate belief-following meta-sentex
;; naming the rule by handle, so a rule and its unexcepted twin share **one** handle —
;; asserting the exception amends that rule in place rather than forking a second one,
;; and retracting the exception restores it.

(tu/deftest-kb an-exception-amends-the-rule-in-place-sharing-one-handle
  (tu/with-terms [bird penguin flies Opus CxBird]
    (let [rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
          plain (v/assert kb (tu/default-rule [(list bird '?b)] (list flies '?b)) CxBird)
          exc   (v/assert kb (except-rule (list penguin '?b)
                                          [(list bird '?b)] (list flies '?b))
                          CxBird)]
      (testing "the exceptWhen is a separate meta-sentex, not the rule"
        (is (not= plain exc)))
      (testing "the rule keeps its one handle; the exception names it"
        (is (= plain (v/handle-of kb rule-form CxBird))))
      (v/assert kb (list bird Opus)    CxBird)
      (v/assert kb (list penguin Opus) CxBird)
      (testing "the exception amends the one rule, so the penguin does not fly"
        (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
      (v/retract! kb exc)
      (testing "retract the exception and the one rule concludes again"
        (is (seq (v/sentexes-matching kb (list flies Opus) CxBird)))))))

;; Two exceptions on one rule that differ only in **which rule variable** they name are
;; two meta-sentexes.  Their trie keys coincide — the key α-renames every variable and
;; the lookup reads one as a wildcard — so the dedup has to read the stored sentence
;; (`kb/find-sentex-handle`), or the second exception resolves to the first and is
;; silently never stored.

(tu/deftest-kb two-exceptions-naming-different-rule-variables-are-two-exceptions
  (tu/with-terms [bird parentOf flies sick Opus Pa CxBird]
    (let [rule (v/assert kb (tu/default-rule [(list bird '?y) (list parentOf '?x '?y)]
                                             (list flies '?y))
                         CxBird)
          on-x (v/assert kb (list 'exceptWhen (list sick '?x) (sx/sentex-handle rule)) CxBird)
          on-y (v/assert kb (list 'exceptWhen (list sick '?y) (sx/sentex-handle rule)) CxBird)]
      (testing "an exception on the parent and one on the bird are distinct meta-sentexes"
        (is (not= on-x on-y))
        (is (= 2 (count (filter #(= 'exceptWhen (first (:sentence %)))
                                (v/find-sentexes kb sick))))))
      (testing "re-asserting either spelling resolves to its own handle"
        (is (= on-x (v/assert kb (list 'exceptWhen (list sick '?x) (sx/sentex-handle rule)) CxBird)))
        (is (= on-y (v/assert kb (list 'exceptWhen (list sick '?y) (sx/sentex-handle rule)) CxBird))))
      ;; Opus is a sick bird with a healthy parent: the exception on the bird blocks,
      ;; the one on the parent does not hold, and the rule must not fire
      (v/assert kb (list bird Opus) CxBird)
      (v/assert kb (list parentOf Pa Opus) CxBird)
      (v/assert kb (list sick Opus) CxBird)
      (testing "the exception naming the bird is the one that holds, so the sick bird does not fly"
        (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
      (v/retract! kb on-y)
      (testing "with only the parent's exception left, the healthy parent's bird flies"
        (is (seq (v/sentexes-matching kb (list flies Opus) CxBird)))))))

(tu/deftest-kb a-ground-exception-and-a-variable-one-are-two-exceptions
  (tu/with-terms [bird flies sick Opus Tux CxBird]
    (let [rule   (v/assert kb (tu/default-rule [(list bird '?b)] (list flies '?b)) CxBird)
          ground (v/assert kb (list 'exceptWhen (list sick Opus) (sx/sentex-handle rule)) CxBird)
          open   (v/assert kb (list 'exceptWhen (list sick '?b) (sx/sentex-handle rule)) CxBird)]
      (testing "the ground exception does not absorb the open one — its key is a wildcard's match"
        (is (not= ground open)))
      (v/assert kb (list bird Tux) CxBird)
      (v/assert kb (list sick Tux) CxBird)
      (testing "the open exception blocks a sick bird the ground one never named"
        (is (empty? (v/sentexes-matching kb (list flies Tux) CxBird)))))))

;; DECISION (Stratification): "a rule set with a cycle through negation is
;; **rejected at assert time**, as a well-formedness check over the rule dependency
;; graph alongside the `genl` cycle check."  Here rule A's exception is what rule B
;; concludes and vice versa.

(tu/deftest-kb a-cycle-through-negation-across-two-rules-is-rejected-at-assert-time
  (tu/with-terms [base p q CxCyc]
    (v/assert kb (except-rule (list q '?x) [(list base '?x)] (list p '?x)) CxCyc)
    (testing "the second rule closes a cycle through negation and must be refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (except-rule (list p '?x) [(list base '?x)] (list q '?x))
                             CxCyc))))))

(tu/deftest-kb a-cycle-through-an-existential-exception-is-rejected-at-assert-time
  ;; the new exception's negative edge runs to the predicates its `thereExists` reads,
  ;; not to the quantifier's own functor, which no rule concludes
  (tu/with-terms [base link p q CxCyc]
    (v/assert kb (except-rule (list q '?x) [(list base '?x)] (list p '?x)) CxCyc)
    (is (= :not-stratified
           (:type (ex-data (try (v/assert kb (except-rule (list 'thereExists '?y
                                                                (list 'and (list link '?x '?y) (list p '?y)))
                                                          [(list base '?x)] (list q '?x))
                                          CxCyc)
                                (catch clojure.lang.ExceptionInfo e e))))))))

(tu/deftest-kb a-cycle-through-an-unknown-exception-is-rejected-at-assert-time
  ;; the same read for an `unknown` query: its edge runs to `p`, not to `unknown`
  (tu/with-terms [base p q CxCyc]
    (v/assert kb (except-rule (list q '?x) [(list base '?x)] (list p '?x)) CxCyc)
    (is (= :not-stratified
           (:type (ex-data (try (v/assert kb (except-rule (list 'unknown (list p '?x))
                                                          [(list base '?x)] (list q '?x))
                                          CxCyc)
                                (catch clojure.lang.ExceptionInfo e e))))))))
