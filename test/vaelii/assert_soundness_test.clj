;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.assert-soundness-test
  "Probes for the seams where `assert`'s checks and `assert`'s *storage* can
  disagree.

  Every definitional check — naming, well-formedness, argIsa, disjointness,
  functionality — runs on the sentence the caller handed in.  What gets stored is
  the sentence the `sentex` constructor canonicalizes out of it.  Wherever those two
  forms differ, there is a seam, and a check that runs on one side while the other
  is stored is a check that can be walked around.

  The seams tested here: a virtual wrapper peeled by the constructor, a conjunctive
  consequent split into several rules, and the derivation path, which stores without
  going through `assert` at all."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- seam 1: a virtual wrapper around a non-rule ------------------------
;;
;; `set/defaultRule` / `exceptWhen` / `set/forwardRule` are wrappers the sentex
;; constructor peels into record fields.  Wrapped around an *implication* that is
;; their whole purpose.  Wrapped around a plain fact they are meaningless — but the
;; constructor peels them just the same, so `(set/defaultRule (dog Felix))` stores
;; the bare fact `(dog Felix)`.
;;
;; The danger is that `assert-one` routes on `rules/rule-sentence?` of the *inner*
;; form.  A wrapped fact is not a rule, so it falls to the fact branch — where the
;; naming, well-formedness and constraint checks all run against the **wrapper**,
;; whose functor is `set/defaultRule` and whose single argument is a list.  Those
;; checks are about `(dog Felix)`; if they inspect `(set/defaultRule (dog Felix))`
;; instead, they inspect the wrong sentence and pass vacuously, and the fact is
;; stored unchecked.

(tu/deftest-kb a-wrapper-around-a-fact-does-not-smuggle-it-past-the-disjointness-check
  ;; one context throughout: the disjointness check is context-scoped and this KB
  ;; is fresh, so a declaration in an unwired UniverseContext would be invisible
  (tu/with-terms [dog cat Felix]
    (v/assert kb (list 'disjoint dog cat) 'NaturalWorldContext)
    (v/assert kb (list cat Felix) 'NaturalWorldContext)
    (testing "asserted directly, the conflicting type is refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list dog Felix) 'NaturalWorldContext))))
    (testing "and wrapping it in set/defaultRule must not buy a way around that"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'set/defaultRule (list dog Felix)) 'NaturalWorldContext))))
    (testing "nothing was stored either way"
      (is (empty? (v/sentexes-matching kb (list dog Felix) 'NaturalWorldContext))))))

(tu/deftest-kb a-wrapper-around-a-fact-does-not-smuggle-it-past-the-context-check
  ;; A context name must end in `Context`.  Asserting into a non-context is refused;
  ;; the wrapper must not launder that either.
  (tu/with-terms [dog Muffet]
    (testing "asserted directly it is refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list dog Muffet) 'SomewhereElse))))
    (testing "wrapped, it is refused too"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'set/defaultRule (list dog Muffet)) 'SomewhereElse))))))

(tu/deftest-kb a-wrapper-around-a-fact-does-not-smuggle-a-non-ground-sentence-in
  ;; A non-ground fact asserts nothing — stored as a premise it would match any goal.
  (tu/with-terms [mortal]
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list mortal '?x) 'NaturalWorldContext)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'set/defaultRule (list mortal '?x)) 'NaturalWorldContext)))))

;; ---- seam 2: a conjunctive consequent split into several rules ----------
;;
;; `(implies A (and C1 C2))` is polycanonicalized into one rule per conjunct, and
;; `assert` then `mapv`s over them.  A `mapv` is not a transaction: if the second
;; conjunct is refused, the first is already stored, indexed, and chained from.  The
;; caller sees a throw and reasonably concludes nothing was asserted.

(tu/deftest-kb a-refused-conjunct-leaves-no-half-asserted-rule
  (tu/with-terms [a b c]
    (let [before-sx (tu/sentex-ids kb)
          before-dd (tu/justification-ids kb)]
      (testing "the rule is refused — its second conjunct is not range-restricted"
        (is (= :not-range-restricted
               (try (v/assert kb (vr/rule-sentence [(list a '?x)]
                                                   (list 'and (list b '?x) (list c '?y)))
                              'NaturalWorldContext)
                    nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
      (testing "and the first conjunct's rule was not left behind"
        (is (= before-sx (tu/sentex-ids kb))
            "a refused rule stores nothing — not even the conjuncts that were fine")
        (is (= before-dd (tu/justification-ids kb)))))))

(tu/deftest-kb a-conjunctive-consequent-still-stores-every-conjunct-when-all-are-well-formed
  ;; The complement, so the fix above cannot be "refuse conjunctive consequents".
  (tu/with-terms [a b c Thing]
    (let [hs (v/assert kb (vr/rule-sentence [(list a '?x)]
                                            (list 'and (list b '?x) (list c '?x)))
                       'NaturalWorldContext)]
      (is (vector? hs) "a conjunctive consequent returns the vector of rule handles")
      (is (= 2 (count hs)))
      (v/assert kb (list a Thing) 'NaturalWorldContext)
      (testing "both conjuncts are derived"
        (is (seq (v/sentexes-matching kb (list b Thing) 'NaturalWorldContext)))
        (is (seq (v/sentexes-matching kb (list c Thing) 'NaturalWorldContext)))))))

;; ---- seam 3: the derivation path ----------------------------------------
;;
;; `place-conclusion` runs the three *constraint* checks (argIsa, disjointness,
;; functionality) so derived content is held to the same standard as asserted
;; content.  Well-formedness of the special predicates is a different check, and a
;; rule may conclude one: `(implies (foo ?x ?y) (genl ?x ?y))` derives taxonomy
;; edges.  A derived edge reaches the closure through `integrate-transitive`, so a
;; derived *cycle* would corrupt `genls`/`specs` — and the closure is what matching,
;; placement and stratification all read.

(tu/deftest-kb a-derived-genl-edge-cannot-close-a-cycle-in-the-taxonomy
  (tu/with-terms [dog animal relates]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (testing "the reverse edge is refused when asserted directly — it would cycle"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'genl animal dog) 'UniverseContext))))
    ;; now try to derive the same edge instead of asserting it
    (v/assert kb (list 'set/forwardRule
                       (vr/rule-sentence [(list relates '?x '?y)] (list 'genl '?x '?y)))
              'UniverseContext)
    (v/assert kb (list relates animal dog) 'UniverseContext)
    (testing "deriving it must not corrupt the closure either"
      (is (not (v/genl? kb animal dog))
          "a derived edge closed a genl cycle: animal is now a subtype of itself")
      (is (v/genl? kb dog animal) "the legitimate edge is untouched"))
    (testing "and the cycle is not reachable through the up-closure"
      (is (not (contains? (set (v/genls kb animal)) dog))))))

;; ---- seam 4: rule identity must track the consequent's polarity ---------
;;
;; The trie key drops the `implies`/`and` frame, and a negative literal keeps its
;; `not` there as *polarity*.  If the consequent's `not` were dropped from the key,
;; a rule and its negation would key identically — and rule assertion is
;; first-writer-wins, so the second would silently resolve to the first rather than
;; storing.  Every existing key test asserts two rules that *should* collide do;
;; this asserts two that must not, don't.

(tu/deftest-kb a-rule-and-its-negated-twin-are-different-rules
  (tu/with-terms [p q]
    (let [pos (v/assert kb (vr/rule-sentence [(list p '?x)] (list q '?x)) 'NaturalWorldContext)
          neg (v/assert kb (vr/rule-sentence [(list p '?x)] (list 'not (list q '?x)))
                        'NaturalWorldContext)]
      (is (not= pos neg)
          "identical antecedents, opposite conclusions — these must be two sentexes")
      (testing "and each keeps its own consequent polarity"
        (is (= :true (:truth (v/sentex kb pos))))
        (is (= :true (:truth (v/sentex kb neg)))
            "both rules are asserted true — the negation is the consequent's polarity,
             carried in the sentence, and never the rule sentex's own truth")
        (let [negated? (fn [h] (boolean
                                (some #(and (sequential? %) (= 'not (first %)))
                                      (tree-seq sequential? seq
                                                (:sentence (v/sentex kb h))))))]
          (is (not (negated? pos)) "the positive rule stores no `not`")
          (is (negated? neg)       "the negative rule keeps its `not` as polarity"))))))

;; ---- range restriction bottoms out as a value ---------
;;
;; `range-problems` is the value form and `check-range-restricted` throws typed ex-info
;; by wrapping it.  Never `clojure.core/assert` here: it is elidable, so a build compiled
;; with `*assert*` false would store the junk rule silently, and its AssertionError
;; carries no `:type`.

(deftest range-restriction-is-a-value-first
  (is (empty? (vr/range-problems ['(p ?x)] '(q ?x))))
  (is (seq (vr/range-problems ['(p ?x)] '(q ?y)))
      "an unbound consequent variable is a reported problem, not an elidable assert")
  (is (= :not-range-restricted
         (try (vr/check-range-restricted ['(p ?x)] '(q ?y)) nil
              (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))

;; ---- seam 4: a rule the rule index cannot key on ------------------------
;;
;; The rule index has two cells and both are keyed on a **predicate**
;; (`kv/rule-ante-key` / `rule-conseq-key`).  A literal with a variable in functor
;; position names none, and `canonicalize-rule` numbers it to `?var0` before
;; `special/index-rule-sentex` reads the sentence — so the posting lands under a key no
;; arriving fact and no goal can spell.  Stored, indexed, and unreachable: the rule
;; answers no backward goal, and fires forward only when a concrete-predicate antecedent
;; beside it arrives, which makes its conclusions depend on arrival order.  So it is
;; refused at the door, with the one exception that claims nothing — an `:inert` rule.

(tu/deftest-kb a-rule-with-a-variable-predicate-is-refused
  (tu/with-terms [likesOf]
    (let [before-sx (tu/sentex-ids kb)
          metarule  (vr/rule-sentence ['(?p ?x ?y) '(transitive ?p)] '(?p ?y ?x))]
      (testing "an antecedent literal with a variable functor"
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/assert kb metarule 'NaturalWorldContext)))]
          (is (= :not-indexable (:type (ex-data e))))
          (is (re-find #"instantiated" (ex-message e))
              "and the message names what to write instead")))
      (testing "a consequent literal with one, even when every antecedent is concrete"
        (is (= :not-indexable
               (try (v/assert kb (vr/rule-sentence [(list likesOf '?x '?y) '(transitive ?p)]
                                                   '(?p ?y ?x))
                              'NaturalWorldContext)
                    nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
      (testing "the same refusal through assert-rule, which wraps and calls assert"
        (is (= :not-indexable
               (try (v/assert-rule kb ['(?p ?x ?y) '(transitive ?p)] '(?p ?y ?x)
                                   'NaturalWorldContext)
                    nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
      (testing "and nothing was stored on the way to any of those"
        (is (= before-sx (tu/sentex-ids kb)))))))

(tu/deftest-kb an-inert-rule-may-carry-a-variable-predicate
  ;; `:inert` runs in neither engine — it is documentation with a handle — so an index
  ;; key it never reads is nothing it promised.  `CoreContext` ships one: the
  ;; decontextualized-predicate lift, stated as `(implies (?pred . ?args) (ist
  ;; UniverseContext (?pred . ?args)))` for a reader and implemented in code.
  (let [h (v/assert kb (list 'set/inertRule
                             (vr/rule-sentence ['(?p ?x ?y) '(transitive ?p)] '(?p ?y ?x)))
                    'NaturalWorldContext)]
    (is (some? h) "the inert spelling still asserts")
    (is (= :inert (:direction (v/sentex kb h))))
    (v/retract! kb h)))

(tu/deftest-kb a-concrete-rule-of-the-same-shape-still-asserts
  ;; The complement, so the refusal above cannot be "refuse a rule with two antecedents":
  ;; the instantiated rule the message asks for is exactly this, and it must land.
  (tu/with-terms [likesOf]
    (let [h (v/assert kb (vr/rule-sentence [(list likesOf '?x '?y)] (list likesOf '?y '?x))
                      'NaturalWorldContext)]
      (is (some? h))
      (v/retract! kb h))))

(deftest a-variable-functor-literal-is-a-value-first
  ;; The same shape as range restriction: the reader answers with the literals, and the
  ;; throw is a wrapper over it — so `check` can report what `assert` refuses without a
  ;; second implementation to drift.
  (is (empty? (vr/variable-functor-literals '(implies (and (dog ?x)) (animal ?x)))))
  (is (= ['(?p ?x ?y) '(?p ?y ?x)]
         (mapv second (vr/variable-functor-literals
                       '(implies (and (?p ?x ?y) (transitive ?p)) (?p ?y ?x)))))
      "both frames are read, and the concrete antecedent beside them is not a problem")
  (is (= :not-indexable
         (try (vr/check-indexable-functors '(implies (and (?p ?x ?y)) (?p ?y ?x))) nil
              (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
