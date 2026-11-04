;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.assert-soundness-test
  "Probes for the gaps where `assert`'s checks and `assert`'s *storage* can
  disagree.

  Every definitional check — naming, well-formedness, arg, disjointness,
  functionality — runs on the sentence the caller handed in.  What gets stored is
  the sentence the `sentex` constructor canonicalizes out of it.  Wherever those two
  forms differ, there is a gap, and a check that runs on one side while the other
  is stored is a check that can be walked around.

  The gaps tested here: a virtual wrapper peeled by the constructor, a conjunctive
  consequent split into several rules, and the derivation path, which stores without
  going through `assert` at all."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as rz]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- gap 1: a virtual wrapper around a non-rule ------------------------
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
  ;; one context throughout: the disjointness check is context-scoped
  (tu/with-terms [dog cat Felix Tom]
    (v/assert kb (list 'disjoint dog cat) 'CxNaturalWorld)
    (v/assert kb (list cat Felix) 'CxNaturalWorld)
    (v/assert kb (list cat Tom) 'CxNaturalWorld)
    (testing "asserted directly, the conflicting type is a clash"
      (is (tu/stored-in-clash? kb (list dog Felix) 'CxNaturalWorld)))
    (testing "and wrapping it in set/defaultRule must not buy a way around that"
      (is (tu/stored-in-clash? kb (list 'set/defaultRule (list 'set/forwardRule (list dog Tom)))
                               'CxNaturalWorld)))
    (testing "the two clashes are the same kind"
      (is (= [:disjoint :disjoint] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-wrapper-around-a-fact-does-not-smuggle-it-past-the-context-check
  ;; A context name must start with `Cx`.  Asserting into a non-context is refused;
  ;; the wrapper must not launder that either.
  (tu/with-terms [dog Muffet]
    (testing "asserted directly it is refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list dog Muffet) 'SomewhereElse))))
    (testing "wrapped, it is refused too"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (list dog Muffet))) 'SomewhereElse))))))

(tu/deftest-kb a-wrapper-around-a-fact-does-not-smuggle-a-non-ground-sentence-in
  ;; A non-ground fact asserts nothing — stored as a premise it would match any goal.
  (tu/with-terms [mortal]
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list mortal '?x) 'CxNaturalWorld)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (list mortal '?x))) 'CxNaturalWorld)))))

;; ---- gap 2: a conjunctive consequent split into several rules ----------
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
                              'CxNaturalWorld {:direction :forward})
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
                       'CxNaturalWorld {:direction :forward})]
      (is (vector? hs) "a conjunctive consequent returns the vector of rule handles")
      (is (= 2 (count hs)))
      (v/assert kb (list a Thing) 'CxNaturalWorld)
      (testing "both conjuncts are derived"
        (is (seq (v/sentexes-matching kb (list b Thing) 'CxNaturalWorld)))
        (is (seq (v/sentexes-matching kb (list c Thing) 'CxNaturalWorld)))))))

;; ---- gap 3: the derivation path ----------------------------------------
;;
;; `place-conclusion` runs the three *constraint* checks (arg, disjointness,
;; functionality) so derived content is held to the same standard as asserted
;; content.  Well-formedness of the special predicates is a different check, and a
;; rule may conclude one: `(implies (foo ?x ?y) (genl ?x ?y))` derives taxonomy
;; edges.  A derived edge reaches the closure through `integrate-transitive`, so a
;; derived *cycle* would corrupt `genls`/`specs` — and the closure is what matching,
;; placement and stratification all read.

(tu/deftest-kb a-derived-genl-edge-cannot-close-a-cycle-in-the-taxonomy
  (tu/with-terms [dog animal relates]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (testing "the reverse edge is refused when asserted directly — it would cycle"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'genl animal dog) 'CxUniverse))))
    ;; now try to derive the same edge instead of asserting it
    (v/assert kb (list 'set/forwardRule
                       (vr/rule-sentence [(list relates '?x '?y)] (list 'genl '?x '?y)))
              'CxUniverse)
    (v/assert kb (list relates animal dog) 'CxUniverse)
    (testing "deriving it must not corrupt the closure either"
      (is (not (v/genl? kb animal dog))
          "a derived edge closed a genl cycle: animal is now a subtype of itself")
      (is (v/genl? kb dog animal) "the legitimate edge is untouched"))
    (testing "and the cycle is not reachable through the up-closure"
      (is (not (contains? (set (v/genls kb animal)) dog))))))

;; ---- gap 4: rule identity must track the consequent's polarity ---------
;;
;; The trie key drops the `implies`/`and` frame, and a negative literal keeps its
;; `not` there as *polarity*.  If the consequent's `not` were dropped from the key,
;; a rule and its negation would key identically — and rule assertion is
;; first-writer-wins, so the second would silently resolve to the first rather than
;; storing.  Every existing key test asserts two rules that *should* collide do;
;; this asserts two that must not, don't.

(tu/deftest-kb a-rule-and-its-negated-twin-are-different-rules
  (tu/with-terms [p q]
    (let [pos (v/assert kb (vr/rule-sentence [(list p '?x)] (list q '?x)) 'CxNaturalWorld {:direction :forward})
          neg (v/assert kb (vr/rule-sentence [(list p '?x)] (list 'not (list q '?x)))
                        'CxNaturalWorld {:direction :forward})]
      (is (not= pos neg)
          "identical antecedents, opposite conclusions — these must be two sentexes")
      (testing "and each keeps its own consequent's sign"
        (is (= (list q '?var0) (:consequent (v/sentex kb pos))))
        (is (= (list 'not (list q '?var0)) (:consequent (v/sentex kb neg)))
            "both rules are asserted true — the negation belongs to the consequent,
             and a rule sentex has no sign of its own")
        (let [negated? (fn [h] (boolean
                                (some #(and (sequential? %) (= 'not (first %)))
                                      (tree-seq sequential? seq
                                                (v/sentence-of (v/sentex kb h))))))]
          (is (not (negated? pos)) "the positive rule stores no `not`")
          (is (negated? neg)       "the negative rule keeps its `not` in its consequent"))))))

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

;; ---- gap 4: a rule the rule index cannot key on ------------------------
;;
;; The rule index has two cells and both are keyed on a **predicate**
;; (`vr/antecedent-key` / `consequent-key`).  A variable in functor position names none,
;; and `canonicalize-rule` numbers it to `?var0` before `special/index-rule-sentex` reads
;; the sentence.  The split (reasoning/27): a variable functor in an **antecedent** is the
;; widest trigger the engine can have — no arriving fact can key it, so it fires only when
;; a concrete antecedent beside it arrives, which makes its conclusions depend on arrival
;; order.  That is refused at the entry point, with the one exception that claims nothing — an
;; `:inert` rule.  A variable functor in the **consequent** is bound by a concrete
;; antecedent (range restriction guarantees it), so it fires forward with the predicate
;; ground and is filed under the `p/var-consequent-key` catch-all for backward reach.

(tu/deftest-kb a-variable-predicate-antecedent-is-refused
  (tu/with-terms [likesOf]
    (let [before-sx (tu/sentex-ids kb)
          metarule  (vr/rule-sentence ['(?p ?x ?y) '(transitive ?p)] '(?p ?y ?x))]
      (testing "an antecedent literal with a variable functor"
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/assert kb metarule 'CxNaturalWorld)))]
          (is (= :not-indexable (:type (ex-data e))))
          (is (= :antecedent (:role (ex-data e))) "and it names the refused side")
          (is (re-find #"instantiated" (ex-message e))
              "and the message names what to write instead")))
      (testing "the same refusal through assert-rule, which wraps and calls assert"
        (is (= :not-indexable
               (try (v/assert-rule kb ['(?p ?x ?y) '(transitive ?p)] '(?p ?y ?x)
                                   'CxNaturalWorld {:direction :forward})
                    nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
      (testing "and nothing was stored on the way to either"
        (is (= before-sx (tu/sentex-ids kb)))))))

(tu/deftest-kb a-variable-predicate-consequent-is-indexed-and-fires
  ;; The consequent half of the split.  A rule concluding `(?p ?x ?y)` off a concrete
  ;; antecedent that binds `?p`: forward it fires with the predicate ground, backward it
  ;; is reachable through the `p/var-consequent-key` catch-all.
  (tu/with-terms [holds loves Tom Ann]
    (let [rule (list 'set/forwardRule (vr/rule-sentence [(list holds '?p '?x '?y)] '(?p ?x ?y)))
          h    (v/assert kb rule 'CxNaturalWorld)]
      (is (some? h) "the rule with a concrete antecedent and a variable consequent asserts")
      (testing "forward: a matching fact fires it with the predicate ground"
        (v/assert kb (list holds loves Tom Ann) 'CxNaturalWorld)
        (is (v/ask? kb (list loves Tom Ann) 'CxNaturalWorld)))
      (testing "backward: a concrete goal reaches the rule through the catch-all"
        (is (contains? (rz/concluding-rule-handles kb loves) h)
            "the var-consequent bucket is unioned into the concrete-goal answer")))))

(tu/deftest-kb a-bare-variable-consequent-is-refused-and-its-dotted-rest-rewrite-concludes
  ;; `?s` is a term in a formula position.  The rewrite binds the functor and the
  ;; arguments separately, and concludes the sentence the antecedent's argument holds.
  (tu/with-terms [believes loves Tom Ann CxOne CxTwo]
    (let [bare   (list 'implies (list believes '?x '?s) '?s)
          dotted (list 'implies (list believes '?x '(?pred . ?args)) '(?pred . ?args))
          fact   (list believes Tom (list loves Tom Ann))
          e      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb bare CxOne)))]
      (is (= :not-well-formed (:type (ex-data e))))
      (is (re-find #"\(\?pred \. \?args\)" (ex-message e)) "the message names the rewrite")
      (testing "forward: the fact's sentence argument is concluded"
        (v/assert kb (list 'set/forwardRule dotted) CxOne)
        (v/assert kb fact CxOne)
        (is (v/ask? kb (list loves Tom Ann) CxOne)))
      (testing "backward: a goal on the concluded predicate reaches the rule"
        (v/assert kb (list 'set/backwardRule dotted) CxTwo)
        (v/assert kb fact CxTwo)
        (is (not (v/ask? kb (list loves Tom Ann) CxTwo)) "nothing is concluded forward")
        (is (= [(list loves Tom Ann)]
               (mapv #(rz/substitute (list loves '?who Ann) %)
                     (v/prove kb (list loves '?who Ann) CxTwo))))))))

(tu/deftest-kb an-unbound-consequent-predicate-is-still-range-refused
  ;; The consequent split does not loosen range restriction: a consequent functor no
  ;; antecedent binds is a typo, not a metarule, and stays refused.
  (tu/with-terms [dog]
    (is (= :not-range-restricted
           (try (v/assert kb (vr/rule-sentence [(list dog '?x)] '(?p ?x)) 'CxNaturalWorld {:direction :forward})
                nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

(tu/deftest-kb an-inert-rule-may-carry-a-variable-predicate
  ;; `:inert` runs in neither engine — it is documentation with a handle — so an index
  ;; key it never reads is nothing it promised.  `CxUniverse` ships one: the
  ;; decontextualized-predicate lift, stated as `(implies (?pred . ?args) (ist
  ;; CxUniverse (?pred . ?args)))` for a reader and implemented in code.
  (tu/with-terms [likes]
    (let [h (v/assert kb (list 'set/inertRule
                               (vr/rule-sentence ['(?p ?x ?y) '(transitive ?p)] '(?p ?y ?x)))
                      'CxNaturalWorld)]
      (is (some? h) "the inert spelling still asserts")
      (is (= #{} (:engines (v/sentex kb h))))
      (is (not (contains? (rz/concluding-rule-handles kb likes) h))
          "an inert var-consequent rule keeps the dead ?var0 key — never a concluder for every goal")
      (v/retract! kb h))))

(tu/deftest-kb a-concrete-rule-of-the-same-shape-still-asserts
  ;; The complement, so the refusal above cannot be "refuse a rule with two antecedents":
  ;; the instantiated rule the message asks for is exactly this, and it must land.
  (tu/with-terms [likesOf]
    (let [h (v/assert kb (vr/rule-sentence [(list likesOf '?x '?y)] (list likesOf '?y '?x))
                      'CxNaturalWorld {:direction :forward})]
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
