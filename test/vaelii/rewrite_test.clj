;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rewrite-test
  "The pure oriented-rewriting engine (`vaelii.impl.rewrite`): orientation by a
  reduction order, one-way matching, and normalization to a fixpoint.  No store, no
  belief — just term algebra, so these are ordinary unit tests with no KB."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.rewrite :as rw]))

(deftest normalization-support-traces-actual-recursive-and-second-steps
  (let [rules [{:lhs '(f (f ?x)) :rhs '(g ?x) :handle 11}
               {:lhs '(g ?x) :rhs '?x :handle 12}
               {:lhs '(unrelated ?x) :rhs '?x :handle 99}]]
    (is (= ['A #{11 12}] (rw/normalize-with-support rules '(f (f A)))))
    (is (= (rw/normalize rules '(f (f A)))
           (first (rw/normalize-with-support rules '(f (f A))))))
    (is (= ['(pair A B) #{11 12}]
           (rw/normalize-with-support rules '(pair (f (f A)) B))))
    (is (= ['(p A) #{11 12}]
           (rw/normalize-sentence-with-support rules '(p (f (f A))))))
    (is (= ['(rewriteOf T (f (f A))) #{}]
           (rw/normalize-sentence-with-support rules '(rewriteOf T (f (f A))))))
    (is (= ['A #{}] (rw/normalize-with-support rules 'A)))))

(deftest term-size-counts-leaves
  (is (= 1 (rw/term-size 'Tom)))
  (is (= 1 (rw/term-size '?x)))
  (is (= 2 (rw/term-size '(grandfather_of ?x))))
  (is (= 3 (rw/term-size '(fatherOf (fatherOf ?x))))))

(deftest orient-picks-the-shrinking-direction
  (testing "the bigger side rewrites to the smaller"
    (is (= '[(fatherOf (fatherOf ?x)) (grandfather_of ?x)]
           (rw/orient '(fatherOf (fatherOf ?x)) '(grandfather_of ?x))))
    (is (= '[(fatherOf (fatherOf ?x)) (grandfather_of ?x)]
           (rw/orient '(grandfather_of ?x) '(fatherOf (fatherOf ?x))))
        "orientation is content-derived, independent of the written order"))
  (testing "an equal-weight pair is oriented by the symbol precedence, either way written"
    ;; g ≻_F f by name, so both spellings orient (g …) → (f …)
    (is (= '[(g ?x) (f ?x)] (rw/orient '(f ?x) '(g ?x))))
    (is (= '[(g ?x) (f ?x)] (rw/orient '(g ?x) '(f ?x))))
    (testing "and an equal-size nesting orients too, where size-only refused"
      (is (= '[(g (f ?x)) (f (g ?x))] (rw/orient '(f (g ?x)) '(g (f ?x)))))))
  (testing "a permutative equation cannot be oriented by any term order"
    (is (nil? (rw/orient '(rel ?x ?y) '(rel ?y ?x)))))
  (testing "the bigger side shrinks even when it repeats a variable"
    ;; (g ?x ?x) -> (f ?x) is a valid terminating rewrite; the reverse would grow
    (is (= '[(g ?x ?x) (f ?x)] (rw/orient '(f ?x) '(g ?x ?x)))))
  (testing "a bigger side carrying a variable the smaller lacks is refused"
    ;; (g ?x ?x) -> (f ?y) would introduce an unbound ?y
    (is (nil? (rw/orient '(f ?y) '(g ?x ?x))))))

(deftest orient-decides-an-equal-weight-pair-differing-at-a-constant
  ;; Same root, same weight, first difference at a *constant* position: a constant is
  ;; a nullary function symbol, so the precedence on the constants decides — without
  ;; throwing, and in either written order.
  (testing "two constants"
    (is (= '[(g b ?x) (g a ?x)] (rw/orient '(g a ?x) '(g b ?x))))
    (is (= '[(g b ?x) (g a ?x)] (rw/orient '(g b ?x) '(g a ?x))))
    (is (= '[(UnitFn Metre ?n) (UnitFn Meter ?n)]
           (rw/orient '(UnitFn Meter ?n) '(UnitFn Metre ?n))))
    (is (= '[(UnitFn Metre ?n) (UnitFn Meter ?n)]
           (rw/orient '(UnitFn Metre ?n) '(UnitFn Meter ?n)))))
  (testing "a constant against a nullary compound of equal weight"
    (is (= '[(g (f) ?x) (g c ?x)] (rw/orient '(g c ?x) '(g (f) ?x))))
    (is (= '[(g (f) ?x) (g c ?x)] (rw/orient '(g (f) ?x) '(g c ?x))))
    (is (nil? (rw/orient '(g c ?x) '(g (c) ?x)))
        "the same symbol as constant and as nullary functor is incomparable"))
  (testing "leaves of different classes order without throwing, and the same either way"
    (let [one-way (rw/orient '(g 1 ?x) '(g a ?x))]
      (is (some? one-way))
      (is (= one-way (rw/orient '(g a ?x) '(g 1 ?x)))))
    (is (= '[(g 2 ?x) (g 1 ?x)] (rw/orient '(g 1 ?x) '(g 2 ?x))))))

(deftest the-precedence-is-total-over-every-term-shape
  ;; `root` returns a *term*, not always a symbol — a functor may itself be compound —
  ;; and an argument may be any encodable value.  So the precedence is asked about
  ;; things `compare` refuses: a compound, a collection, a vector whose elements are of
  ;; mixed classes.  It must answer all of them, because `orient` is reached from the
  ;; assert entry point and a comparison that throws there refuses an equation by exception
  ;; instead of by returning nil.
  (testing "a compound root"
    (is (= '[((g ?x) a) ((f ?x) a)] (rw/orient '((f ?x) a) '((g ?x) a))))
    (is (= '[((g ?x) a) ((f ?x) a)] (rw/orient '((g ?x) a) '((f ?x) a)))
        "content-derived, so the written order does not decide it")
    (is (false? (rw/kbo> '((f ?x) a) '((g ?x) a))))
    (is (true?  (rw/kbo> '((g ?x) a) '((f ?x) a)))))
  (testing "a collection in argument position"
    (doseq [[l r] [['(g #{1} ?x) '(g #{2} ?x)]
                   ['(g {:a 1} ?x) '(g {:b 2} ?x)]
                   ['(g [1 :a] ?x) '(g [1 "b"] ?x)]
                   ['(g [:a] ?x) '(g [1] ?x)]]]
      (let [one-way (rw/orient l r)]
        (is (some? one-way) (str "no orientation for " (pr-str [l r])))
        (is (= one-way (rw/orient r l))
            (str "the two written orders disagree for " (pr-str [l r])))))))

(deftest match-is-one-way
  (testing "a ground subject binds the pattern's variables"
    (is (= '{?x Tom} (rw/match '(fatherOf (fatherOf ?x)) '(fatherOf (fatherOf Tom))))))
  (testing "a variable-bearing subject binds the pattern var to the subject term"
    (is (= '{?x ?y} (rw/match '(fatherOf (fatherOf ?x)) '(fatherOf (fatherOf ?y))))))
  (testing "a repeated pattern variable demands consistency"
    (is (= '{?x Tom} (rw/match '(rel ?x ?x) '(rel Tom Tom))))
    (is (nil? (rw/match '(rel ?x ?x) '(rel Tom Sue)))))
  (testing "arity / head mismatch does not match"
    (is (nil? (rw/match '(fatherOf ?x) '(motherOf Tom))))
    (is (nil? (rw/match '(fatherOf ?x) '(fatherOf Tom Extra))))))

(deftest normalize-reduces-to-the-normal-form
  (let [rules [{:lhs '(fatherOf (fatherOf ?x)) :rhs '(grandfather_of ?x)}]]
    (testing "a term is rewritten to its normal form"
      (is (= '(grandfather_of Tom) (rw/normalize rules '(fatherOf (fatherOf Tom))))))
    (testing "a nested application normalizes innermost-first, cascading"
      ;; fatherOf(fatherOf(fatherOf(fatherOf Tom)))) -> grandfather_of(grandfather_of Tom)
      (is (= '(grandfather_of (grandfather_of Tom))
             (rw/normalize rules '(fatherOf (fatherOf (fatherOf (fatherOf Tom))))))))
    (testing "an already-normal term is unchanged"
      (is (= '(grandfather_of Tom) (rw/normalize rules '(grandfather_of Tom)))))
    (testing "a variable-bearing term normalizes too"
      (is (= '(grandfather_of ?y) (rw/normalize rules '(fatherOf (fatherOf ?y))))))
    (testing "an empty list is a term with no functor, and comes back as itself"
      ;; rebuilding it as `(apply list (first term) …)` would hand back `(nil)` — a term
      ;; nobody wrote, which then keys and matches as itself
      (is (= '() (rw/normalize rules '())))
      (is (= '(parent_chain ()) (rw/normalize-sentence rules '(parent_chain ())))))))

(deftest normalize-sentence-protects-the-predication
  (let [rules [{:lhs '(fatherOf (fatherOf ?x)) :rhs '(grandfather_of ?x)}]]
    (testing "each argument normalizes; the sentence functor is left alone"
      (is (= '(parent_chain (grandfather_of Tom))
             (rw/normalize-sentence rules '(parent_chain (fatherOf (fatherOf Tom)))))))
    (testing "a bare predication matching the rule shape is NOT rewritten"
      ;; (fatherOf (fatherOf Tom)) as a top-level fact keeps its predicate
      (is (= '(fatherOf (fatherOf Tom))
             (rw/normalize-sentence rules '(fatherOf (fatherOf Tom))))))
    (testing "no rules is a no-op"
      (is (= '(parent_chain (fatherOf (fatherOf Tom)))
             (rw/normalize-sentence [] '(parent_chain (fatherOf (fatherOf Tom)))))))))

(deftest normalize-sentence-leaves-an-equality-relation-as-written
  ;; An equality relation's arguments are mentions (`rw/equality-relations`), at the top
  ;; or nested, so the rewrite restates neither the relation nor what it relates.
  ;; `rule-applies?` reads the same positions, so a rule that normalizes nothing in the
  ;; sentence justifies no twin of it.
  (let [rule  {:lhs '(fatherOf (fatherOf ?x)) :rhs '(grandfather_of ?x)}
        rules [rule]]
    (doseq [s '[(not (equals (fatherOf (fatherOf Tom)) (grandfather_of Tom)))
                (equals (fatherOf (fatherOf Tom)) Bob)
                (not (sameAs Tom Bob))]]
      (testing (pr-str s)
        (is (= s (rw/normalize-sentence rules s)))
        (is (not (rw/rule-applies? rule s)))))
    (testing "a literal beside an equality literal still normalizes"
      (is (= '(implies (and (equals (fatherOf (fatherOf ?a)) ?b) (chain (grandfather_of ?a)))
                       (linked ?b))
             (rw/normalize-sentence
              rules
              '(implies (and (equals (fatherOf (fatherOf ?a)) ?b) (chain (fatherOf (fatherOf ?a))))
                        (linked ?b)))))
      (is (rw/rule-applies? rule '(and (equals Tom Bob) (chain (fatherOf (fatherOf Tom)))))))))

(deftest schematic-equation-detection
  (is (rw/schematic-equation? '(equals (fatherOf (fatherOf ?x)) (grandfather_of ?x))))
  (testing "not schematic: ground compound (reifies to symbols), symbol merge, sameAs"
    (is (not (rw/schematic-equation? '(equals (FruitFn AppleA) (FruitFn AppleB)))))
    (is (not (rw/schematic-equation? '(equals Obama BarackObama))))
    (is (not (rw/schematic-equation? '(sameAs (fatherOf ?x) (dadOf ?x)))))))

(deftest rule-applies-tracks-contribution
  (let [rule {:lhs '(fatherOf (fatherOf ?x)) :rhs '(grandfather_of ?x)}]
    (is (rw/rule-applies? rule '(parent_chain (fatherOf (fatherOf Tom)))))
    (is (not (rw/rule-applies? rule '(parent_chain (motherOf Tom)))))))

(deftest non-joining-pairs-surfaces-inter-rule-conflicts
  (let [r1 {:handle 1 :lhs '(f (f ?x)) :rhs '(g ?x)}
        r2 {:handle 2 :lhs '(f (f ?x)) :rhs '(h ?x)}   ; same LHS, different RHS → conflict
        p1 {:handle 3 :lhs '(p (p ?x)) :rhs '(q ?x)}]  ; disjoint predicates
    (testing "two rules disagreeing about a shared term are reported"
      (let [njs (rw/non-joining-pairs r2 [r1 r2])]
        (is (seq njs))
        (is (every? #(= 1 (:with %)) njs))
        (is (every? #(not= (:form-a %) (:form-b %)) njs))))
    (testing "disjoint rules overlap nowhere, so nothing is reported"
      (is (empty? (rw/non-joining-pairs p1 [r1 p1]))))
    (testing "a lone rule reports nothing — self-overlaps are excluded"
      (is (empty? (rw/non-joining-pairs r1 [r1]))))))

(deftest a-critical-pair-keeps-every-identification-the-unifier-made
  ;; `(h ?x ?x ?x ?y)` overlapping `(h ?u ?v ?w (g ?t))` identifies ?u, ?v and ?w with one
  ;; another, and the reducts have to say so.  A unifier reading a binding one hop deep
  ;; sees ?u's own binding as unbound and *overwrites* it rather than extending the chain,
  ;; which drops one identification: the reduct then carries a free variable where the
  ;; overlap says there is one term, and the pair is reported in a shape no term reaches.
  (let [r1    {:handle 1 :lhs '(h ?x ?x ?x ?y)      :rhs '(q ?x ?y)}
        r2    {:handle 2 :lhs '(h ?u ?v ?w (g ?t))  :rhs '(r ?u ?v ?w ?t)}
        pairs (rw/non-joining-pairs r1 [r1 r2])
        rs    (keep (fn [{:keys [form-a form-b]}]
                      (first (filter #(and (sequential? %) (= 'r (first %)))
                                     [form-a form-b])))
                    pairs)]
    (is (seq rs) "the two rules overlap, so the pair is reported")
    (doseq [[_ a b c] rs]
      (is (= a b c)
          (str "the three positions the overlap identifies are one variable: "
               (pr-str rs))))))

(deftest an-overlap-only-in-functor-position-is-not-a-critical-pair
  ;; `normalize` rebuilds a compound as `(apply list (first term) (map normalize (rest
  ;; term)))` — it descends into the arguments and never into the head — so a rule whose
  ;; LHS unifies with another's *functor* can never fire there, and a critical pair
  ;; reported over that overlap warns about a reduction the engine does not perform.
  (let [head-only {:handle 1 :lhs '((g ?x) ?y) :rhs '(one ?y)}
        inner     {:handle 2 :lhs '(g ?z)      :rhs '(two ?z)}
        arg       {:handle 3 :lhs '(f (g ?x))  :rhs '(three ?x)}]
    (testing "the overlap sits in functor position, so nothing is reported either way"
      (is (empty? (rw/non-joining-pairs head-only [head-only inner])))
      (is (empty? (rw/non-joining-pairs inner [head-only inner]))))
    (testing "the same two rules overlapping in an argument still report"
      ;; `(f (g ?x))` and `(g ?z)` overlap at argument 1, which `normalize` does reduce:
      ;; `(f (two ?x))` one way and `(three ?x)` the other, and those do not join
      (let [njs (rw/non-joining-pairs arg [arg inner])]
        (is (seq njs) "a real overlap is still a critical pair")
        (is (every? #(= 2 (:with %)) njs))))))
