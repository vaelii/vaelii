;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.dot-test
  "Dotted rest patterns, `(?pred . ?args)`: unification and substitution, and the same
  patterns as goals, rule literals and index content in a KB."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(deftest dotted-unify
  (testing "a dotted rest-pattern binds the tail as a list"
    (is (= '{?pred parentOf ?args (Tom Bob)}
           (res/unify '(?pred . ?args) '(parentOf Tom Bob))))
    (is (= '{?a X ?rest (Y Z)}
           (res/unify '(foo ?a . ?rest) '(foo X Y Z))))
    (is (= '{?pred flies ?args (Tweety)}
           (res/unify '(?pred . ?args) '(flies Tweety)))))
  (testing "the empty tail binds to ()"
    (is (= '{?pred thing ?args ()}
           (res/unify '(?pred . ?args) '(thing)))))
  (testing "the dotted pattern binds the same on the right of the unification"
    (is (= '{?pred parentOf ?args (Tom Bob)}
           (res/unify '(parentOf Tom Bob) '(?pred . ?args))))))

(deftest a-dot-outside-the-rest-shape-binds-no-rest
  (testing "a `.` with no rest variable after it binds nothing"
    (is (nil? (res/unify '(p .) '(p X))))
    (is (nil? (res/unify '(p X) '(p .))))
    (is (nil? (res/unify '(p A .) '(p A B)))))
  (testing "a `.` followed by a constant or by two terms is not a rest marker"
    (is (nil? (res/unify '(p . A) '(p A))))
    (is (nil? (res/unify '(p . ?a ?b) '(p X Y))))))

(deftest two-dotted-patterns-unify-rest-with-rest
  (is (= '{?a ?b} (res/unify '(p . ?a) '(p . ?b))))
  (is (= '(p X . ?a)
         (res/substitute '(p . ?b) (res/unify '(p X . ?a) '(p . ?b)))))
  (is (= '(p X Y)
         (res/substitute '(p ?x . ?a) (res/unify '(p ?x . ?a) '(p X . ?b) '{?b (Y)})))))

(deftest dotted-substitute-splices
  (is (= '(parentOf Tom Bob)
         (res/substitute '(?pred . ?args) '{?pred parentOf ?args (Tom Bob)})))
  (testing "nested inside another form"
    (is (= '(ist CxUniverse (parentOf Tom Bob))
           (res/substitute '(ist CxUniverse (?pred . ?args))
                           '{?pred parentOf ?args (Tom Bob)}))))
  (testing "a `.` outside the rest shape splices nothing"
    (is (= '(p .) (res/substitute '(p .) {})))
    (is (= '(p X . A) (res/substitute '(p ?x . A) '{?x X})))))

(deftest ordinary-unify-unaffected
  (is (= '{?x B} (res/unify '(a ?x c) '(a B c))))
  (is (nil? (res/unify '(a b) '(a c))))
  (is (= {} (res/unify '(a b) '(a b)))))

(deftest occurs-check-rejects-a-cyclic-binding
  (testing "a variable cannot be bound to a term that contains it"
    (is (nil? (res/unify '?x '(f ?x))) "direct occurrence")
    (is (nil? (res/unify '(f ?x) '(f (g ?x)))) "nested occurrence")
    (is (nil? (res/unify '?x '(f (g (h ?x))))) "deeply nested"))
  (testing "an occurrence reached through an existing binding is caught too"
    ;; unifying ?x with ?y where ?y is already bound to (f ?x) is the same cycle
    (is (nil? (res/unify '?x '?y '{?y (f ?x)}))))
  (testing "binding a variable to itself is identity, not a cycle"
    (is (= {} (res/unify '?x '?x))))
  (testing "a variable binding to a term that does NOT contain it still succeeds"
    (is (= '{?x (f ?y)} (res/unify '?x '(f ?y))))
    ;; the binding is stored unsubstituted; substitute resolves ?y -> a later
    (is (= '{?y a ?x (g ?y)} (res/unify '?x '(g ?y) '{?y a})))))

;; ---- in a KB ---------------------------------------------------------------

(tu/deftest-kb a-dotted-goal-binds-the-rest-of-a-stored-fact
  (tu/with-terms [parentOf Tom Ann CxFam]
    (v/assert kb (list parentOf Tom Ann) CxFam)
    (is (= [{'?args (list Tom Ann)}] (v/query kb (list parentOf '. '?args) CxFam)))
    (is (= [{'?r (list Ann)}] (v/query kb (list parentOf Tom '. '?r) CxFam)))
    (is (= [{'?x Tom '?r (list Ann)}] (v/query kb [(list parentOf '?x '. '?r)] CxFam)))
    (is (empty? (v/query kb (list parentOf Tom Ann Ann '. '?r) CxFam))
        "more positional arguments than the fact holds")))

(tu/deftest-kb a-goal-with-a-dot-outside-the-rest-shape-is-refused
  (doseq [[label read] [["query" #(v/query kb % 'CxUniverse)]
                        ["ask?" #(v/ask? kb % 'CxUniverse)]
                        ["prove" #(v/prove kb % 'CxUniverse)]
                        ["sentexes-matching" #(v/sentexes-matching kb % 'CxUniverse)]]
          goal  ['(unary_predicate .) '(parentOf ?x . Tom) '(parentOf ?x (ListFn .))]]
    (testing (str label " " (pr-str goal))
      (is (= :shape (tu/refusal-type #(read goal))))))
  (testing "as a conjunct of a vector goal"
    (is (= :shape (tu/refusal-type #(v/query kb '[(dog ?x) (unary_predicate .)] 'CxUniverse))))))

(tu/deftest-kb the-rest-marker-is-not-a-term
  (testing "the starter's dotted rules put no `.` in the vocabulary"
    (is (not-any? #{'.} (v/terms kb))))
  (testing "so the integrity sweep reports no `.`"
    (is (= :audited (:status (v/kb-integrity kb #{'.} 'CxUniverse))))))

(tu/deftest-kb a-dotted-rule-concludes-forward-and-backward
  (tu/with-terms [parentOf ancestorOf Tom Ann CxFwd CxBwd]
    (let [rule (list 'implies (list parentOf '?x '. '?rest) (list ancestorOf '?x '. '?rest))]
      (doseq [[ctx direction] [[CxFwd 'set/forwardRule] [CxBwd 'set/backwardRule]]]
        (testing (str direction)
          (v/assert kb (list direction rule) ctx)
          (v/assert kb (list parentOf Tom Ann) ctx)
          (is (= [{'?x Tom}] (v/query kb (list ancestorOf '?x Ann) ctx {:max-depth 2})))
          (is (= #{{'?x Tom}} (set (v/prove kb (list ancestorOf '?x Ann) ctx))))
          (is (= [{'?r (list Ann)}] (v/query kb (list ancestorOf Tom '. '?r) ctx {:max-depth 2}))))))))

(tu/deftest-kb a-dotted-literal-of-a-fixed-arity-predicate-holds-no-argument-at-the-dot
  (tu/with-terms [parentOf person_kind noted_kind]
    (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 2 person_kind) 'CxUniverse)
    (is (nil? (tu/write-conviction
               kb (list 'set/forwardRule
                        (list 'implies (list parentOf '?x '. '?r) (list noted_kind '?x)))
               'CxUniverse))
        "`.` and the rest variable are not arguments 2 and 3")))

(tu/deftest-kb a-sentence-with-a-dot-outside-the-rest-shape-is-refused
  (tu/with-terms [parentOf noted_kind Tom Bob CxFam]
    (let [in-rule #(list 'set/forwardRule
                         (list 'implies (list 'and (list noted_kind '?x) %) (list noted_kind '?x)))]
      (doseq [s      [(list parentOf Tom '.)
                      (list parentOf Tom '. Bob)
                      (in-rule (list parentOf '?x '.))
                      (in-rule (list parentOf '?x '. '?a '?b))
                      (in-rule (list parentOf '?x (list 'ListFn '.)))]
              naming [:strict :warn :off]
              :let   [kb (assoc kb :naming naming)]]
        (testing (str naming " " (pr-str s))
          (is (= :shape (tu/refusal-type #(v/assert kb s CxFam))))
          (is (= :shape (tu/refusal-type #(v/assert-inert kb s CxFam))))
          (is (= [:shape] (mapv :type (v/check kb s CxFam)))))))
    (testing "a rest pattern stated as a fact is open"
      (is (= :not-ground (tu/refusal-type #(v/assert kb (list parentOf Tom '. '?r) CxFam)))))))
