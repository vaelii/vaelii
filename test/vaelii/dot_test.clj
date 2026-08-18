;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.dot-test
  "Dotted rest-pattern unification and substitution — `(?pred . ?args)`."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.resolution :as res]))

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
           (res/unify '(?pred . ?args) '(thing))))))

(deftest dotted-substitute-splices
  (is (= '(parentOf Tom Bob)
         (res/substitute '(?pred . ?args) '{?pred parentOf ?args (Tom Bob)})))
  (testing "nested inside another form"
    (is (= '(ist CxUniverse (parentOf Tom Bob))
           (res/substitute '(ist CxUniverse (?pred . ?args))
                           '{?pred parentOf ?args (Tom Bob)})))))

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
