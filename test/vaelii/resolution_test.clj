;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.resolution-test
  "Unification, backward + forward chaining, recursion detection, and
  dependency-directed retraction (with rules as sentexes)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb unification
  (is (= '{?x Muffet} (res/unify '(dog ?x) '(dog Muffet))))
  (is (nil? (res/unify '(dog ?x) '(cat Muffet))))
  (is (= 'Muffet (get (res/unify '(?r ?x ?y) '(parentOf Muffet Rex)) '?x))))

(deftest a-quoted-form-is-a-constant-to-unify-and-substitute
  (testing "a quoted form unifies with an equal form or a variable, and binds nothing inside"
    (is (= {} (res/unify '(Quote (dog ?x)) '(Quote (dog ?x)))))
    (is (nil? (res/unify '(Quote (dog ?x)) '(Quote (dog Muffet)))))
    (is (nil? (res/unify '(Quote (dog ?x)) '(Quote (dog ?y)))))
    (is (= '{?x (Quote (dog ?x))} (res/unify '?x '(Quote (dog ?x))))))
  (testing "substitute returns a quoted form whole"
    (is (= '(said Tom (Quote (dog ?x)))
           (res/substitute '(said Tom (Quote (dog ?x))) '{?x Muffet}))))
  (testing "an argument list headed by the symbol Quote is not a quoted form"
    (is (= '{?t expression} (res/unify-args '(Quote ?t) '(Quote expression))))
    (is (= '{?t expression} (res/unify '(result Quote ?t) '(result Quote expression))))))

(tu/deftest-kb backward-with-rule
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z) 'CxFam {:direction :forward})
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (v/assert kb (list parentOf bob ann) 'CxFam)
    (let [sols (v/prove kb (list grandparentOf '?g '?d) 'CxFam)]
      (testing "Tom is Ann's grandparent"
        (is (some (fn [b] (and (= tom (get b '?g)) (= ann (get b '?d)))) sols))))))

(tu/deftest-kb forward-chaining-derives
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z) 'CxFam {:direction :forward})
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (v/assert kb (list parentOf bob ann) 'CxFam)
    (testing "grandparent is materialized by forward chaining"
      (is (= 1 (count (v/sentexes-matching kb (list grandparentOf tom ann) 'CxFam))))
      (is (v/believed? kb (v/handle-of kb (list grandparentOf tom ann) 'CxFam))))))

(tu/deftest-kb recursion-is-bounded
  (let [nat (tu/tmp-type) z (tu/tmp-ind) succ (tu/tmp-pred)]
    (v/assert kb (list nat z) 'CxUniverse)
    (v/assert-rule kb [(list nat '?n)] (list nat (list succ '?n)) 'CxUniverse {:direction :forward :chain? false})
    (let [result (v/forward-chain kb {:max-depth 5})]
      (testing "productive recursion terminates at the depth bound and is flagged"
        (is (:truncated? result))
        (is (= 5 (:derived result)))
        (is (= 6 (count (v/sentexes-matching kb (list nat '?x) 'CxUniverse))))))))  ; Z plus 5 derived

(tu/deftest-kb retraction-saves-alternate-witness
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind) carol (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z) 'CxFam {:direction :forward})
    (v/assert kb (list parentOf tom bob)   'CxFam)
    (v/assert kb (list parentOf bob ann)   'CxFam)
    (v/assert kb (list parentOf tom carol) 'CxFam)
    (v/assert kb (list parentOf carol ann) 'CxFam)          ; two witnesses for (gp Tom Ann)
    (let [gp    (v/handle-of kb (list grandparentOf tom ann) 'CxFam)
          bob-h (v/handle-of kb (list parentOf tom bob) 'CxFam)]
      (is (v/believed? kb gp))
      (v/retract! kb bob-h)
      (testing "grandparent survives — re-derived via the Carol witness"
        (is (v/believed? kb gp))
        (is (seq (v/sentexes-matching kb (list grandparentOf tom ann) 'CxFam))))
      (testing "the retracted premise itself is gone"
        (is (empty? (v/sentexes-matching kb (list parentOf tom bob) 'CxFam)))))))

(tu/deftest-kb retraction-sweeps-solely-supported
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z) 'CxFam {:direction :forward})
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (v/assert kb (list parentOf bob ann) 'CxFam)            ; only one witness
    (let [gp     (v/handle-of kb (list grandparentOf tom ann) 'CxFam)
          bob-h  (v/handle-of kb (list parentOf tom bob) 'CxFam)
          result (v/retract! kb bob-h)]
      (testing "grandparent had no other support and is swept"
        (is (not (v/believed? kb gp)))
        (is (empty? (v/sentexes-matching kb (list grandparentOf tom ann) 'CxFam))))
      (testing "only the solely-supported records are removed"
        (is (= 2 (:removed-sentexes result)))             ; parent Tom Bob + grandparent
        (is (= 1 (:removed-justifications result))))           ; the grandparent justification
      (testing "the unrelated fact stays"
        (is (seq (v/sentexes-matching kb (list parentOf bob ann) 'CxFam)))))))
