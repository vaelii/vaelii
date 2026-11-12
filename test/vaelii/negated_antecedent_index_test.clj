;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negated-antecedent-index-test
  "A negated antecedent `(not (p ?x))` files under `[:not p]` in the antecedent index
  (`rules/antecedent-key`), and a negative datum triggers through that one key
  (`rules/trigger-keys`): an arriving `(not (p a))` reaches the rules negated on `p`
  rather than every rule with a negated antecedent anywhere.  Both sides spell the key
  the same way, the rebuilt index spells it the same way, and the firing, its
  retraction and its arrival-order independence are what the spelling has to keep."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest the-key-is-the-negated-body's-predicate
  (is (= 'flies (rules/antecedent-key '(flies ?x))))
  (is (= [:not 'flies] (rules/antecedent-key '(not (flies ?x)))))
  (is (= ['bird [:not 'flies]]
         (vec (rules/antecedent-predicates
               '(implies (and (bird ?x) (not (flies ?x))) (grounded ?x)))))))

(deftest the-dependency-spelling-is-the-one-a-conclusion-is-filed-under
  ;; The index key and the graph key part company on a negation, and only there: a
  ;; conclusion `(not (flies ?x))` is filed under its outermost functor, so a reader looking a
  ;; dependency up among the concluders has to ask for `not`.
  (is (= 'not (rules/consequent-predicate '(implies (bird ?x) (not (flies ?x))))))
  (is (= ['bird 'not]
         (vec (rules/dependency-predicates
               '(implies (and (bird ?x) (not (flies ?x))) (grounded ?x))))))
  (testing "a rule with no negated antecedent spells both the same way"
    (let [s '(implies (and (bird ?x) (winged ?x)) (grounded ?x))]
      (is (= (vec (rules/antecedent-predicates s))
             (vec (rules/dependency-predicates s)))))))

(tu/deftest-kb a-negated-antecedent-rule-fires-in-either-arrival-order
  (tu/with-terms [bird flies grounded other Tweety Opus CxNeg]
    (let [rh (v/assert-rule kb [(list bird '?x) (list 'not (list flies '?x))]
                            (list grounded '?x) CxNeg {:direction :forward})]
      (testing "the rule is posted under its body's predicate, not under the bare not"
        (is (contains? (set (reads/as-stored-rules-by-antecedent-global (:index kb) [:not flies])) rh))
        (is (not (contains? (set (reads/as-stored-rules-by-antecedent-global (:index kb) 'not)) rh)))
        (is (contains? (set (reads/as-stored-rules-by-antecedent-global (:index kb) bird)) rh)))
      (testing "negation last: the negative datum is the trigger"
        (v/assert kb (list bird Tweety) CxNeg)
        (let [nh (v/assert kb (list 'not (list flies Tweety)) CxNeg)]
          (is (v/ask? kb (list grounded Tweety) CxNeg))
          (testing "retracting the negation withdraws the conclusion"
            (v/retract! kb nh)
            (is (not (v/ask? kb (list grounded Tweety) CxNeg))))))
      (testing "negation first: the positive datum is the trigger and the join reads it"
        (v/assert kb (list 'not (list flies Opus)) CxNeg)
        (v/assert kb (list bird Opus) CxNeg)
        (is (v/ask? kb (list grounded Opus) CxNeg)))
      (testing "a negation on another predicate finds no rule under its key"
        (v/assert kb (list 'not (list other Tweety)) CxNeg)
        (is (empty? (reads/as-stored-rules-by-antecedent-global (:index kb) [:not other])))
        (is (v/ask? kb (list grounded Opus) CxNeg))))))

(deftest reindex-rebuilds-the-negated-antecedent-key
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (tu/with-terms [bird flies grounded Tweety]
      (let [rh (v/assert-rule kb [(list bird '?x) (list 'not (list flies '?x))]
                              (list grounded '?x) 'CxUniverse {:direction :forward})]
        (v/assert kb (list bird Tweety) 'CxUniverse)
        (v/assert kb (list 'not (list flies Tweety)) 'CxUniverse)
        (is (v/ask? kb (list grounded Tweety) 'CxUniverse))
        (p/clear-index! (:index kb))
        (reindex/reindex kb)
        (v/recover kb)
        (testing "the rebuilt index files the rule under the same key the live one did"
          (is (contains? (set (reads/as-stored-rules-by-antecedent-global (:index kb) [:not flies])) rh))
          (is (empty? (reads/as-stored-rules-by-antecedent-global (:index kb) 'not))))
        (testing "and the conclusion is back"
          (is (v/ask? kb (list grounded Tweety) 'CxUniverse)))))))
