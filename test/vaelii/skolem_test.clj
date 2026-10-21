;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.skolem-test
  "Head existentials and skolemization; see docs/skolem.md."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.skolem :as skolem]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private C 'CxUniverse)

(defn- witness
  "The skolem constant in the (single) believed match of `goal`, at argument `pos`."
  [kb goal pos]
  (let [ms (v/sentexes-matching kb goal C)]
    (when (seq ms) (nth (:sentence (first ms)) pos))))

(defn- exists-rule [kb pP qQ]
  (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C {:direction :forward}))

(tu/deftest-kb the-skolem-is-one-constant-per-antecedent-binding
  (tu/with-terms [pP qQ A A2]
    (exists-rule kb pP qQ)
    (v/assert kb (list pP A) C {:strength :monotonic})
    (let [k1 (witness kb (list qQ A '?w) 2)]
      (is (= 'SkolemFn (first (nat/nat-expression kb k1))) "K is a reified SkolemFn NAT")
      (testing "re-firing on the same binding reuses the one constant (fixpoint)"
        (v/forward-chain kb)
        (v/forward-chain kb)
        (is (not (:truncated? (:last (v/chain-stats kb)))))
        (is (= [k1] (map #(nth (:sentence %) 2) (v/sentexes-matching kb (list qQ A '?w) C)))))
      (testing "a different antecedent binding gets a distinct witness"
        (v/assert kb (list pP A2) C {:strength :monotonic})
        (let [k2 (witness kb (list qQ A2 '?w) 2)]
          (is (nat/reified-nat-symbol? k2))
          (is (not= k1 k2)))))))

(tu/deftest-kb each-existential-variable-gets-its-own-witness
  (tu/with-terms [pP qQ A]
    (v/assert-rule kb [(list pP '?x)] (list 'exists '[?y ?z] (list qQ '?x '?y '?z)) C {:direction :forward})
    (v/assert kb (list pP A) C {:strength :monotonic})
    (let [ky (witness kb (list qQ A '?y '?z) 2)
          kz (witness kb (list qQ A '?y '?z) 3)]
      (is (not= ky kz))
      (is (= [[0 A] [1 A]] (map #(drop 2 (nat/nat-expression kb %)) [ky kz]))
          "one existential index per marked variable, over the same frontier"))))

(tu/deftest-kb a-conjunctive-existential-head-shares-one-witness
  (tu/with-terms [pP qQ rR A]
    (v/assert-rule kb [(list pP '?x)]
                   (list 'exists '?y (list 'and (list qQ '?x '?y) (list rR '?y))) C {:direction :forward})
    (v/assert kb (list pP A) C {:strength :monotonic})
    (let [k-q (witness kb (list qQ A '?w) 2)]
      (is (nat/reified-nat-symbol? k-q))
      (is (= k-q (witness kb (list rR '?w) 1))))))

(tu/deftest-kb an-aggregate-output-is-not-part-of-the-frontier
  (tu/with-terms [node ancestorOf tally tallyOf A B]
    (v/assert-rule kb [(list node '?x) (list 'agg/count '?n '?a (list ancestorOf '?a '?x))]
                   (list 'exists '?y (list 'and (list tally '?x '?y) (list tallyOf '?y '?n)))
                   C {:direction :forward})
    (v/assert kb (list ancestorOf A B) C {:strength :monotonic})
    (v/assert kb (list node B) C {:strength :monotonic})
    (let [k (witness kb (list tally B '?w) 2)]
      (is (= [0 B] (drop 2 (nat/nat-expression kb k))) "keyed on ?x alone, not on ?n")
      (is (v/query? kb (list tallyOf k 1) C)))))

(tu/deftest-kb retracting-the-antecedent-drops-the-witness-and-its-nat
  (tu/with-terms [pP qQ A]
    (exists-rule kb pP qQ)
    (let [h (v/assert kb (list pP A) C {:strength :monotonic})
          k (witness kb (list qQ A '?w) 2)]
      (is (some? k))
      (v/retract! kb h)
      (is (empty? (v/sentexes-matching kb (list qQ A '?w) C)))
      (is (nil? (nat/nat-expression kb k)) "the skolem's natFormula is swept"))))

(tu/deftest-kb the-witness-is-a-function-of-the-rule-content
  (tu/with-terms [pP qQ likes Tom A]
    (let [hr (exists-rule kb pP qQ)]
      (v/assert kb (list pP A) C {:strength :monotonic})
      (let [k1 (witness kb (list qQ A '?w) 2)]
        ;; a premise about the witness keeps its natFormula alive across the retraction
        (v/assert kb (list likes Tom k1) C {:strength :monotonic})
        (v/retract! kb hr)
        (is (nil? (witness kb (list qQ A '?w) 2)) "the derived witness fell with its rule")
        (let [hr2 (exists-rule kb pP qQ)
              k2  (witness kb (list qQ A '?w) 2)]
          (is (not= hr hr2) "the re-asserted rule takes a new handle")
          (is (= k1 k2) "and mints the same witness")
          (is (v/query? kb (list likes Tom k2) C)))))))

(deftest the-rule-digest-ignores-ambient-print-settings
  (let [r1 {:antecedents '[(p ?x)] :consequent '(q ?x) :context 'C}
        r2 {:antecedents '[(r ?x)] :consequent '(s ?x) :context 'C}
        plain (#'skolem/rule-digest r1)]
    (binding [*print-level* 1 *print-length* 1]
      (is (= plain (#'skolem/rule-digest r1)))
      (is (not= (#'skolem/rule-digest r1) (#'skolem/rule-digest r2))))))

(tu/deftest-kb storing-a-wrapped-existential-rule-declares-skolemfn
  (tu/with-terms [pP qQ rR]
    (is (nil? (v/handle-of kb '(reifiable_function SkolemFn) C)))
    (v/assert kb (list 'exceptWhen (list rR '?x)
                       (list 'set/forwardRule
                             (list 'implies (list pP '?x) (list 'exists '?y (list qQ '?x '?y)))))
              C)
    (is (some? (v/handle-of kb '(reifiable_function SkolemFn) C)))))

(tu/deftest-kb a-backward-existential-rule-answers-with-a-fresh-variable
  (tu/with-terms [pP qQ A]
    (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C {:direction :backward})
    (v/assert kb (list pP A) C {:strength :monotonic})
    (let [answers (v/prove kb (list qQ A '?m) C)]
      (is (= 1 (count answers)))
      (is (sx/variable? (get (first answers) '?m))))))
