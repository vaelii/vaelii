;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.direction-test
  "Directed rules via the set/forwardRule, set/backwardRule, set/inertRule virtual
  predicates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb forward-rule-materializes
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/forwardRule ancestor-rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "a forward rule forward-chains its consequent"
      (is (seq (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam))))))

(tu/deftest-kb backward-rule-does-not-materialize-but-proves
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/backwardRule ancestor-rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "a backward rule is not forward-materialized"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam))))
    (testing "but it answers backward queries"
      (is (v/provable? kb (list ancestorOf tom bob) 'CxFam)))))

(tu/deftest-kb inert-rule-is-documentation-only
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/inertRule ancestor-rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "an inert rule drives no inference"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam)))
      (is (not (v/provable? kb (list ancestorOf tom bob) 'CxFam))))
    (testing "but the rule sentex is stored and findable by its terms"
      (is (= 1 (count (v/find-sentexes kb ancestorOf)))))
    ;; Documentation is only documentation if it is *there*: believed like any other
    ;; rule, and posted under its predicates so a browser and a term search find it.
    ;; Not firing is the direction's doing, not an absence of either of those — which
    ;; is what separates this from `assert-inert`, whose sentex nothing believes
    ;; (docs/inference.md, "An inert rule is documentation with a handle").
    (let [h (v/handle-of kb (list 'set/inertRule ancestor-rule) 'CxFam)]
      (testing "the rule is believed, at an ordinary class — there is no :inert strength"
        (is (v/in? kb h))
        (is (= :default (:strength (v/sentex kb h))))
        (is (= :default (v/defeat-class kb h)))
        (is (= :inert (:direction (v/sentex kb h)))))
      (testing "and it is indexed both ways, which is what makes it browsable"
        (is (contains? (set (p/rules-by-consequent (:index kb) ancestorOf)) h))
        (is (contains? (set (p/rules-by-antecedent (:index kb) parentOf)) h))))))

(tu/deftest-kb a-transitivity-rule-is-written-down-inert-while-the-closure-answers
  ;; The pattern `docs/taxonomy.md` describes: transitivity is not run as a rule — the
  ;; closure answers it — so the rule is written down inert, where a reader looks for it.
  ;; The closure keeps answering with the rule sitting there, and the rule adds no
  ;; derived sentex of its own: asserting it bare would materialize one per pair.
  (tu/with-terms [animal_ dog_ terrier_ Rex]
    (let [rule (vr/rule-sentence [(list 'genl '?a '?b) (list 'genl '?b '?c)]
                                 (list 'genl '?a '?c))]
      (v/assert kb (list 'set/inertRule rule) 'CxUniverse)
      (v/assert kb (list 'genl terrier_ dog_) 'CxUniverse)
      (v/assert kb (list 'genl dog_ animal_) 'CxUniverse)
      (v/assert kb (list terrier_ Rex) 'CxUniverse)
      (testing "the closure answers the transitive question the rule describes"
        (is (v/genl? kb terrier_ animal_))
        ;; ...and a query at the supertype reaches the instance through it.  `ask`, not
        ;; `sentexes-matching`: the closure is answered on demand and stores no edge, so
        ;; there is no `(animal Rex)` sentex to match — which is the whole design.
        (is (v/provable? kb (list animal_ Rex) 'CxUniverse))
        (is (= [{'?w Rex}] (v/ask kb (list animal_ '?w) 'CxUniverse))))
      (testing "while the rule itself derives nothing"
        (is (empty? (v/sentexes-matching kb (list 'genl terrier_ animal_)
                                         'CxUniverse))
            "no materialized (genl terrier animal) — the closure is not a stored edge")))))

(tu/deftest-kb direction-via-opts
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'CxFam {:direction :backward})
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing ":direction opt matches the virtual-predicate behavior"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam)))
      (is (v/provable? kb (list ancestorOf tom bob) 'CxFam)))))

(tu/deftest-kb assert-rule-takes-every-direction-its-docstring-names
  ;; `:both` is `:forward`'s class (docs/inference.md), so it stores the rule `:forward`
  ;; stores; `assert-rule` wraps the sentence and must not also hand `assert` the opt.
  (doseq [d [:forward :backward :inert :both]]
    (let [p (tu/tmp-pred) q (tu/tmp-pred) a (tu/tmp-ind)
          h (v/assert-rule kb [(list p '?x)] (list q '?x) 'CxFam {:direction d})]
      (v/assert kb (list p a) 'CxFam)
      (testing (str d)
        (is (= (if (= :both d) :forward d) (:direction (v/sentex kb h))))
        (is (= (contains? #{:forward :both} d)
               (some? (v/handle-of kb (list q a) 'CxFam))))))))

(tu/deftest-kb bare-rule-is-backward-by-default
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb rule 'CxFam)                                  ; a bare implies
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "a bare rule is backward by default — it does not forward-materialize"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam)))
      (is (= :backward (:direction (v/sentex kb (v/handle-of kb rule 'CxFam))))))
    (testing "but it still answers backward queries"
      (is (v/provable? kb (list ancestorOf tom bob) 'CxFam)))))

(tu/deftest-kb forward-only-rule-forward-chains-but-is-not-backward-usable
  ;; The fourth direction, a tests-only mode: set/forwardOnlyRule forward-chains like
  ;; set/forwardRule but is never used in backward proof.  The shipped ontology uses
  ;; set/forwardRule (forward + backward), never this.
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/forwardOnlyRule rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (let [sx (v/sentex kb (v/handle-of kb (list 'set/forwardOnlyRule rule) 'CxFam))]
      (testing "the record carries :forward-only"
        (is (= :forward-only (:direction sx))))
      (testing "it forward-chains its consequent, like a forward rule"
        (is (seq (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam))))
      (testing "the chainers read it forward-capable but not backward-capable"
        (is (vr/forward-sentex? sx))
        (is (not (vr/backward-sentex? sx)))))))
