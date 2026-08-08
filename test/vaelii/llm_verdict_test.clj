;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.llm-verdict-test
  "The four-axis reading of a proposed batch (`vaelii.impl.llm.verdict`) — what the KB
  refuses, what shape a line should have been in, what vocabulary it invents, and what
  the engine could not decide.

  No model anywhere: a verdict is computed from a batch, and a batch is data."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.llm.verdict :as verdict]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

;; the corrections read the shipped schema — argIsa constraints, declared arities, the
;; genl edges that decide what is a type — so the starter is the fixture
(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- verdict-for [kb sentence]
  (first (verdict/verdicts kb {:add [[sentence 'OrganismContext]] :remove []})))

;; ---- the four axes, one at a time ---------------------------------------

(tu/deftest-kb a-line-the-kb-would-take-as-written-is-ok
  (let [v (verdict-for kb '(genl penguin bird))]
    (is (= :ok (:verdict v)))
    (is (empty? (:problems v)))
    (is (nil? (:correction v)))
    (is (empty? (:coined v)))))

(tu/deftest-kb a-refusal-arrives-typed-not-as-a-message
  (let [v (verdict-for kb '(genl penguin Muffet))]
    (is (= :refused (:verdict v)))
    (testing "the type is the keyword `assert` would have thrown"
      (is (= :not-well-formed (:type (first (:problems v))))))
    (testing "and the message rides along for the reader who opens it"
      (is (string? (:message (first (:problems v))))))))

(tu/deftest-kb a-claim-about-a-type-symbol-is-corrected-not-refused
  (let [v (verdict-for kb '(mortal penguin))]
    (testing "the KB would store it — nothing in the check chain sees this"
      (is (empty? (:problems v))))
    (testing "but the shape is wrong, and the correction says which shape it wants"
      (is (= :unary-on-type (:rule (:correction v))))
      (is (= '(set/defaultRule (implies (penguin ?x) (mortal ?x))) (:to (:correction v)))))
    (testing "with the definitional reading offered as the alternative"
      (is (= ['(genl penguin mortal)] (:alternatives (:correction v)))))))

(tu/deftest-kb coined-vocabulary-is-split-by-what-it-risks
  (testing "a one-place claim coins a property"
    (tu/with-terms [swims]
      (let [v (verdict-for kb (list 'implies '(penguin ?x) (list swims '?x)))]
        (is (= :coins (:verdict v)))
        (is (= [:property] (map :kind (:coined v))))
        (is (= [1] (map :arity (:coined v)))))))
  (testing "an n-place one coins a relation — a different judgement, so a different chip"
    (tu/with-terms [hunts]
      (let [v (verdict-for kb (list 'implies '(penguin ?x) (list hunts '?x 'Antarctica)))]
        (is (= :coins (:verdict v)))
        (is (= [:relation] (map :kind (:coined v))))))))

(tu/deftest-kb an-undecidable-rewrite-is-uncertain-rather-than-silently-chosen
  ;; `partOf` constrains both positions to the same type, so the argument order carries
  ;; no signal and the lift's direction is the author's call
  (let [v (verdict-for kb '(partOf penguin wing))]
    (is (= :relation-on-types (:rule (:correction v))))
    (is (= :low (:confidence (:correction v))))
    (is (= :uncertain (:verdict v))
        "a rewrite the engine cannot decide outranks the vocabulary it would coin")))

;; ---- the axes are independent, and the verdict is the worst of them -----

(tu/deftest-kb the-verdict-is-the-worst-thing-true-of-the-line
  (testing "refused outranks everything — a line the KB will not take is not a naming question"
    (tu/with-terms [wobbles]
      (let [v (verdict-for kb (list wobbles '?x))]           ; non-ground fact
        (is (= :refused (:verdict v)))
        (is (seq (:coined v)) "and the coining is still reported beside it"))))
  (testing "coins outranks ok"
    (tu/with-terms [waddles]
      (is (= :coins (:verdict (verdict-for kb (list 'implies '(penguin ?x)
                                                    (list waddles '?x))))))))
  (testing "every axis is reported whatever the verdict — ranking is for attention"
    (let [v (verdict-for kb '(mortal penguin))]
      (is (contains? v :problems))
      (is (contains? v :correction))
      (is (contains? v :coined)))))

;; ---- the batch shape ----------------------------------------------------

(tu/deftest-kb verdicts-line-up-with-the-batch-by-index
  (let [batch {:add [['(genl penguin bird) 'OrganismContext]
                     ['(mortal penguin) 'OrganismContext]
                     ['(genl penguin Muffet) 'OrganismContext]]
               :remove []}
        vs (verdict/verdicts kb batch)]
    (is (= [0 1 2] (map :index vs)))
    (is (= [:ok :ok :refused] (map :verdict vs))
        "a rewrite the engine is sure of does not demote the line — the chip says it")
    (is (= :unary-on-type (:rule (:correction (second vs))))
        "and the correction is still there to be rendered")
    (is (= (map first (:add batch)) (map :sentence vs)))
    (is (= ['OrganismContext 'OrganismContext 'OrganismContext] (map :context vs)))))

(tu/deftest-kb a-precomputed-check-is-used-rather-than-repeated
  (let [batch {:add [['(genl penguin Muffet) 'OrganismContext]] :remove []}
        ;; the caller's own check-edit result, handed in the way `propose-page` hands
        ;; back its `:rejections`
        problems (v/check-edit kb batch)
        vs (verdict/verdicts kb batch {:problems problems})]
    (is (= :refused (:verdict (first vs))))
    (is (= (map :type problems) (map :type (:problems (first vs)))))))

(tu/deftest-kb the-summary-names-every-verdict-even-at-zero
  (let [vs (verdict/verdicts kb {:add [['(genl penguin bird) 'OrganismContext]] :remove []})
        s  (verdict/summary vs)]
    (is (= #{:refused :uncertain :coins :ok} (set (keys s))))
    (is (= 1 (:ok s)))
    (is (= 0 (:refused s)) "a fixed row of counts, so nothing shifts as a batch changes")))

(tu/deftest-kb an-empty-batch-has-no-verdicts-and-does-not-throw
  (is (= [] (verdict/verdicts kb {:add [] :remove []})))
  (is (= {:refused 0 :uncertain 0 :coins 0 :ok 0} (verdict/summary []))))

(tu/deftest-kb nothing-here-writes
  (let [before (tu/sentex-ids kb)]
    (verdict/verdicts kb {:add [['(mortal penguin) 'OrganismContext]
                                ['(genl penguin Muffet) 'OrganismContext]]
                          :remove []})
    (is (= before (tu/sentex-ids kb)) "a verdict is a reading of a proposal")))
