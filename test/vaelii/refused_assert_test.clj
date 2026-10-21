;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.refused-assert-test
  "A refused `assert` leaves the KB as the call found it.

  `assert` writes before some of the checks that refuse it: a ground reifiable NAT is
  minted, a head existential declares `SkolemFn`, and the sentence is stored and chained
  before an `exceptWhen` query evaluated as a rule fires can refuse.  Each test here
  builds the pre-state, snapshots it, makes the refused call, and compares: the stored
  handles, the justifications, the premise marks and what is believed are what they were.
  Where `check` can predict the refusal, it names the same `:type`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.types.dense-roots :as dense-roots-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- state
  "What a refused call must leave as it was: the three record sets `tu/baseline` reads,
  and the handles believed."
  [kb]
  (let [b (tu/baseline kb)]
    (assoc b :believed (into #{} (filter #(v/in? kb %)) (:sentexes b)))))

(defn- refusal-type
  "The `:type` `assert` throws for `sentence`, or `:stored` when it does not throw."
  ([kb sentence context] (refusal-type kb sentence context nil))
  ([kb sentence context opts]
   (try (v/assert kb sentence context opts) :stored
        (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))

(defn- refused-leaves-nothing
  "Assert `sentence`, expecting it refused with `expected`, and check the KB is the
  state it was before the call."
  ([kb sentence context expected] (refused-leaves-nothing kb sentence context nil expected))
  ([kb sentence context opts expected]
   (let [before (state kb)]
     (is (= expected (refusal-type kb sentence context opts)))
     (let [after (state kb)]
       (is (= before after)
           (str "the refused call left "
                (pr-str (mapv #(v/sentence-of (v/sentex kb %))
                              (remove (:sentexes before) (:sentexes after))))))))))

(defn- checked-types [kb sentence context]
  (into #{} (map :type) (v/check kb sentence context)))

;; ---- an inline exceptWhen, refused per stored form ----------------------------

(tu/deftest-kb an-exception-one-alternative-leaves-open-stores-no-rule
  ;; the exception's variable is bound in one DNF alternative only: the rule stored for
  ;; the other alternative would read an unbound ?y
  (tu/with-terms [bird robin flier sick friendOf Tweety Rob]
    (v/assert kb (list bird Tweety) 'CxUniverse)
    (v/assert kb (list robin Rob) 'CxUniverse)
    (let [s (list 'exceptWhen (list sick '?y)
                  (list 'set/forwardRule
                        (list 'implies (list 'or (list 'and (list bird '?x) (list friendOf '?x '?y))
                                             (list robin '?x))
                              (list flier '?x))))]
      (testing "check predicts the refusal"
        (is (= #{:exception-not-closed} (checked-types kb s 'CxUniverse))))
      (refused-leaves-nothing kb s 'CxUniverse :exception-not-closed)
      (is (empty? (v/ask kb (list flier '?x) 'CxUniverse)) "and no rule fired"))))

(tu/deftest-kb an-exception-over-a-fact-is-refused-as-not-well-formed
  (tu/with-terms [dog sick Fido Rex]
    (v/assert kb (list dog Rex) 'CxUniverse)
    (doseq [target [(list dog Fido) (list dog Rex) (list 'set/forwardRule (list dog Fido))]]
      (let [s (list 'exceptWhen (list sick Fido) target)]
        (testing (pr-str target)
          (is (= #{:not-well-formed} (checked-types kb s 'CxUniverse)) "check predicts it")
          (refused-leaves-nothing kb s 'CxUniverse :not-well-formed))))))

(tu/deftest-kb an-exception-closing-a-cycle-under-one-conjunct-stores-no-rule
  ;; the conjunctive consequent is stored as one rule per conjunct, and the (q ?x) rule
  ;; with the exception on (e ?x) closes q -> e -| q
  (tu/with-terms [a b q e A]
    (v/assert kb (list 'set/forwardRule (list 'implies (list q '?x) (list e '?x))) 'CxUniverse)
    (v/assert kb (list a A) 'CxUniverse)
    (let [s (list 'exceptWhen (list e '?x)
                  (list 'set/forwardRule
                        (list 'implies (list a '?x) (list 'and (list b '?x) (list q '?x)))))]
      (testing "check predicts the refusal"
        (is (= #{:not-stratified} (checked-types kb s 'CxUniverse))))
      (refused-leaves-nothing kb s 'CxUniverse :not-stratified))))

;; ---- a NAT minted before the check that refuses ---------------------------------

(defn- fruit-schema!
  [kb FruitFn fruit edible]
  (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
  (v/assert kb (list 'genl fruit 'thing) 'CxUniverse)
  (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
  (v/assert kb (list 'set/forwardRule (list 'implies (list fruit '?x) (list edible '?x))) 'CxUniverse))

(defn- stone-schema!
  "`(arg tintOf 2 color)` over a `Stone` held by a type disjoint from `color`, so a
  `tintOf` fact naming `Stone` is refused as `:arg-type` under the constraint reading."
  [kb tintOf color rock Stone]
  (v/assert kb (list 'genl color 'thing) 'CxUniverse)
  (v/assert kb (list 'genl rock 'thing) 'CxUniverse)
  (v/assert kb (list 'disjoint color rock) 'CxUniverse)
  (v/assert kb (list rock Stone) 'CxUniverse)
  (v/assert kb (list 'arg tintOf 2 color) 'CxUniverse))

(tu/deftest-kb a-sentence-refused-after-its-nat-was-minted-leaves-no-mint
  (tu/with-terms [FruitFn fruit edible hueOf tintOf color rock AppleTree Red Stone]
    (fruit-schema! kb FruitFn fruit edible)
    (stone-schema! kb tintOf color rock Stone)
    (testing "an argument-type refusal"
      (tu/without-entailing
       (refused-leaves-nothing kb (list tintOf (list FruitFn AppleTree) Stone) 'CxUniverse
                               :arg-type)))
    (testing "a non-ground fact"
      (refused-leaves-nothing kb (list hueOf (list FruitFn AppleTree) '?c) 'CxUniverse :not-ground))
    (testing "an option refused after the mint"
      (refused-leaves-nothing kb (list hueOf (list FruitFn AppleTree) Red) 'CxUniverse
                              {:direction :backward} :unknown-option))
    (testing "no natFormula names the application"
      (is (empty? (v/sentexes-matching kb (list 'natFormula '?k (list FruitFn AppleTree))
                                       'CxUniverse))))))

(tu/deftest-kb a-context-nat-minted-for-a-refused-sentence-is-taken-back
  (tu/with-terms [CxTimeFn CxMonad Day Rex]
    (v/assert kb (list 'result CxTimeFn 'context) 'CxUniverse)
    (refused-leaves-nothing kb (list 'Bad_Pred Rex) (list CxTimeFn CxMonad Day) :naming)))

(tu/deftest-kb a-nat-whose-result-type-misses-the-demand-is-refused-alike
  ;; the constraint reading, where the declaration convicts the constant for its result
  ;; type; the entailing one mints `(dog …)` beside `(fruit …)` and stores the clash
  (tu/with-terms [FruitFn fruit dog ownsDog AppleTree Bob]
    (doseq [s [(list 'genl fruit 'thing) (list 'genl dog 'thing) (list 'disjoint fruit dog)
               (list 'reifiable_function FruitFn) (list 'result FruitFn fruit)
               (list 'arg ownsDog 2 dog)]]
      (v/assert kb s 'CxUniverse))
    (let [s (list ownsDog Bob (list FruitFn AppleTree))]
      (tu/without-entailing
       (testing "check names the type assert throws"
         (is (= #{:arg-type} (checked-types kb s 'CxUniverse))))
       (refused-leaves-nothing kb s 'CxUniverse :arg-type)))))

(tu/deftest-kb a-nat-whose-result-type-the-entailment-extends-is-admitted-by-both
  ;; `fruit` does not reach `food` and is not disjoint from it, so the mint's constant
  ;; takes `food` by entailment and assert stores the fact: check says the same, before
  ;; the mint and after it
  (tu/with-terms [FruitFn fruit food ownsFood AppleTree Bob Ann]
    (doseq [s [(list 'genl fruit 'thing) (list 'genl food 'thing)
               (list 'reifiable_function FruitFn) (list 'result FruitFn fruit)
               (list 'arg ownsFood 2 food)]]
      (v/assert kb s 'CxUniverse))
    (tu/with-entailing
      (is (= [] (v/check kb (list ownsFood Bob (list FruitFn AppleTree)) 'CxUniverse)))
      (is (= :stored (refusal-type kb (list ownsFood Bob (list FruitFn AppleTree)) 'CxUniverse)))
      (is (= [] (v/check kb (list ownsFood Ann (list FruitFn AppleTree)) 'CxUniverse))))))

(tu/deftest-kb a-listener-hears-nothing-of-a-refused-mint
  (tu/with-terms [FruitFn fruit edible tintOf color rock AppleTree Stone]
    (fruit-schema! kb FruitFn fruit edible)
    (stone-schema! kb tintOf color rock Stone)
    (let [events (atom [])
          token  (v/watch kb #(swap! events conj %))]
      (try
        (is (= :arg-type (tu/without-entailing
                          (refusal-type kb (list tintOf (list FruitFn AppleTree) Stone) 'CxUniverse))))
        (is (= [] @events) "the mint's settle is held and its handles are gone")
        (finally (v/unwatch kb token))))))

;; ---- a skolem declaration made for a refused rule -------------------------------

(tu/deftest-kb a-refused-existential-rule-leaves-no-skolem-declaration
  (tu/with-terms [dog ownerOf Rex]
    (v/assert kb (list dog Rex) 'CxUniverse)
    (refused-leaves-nothing kb (list 'implies (list dog '?x) (list 'exists '?y (list ownerOf '?z '?y)))
                            'CxUniverse :not-range-restricted)
    (is (nil? (v/handle-of kb '(reifiable_function SkolemFn) 'CxUniverse)))))

;; ---- a refusal raised while the assertion's rules fire ---------------------------

(tu/deftest-kb a-costly-exception-pattern-met-while-chaining-takes-the-fact-back
  (tu/with-terms [hasLabel labelled_thing ItemOne ItemTwo]
    (v/assert kb (list 'exceptWhen (list 'matchesPattern '?s "(.*a){20}b")
                       (list 'set/forwardRule (list 'implies (list hasLabel '?x '?s)
                                                    (list labelled_thing '?x))))
              'CxUniverse)
    (v/assert kb (list hasLabel ItemTwo "x") 'CxUniverse)
    (refused-leaves-nothing kb (list hasLabel ItemOne (str (apply str (repeat 30 \a)) "c"))
                            'CxUniverse :pattern-too-costly)
    (testing "the KB goes on taking writes"
      (is (= [{'?x ItemTwo}] (v/ask kb (list labelled_thing '?x) 'CxUniverse))))))

;; ---- an index write refused part-way ---------------------------------------------

(deftest an-index-write-refused-part-way-leaves-no-posting
  ;; the columnar index writes the trie before the argument roots, and a new (predicate,
  ;; position) pair past the scope ceiling refuses in the second step: the trie posting
  ;; the first step wrote has to come out with the record
  (let [kb (v/open-kb {:backend :memory-columnar :space [::argfam-ceiling] :recover? false})]
    (try
      (v/assert kb '(likes Aa Bb) 'CxUniverse)
      (let [before (state kb)]
        (is (= :argument-family-ceiling
               (with-redefs-fn {#'dense-roots-types/argfam-ceiling 0}
                 #(refusal-type kb '(hates Aa Bb) 'CxUniverse))))
        (is (= before (state kb)))
        (is (nil? (v/handle-of kb '(hates Aa Bb) 'CxUniverse)) "no posting names the handle")
        (testing "and the same assert lands once the ceiling allows it"
          (is (nat-int? (v/assert kb '(hates Aa Bb) 'CxUniverse)))
          (is (= [{'?x 'Aa '?y 'Bb}] (v/ask kb '(hates ?x ?y) 'CxUniverse)))))
      (finally (tu/clear-kb! kb)))))
