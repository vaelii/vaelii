;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wff-test
  "Well-formedness checking of genl, genlCx, disjoint, disjoint_metatype, arg."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ill-formed?
  "Did asserting this into the KB under test fail well-formedness?"
  [& args]
  (try (apply v/assert tu/*kb* args) false
       (catch clojure.lang.ExceptionInfo e
         (boolean (re-find #"not well-formed" (.getMessage e))))))

(tu/deftest-kb genl-well-formedness
  (let [dog (tu/tmp-type) animal (tu/tmp-type) mammal (tu/tmp-type)
        muffet (tu/tmp-ind) rover (tu/tmp-ind)]
    (testing "well-formed genl is accepted"
      (is (v/assert kb (list 'genl dog animal) 'CxUniverse)))
    (testing "genl relates types, not individuals"
      (is (ill-formed? (list 'genl muffet animal) 'CxUniverse))
      (is (ill-formed? (list 'genl dog rover) 'CxUniverse)))
    (testing "genl of a type with itself is ill-formed"
      (is (ill-formed? (list 'genl dog dog) 'CxUniverse)))
    (testing "a genl cycle is rejected"
      (v/assert kb (list 'genl mammal animal) 'CxUniverse)
      (is (ill-formed? (list 'genl animal mammal) 'CxUniverse)))))   ; would close mammal→animal→mammal

(tu/deftest-kb a-genl-cycle-is-refused-at-every-strength
  ;; The cycle check reads reachability and no strength: a cycle condenses into one
  ;; component every reader shares, so a `:default` edge closes one as a `:monotonic` one does.
  (doseq [[down up] [[:monotonic :default] [:default :default]
                     [:default :monotonic] [:monotonic :monotonic]]]
    (tu/with-terms [mortal organism]
      (v/assert kb (list 'genl mortal organism) 'CxUniverse {:strength down})
      (testing [down up]
        (is (ill-formed? (list 'genl organism mortal) 'CxUniverse {:strength up}))))))

(tu/deftest-kb disjoint-well-formedness
  (let [dog (tu/tmp-type) cat (tu/tmp-type) mammal (tu/tmp-type) muffet (tu/tmp-ind)]
    (testing "well-formed disjoint is accepted"
      (is (v/assert kb (list 'disjoint dog cat) 'CxUniverse)))
    (testing "disjoint relates types, not individuals"
      (is (ill-formed? (list 'disjoint muffet cat) 'CxUniverse)))
    (testing "a disjoint over genl-related types is well formed, and stored"
      ;; decision 8 of docs/reference.md: refusing it would read the stored edge
      (v/assert kb (list 'genl dog mammal) 'CxUniverse)
      (is (v/assert kb (list 'disjoint dog mammal) 'CxUniverse)))))

(tu/deftest-kb arg-and-genlCx-well-formedness
  (let [parentOf (tu/tmp-pred) animal (tu/tmp-type) muffet (tu/tmp-ind) a-ctx (tu/tmp-ctx)]
    (testing "arg needs a predicate, a positive integer, and a type"
      (is (v/assert kb (list 'arg parentOf 1 animal) 'CxUniverse))
      (is (ill-formed? (list 'arg parentOf 0 animal) 'CxUniverse))    ; position must be positive
      (is (ill-formed? (list 'arg parentOf 1 muffet) 'CxUniverse)))     ; type is an individual
    (testing "genlCx relates contexts"
      (is (v/assert kb (list 'genlCx a-ctx 'CxUniverse) 'CxUniverse))
      (is (ill-formed? (list 'genlCx animal 'CxUniverse) 'CxUniverse)))))  ; not a context

(tu/deftest-kb an-argument-constraint-may-be-about-a-function
  ;; A function has argument positions exactly as a predicate does — `(arg Milli 1
  ;; unit_of_measure)` says what the argument of a NAT `(Milli Meter)` must be, the same
  ;; kind of claim `result` makes about its result — and a function is spelled
  ;; CapitalCamelCase, which is also how an individual is spelled.  So the constrained
  ;; relation cannot be held to a spelling without refusing the whole vocabulary of
  ;; function argument types.
  (tu/with-terms [Milli a_unit]
    (v/assert kb (list 'genl a_unit 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function Milli) 'CxUniverse)
    (is (v/assert kb (list 'arg Milli 1 a_unit) 'CxUniverse))
    (testing "and both constraints may be about it, since they ask different questions"
      (is (v/assert kb (list 'genlArg Milli 1 a_unit) 'CxUniverse)))
    (testing "what is decidable from the sentence is still checked"
      (is (ill-formed? (list 'arg Milli 1 (tu/tmp-ind)) 'CxUniverse))   ; type is an individual
      (is (ill-formed? (list 'arg Milli 0 a_unit) 'CxUniverse)))))      ; position not positive

(tu/deftest-kb a-value-in-a-type-position-is-not-well-formed
  ;; a value has instances of nothing, so a declaration that places one in the lattice or
  ;; names one as a type says nothing true; the check reads the sentence alone
  (tu/with-terms [dog cat relatesTo]
    (doseq [value ["Bob" 5 2.5 1N 1.5M :bob true \b nil #inst "2020-01-01"
                   #uuid "00000000-0000-0000-0000-000000000001"]
            sentence [(list 'genl value dog) (list 'genl dog value)
                      (list 'disjoint value cat) (list 'disjoint dog value)
                      (list 'covering dog value cat) (list 'partition value dog cat)
                      (list 'disjoint_metatype value) (list 'sibling_disjoint value)
                      (list 'orthogonal value cat) (list 'siblingDisjointException dog value)
                      (list 'arg relatesTo 1 value) (list 'genlArg relatesTo 1 value)
                      (list 'quotedArg relatesTo 1 value)
                      (list 'interArg relatesTo 1 dog 2 value) (list 'interArg relatesTo 1 value 2 cat)
                      (list 'args relatesTo value) (list 'argAndRest relatesTo 1 value)]]
      (is (= [:not-well-formed] (mapv :type (v/check kb sentence 'CxUniverse)))
          (pr-str sentence)))
    (testing "an instance position takes a value"
      (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
      (is (not-any? #{:not-well-formed} (map :type (v/check kb (list dog "Bob") 'CxUniverse)))))))

(tu/deftest-kb a-rule-concluding-a-value-edge-drops-the-firing
  (tu/with-terms [tagged dog]
    (v/clear-violations! kb)
    (v/assert kb (list 'set/forwardRule (list 'implies (list tagged '?x) (list 'genl '?x dog)))
              'CxUniverse)
    (v/assert kb (list tagged "Bob") 'CxUniverse)
    (is (not (v/genl? kb "Bob" dog 'CxUniverse)))
    (is (= [[:not-well-formed (list 'genl "Bob" dog)]]
           (mapv (juxt :violation :sentence) (v/violations kb))))))

(def ^:private relation-slots
  "One sentence builder per position that names a predicate or a function, taking the
  occupant `x`, a predicate `p` and a type `t`."
  (concat
   (for [mark '[transitive symmetric asymmetric reflexive functional irreflexive
                anti_symmetric anti_transitive commutative decontextualized_predicate
                forced_decontextualized_predicate forced_monotonic_predicate
                forced_monotonic_between_predicates target_following_predicate
                abducible_predicate closed_extent_predicate modal_predicate
                reifiable_function unreifiable_function]]
     (fn [x _ _] (list mark x)))
   [(fn [x _ _] (list 'closedExtentForArg x 1 5))
    (fn [x _ _] (list 'functionalInArg x 1))
    (fn [x _ _] (list 'commutativeInArgAndRest x 1))
    (fn [x _ _] (list 'commutativeInArgs x 1 2))
    (fn [x p _] (list 'inverse x p))       (fn [x p _] (list 'inverse p x))
    (fn [x p _] (list 'genlInverse x p))   (fn [x p _] (list 'genlInverse p x))
    (fn [x _ t] (list 'arg x 1 t))         (fn [x _ t] (list 'interArg x 1 t 2 t))
    (fn [x _ _] (list 'argArg x 1 2))      (fn [x _ t] (list 'interArgEqual x 1 3 2 t))
    (fn [x _ t] (list 'argAndRest x 1 t))
    (fn [x _ _] (list 'transitiveInArg x 1 'genl))
    (fn [x p _] (list 'transitiveInArg p 1 x))
    (fn [x p _] (list 'contextArgSubrelation x 1 p))
    (fn [x p _] (list 'functionCorrespondingPredicate x p 2))
    (fn [x _ _] (list 'functionCorrespondingPredicate 'MotherFn x 2))]))

(tu/deftest-kb a-value-in-a-relation-position-is-not-well-formed
  ;; a value denotes itself, so it names no predicate and no function
  (tu/with-terms [relatesTo dog]
    (doseq [value ["f" 5 2.5 1N :f true \f nil #inst "2020-01-01"
                   #uuid "00000000-0000-0000-0000-000000000001"]
            slot  relation-slots
            :let  [sentence (slot value relatesTo dog)]]
      (is (= [:not-well-formed] (mapv :type (v/check kb sentence 'CxUniverse)))
          (pr-str sentence)))
    (testing "a symbol and a compound name a relation"
      (doseq [x [relatesTo (list 'TmpRelFn relatesTo)]
              :let [sentence (list 'transitive x)]]
        (is (not-any? #{:not-well-formed} (map :type (v/check kb sentence 'CxUniverse)))
            (pr-str sentence))))))
