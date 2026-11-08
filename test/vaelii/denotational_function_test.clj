;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.denotational-function-test
  "A reifiable function's inputs determine its denotation. Two equations naming one
  application equate their symbol values, as monotonic functionalInArg tuples do.
  Explicit equations are forced-monotonic; default tuple dilemmas are not equivalent."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

(defn- declare-function
  "Declare an invented function whose ground applications reify."
  [kb f]
  (v/assert kb (list 'reifiable_function f) U))

(defn- equations
  "Assert equations naming `application` by each symbol in `values`. Return handles."
  [kb application values context]
  (mapv #(v/assert kb (list 'equals application %) context {:strength :monotonic}) values))

(defn- assert-equality-answers
  "Check a ground equality through each query engine without printing the KB."
  [kb a b context expected]
  (doseq [[label query] [[:ask v/ask] [:prove v/prove] [:query v/query]]]
    (let [answers (set (query kb (list 'equals a b) context))]
      (is (= expected answers) (str label " " (pr-str (list 'equals a b)) " in " context)))))

(tu/deftest-kb two-symbol-values-of-one-application-merge-in-either-order
  (doseq [input-count [0 1 2], reverse? [false true]]
    (tu/with-terms [ObjectFn Archive Path ObjectOne ObjectTwo]
      (declare-function kb ObjectFn)
      (assert-equality-answers kb ObjectOne ObjectTwo U #{})
      (equations kb (apply list ObjectFn (take input-count [Archive Path]))
                 (if reverse? [ObjectTwo ObjectOne] [ObjectOne ObjectTwo]) U)
      (assert-equality-answers kb ObjectOne ObjectTwo U #{{}}))))

(tu/deftest-kb ^:red a-ground-literal-denotation-is-refused-before-entering-symbol-equality
  (tu/with-terms [ValueFn Subject]
    (declare-function kb ValueFn)
    (is (= :not-well-formed
           (tu/refusal-type
            #(v/assert kb (list 'equals (list ValueFn Subject) 1980) U)))
        "ground equality relates symbol names, not a symbol and a numeric literal")))

(tu/deftest-kb every-input-and-the-function-name-distinguish-the-determinant
  (doseq [changed [:first-input :second-input :function]]
    (testing (name changed)
      (tu/with-terms [ObjectFn OtherFn Archive OtherArchive Path OtherPath ObjectOne ObjectTwo]
        (declare-function kb ObjectFn)
        (declare-function kb OtherFn)
        (let [application (list ObjectFn Archive Path)
              other       (case changed
                            :first-input (list ObjectFn OtherArchive Path)
                            :second-input (list ObjectFn Archive OtherPath)
                            :function (list OtherFn Archive Path))]
          (equations kb application [ObjectOne] U)
          (equations kb other [ObjectTwo] U)
          (assert-equality-answers kb application ObjectOne U #{{}})
          (assert-equality-answers kb other ObjectTwo U #{{}})
          (assert-equality-answers kb ObjectOne ObjectTwo U #{}))))))

(tu/deftest-kb a-211-input-function-distinguishes-a-changed-input
  (tu/with-terms [ObjectFn ObjectOne ObjectTwo ObjectThree]
    (declare-function kb ObjectFn)
    (v/assert kb (list 'arity ObjectFn 211) U)
    (let [inputs (vec (repeatedly 211 #(tu/tmp-ind "Input")))
          other (assoc inputs 4 (tu/tmp-ind "OtherInput"))
          application (apply list ObjectFn inputs)
          other-application (apply list ObjectFn other)]
      (equations kb application [ObjectOne ObjectTwo] U)
      (equations kb other-application [ObjectThree] U)
      (assert-equality-answers kb ObjectOne ObjectTwo U #{{}})
      (assert-equality-answers kb application ObjectOne U #{{}})
      (assert-equality-answers kb other-application ObjectThree U #{{}})
      (assert-equality-answers kb ObjectOne ObjectThree U #{}))))

(tu/deftest-kb retracting-either-sibling-context-equation-separates-the-values-and-retains-the-other
  (doseq [retired [0 1]]
    (tu/with-terms [ObjectFn Archive Path ObjectOne ObjectTwo carriesTag Marker CxLeft CxRight CxJoint]
      (declare-function kb ObjectFn)
      (doseq [[c parent] [[CxLeft U] [CxRight U] [CxJoint CxLeft] [CxJoint CxRight]]]
        (v/assert kb (list 'genlCx c parent) U))
      (let [application (list ObjectFn Archive Path)
            values      [ObjectOne ObjectTwo]
            handles     [(first (equations kb application [ObjectOne] CxLeft))
                         (first (equations kb application [ObjectTwo] CxRight))]
            retained    (nth values (- 1 retired))
            removed     (nth values retired)]
        (v/assert kb (list carriesTag retained Marker) U {:strength :monotonic})
        (assert-equality-answers kb ObjectOne ObjectTwo CxJoint #{{}})
        (v/retract! kb (nth handles retired))
        (assert-equality-answers kb ObjectOne ObjectTwo CxJoint #{})
        (assert-equality-answers kb application retained CxJoint #{{}})
        (assert-equality-answers kb application removed CxJoint #{})
        (is (= #{{'?tag Marker}}
               (set (v/ask kb (list carriesTag retained '?tag) CxJoint))))))))

(tu/deftest-kb retracting-the-latest-equation-retains-the-applications-first-value
  (tu/with-terms [ObjectFn Archive Path ObjectOne ObjectTwo]
    (declare-function kb ObjectFn)
    (let [application (list ObjectFn Archive Path)
          [_ latest] (equations kb application [ObjectOne ObjectTwo] U)]
      (assert-equality-answers kb ObjectOne ObjectTwo U #{{}})
      (v/retract! kb latest)
      (assert-equality-answers kb ObjectOne ObjectTwo U #{})
      (assert-equality-answers kb application ObjectOne U #{{}})
      (assert-equality-answers kb application ObjectTwo U #{}))))

(tu/deftest-kb only-joint-readers-equate-values-stated-in-sibling-contexts
  (doseq [edges-last? [false true]]
    (tu/with-terms [ObjectFn Archive Path ObjectOne ObjectTwo CxLeft CxRight CxJoint CxOther]
      (declare-function kb ObjectFn)
      (doseq [c [CxLeft CxRight CxJoint CxOther]]
        (v/assert kb (list 'genlCx c U) U))
      (let [connect (fn []
                      (doseq [reader [CxJoint CxOther], source [CxLeft CxRight]]
                        (v/assert kb (list 'genlCx reader source) U)))
            application (list ObjectFn Archive Path)]
        (when-not edges-last? (connect))
        (equations kb application [ObjectOne] CxLeft)
        (equations kb application [ObjectTwo] CxRight)
        (when edges-last?
          (doseq [reader [CxJoint CxOther]]
            (assert-equality-answers kb ObjectOne ObjectTwo reader #{}))
          (connect))
        (doseq [reader [U CxLeft CxRight]]
          (assert-equality-answers kb ObjectOne ObjectTwo reader #{}))
        (doseq [reader [CxJoint CxOther]]
          (assert-equality-answers kb ObjectOne ObjectTwo reader #{{}}))))))
