;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.denotational-context-mirror-test
  "A functional selection predicate and a denotational function select one referent.
  Predicates applied to that referent must agree under either representation, including
  functional label collisions visible only in overlapping contexts. Selection and calendar
  ordering declarations are monotonic, matching the function referent's structural identity."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:private U 'CxUniverse)

(defn- contexts
  "Mint named or calendar contexts. Return source/read contexts and their ordering step."
  [kb {:keys [topology overlap?]}]
  (tu/with-terms [CxLeft CxRight CxJoint SpanFn Dimension present Marker]
    (let [calendar? (= topology :calendar)
          _ (when calendar?
              (v/assert kb (list 'result SpanFn 'context) U)
              (doseq [f '[DatetimeFn DatetimeRangeFn]]
                (v/assert kb (list 'unreifiable_function f) U)))
          written (if calendar?
                    [(list SpanFn Dimension '(DatetimeRangeFn "2000-01" "2000-02"))
                     (list SpanFn Dimension (if overlap?
                                              '(DatetimeRangeFn "2000-02" "2000-03")
                                              '(DatetimeRangeFn "2000-03" "2000-04")))
                     (list SpanFn Dimension '(DatetimeFn "2000-02"))]
                    [CxLeft CxRight CxJoint])
          ids (mapv #(->> (v/assert kb (list present Marker) %) (v/sentex kb) :context) written)
          [left right joint] ids]
      (doseq [c ids] (v/assert kb (list 'genlCx c U) U))
      {:written written :ids ids
       :order (fn []
                (if calendar?
                  (v/assert kb (list 'contextArgSubrelation SpanFn 2 'subintervalOf) U {:strength :monotonic})
                  (do (v/assert kb (list 'genlCx joint left) U)
                      (when overlap? (v/assert kb (list 'genlCx joint right) U)))))})))

(defn- observe
  "Read labels, equality, and functional clash categories without representation-specific IDs."
  [kb {:keys [label objects values layout difference]}]
  (let [[left right joint] (:ids layout)
        [one two] values
        count-at (fn [object ctx] (count (set (map '?value (v/ask kb (list label object '?value) ctx)))))
        true-at (fn [object value ctx] (boolean (v/ask? kb (list label object value) ctx)))
        functional? #(boolean (some (comp #{:functional} :kind) %))]
    {:leaf-counts [(count-at (first objects) left) (count-at (second objects) right)]
     :leaf-values [(true-at (first objects) one left) (true-at (second objects) two right)]
     :joint-count (count-at (first objects) joint)
     :joint-values [(true-at (first objects) one joint) (true-at (first objects) two joint)]
     :same-values (and (symbol? one) (symbol? two) (boolean (v/same-class? kb one two joint)))
     :dilemma (functional? (v/contradictions kb joint))
     :conflict (functional? (v/conflicts kb))
     :difference (when difference (boolean (v/ask? kb difference U)))}))

(defn- run-case
  "Build one representation in an independent neutral KB. Return observations before/after withdrawal."
  [{:keys [functional? value-kind reverse? strengths arrival difference-order retract-side
           determinant-count determined-position changed-input peer? merge-reader?]
    :as options} representation]
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [SelectedFn selection labelOf generalLabelOf Subject ObjectOne ObjectTwo LabelOne LabelTwo
                    CxPeer CxMerge]
      (let [layout (contexts kb options)
            [left right] (:written layout)
            input-count (or determinant-count 1)
            position (or determined-position (inc input-count))
            inputs (if (zero? input-count) []
                       (into [Subject] (repeatedly (dec input-count) #(tu/tmp-ind "Input"))))
            other-inputs (if (some? changed-input) (assoc inputs changed-input (tu/tmp-ind "OtherInput")) inputs)
            objects (if (= representation :predicate)
                      [ObjectOne ObjectTwo]
                      [(apply list SelectedFn inputs) (apply list SelectedFn other-inputs)])
            values (if (= value-kind :strings) ["Amber Atlas" "Indigo Orchard"] [LabelOne LabelTwo])
            difference (when difference-order (list 'not (list 'equals LabelOne LabelTwo)))
            state {:label labelOf :objects objects :values values :layout layout :difference difference}
            selector (fn []
                       (if (= representation :predicate)
                         (v/assert kb (list 'functionalInArg selection position) U {:strength :monotonic})
                         (v/assert kb (list 'reifiable_function SelectedFn) U {:strength :monotonic})))
            mark (fn [] (when functional?
                          (v/assert kb (list 'functional (if (= arrival :genl-last) generalLabelOf labelOf)) U)))
            fact (fn [side]
                   (let [ctx (nth [left right] side)]
                     (when (= representation :predicate)
                       (let [args (nth [inputs other-inputs] side)]
                         (v/assert kb (apply list selection
                                             (concat (take (dec position) args) [(nth objects side)]
                                                     (drop (dec position) args)))
                                   ctx {:strength :monotonic})))
                     (v/assert kb (list labelOf (nth objects side) (nth values side)) ctx
                               {:strength (nth strengths side)})))]
        (when-not (= arrival :selection-last) (selector))
        (when-not (= arrival :order-last) ((:order layout)))
        (when-not (= arrival :mark-last) (mark))
        (when (= difference-order :first) (v/assert kb difference U))
        (let [handles (into {} (map (fn [side] [side (fact side)])) (if reverse? [1 0] [0 1]))]
          (when (= arrival :selection-last) (selector))
          (when (= difference-order :last) (v/assert kb difference U))
          (when (= arrival :mark-last) (mark))
          (when (= arrival :genl-last) (v/assert kb (list 'genl labelOf generalLabelOf) U))
          (when (= arrival :order-last) ((:order layout)))
          (let [before (observe kb state)]
            (when peer?
              (doseq [source (take 2 (:ids layout))]
                (v/assert kb (list 'genlCx CxPeer source) U)))
            (when merge-reader?
              (v/assert kb (list 'genlCx CxMerge (nth (:ids layout) 2)) U)
              (v/assert kb (list 'sameAs (first values) (second values)) CxMerge {:strength :monotonic}))
            (when (some? retract-side) (v/retract! kb (get handles retract-side)))
            {:before before :after (when (some? retract-side) (observe kb state))
             :peer (when peer? (observe kb (assoc-in state [:layout :ids 2] CxPeer)))
             :merged-reader (when merge-reader? (observe kb (assoc-in state [:layout :ids 2] CxMerge)))
             :merged-source-beliefs (when merge-reader? (mapv #(v/believed? kb (handles %) CxMerge) [0 1]))
             :joint-after-merge (when merge-reader? (observe kb state))
             :joint-source-beliefs (when merge-reader?
                                     (mapv #(v/believed? kb (handles %) (nth (:ids layout) 2)) [0 1]))}))))))

(defn- expected
  "The label contract: monotonic symbols merge; default ties remain dilemmas; stronger labels win."
  [{:keys [functional? overlap? value-kind strengths difference-order changed-input]}]
  (let [shared? (and overlap? (nil? changed-input))
        constrained? (and functional? shared?)
        mixed? (and constrained? (= strengths [:default :monotonic]))
        merged? (and constrained? (= value-kind :symbols) (= strengths [:monotonic :monotonic]))
        conflict? (and constrained? (= value-kind :strings) (= strengths [:monotonic :monotonic]))
        dilemma? (and constrained? (not merged?) (not mixed?) (not conflict?))]
    {:leaf-counts [1 1] :leaf-values [true true]
     :joint-count (if (or (not shared?) mixed? merged?) 1 2)
     :joint-values (cond (not shared?) [true false] mixed? [false true] :else [true true])
     :same-values (boolean merged?) :dilemma (boolean dilemma?) :conflict (boolean conflict?)
     :difference (when difference-order true)}))

(defn- assert-both-representations
  "Check both spellings against the independent expected observation, then against each other."
  [options]
  (let [want (expected options)
        observations (mapv #(-> (run-case options %) :before) [:predicate :function])]
    (is (= [want want] observations) (pr-str options))))

(deftest ^:slow labels-have-the-same-contract-in-named-and-calendar-contexts
  (doseq [functional? [false true], value-kind [:strings :symbols]
          topology [:named :calendar], overlap? [false true], reverse? [false true]]
    (assert-both-representations
     {:functional? functional? :value-kind value-kind :topology topology :overlap? overlap?
      :reverse? reverse? :arrival :facts-last
      :strengths (if (= value-kind :symbols) [:monotonic :monotonic] [:default :default])})))

(deftest label-strengths-and-explicit-difference-have-the-same-contract
  (doseq [value-kind [:strings :symbols], reverse? [false true]
          strengths [[:default :default] [:default :monotonic] [:monotonic :monotonic]]
          :when (not= strengths (if (= value-kind :symbols) [:monotonic :monotonic] [:default :default]))]
    (assert-both-representations
     {:functional? true :value-kind value-kind :topology :named :overlap? true
      :reverse? reverse? :strengths strengths :arrival :facts-last}))
  (doseq [difference-order [:first :last]]
    (assert-both-representations
     {:functional? true :value-kind :symbols :topology :named :overlap? true
      :strengths [:default :default] :difference-order difference-order :arrival :facts-last})))

(deftest selecting-any-output-position-matches-the-remaining-function-inputs
  (doseq [[input-count position changed-input]
          [[0 1 nil] [1 1 nil] [2 2 nil] [2 3 nil]
           [2 3 0] [2 3 1] [211 212 nil] [211 212 4]]]
    (assert-both-representations
     {:functional? true :value-kind :symbols :topology :named :overlap? true
      :strengths [:monotonic :monotonic] :arrival :facts-last
      :determinant-count input-count :determined-position position :changed-input changed-input})))

(deftest ^:slow labels-already-stored-agree-when-a-mark-or-context-order-arrives-last
  (doseq [arrival [:mark-last :selection-last :genl-last :order-last], topology [:named :calendar]
          value-kind [:strings :symbols]]
    (assert-both-representations
     {:functional? true :value-kind value-kind :topology topology :overlap? true
      :strengths (if (= value-kind :symbols) [:monotonic :monotonic] [:default :default])
      :arrival arrival})))

(deftest independent-joint-readers-see-the-same-label-merge-or-dilemma
  (doseq [representation [:predicate :function], value-kind [:strings :symbols]]
    (let [options {:functional? true :value-kind value-kind :topology :named :overlap? true
                   :strengths (if (= value-kind :symbols) [:monotonic :monotonic] [:default :default])
                   :arrival :facts-last :peer? true}
          {:keys [before peer]} (run-case options representation)]
      (is (= [(expected options) (expected options)] [before peer])
          (str representation " " value-kind)))))

(deftest a-reader-equating-the-symbol-labels-reads-no-default-defeat
  (doseq [representation [:predicate :function]]
    (let [options {:functional? true :value-kind :symbols :topology :named :overlap? true
                   :strengths [:default :monotonic] :arrival :facts-last :merge-reader? true}
          {:keys [before merged-reader merged-source-beliefs joint-after-merge joint-source-beliefs]}
          (run-case options representation)]
      (testing (name representation)
        (is (= (expected options) before joint-after-merge))
        (is (= [false true] joint-source-beliefs))
        (is (= [true true] merged-source-beliefs))
        (is (= (assoc (expected options) :joint-values [true true] :same-values true)
               merged-reader))))))

(deftest withdrawing-either-label-separates-symbol-values-and-retains-the-other
  (doseq [representation [:predicate :function], retract-side [0 1]]
    (let [options {:functional? true :value-kind :symbols :topology :named :overlap? true
                   :strengths [:monotonic :monotonic] :arrival :facts-last :retract-side retract-side}
          {:keys [before after]} (run-case options representation)
          remaining (if (zero? retract-side) [false true] [true false])]
      (testing (str representation " withdraw " retract-side)
        (is (= (expected options) before))
        (is (= {:leaf-counts (if (zero? retract-side) [0 1] [1 0])
                :leaf-values remaining :joint-count 1 :joint-values remaining
                :same-values false :dilemma false :conflict false :difference nil}
               after))))))
