;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-value-maintenance-test
  "A correspondence keeps the mint map its own supported rewrite supersedes."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- declare-function!
  "Declare one application, its result/projection, and two sibling readers on a bare KB."
  ([kb] (declare-function! kb 'CxUniverse 'CxUniverse))
  ([kb result-context projection-context]
   (doseq [s '[(reifiable_function QualifierFn)
               (genlCx CxStory CxUniverse)
               (genlCx CxOther CxUniverse)]]
     (v/assert kb s 'CxUniverse))
   (v/assert kb '(result QualifierFn qualified_relation) result-context)
   (v/assert kb '(functionCorrespondingPredicate QualifierFn qualifierOf 2) projection-context)))

(defn- named-answers
  "The named target's result membership, correspondence projection and original use."
  ([kb context] (named-answers kb 'namedRoot context))
  ([kb target context]
   (mapv #(v/ask? kb % context)
         [(list 'qualified_relation target)
          (list 'qualifierOf 'base target)
          (list 'related target 'Other)])))

(deftest a-compound-rewrite-keeps-its-projection-through-a-deferred-settle
  (doseq [deferred? [false true]
          context '[CxUniverse CxStory]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (let [h (atom nil)
            write! #(do (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
                        (reset! h (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) context)))]
        (if deferred? (v/with-deferred-settle kb (write!)) (write!))
        (is (= [true true true] (named-answers kb context)))
        (when (= 'CxStory context)
          (is (= [false false false] (named-answers kb 'CxOther)))
          (is (= [false false false] (named-answers kb 'CxUniverse))))
        (v/retract! kb @h)
        (is (= [false false false] (named-answers kb context)))
        (is (true? (v/ask? kb '(related (QualifierFn base) Other) context)))))))

(deftest a-retired-map-does-not-keep-a-withdrawn-correspondence
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/with-deferred-settle kb
      (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
      (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
    (is (= [true true true] (named-answers kb 'CxUniverse)))
    (v/retract! kb (v/handle-of kb '(functionCorrespondingPredicate QualifierFn qualifierOf 2) 'CxUniverse))
    (is (= [true false true] (named-answers kb 'CxUniverse)))))

(deftest a-retired-map-does-not-keep-an-ambiguous-rewrite
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/with-deferred-settle kb
      (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
      (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
    (is (= [true true true] (named-answers kb 'CxUniverse)))
    (let [rival (v/assert kb '(rewriteOf rivalRoot (QualifierFn base)) 'CxUniverse)]
      (is (= [false false false] (named-answers kb 'CxUniverse)))
      (is (false? (v/ask? kb '(related rivalRoot Other) 'CxUniverse)))
      (is (true? (v/ask? kb '(related (QualifierFn base) Other) 'CxUniverse)))
      (v/retract! kb rival)
      (is (= [true true true] (named-answers kb 'CxUniverse))))))

(deftest an-actually-used-compound-rewrite-target-has-the-same-result-and-projection-in-either-order
  (doseq [alias-first? [true false]
          deferred? [false true]
          context '[CxUniverse CxStory]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (let [alias '(rewriteOf namedRoot (QualifierFn base))
            use   '(related (QualifierFn base) Other)
            load! #(doseq [s (if alias-first? [alias use] [use alias])]
                     (v/assert kb s context))]
        (if deferred? (v/with-deferred-settle kb (load!)) (load!))
        (is (= [true true true] (named-answers kb context))
            (pr-str {:alias-first? alias-first? :deferred? deferred? :context context}))
        (when alias-first?
          (is (empty? (v/sentexes-matching kb '(natFormula ?k ?e) 'CxUniverse))))
        (when (= 'CxStory context)
          (is (= [false false false] (named-answers kb 'CxOther)))
          (is (= [false false false] (named-answers kb 'CxUniverse))))))))

(deftest named-results-are-structural-but-the-projection-declaration-is-contextual
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb 'CxOther 'CxOther)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxStory)
    (v/assert kb '(related (QualifierFn base) Other) 'CxStory)
    (is (= [true false true] (named-answers kb 'CxStory)))
    (is (= [false false false] (named-answers kb 'CxOther)))
    (let [edge (v/assert kb '(genlCx CxStory CxOther) 'CxUniverse)]
      (is (= [true true true] (named-answers kb 'CxStory)))
      (v/retract! kb edge)
      (is (= [true false true] (named-answers kb 'CxStory))))))

(deftest a-used-named-target-takes-late-declarations-and-loses-their-derived-facts
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (v/assert kb '(reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
    (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
    (is (= [false false true] (named-answers kb 'CxUniverse)))
    (let [result (v/assert kb '(result QualifierFn qualified_relation) 'CxUniverse)
          projection (v/assert kb '(functionCorrespondingPredicate QualifierFn qualifierOf 2) 'CxUniverse)]
      (is (= [true true true] (named-answers kb 'CxUniverse)))
      (v/retract! kb result)
      (is (= [false true true] (named-answers kb 'CxUniverse)))
      (v/retract! kb projection)
      (is (= [false false true] (named-answers kb 'CxUniverse))))))

(deftest derived-metadata-is-not-its-own-demand-and-independent-uses-are-retained
  (doseq [deferred? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (v/assert-rule kb '[(qualified_relation ?x)] '(shadow ?x) 'CxUniverse {:direction :forward})
      (v/assert-rule kb '[(shadow ?x)] '(qualified_relation ?x) 'CxUniverse {:direction :forward})
      (let [alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
            h (atom nil)
            use! #(reset! h (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse))]
        (v/assert kb '(comment Example (Quote namedRoot)) 'CxUniverse)
        (is (= [false false false] (named-answers kb 'CxUniverse)))
        (v/preview kb {:add [['(related (QualifierFn base) Other) 'CxUniverse]]})
        (is (= [false false false] (named-answers kb 'CxUniverse)))
        (if deferred? (v/with-deferred-settle kb (use!)) (use!))
        (is (= [true true true] (named-answers kb 'CxUniverse)))
        (is (true? (v/ask? kb '(shadow namedRoot) 'CxUniverse)))
        (let [independent (v/assert kb '(shadow namedRoot) 'CxUniverse)]
          (v/retract! kb @h)
          (is (= [true true false] (named-answers kb 'CxUniverse)))
          (v/retract! kb independent)
          (is (= [false false false] (named-answers kb 'CxUniverse)))
          (is (false? (v/ask? kb '(shadow namedRoot) 'CxUniverse))))
        (v/retract! kb alias)))))

(deftest an-ambiguous-alias-withdraws-derived-metadata-not-the-captured-user-tuple
  (doseq [deferred? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (let [alias (atom (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
            rival (atom nil)]
        (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
        (is (= [true true true] (named-answers kb 'CxUniverse)))
        (let [add! #(do (reset! rival (v/assert kb '(rewriteOf rivalRoot (QualifierFn base)) 'CxUniverse))
                        (v/assert kb '(marked rivalRoot) 'CxUniverse))]
          (if deferred? (v/with-deferred-settle kb (add!)) (add!)))
        (is (= [false false true] (named-answers kb 'CxUniverse)))
        (is (= [false false false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (v/retract! kb @alias)
        (is (= [true true false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (reset! alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
        (is (= [false false true] (named-answers kb 'CxUniverse)))
        (is (= [false false false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (v/retract! kb @rival)
        (is (= [true true true] (named-answers kb 'CxUniverse)))
        (is (= [false false false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (v/retract! kb @alias)
        (is (= [false false true] (named-answers kb 'CxUniverse)))))))

(deftest an-excepted-alias-withdraws-and-restores-the-named-metadata
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (let [alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)]
      (v/assert kb '(related (QualifierFn base) Other) 'CxStory)
      (is (= [true true true] (named-answers kb 'CxStory)))
      (let [except (v/assert kb (list 'except (list 'sentexHandle alias)) 'CxStory)]
        (is (= [false false true] (named-answers kb 'CxStory)))
        (v/retract! kb except)
        (is (= [true true true] (named-answers kb 'CxStory)))))))

(deftest named-support-is-owned-after-a-contextual-target-normalization
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (let [alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxStory)]
      (v/assert kb '(related (QualifierFn base) Other) 'CxStory)
      (v/assert kb '(rewriteOf preferredRoot namedRoot) 'CxStory)
      (is (true? (v/ask? kb '(qualified_relation preferredRoot) 'CxStory)))
      (is (true? (v/ask? kb '(qualifierOf base preferredRoot) 'CxStory)))
      (is (false? (v/ask? kb '(qualified_relation preferredRoot) 'CxOther)))
      (v/retract! kb alias)
      (is (false? (v/ask? kb '(qualified_relation preferredRoot) 'CxStory)))
      (is (false? (v/ask? kb '(qualifierOf base preferredRoot) 'CxStory)))
      (is (true? (v/ask? kb '(related preferredRoot Other) 'CxStory))))))

(deftest an-admissible-genlresult-is-derived-and-withdrawn-with-its-support
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (doseq [s '[(reifiable_function TypeQualifierFn)
                (rewriteOf named_type (TypeQualifierFn base))
                (related (TypeQualifierFn base) Other)]]
      (v/assert kb s 'CxUniverse))
    (let [declaration (v/assert kb '(genlResult TypeQualifierFn super_type) 'CxUniverse)]
      (is (true? (v/ask? kb '(genl named_type super_type) 'CxUniverse)))
      (v/retract! kb declaration)
      (is (false? (v/ask? kb '(genl named_type super_type) 'CxUniverse)))
      (is (true? (v/ask? kb '(related named_type Other) 'CxUniverse))))))

(deftest named-materialization-keeps-the-existing-forced-output-restriction
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (doseq [s '[(reifiable_function PredicateQualifierFn)
                (rewriteOf namedPredicate (PredicateQualifierFn base))
                (related (PredicateQualifierFn base) Other)
                (genlResult PredicateQualifierFn superPredicate)]]
      (v/assert kb s 'CxUniverse))
    (is (true? (v/ask? kb '(genlResult PredicateQualifierFn superPredicate) 'CxUniverse)))
    (is (true? (v/ask? kb '(related namedPredicate Other) 'CxUniverse)))
    (is (false? (v/ask? kb '(genl namedPredicate superPredicate) 'CxUniverse)))))
