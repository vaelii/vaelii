;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-value-maintenance-test
  "A correspondence keeps the mint map its own supported rewrite supersedes."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- declare-function!
  "Declare one application, its result/projection, and two sibling readers on a bare KB."
  [kb]
  (doseq [s '[(reifiable_function QualifierFn)
              (result QualifierFn qualified_relation)
              (functionCorrespondingPredicate QualifierFn qualifierOf 2)
              (genlCx CxStory CxUniverse)
              (genlCx CxOther CxUniverse)]]
    (v/assert kb s 'CxUniverse)))

(defn- named-answers
  "The named target's result membership, correspondence projection and original use."
  [kb context]
  (mapv #(v/ask? kb % context)
        '[(qualified_relation namedRoot)
          (qualifierOf base namedRoot)
          (related namedRoot Other)]))

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
