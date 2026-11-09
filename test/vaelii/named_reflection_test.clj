;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.named-reflection-test
  "Queryable application reflection follows supported named identities, not mint order."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- reflection-status
  "Positive and explicit negative proof bits; unsupported is neither."
  [kb context]
  [(v/ask? kb '(natFormula namedRoot (QualifierFn base)) context)
   (v/ask? kb '(not (natFormula namedRoot (QualifierFn base))) context)])

(deftest reflection-and-its-consumers-agree-in-either-arrival-order
  (doseq [alias-first? [true false]
          deferred? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (v/assert kb '(reifiable_function QualifierFn) 'CxUniverse)
      (v/assert-rule kb '[(natFormula ?target (QualifierFn ?input))]
                     '(observed ?target ?input) 'CxUniverse {:direction :forward})
      (v/assert-rule kb '[(natFormula ?target (QualifierFn ?input))]
                     '(backSeen ?target ?input) 'CxUniverse {:direction :backward})
      (let [alias '(rewriteOf namedRoot (QualifierFn base))
            use '(related (QualifierFn base) Other)
            load! #(doseq [s (if alias-first? [alias use] [use alias])]
                     (v/assert kb s 'CxUniverse))]
        (if deferred? (v/with-deferred-settle kb (load!)) (load!))
        (let [actual {:closed (v/ask? kb '(natFormula namedRoot (QualifierFn base)) 'CxUniverse)
                      :open (set (v/query kb '(natFormula ?target (QualifierFn base)) 'CxUniverse))
                      :forward (v/ask? kb '(observed namedRoot base) 'CxUniverse)
                      :backward (v/query? kb '(backSeen namedRoot base) 'CxUniverse {:max-depth 3})}]
          (is (= {:closed true :open '#{{?target namedRoot}} :forward true :backward true}
                 actual)))))))

(deftest nested-reflection-payloads-agree-in-either-arrival-order
  (let [answers
        (mapv
         (fn [alias-first?]
           (tu/with-cleared-kb [kb tu/isolated-fresh]
             (doseq [s '[(reifiable_function OuterFn) (reifiable_function InnerFn)]]
               (v/assert kb s 'CxUniverse))
             (let [alias '(rewriteOf namedRoot (OuterFn (InnerFn X)))
                   use '(related namedRoot Other)]
               (doseq [s (if alias-first? [alias use] [use alias])]
                 (v/assert kb s 'CxUniverse))
               (let [answer {:closed (v/ask? kb '(natFormula namedRoot (OuterFn (InnerFn X))) 'CxUniverse)
                             :open (set (v/query kb '(natFormula namedRoot ?expression) 'CxUniverse))
                             :rewrite (set (v/query kb '(rewriteOf namedRoot ?expression) 'CxUniverse))}]
                 answer)))) [true false])]
    (is (= [{:closed true
             :open '#{{?expression (OuterFn (InnerFn X))}}
             :rewrite '#{{?expression (OuterFn (InnerFn X))}}}
            {:closed true
             :open '#{{?expression (OuterFn (InnerFn X))}}
             :rewrite '#{{?expression (OuterFn (InnerFn X))}}}]
           answers))))

(deftest named-reflection-withdraws-with-its-private-alias-and-independent-demand
  (doseq [alias-first? [true false]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (doseq [s '[(reifiable_function QualifierFn)
                  (genlCx CxSecret CxUniverse) (genlCx CxSibling CxUniverse)]]
        (v/assert kb s 'CxUniverse))
      (v/assert-rule kb '[(natFormula ?target (QualifierFn ?input))]
                     '(shadow ?target) 'CxUniverse {:direction :forward})
      (let [alias '(rewriteOf namedRoot (QualifierFn base))
            use '(related (QualifierFn base) Other)
            hs (mapv #(v/assert kb % 'CxSecret) (if alias-first? [alias use] [use alias]))
            alias-h (if alias-first? (first hs) (second hs))
            use-h (if alias-first? (second hs) (first hs))]
        (is (= [true false] (reflection-status kb 'CxSecret)))
        (is (= [false false] (reflection-status kb 'CxUniverse)))
        (is (= [false false] (reflection-status kb 'CxSibling)))
        (is (false? (v/premise? kb (v/handle-of kb '(natFormula namedRoot (QualifierFn base)) 'CxSecret))))
        (v/retract! kb use-h)
        (is (= [false false] (reflection-status kb 'CxSecret)))
        (is (false? (v/ask? kb '(shadow namedRoot) 'CxSecret)))
        (let [first-use (v/assert kb '(kept namedRoot) 'CxSecret)
              second-use (v/assert kb '(marked namedRoot) 'CxSecret)]
          (is (= [true false] (reflection-status kb 'CxSecret)))
          (v/retract! kb first-use)
          (is (= [true false] (reflection-status kb 'CxSecret)))
          (let [rival (v/assert kb '(rewriteOf rivalRoot (QualifierFn base)) 'CxSecret)]
            (is (= [false false] (reflection-status kb 'CxSecret)))
            (v/retract! kb rival)
            (is (= [true false] (reflection-status kb 'CxSecret))))
          (v/retract! kb alias-h)
          (is (= [false false] (reflection-status kb 'CxSecret)))
          (is (true? (v/ask? kb '(marked namedRoot) 'CxSecret)))
          (v/retract! kb second-use))))))

(deftest resultarg-consumes-supported-named-reflection
  (tu/with-entailing
    (doseq [alias-first? [true false]
            declaration-first? [true false]]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (v/assert kb '(reifiable_function QualifierFn) 'CxUniverse)
        (when declaration-first?
          (v/assert kb '(resultArg QualifierFn 1) 'CxUniverse))
        (let [alias '(rewriteOf namedRoot (QualifierFn base))
              use '(related (QualifierFn base) Other)]
          (doseq [s (if alias-first? [alias use] [use alias])]
            (v/assert kb s 'CxUniverse))
          (when-not declaration-first?
            (v/assert kb '(resultArg QualifierFn 1) 'CxUniverse))
          (is (= [true false] (reflection-status kb 'CxUniverse)))
          (is (true? (v/ask? kb '(base namedRoot) 'CxUniverse))))))))

(deftest open-reflection-and-rewrite-answers-agree-in-either-arrival-order
  (let [answers
        (mapv
         (fn [alias-first?]
           (tu/with-neutral-kb [kb tu/isolated-fresh]
             (v/assert kb '(reifiable_function QualifierFn) 'CxUniverse)
             (doseq [s (if alias-first?
                         '[(rewriteOf namedRoot (QualifierFn base)) (related (QualifierFn base) Other)]
                         '[(related (QualifierFn base) Other) (rewriteOf namedRoot (QualifierFn base))])]
               (v/assert kb s 'CxUniverse))
             (let [actual {:maps (set (v/query kb '(natFormula ?target ?expression) 'CxUniverse))
                           :rewrites (set (v/query kb '(rewriteOf namedRoot ?expression) 'CxUniverse))
                           :denial (v/ask? kb '(not (natFormula namedRoot (QualifierFn base))) 'CxUniverse)}]
               actual))) [true false])]
    (is (= (first answers) (second answers)))))

(deftest reflection-status-distinguishes-unsupported-from-an-explicit-denial
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (v/assert kb '(reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
    (is (= [false false] (reflection-status kb 'CxUniverse)))
    (let [denial (v/assert kb '(not (natFormula namedRoot (QualifierFn base))) 'CxUniverse)]
      (is (= [false true] (reflection-status kb 'CxUniverse)))
      (v/retract! kb denial)
      (is (= [false false] (reflection-status kb 'CxUniverse))))))
