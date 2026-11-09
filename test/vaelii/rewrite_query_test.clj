;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rewrite-query-test
  "The positive rewriteOf public relation is read through reader representatives.
  Raw storage remains directed."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.quasiquote :as quasiquote]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb a-rewrite-binding-roundtrips-and-composes-before-projection
  (tu/with-terms [preferred old marked unrelated]
    (v/assert kb (list marked preferred) 'CxUniverse)
    (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
    (let [answers (set (v/query kb (list 'rewriteOf preferred '?x) 'CxUniverse))]
      (is (= #{{'?x preferred}} answers))
      (doseq [answer answers]
        (is (true? (v/ask? kb (list 'rewriteOf preferred (get answer '?x)) 'CxUniverse))))
      (is (= #{{'?x preferred}}
             (set (v/query kb (list 'and (list 'rewriteOf preferred '?x)
                                   (list marked '?x)) 'CxUniverse)))))
    (testing "a variable predicate does not expose the retired spelling"
      (let [bindings (filter #(= 'rewriteOf (get % '?p))
                             (v/query kb (list '?p preferred '?x) 'CxUniverse))]
        (is (seq bindings))
        (is (= #{preferred} (set (map #(get % '?x) bindings))))))
    (testing "normalization is applied before repeated-variable unification"
      (is (contains? (set (v/query kb '(rewriteOf ?x ?x) 'CxUniverse))
                     {'?x preferred}))
      (is (= #{{'?x preferred}}
             (set (v/query kb (list 'rewriteOf '?x old) 'CxUniverse))))
      (is (contains? (set (v/query kb '(rewriteOf ?x ?y) 'CxUniverse))
                     {'?x preferred '?y preferred})))
    (testing "a visible witness permits either spelling, not universal reflexivity"
      (is (true? (v/ask? kb (list 'rewriteOf old preferred) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'rewriteOf preferred preferred) 'CxUniverse)))
      (is (false? (v/ask? kb (list 'rewriteOf unrelated unrelated) 'CxUniverse))))
    (testing "the actual stored edge is still directed and as authored"
      (is (some? (v/handle-of kb (list 'rewriteOf preferred old) 'CxUniverse)))
      (is (nil? (v/handle-of kb (list 'rewriteOf preferred preferred) 'CxUniverse))))))

(tu/deftest-kb a-private-rewrite-is-not-a-public-normalization-witness
  (tu/with-terms [preferred old CxPrivate CxChild CxSibling]
    (v/assert kb (list 'genlCx CxChild CxPrivate) 'CxUniverse)
    (v/assert kb (list 'rewriteOf preferred old) CxPrivate)
    (doseq [reader [CxPrivate CxChild]]
      (is (= #{{'?x preferred}}
             (set (v/query kb (list 'rewriteOf old '?x) reader)))))
    (doseq [reader ['CxUniverse CxSibling]]
      (is (empty? (v/query kb (list 'rewriteOf old '?x) reader)))
      (is (false? (v/ask? kb (list 'rewriteOf preferred preferred) reader))))))

(tu/deftest-kb identity-class-answers-keep-live-aliases-but-not-retired-spellings
  (tu/with-terms [preferred old identityAlias]
    (v/assert kb (list 'sameAs preferred identityAlias) 'CxUniverse)
    (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
    (doseq [pred ['sameAs 'equals]]
      (is (= #{preferred identityAlias}
             (set (map #(get % '?x)
                       (v/query kb (list pred preferred '?x) 'CxUniverse)))))
      (is (true? (v/ask? kb (list pred preferred identityAlias) 'CxUniverse))))))

(tu/deftest-kb a-forward-rewrite-consumer-constructs-the-public-endpoint-not-the-raw-payload
  ;; Ordinary unquoted conclusions could hide a raw binding by reifying it on write.
  ;; Constructing a mention makes that difference observable instead.
  (tu/with-terms [QualifierFn base namedRoot mentioned CxPrivate CxSibling]
    (quasiquote/ensure-quasiquote-functions kb)
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert-rule kb [(list 'rewriteOf namedRoot '?endpoint)]
                   (list mentioned (list 'Quasiquote (list 'Unquote '?endpoint)))
                   'CxUniverse {:direction :forward})
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn base)) CxPrivate)
    (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
    (is (false? (v/ask? kb (list mentioned (list 'Quote (list QualifierFn base))) CxPrivate)))
    (doseq [reader ['CxUniverse CxSibling]]
      (is (false? (v/ask? kb (list mentioned (list 'Quote namedRoot)) reader))))))
