;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.causation-timing-test
  "A cause starts no later than its effect.

  CxUniverse's rule concludes `(instantNotAfter (StartFn C) (StartFn E))` from
  `(causes C E)`.  The point network reads the conclusion, so with `:point` registered a
  stated order that puts the effect's start before the cause's is a qualitative
  inconsistency.  Each test states its facts in its own context below CxUniverse, so one
  test's network cannot reach another's."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! (v/add-reasoner :point)))))
(use-fixtures :each (tu/neutral))

(defn- story!
  "A fresh context below CxUniverse, holding `facts`."
  [kb facts]
  (let [ctx (tu/tmp-ctx "Story")]
    (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
    (run! #(v/assert kb % ctx) facts)
    ctx))

(defn- consistent? [kb ctx] (:consistent? (v/qualitative-network kb :point ctx)))

(tu/deftest-kb a-cause-starts-no-later-than-its-effect
  (tu/with-terms [Spark Blaze]
    (let [ctx (story! kb [(list 'causal_event Spark)
                          (list 'event Blaze)
                          (list 'causes Spark Blaze)])]
      (is (true? (v/ask? kb (list 'instantNotAfter (list 'StartFn Spark) (list 'StartFn Blaze)) ctx))
          "the rule concludes the order of the two starts"))))

(tu/deftest-kb an-effect-that-started-before-its-cause-is-an-inconsistency
  (tu/with-terms [Flattery Singing Rolling Destruction Shove Fall]
    (testing "an effect starting first is refuted"
      (let [ctx (story! kb [(list 'causal_event Flattery)
                            (list 'event Singing)
                            (list 'instantBefore (list 'StartFn Singing) (list 'StartFn Flattery))
                            (list 'causes Flattery Singing)])]
        (is (false? (consistent? kb ctx)))))
    (testing "a cause that starts first and lasts past the effect's start is consistent"
      (let [ctx (story! kb [(list 'causal_event Rolling)
                            (list 'event Destruction)
                            (list 'instantBefore (list 'StartFn Rolling) (list 'StartFn Destruction))
                            (list 'instantAfter (list 'EndFn Rolling) (list 'StartFn Destruction))
                            (list 'causes Rolling Destruction)])]
        (is (true? (consistent? kb ctx)))))
    (testing "and so is a cause and an effect that start together"
      (let [ctx (story! kb [(list 'causal_event Shove)
                            (list 'event Fall)
                            (list 'instantEqual (list 'StartFn Shove) (list 'StartFn Fall))
                            (list 'causes Shove Fall)])]
        (is (true? (consistent? kb ctx)))))))
