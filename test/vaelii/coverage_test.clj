;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.coverage-test
  "`scripts/coverage.sh`: the probe and the instrumentation its JVMs install, the hit
  files they write, and the sums `vaelii.coverage` reads back from them."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [vaelii.coverage :as cm]
            [vaelii.test-util :as tu])
  (:import (java.util.concurrent.atomic AtomicInteger)))

(defn- hits-files
  "Writes each element of `jvms`, a seq of `[lib file line hits]` rows standing for one
  JVM's instrumented forms, to its own hit file under `dir`, and returns the paths."
  [dir jvms]
  (vec (map-indexed
        (fn [i rows]
          (let [f (str (io/file dir (str i ".tsv.gz")))]
            (cm/write-hits-file f (for [[lib file line hits] rows]
                                    {:lib lib :file file :line line :hits (AtomicInteger. hits)}))
            f))
        jvms)))

(deftest merged-forms-sum-each-forms-hits-across-the-jvms
  (tu/with-tmp
    (fn [dir]
      (let [x  'vaelii.x
            fs (hits-files dir [[[x "vaelii/x.clj" 3 0] [x "vaelii/x.clj" 4 2] [x "vaelii/x.clj" nil 0]]
                                [[x "vaelii/x.clj" 3 5] [x "vaelii/x.clj" 4 0] [x "vaelii/x.clj" nil 0]]])]
        (is (= [{:tracked true :lib x :file "vaelii/x.clj" :line 3 :hits 5 :covered true}
                {:tracked true :lib x :file "vaelii/x.clj" :line 4 :hits 2 :covered true}
                {:tracked true :lib x :file "vaelii/x.clj" :line nil :hits 0 :covered false}]
               (cm/merged-forms fs)))))))

(deftest merged-forms-refuse-jvms-that-instrumented-different-forms
  (tu/with-tmp
    (fn [dir]
      (let [fs (hits-files dir [[['vaelii.x "vaelii/x.clj" 3 1]]
                                [['vaelii.x "vaelii/x.clj" 4 1]]])]
        (is (= :coverage-mismatch
               (try (cm/merged-forms fs)
                    nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))))

(deftest first-hit-cover-calls-cloverage-s-probe-once-per-form
  (let [calls (atom [])
        cover (cm/first-hit-cover #(swap! calls conj %) (boolean-array 4))]
    (doseq [idx [2 2 0 2 0 7 7]] (cover idx))
    (is (= [2 0 7 7] @calls))))

(deftest skipping-track-coverage-registers-every-form-and-probes-the-unskipped
  (let [registered (atom [])
        track      (fn [_line-hint form]
                     (let [idx (count (swap! registered conj form))]
                       (list 'capture (dec idx) form)))
        skip       (cm/skipping-track-coverage track #{1})]
    (is (= ['(capture 0 a) '(do b) '(capture 2 c)]
           (mapv #(skip 1 %) '[a b c])))
    (is (= '[a b c] @registered))))
