;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.seed-test
  "Ontology KB files: declarative KB content held as plain text under resources/kb/.
  An upper file is named for its domain and loads into CxUniverse; a middle file is named
  for its context.  Every file present is discovered and loaded on kb start
  (vaelii.host.starter)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest the-kb-files-are-on-the-classpath
  (testing "the vocabulary file is read as a non-empty list of sentences"
    (let [ss (seed/read-sentences "core" "upper")]
      (is (seq ss))
      (is (every? seq? ss) "every form is an s-expression")))
  (testing "a layer file reads by name, as a symbol or a string, with or without .txt"
    (is (seq (seed/read-sentences 'CxBiology "middle")))
    (is (= (seed/read-sentences 'CxBiology "middle")
           (seed/read-sentences "CxBiology" "middle")
           (seed/read-sentences "CxBiology.txt" "middle")))))

(deftest every-file-in-a-layer-is-discovered
  ;; the point of layer discovery: a KB is added by dropping a file, no code change
  (testing "upper holds the domain files, sorted, and the loader reads core.txt first"
    (is (= ["abstract.txt" "core.txt" "life.txt" "measure.txt" "organism.txt"
            "reflection.txt" "society.txt" "space.txt" "time.txt"]
           (seed/layer-files "upper")))
    (is (= "core.txt" (first (core-context/upper-files)))))
  (testing "middle holds the theory contexts"
    (is (= '[CxAnatomy CxBiology CxChange CxKinship CxMereology
             CxNormalPhysicalConditions CxRealWorld CxSize CxSocial CxTra]
           (seed/layer-contexts "middle"))))
  (testing "an absent layer is nil, not a crash"
    (is (nil? (seed/layer-contexts "no-such-layer")))))

(deftest a-missing-kb-file-fails-loudly
  ;; a silently empty ontology is worse than a failure to start
  (testing "an absent context file throws rather than yielding nil"
    (is (thrown? clojure.lang.ExceptionInfo (seed/read-sentences 'CxNoSuch)))
    (is (thrown? clojure.lang.ExceptionInfo (seed/load-context nil 'CxNoSuch)))))

;; ---- a file's order is its terms', not its dependencies' ------------------

(tu/deftest-kb a-sentence-refused-for-what-has-not-arrived-yet-is-retried
  ;; The blocks of a KB file run in natural sort order, so it cannot also be
  ;; dependency-ordered: `(transitiveInArgInverse largerThan 1 tangiblePartOf)` is filed under
  ;; `largerThan` and `(transitive tangiblePartOf)` under `tangiblePartOf`, and `l` sorts before `t`.
  ;; The preservation's transitivity check reads the store, so in file order it is
  ;; refused — for where its author filed a sentence, which is not a property of the
  ;; knowledge.
  (tu/with-terms [largerThan1 partOf1 A1 B1 C1]
    (let [sentences [(list 'transitiveInArgInverse largerThan1 1 partOf1)  ; needs the next line
                     (list 'transitive partOf1)
                     (list partOf1 B1 C1)
                     (list partOf1 A1 B1)
                     (list largerThan1 C1 'thing)]]
      (testing "in that order, one at a time, the declaration is refused"
        (is (thrown? clojure.lang.ExceptionInfo
                     (doseq [s sentences] (v/assert kb s 'CxUniverse)))))
      (testing "and loaded as a file is loaded, every sentence lands"
        (seed/load-sentences kb sentences 'CxUniverse)
        (is (every? some? (map #(v/handle-of kb % 'CxUniverse) sentences)))
        (is (v/ask? kb (list largerThan1 A1 'thing) 'CxUniverse)
            "two hops, so the declaration is not merely stored but usable")))))

(tu/deftest-kb a-sentence-nothing-could-heal-still-throws
  ;; The retry is for a sentence waiting on its file, not an amnesty.  A round that
  ;; changes nothing re-asserts what is left without a catch, so the error that comes
  ;; out is the one the sentence has once everything that could help it is stored.
  (tu/with-terms [cursed2 begat2 dog2_t Nobody2]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"not transitive"
         (seed/load-sentences kb [(list 'transitiveInArgInverse cursed2 1 begat2)
                                  (list dog2_t Nobody2)]
                              'CxUniverse)))
    (testing "and what could load, did"
      (is (some? (v/handle-of kb (list dog2_t Nobody2) 'CxUniverse))))))

(tu/deftest-kb a-middle-file-loads-into-its-own-context
  ;; the file name is the context: CxBiology.txt lands in CxBiology, over the upper
  ;; layer, and its rules fire from the file
  (tu/load-core! kb)
  (seed/load-context kb 'CxBiology "middle")
  (testing "its sentences land in the context the file names"
    (is (seq (v/sentexes-matching kb '(capabilityType bird flying) 'CxBiology)))
    (is (empty? (v/sentexes-matching kb '(capabilityType bird flying) 'CxUniverse))))
  (testing "and its edges are stored in CxUniverse, where every edge is"
    (is (seq (v/sentexes-matching kb '(genlCx CxBiology CxUniverse) 'CxUniverse))))
  (testing "and its rules read the upper layer's genl closure"
    (tu/with-terms [Rex]
      (v/assert kb (list 'dog Rex) 'CxBiology)
      (is (v/isa? kb Rex 'organism 'CxBiology))
      (is (v/ask? kb (list 'mortal Rex) 'CxBiology)))))
