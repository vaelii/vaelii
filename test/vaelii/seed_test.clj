;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.seed-test
  "Ontology KB files: declarative KB content held as plain text under resources/kb/,
  one file per context, the file name the context, the sub-directory the layer.
  Every context present is discovered and loaded on kb start (vaelii.host.starter)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.seed :as seed]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest the-kb-files-are-on-the-classpath
  (testing "the vocabulary head is indistinguishable from a non-empty list of sentences"
    (let [ss (seed/read-sentences 'CxCore)]
      (is (seq ss))
      (is (every? seq? ss) "every form is an s-expression")))
  (testing "a layer file reads by (context, dir), by symbol or string alike"
    (is (seq (seed/read-sentences 'CxOrganism "upper")))
    (is (= (seed/read-sentences 'CxOrganism "upper")
           (seed/read-sentences "CxOrganism" "upper")))))

(deftest every-context-in-a-layer-is-discovered
  ;; the point of layer discovery: a KB is added by dropping a file, no code change
  (testing "upper holds the definitional contexts, sorted"
    (is (= '[CxAbstract CxLife CxMeasure CxOrganism
             CxSociety CxSpace CxTime]
           (seed/layer-contexts "upper"))))
  (testing "middle holds the theory contexts"
    (is (= '[CxAnatomy CxBiology CxChange CxKinship
             CxMereology CxSize CxSocial]
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
  ;; dependency-ordered: `(transitiveInArg largerThan 1 partOf)` is filed under
  ;; `largerThan` and `(transitive partOf)` under `partOf`, and `l` sorts before `p`.
  ;; The preservation's transitivity check reads the store, so in file order it is
  ;; refused — for where its author filed a sentence, which is not a property of the
  ;; knowledge.
  (tu/with-terms [largerThan1 partOf1 A1 B1 C1]
    (let [sentences [(list 'transitiveInArg largerThan1 1 partOf1)  ; needs the next line
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
         (seed/load-sentences kb [(list 'transitiveInArg cursed2 1 begat2)
                                  (list dog2_t Nobody2)]
                              'CxUniverse)))
    (testing "and what could load, did"
      (is (some? (v/handle-of kb (list dog2_t Nobody2) 'CxUniverse))))))

(tu/deftest-kb a-layer-context-loads-into-its-own-context
  ;; the file name is the context — CxOrganism.txt lands in CxOrganism, on
  ;; top of the CxCore vocabulary, and the genl closure is built from the file.
  (seed/load-context kb 'CxCore)
  (seed/load-context kb 'CxOrganism "upper")
  (testing "its sentences land in the context the file names"
    (is (seq (v/sentexes-matching kb '(genl dog mammal) 'CxOrganism)))
    (is (empty? (v/sentexes-matching kb '(genl dog mammal) 'CxCore))))
  (testing "and the genl closure is built from the file"
    (tu/with-terms [Rex]
      (v/assert kb (list 'dog Rex) 'CxOrganism)
      (is (v/isa? kb Rex 'mammal))
      (is (v/isa? kb Rex 'animal))              ; the whole biological chain is in this one file
      (is (not (v/isa? kb Rex 'plant))))))
