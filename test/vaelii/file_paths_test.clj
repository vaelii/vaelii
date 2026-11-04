;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.file-paths-test
  "The file-path vocabulary of CxTra.  A reference is a filesystem namespace and an
  absolute path taken together, so one path in two namespaces is two references, and a
  grant of lookup in a namespace is an access kind that entails no read access."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(def ^:private terms
  '[filesystem_namespace file_path_reference file_lookup FilePathRefFn filePathRefOf
    pathNamespace pathText FileLookupFn fileLookupOf])

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(defn- desk!
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert kb (list 'genlCx ctx CPT) 'CxUniverse))

(tu/deftest-kb each-term-is-stated-in-the-theory-with-one-comment
  (doseq [t terms]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment t '?c) CPT)))
        (str t " carries one comment in the theory")))
  (is (holds-genl 'file_lookup 'resource_access CPT))
  (is (holds-genl 'file_path_reference 'linguistic CPT))
  (is (holds-genl 'filesystem_namespace 'intangible CPT)))

(tu/deftest-kb a-reference-is-read-back-as-its-namespace-and-its-path
  (tu/with-terms [CxDesk Inside Outside]
    (desk! kb CxDesk)
    (v/assert kb (list 'filesystem_namespace Inside) CxDesk)
    (v/assert kb (list 'filesystem_namespace Outside) CxDesk)
    (v/assert kb (list 'filePathRefOf Inside "/etc/hosts" (list 'FilePathRefFn Inside "/etc/hosts")) CxDesk)
    (v/assert kb (list 'filePathRefOf Outside "/etc/hosts" (list 'FilePathRefFn Outside "/etc/hosts")) CxDesk)
    ;; `ask` answers one literal, so the two readings are joined here
    (let [with-path (into #{} (map #(get % '?r))
                          (v/ask kb (list 'pathText '?r "/etc/hosts") CxDesk))
          refs      (fn [ns] (into #{} (comp (map #(get % '?r)) (filter with-path))
                                   (v/ask kb (list 'pathNamespace '?r ns) CxDesk)))]
      (testing "each namespace's reference reads back its namespace and its path"
        (is (= 1 (count (refs Inside))))
        (is (= 1 (count (refs Outside)))))
      (testing "one path in two namespaces is two references"
        (is (not= (refs Inside) (refs Outside)))))))

(tu/deftest-kb lookup-is-an-access-kind-that-entails-no-read
  (tu/with-terms [CxDesk Ann Inside]
    (desk! kb CxDesk)
    (v/assert kb (list 'human Ann) CxDesk)
    (v/assert kb (list 'filesystem_namespace Inside) CxDesk)
    (v/assert kb (list 'hasCapability Ann (list 'FileLookupFn Inside)) CxDesk)
    (is (holds-ask (list 'hasCapability Ann 'file_lookup) CxDesk))
    (is (holds-ask (list 'hasCapability Ann 'resource_access) CxDesk))
    (is (not (holds-ask (list 'hasCapability Ann 'read_access) CxDesk)))
    (is (seq (v/ask kb (list 'fileLookupOf Inside '?kind) CxDesk)))))
