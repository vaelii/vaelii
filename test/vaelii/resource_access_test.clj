;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.resource-access-test
  "The access vocabulary of CxTra.  A grant is a capability over a function term that
  keeps the resource, so `hasCapability` carries it up to its access kind; admin and
  deploy access each entail write access over the same resource by default, and no
  other kind entails another."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(def ^:private kinds '[resource_access read_access write_access shell_access admin_access deploy_access])

(def ^:private functions '[ReadAccessFn WriteAccessFn ShellAccessFn AdminAccessFn DeployAccessFn])

(def ^:private predicates '[readAccessOf writeAccessOf shellAccessOf adminAccessOf deployAccessOf custodianOf])

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(defn- desk!
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert kb (list 'genlCx ctx CPT) 'CxUniverse))

(tu/deftest-kb each-term-is-stated-in-the-theory-with-one-comment
  (doseq [t (concat kinds functions predicates)]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment t '?c) CPT)))
        (str t " carries one comment in the theory")))
  (doseq [k (rest kinds)]
    (is (holds-genl k 'resource_access CPT) (str k)))
  (is (holds-genl 'resource_access 'happening CPT))
  (testing "no access kind is a kind of another"
    (doseq [a (rest kinds) b (rest kinds) :when (not= a b)]
      (is (not (holds-genl a b CPT)) (str a " " b)))))

(tu/deftest-kb a-grant-reaches-its-kind-and-keeps-its-resource
  (tu/with-terms [CxDesk Ann Bo Box Repo]
    (desk! kb CxDesk)
    (v/assert kb (list 'human Ann) CxDesk)
    (v/assert kb (list 'human Bo) CxDesk)
    (v/assert kb (list 'computer Box) CxDesk)
    (v/assert kb (list 'hasCapability Ann (list 'ShellAccessFn Box)) CxDesk)
    (v/assert kb (list 'hasCapability Bo (list 'ReadAccessFn Repo)) CxDesk)
    (testing "the grant is answered for its resource, and carried up to the kinds"
      (is (holds-ask (list 'hasCapability Ann (list 'ShellAccessFn Box)) CxDesk))
      (is (holds-ask (list 'hasCapability Ann 'shell_access) CxDesk))
      (is (holds-ask (list 'hasCapability Ann 'resource_access) CxDesk)))
    (testing "the resource is kept: a grant over one resource is not one over another"
      (is (not (holds-ask (list 'hasCapability Ann (list 'ShellAccessFn Repo)) CxDesk))))
    (testing "shell access does not entail read access"
      (is (not (holds-ask (list 'hasCapability Ann 'read_access) CxDesk))))
    (testing "the corresponding predicate names the kind"
      (is (seq (v/ask kb (list 'shellAccessOf Box '?kind) CxDesk))))))

(tu/deftest-kb admin-and-deploy-access-each-entail-write-access-over-the-same-resource
  (tu/with-terms [CxDesk Ann Bo Cy Box Repo]
    (desk! kb CxDesk)
    (doseq [p [Ann Bo Cy]] (v/assert kb (list 'human p) CxDesk))
    (v/assert kb (list 'hasCapability Ann (list 'AdminAccessFn Box)) CxDesk)
    (v/assert kb (list 'hasCapability Bo (list 'DeployAccessFn Box)) CxDesk)
    (v/assert kb (list 'hasCapability Cy (list 'WriteAccessFn Repo)) CxDesk)
    (is (holds-ask (list 'hasCapability Ann (list 'WriteAccessFn Box)) CxDesk))
    (is (holds-ask (list 'hasCapability Bo (list 'WriteAccessFn Box)) CxDesk))
    (is (holds-ask (list 'hasCapability Ann 'write_access) CxDesk))
    (testing "over the same resource only"
      (is (not (holds-ask (list 'hasCapability Ann (list 'WriteAccessFn Repo)) CxDesk))))
    (testing "write access entails neither read nor admin access"
      (is (not (holds-ask (list 'hasCapability Cy 'read_access) CxDesk)))
      (is (not (holds-ask (list 'hasCapability Cy 'admin_access) CxDesk))))
    (testing "admin access does not entail shell access"
      (is (not (holds-ask (list 'hasCapability Ann 'shell_access) CxDesk))))))

(tu/deftest-kb each-access-function-names-its-corresponding-predicate
  ;; A function comes with the predicate relating its argument to its result, so a grant
  ;; is not sayable only as a function term.
  (is (= '{ReadAccessFn readAccessOf, WriteAccessFn writeAccessOf, ShellAccessFn shellAccessOf,
           AdminAccessFn adminAccessOf, DeployAccessFn deployAccessOf,
           MergeAccessFn mergeAccessOf}
         (into {} (for [b (v/ask kb '(functionCorrespondingPredicate ?f ?p) CPT)
                        :when (.endsWith (name (get b '?f)) "AccessFn")]
                    [(get b '?f) (get b '?p)])))))
