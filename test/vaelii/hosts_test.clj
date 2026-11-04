;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.hosts-test
  "The hosts vocabulary of CxTra: computers, the computational systems that run on them,
  and the clusters, networks and namespaces that group them.  `runsOn` is transitive and
  carries no other fact, and a host name is a string that equates nothing."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(def ^:private kinds
  '[computer virtual_machine software_container software_service mcp_server
    kubernetes_cluster network kubernetes_namespace])

(def ^:private relations
  '[runsOn clusterNode controlPlaneNode workerNode onNetwork kubernetesNamespaceOf hostnameOf])

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(defn- problem-types
  "The `:type` of each problem `check` reports for `sentence` in `ctx`, or of the argument
  conviction `assert` holds it inert under, under the constraint-only reading."
  [sentence ctx]
  (tu/without-entailing
   (or (not-empty (mapv :type (v/check tu/*kb* sentence ctx)))
       (into [] (keep :type) [(tu/write-conviction tu/*kb* sentence ctx)]))))

(defn- desk!
  "A context under CxWell and CxTra, as a user's own context opts in."
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert kb (list 'genlCx ctx CPT) 'CxUniverse))

(tu/deftest-kb each-term-is-stated-in-the-theory-with-one-comment
  (doseq [t (concat kinds relations)]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment t '?c) CPT)))
        (str t " carries one comment in the theory")))
  (doseq [k kinds]
    (is (holds-genl k 'thing CPT) (str k " reaches thing from the theory"))
    (is (not (holds-genl k 'thing 'CxWell)) (str k " is not placed in CxWell"))))

(tu/deftest-kb the-placements-and-the-separations
  (testing "hardware is an electronic device and the rest are computational systems"
    (is (holds-genl 'computer 'electronic_device CPT))
    (doseq [k '[virtual_machine software_container software_service kubernetes_cluster]]
      (is (holds-genl k 'computational_system CPT) (str k)))
    (is (holds-genl 'mcp_server 'software_service CPT))
    (is (holds-genl 'network 'intangible CPT))
    (is (holds-genl 'kubernetes_namespace 'intangible CPT)))
  (testing "a virtual machine, a container and a service are three things"
    (is (v/disjoint? kb 'virtual_machine 'software_container CPT))
    (is (v/disjoint? kb 'software_container 'software_service CPT))
    (is (v/disjoint? kb 'virtual_machine 'software_service CPT)))
  (testing "hardware is not a computational system, and a person is not a computer"
    (is (v/disjoint? kb 'computer 'computational_system CPT))
    (is (v/disjoint? kb 'person 'computer CPT))))

(tu/deftest-kb runs-on-composes-and-carries-nothing-else
  (tu/with-terms [CxDesk Box Guest Pod Svc]
    (desk! kb CxDesk)
    (v/assert kb (list 'computer Box) CxDesk)
    (v/assert kb (list 'virtual_machine Guest) CxDesk)
    (v/assert kb (list 'software_container Pod) CxDesk)
    (v/assert kb (list 'software_service Svc) CxDesk)
    (v/assert kb (list 'runsOn Svc Pod) CxDesk)
    (v/assert kb (list 'runsOn Pod Guest) CxDesk)
    (v/assert kb (list 'runsOn Guest Box) CxDesk)
    (v/assert kb (list 'hostnameOf Pod "pod-1") CxDesk)
    (testing "location composes"
      (is (holds-ask (list 'runsOn Svc Box) CxDesk))
      (is (holds-ask (list 'runsOn Pod Box) CxDesk)))
    (testing "a name read inside the container is not concluded of its host"
      (is (not (holds-ask (list 'hostnameOf Guest "pod-1") CxDesk)))
      (is (not (holds-ask (list 'hostnameOf Box "pod-1") CxDesk))))))

(tu/deftest-kb two-systems-that-share-a-name-are-not-one
  (tu/with-terms [CxDesk Left Right]
    (desk! kb CxDesk)
    (v/assert kb (list 'computer Left) CxDesk)
    (v/assert kb (list 'computer Right) CxDesk)
    (v/assert kb (list 'hostnameOf Left "web") CxDesk)
    (v/assert kb (list 'hostnameOf Right "web") CxDesk)
    (v/assert kb (list 'hostnameOf Left "web-a") CxDesk)
    (is (holds-ask (list 'hostnameOf Left "web") CxDesk))
    (is (holds-ask (list 'hostnameOf Right "web") CxDesk))
    (is (holds-ask (list 'hostnameOf Left "web-a") CxDesk) "one thing answers to two names")
    (is (not (holds-ask (list 'equals Left Right) CxDesk)))
    (is (not (tu/stored-in-clash? kb (list 'hostnameOf Left "web-a") CxDesk)))))

(tu/deftest-kb a-role-in-a-cluster-is-membership
  (tu/with-terms [CxDesk Cluster Ctl Worker Box Lan Ns]
    (desk! kb CxDesk)
    (v/assert kb (list 'kubernetes_cluster Cluster) CxDesk)
    ;; a node is the operating system install the node agent runs in, which runs on a
    ;; computer for a bare-metal node
    (v/assert kb (list 'computer Box) CxDesk)
    (v/assert kb (list 'computational_system Ctl) CxDesk)
    (v/assert kb (list 'computational_system Worker) CxDesk)
    (v/assert kb (list 'runsOn Ctl Box) CxDesk)
    (v/assert kb (list 'controlPlaneNode Cluster Ctl) CxDesk)
    (v/assert kb (list 'workerNode Cluster Worker) CxDesk)
    (v/assert kb (list 'onNetwork Ctl Lan) CxDesk)
    (v/assert kb (list 'kubernetesNamespaceOf Ns Cluster) CxDesk)
    (is (holds-ask (list 'clusterNode Cluster Ctl) CxDesk))
    (is (holds-ask (list 'clusterNode Cluster Worker) CxDesk))
    (is (not (holds-ask (list 'workerNode Cluster Ctl) CxDesk)))
    (tu/with-entailing
      (v/assert kb (list 'onNetwork Worker Lan) CxDesk)
      (v/assert kb (list 'kubernetesNamespaceOf Ns Cluster) CxDesk))
    (testing "a computer is not a node: the node runs on it"
      (is (= [:arg-type] (problem-types (list 'clusterNode Cluster Box) CxDesk))))
    (testing "the declared argument types are derived"
      (is (v/isa? kb Lan 'network CxDesk))
      (is (v/isa? kb Ns 'kubernetes_namespace CxDesk)))))
