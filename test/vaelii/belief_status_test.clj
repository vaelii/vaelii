;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.belief-status-test
  "Contextual belief introspection: raw IN, exception force, and inheritance stay
  distinct while the status report agrees with the boolean and matching surfaces."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest raw-in-doc-points-to-contextual-diagnostics
  (is (re-find #"belief-status" (:doc (meta #'v/in?)))
      "the raw-IN read points a caller at the diagnostic for contextual disagreement"))

(tu/deftest-kb contextual-belief-status-separates-every-gate
  (tu/with-terms [bright gem CxTop CxSibling CxLeaf]
    (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxSibling 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [inherit-h (v/assert kb (list 'genlCx CxLeaf CxTop) 'CxUniverse
                              {:strength :monotonic})
          h (v/assert kb (list bright gem) CxTop {:strength :monotonic})]
      (testing "belief does not imply assertion-context inheritance"
        (let [status (v/belief-status kb h CxSibling)]
          (is (v/believed? kb h CxSibling))
          (is (= true (:believed? status)))
          (is (false? (:visible? status)))
          (is (nil? (:inherited-path status)))
          (is (empty? (v/sentexes-matching kb (list bright gem) CxSibling)))))
      (testing "a visible inherited fact carries the exact genlCx support path"
        (let [status (v/belief-status kb h CxLeaf)]
          (is (= [{:handle inherit-h :context 'CxUniverse}]
                 (:inherited-path status)))
          (is (:visible? status))
          (is (= (:visible? status)
                 (v/ask? kb (list bright gem) CxLeaf)))))
      (testing "same-context inheritance is the empty path"
        (is (= [] (:inherited-path (v/belief-status kb h CxTop)))))
      (let [e2 (v/assert kb (list 'except (sx/sentex-handle h)) 'CxWell
                         {:strength :monotonic})
            e1 (v/assert kb (list 'except (sx/sentex-handle h)) CxTop
                         {:strength :monotonic})]
        (testing "raw IN remains true while a contextual exception removes belief"
          (let [status (v/belief-status kb h CxLeaf)]
            (is (v/in? kb h))
            (is (not (v/believed? kb h CxLeaf)))
            (is (= false (:believed? status) (:visible? status)))
            (is (:excepted? status))
            (is (= (sort-by str [CxTop 'CxWell])
                   (mapv #(-> (v/sentex kb (:handle %)) :context)
                         (:exceptions status))))
            (is (= status (v/belief-status kb h CxLeaf))
                "the branching forest is deterministic")))
        (testing "the cheap boolean makes one contextual exception query, not a global scan"
          (let [calls (atom 0)
                excepted? res/excepted?]
            (with-redefs [res/excepted-anywhere?
                          (fn [& _]
                            (throw (ex-info "believed? scanned every exception context" {})))
                          res/excepted?
                          (fn [& args]
                            (swap! calls inc)
                            (apply excepted? args))]
              (is (false? (v/believed? kb h CxLeaf)))
              (is (= 1 @calls)))))
        (let [m (v/assert kb (list 'except (sx/sentex-handle e1)) CxLeaf
                          {:strength :monotonic})]
          (testing "a meta-except restores one branch but another live branch still hides"
            (let [status (v/belief-status kb h CxLeaf)
                  roots  (into {} (map (juxt :handle identity)) (:exceptions status))]
              (is (= [{:handle m :in? true :in-force? true :excepted-by []}]
                     (:excepted-by (get roots e1))))
              (is (false? (:in-force? (get roots e1))))
              (is (:in-force? (get roots e2)))
              (is (:excepted? status))))
          (v/retract! kb e2)
          (testing "with the other branch gone, the meta-except restores belief"
            (let [status (v/belief-status kb h CxLeaf)]
              (is (v/believed? kb h CxLeaf))
              (is (= true (:believed? status) (:visible? status)))
              (is (false? (:excepted? status))))))))))

(tu/deftest-kb status-covers-out-absent-and-malformed-handles
  (tu/with-terms [flies Tweety CxStatus]
    (v/assert kb (list 'genlCx CxStatus 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list flies Tweety) CxStatus {:strength :default})]
      (v/assert kb (list 'not (list flies Tweety)) CxStatus {:strength :monotonic})
      (testing "a defeated sentex is stored but OUT"
        (let [status (v/belief-status kb h CxStatus)]
          (is (:stored? status))
          (is (false? (:in? status)))
          (is (false? (:believed? status)))
          (is (false? (:visible? status)))))
      (testing "nil and an unknown integer without dangling exceptions are all false"
        (doseq [handle [nil 999999999]]
          (let [status (v/belief-status kb handle CxStatus)]
            (is (= handle (:handle status)))
            (is (false? (:stored? status)))
            (is (false? (:in? status)))
            (is (nil? (:assertion-context status)))
            (is (= [] (:exceptions status)))
            (is (false? (:excepted? status)))
            (is (nil? (:inherited-path status)))
            (is (false? (:believed? status)))
            (is (false? (:visible? status)))
            (is (false? (v/believed? kb handle CxStatus))))))
      (testing "a dangling exception remains diagnosable without making its target stored"
        (let [missing 999999999
              eh (v/assert kb (list 'except (sx/sentex-handle missing)) CxStatus
                           {:strength :monotonic})
              status (v/belief-status kb missing CxStatus)]
          (is (false? (:stored? status)))
          (is (false? (:in? status)))
          (is (= [eh] (mapv :handle (:exceptions status))))
          (is (:excepted? status))
          (is (false? (:believed? status)))
          (is (false? (:visible? status)))))
      (testing "malformed handles keep the established typed refusal"
        (doseq [f [v/believed? v/belief-status]]
          (let [e (try (f kb [h] CxStatus) nil (catch clojure.lang.ExceptionInfo e e))]
            (is (= :bad-handle (:type (ex-data e))))))))))

(tu/deftest-kb exception-forest-order-follows-content-not-allocation
  (tu/with-terms [glows Alpha Beta CxA CxB CxReader]
    (v/assert kb (list 'genlCx CxReader CxA) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxReader CxB) 'CxUniverse {:strength :monotonic})
    (let [h1 (v/assert kb (list glows Alpha) CxReader {:strength :monotonic})
          h2 (v/assert kb (list glows Beta) CxReader {:strength :monotonic})]
      ;; Same semantic branches, opposite assertion order.
      (v/assert kb (list 'except (sx/sentex-handle h1)) CxA {:strength :monotonic})
      (v/assert kb (list 'except (sx/sentex-handle h1)) CxB {:strength :monotonic})
      (v/assert kb (list 'except (sx/sentex-handle h2)) CxB {:strength :monotonic})
      (v/assert kb (list 'except (sx/sentex-handle h2)) CxA {:strength :monotonic})
      (let [contexts (fn [h]
                       (mapv #(-> (v/sentex kb (:handle %)) :context)
                             (:exceptions (v/belief-status kb h CxReader))))]
        (is (= (sort-by str [CxA CxB]) (contexts h1) (contexts h2)))))))

(tu/deftest-kb linear-meta-except-chain-is-evaluated-once-per-node
  (tu/with-terms [rings Bell CxChain]
    (let [target (v/assert kb (list rings Bell) CxChain {:strength :monotonic})
          depth 40]
      (loop [target target, n depth]
        (when (pos? n)
          (recur (v/assert kb (list 'except (sx/sentex-handle target)) CxChain
                           {:strength :monotonic})
                 (dec n))))
      (let [reads (atom 0)
            in? jtms/in?
            status (with-redefs [jtms/in? (fn [& args]
                                            (swap! reads inc)
                                            (apply in? args))]
                     (v/belief-status kb target CxChain))
            node-count (fn node-count [nodes]
                         (+ (count nodes)
                            (reduce + 0 (map #(node-count (:excepted-by %)) nodes))))]
        (is (= depth (node-count (:exceptions status))))
        (is (<= @reads (+ depth 2))
            "one raw target read plus at most one cascade read per exception")))))
