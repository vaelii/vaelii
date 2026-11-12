;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.settle-skip-test
  "The rows a settle asks before it skips its pass (`settle/idle-conditions`) name every arm
  the pass calls.  The suite's cross-check (`settle/*check-skip?*`) holds a row to what its
  arms do, where a test reaches them; this holds the lists to `pass-work`'s body, so an arm
  added to the pass fails here before any write reaches it (docs/nmtms.md, \"A settle that
  owes nothing\")."
  (:require [clojure.repl :as repl]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.settle :as settle]))

(defn- calls
  "The vars `form`, read in `ns`, calls: each symbol heading a list that resolves to a
  function var outside `clojure.core`.  A macro is not a call, and the forms it wraps are
  read as any other."
  [ns form]
  (into #{}
        (comp (filter seq?)
              (keep #(when (symbol? (first %)) (ns-resolve ns (first %))))
              (filter var?)
              (remove #(:macro (meta %)))
              (remove #(= 'clojure.core (ns-name (:ns (meta %))))))
        (tree-seq coll? seq form)))

(deftest every-pass-call-names-a-row
  (let [ns    (the-ns 'vaelii.impl.settle)
        body  (binding [*ns* ns] (read-string (repl/source-fn 'vaelii.impl.settle/pass-work)))
        made  (calls ns body)
        named (into @#'settle/pass-reads (mapcat :arms) @#'settle/idle-conditions)]
    (testing "a call of `pass-work` no row names: add it to the rows it reads, or to `pass-reads`"
      (is (= #{} (into #{} (remove named) made))))
    (testing "a row or `pass-reads` names a var `pass-work` no longer calls"
      (is (= #{} (into #{} (remove made) named))))))

(deftest rows-asked-cheapest-first
  (let [order (zipmap @#'settle/cost-order (range))
        costs (map (comp order :cost) @#'settle/idle-conditions)]
    (is (every? some? costs))
    (is (= costs (sort costs)))
    (is (apply distinct? (map :id @#'settle/idle-conditions)))))
