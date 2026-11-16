;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.call-caps
  "The late check of every `vaelii.impl.call-cap` cap, once per test JVM.  The `:test`
  profile's injection calls `install!`, which starts the count and wraps
  `clojure.test/run-tests` to run this namespace after every namespace it was given.
  `lein test` makes one `run-tests` call per JVM, so the check runs last in every CI shard.
  The check is `test-ns-hook`, which defines no test var, so test counts and `lein
  test-red`'s verdicts are unchanged.  Its failure sets `lein test`'s exit status."
  (:require [clojure.string :as str]
            [clojure.test :as t]
            [vaelii.impl.call-cap :as call-cap]))

(defonce ^:private testing-ns
  (atom nil))

(defn- caller
  "The test running now, or the namespace whose fixture is running."
  [_kb]
  (if-let [v (first t/*testing-vars*)]
    (str (symbol v))
    (str @testing-ns " (a fixture)")))

(defn- ns-sym [x]
  (if (instance? clojure.lang.Namespace x) (ns-name x) x))

(defn test-ns-hook
  "Require every KB's count under each name to be at most that name's cap.  A failure
  prints one line per name, first caller and count, with the number of KBs it covers and
  up to three of them."
  []
  (let [over  (filter #(and (:cap %) (> (:count %) (:cap %))) (call-cap/entries))
        lines (sort (for [[[n tag c cap] es] (group-by (juxt :name :tag :count :cap) over)]
                      (format "  %s %d/%d %s, %d KB(s): %s" n c cap tag (count es)
                              (str/join " " (take 3 (sort (map :kb es)))))))]
    (t/testing "every counted call stays within its cap on each KB"
      (t/is (empty? over)
            (str/join "\n" (cons "over-cap calls (name, count/cap, first caller, KBs):"
                                 lines))))))

(defn install!
  "Count every `call-cap` name from here on, tagging a KB with its first caller, and run
  this namespace last in every `clojure.test/run-tests` call."
  []
  (call-cap/count! caller)
  (alter-var-root #'t/test-ns
                  (fn [test-ns] (fn [ns] (reset! testing-ns (ns-sym ns)) (test-ns ns))))
  (alter-var-root #'t/run-tests
                  (fn [run-tests]
                    (fn [& nss]
                      (apply run-tests
                             (concat (remove #{'vaelii.call-caps} (map ns-sym (or (seq nss) [*ns*])))
                                     ['vaelii.call-caps])))))
  :installed)
