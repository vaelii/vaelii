;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-protocol-test
  "`vaelii.impl.jtms-protocol/roles` against the `Tms` protocol it classifies.

  The protocol's docstring divides its methods into seven roles and states what each
  role holds, what supplies it and where it enters belief.  A docstring that says so and
  a protocol that grew a method since are two claims, not one, so the division is written
  as data beside the protocol and checked here.

  What this cannot check is whether a method is in the *right* role.  That stays review's,
  and the protocol docstring is written so a reviewer can do it: each role names what
  supplies its state, so a method is in the wrong role whenever its own docstring names a
  different supplier."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.impl.jtms-protocol :as tms-protocol]))

(defn- protocol-methods
  "The method names `Tms` defines, as the bare symbols `roles` names them by."
  []
  (into #{} (map (comp symbol name)) (keys (:sigs tms-protocol/Tms))))

(deftest every-tms-method-is-in-exactly-one-role
  (let [declared (protocol-methods)
        named    (apply set/union (vals tms-protocol/roles))]
    (is (= declared named)
        (str "a Tms method must be in exactly one `roles` entry — "
             "unclassified: " (sort (set/difference declared named))
             ", named but not a method: " (sort (set/difference named declared))))
    (doseq [[a xs] tms-protocol/roles
            [b ys] tms-protocol/roles
            :when  (neg? (compare (str a) (str b)))]
      (is (empty? (set/intersection xs ys))
          (str a " and " b " both name " (sort (set/intersection xs ys)))))
    (is (= (count declared) (reduce + (map count (vals tms-protocol/roles))))
        "the roles partition the method set, so the counts agree")))

(deftest the-three-overrides-are-their-own-roles
  ;; The three sets a caller replaces whole each settle enter belief at three different
  ;; points — `blocked` inside `valid?`, `defeated` inside the fixpoint, `superseded`
  ;; after both — so each is its own role rather than one "invalidation" or "arbitration"
  ;; group.  `vaelii.impl.jtms` states the three insertion points under *the state*.
  (doseq [r [:blocked :defeated :superseded]]
    (is (contains? tms-protocol/roles r) (str r " is a role of its own")))
  (is (= '#{-blocked -defeated -superseded}
         (into #{} (mapcat #(filter (set (get tms-protocol/roles %))
                                    ['-blocked '-defeated '-superseded]))
               [:blocked :defeated :superseded]))
      "each override's reader sits in its own role, not in :output"))
