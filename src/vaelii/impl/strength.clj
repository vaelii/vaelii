;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.strength
  "Assumption strengths and the derived defeat-class: two classes, `:monotonic` above
  `:default`, and a justification confers the minimum of its own strength and its
  antecedents' classes.  See docs/nmtms.md, \"Strengths and the defeat-class\"."
  (:refer-clojure :exclude [min max]))

(def assertable
  "The strengths a caller may put on an assertion."
  #{:monotonic :default})

(def ^:private rank    {:default 1 :monotonic 2})
(def ^:private by-rank {1 :default 2 :monotonic})

(defn rank-of "Numeric rank of a class (0 for unknown)." [class] (get rank class 0))
(defn class-of-rank [r] (get by-rank r :default))

(defn max "The stronger of two classes." [a b] (if (>= (rank-of a) (rank-of b)) a b))
(defn min "The weaker of two classes."   [a b] (if (<= (rank-of a) (rank-of b)) a b))

(defn defeasible? "Is this class a plain default (the only solver-eligible class)?"
  [class] (= class :default))
(defn known-true? "Is this class strong enough to never be sent to a solver?"
  [class] (= class :monotonic))
(defn assertable? [s] (contains? assertable s))
