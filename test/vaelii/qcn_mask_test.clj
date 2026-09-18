;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-mask-test
  "The bitmask compilation, held against the algebra it was compiled from.

  `qcn` runs its pass over bitmasks: a constraint is the bits of a long, composition and
  converse are table reads, and the tables are built by dynamic programming over the
  *base* relations — `f(s) = f(s minus its lowest relation) | f(that relation)`.  That
  recurrence is only valid because composition and converse distribute over union, which
  is true of every algebra here by construction and is exactly the kind of assumption that
  fails silently: a wrong table entry is a wrong *entailment*, reported with as much
  confidence as a right one, never a crash.

  So the tables are checked against the algebra's own set-valued `:compose` and
  `:converse`, which share no code with them.  Exhaustively where the relation count
  allows, and over a deterministic sample where 2^k squared does not.

  Both table strategies are covered: the six shipped calculi all take the **dense**
  whole-mask table, so a synthetic algebra wide enough to fall back to the base-table loop
  stands in for the other branch."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.distance :as dist]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.orientation :as dir]
            [vaelii.impl.point :as pt]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.relative :as rel]
            [vaelii.impl.space :as space])
  (:import [vaelii.impl.types.qcn IRelationOps]))

(def ^:private compile-algebra #'qcn/compile-algebra)

(defn- composed
  "The compiled composition of two masks."
  [compiled ^long m1 ^long m2]
  (.compose ^IRelationOps (:ops compiled) m1 m2))

(defn- conversed
  "The compiled converse of a mask."
  [compiled ^long m]
  (.converse ^IRelationOps (:ops compiled) m))

(def algebras
  "Every shipped algebra, by name."
  {:rcc8     space/rcc8-algebra
   :allen    iv/allen-algebra
   :cardinal dir/direction-algebra
   :relative rel/relative-algebra
   :distance dist/distance-algebra
   :point    pt/point-algebra})

(defn- masks
  "Every mask of a `k`-relation algebra."
  [k]
  (range (bit-shift-left 1 k)))

(defn- sample-masks
  "`n` masks drawn deterministically from a `k`-relation algebra — a fixed seed, so a
  failure is reproducible and a passing run is not luck that varies per build."
  [k n seed]
  (let [rnd (java.util.Random. seed)
        hi  (bit-shift-left 1 k)]
    (repeatedly n #(.nextInt rnd hi))))

;; ---- the round trip ------------------------------------------------------

(deftest every-mask-decodes-to-the-set-that-encodes-to-it
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [encode decode universe identity]} (compile-algebra algebra)
            k (count (:universe algebra))]
        (is (= (:universe algebra) (decode universe))
            "the universe mask decodes to the algebra's universe")
        (is (= (:identity algebra) (decode identity))
            "the identity mask decodes to the algebra's identity")
        (is (= #{} (decode 0)) "the empty mask is the empty constraint")
        (doseq [m (masks k)]
          (is (= m (encode (decode m)))
              (str "mask " m " round-trips through its relation set")))))))

;; ---- the tables ----------------------------------------------------------

(deftest converse-agrees-with-the-algebra-on-every-constraint
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [decode] :as compiled} (compile-algebra algebra)
            set-converse (:converse algebra)
            k (count (:universe algebra))]
        (doseq [m (masks k)]
          (let [s (decode m)]
            (is (= (set-converse s) (decode (conversed compiled m)))
                (str "converse of " s))))))))

(deftest composition-agrees-with-the-algebra-on-every-pair-of-base-relations
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [encode decode] :as compiled} (compile-algebra algebra)
            set-compose (:compose algebra)]
        (doseq [a (:universe algebra)
                b (:universe algebra)]
          (is (= (set-compose #{a} #{b})
                 (decode (composed compiled (encode #{a}) (encode #{b}))))
              (str "compose " a " " b)))))))

(deftest ^:slow composition-agrees-with-the-algebra-on-whole-constraints
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [decode] :as compiled} (compile-algebra algebra)
            set-compose (:compose algebra)
            k    (count (:universe algebra))
            ;; exhaustive where 2^k squared is small enough to be honest work, and a
            ;; deterministic sample where it is not — the base-pair test above already
            ;; covers every table entry the whole-mask one is built from.
            pairs (if (<= k 7)
                    (for [a (masks k) b (masks k)] [a b])
                    (map vector (sample-masks k 4000 42) (sample-masks k 4000 4242)))]
        (doseq [[a b] pairs]
          (let [sa (decode a) sb (decode b)]
            (is (= (set-compose sa sb) (decode (composed compiled a b)))
                (str "compose " sa " " sb))))))))

;; ---- the two table strategies --------------------------------------------

(deftest the-two-numbers-that-bound-this-layer-are-the-documented-ones
  ;; Neither is a cache — nothing is held and nothing is evicted — so neither has a row
  ;; on the caches page, and docs/qcn.md ("Two numbers bound this layer, and neither is a
  ;; cache") is where a reader meets them instead.  The tests below spell the threshold
  ;; out again as an arithmetic bound, so a constant that moved with nothing else moving
  ;; would leave three readings disagreeing rather than one.
  (is (= 62 @#'qcn/max-base-relations)
      "a constraint is the bits of a long, and 62 is what one holds")
  (is (= (bit-shift-left 1 18) @#'qcn/dense-table-limit)
      "the whole-mask composition table is built at or under this many entries"))

(deftest every-shipped-algebra-takes-the-dense-table
  (testing "the whole-mask table is affordable for all six, Allen's thirteen included"
    (doseq [[nm algebra] algebras]
      (let [k (count (:universe algebra))]
        (is (<= (* k (bit-shift-left 1 k)) (bit-shift-left 1 18))
            (str (name nm) " has " k " base relations, whose whole-mask table is "
                 (* k (bit-shift-left 1 k)) " entries"))))))

(def ^:private wide-relations
  "Sixteen base relations — enough that the whole-mask table (16 × 65536 entries) is over
  the limit, so a compiled algebra of them takes the base-table loop instead."
  (vec (map #(keyword (str "r" %)) (range 16))))

(def ^:private wide-base
  "A composition table over them.  It need not be a *sound* algebra — this is a test of
  the compilation, and what the compilation must reproduce is the union over base pairs,
  whatever those pairs compose to.  Deterministic, so the table is the same every run."
  (let [rnd (java.util.Random. 7)]
    (into {} (for [a wide-relations]
               [a (into {} (for [b wide-relations]
                             [b (into #{} (remove nil?)
                                      (map (fn [r] (when (.nextBoolean rnd) r))
                                           wide-relations))]))]))))

(def ^:private wide-converse
  "Its converse: the relations paired off end to end, so the map is a permutation and the
  converse of a set is the union of its members' — which is all the compilation assumes."
  (into {} (map-indexed (fn [i r] [r (nth wide-relations (- 15 i))])) wide-relations))

(def ^:private wide-algebra
  {:universe (set wide-relations)
   :identity #{(first wide-relations)}
   :compose  (fn [s1 s2]
               (into #{} (mapcat (fn [a] (mapcat #(get-in wide-base [a %]) s2))) s1))
   :converse (fn [s] (into #{} (map wide-converse) s))})

(deftest a-wide-algebra-falls-back-to-the-base-table-and-still-agrees
  (testing "sixteen relations is past the dense limit"
    (is (> (* 16 (bit-shift-left 1 16)) (bit-shift-left 1 18))))
  (let [{:keys [decode] :as compiled} (compile-algebra wide-algebra)
        set-compose  (:compose wide-algebra)
        set-converse (:converse wide-algebra)]
    (testing "converse over a deterministic sample"
      (doseq [m (sample-masks 16 2000 11)]
        (is (= (set-converse (decode m)) (decode (conversed compiled m))))))
    (testing "composition over a deterministic sample"
      (doseq [[a b] (map vector (sample-masks 16 3000 13) (sample-masks 16 3000 17))]
        (is (= (set-compose (decode a) (decode b))
               (decode (composed compiled a b))))))))

(deftest an-algebra-wider-than-a-mask-is-refused-rather-than-truncated
  (let [too-many (into #{} (map #(keyword (str "r" %))) (range 70))]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"base relations"
         (compile-algebra {:universe too-many
                           :identity #{:r0}
                           :compose  (fn [_ _] too-many)
                           :converse identity})))))
