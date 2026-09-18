;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.qcn
  "The two relation-algebra operations over masks, as a held namespace
  (`vaelii.impl.types.prover` states what that means): the `IRelationOps` interface and its
  dense and sparse implementations, which `vaelii.impl.qcn` compiles an algebra into.
  The implementations are primitive loops over `long[]` tables and call no vaelii
  namespace, so their methods stay inline.")

;; The two table-driven operations, over masks.  A protocol rather than a pair of
;; closures so the calls in the tightening step are **primitive**: a Clojure function
;; taking and returning a long boxes both ways through `IFn.invoke`, which at one
;; composition per triple is the largest allocation left in a cubic loop — precisely what
;; masks are here to retire.
(definterface IRelationOps
  (^long compose [^long m1 ^long m2])
  (^long converse [^long m]))

(deftype DenseOps [^longs comp-tbl ^longs conv-tbl ^long size]
  IRelationOps
  ;; `comp-tbl` holds the composition of a single relation with any mask, so composing two
  ;; is one read per relation set on the left, and a converse is one read flat.
  (compose [_ m1 m2]
    (loop [a m1, acc 0]
      (if (zero? a)
        acc
        (let [i (Long/numberOfTrailingZeros a)]
          (recur (bit-and a (dec a))
                 (bit-or acc (aget comp-tbl (+ (* i size) m2))))))))
  (converse [_ m] (aget conv-tbl m)))

(defn- union-row
  "The union of `base[i][j]` over the relations set in `m`: one row of the base table,
  masked — the composition of a single relation with a whole constraint."
  ^long [^longs base ^long k ^long i ^long m]
  (loop [b m, acc 0]
    (if (zero? b)
      acc
      (let [j (Long/numberOfTrailingZeros b)]
        (recur (bit-and b (dec b))
               (bit-or acc (aget base (+ (* i k) j))))))))

(deftype SparseOps [^longs comp-base ^longs conv-base ^long k]
  IRelationOps
  ;; the fallback for an algebra too wide to hold a whole-mask table: the same unions, read
  ;; one base pair at a time rather than one row at a time.  Still no allocation.
  (compose [_ m1 m2]
    (loop [a m1, acc 0]
      (if (zero? a)
        acc
        (let [i (Long/numberOfTrailingZeros a)]
          (recur (bit-and a (dec a))
                 (bit-or acc (union-row comp-base k i m2)))))))
  (converse [_ m]
    (loop [a m, acc 0]
      (if (zero? a)
        acc
        (let [i (Long/numberOfTrailingZeros a)]
          (recur (bit-and a (dec a)) (bit-or acc (aget conv-base i))))))))
