;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.postings
  "The tiered handle posting — a sorted `int[]` while small, a `RoaringBitmap` past
  `promote` — and the intersections over it, as a held namespace
  (`vaelii.impl.types.prover` states what that means).  `IntPostings` mutates its own
  fields, which only its inline methods can do, so the type and the code it calls live
  here together.  The dense index backend (`vaelii.impl.dense-kv`), the columnar trie and
  the dense TMS's adjacency columns store their handle sets in it."
  (:import [java.util Arrays]
           [org.roaringbitmap RoaringBitmap]))

(def ^:const promote 128)   ; int[] → RoaringBitmap above this many entries (public for the oracle)

;; ---- IntPostings: a sorted int[] while small, a RoaringBitmap when hot ----

(defprotocol IPostings
  (padd!    [p h] "Add handle h (in place); return p.")
  (prem!    [p h] "Remove handle h (in place); return p.")
  (pcard    [p]   "Cardinality.")
  (pcontains? [p h]
    "Is handle h present?  A binary search on the `int[]`, or the bitmap's own test —
    the O(log n) / O(1) probe that answers membership without building the set
    `pmembers` builds, which is what an index gate calling it per firing needs.")
  (pmembers [p]   "A fresh Clojure set of the handles (as Longs).")
  (pints    [p]
    "A fresh sorted `int[]` of the handles — the boxing-free read, for a caller that
    iterates rather than set-tests.  Fresh (never the live array) because callers walk
    it while mutating the posting, which is exactly what `vaelii.impl.dense-jtms` does
    when it pushes a node's justifications onto a worklist.")
  (pseed [p]
    "This posting as an intersection accumulator — its own `int[]` or its own
    `RoaringBitmap`, handed back rather than copied.  Safe because `pand` allocates its
    result on every arm, so nothing downstream can write through it.")
  (pand [p acc]
    "`acc` — a sorted `int[]` or a `RoaringBitmap` — narrowed to the handles this posting
    also holds, as a **fresh** accumulator.  Dispatches on both representations: two hot
    postings meet in `RoaringBitmap/and`, two cold ones in a sorted merge, and a mixed
    pair probes the cold side's entries into the bitmap.  So neither side is materialized,
    and neither side is mutated — `RoaringBitmap.and` the *instance* method would mutate
    its receiver, and a query that quietly shrank a posting is a corrupt index the oracle
    finds late rather than never."))

(defn- ints->set [^ints a]
  (loop [i 0, s (transient #{})]
    (if (< i (alength a)) (recur (inc i) (conj! s (long (aget a i)))) (persistent! s))))

;; ---- the intersection arms ----------------------------------------------
;; Each takes ascending runs and returns a fresh ascending run, which is what keeps every
;; `pand` arm allocating (see the protocol) and lets the arms compose in any order.  There
;; are three, and which one runs is a property of the two *values*: a bitmap probe, a
;; sorted merge, or — for a lopsided pair with no bitmap between them — a binary search of
;; the short run into the long one.

(def ^:private ^:const gallop
  "How many times longer one run must be before its partner is *searched into* it rather
  than merged with it.  A merge is O(na+nb) and a search O(ns·log nb), so the crossover is
  where the ratio passes log of the long side — under 20 for anything that fits an `int`.
  32 sits past it with room, so the arm is taken only where it clearly wins."
  32)

(defn- ints-merge
  "The intersection of two ascending `int[]`s of comparable length — one pass over each."
  ^ints [^ints a ^ints b]
  (let [na (alength a), nb (alength b), out (int-array (min na nb))]
    (loop [i 0, j 0, k 0]
      (if (or (>= i na) (>= j nb))
        (Arrays/copyOf out (int k))
        (let [x (aget a (int i)), y (aget b (int j))]
          (cond (< x y) (recur (inc i) j k)
                (> x y) (recur i (inc j) k)
                :else   (do (aset out (int k) x) (recur (inc i) (inc j) (inc k)))))))))

(defn- ints-probe
  "The entries of ascending `small` that ascending `big` holds, each found by binary search
  with the window advancing — `big` is never walked, only searched.  This is the no-bitmap
  form of the same idea `ints-in-roaring` has, and it is what a mapped root run needs,
  since a snapshot's postings are plain sorted runs with no hot tier to probe."
  ^ints [^ints small ^ints big]
  (let [ns (alength small), nb (alength big), out (int-array ns)]
    (loop [i 0, lo 0, k 0]
      (if (or (>= i ns) (>= lo nb))
        (Arrays/copyOf out (int k))
        (let [x (aget small (int i))
              j (Arrays/binarySearch big (int lo) nb x)]
          (if (>= j 0)
            (do (aset out (int k) x) (recur (inc i) (inc j) (inc k)))
            (recur (inc i) (- (inc j)) k)))))))       ; miss ⇒ -(insertion point) - 1

(defn- ints-and
  "The intersection of two ascending `int[]`s, merged or searched by their length ratio."
  ^ints [^ints a ^ints b]
  (let [na (alength a), nb (alength b)]
    (cond
      (< (* gallop na) nb) (ints-probe a b)
      (< (* gallop nb) na) (ints-probe b a)
      :else                (ints-merge a b))))

(defn- ints-in-roaring
  "The entries of ascending `a` that `r` holds — one bitmap test apiece, so the bitmap is
  probed rather than enumerated.  This is the arm that makes a rare ∩ hot narrowing cost
  the rare side."
  ^ints [^ints a ^RoaringBitmap r]
  (let [n (alength a), out (int-array n)]
    (loop [i 0, k 0]
      (if (>= i n)
        (Arrays/copyOf out (int k))
        (let [x (aget a (int i))]
          (if (.contains r x)
            (do (aset out (int k) x) (recur (inc i) (inc k)))
            (recur (inc i) k)))))))

(deftype IntPostings [^:unsynchronized-mutable ^ints arr
                      ^:unsynchronized-mutable ^RoaringBitmap roar]
  IPostings
  (padd! [this h]
    (let [h (int h)]
      (if roar
        (.add roar h)
        (let [i (Arrays/binarySearch arr h)]
          (when (neg? i)                                   ; absent → insert (sorted)
            (let [ip (dec (- i)), n (alength arr), b (int-array (inc n))]
              (System/arraycopy arr 0 b 0 ip)
              (aset b ip h)
              (System/arraycopy arr ip b (inc ip) (- n ip))
              (if (> (inc n) promote)                      ; grew hot → become a bitmap
                (let [r (RoaringBitmap.)]
                  (dotimes [k (inc n)] (.add r (aget b k)))
                  (set! roar r) (set! arr nil))
                (set! arr b)))))))
    this)
  (prem! [this h]
    (let [h (int h)]
      (if roar
        (.remove roar h)
        (let [i (Arrays/binarySearch arr h)]
          (when (>= i 0)
            (let [n (alength arr), b (int-array (dec n))]
              (System/arraycopy arr 0 b 0 i)
              (System/arraycopy arr (inc i) b i (- n i 1))
              (set! arr b))))))
    this)
  (pcard [_] (long (if roar (.getCardinality roar) (alength arr))))
  (pcontains? [_ h]
    (let [h (int h)]
      (if roar (.contains roar h) (>= (Arrays/binarySearch arr h) 0))))
  (pmembers [_] (if roar (ints->set (.toArray roar)) (ints->set arr)))
  (pints [_] (if roar (.toArray roar) (aclone arr)))
  (pseed [_] (or roar arr))
  (pand [_ acc]
    (if roar
      (if (instance? RoaringBitmap acc)
        (RoaringBitmap/and ^RoaringBitmap acc roar)    ; both hot — the native ∧
        (ints-in-roaring acc roar))                    ; acc is the cold side — probe it in
      (if (instance? RoaringBitmap acc)
        (ints-in-roaring arr ^RoaringBitmap acc)       ; this side is cold, so ≤ `promote`
        (ints-and arr acc)))))

;; public: the columnar trie (vaelii.impl.columnar) reuses IntPostings for its leaf
;; handle sets — this is where Phase 1's postings and Phase 2's trie unify.
(defn int-postings [] (->IntPostings (int-array 0) nil))

(defn as-set [v] (if (instance? IntPostings v) (pmembers v) (or v #{})))

;; ---- intersection over the postings, not the sets they would make -------
;;
;; A posting here is an `IntPostings` or a bare ascending `int[]` (what a mapped run copies
;; out to — `vaelii.impl.dense-roots`), and the three helpers below are the generic form of
;; `pcard` / `pseed` / `pand` over both.  The accumulator is whatever the arms produce, an
;; `int[]` or a `RoaringBitmap`, and it is materialized into a Clojure set exactly once, at
;; the end, at the size of the *answer* rather than of the columns it came from.

(defn- card* ^long [p] (if (instance? IntPostings p) (pcard p) (alength ^ints p)))
(defn- seed* [p] (if (instance? IntPostings p) (pseed p) p))

(defn- and* [p acc]
  (if (instance? IntPostings p)
    (pand p acc)
    (if (instance? RoaringBitmap acc)
      (ints-in-roaring p ^RoaringBitmap acc)
      (ints-and p acc))))

(defn- acc-count ^long [acc]
  (if (instance? RoaringBitmap acc) (.getCardinality ^RoaringBitmap acc) (alength ^ints acc)))

(defn- acc->set [acc]
  (if (instance? RoaringBitmap acc) (ints->set (.toArray ^RoaringBitmap acc)) (ints->set acc)))

(defn intersect-postings
  "The intersection of `postings` — each an `IntPostings` or an ascending `int[]` — as a
  Clojure set of Longs.

  **Smallest first**, which is not the tie-break it looks like: the accumulator can only
  shrink, so seeding it with the narrowest column is what keeps every later step a probe of
  a few entries rather than a scan of a hot one.  An accumulator that empties stops the
  fold, since nothing after it can put a handle back.

  Public because `vaelii.impl.dense-roots` holds the same postings under its own keys and
  must narrow them the same way."
  [postings]
  (let [[p & more] (sort-by card* postings)]
    (acc->set
     (reduce (fn [acc q]
               (let [acc' (and* q acc)]
                 (if (zero? (acc-count acc')) (reduced acc') acc')))
             (seed* p)
             more))))

(defn postings-set
  "A posting — an `IntPostings` or an ascending `int[]` — as a fresh Clojure set of Longs,
  for the mixed fold a caller falls back to when one of the keys is not a handle family."
  [p]
  (if (instance? IntPostings p) (pmembers p) (ints->set p)))
