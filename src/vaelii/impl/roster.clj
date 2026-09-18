;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.roster
  "A **live-handle roster**: what `sentex-ids` / `justification-ids` / `premise-ids` hand
  back, for a store big enough that the shape matters.

  The three enumerations answer a `java.util.Set` of handles.  The memory store answers a
  `PersistentHashSet<Long>`, because that is what its own state already is; the disk store
  answers a `HandleRoster` snapshot of the `LiveRoster` below.  At the scale a durable or
  server-backed store exists for, the boxed shape *is* the cost: measured
  over contiguous handles, a `PersistentHashSet<Long>` retains **48–75 bytes per handle**
  (the hash trie's fill varies with cardinality), so **4.5–7.0 GB at 100M** — and
  `rebuild-tms` holds the sentex roster while it walks the premises and the
  justifications.

  Handles are minted in assertion order (`next-id`) from one counter across the three
  kinds, so a roster is a strided run of longs — holes where records were deleted, and
  holes where the other kinds' handles fall.  That is the one shape a compressed bitmap is
  built for.  Over the same handles with a tenth of them punched out, a `Roaring64Bitmap`
  retains **0.13–0.26 bytes per handle**, and less than that on an unbroken run, where
  the whole roster is a few run containers.  It answers `contains?` in *less* time than
  the hash set, not more (`vaelii.impl.protocols`, the enumeration contract).

  ## What this is not

  Not an `IPersistentSet`.  `conj`, `disj` and `clojure.set` need one, so a caller wanting
  those converts with `(set roster)` — which is the 4.5 GB, paid at the call site that
  asked for it rather than by every store on every enumeration.  The protocol promises
  membership, iteration, cardinality and ordering, which is what every caller in the
  engine uses.

  Immutable once built, so concurrent readers need no coordination — the one property the
  bitmap has to have here, since a store's readers enumerate while its writer writes.

  ## The live roster beside it

  A store that *answers* a roster also *holds* one, and that one is mutated on every put
  and every delete.  `LiveRoster` is the same bitmap kept in place for that.  The disk
  store holds four: the per-kind live-handle sets, where the `PersistentHashSet<Long>` they
  replace cost 48–75 bytes a handle — **9.47 GB at 100M records** (`docs/density.md`) —
  and the premise set, which was the same boxed set at **4.12 GB**.

  **It synchronizes nothing.**  A `Roaring64Bitmap` is mutable and not
  thread-safe, so every call here needs a monitor around it — and the monitor is the
  caller's, because the caller already has one.  The disk store mutates its live set under
  the owning kind's lock, in the same acquisition as the file write the set is a claim
  about (`vaelii.impl.disk.record-store`, \"two monitors\"); an internal lock would be a
  second, weaker one that still could not make the pair atomic.  So: **hold the lock that
  covers the field, for reads as well as writes.**  A tally and a first handle are reads
  that a boxed set needs no monitor for and this one does.

  A reader that outlives the call gets `live-snapshot`, an immutable `HandleRoster` over a
  copy: it costs the *bitmap's* size, not the corpus's, which is why handing one out is
  affordable where copying the boxed set was the thing to avoid.

  A held namespace (`vaelii.impl.types.prover` states what that means): it defines the `HandleRoster` and `LiveRoster` types, whose methods are inline, and requires no vaelii namespace, so the development browser's reloader never re-evaluates it, and an edit to it takes a restart."
  (:import [java.util Collection Iterator Set]
           [org.roaringbitmap.longlong LongIterator Roaring64Bitmap]))

(defn- long-of
  "`o` as a boxed long when it is an integer handle a `long` can hold, else nil.

  A roster is keyed by the *number*, so a handle boxed as an `Integer` and the same handle
  boxed as a `Long` are one member — the same normalization the SQL stores' fetch caches
  need one layer down.  An integer **too large for a long** answers nil rather than
  throwing: `contains?` on the Clojure set this replaces answers `false` for it, and a
  membership test that throws where the set said no is exactly the kind of difference this
  namespace exists not to have."
  ^Long [o]
  (cond
    (instance? Long o)    o
    (instance? Integer o) (Long/valueOf (.longValue ^Integer o))
    (integer? o)          (try (Long/valueOf (long o))
                               (catch IllegalArgumentException _ nil))
    :else                 nil))

(defn- long-iterator
  "The bitmap's handles as a `java.util.Iterator<Long>` — Roaring's own `LongIterator` is
  not one, and `iterator-seq`, `for` and the `Set` contract all want one."
  ^Iterator [^Roaring64Bitmap bits]
  (let [^LongIterator it (.getLongIterator bits)]
    (reify Iterator
      (hasNext [_] (.hasNext it))
      (next [_] (Long/valueOf (.next it))))))

(deftype HandleRoster [^Roaring64Bitmap bits ^long n]
  Set
  (size [_] (int n))
  (isEmpty [_] (zero? n))
  (contains [_ o] (boolean (when-let [v (long-of o)] (.contains bits (long v)))))
  (containsAll [_ c]
    (every? (fn [o] (boolean (when-let [v (long-of o)] (.contains bits (long v))))) c))
  (iterator [_] (long-iterator bits))
  (toArray [_] (.toArray ^Collection (vec (iterator-seq (long-iterator bits)))))
  (^objects toArray [_ ^objects a]
    ;; the `Collection` contract: fill `a` when it is long enough, else a fresh array,
    ;; and null-terminate a longer one.  Nothing in the engine calls this — it is here
    ;; because a `java.util.Set` that lies about `toArray` breaks the java-side callers
    ;; that make it worth being a `Set` at all.
    (let [xs           (vec (iterator-seq (long-iterator bits)))
          m            (count xs)
          ^objects out (if (>= (alength a) m) a (object-array m))]
      (dotimes [i m] (aset out i (nth xs i)))
      (when (> (alength out) m) (aset out m nil))
      out))
  (add [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (remove [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (addAll [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (removeAll [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (retainAll [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (clear [_] (throw (UnsupportedOperationException. "a handle roster is immutable")))

  ;; `seq`, `first` and `reduce` reach a roster through `Iterable` alone; `Seqable` and
  ;; `Counted` are here so they take the bitmap's own iteration and cardinality rather
  ;; than a wrapper and an int round trip.
  clojure.lang.Seqable
  (seq [_] (iterator-seq (long-iterator bits)))

  clojure.lang.Counted
  (count [_] (int n))

  ;; the `java.util.Set` contract: equal to any Set with the same members, hashing to the
  ;; sum of its members' hashes.  Clojure's `=` reaches these only from the java side —
  ;; with a Clojure set on either side it goes through `APersistentSet.equiv`, which tests
  ;; `size` and `contains` and so reads a roster without materializing one.
  Object
  (equals [_ o]
    (boolean (and (instance? Set o)
                  (= (int n) (.size ^Set o))
                  (every? (fn [x] (boolean (when-let [v (long-of x)]
                                             (.contains bits (long v)))))
                          ^Collection o))))
  (hashCode [_]
    (let [^LongIterator it (.getLongIterator bits)]
      (loop [h (int 0)]
        (if (.hasNext it) (recur (unchecked-add-int h (Long/hashCode (.next it)))) h))))
  (toString [_] (str "#vaelii/roster{" n " handles}")))

(defn roster
  "The handles in `ids` as a `HandleRoster`.  `ids` is anything reducible — a seq, a
  vector, an array — and need not arrive sorted."
  [ids]
  (let [b ^Roaring64Bitmap (Roaring64Bitmap.)]
    (reduce (fn [^Roaring64Bitmap acc id] (.addLong acc (long id)) acc) b ids)
    (.runOptimize b)
    (HandleRoster. b (.getLongCardinality b))))

(defn collector
  "A mutable `[add! finish]` pair, for a caller with a row loop rather than a reducible —
  a SQL store's cursor walk.  `add!` takes one handle; `finish` returns the immutable
  roster and is called once."
  []
  (let [b ^Roaring64Bitmap (Roaring64Bitmap.)]
    [(fn add! [id] (.addLong b (long id)) nil)
     (fn finish [] (.runOptimize b) (HandleRoster. b (.getLongCardinality b)))]))

(defn roster?
  "Is `x` one of these?  For a caller deciding whether `(set x)` would cost anything."
  [x]
  (instance? HandleRoster x))

;; ---- the live roster ----------------------------------------------------
;; The mutable half: a store's own live-handle set, not the value it hands out.  Every
;; function below is unsynchronized and expects the caller's monitor — see the "live
;; roster beside it" section of the namespace docstring for why that is the discipline
;; rather than an omission.

(deftype LiveRoster [^Roaring64Bitmap bits])

(defn live-roster
  "An empty live roster."
  ^LiveRoster [] (LiveRoster. (Roaring64Bitmap.)))

(defn live-add!
  "Add handle `id`, which must be an integer a `long` can hold — every caller is putting a
  handle the store itself minted, where `live-has?` and `live-remove!` take whatever a
  caller passed.  Returns nil."
  [^LiveRoster r id]
  (.addLong ^Roaring64Bitmap (.bits r) (long id))
  nil)

(defn live-add-all!
  "Add every handle in `ids` (anything reducible).  Returns nil."
  [^LiveRoster r ids]
  (let [b ^Roaring64Bitmap (.bits r)]
    (reduce (fn [_ id] (.addLong b (long id)) nil) nil ids))
  nil)

(defn live-remove!
  "Drop handle `id`, or do nothing when it is not a handle this roster could hold.  A
  no-op on a member it does not have, like the `disj` it replaces.  Returns nil."
  [^LiveRoster r id]
  (when-let [v (long-of id)]
    (.removeLong ^Roaring64Bitmap (.bits r) (long v)))
  nil)

(defn live-remove-all!
  "Drop every handle in `ids`.  Returns nil."
  [^LiveRoster r ids]
  (reduce (fn [_ id] (live-remove! r id)) nil ids)
  nil)

(defn live-has?
  "Is `id` live?  Answers false — never throws — for anything that is not a handle this
  roster could hold, which is what `contains?` on the set this replaces answers."
  [^LiveRoster r id]
  (boolean (when-let [v (long-of id)]
             (.contains ^Roaring64Bitmap (.bits r) (long v)))))

(defn live-tally
  "How many handles are live."
  ^long [^LiveRoster r]
  (.getLongCardinality ^Roaring64Bitmap (.bits r)))

(defn live-least
  "The smallest live handle, or nil when there is none.  A boxed set answers `first` with
  whichever handle its hash order puts in front; this answers the lowest.  Both satisfy
  the question the callers ask — *is there one at all* (`vaelii.impl.protocols`,
  `Tallying`) — and a determinate answer is the better one to give them."
  [^LiveRoster r]
  (let [b ^Roaring64Bitmap (.bits r)]
    (when-not (.isEmpty b) (Long/valueOf (.first b)))))

(defn live-clear!
  "Empty the roster in place.  Returns nil."
  [^LiveRoster r]
  (.clear ^Roaring64Bitmap (.bits r))
  nil)

(defn live-optimize!
  "Fold contiguous runs into run containers.  Worth calling once after a bulk build in
  ascending order — an open's idx scan — and not worth calling per write, since the next
  insert into a container undoes it.  Returns nil."
  [^LiveRoster r]
  (.runOptimize ^Roaring64Bitmap (.bits r))
  nil)

(defn live-snapshot
  "An immutable `HandleRoster` over a copy of `r` — what a reader that outlives the
  caller's monitor gets, and what an iteration that mutates the roster as it walks needs.
  Costs the bitmap's size rather than the corpus's."
  [^LiveRoster r]
  (let [b (doto (Roaring64Bitmap.) (.or ^Roaring64Bitmap (.bits r)))]
    (.runOptimize b)
    (HandleRoster. b (.getLongCardinality b))))
