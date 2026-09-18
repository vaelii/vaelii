;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-jtms
  "The dense truth-maintenance network — the `:tms :dense` option, the default since
  0.9.0 (it holds the network in ~3.8× less RAM at corpus scale; docs/density.md).

  The JTMS is **always resident**, so its footprint is a wall in its own right
  (measured: ~467 B/node, which is ~43 GB at 100M nodes), and the decomposition
  (`lein bench-jtms`) says exactly where the bytes are:

  ```
    nodes  71%   <- 310 B/node of it is the per-node MAP OBJECT and its HAMT slot
    in     13%   <- 100% dense; RoaringBitmap measured 384x here
    groundable 13%
  ```

  Two findings shape everything below.  **The per-node scalars are already free** —
  stripping `:depth`, `:premise?` or `:datum` from the reference releases *nothing*,
  because they are shared cached objects (small `Long`s, keywords, booleans).  So the
  lever is not \"shrink the fields\", it is \"stop having a map per node\": a node here
  is a bit in a bitmap and, where it has one, an entry in a primitive-keyed map.  And
  **belief sets are the opposite regime from the index's postings** — `bench-postings`
  found RoaringBitmap a *loss* (1.07-1.45x) on the index's millions of tiny postings,
  while `:in` holds nearly every node and compresses 384x.  Both measurements are
  right; density is the variable.

  ```
    nodes / premises / in / groundable / defeated / blocked
    touched / touched-in / touched-new                         RoaringBitmap
    depths                                    Int2IntOpenHashMap  (absent => 0)
    supports / consequences   Int2ObjectOpenHashMap<IntPostings>  (absent => empty)
    a justification            columns keyed by id, never an object  (see below)
    superseded                             atom of a persistent map  (sparse)
  ```

  The depths, the two adjacency maps and the three justification columns keyed by id are
  the fact-scaled half of that table, and the network reaches them through the
  `TmsColumns` interface rather than as fields.  `HeapColumns` holds them in the fastutil
  maps above.  Every relabel, sweep and mutation below is written once against the
  interface, so an implementation that holds the six elsewhere runs the same fixpoint.

  Two of those deserve their reasons.  **The defeat-classes are one bitmap** because
  the lattice has exactly two elements (`vaelii.impl.strength` — monotonic > default,
  and the reference already stores only the entries *above* the bottom), so \"the
  class map\" is precisely \"the set of monotonic datums\".  **Adjacency reuses Phase
  1's `IntPostings`** (a sorted `int[]` promoted to a bitmap past 128) rather than a
  bare `int[]`: a node's supports are usually one or two, but the *consequences* of a
  much-used premise — a rule's node lists every justification it licensed — grow
  without bound, and an array-copy insert would make loading such a
  rule quadratic.

  ## Why this is a second implementation and not a swap

  `RoaringBitmap` is mutable, and the reference is an atom over one persistent map
  whose all-or-nothing mutation `jtms_atomicity_test` pins.  A mutable bitmap inside
  that value would break `swap!`'s retry semantics and let a reader observe a
  half-applied relabel — so the dense structures cannot be dropped into the reference,
  and the two ship side by side behind `vaelii.impl.jtms-protocol/Tms`.  That is the same shape
  the index took (`:memory-columnar` is a whole second trie beside `KvIndexStore`),
  and it carries the same obligation: the algorithms are duplicated here against the
  dense structures, so `jtms_dense_oracle_test` proves the two answer identically
  under randomized operation streams before either is trusted.

  **Concurrency.** A `StampedLock` gives the incidental reader the consistent view the
  single-writer contract owes one — \"a reader thread beside a writer thread (the web
  browser over a REPL's KB) is the supported shape\" (docs/storage.md), and the atom-
  over-persistent-map reference gives that reader a consistent view for free.  The dense
  network mutates its bitmaps in place, so it earns the same guarantee with a lock, and
  the lock is chosen so the engine's own single writer never pays for it.  Writers take
  the exclusive stamp — serializing exactly as the reference's `swap!` retry does.  Point
  reads (`in?`, the hottest call in the engine, one per candidate on the match path) run
  **optimistically**: no lock in the steady state, since writes are bursty and reads are
  the hot path, validated after the fact and redone under a shared read stamp only if a
  write intervened or the lock-free read saw torn state.  Iterating reads take the shared
  stamp directly — they already allocate O(nodes), so the acquisition disappears into the
  materialization, and an unlocked walk over a bitmap a writer is rewriting in place could
  tear.  A reader never observes a partially-applied relabel; it sees the state either
  fully before or fully after, exactly as it would on the reference.  The lock is
  **non-reentrant**: every protocol method below takes a stamp once and calls only
  raw-field helpers (no method re-enters), and every read body is side-effect-free (so the
  optimistic retry is safe).

  **Precondition.** `ensure-node` precedes `add-justification`, and a justification's
  antecedents already have nodes — which every engine path does.  (The reference
  tolerates the violation by growing a malformed phantom node; neither implementation
  is specified there.)

  **Limit.** The bitmaps and the fastutil maps are `int`-keyed, so a handle or
  justification id must fit a 32-bit int: the ceiling is 2^31-1 = 2,147,483,647.
  Handles are allocated in assertion order and never reused, so this bounds a KB's
  *cumulative* allocations (~2.1B), not its live node count — 21x the engine's 100M
  target, but reachable by a long-lived writer that churns assert/retract for long
  enough.  Crossing it throws `:type :handle-ceiling`, an actionable error naming the
  ceiling and carrying `:remedy {:tms :reference}` (`check-handle!`, at the two entry
  points a new id enters), rather than the bare \"integer overflow\" the cast would raise — and never a silent truncation
  that would collide two handles, so belief is never corrupted.  A KB that expects to
  churn past 2^31 pins `{:tms :reference}`, whose `Long`-keyed persistent maps have no
  such ceiling.  This is measured in density.md."
  (:require [taoensso.nippy :as nippy]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.jtms-protocol :refer [Tms]]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.postings :as postings]
            [vaelii.impl.types.tms :as tms-types])
  (:import [it.unimi.dsi.fastutil.ints Int2IntOpenHashMap Int2ObjectOpenHashMap]
           [java.io DataInput DataOutput]
           [java.util Arrays]
           [java.util.concurrent.locks StampedLock]
           [org.roaringbitmap RoaringBitmap]
           [vaelii.impl.types.tms HeapColumns TmsColumns]))

;; ---- bitmap helpers -----------------------------------------------------

(defn- rb ^RoaringBitmap [] (RoaringBitmap.))
(defn- rb-add! ^RoaringBitmap [^RoaringBitmap r d] (.add r (int d)) r)
(defn- rb-del! ^RoaringBitmap [^RoaringBitmap r d] (.remove r (int d)) r)

(defn- rb-has?
  "Is `d` a member?  **False for anything that cannot name a node**, nil included.
  Every read here is total, because the reference's are: a persistent map answers an
  unknown key as absent, and callers rely on it — `handle-of` yields nil for a sentence
  that is not stored, and `defeat-class` / `in?` are called with that nil.  The guard
  costs a perfectly-predicted branch on the engine's hottest call."
  [^RoaringBitmap r d]
  (and (integer? d) (.contains r (int d))))

(defn- rb-longs
  "The members as a vector of Longs — the engine's handle type, so what leaves this
  namespace is indistinguishable from what the reference returns."
  [^RoaringBitmap r]
  (let [it (.getIntIterator r)]
    (loop [acc (transient [])]
      (if (.hasNext it) (recur (conj! acc (long (.next it)))) (persistent! acc)))))

(defn- rb-set [^RoaringBitmap r]
  (let [it (.getIntIterator r)]
    (loop [acc (transient #{})]
      (if (.hasNext it) (recur (conj! acc (long (.next it)))) (persistent! acc)))))

;; ---- the justification columns ------------------------------------------
;;
;; A justification is not stored as an object.  Its belief-relevant fields are held in
;; primitive columns keyed by justification id — `jtms/graph-just` projects on the way
;; in, `just-record` rebuilds one only when a caller asks, which no relabel does.  The
;; decomposition
;; (`lein bench-jtms`, a rules-heavy corpus at 3.6 justifications per node) is what
;; picks the columns:
;;
;; ```
;;   structure     118 B   the record object + its map slot   -> gone
;;   bindings       80 B   never read by belief               -> the record store's
;;   antecedents    73 B   a vector of boxed handles          -> one int[]
;;   consequence     6 B                                      -> an int column
;;   id/informant/strength       0 B   shared objects already
;; ```
;;
;; `informant` splits in two because it is either a rule handle or a symbol
;; (`:premise`, a special-predicate name).  Both columns' values are compared with `=`
;; and never arithmetic, so an int column and an object column answer alike; the int
;; one exists so the common case cannot depend on a caller happening to share its
;; boxed handle.  A rule handle lives in `j-inf` alone: `j-antes` never repeats it
;; (`jtms/graph-just`), and `valid?` and the adjacency read the two columns together.
;; `strength` is one bitmap for the same reason the class map is: the lattice has two
;; elements.

(def ^:private ^:const no-informant
  "The `informant` column's absent marker — a justification whose informant is not a
  handle is in the object column instead."
  Integer/MIN_VALUE)

;; ---- the columns: depth, adjacency and the justification columns ---------
;;
;; `TmsColumns` and its heap implementation, `HeapColumns`, are `vaelii.impl.types.tms`,
;; which states the columns' contract.

(defn- heap-columns
  "Empty `HeapColumns`.  The informant column answers an absent id with `no-informant`,
  never with handle 0."
  ^HeapColumns []
  (tms-types/->HeapColumns (Int2IntOpenHashMap.) (Int2ObjectOpenHashMap.) (Int2ObjectOpenHashMap.)
                           (Int2IntOpenHashMap.)
                           (doto (Int2IntOpenHashMap.) (.defaultReturnValue (int no-informant)))
                           (Int2ObjectOpenHashMap.)))

(defn- ints-set
  "An ascending `int[]` of ids as a Clojure set of Longs, the engine's handle type."
  [^ints a]
  (loop [i 0, s (transient #{})]
    (if (< i (alength a)) (recur (inc i) (conj! s (long (aget a i)))) (persistent! s))))

(defn- supports-set
  "The justification ids concluding `d`, as a set — empty for an unknown datum and for
  anything that cannot name one, nil included, as the reference's `get-in … #{}` is."
  [^TmsColumns cols d]
  (if (integer? d) (ints-set (.supportsOf cols (int d))) #{}))

(defn- dependents-set
  "The justification ids citing `d`, as a set — total, as `supports-set` is."
  [^TmsColumns cols d]
  (if (integer? d) (ints-set (.dependentsOf cols (int d))) #{}))

;; ---- reader/writer coordination -----------------------------------------
;;
;; A `StampedLock` restores the consistent view an incidental reader is owed
;; (docs/storage.md, the single-writer contract) without taxing the engine's own single
;; writer.  See the namespace docstring's *Concurrency* note for the shape; the three
;; macros are how every method below takes its stamp.

(defmacro ^:private with-write
  "Run `body` holding the exclusive write stamp — writers serialize here, and a reader
  under a read stamp is excluded for the duration."
  [lock & body]
  `(let [^StampedLock l# ~lock, s# (.writeLock l#)]
     (try ~@body (finally (.unlockWrite l# s#)))))

(defmacro ^:private with-read
  "Run `body` holding a shared read stamp — for the iterating reads, which materialize
  O(nodes) and would tear if they walked a bitmap a writer is rewriting in place."
  [lock & body]
  `(let [^StampedLock l# ~lock, s# (.readLock l#)]
     (try ~@body (finally (.unlockRead l# s#)))))

(defmacro ^:private opt-read
  "Optimistic read of `body` — no lock in the steady state.  Redone under a shared read
  stamp if a writer intervened (`validate` fails) or the lock-free body saw torn state
  (threw).  `body` must be pure: it can run twice, and the first run may see a
  half-applied write.  An interned-keyword sentinel (never a value a read returns) marks
  the torn/aborted case rather than a wrapper object, so the steady-state path allocates
  nothing the body itself did not — measured at 0 extra bytes against the unlocked read."
  [lock & body]
  `(let [^StampedLock l# ~lock
         st# (.tryOptimisticRead l#)]
     (if (zero? st#)
       (with-read l# ~@body)                 ; a writer holds it now — wait, don't spin
       (let [r# (try (do ~@body) (catch Throwable _# ::torn))]
         (if (and (not (identical? ::torn r#)) (.validate l# st#))
           r#
           (with-read l# ~@body))))))

;; ---- the `Tms` methods -------------------------------------------------

;; The deftype's methods call the operations below, and those need the type itself for
;; their hints — a genuine in-file cycle, so the entry points are declared ahead of it.
(declare add-just! clear-defeats! defeat! ensure! ensure-noop? just-record premise! relabel-all! restrength-informant! retract-datum! set-blocked! snapshot suspend-premise! sweep-from!)

(deftype DenseTms [^StampedLock lock
                   ^RoaringBitmap nodes
                   ^RoaringBitmap premises
                   ^RoaringBitmap mono-premises
                   ;; depth, adjacency, and the consequence / informant / antecedent
                   ;; columns — see `TmsColumns`
                   ^TmsColumns cols
                   ;; the live ids, and the two sparse or two-class columns
                   ^RoaringBitmap jids
                   ^Int2ObjectOpenHashMap j-inf-sym
                   ^RoaringBitmap j-mono
                   ^RoaringBitmap in
                   ^RoaringBitmap groundable
                   ^RoaringBitmap defeated
                   ^RoaringBitmap blocked
                   ^RoaringBitmap touched
                   ^RoaringBitmap touched-in
                   ^RoaringBitmap touched-new
                   ^RoaringBitmap mono
                   ^clojure.lang.Atom superseded]
  ;; `@tms` yields the canonical map the reference stores natively — materialized, so
  ;; this is a testing and debugging read, never an engine path.  It takes the shared read
  ;; stamp `-snapshot` takes: the map is built field by field, and a writer that sweeps a
  ;; datum between the `:nodes` read and the `:in` read leaves the snapshot holding belief
  ;; in a datum with no node (`vaelii.jtms-concurrency-test`).
  clojure.lang.IDeref
  (deref [this] (with-read lock (snapshot this)))
  Tms
  (-believed? [_ datum]
    (opt-read lock (and (rb-has? in datum) (not (contains? @superseded datum)))))
  (-believed [_] (with-read lock (seq (remove @superseded (rb-longs in)))))
  (-node? [_ datum] (opt-read lock (rb-has? nodes datum)))
  (-datums [_] (with-read lock (seq (rb-longs nodes))))
  ;; O(1)/early-terminating boolean checks — a poll on the render path must neither
  ;; drain the bitmap into boxed Longs (as `(first (-datums …))` would) nor walk it
  ;; while a writer rewrites it in place.
  (-any-node? [_] (opt-read lock (not (.isEmpty ^RoaringBitmap nodes))))
  (-any-belief? [_]
    (with-read lock
      (and (not (.isEmpty ^RoaringBitmap in))
           (let [sup @superseded]
             (or (empty? sup)
                 (let [it (.getIntIterator ^RoaringBitmap in)]
                   (loop []
                     (cond
                       (not (.hasNext it))               false
                       (contains? sup (long (.next it))) (recur)
                       :else                             true))))))))
  (-depth [_ datum] (opt-read lock (if (integer? datum) (long (.depthOf cols (int datum))) 0)))
  (-premise? [_ datum] (opt-read lock (rb-has? premises datum)))
  (-premise-strength [_ datum]
    (opt-read lock
              (when (rb-has? premises datum)
                (if (rb-has? mono-premises datum) :monotonic :default))))
  (-defeat-class [_ datum]
    (opt-read lock
              (when (rb-has? in datum) (if (rb-has? mono datum) :monotonic :default))))
  (-defeated [_] (with-read lock (rb-set defeated)))
  (-blocked [_] (with-read lock (rb-set blocked)))
  ;; the supersession map is an immutable value in an atom, always consistent on its
  ;; own — no stamp needed, and it is mutated only under the write stamp anyway
  (-superseded [_] @superseded)
  (-touched [_] (with-read lock (rb-set touched)))
  (-touched-in [_] (with-read lock (rb-set touched-in)))
  (-touched-new [_] (with-read lock (rb-set touched-new)))
  (-reset-touched [_]
    (with-write lock (.clear touched) (.clear touched-in) (.clear touched-new)) nil)
  (-supports [_ datum] (with-read lock (supports-set cols datum)))
  (-dependents [_ datum] (with-read lock (dependents-set cols datum)))
  (-justification [this jid] (with-read lock (when (rb-has? jids jid) (just-record this jid))))
  (-justifications [this] (with-read lock (seq (mapv #(just-record this %) (rb-longs jids)))))
  (-ensure-node [this datum depth]
    ;; Take the exclusive stamp only when the write would change something: a node
    ;; already present at a depth no higher than `depth` is exactly what `ensure!`
    ;; leaves (it keeps the `min` of the two).  This runs once per placement, so most
    ;; calls are that no-op, and the probe is optimistic — no lock in the steady state.
    ;; Skipping is sound under the single-writer contract: nothing moves the node
    ;; between the probe and the write that is not taken.  Same skip the reference
    ;; makes (`jtms/-ensure-node`), under the same switch.
    (when-not (and observe/*chain-fast-paths* (opt-read lock (ensure-noop? this datum depth)))
      (with-write lock (ensure! this datum depth)))
    nil)
  (-add-premise [this datum strength] (with-write lock (premise! this datum strength)) nil)
  (-suspend-premise [this datum] (with-write lock (suspend-premise! this datum)) nil)
  (-add-justification [this just] (with-write lock (add-just! this just)) nil)
  (-restrength-informant [this informant strength]
    (with-write lock (restrength-informant! this informant strength)) nil)
  (-relabel [this] (with-write lock (relabel-all! this)) nil)
  (-defeat [this datums] (with-write lock (defeat! this datums)) nil)
  (-clear-defeats [this] (with-write lock (clear-defeats! this)) nil)
  (-set-blocked [this jids] (with-write lock (set-blocked! this jids)) nil)
  (-update-blocked [this f] (with-write lock (set-blocked! this (f (rb-set blocked)))) nil)
  (-supersede [_ m] (with-write lock (reset! superseded (into {} m))) nil)
  (-retract [this datum] (with-write lock (retract-datum! this datum)))
  (-sweep [this seeds] (with-write lock (sweep-from! this seeds)))
  (-snapshot [this] (with-read lock (snapshot this))))

;; ---- reading a justification out of the columns --------------------------

(defn- j-antecedents ^ints [^DenseTms this jid]
  (.antecedentsOf ^TmsColumns (.-cols this) (int jid)))

(defn- j-consequence
  "The consequence handle, or -1 for a justification that is not stored — the callers
  are walks over adjacency, which can name an id whose justification has been swept."
  ^long [^DenseTms this jid]
  (.consequenceOf ^TmsColumns (.-cols this) (int jid)))

(defn- j-informant-int
  "The informant as an int when it is a handle, else the absent marker — what
  `conferred-class` compares antecedents against, so a symbolic informant simply
  matches nothing."
  ^long [^DenseTms this jid]
  (long (.informantOf ^TmsColumns (.-cols this) (int jid))))

(defn- supports-of
  "The ids of the justifications concluding `d`, as a fresh `int[]`."
  ^ints [^DenseTms this d]
  (.supportsOf ^TmsColumns (.-cols this) (int d)))

(defn- dependents-of
  "The ids of the justifications citing `d`, as a fresh `int[]`."
  ^ints [^DenseTms this d]
  (.dependentsOf ^TmsColumns (.-cols this) (int d)))

(defn- j-informant [^DenseTms this jid]
  (let [i (j-informant-int this jid)]
    (if (== i no-informant)
      (.get ^Int2ObjectOpenHashMap (.-j-inf-sym this) (int jid))
      i)))

(defn- just-record
  "Rebuild the `Justification` a caller asked for.  `:bindings` is nil: the network
  keeps the graph and the record store keeps the record (`jtms/graph-just`).  Nothing
  on a relabel path calls this — the fixpoints read the columns directly."
  [^DenseTms this jid]
  (tms-types/->Justification
   (long jid)
   (j-informant this jid)
   (into [] (map long) (j-antecedents this jid))
   (j-consequence this jid)
   nil
   (if (rb-has? ^RoaringBitmap (.-j-mono this) jid) :monotonic :default)))

;; ---- validity and class, against the dense structures -------------------
;;
;; These mirror `vaelii.impl.jtms`'s private `valid?` / `conferred-class` /
;; `node-class`.  The semantics are the specification (docs/nmtms.md); the
;; differential oracle is what holds the two readings of it together.

(defn- all-in?
  "Are all of `ids` believed?  A hand-rolled loop rather than `every?` over a boxed
  seq: this is the innermost test of every fixpoint iteration."
  [^ints ids ^RoaringBitmap in]
  (let [n (alength ids)]
    (loop [i 0]
      (cond (== i n) true
            (.contains in (aget ids i)) (recur (unchecked-inc i))
            :else false))))

(defn- valid?
  "Is justification `jid` satisfied — every antecedent believed, its rule believed when
  the informant is a rule handle, and not blocked by its rule's exception?"
  [^DenseTms this jid ^RoaringBitmap in ^RoaringBitmap blocked]
  (and (not (.contains blocked (int jid)))
       (all-in? (j-antecedents this jid) in)
       (let [i (j-informant-int this jid)]
         (or (== i no-informant) (.contains in (int i))))))

(defn- conferred-class
  "The class a valid justification confers: its own strength, capped by the weakest of
  its antecedents' classes.  A rule-handle informant is not in `j-antes`, so the cap
  never reads it: a rule is a condition of *validity*, not a ground."
  [^DenseTms this jid ^RoaringBitmap classes]
  (let [antes (j-antecedents this jid)]
    (areduce antes i acc (if (rb-has? ^RoaringBitmap (.-j-mono this) jid) :monotonic :default)
             (strength/min acc (if (.contains classes (aget antes i)) :monotonic :default)))))

(defn- node-class
  "The strongest support an IN datum has: its premise strength, and what each currently
  valid justification confers.  A blocked justification is not valid, so it confers
  nothing — exactly as if it were missing an antecedent."
  [^DenseTms this d ^RoaringBitmap in ^RoaringBitmap classes]
  (let [blocked ^RoaringBitmap (.-blocked this)
        live    ^RoaringBitmap (.-jids this)
        prem    (when (and (rb-has? ^RoaringBitmap (.-premises this) d)
                           (not (rb-has? ^RoaringBitmap (.-defeated this) d)))
                  (if (rb-has? ^RoaringBitmap (.-mono-premises this) d) :monotonic :default))
        ids     (supports-of this d)]
    (areduce ids i acc (or prem :default)
             (let [jid (aget ids i)]
               (if (and (.contains live jid) (valid? this jid in blocked))
                 (strength/max acc (conferred-class this jid classes))
                 acc)))))

;; ---- region-local relabelling -------------------------------------------

(defn- affected-region
  "Every node whose label could move when `seeds` do: the forward closure over
  consequence justifications, seeds included."
  ^RoaringBitmap [^DenseTms this seeds]
  (let [seen (rb)]
    (loop [stack (vec seeds)]
      (when (seq stack)
        (let [d (peek stack), stack (pop stack)]
          (if (rb-has? seen d)
            (recur stack)
            (do (rb-add! seen d)
                (let [ids (dependents-of this d)]
                  (recur (areduce ids i acc stack
                                  (let [c (j-consequence this (aget ids i))]
                                    (if (neg? c) acc (conj acc c)))))))))))
    seen))

(defn- region-fixpoint!
  "Least fixpoint of IN over `region`, accumulated **into** `acc` — the live bitmap, with
  the region already cleared out of it, so what it holds on entry is the boundary and the
  fixpoint only ever adds region members back.  `forced-out` is forced OUT whatever its
  support (the defeated set when labelling, empty when computing groundability).

  Starting from nothing believed inside the region and only ever adding is what keeps
  support well-founded, and a least fixpoint is unique — so going local costs no order
  independence.  Semi-naive: `valid?` is monotone in `in`, so a justification is
  retried only when one of its antecedents newly enters, reached through the stored
  inverse edge.

  **It accumulates into the live bitmap rather than into a clone of it, and that is what
  makes a relabel proportional to the region rather than to the graph.**  A clone is
  proportional to the *believed set*, so adding one premise to a KB with ten million
  believed datums copied ten million bits — and a rebuild, which adds a premise per
  stored premise, was quadratic.  Measured: per-premise cost rose 14.9× across three
  million premises where the reference representation stayed flat."
  [^DenseTms this ^RoaringBitmap region cands ^RoaringBitmap acc
   ^RoaringBitmap forced-out]
  (let [blocked ^RoaringBitmap (.-blocked this)]
    ;; seed: the region's own premises, unless forced OUT
    (let [it (.getIntIterator (RoaringBitmap/and region ^RoaringBitmap (.-premises this)))]
      (while (.hasNext it)
        (let [d (.next it)]
          (when-not (.contains forced-out d) (.add acc d)))))
    (loop [stack (vec cands)]
      (if (empty? stack)
        nil
        (let [jid   (peek stack)
              stack (pop stack)
              c     (j-consequence this jid)]
          (if (and (not (neg? c))
                   (rb-has? region c)
                   (not (rb-has? acc c))
                   (not (rb-has? forced-out c))
                   (valid? this jid acc blocked))
            (do (rb-add! acc c)
                (let [ids (dependents-of this c)]
                  (recur (areduce ids i a stack (conj a (aget ids i))))))
            (recur stack)))))))

(defn- region-classes!
  "Defeat-classes for `region` under `in`, as a least fixpoint — every in-region IN
  node starts at the lattice's bottom and the recursive equation is iterated to
  stability, so the answer is unique and cannot depend on visit order.

  `classes` is the live monotonic bitmap with the region already cleared out of it, and
  is mutated in place for the same reason `region-fixpoint!` is: an OUT datum has no
  class and an IN one restarts at `:default` (absent from the bitmap), so what is left
  outside the region is boundary that does not move.

  The bitmap *is* the whole class map: the lattice has two elements.  A boundary node
  whose class could move would have an antecedent in the region and so would be in it."
  [^DenseTms this ^RoaringBitmap region ^RoaringBitmap in ^RoaringBitmap classes]
  (let [members (RoaringBitmap/and region in)]
    ;; The lattice has height one, so a member rises at most once and the worklist only
    ;; ever ADDS — which is exactly what makes this the least fixpoint rather than some
    ;; fixpoint.
    (loop [stack (rb-longs members)]
      (if (empty? stack)
        nil
        (let [d     (peek stack)
              stack (pop stack)]
          (if (or (rb-has? classes d)
                  (not= :monotonic (node-class this d in classes)))
            (recur stack)
            (do (rb-add! classes d)
                (let [ids (dependents-of this d)]
                  (recur (areduce ids i acc stack
                                  (let [c (j-consequence this (aget ids i))]
                                    (if (and (not (neg? c)) (rb-has? in c))
                                      (conj acc c)
                                      acc))))))))))))

(defn- relabel-region!
  "Recompute belief, groundability and the classes for `region`, holding everything
  outside it fixed — equivalent to a global relabel whenever the region is the
  affected closure of what changed, and proportional to the region rather than to the
  graph."
  [^DenseTms this ^RoaringBitmap region]
  (let [live    ^RoaringBitmap (.-jids this)
        ;; only the justifications that can conclude something in the region matter
        cands   (let [it (.getIntIterator region)]
                  (loop [acc (transient [])]
                    (if-not (.hasNext it)
                      (persistent! acc)
                      (let [ids (supports-of this (.next it))]
                        (recur (areduce ids i a acc
                                        (if (.contains live (aget ids i))
                                          (conj! a (aget ids i))
                                          a)))))))
        in      ^RoaringBitmap (.-in this)
        ground  ^RoaringBitmap (.-groundable this)
        mono    ^RoaringBitmap (.-mono this)
        ;; Which of the region this window has not relabelled yet, and of those which are
        ;; believed *now* — read FIRST, because the fixpoint below overwrites the region's
        ;; labels in place and the prior ones are then gone.  See `jtms/touched-in`.
        fresh    (RoaringBitmap/andNot region ^RoaringBitmap (.-touched this))
        fresh-in (RoaringBitmap/and fresh in)]
    ;; Clearing the region out of each live bitmap leaves exactly the boundary, which is
    ;; what each fixpoint starts from and holds fixed.  In place: the static `andNot`
    ;; copies every container of a bitmap the size of the believed set, where the mutating
    ;; one is a merge over the container lists and touches only the region's own.
    (.andNot in region)
    (.andNot ground region)
    ;; the two are independent — each reads and writes only its own accumulator — so the
    ;; groundability pass cannot see a half-written in-set even though the in-set is now
    ;; written in place
    (region-fixpoint! this region cands in ^RoaringBitmap (.-defeated this))
    (region-fixpoint! this region cands ground (rb))
    ;; the classes are a function of the NEW in-set, and of the current `mono` outside the
    ;; region for their boundary — so the region is cleared out of `mono` and no further
    (.andNot mono region)
    (region-classes! this region in mono)
    (.or ^RoaringBitmap (.-touched-in this) fresh-in)
    ;; A supporter's belief can flip only inside a relabelled region, so the accumulated
    ;; touched set is a superset of every handle whose belief moved this settle — what
    ;; `tax/refresh-beliefs` reads to skip a cache no moved supporter touches.
    (.or ^RoaringBitmap (.-touched this) region)
    nil))

(defn- resettle! [^DenseTms this seeds]
  (relabel-region! this (affected-region this seeds)))

;; ---- mutation -----------------------------------------------------------

(def ^:private ^:const max-handle
  "The dense network's ceiling: bitmaps and fastutil maps are `int`-keyed, so a handle or
  justification id must fit a 32-bit int.  See the namespace docstring's *Limit*."
  Integer/MAX_VALUE)

(defn- check-handle!
  "Return `x` as a `long` after checking it fits the int ceiling, throwing an actionable
  error in place of the bare `integer overflow` the cast would otherwise raise.  Called
  where a new id first enters — `ensure!` for a node handle, `add-just!` for a
  justification id; antecedents and consequences reach `add-just!` already having nodes,
  so they were checked when those nodes were made.  `kind` names what overran."
  ^long [x kind]
  (let [v (long x)]
    (when (> v max-handle)
      (throw (ex-info (str "dense TMS: " kind " " v " exceeds the 2^31-1 handle ceiling ("
                           max-handle ").  Open the KB with {:tms :reference} — its "
                           "Long-keyed network has no ceiling (docs/density.md, Phase 3).")
                      {:type :handle-ceiling :kind kind :value v :ceiling max-handle
                       :remedy {:tms :reference}})))
    v))

(defn- ensure-noop?
  "Would `ensure!` leave the network exactly as it stands — is `datum` already a node at
  a depth no higher than `depth`?  That is what `ensure!` writes back, since it keeps the
  `min` of the stored depth and the asked one, so the exclusive stamp buys nothing there.

  Total, as every read here is: false for anything that cannot name a node — nil, a
  non-integer, or a handle past `max-handle` — so the refusal stays `check-handle!`'s to
  raise from inside `ensure!` rather than becoming a cast error from this probe."
  [^DenseTms this datum depth]
  (and (integer? datum)
       (<= (long datum) max-handle)
       (rb-has? ^RoaringBitmap (.-nodes this) datum)
       (<= (long (.depthOf ^TmsColumns (.-cols this) (int datum))) (long depth))))

(defn- ensure! [^DenseTms this datum depth]
  (let [d    (int (check-handle! datum "node handle"))
        cols ^TmsColumns (.-cols this)]
    (if (rb-has? ^RoaringBitmap (.-nodes this) d)
      (.setDepth cols d (int (min (.depthOf cols d) (int depth))))
      ;; the window's record of what it created, taken here because this is the only
      ;; line that knows — see `jtms/touched-new`
      (do (rb-add! ^RoaringBitmap (.-nodes this) d)
          (rb-add! ^RoaringBitmap (.-touched-new this) d)
          (.setDepth cols d (int depth))))
    nil))

(defn- premise! [^DenseTms this datum strength-kw]
  (ensure! this datum 0)
  (rb-add! ^RoaringBitmap (.-premises this) datum)
  (if (= :monotonic strength-kw)
    (rb-add! ^RoaringBitmap (.-mono-premises this) datum)
    (rb-del! ^RoaringBitmap (.-mono-premises this) datum))
  (resettle! this [datum]))

(defn- suspend-premise!
  "Drop the premise mark and relabel the affected closure — `retract-datum!` without
  the sweep, so nothing is deleted and `premise!` puts it back exactly."
  [^DenseTms this datum]
  (when (rb-has? ^RoaringBitmap (.-nodes this) datum)
    (rb-del! ^RoaringBitmap (.-premises this) datum)
    (rb-del! ^RoaringBitmap (.-mono-premises this) datum)
    (relabel-region! this (affected-region this [datum])))
  nil)

(defn- add-just!
  "Record `just` and relabel only what it actually moves.

  The fast path is what keeps a recursive forward load linear.  A *redundant*
  justification — one whose consequence is already believed and which confers no
  stronger a class than it already holds (or is not even valid) — moves nothing: an
  already-IN node feeds its consequences identically on one witness or two.  So the
  forward closure is walked once, when a fact is *first* derived (a brand-new node has
  no consequences yet, so its region is a singleton), and every later re-derivation by
  another path is a no-op.  Any real change still takes the full resettle."
  [^DenseTms this just]
  (let [{:keys [id informant antecedents consequence strength]} (jtms/graph-just just)
        jid   (int (check-handle! id "justification id"))
        cols  ^TmsColumns (.-cols this)
        in    ^RoaringBitmap (.-in this)
        mono  ^RoaringBitmap (.-mono this)]
    ;; The columns, in place of a stored object.  Every one is **set**, never merged:
    ;; where a map entry would have been replaced wholesale, six columns each have to
    ;; be told, and a column left alone on a re-add would answer for a swept
    ;; justification that held the same id.
    (rb-add! ^RoaringBitmap (.-jids this) jid)
    (.putJustification cols jid (int consequence)
                       (int (if (integer? informant) informant no-informant))
                       (int-array antecedents))
    (if (integer? informant)
      (.remove ^Int2ObjectOpenHashMap (.-j-inf-sym this) jid)
      (.put ^Int2ObjectOpenHashMap (.-j-inf-sym this) jid informant))
    (if (= :monotonic strength)
      (rb-add! ^RoaringBitmap (.-j-mono this) jid)
      (rb-del! ^RoaringBitmap (.-j-mono this) jid))
    (.addSupport cols (int consequence) jid)
    ;; The adjacency lists the justification under each antecedent and under its rule —
    ;; one `run!` over the antecedents, reduced in place with no cons cells, and one entry
    ;; for a rule informant.  This is the hottest write path there is, one per derived
    ;; fact, so nothing here allocates a seq to iterate both.
    (run! (fn [a] (.addDependent ^TmsColumns cols (int a) jid)) antecedents)
    (when (integer? informant) (.addDependent cols (int informant) jid))
    (if (and (rb-has? in consequence)
             (or (not (valid? this jid in ^RoaringBitmap (.-blocked this)))
                 (let [cls (if (rb-has? mono consequence) :monotonic :default)]
                   (= cls (strength/max cls (conferred-class this jid mono))))))
      ;; the fast path still notes the consequence as touched, for the reason
      ;; `jtms/add-just*` records: a second witness moves what a caller *published* about
      ;; the datum while moving no label, and `touched-in` takes it unless this window has
      ;; relabelled it already
      (let [t ^RoaringBitmap (.-touched this)]
        (when-not (rb-has? t consequence)
          (rb-add! ^RoaringBitmap (.-touched-in this) consequence))
        (rb-add! t consequence))
      (resettle! this [consequence]))))

(defn- restrength-informant!
  "The dense half of `jtms/restrength-informant`: the rule-contribution slot is the
  `j-mono` bitmap, the candidate justifications are the informant's own `conseqs`
  adjacency (`add-just!` lists a justification under its rule's node), and the informant
  column filters out a justification that merely uses the handle as an ordinary
  antecedent.  Only a bit that actually moves seeds the relabel."
  [^DenseTms this informant strength]
  (when (integer? informant)
    (let [inf   (int informant)
          jmono ^RoaringBitmap (.-j-mono this)
          mono? (= :monotonic strength)
          ids   (dependents-of this inf)
          n     (alength ids)]
      (loop [i 0, seeds (transient [])]
        (if (< i n)
          (let [jid (aget ids i)]
            ;; an absent id reads `no-informant`, which no handle equals
            (if (and (== (j-informant-int this jid) inf)
                     (not= mono? (rb-has? jmono jid)))
              (do (if mono? (rb-add! jmono jid) (rb-del! jmono jid))
                  (let [c (j-consequence this jid)]
                    (recur (inc i) (if (neg? c) seeds (conj! seeds c)))))
              (recur (inc i) seeds)))
          (let [s (persistent! seeds)]
            (when (seq s) (resettle! this s))))))))

(defn- defeat! [^DenseTms this datums]
  (let [d ^RoaringBitmap (.-defeated this)]
    (doseq [x datums] (rb-add! d x))
    (resettle! this datums)))

(defn- clear-defeats!
  "Empty the derived defeated set and relabel — the basis for revival.  The region is
  the *previously* defeated nodes, so a settle that defeated nothing does no work."
  [^DenseTms this]
  (let [d   ^RoaringBitmap (.-defeated this)
        was (rb-longs d)]
    (.clear d)
    (resettle! this was)))

(defn- set-blocked!
  "Replace the blocked set and relabel what moved.  Only the justifications whose
  blocked status actually changed can move a label, so they alone seed the region —
  a call that changes nothing does no work at all."
  [^DenseTms this jids]
  (let [want    (reduce rb-add! (rb) jids)
        blocked ^RoaringBitmap (.-blocked this)
        changed (RoaringBitmap/xor want blocked)]
    (when-not (.isEmpty changed)
      (let [seeds (into [] (keep #(let [c (j-consequence this %)] (when-not (neg? c) c)))
                        (rb-longs changed))]
        (doto blocked (.clear) (.or want))
        (resettle! this seeds)))))

(defn- relabel-all!
  "Whole-graph relabel — no engine path calls it, so this is the differential oracle's
  whole-graph operation, which is why both representations carry it (`jtms/relabel`).

  Blocking and supersession are **cleared first**: nothing about an exception or an
  equality merge is stored, so a whole-graph relabel can read neither back, and one that
  merged into whatever was there could only ever *add* — leaving a block standing for a
  justification whose exception no longer holds.  It lands unblocked, and a caller that
  wants either states the whole answer again."
  [^DenseTms this]
  (.clear ^RoaringBitmap (.-blocked this))
  (reset! ^clojure.lang.Atom (.-superseded this) {})
  (relabel-region! this (.clone ^RoaringBitmap (.-nodes this))))

;; ---- retraction ---------------------------------------------------------

(defn- sweep!
  "Collect the datums in `suspects` that are no longer *structurally* derivable and are
  not premises, tear them and every justification touching them out of the graph, and
  return the removals for the caller to apply to its own stores.

  Groundability ignores defeats, so a defeated node with a surviving derivation is kept
  for revival, while one whose only support was just torn down is swept.  Blocking, by
  contrast, does suppress groundability, which is what makes this the garbage collector
  for an excepted conclusion as well as for a retracted one.

  Region-local: the justifications to tear down are read off the dead nodes' own
  adjacency, never by scanning `jids` — `exceptWhen` blocks on ordinary fact arrival,
  so sweeping is routine, and a sweep that scanned the graph would make a run of them
  quadratic."
  [^DenseTms this ^RoaringBitmap suspects]
  (let [ground ^RoaringBitmap (.-groundable this)
        prem   ^RoaringBitmap (.-premises this)
        live   ^RoaringBitmap (.-jids this)
        cols   ^TmsColumns (.-cols this)
        dead   (into [] (remove #(or (rb-has? prem %) (rb-has? ground %)))
                     (rb-longs suspects))
        dead-jids (into #{}
                        (comp (mapcat (fn [d] (concat (supports-set cols d)
                                                      (dependents-set cols d))))
                              (filter #(.contains live (int %))))
                        dead)
        ;; read the informants BEFORE the columns are unlinked — a premise
        ;; justification is the caller's own and is not ours to report as removed
        removed-justs (into [] (remove #(= :premise (j-informant this %))) dead-jids)]
    (doseq [jid dead-jids]
      (let [antes (j-antecedents this jid)
            inf   (j-informant-int this jid)
            c     (j-consequence this jid)
            k     (int jid)]
        (rb-del! live k)
        (.dropJustification cols k)
        (.remove ^Int2ObjectOpenHashMap (.-j-inf-sym this) k)
        (rb-del! ^RoaringBitmap (.-j-mono this) k)
        (.removeSupport cols (int c) k)
        (dotimes [i (alength antes)] (.removeDependent cols (aget antes i) k))
        (when-not (== inf no-informant) (.removeDependent cols (int inf) k))))
    (doseq [d dead]
      (rb-del! ^RoaringBitmap (.-nodes this) d)
      (rb-del! ^RoaringBitmap (.-premises this) d)
      (rb-del! ^RoaringBitmap (.-mono-premises this) d)
      (rb-del! ^RoaringBitmap (.-mono this) d)
      ;; the swept nodes were OUT and ungroundable, so dropping them cannot move any
      ;; survivor's label — only the bookkeeping needs the removal
      (rb-del! ^RoaringBitmap (.-in this) d)
      (rb-del! ^RoaringBitmap (.-groundable this) d)
      (.dropNode cols (int d)))
    ;; a block names a justification and a supersession names a datum, so a swept one
    ;; must lose both — an entry left behind would be reapplied to whatever reuses the id
    (doseq [jid dead-jids] (rb-del! ^RoaringBitmap (.-blocked this) jid))
    ;; one transient pass rather than `apply dissoc`, whose per-key HAMT path copy `dead`
    ;; — a whole swept region — would pay for on every `exceptWhen` block (`jtms/dissoc-all`)
    (swap! ^clojure.lang.Atom (.-superseded this) jtms/dissoc-all dead)
    {:removed-sentexes dead :removed-justifications removed-justs}))

(defn- retract-datum!
  "Dependency-directed retraction: drop the premise, relabel the affected closure (a
  suspect re-derivable by another witness stays IN), then sweep what the retraction
  solely supported.  An unknown datum is a no-op — retraction is idempotent, and
  materializing the node would let the sweep collect a phantom and claim a removal that
  never happened."
  [^DenseTms this datum]
  (if-not (rb-has? ^RoaringBitmap (.-nodes this) datum)
    {:removed-sentexes [] :removed-justifications []}
    (do (rb-del! ^RoaringBitmap (.-premises this) datum)
        (rb-del! ^RoaringBitmap (.-mono-premises this) datum)
        ;; marking and relabelling walk the graph once between them: the affected
        ;; closure is both the suspect set and the region to relabel
        (let [suspects (affected-region this [datum])]
          (relabel-region! this suspects)
          (sweep! this suspects)))))

(defn- sweep-from! [^DenseTms this seeds]
  (sweep! this (affected-region this seeds)))

;; ---- the byte image -------------------------------------------------------
;;
;; The whole network as bytes, written between operations and read back into an empty
;; network with no relabel: every label, class, block, defeat and supersession is read,
;; not recomputed.  `vaelii.impl.reasoning-image` is the caller, and decides whether an
;; image may be installed at all; this section only writes and reads one.
;;
;; The touched window is not written.  An image is taken between operations, and a
;; reloaded network starts its window empty, as a freshly settled one does.  Keys are
;; written in sorted order, so two images of equal networks are equal bytes.  A zero depth
;; is not written: `depths` answers an absent key as 0.

(def image-version
  "The byte image's layout number.  `read-image!` refuses any other, so an image written
  under an earlier set of justification columns is discarded rather than misread."
  2)

(def ^:private ^:const image-magic 0x76544D53)

(defn- image-bitmaps
  "The bitmaps an image carries, in the order it writes them."
  [^DenseTms t]
  [(.-nodes t) (.-premises t) (.-mono-premises t) (.-jids t) (.-j-mono t)
   (.-in t) (.-groundable t) (.-defeated t) (.-blocked t) (.-mono t)])

(defn- sorted-keys ^ints [m]
  (let [^ints a (if (instance? Int2IntOpenHashMap m)
                  (.toIntArray (.keySet ^Int2IntOpenHashMap m))
                  (.toIntArray (.keySet ^Int2ObjectOpenHashMap m)))]
    (Arrays/sort a)
    a))

(defn- write-bitmap! [^DataOutput o ^RoaringBitmap r]
  ;; a clone, because `runOptimize` rewrites containers and the writer holds only a read
  ;; stamp over the live one
  (let [c (.clone r)] (.runOptimize c) (.serialize c o)))

(defn- write-ints! [^DataOutput o ^ints a]
  (.writeInt o (alength a))
  (dotimes [k (alength a)] (.writeInt o (aget a k))))

(defn- read-ints ^ints [^DataInput i]
  (let [n (.readInt i) a (int-array n)]
    (dotimes [k n] (aset a k (.readInt i)))
    a))

(defn- write-int-map! [^DataOutput o ^Int2IntOpenHashMap m skip-zero?]
  (let [ks (sorted-keys m)
        n  (loop [k 0 c 0]
             (if (== k (alength ks))
               c
               (recur (inc k) (if (and skip-zero? (zero? (.get m (aget ks k)))) c (inc c)))))]
    (.writeInt o (int n))
    (dotimes [k (alength ks)]
      (let [key (aget ks k) v (.get m key)]
        (when-not (and skip-zero? (zero? v))
          (.writeInt o key)
          (.writeInt o v))))))

(defn- read-int-map! [^DataInput i ^Int2IntOpenHashMap m]
  (dotimes [_ (.readInt i)] (.put m (.readInt i) (.readInt i))))

(defn- write-postings! [^DataOutput o ^Int2ObjectOpenHashMap m]
  (let [ks (sorted-keys m)]
    (.writeInt o (alength ks))
    (dotimes [k (alength ks)]
      (let [key (aget ks k)
            s   (postings/pseed (.get m key))]
        (.writeInt o key)
        (if (instance? RoaringBitmap s)
          (do (.writeByte o 1) (write-bitmap! o s))
          (do (.writeByte o 0) (write-ints! o s)))))))

(defn- read-postings!
  "Each posting comes back in the form it was written in — a sorted `int[]`, or a bitmap
  once it had grown past `IntPostings`' promotion bound — so the reloaded network promotes
  on the same later insert the original would have."
  [^DataInput i ^Int2ObjectOpenHashMap m]
  (dotimes [_ (.readInt i)]
    (let [key (.readInt i)]
      (.put m key (if (== 1 (.readByte i))
                    (postings/->IntPostings nil (doto (RoaringBitmap.) (.deserialize i)))
                    (postings/->IntPostings (read-ints i) nil))))))

(defn- write-arrays! [^DataOutput o ^Int2ObjectOpenHashMap m]
  (let [ks (sorted-keys m)]
    (.writeInt o (alength ks))
    (dotimes [k (alength ks)]
      (let [key (aget ks k)]
        (.writeInt o key)
        (write-ints! o (.get m key))))))

(defn- read-arrays! [^DataInput i ^Int2ObjectOpenHashMap m]
  (dotimes [_ (.readInt i)] (let [key (.readInt i)] (.put m key (read-ints i)))))

(defn- write-data! [^DataOutput o x]
  (let [^bytes b (nippy/freeze x)]
    (.writeInt o (alength b))
    (.write o b)))

(defn- read-data [^DataInput i]
  (let [b (byte-array (.readInt i))]
    (.readFully i b)
    (nippy/thaw b)))

(defn- heap-cols
  "`t`'s columns as `HeapColumns`, which are the only columns the byte image writes and
  reads.  Throws `IllegalStateException` for any other implementation."
  ^HeapColumns [^DenseTms t]
  (let [c (.-cols t)]
    (if (instance? HeapColumns c)
      c
      (throw (IllegalStateException. "the byte image writes and reads HeapColumns only")))))

(defn write-image
  "Write the whole of dense network `t` to `o`, under a read stamp, so a concurrent reader
  is not held up and a writer waits for the image to finish."
  [^DenseTms t ^DataOutput o]
  (with-read (.-lock t)
    (.writeInt o image-magic)
    (.writeInt o (int image-version))
    (run! #(write-bitmap! o %) (image-bitmaps t))
    (let [c (heap-cols t)]
      (write-int-map! o (.-depths c) true)
      (write-int-map! o (.-j-conseq c) false)
      (write-int-map! o (.-j-inf c) false)
      (write-postings! o (.-supports c))
      (write-postings! o (.-conseqs c))
      (write-arrays! o (.-j-antes c)))
    (write-data! o (let [m ^Int2ObjectOpenHashMap (.-j-inf-sym t)]
                     (mapv (fn [k] [k (.get m (int k))]) (sorted-keys m))))
    (write-data! o (into (sorted-map) @(.-superseded t))))
  nil)

(defn read-image!
  "Read an image `write-image` wrote from `i` into dense network `t`, which must hold no
  node.  Throws `IllegalStateException` for a populated `t` and
  `IllegalArgumentException` for bytes that are not an image of `image-version`; both are
  a caller's error rather than a state of the KB, since `vaelii.impl.reasoning-image` checks
  the manifest before it reads a byte."
  [^DenseTms t ^DataInput i]
  (with-write (.-lock t)
    (when-not (.isEmpty ^RoaringBitmap (.-nodes t))
      (throw (IllegalStateException. "read-image! needs an empty network")))
    (let [magic (.readInt i) version (.readInt i)]
      (when-not (and (== magic image-magic) (== version (long image-version)))
        (throw (IllegalArgumentException.
                (str "not a dense network image of version " image-version)))))
    (run! (fn [^RoaringBitmap r] (.deserialize r i)) (image-bitmaps t))
    (let [c (heap-cols t)]
      (read-int-map! i (.-depths c))
      (read-int-map! i (.-j-conseq c))
      (read-int-map! i (.-j-inf c))
      (read-postings! i (.-supports c))
      (read-postings! i (.-conseqs c))
      (read-arrays! i (.-j-antes c)))
    (let [m ^Int2ObjectOpenHashMap (.-j-inf-sym t)]
      (doseq [[k v] (read-data i)] (.put m (int k) v)))
    (reset! (.-superseded t) (into {} (read-data i))))
  t)

(defn node-count
  "How many nodes dense network `t` holds — the bitmap's cardinality, read under a read
  stamp without materializing a handle."
  ^long [^DenseTms t]
  (with-read (.-lock t) (.getLongCardinality ^RoaringBitmap (.-nodes t))))

(defn- copy-structures!
  "Copy every structure of dense network `src` into `target`, whose write stamp the caller
  holds.  The postings `src`'s maps hold are shared with `target`, not copied, so `src` is
  not written afterwards."
  [^DenseTms target ^DenseTms src]
  (run! (fn [[^RoaringBitmap t ^RoaringBitmap s]] (.or t s))
        (map vector (image-bitmaps target) (image-bitmaps src)))
  (let [tc (heap-cols target)
        sc (heap-cols src)]
    (.putAll ^Int2IntOpenHashMap (.-depths tc) ^Int2IntOpenHashMap (.-depths sc))
    (.putAll ^Int2IntOpenHashMap (.-j-conseq tc) ^Int2IntOpenHashMap (.-j-conseq sc))
    (.putAll ^Int2IntOpenHashMap (.-j-inf tc) ^Int2IntOpenHashMap (.-j-inf sc))
    (doseq [[^Int2ObjectOpenHashMap t ^Int2ObjectOpenHashMap s]
            [[(.-supports tc) (.-supports sc)] [(.-conseqs tc) (.-conseqs sc)]
             [(.-j-antes tc) (.-j-antes sc)]
             [(.-j-inf-sym target) (.-j-inf-sym src)]]]
      (.putAll t s)))
  (reset! (.-superseded target) @(.-superseded src)))

(defn copy-into!
  "Copy every structure of dense network `src` into `target`, which must hold no node,
  under `target`'s write stamp.  `read-image!` reads into a fresh network and this moves
  the result into the one a KB already holds: the KB holds its network by identity, so an
  image cannot replace the object, and reading into a scratch network first means a
  truncated image leaves the KB's network untouched."
  [^DenseTms target ^DenseTms src]
  (with-write (.-lock target)
    (when-not (.isEmpty ^RoaringBitmap (.-nodes target))
      (throw (IllegalStateException. "copy-into! needs an empty network")))
    (copy-structures! target src))
  target)

(defn moved-between
  "What replacing dense network `a` with `b` moves, as `{:moved bitmap :was-in bitmap}`.
  `:moved` holds the handles with a node or an IN label in one network and not the other,
  and `:was-in` holds those of them IN in `a`.  Each network is read under its own read
  stamp."
  [^DenseTms a ^DenseTms b]
  (let [snap (fn [^DenseTms t]
               (with-read (.-lock t)
                 [(.clone ^RoaringBitmap (.-in t)) (.clone ^RoaringBitmap (.-nodes t))]))
        [^RoaringBitmap a-in ^RoaringBitmap a-nodes] (snap a)
        [^RoaringBitmap b-in ^RoaringBitmap b-nodes] (snap b)
        moved (RoaringBitmap/or (RoaringBitmap/xor a-in b-in) (RoaringBitmap/xor a-nodes b-nodes))]
    {:moved moved :was-in (RoaringBitmap/and moved a-in)}))

;; ---- the canonical snapshot ---------------------------------------------

(defn- snapshot
  "The whole network as the reference's persistent-map shape — what the differential
  oracle compares, and what `@tms` yields.  Materializes everything, so it is a testing
  and debugging surface and no engine path calls it."
  [^DenseTms this]
  (let [prem   ^RoaringBitmap (.-premises this)
        mprem  ^RoaringBitmap (.-mono-premises this)
        cols   ^TmsColumns (.-cols this)]
    {:nodes (into {}
                  (map (fn [d]
                         [d (cond-> {:datum d
                                     :premise? (rb-has? prem d)
                                     :depth (long (.depthOf cols (int d)))
                                     :supports (supports-set cols d)
                                     :consequences (dependents-set cols d)}
                              (rb-has? prem d)
                              (assoc :premise-strength
                                     (if (rb-has? mprem d) :monotonic :default)))]))
                  (rb-longs ^RoaringBitmap (.-nodes this)))
     :justs (into {} (map (fn [jid] [jid (just-record this jid)]))
                  (rb-longs ^RoaringBitmap (.-jids this)))
     :defeated   (rb-set ^RoaringBitmap (.-defeated this))
     :blocked    (rb-set ^RoaringBitmap (.-blocked this))
     :superseded @^clojure.lang.Atom (.-superseded this)
     :classes    (into {} (map (fn [d] [d :monotonic]))
                       (rb-longs ^RoaringBitmap (.-mono this)))
     :in         (rb-set ^RoaringBitmap (.-in this))
     :groundable (rb-set ^RoaringBitmap (.-groundable this))
     :touched     (rb-set ^RoaringBitmap (.-touched this))
     :touched-in  (rb-set ^RoaringBitmap (.-touched-in this))
     :touched-new (rb-set ^RoaringBitmap (.-touched-new this))}))

;; ---- construction -------------------------------------------------------

(defn create-dense-tms
  "A fresh, empty dense truth-maintenance network — `vaelii.impl.jtms/create-tms`'s
  counterpart, selected by `open-kb`'s `{:tms :dense}`."
  []
  (->DenseTms (StampedLock.)
              (rb) (rb) (rb)                                   ; nodes premises mono-premises
              (heap-columns)                                   ; cols
              (rb)                                             ; jids
              (Int2ObjectOpenHashMap.)                         ; j-inf-sym
              (rb)                                             ; j-mono
              (rb) (rb) (rb) (rb) (rb) (rb) (rb) (rb)          ; in groundable defeated blocked
                                                               ; touched touched-in touched-new
                                                               ; mono
              (atom {})))
