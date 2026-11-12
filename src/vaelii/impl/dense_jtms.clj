;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-jtms
  "The dense truth-maintenance network, `:tms :dense`, the default. A node is a bit in a bitmap
  and, where it has one, an entry in a primitive-keyed map, instead of a map per node
  (docs/density.md, Phase 3).

    nodes / premises / in / blocked / forced mono, out, void, held
    touched / touched-in / touched-new / touched-out         RoaringBitmap
    depths                                  Int2IntOpenHashMap  (absent => 0)
    supports / consequences Int2ObjectOpenHashMap<IntPostings>  (absent => empty)
    a justification         columns keyed by id, never an object
    superseded                           atom of a persistent map  (sparse)

  The depths, the two adjacency maps and the three justification columns are reached
  through the `TmsColumns` interface, which `HeapColumns` implements with the fastutil maps,
  so every relabel, sweep and mutation is written once against the interface. The defeat
  classes are one bitmap because the lattice has two elements.

  Concurrency: a `StampedLock` gives a reader beside the writer a consistent snapshot.
  Writers take the write lock. Point reads (`in?`) are optimistic, validated after the fact
  and redone under the shared read lock if a write intervened; iterating reads take the
  shared lock. The lock is non-reentrant, so every protocol method takes it once and calls
  only raw-field helpers, and every read body is side-effect-free.

  `ensure-node` precedes `add-justification`, and a justification's antecedents already have
  nodes. Handles and justification ids must fit a 32-bit int; crossing 2^31-1 throws
  `:type :handle-ceiling` with `:remedy {:tms :reference}` (`check-handle!`).
  `jtms_dense_oracle_test` proves the two networks answer identically. See docs/nmtms.md,
  \"Two representations of the same network\"."
  (:require [taoensso.nippy :as nippy]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.jtms-protocol :refer [Tms]]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.postings :as postings]
            [vaelii.impl.types.tms :as tms-types])
  (:import [it.unimi.dsi.fastutil.ints Int2IntOpenHashMap Int2ObjectOpenHashMap]
           [java.io DataInput DataOutput]
           [java.util Arrays]
           [java.util.concurrent.atomic AtomicReference]
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

(defn- not-held?
  "Is `d` outside `held`, the `:held` forced set?  One emptiness check when it is empty."
  [^RoaringBitmap held d]
  (or (.isEmpty held) (not (rb-has? held d))))

(defn- without-held
  "`bits` less the members of `held`, a new bitmap; `bits` itself when `held` is empty."
  ^RoaringBitmap [^RoaringBitmap bits ^RoaringBitmap held]
  (if (.isEmpty held) bits (RoaringBitmap/andNot bits held)))

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
;; A justification is not stored as an object. Its belief-relevant fields are primitive
;; columns keyed by justification id: `jtms/graph-just` projects on the way in, and
;; `just-record` rebuilds one only when a caller asks (docs/density.md). `informant` splits
;; in two because it is either a rule handle or a symbol (`:premise`, a special-predicate
;; name); both columns' values are compared with `=`. A rule handle lives in `j-inf` alone,
;; and `valid?` and the adjacency read the two columns together. `strength` is one bitmap,
;; as the class map is. `subsumptions` is a sparse object column: only a firing that matched
;; a literal through a `genl` pair has one, and the dedup key reads it.

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

(defn- supports-set
  "The justification ids concluding `d`, as a set — empty for an unknown datum and for
  anything that cannot name one, nil included, as the reference's `get-in … #{}` is."
  [^TmsColumns cols d]
  (if (integer? d) (postings/ints->set (.supportsOf cols (int d))) #{}))

(defn- dependents-set
  "The justification ids citing `d`, as a set — total, as `supports-set` is."
  [^TmsColumns cols d]
  (if (integer? d) (postings/ints->set (.dependentsOf cols (int d))) #{}))

;; ---- reader/writer coordination -----------------------------------------
;;
;; A `StampedLock` restores the consistent snapshot an incidental reader is owed
;; (docs/storage.md, the single-writer contract) without taxing the engine's own single
;; writer.  See the namespace docstring's *Concurrency* note for the shape; the three
;; macros are how every method below takes its lock.

(defmacro ^:private with-write
  "Run `body` holding the write lock — writers serialize here, and a reader
  under a read lock is excluded for the duration."
  [lock & body]
  `(let [^StampedLock l# ~lock, s# (.writeLock l#)]
     (try ~@body (finally (.unlockWrite l# s#)))))

(defmacro ^:private with-read
  "Run `body` holding a shared read lock — for the iterating reads, which materialize
  O(nodes) and would tear if they walked a bitmap a writer is rewriting in place."
  [lock & body]
  `(let [^StampedLock l# ~lock, s# (.readLock l#)]
     (try ~@body (finally (.unlockRead l# s#)))))

(defmacro ^:private opt-read
  "Optimistic read of `body` — no lock in the steady state.  Redone under a shared read
  lock if a writer intervened (`validate` fails) or the lock-free body saw torn state
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
(declare add-just! begin-record! drop-just! ensure! ensure-noop? forced-bitmap held-forced held-in held-in? just-record open-hold! premise! reader-hold relabel-all! restrength-informant! retract-datum! set-blocked! set-forced! snapshot suspend-premise! sweep-from!)

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
                   ^Int2ObjectOpenHashMap j-subs
                   ^RoaringBitmap j-mono
                   ^RoaringBitmap in
                   ^RoaringBitmap blocked
                   ^RoaringBitmap touched
                   ^RoaringBitmap touched-in
                   ^RoaringBitmap touched-new
                   ;; what a forced-set change took from IN to OUT since the reset
                   ^RoaringBitmap touched-out
                   ^RoaringBitmap mono
                   ;; the forced sets (`jtms-protocol/-forced?`): premises held `:monotonic`,
                   ;; datums held OUT, justifications held void, datums IN and not believed
                   ^RoaringBitmap f-mono
                   ^RoaringBitmap f-out
                   ^RoaringBitmap f-void
                   ^RoaringBitmap f-held
                   ^clojure.lang.Atom superseded
                   ;; nil, or the open hold: `observe/new-hold`'s map plus `:touched`,
                   ;; `:in` and `:mono` bitmaps holding the labels as they were before the
                   ;; hold's first relabel moved them, `:blocked` and the three
                   ;; `:forced-*` keys holding a copy of each set taken before the hold
                   ;; first changed it (nil until then), and `:superseded`, the
                   ;; supersession map it began with
                   ^AtomicReference hold
                   ;; `{:gen n :epochs [bitmap …]}`: the touched sets' marks, each epoch what
                   ;; the touched sets recorded from one `-touch-mark` to the next; empty
                   ;; until the first mark since a reset, and outdated by `-reset-touched`
                   ^AtomicReference marks]
  ;; `@tms` yields the canonical map the reference stores natively — materialized, so
  ;; this is a testing and debugging read, never an engine path.  It takes the shared read
  ;; lock `-snapshot` takes: the map is built field by field, and a writer that sweeps a
  ;; datum between the `:nodes` read and the `:in` read leaves the snapshot holding belief
  ;; in a datum with no node (`vaelii.jtms-concurrency-test`).
  clojure.lang.IDeref
  (deref [this] (with-read lock (snapshot this)))
  Tms
  ;; The reads that answer from an open hold decide so inside the optimistic read they run
  ;; under (`reader-hold`), so a hold opening or a relabel landing between the decision
  ;; and the read fails the validation and the read is redone.
  (-believed? [this datum]
    (opt-read lock
              (if-let [h (reader-hold this)]
                (and (held-in? this h datum) (not (contains? (:superseded h) datum))
                     (not-held? (held-forced this :held) datum))
                (and (rb-has? in datum) (not (contains? @superseded datum))
                     (not-held? f-held datum)))))
  (-believed [this]
    (with-read lock
      (if-let [h (reader-hold this)]
        (seq (remove (:superseded h) (rb-longs (without-held (held-in this h) (held-forced this :held)))))
        (seq (remove @superseded (rb-longs (without-held in f-held)))))))
  (-node? [_ datum] (opt-read lock (rb-has? nodes datum)))
  (-datums [_] (with-read lock (seq (rb-longs nodes))))
  ;; O(1)/early-terminating boolean checks — a poll on the render path must neither
  ;; drain the bitmap into boxed Longs (as `(first (-datums …))` would) nor walk it
  ;; while a writer rewrites it in place.
  (-any-node? [_] (opt-read lock (not (.isEmpty ^RoaringBitmap nodes))))
  (-any-belief? [this]
    (with-read lock
      (let [h   (reader-hold this)
            ^RoaringBitmap bits (without-held (if h (held-in this h) in) (held-forced this :held))
            sup (if h (:superseded h) @superseded)]
        (and (not (.isEmpty bits))
             (or (empty? sup)
                 (let [it (.getIntIterator bits)]
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
  (-defeat-class [this datum]
    (opt-read lock
              (let [h (reader-hold this)]
                (if (and h (rb-has? (:touched h) datum))
                  (when (rb-has? (:in h) datum)
                    (if (rb-has? (:mono h) datum) :monotonic :default))
                  (when (rb-has? in datum) (if (rb-has? mono datum) :monotonic :default))))))
  (-blocked [this]
    (with-read lock
      (let [^AtomicReference r (some-> (reader-hold this) :blocked)]
        (rb-set (or (when r (.get r)) blocked)))))
  ;; the supersession map is an immutable value in an atom, always consistent on its own,
  ;; and mutated only under the write lock — so the optimistic read here is for the
  ;; decision between it and the map an open hold keeps
  (-superseded [this]
    (opt-read lock (if-let [h (reader-hold this)] (:superseded h) @superseded)))
  (-touched [_] (with-read lock (rb-set touched)))
  (-touched-in [_] (with-read lock (rb-set touched-in)))
  (-touched-new [_] (with-read lock (rb-set touched-new)))
  (-touched-out [_] (with-read lock (rb-set touched-out)))
  (-reset-touched [_]
    (with-write lock (.clear touched) (.clear touched-in) (.clear touched-new)
      (.clear touched-out)
      (.set marks {:gen (inc (long (:gen (.get marks)))) :epochs []})) nil)
  (-touch-mark [_]
    ;; a mark taken while the open epoch is empty shares it: nothing was recorded between
    ;; the two marks, so an epoch per mark would only lengthen the OR `-touched-since` runs
    (with-write lock
      (let [m0 (.get marks)
            e  ^RoaringBitmap (peek (:epochs m0))
            m  (if (and e (.isEmpty e)) m0 (update m0 :epochs conj (rb)))]
        (.set marks m)
        [(:gen m) (dec (count (:epochs m)))])))
  (-touched-since [_ mark]
    (with-read lock
      (let [{:keys [gen epochs]} (.get marks)
            [g i] mark]
        (if (and mark (= g gen) (< (long i) (count epochs)))
          (let [acc (rb)]
            (run! #(.or acc ^RoaringBitmap %) (subvec epochs i))
            (rb-set acc))
          (rb-set touched)))))
  (-supports [_ datum] (with-read lock (supports-set cols datum)))
  (-dependents [_ datum] (with-read lock (dependents-set cols datum)))
  (-justification [this jid] (with-read lock (when (rb-has? jids jid) (just-record this jid))))
  (-justifications [this] (with-read lock (seq (mapv #(just-record this %) (rb-longs jids)))))
  (-ensure-node [this datum depth]
    ;; Take the write lock only when the write would change something: a node
    ;; already present at a depth no higher than `depth` is exactly what `ensure!`
    ;; leaves (it keeps the `min` of the two).  This runs once per placement, so most
    ;; calls are that no-op, and the probe is optimistic — no lock in the steady state.
    ;; Skipping is sound under the single-writer contract: nothing moves the node
    ;; between the probe and the write that is not taken.  Same skip the reference
    ;; makes (`jtms/ensure-node`), under the same switch.
    (when-not (and observe/*chain-fast-paths* (opt-read lock (ensure-noop? this datum depth)))
      (with-write lock (begin-record! this) (ensure! this datum depth)))
    nil)
  (-add-premise [this datum strength] (with-write lock (begin-record! this) (premise! this datum strength)) nil)
  (-suspend-premise [this datum] (with-write lock (begin-record! this) (suspend-premise! this datum)) nil)
  (-add-justification [this just] (with-write lock (begin-record! this) (add-just! this just)) nil)
  (-restrength-informant [this informant strength]
    (with-write lock (begin-record! this) (restrength-informant! this informant strength)) nil)
  (-forced? [this kind x] (opt-read lock (rb-has? (held-forced this kind) x)))
  (-forced-members [this kind] (with-read lock (rb-set (held-forced this kind))))
  (-set-forced [this kind xs on?] (with-write lock (begin-record! this) (set-forced! this kind xs on?)) nil)
  (-relabel [this] (with-write lock (begin-record! this) (relabel-all! this)) nil)
  (-set-blocked [this jids] (with-write lock (begin-record! this) (set-blocked! this jids)) nil)
  (-supersede [this m]
    (with-write lock (begin-record! this) (reset! superseded (if (map? m) m (into {} m))))
    nil)
  (-retract [this datum] (with-write lock (begin-record! this) (retract-datum! this datum)))
  (-sweep [this seeds] (with-write lock (begin-record! this) (sweep-from! this seeds)))
  (-drop-justification [this jid] (with-write lock (begin-record! this) (drop-just! this jid)))
  (-snapshot [this] (with-read lock (snapshot this)))
  (-hold [this h] (with-write lock (open-hold! this h)))
  (-release [_ h] (with-write lock (when (identical? h (:hold (.get hold))) (.set hold nil))) nil)
  (-held [_] (:hold (.get hold))))

;; ---- the hold ------------------------------------------------------------
;;
;; `vaelii.impl.jtms-protocol`'s `-hold`: a settle opens one on its network, and until it
;; closes, a thread other than its owner reads the labels as they stood when it opened.
;; The first relabel to move a label records its value before the move (`relabel-region!`),
;; and the blocked set is copied before its first change, so the cost is the region each
;; relabel already walks plus one copy of that small set.

(defn- open-hold!
  "Open hold `h` on `this`, whose write lock the caller holds: true, or false when a hold
  is open already."
  [^DenseTms this h]
  (let [^AtomicReference r (.-hold this)]
    (if (some? (.get r))
      false
      (do (.set r {:hold       h
                   :touched    (rb)
                   :in         (rb)
                   :mono       (rb)
                   :blocked    (AtomicReference. nil)
                   :forced-mono (AtomicReference. nil)
                   :forced-out  (AtomicReference. nil)
                   :forced-void (AtomicReference. nil)
                   :forced-held (AtomicReference. nil)
                   :superseded @^clojure.lang.Atom (.-superseded this)})
          true))))

(defn- open-epoch
  "The open epoch, the bitmap the last `-touch-mark` opened, or nil before the
  first mark since a reset.  Written under the write lock, as `touched` is."
  ^RoaringBitmap [^DenseTms this]
  (peek (:epochs (.get ^AtomicReference (.-marks this)))))

(defn- reader-hold
  "The open hold, when the current thread reads the labels it keeps (not its owner, and
  `observe/reads-held?`), else nil — one field read when no hold is open.  Called inside
  the lock or optimistic read the read takes: the hold is opened and released under the
  write lock, and registered after it opens and unregistered before it is released, so a
  validated read that finds it unregistered reads labels no settle was deciding."
  [^DenseTms this]
  (let [st (.get ^AtomicReference (.-hold this))]
    (when (and st
               (not (identical? (:owner (:hold st)) (Thread/currentThread)))
               (observe/reads-held? (:hold st)))
      st)))

(defn- held-in?
  "Was `d` IN when hold `st` opened?"
  [^DenseTms this st d]
  (if (rb-has? (:touched st) d)
    (rb-has? (:in st) d)
    (rb-has? ^RoaringBitmap (.-in this) d)))

(defn- held-in
  "The IN set as it stood when hold `st` opened, as a new bitmap."
  ^RoaringBitmap [^DenseTms this st]
  (doto (RoaringBitmap/andNot ^RoaringBitmap (.-in this) ^RoaringBitmap (:touched st))
    (.or ^RoaringBitmap (:in st))))

(def ^:private forced-hold-key
  {:mono :forced-mono :out :forced-out :void :forced-void :held :forced-held})

(defn- forced-bitmap
  "The live bitmap of forced set `kind`."
  ^RoaringBitmap [^DenseTms this kind]
  (case kind
    :mono (.-f-mono this)
    :out  (.-f-out this)
    :void (.-f-void this)
    :held (.-f-held this)))

(defn- held-forced
  "Forced set `kind` as the current thread reads it: the copy an open hold kept, for a
  thread that reads the hold (`reader-hold`), and the live bitmap otherwise."
  ^RoaringBitmap [^DenseTms this kind]
  (or (when-let [st (reader-hold this)]
        (.get ^AtomicReference (get st (forced-hold-key kind))))
      (forced-bitmap this kind)))

(defn- keep-copy!
  "Copy `live` under `k` in `st`, an open hold or this network's write record, unless a
  copy is there already."
  [st k ^RoaringBitmap live]
  (let [^AtomicReference r (get st k)]
    (when (nil? (.get r)) (.set r (.clone live)))))

(defn- keep-held!
  "Copy `live`, the network's `k` set, into the open hold and the open write record
  before its first change there, so each reads the set as it stood when it opened."
  [^DenseTms this k ^RoaringBitmap live]
  (when-let [st (.get ^AtomicReference (.-hold this))] (keep-copy! st k live))
  (when-let [st (observe/recorded this)] (keep-copy! st k live)))

;; ---- the write record ------------------------------------------------------
;;
;; While a write record is open (`observe/*write-record*`), every mutating method opens
;; this network's entry before it moves anything (`begin-record!`), and each move records
;; the value it replaces: the labels and classes as the hold keeps them, a copy of each
;; set as the hold keeps it, the supersession map, and per handle or id the premise
;; marks, the node and the justification.  `before-network` reads the network as it stood.

(defn- begin-record!
  "Open this network's entry in the write record, when one is open and holds none: the
  label, class and set slots a hold has, the supersession map as it stands, and the
  empty `{handle [premise? mono?]}`, `{handle depth-or-nil}` and `{jid
  justification-or-nil}` maps the moves fill."
  [^DenseTms this]
  (when observe/*write-record*
    (observe/record-of this (fn [] {:touched     (rb)
                                    :in          (rb)
                                    :mono        (rb)
                                    :blocked     (AtomicReference. nil)
                                    :forced-mono (AtomicReference. nil)
                                    :forced-out  (AtomicReference. nil)
                                    :forced-void (AtomicReference. nil)
                                    :forced-held (AtomicReference. nil)
                                    :superseded  @^clojure.lang.Atom (.-superseded this)
                                    :premises    (java.util.HashMap.)
                                    :nodes       (java.util.HashMap.)
                                    :justs       (java.util.HashMap.)}))))

(defn- keep-premise!
  "Record `d`'s premise marks `[premise? mono?]` before their first change."
  [^DenseTms this d]
  (when-let [st (observe/recorded this)]
    (let [^java.util.HashMap m (:premises st) k (long d)]
      (when-not (.containsKey m k)
        (.put m k [(rb-has? (.-premises this) d) (rb-has? (.-mono-premises this) d)])))))

(defn- keep-node!
  "Record whether `d` has a node, as its depth or nil, before the node is made or swept."
  [^DenseTms this d]
  (when-let [st (observe/recorded this)]
    (let [^java.util.HashMap m (:nodes st) k (long d)]
      (when-not (.containsKey m k)
        (.put m k (when (rb-has? (.-nodes this) d) (long (.depthOf ^TmsColumns (.-cols this) (int d)))))))))

(defn- keep-just!
  "Record justification `jid` as it stands, or nil when it is not stored, before it is
  added, unlinked or changes class."
  [^DenseTms this jid]
  (when-let [st (observe/recorded this)]
    (let [^java.util.HashMap m (:justs st) k (long jid)]
      (when-not (.containsKey m k)
        (.put m k (when (rb-has? (.-jids this) jid) (just-record this jid)))))))

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
  (cond-> (tms-types/->Justification
           (long jid)
           (j-informant this jid)
           (into [] (map long) (j-antecedents this jid))
           (j-consequence this jid)
           nil
           (if (rb-has? ^RoaringBitmap (.-j-mono this) jid) :monotonic :default))
    (.containsKey ^Int2ObjectOpenHashMap (.-j-subs this) (int jid))
    (assoc :subsumptions (.get ^Int2ObjectOpenHashMap (.-j-subs this) (int jid)))))

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
  the informant is a rule handle, not blocked by its rule's exception, and not void?"
  [^DenseTms this jid ^RoaringBitmap in ^RoaringBitmap blocked]
  (and (not (.contains blocked (int jid)))
       (not (.contains ^RoaringBitmap (.-f-void this) (int jid)))
       (all-in? (j-antecedents this jid) in)
       (let [i (j-informant-int this jid)]
         (or (== i no-informant) (.contains in (int i))))))

(defn- conferred-class
  "The class a valid justification confers: its own strength, capped by the weakest of
  its antecedents' classes, and by its rule's class when the informant is a rule handle
  that is not a premise.  Under `jtms/respell-informant` only the first antecedent caps
  it (`jtms/class-antecedents`)."
  [^DenseTms this jid ^RoaringBitmap classes]
  (let [antes (j-antecedents this jid)
        inf   (j-informant-int this jid)
        n     (if (and (> (alength antes) 1)
                       (== no-informant inf)
                       (= jtms/respell-informant
                          (.get ^Int2ObjectOpenHashMap (.-j-inf-sym this) (int jid))))
                1
                (alength antes))
        acc   (if (and (not (== no-informant inf))
                       (not (rb-has? ^RoaringBitmap (.-premises this) inf))
                       (rb-has? ^RoaringBitmap (.-j-mono this) jid))
                (if (.contains classes (int inf)) :monotonic :default)
                (if (rb-has? ^RoaringBitmap (.-j-mono this) jid) :monotonic :default))]
    (loop [i 0, acc acc]
      (if (== i n)
        acc
        (recur (unchecked-inc i)
               (strength/min acc (if (.contains classes (aget antes i)) :monotonic :default)))))))

(defn- node-class
  "The strongest support an IN datum has: its premise strength, and what each currently
  valid justification confers.  A blocked justification is not valid, so it confers
  nothing — exactly as if it were missing an antecedent."
  [^DenseTms this d ^RoaringBitmap in ^RoaringBitmap classes]
  (let [blocked ^RoaringBitmap (.-blocked this)
        live    ^RoaringBitmap (.-jids this)
        prem    (when (rb-has? ^RoaringBitmap (.-premises this) d)
                  (if (or (rb-has? ^RoaringBitmap (.-mono-premises this) d)
                          (rb-has? ^RoaringBitmap (.-f-mono this) d))
                    :monotonic
                    :default))
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
  "Least fixpoint of IN over `region`, accumulated into `acc`, the live bitmap with the region
  already cleared out of it, so what it holds on entry is the boundary and the fixpoint only
  adds region members back. Semi-naive: `valid?` is monotone in `in`, so a justification is
  retried only when one of its antecedents newly enters, through the stored inverse edge.
  Accumulating into the live bitmap, not a clone, keeps a relabel proportional to the region
  (docs/defenses.md, \"Locality is a claim about every representation\")."
  [^DenseTms this ^RoaringBitmap region cands ^RoaringBitmap acc]
  (let [blocked ^RoaringBitmap (.-blocked this)
        out     ^RoaringBitmap (.-f-out this)]
    ;; seed: the region's own premises, less the forced-out ones
    (.or acc (doto (RoaringBitmap/and region ^RoaringBitmap (.-premises this)) (.andNot out)))
    (loop [stack (vec cands)]
      (if (empty? stack)
        nil
        (let [jid   (peek stack)
              stack (pop stack)
              c     (j-consequence this jid)]
          (if (and (not (neg? c))
                   (rb-has? region c)
                   (not (rb-has? acc c))
                   (not (rb-has? out c))
                   (valid? this jid acc blocked))
            (do (rb-add! acc c)
                (let [ids (dependents-of this c)]
                  (recur (areduce ids i a stack (conj a (aget ids i))))))
            (recur stack)))))))

(defn- region-classes!
  "Defeat-classes for `region` under `in`, as a least fixpoint: every in-region IN node starts
  at the lattice's bottom and the equation is iterated to stability. `classes` is the live monotonic bitmap with the region already
  cleared out of it, mutated in place; an OUT datum has no class and an IN one restarts at
  `:default` (absent from the bitmap)."
  [^DenseTms this ^RoaringBitmap region ^RoaringBitmap in ^RoaringBitmap classes]
  (let [members (RoaringBitmap/and region in)
        ;; the nodes on the stack: a node a rise reaches through several of its
        ;; justifications is pushed once and evaluated once, after every rise before it
        pending (.clone members)]
    ;; The lattice has height one, so a member rises at most once and the worklist only
    ;; ever ADDS — which is exactly what makes this the least fixpoint rather than some
    ;; fixpoint.
    (loop [stack (rb-longs members)]
      (if (empty? stack)
        nil
        (let [d     (peek stack)
              stack (pop stack)]
          (rb-del! pending d)
          (if (or (rb-has? classes d)
                  (not= :monotonic (node-class this d in classes)))
            (recur stack)
            (do (rb-add! classes d)
                (let [ids (dependents-of this d)]
                  (recur (areduce ids i acc stack
                                  (let [c (j-consequence this (aget ids i))]
                                    (if (and (not (neg? c)) (rb-has? in c)
                                             (not (rb-has? classes c)) (not (rb-has? pending c)))
                                      (do (rb-add! pending c) (conj acc c))
                                      acc))))))))))))

(defn- relabel-region!
  "Recompute belief and the classes for `region`, holding everything outside it fixed
  (docs/nmtms.md, \"Locality\")."
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
        mono    ^RoaringBitmap (.-mono this)
        ;; Which of the region no relabel since the reset has reached yet, and of those which are
        ;; believed *now* — read FIRST, because the fixpoint below overwrites the region's
        ;; labels in place and the prior ones are then gone.  See `jtms/touched-in`.
        fresh    (RoaringBitmap/andNot region ^RoaringBitmap (.-touched this))
        ;; a `:held` member is IN and was not believed
        fresh-in (without-held (RoaringBitmap/and fresh in) (.-f-held this))]
    ;; ...and the same record for an open hold, whose readers read the labels as they
    ;; were before its first relabel moved them, and for the open write record — read
    ;; FIRST for the same reason
    (doseq [st [(.get ^AtomicReference (.-hold this)) (observe/recorded this)] :when st]
      (let [^RoaringBitmap ht (:touched st)
            f (RoaringBitmap/andNot region ht)]
        (.or ^RoaringBitmap (:in st) (RoaringBitmap/and f in))
        (.or ^RoaringBitmap (:mono st) (RoaringBitmap/and f mono))
        (.or ht f)))
    ;; Clearing the region out of the live bitmap leaves exactly the boundary, which is
    ;; what the fixpoint starts from and holds fixed.  In place: the static `andNot`
    ;; copies every container of a bitmap the size of the believed set, where the mutating
    ;; one is a merge over the container lists and touches only the region's own.
    (.andNot in region)
    (region-fixpoint! this region cands in)
    ;; the classes are a function of the NEW in-set, and of the current `mono` outside the
    ;; region for their boundary — so the region is cleared out of `mono` and no further
    (.andNot mono region)
    (region-classes! this region in mono)
    (.or ^RoaringBitmap (.-touched-in this) fresh-in)
    ;; A supporter's belief can flip only inside a relabelled region, so the accumulated
    ;; touched set is a superset of every handle whose belief moved this settle — what
    ;; `tax/refresh-beliefs` reads to skip a cache no moved supporter touches.
    (.or ^RoaringBitmap (.-touched this) region)
    (when-let [e (open-epoch this)] (.or e region))
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
  `min` of the stored depth and the asked one, so the write lock buys nothing there.

  Total, as every read here is: false for anything that cannot name a node — nil, a
  non-integer, or a handle past `max-handle` — so the refusal stays `check-handle!`'s to
  raise from inside `ensure!` rather than becoming a cast error from this probe."
  [^DenseTms this datum depth]
  (and (integer? datum)
       (<= (long datum) max-handle)
       (rb-has? ^RoaringBitmap (.-nodes this) datum)
       (<= (long (.depthOf ^TmsColumns (.-cols this) (int datum))) (long depth))))

(defn- consequence-or-nil
  "`j-consequence`, nil for an id no longer stored — the reading `jtms/lowered-depths` and
  `jtms/region-depths` take."
  [^DenseTms this jid]
  (let [c (j-consequence this jid)] (when-not (neg? c) c)))

(defn- lower-depth!
  "Lower `d` to `depth` and push the fall down its consequences (`jtms/lowered-depths`)."
  [^DenseTms this d depth]
  (let [cols ^TmsColumns (.-cols this)]
    (doseq [[x v] (jtms/lowered-depths d depth
                                       #(dependents-of this %)
                                       #(j-antecedents this %)
                                       #(consequence-or-nil this %)
                                       #(.depthOf cols (int %)))]
      (.setDepth cols (int x) (int v)))))

(defn- redepth!
  "Re-solve the depths over the consequence closure of those `seeds` still in the graph
  (`jtms/redepth*`'s dense half)."
  [^DenseTms this seeds]
  (let [live (filterv #(rb-has? ^RoaringBitmap (.-nodes this) %) seeds)]
    (when (seq live)
      (let [cols ^TmsColumns (.-cols this)]
        (doseq [[d v] (jtms/region-depths (rb-longs (affected-region this live))
                                          #(rb-has? ^RoaringBitmap (.-premises this) %)
                                          #(supports-of this %)
                                          #(dependents-of this %)
                                          #(j-antecedents this %)
                                          #(consequence-or-nil this %)
                                          #(.depthOf cols (int %)))]
          (.setDepth cols (int d) (int v)))))))

(defn- ensure! [^DenseTms this datum depth]
  (let [d    (int (check-handle! datum "node handle"))
        cols ^TmsColumns (.-cols this)]
    (if (rb-has? ^RoaringBitmap (.-nodes this) d)
      (when (< (long depth) (long (.depthOf cols d)))
        (lower-depth! this d depth))
      ;; the touched sets' record of what was created, taken here because this is the only
      ;; line that knows — see `jtms/touched-new`
      (do (keep-node! this d)
          (rb-add! ^RoaringBitmap (.-nodes this) d)
          (rb-add! ^RoaringBitmap (.-touched-new this) d)
          (.setDepth cols d (int depth))))
    nil))

(defn- premise!
  "Mark `datum` a premise and relabel its region, except where the mark is one the node
  already holds at the same class and the node is IN: `jtms/premise*`'s fast path, which
  relabels nothing and notes `datum` alone as touched."
  [^DenseTms this datum strength-kw]
  (ensure! this datum 0)
  (let [mono?    (= :monotonic strength-kw)
        premises ^RoaringBitmap (.-premises this)
        monos    ^RoaringBitmap (.-mono-premises this)]
    (if (and (rb-has? premises datum)
             (= mono? (rb-has? monos datum))
             (rb-has? ^RoaringBitmap (.-in this) datum))
      (let [t ^RoaringBitmap (.-touched this)]
        (when-not (or (rb-has? t datum) (rb-has? ^RoaringBitmap (.-f-held this) datum))
          (rb-add! ^RoaringBitmap (.-touched-in this) datum))
        (rb-add! t datum)
        (when-let [e (open-epoch this)] (rb-add! e datum)))
      (do (keep-premise! this datum)
          (rb-add! premises datum)
          (if mono? (rb-add! monos datum) (rb-del! monos datum))
          (resettle! this [datum])))))

(defn- suspend-premise!
  "Drop the premise mark and relabel the affected closure — `retract-datum!` without
  the sweep, so nothing is deleted and `premise!` puts it back exactly."
  [^DenseTms this datum]
  (when (rb-has? ^RoaringBitmap (.-nodes this) datum)
    (keep-premise! this datum)
    (rb-del! ^RoaringBitmap (.-premises this) datum)
    (rb-del! ^RoaringBitmap (.-mono-premises this) datum)
    (relabel-region! this (affected-region this [datum]))
    (redepth! this [datum]))
  nil)

(defn- add-just!
  "Record `just` and relabel only what it moves. A redundant justification (its consequence
  already believed, conferring no stronger a class, or not valid) moves nothing, so the
  forward closure is walked once, when a fact is first derived. Any real change takes the
  full resettle."
  [^DenseTms this just]
  (let [{:keys [id informant antecedents consequence strength subsumptions]} (jtms/graph-just just)
        jid   (int (check-handle! id "justification id"))
        cols  ^TmsColumns (.-cols this)
        in    ^RoaringBitmap (.-in this)
        mono  ^RoaringBitmap (.-mono this)]
    (keep-just! this jid)
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
    (if subsumptions
      (.put ^Int2ObjectOpenHashMap (.-j-subs this) jid subsumptions)
      (.remove ^Int2ObjectOpenHashMap (.-j-subs this) jid))
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
      ;; the datum while moving no label, and `touched-in` takes it unless a relabel since the
      ;; reset has reached it already
      (let [t ^RoaringBitmap (.-touched this)]
        (when-not (rb-has? t consequence)
          (rb-add! ^RoaringBitmap (.-touched-in this) consequence))
        (rb-add! t consequence)
        (when-let [e (open-epoch this)] (rb-add! e consequence)))
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
              (do (keep-just! this jid)
                  (if mono? (rb-add! jmono jid) (rb-del! jmono jid))
                  (let [c (j-consequence this jid)]
                    (recur (inc i) (if (neg? c) seeds (conj! seeds c)))))
              (recur (inc i) seeds)))
          (let [s (persistent! seeds)]
            (when (seq s) (resettle! this s))))))))

(defn- set-blocked!
  "Replace the blocked set with the ids of `jids` the network holds, and relabel what moved.
  Only the justifications whose blocked status actually changed can move a label, so they
  alone seed the region — a call that changes nothing does no work at all."
  [^DenseTms this jids]
  (let [want    (RoaringBitmap/and (reduce rb-add! (rb) jids) (.-jids this))
        blocked ^RoaringBitmap (.-blocked this)
        changed (RoaringBitmap/xor want blocked)]
    (when-not (.isEmpty changed)
      (keep-held! this :blocked blocked)
      (let [seeds (into [] (keep #(let [c (j-consequence this %)] (when-not (neg? c) c)))
                        (rb-longs changed))]
        (doto blocked (.clear) (.or want))
        (resettle! this seeds)))))

(defn- set-forced!
  "Add each of `xs` to forced set `kind` (`on?`) or take it out, and relabel the region
  the moved members reach: the datums with a node for `:mono` and `:out`, the
  consequences of the stored justifications for `:void`.  A `:held` move relabels
  nothing and records its IN members in the touched sets (`jtms/set-forced*`)."
  [^DenseTms this kind xs on?]
  (let [r     (forced-bitmap this kind)
        on?   (boolean on?)
        moved (into [] (comp (distinct) (filter #(not= on? (rb-has? r %)))) xs)]
    (when (seq moved)
      (keep-held! this (forced-hold-key kind) r)
      (doseq [x moved] (if on? (rb-add! r x) (rb-del! r x)))
      (if (= :held kind)
        (let [live    (doto ^RoaringBitmap (reduce rb-add! (rb) moved) (.and ^RoaringBitmap (.-in this)))
              touched ^RoaringBitmap (.-touched this)]
          (when on?
            (.or ^RoaringBitmap (.-touched-in this) (RoaringBitmap/andNot live touched))
            (.or ^RoaringBitmap (.-touched-out this) live))
          (.or touched live)
          (when-let [e (open-epoch this)] (.or e live)))
        (let [region (affected-region this (if (= :void kind)
                                             (into [] (keep #(consequence-or-nil this %)) moved)
                                             (filterv #(rb-has? ^RoaringBitmap (.-nodes this) %) moved)))
              was    (RoaringBitmap/and region ^RoaringBitmap (.-in this))]
          (relabel-region! this region)
          ;; what the change took OUT, for `jtms/revived` to re-seed if it comes back
          (.or ^RoaringBitmap (.-touched-out this) (RoaringBitmap/andNot was ^RoaringBitmap (.-in this))))))))

(defn- relabel-all!
  "Whole-graph relabel — no engine path calls it, so this is the differential oracle's
  whole-graph operation, which is why both representations carry it (`jtms/relabel`).

  Blocking and supersession are **cleared first**: nothing about an exception or an
  equality merge is stored, so a whole-graph relabel can read neither back, and one that
  merged into whatever was there could only ever *add* — leaving a block standing for a
  justification whose exception no longer holds.  It lands unblocked, and a caller that
  wants either states the whole answer again."
  [^DenseTms this]
  (keep-held! this :blocked (.-blocked this))
  (.clear ^RoaringBitmap (.-blocked this))
  (reset! ^clojure.lang.Atom (.-superseded this) {})
  (relabel-region! this (.clone ^RoaringBitmap (.-nodes this))))

;; ---- retraction ---------------------------------------------------------

(defn- unlink-just!
  "Take justification `jid` out of the columns: its live bit, its informant and class
  slots, its consequence's support list and every dependent list it sits in.  No
  relabel.  Reads the adjacency before the columns drop it."
  [^DenseTms this jid]
  (let [antes (j-antecedents this jid)
        inf   (j-informant-int this jid)
        c     (j-consequence this jid)
        cols  ^TmsColumns (.-cols this)
        k     (int jid)]
    (keep-just! this jid)
    (rb-del! ^RoaringBitmap (.-jids this) k)
    (.dropJustification cols k)
    (.remove ^Int2ObjectOpenHashMap (.-j-inf-sym this) k)
    (.remove ^Int2ObjectOpenHashMap (.-j-subs this) k)
    (rb-del! ^RoaringBitmap (.-j-mono this) k)
    (.removeSupport cols (int c) k)
    (dotimes [i (alength antes)] (.removeDependent cols (aget antes i) k))
    (when-not (== inf no-informant) (.removeDependent cols (int inf) k))))

(defn- sweep!
  "Collect the datums in `suspects` that are no longer structurally derivable and are not
  premises, tear them and every justification touching them out of the graph, and return the
  removals for the caller to apply to its own stores. A survivor that lost a justification,
  and each of `raised`, has its depth re-solved (`redepth!`). Nothing forces a node OUT, so
  this also collects an excepted conclusion. Region-local: the justifications come off the
  dead nodes' own adjacency, never a scan of `jids`."
  [^DenseTms this ^RoaringBitmap suspects raised]
  (let [ground ^RoaringBitmap (.-in this)
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
        removed-justs (into [] (remove #(= :premise (j-informant this %))) dead-jids)
        supports      (mapv #(vector (j-consequence this %) (j-informant this %)) removed-justs)
        ;; the survivors among these lost a justification
        lost          (into (vec raised) (keep #(consequence-or-nil this %)) dead-jids)]
    (doseq [jid dead-jids] (unlink-just! this jid))
    (doseq [d dead]
      (keep-node! this d)
      (rb-del! ^RoaringBitmap (.-nodes this) d)
      (rb-del! ^RoaringBitmap (.-premises this) d)
      (rb-del! ^RoaringBitmap (.-mono-premises this) d)
      (rb-del! ^RoaringBitmap (.-mono this) d)
      (when (rb-has? ^RoaringBitmap (.-f-mono this) d)
        (keep-held! this :forced-mono (.-f-mono this))
        (rb-del! ^RoaringBitmap (.-f-mono this) d))
      (when (rb-has? ^RoaringBitmap (.-f-out this) d)
        (keep-held! this :forced-out (.-f-out this))
        (rb-del! ^RoaringBitmap (.-f-out this) d))
      (when (rb-has? ^RoaringBitmap (.-f-held this) d)
        (keep-held! this :forced-held (.-f-held this))
        (rb-del! ^RoaringBitmap (.-f-held this) d))
      ;; the swept nodes were OUT, so dropping them cannot move any survivor's label —
      ;; only the bookkeeping needs the removal
      (rb-del! ^RoaringBitmap (.-in this) d)
      (.dropNode cols (int d)))
    ;; a block names a justification and a supersession names a datum, so a swept one
    ;; must lose both — an entry left behind would be reapplied to whatever reuses the id
    (when (seq dead-jids) (keep-held! this :blocked (.-blocked this)))
    (doseq [jid dead-jids] (rb-del! ^RoaringBitmap (.-blocked this) jid))
    (doseq [jid dead-jids :when (rb-has? ^RoaringBitmap (.-f-void this) jid)]
      (keep-held! this :forced-void (.-f-void this))
      (rb-del! ^RoaringBitmap (.-f-void this) jid))
    ;; one transient pass rather than `apply dissoc`, whose per-key HAMT path copy `dead`
    ;; — a whole swept region — would pay for on every `exceptWhen` block (`jtms/dissoc-all`)
    (swap! ^clojure.lang.Atom (.-superseded this) jtms/dissoc-all dead)
    (redepth! this lost)
    (cond-> {:removed-sentexes dead :removed-justifications removed-justs}
      (seq supports) (assoc :removed-supports supports))))

(defn- retract-datum!
  "Dependency-directed retraction: drop the premise, relabel the affected closure (a
  suspect re-derivable by another witness stays IN), then sweep what the retraction
  solely supported.  An unknown datum is a no-op — retraction is idempotent, and
  materializing the node would let the sweep collect a phantom and claim a removal that
  never happened."
  [^DenseTms this datum]
  (if-not (rb-has? ^RoaringBitmap (.-nodes this) datum)
    {:removed-sentexes [] :removed-justifications []}
    (do (keep-premise! this datum)
        (rb-del! ^RoaringBitmap (.-premises this) datum)
        (rb-del! ^RoaringBitmap (.-mono-premises this) datum)
        ;; marking and relabelling walk the graph once between them: the affected
        ;; closure is both the suspect set and the region to relabel
        (let [suspects (affected-region this [datum])]
          (relabel-region! this suspects)
          (sweep! this suspects [datum])))))

(defn- sweep-from! [^DenseTms this seeds]
  (sweep! this (affected-region this seeds) nil))

(defn- drop-just!
  "`jtms/drop-justification!`'s dense half: unlink `jid`, unblock it, relabel its
  consequence's region and sweep it.  An unknown `jid` is a no-op."
  [^DenseTms this jid]
  (if-not (rb-has? ^RoaringBitmap (.-jids this) jid)
    {:removed-sentexes [] :removed-justifications []}
    (let [c   (j-consequence this jid)
          inf (j-informant this jid)]
      (unlink-just! this jid)
      (keep-held! this :blocked (.-blocked this))
      (rb-del! ^RoaringBitmap (.-blocked this) jid)
      (when (rb-has? ^RoaringBitmap (.-f-void this) jid)
        (keep-held! this :forced-void (.-f-void this))
        (rb-del! ^RoaringBitmap (.-f-void this) jid))
      (let [suspects (affected-region this [c])]
        (relabel-region! this suspects)
        (update (sweep! this suspects [c]) :removed-supports (fnil conj []) [c inf])))))

;; ---- the network before the write ----------------------------------------------

(defn before-network
  "`this` as it stood when the open write record opened its entry for it
  (`begin-record!`), as a read-only `Tms`, or `this` itself when the record holds none.
  A value no move recorded is read off the live network, which no move since changed.
  Answers the reads the read walk makes: labels, classes, premise marks, nodes, the
  support and dependent ids, justifications, the blocked and forced sets and the
  supersession map.  Every other method throws."
  [^DenseTms this]
  (if-let [st (observe/recorded this)]
    (let [lock  ^StampedLock (.-lock this)
          cols  ^TmsColumns (.-cols this)
          ^java.util.HashMap justs (:justs st)
          ^java.util.HashMap prems (:premises st)
          ^java.util.HashMap nodes (:nodes st)
          ^RoaringBitmap t (:touched st)
          gone  (filterv some? (vals justs))
          by-c  (group-by #(long (:consequence %)) gone)
          by-a  (reduce (fn [m j] (reduce #(update %1 (long %2) (fnil conj []) j) m (jtms/rests-on j)))
                        {} gone)
          ids   (fn [live extra] (-> (into #{} (remove #(.containsKey justs (long %))) live)
                                     (into (map :id) extra)))
          k     (fn [d] (when (integer? d) (long d)))
          kept  (fn [key ^RoaringBitmap live] ^RoaringBitmap (or (.get ^AtomicReference (get st key)) live))
          no    (fn [m] (throw (UnsupportedOperationException.
                                (str "the network before the write does not answer " m))))]
      (reify Tms
        (-believed? [_ d]
          (and (if (rb-has? t d)
                 (rb-has? (:in st) d)
                 (opt-read lock (rb-has? (.-in this) d)))
               (not (contains? (:superseded st) d))
               (opt-read lock (not-held? (kept :forced-held (.-f-held this)) d))))
        (-defeat-class [_ d]
          (if (rb-has? t d)
            (when (rb-has? (:in st) d) (if (rb-has? (:mono st) d) :monotonic :default))
            (opt-read lock (when (rb-has? (.-in this) d)
                             (if (rb-has? (.-mono this) d) :monotonic :default)))))
        (-node? [_ d]
          (if (and (k d) (.containsKey nodes (k d)))
            (some? (.get nodes (k d)))
            (opt-read lock (rb-has? (.-nodes this) d))))
        (-depth [_ d]
          (cond (not (integer? d))            0
                (.containsKey nodes (k d))    (or (.get nodes (k d)) 0)
                :else (opt-read lock (long (.depthOf cols (int d))))))
        (-premise? [_ d]
          (if (and (k d) (.containsKey prems (k d)))
            (first (.get prems (k d)))
            (opt-read lock (rb-has? (.-premises this) d))))
        (-premise-strength [_ d]
          (if (and (k d) (.containsKey prems (k d)))
            (let [[p? m?] (.get prems (k d))] (when p? (if m? :monotonic :default)))
            (opt-read lock (when (rb-has? (.-premises this) d)
                             (if (rb-has? (.-mono-premises this) d) :monotonic :default)))))
        (-supports [_ d] (ids (jtms/supports this d) (get by-c (k d))))
        (-dependents [_ d] (ids (jtms/dependents this d) (get by-a (k d))))
        (-justification [_ jid]
          (if (and (k jid) (.containsKey justs (k jid)))
            (.get justs (k jid))
            (jtms/justification this jid)))
        (-blocked [_] (with-read lock (rb-set (kept :blocked (.-blocked this)))))
        (-forced? [_ kind x]
          (opt-read lock (rb-has? (kept (forced-hold-key kind) (forced-bitmap this kind)) x)))
        (-forced-members [_ kind]
          (with-read lock (rb-set (kept (forced-hold-key kind) (forced-bitmap this kind)))))
        (-superseded [_] (:superseded st))
        (-held [_] nil)
        (-datums [_] (no '-datums))
        (-any-node? [_] (no '-any-node?))
        (-justifications [_] (no '-justifications))
        (-believed [_] (no '-believed))
        (-any-belief? [_] (no '-any-belief?))
        (-snapshot [_] (no '-snapshot))
        (-touched [_] (no '-touched))
        (-touched-in [_] (no '-touched-in))
        (-touched-new [_] (no '-touched-new))
        (-touched-out [_] (no '-touched-out))
        (-reset-touched [_] (no '-reset-touched))
        (-touch-mark [_] (no '-touch-mark))
        (-touched-since [_ _] (no '-touched-since))
        (-ensure-node [_ _ _] (no '-ensure-node))
        (-add-premise [_ _ _] (no '-add-premise))
        (-suspend-premise [_ _] (no '-suspend-premise))
        (-add-justification [_ _] (no '-add-justification))
        (-restrength-informant [_ _ _] (no '-restrength-informant))
        (-set-forced [_ _ _ _] (no '-set-forced))
        (-relabel [_] (no '-relabel))
        (-set-blocked [_ _] (no '-set-blocked))
        (-supersede [_ _] (no '-supersede))
        (-retract [_ _] (no '-retract))
        (-sweep [_ _] (no '-sweep))
        (-drop-justification [_ _] (no '-drop-justification))
        (-hold [_ _] (no '-hold))
        (-release [_ _] (no '-release))))
    this))

;; ---- the byte image -------------------------------------------------------
;;
;; The whole network as bytes, written between operations and read back into an empty
;; network with no relabel: every label, class, block and supersession is read, not
;; recomputed. `vaelii.impl.reasoning-image` decides whether an image may be installed. The
;; touched sets are not written, and keys are written in sorted order, so two images of
;; equal networks are equal bytes. A zero depth is not written.

(def image-version
  "The byte image's layout number.  `read-image!` refuses any other, so an image of
  another layout is discarded rather than misread."
  6)

(def ^:private ^:const image-magic 0x76544D53)

(defn- image-bitmaps
  "The bitmaps an image carries, in the order it writes them."
  [^DenseTms t]
  [(.-nodes t) (.-premises t) (.-mono-premises t) (.-jids t) (.-j-mono t)
   (.-in t) (.-blocked t) (.-mono t) (.-f-mono t) (.-f-out t) (.-f-void t) (.-f-held t)])

(defn- sorted-keys ^ints [m]
  (let [^ints a (if (instance? Int2IntOpenHashMap m)
                  (.toIntArray (.keySet ^Int2IntOpenHashMap m))
                  (.toIntArray (.keySet ^Int2ObjectOpenHashMap m)))]
    (Arrays/sort a)
    a))

(defn- write-bitmap! [^DataOutput o ^RoaringBitmap r]
  ;; a clone, because `runOptimize` rewrites containers and the writer holds only a read
  ;; lock over the live one
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

(defn- read-data
  "A `write-data!` frame, thawed behind the class-name check: an image is a file, and a
  file is untrusted input (`vaelii.impl.io.thaw`).  Its symbols are the symbol
  pool's (`safe/sharing`): an informant names a special predicate per justification."
  [^DataInput i]
  (let [b (byte-array (.readInt i))]
    (.readFully i b)
    (safe/thaw b (safe/sharing))))

(defn- heap-cols
  "`t`'s columns as `HeapColumns`, which are the only columns the byte image writes and
  reads.  Throws `IllegalStateException` for any other implementation."
  ^HeapColumns [^DenseTms t]
  (let [c (.-cols t)]
    (if (instance? HeapColumns c)
      c
      (throw (IllegalStateException. "the byte image writes and reads HeapColumns only")))))

(defn write-image
  "Write the whole of dense network `t` to `o`, under a read lock, so a concurrent reader
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
    (doseq [m [(.-j-inf-sym t) (.-j-subs t)]]
      (write-data! o (mapv (fn [k] [k (.get ^Int2ObjectOpenHashMap m (int k))]) (sorted-keys m))))
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
    (doseq [^Int2ObjectOpenHashMap m [(.-j-inf-sym t) (.-j-subs t)]]
      (doseq [[k v] (read-data i)] (.put m (int k) v)))
    (reset! (.-superseded t) (into {} (read-data i))))
  t)

(defn node-count
  "How many nodes dense network `t` holds — the bitmap's cardinality, read under a read
  lock without materializing a handle."
  ^long [^DenseTms t]
  (with-read (.-lock t) (.getLongCardinality ^RoaringBitmap (.-nodes t))))

(defn record-mismatch
  "Where dense network `t` and a record store's handle sets disagree, or nil:
  `[:sentex h]` for a node `sentexes` lacks, `[:justification h]` for a justification
  `justifications` lacks, and `[:premise h]` for a node that is a premise in one of `t`
  and `premises` and not in the other.  Each set is a `java.util.Set` of Long handles, as
  `p/sentex-ids` answers.  One pass over `t`'s node, justification and premise bitmaps and
  over `premises`, under a read lock."
  [^DenseTms t ^java.util.Set sentexes ^java.util.Set justifications ^java.util.Set premises]
  (with-read (.-lock t)
    (let [^RoaringBitmap nodes (.-nodes t)
          ^RoaringBitmap prems (.-premises t)
          absent (fn [kind ^RoaringBitmap r ^java.util.Set s]
                   (let [it (.getIntIterator r)]
                     (loop []
                       (when (.hasNext it)
                         (let [h (long (.next it))]
                           (if (.contains s h) (recur) [kind h]))))))]
      (or (absent :sentex nodes sentexes)
          (absent :justification (.-jids t) justifications)
          (absent :premise prems premises)
          (some #(when (and (rb-has? nodes %) (not (rb-has? prems %))) [:premise (long %)])
                premises)))))

(defn unsupported-nodes
  "The nodes of dense network `t` that are no premise and that no justification
  concludes, ascending, as Longs: the premise bitmap subtracted from the node bitmap, then
  one supports probe per remaining node, under a read lock."
  [^DenseTms t]
  (with-read (.-lock t)
    (let [^TmsColumns cols (.-cols t)
          it (.getIntIterator (RoaringBitmap/andNot ^RoaringBitmap (.-nodes t)
                                                    ^RoaringBitmap (.-premises t)))]
      (loop [acc (transient [])]
        (if (.hasNext it)
          (let [d (.next it)]
            (recur (if (zero? (alength (.supportsOf cols d))) (conj! acc (long d)) acc)))
          (persistent! acc))))))

(defn- copy-structures!
  "Copy every structure of dense network `src` into `target`, whose write lock the caller
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
             [(.-j-inf-sym target) (.-j-inf-sym src)]
             [(.-j-subs target) (.-j-subs src)]]]
      (.putAll t s)))
  (reset! (.-superseded target) @(.-superseded src)))

(defn copy-into!
  "Copy every structure of dense network `src` into `target`, which must hold no node,
  under `target`'s write lock.  `read-image!` reads into a fresh network and this moves
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
  lock."
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
     :blocked    (rb-set ^RoaringBitmap (.-blocked this))
     :superseded @^clojure.lang.Atom (.-superseded this)
     :forced     {:mono (rb-set ^RoaringBitmap (.-f-mono this))
                  :out  (rb-set ^RoaringBitmap (.-f-out this))
                  :void (rb-set ^RoaringBitmap (.-f-void this))
                  :held (rb-set ^RoaringBitmap (.-f-held this))}
     :classes    (into {} (map (fn [d] [d :monotonic]))
                       (rb-longs ^RoaringBitmap (.-mono this)))
     :in         (rb-set ^RoaringBitmap (.-in this))
     :touched     (rb-set ^RoaringBitmap (.-touched this))
     :touched-in  (rb-set ^RoaringBitmap (.-touched-in this))
     :touched-new (rb-set ^RoaringBitmap (.-touched-new this))
     :touched-out (rb-set ^RoaringBitmap (.-touched-out this))}))

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
              (Int2ObjectOpenHashMap.)                         ; j-subs
              (rb)                                             ; j-mono
              (rb) (rb) (rb) (rb) (rb) (rb) (rb)               ; in blocked touched touched-in
                                                               ; touched-new touched-out mono
              (rb) (rb) (rb) (rb)                              ; f-mono f-out f-void f-held
              (atom {})
              (AtomicReference. nil)
              (AtomicReference. {:gen 0 :epochs []})))
