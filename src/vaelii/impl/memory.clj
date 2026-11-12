;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.memory
  "The default in-memory backends for the two storage protocols, selected at KB
  construction.  The engine above the protocols never touches a concrete store, so a
  KB built on these runs the whole engine with no external dependency; the on-disk
  backend (`vaelii.impl.disk`) is the durable alternative.

  The record store implements `RecordStore` directly over maps.  The index reuses
  `vaelii.impl.kv/KvIndexStore` — the one trie/roots/index implementation — over a
  `MemoryKvBackend`: one map keyed by the structured key vectors (equal vectors are
  equal keys), holding a `Long` at each counter key and a set at each set key.
  `kv-intersect` is a `clojure.set/intersection`; `kv-members` returns the stored set
  by reference (no serialization, no copy).

  **Durable-within-the-JVM semantics by space number.**  Two KBs constructed over the
  same `:space` number must share state, or the persistence/recovery tests (a second KB
  restarted over the same databases) would find an empty store.  A process-global
  registry keyed by space number provides that: `(memory-record-store {:space 15})` twice
  returns records backed by *one* state atom, and by one handle counter beside it.
  `clear-records!` / `clear-index!` empty a space.  (State lives only for the life of
  the JVM; the on-disk backend is what survives a process restart.)

  **Single-writer.**  Pure runs one writer (docs/storage.md, \"The single-writer
  contract\"), so a store's state is one atom mutated by `swap!`; reads deref a snapshot
  and are lock-free.  Interleaved *writers* would not be serializable."
  (:require [clojure.set :as set]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]))

;; ---- per-space registries --------------------------------------------------
;; defonce so the registry survives REPL reloads and is shared across a JVM's test
;; namespaces — one shared store per space number, for the life of the JVM.

(defonce ^:private record-spaces   (atom {}))
(defonce ^:private record-counters (atom {}))
(defonce ^:private record-reserved (atom {}))
(defonce ^:private index-spaces    (atom {}))
(defonce ^:private space-reasoners (atom {}))

(defn- space-atom
  "The state atom for `space` in `registry`, created once on first use so two stores
  over the same space number share one atom — space sharing, in RAM."
  [registry space init]
  (or (@registry space)
      (-> (swap! registry (fn [m] (if (m space) m (assoc m space (atom init)))))
          (get space))))

(defonce ^:private engine-space-seq (atom 0))

(defn engine-space
  "A fresh private space for an in-RAM KB the engine opens for itself: an ephemeral
  `fork`, or a `kb-diff` side read from a path.  No entry point hands the value to a
  caller, so `core/close!` of the KB opened over it drops the space from every registry
  (`kb/release-engine-space!`).  `kind` labels the space for a reader of the registry."
  [kind]
  [::engine kind (swap! engine-space-seq inc)])

(defn engine-space?
  "Is `space` one `engine-space` allocated?"
  [space]
  (and (vector? space) (= ::engine (first space))))

;; ---- record store --------------------------------------------------------

(def ^:private empty-record-state
  {:sentexes {} :justifications {} :provenance {} :premises #{}})

(defn- store-record
  "Write `rec` at handle `id` under `kind`, keeping `counter` — the highest handle
  issued — at or above it.  That second half is what makes the handle an identity:
  `put-sentex` and `put-justification` both honour an explicit `:id` (an import lands
  records at the handles its dump gave them), and a counter left behind one would hand
  the same number out again on the very next write, overwriting a record with no error
  and no warning.  O(1), and a no-op when the id came from `next-id`, which is already
  ahead of it.

  The counter is its **own** atom rather than a key in the state map, so allocating a
  handle is a compare-and-set on a `Long` and not on the whole store — one is minted per
  stored sentex and per justification, and forward chaining takes one per firing
  (docs/inference.md).  The disk store holds its counter the same way, so both backends
  allocate alike."
  [state counter kind id rec]
  (swap! state (fn [m] (assoc m kind (assoc (get m kind) id rec))))
  (when (> (long id) (long @counter)) (swap! counter max (long id)))
  id)

(defrecord MemoryRecordStore [state counter reserved]
  p/RecordStore
  (next-id [_]
    (if-let [r @reserved]
      (long (swap! counter #(cap/skip-reserved r (inc (long %)))))
      (long (swap! counter inc))))
  (put-sentex [this sentex]
    (let [id (or (:id sentex) (p/next-id this))]
      (observe/keep-before! this [:sentex id] #(get (:sentexes @state) id))
      (store-record state counter :sentexes id (assoc sentex :id id))))
  ;; Every fetch is tallied by kind (`vaelii.impl.profile`), which is the record-store
  ;; half of the read tally the index keeps — a deref and a `nil?` check when nobody is
  ;; asking.  It sits on the protocol method and not on the state read below it, so this
  ;; store and the durable one count the same events (`mark-premise` reaches into the
  ;; state map here and re-`fetch`es there, and a tally that counted both would be a
  ;; reading of which backend is running).
  (get-sentex [_ id] (prof/record-fetch :sentex id) (get (:sentexes @state) id))
  (delete-sentex! [this id]
    (observe/keep-before! this [:sentex id] #(get (:sentexes @state) id))
    (swap! state (fn [st] (-> st
                              (update :sentexes dissoc id)
                              (update :premises disj id)
                              (update :provenance dissoc id))))
    nil)
  (put-justification [this justification]
    (let [id (or (:id justification) (p/next-id this))]
      (observe/keep-before! this [:justification id] #(get (:justifications @state) id))
      (store-record state counter :justifications id (assoc justification :id id))))
  (get-justification [_ id] (prof/record-fetch :justification) (get (:justifications @state) id))
  (delete-justification! [this id]
    (observe/keep-before! this [:justification id] #(get (:justifications @state) id))
    (swap! state (fn [st] (-> st
                              (update :justifications dissoc id)
                              (update :provenance dissoc id))))
    nil)
  (put-provenance    [_ id prov] (swap! state assoc-in [:provenance id] prov) prov)
  (get-provenance    [_ id]      (prof/record-fetch :provenance) (get (:provenance @state) id))
  (delete-provenance! [_ id]     (swap! state update :provenance dissoc id) nil)
  (sentex-ids    [_] (prof/record-fetch :sentex-ids) (set (keys (:sentexes @state))))
  (justification-ids [_] (prof/record-fetch :justification-ids) (set (keys (:justifications @state))))
  (mark-premise [_ id strength]
    ;; the assumption strength lives on the sentex record itself; premises are also
    ;; tracked in a set.  Guard both on the record existing — a handle with no sentex
    ;; must not conjure a phantom map entry, nor a phantom premise (the durable store
    ;; guards the same way, and `premise-ids` must agree across the two).
    ;;
    ;; A record already carrying this strength is left alone, which is the ordinary
    ;; assert: `kb/create-sentex` writes the strength into the record it stores, so the
    ;; mark that follows asks for the strength it already has.  Re-`assoc`ing it copies
    ;; a path through a map holding every sentex in the KB, once per fact of a bulk
    ;; load, to arrive at the value already there.  The durable store pays more for the
    ;; same guard (`vaelii.impl.disk.record-store`: a second whole frame).
    (swap! state (fn [st]
                   (let [want (or strength :default)
                         sx   (get-in st [:sentexes id])]
                     (if-not sx
                       st
                       (cond-> (update st :premises (fnil conj #{}) id)
                         (not= want (:strength sx))
                         (assoc-in [:sentexes id :strength] want))))))
    nil)
  (unmark-premise! [_ id]
    (swap! state (fn [st]
                   (cond-> st
                     (get-in st [:sentexes id]) (assoc-in [:sentexes id :strength] nil)
                     :always                    (update :premises disj id))))
    nil)
  (premise-ids [_] (prof/record-fetch :premise-ids) (set (:premises @state)))
  (premise-strength [_ id]
    (prof/record-fetch :premise-strength)
    (or (:strength (get (:sentexes @state) id)) :default))
  (clear-records! [_] (reset! state empty-record-state) (reset! counter 0) nil)

  ;; The tallies read the maps this store already holds, so implementing them buys
  ;; nothing here — except that a caller then reads one number instead of copying the key
  ;; set to count it, and that a store answering the capability is what keeps the helpers
  ;; off the fallback on the reference backend the others are compared against.
  p/Tallying
  (sentex-tally        [_] (count (:sentexes @state)))
  (justification-tally [_] (count (:justifications @state)))
  (a-sentex-id         [_] (first (keys (:sentexes @state))))
  (a-justification-id  [_] (first (keys (:justifications @state))))
  (a-premise-id        [_] (first (:premises @state)))

  p/HandleReserving
  (reserve-handles! [_ ranges] (swap! reserved cap/reserve-ranges ranges) nil))

(defn memory-record-store
  "An in-memory `RecordStore`.  Only `:space` in `opts` matters: it selects the shared
  state atom **and** the shared handle counter, which have to be the same pair for two
  stores over one space or the second would re-issue handles the first had already
  written."
  [{:keys [space] :or {space 0}}]
  (->MemoryRecordStore (space-atom record-spaces space empty-record-state)
                       (space-atom record-counters space 0)
                       (space-atom record-reserved space nil)))

(defn drop-record-space!
  "Forget the records and the handle counter held under `space`, so a process that opens
  a KB per private space does not keep every space it has finished with.  A store already
  holding the space keeps its atoms; a store opened on `space` afterwards starts empty.
  Returns true when an entry was dropped."
  [space]
  (let [had? (contains? @record-spaces space)]
    (swap! record-spaces dissoc space)
    (swap! record-counters dissoc space)
    (swap! record-reserved dissoc space)
    (swap! space-reasoners dissoc space)
    had?))

(defn recorded-reasoners
  "The reasoner names recorded for the records in `space`, as a set, or nil when none
  were recorded (`vaelii.impl.kb/add-reasoners!`).  `drop-record-space!` forgets them;
  `clear-records!` keeps them, as a disk store's `reasoners.edn` outlives a wipe."
  [space]
  (get @space-reasoners space))

(defn record-reasoners!
  "Record `names` as the reasoner set of the records in `space`."
  [space names]
  (swap! space-reasoners assoc space (set names))
  nil)

;; ---- index KV backend ----------------------------------------------------
;; One map keyed by the structured key vectors, holding a Long at each counter key
;; and a set at each set key.  `KvIndexStore` (vaelii.impl.kv) supplies all the trie
;; and index logic; this only says how a scalar, a counter, and a set live in a map.

(def ^:dynamic *bulk-txn*
  "During a bulk load, `{:state <the loaded backend's state atom> :txn <a volatile!
  holding a transient of its map>}`.  While bound, **that** backend's writes land on the
  transient (`assoc!` — no per-op HAMT path copy) and its reads answer from the same
  transient, so a read inside the load sees every write the load made.  The whole load is
  one `persistent!` at the end instead of a `swap!` per fact.  nil (the default) leaves
  every op on the persistent atom; a read outside a load pays one read of this var and,
  inside one, an `identical?` check.  Use `with-bulk-writes` for a distinct load.

  The binding names the backend it is for, because a dynamic binding is per *thread*,
  not per backend: a write this thread makes to any other `MemoryKvBackend` while the
  load runs — a second KB's index, a chaining callback asserting elsewhere — lands on
  that backend's own atom (`txn-for`), never on the loaded one's transient.  A reader on
  another thread reads the atom, which holds the state before the load.

  **The accumulator's life is the batch's, and no longer.**  `with-bulk-writes` clears
  the volatile as it installs, so the binding a body conveyed somewhere — a future, a
  lazy seq realized afterwards — finds nothing to write on and takes the atom, which is
  where a write outside the batch belongs.  A transient reached after its `persistent!`
  throws."
  nil)

(defn- txn-for
  "The bulk transient for the backend whose state atom is `state`, or nil — nil too
  when the bound load is over another backend, whose transient must not take this
  backend's writes, and nil once the batch has installed its accumulator (`*bulk-txn*`)."
  [state]
  (when-let [b *bulk-txn*]
    (when (identical? (:state b) state)
      (when (some? @(:txn b)) (:txn b)))))

(defn- current
  "The map a read of the backend over `state` answers from: the open bulk transient when
  this thread is loading into that backend (`txn-for`), else the atom's value.  A
  transient answers `get`, `contains?` and `count`, the three lookups the reads make."
  [state]
  (if-let [tv (txn-for state)] @tv @state))

(defn- mem-op!
  "The transient twin of `kv/apply-op`: apply one write op to transient map `t`, returning
  the new transient (a transient op's return must be captured).  No reply is computed;
  `fold-ops` reads a counter's value back off the transient.  The set *values* stay
  persistent; it is the millions-of-keys map that is transient.

  That trade is right for the trie's child and leaf sets, which are small.  It is not
  free for the secondary roots the same op writes: `[:context-root …]`,
  `[:predicate-extent …]` and the term index grow to the size of the KB, so each `conj` here
  is a path copy in a HAMT of that size, per fact loaded.  Making those transient too
  would mean a second representation for reads to know about, which is the cost this
  declines rather than one it avoids."
  [t [op k a]]
  (case op
    :put  (assoc! t k a)
    :delete  (dissoc! t k)
    :increment (assoc! t k (inc (long (get t k 0))))
    ;; floored at 0, like `kv/apply-op`'s arm — the two folds may not disagree about
    ;; what one op means, and a counter here is a cardinality (`p/KvBackend`)
    :decrement (assoc! t k (max 0 (dec (long (get t k 0)))))
    :add-to-set (assoc! t k (conj (get t k #{}) a))
    :remove-from-set (let [s (disj (get t k #{}) a)]
                       (if (empty? s) (dissoc! t k) (assoc! t k s)))
    (p/unknown-op! op)))

(defn- fold-ops
  "Fold `ops` into transient `t` (`mem-op!`), returning `[t' replies]`: a counter op's
  reply is its value after the op, read back off the transient, and every other op's is
  nil."
  [t ops]
  (let [rs (java.util.ArrayList.)
        t  (reduce (fn [t [op k :as o]]
                     (let [t' (mem-op! t o)]
                       (.add rs (when (or (identical? op :increment) (identical? op :decrement))
                                  (get t' k)))
                       t'))
                   t ops)]
    [t (vec rs)]))

;; Every op consults `*bulk-txn*`: bound (a bulk load over this backend), a write lands on
;; the transient and a read answers from it (`current`); nil (everything else), both use
;; the persistent atom, byte-for-byte the unbatched path.
(defrecord MemoryKvBackend [state]
  p/KvBackend
  (kv-get  [_ k] (get (current state) k))
  (kv-put  [_ k v]
    (if-let [tv (txn-for state)] (vswap! tv assoc! k v) (swap! state assoc k v))
    nil)
  (kv-delete  [_ k]
    (if-let [tv (txn-for state)] (vswap! tv dissoc! k) (swap! state dissoc k))
    nil)
  (kv-increment [_ k]   (if-let [tv (txn-for state)]
                          (let [v (inc (long (get @tv k 0)))] (vswap! tv assoc! k v) v)
                          (long (get (swap! state update k (fnil inc 0)) k))))
  ;; floored at 0 on both arms: a counter is a cardinality (`p/KvBackend`), and the
  ;; transient a bulk load writes through has to answer as the persistent one does
  (kv-decrement [_ k]   (if-let [tv (txn-for state)]
                          (let [v (max 0 (dec (long (get @tv k 0))))] (vswap! tv assoc! k v) v)
                          (long (get (swap! state update k
                                            (fn [v] (max 0 (dec (long (or v 0))))))
                                     k))))
  (kv-add-to-set [_ k m]
    (if-let [tv (txn-for state)]
      (vswap! tv assoc! k (conj (get @tv k #{}) m))
      (swap! state update k (fnil conj #{}) m))
    nil)
  (kv-remove-from-set [_ k m]
    (if-let [tv (txn-for state)]
      (vswap! tv (fn [t] (let [s (disj (get t k #{}) m)]
                           (if (empty? s) (dissoc! t k) (assoc! t k s)))))
      (swap! state (fn [st]
                     (let [s (disj (get st k) m)]
                       (if (empty? s) (dissoc st k) (assoc st k s))))))
    nil)
  ;; the stored set by reference — the O(1) return the in-memory backend is for
  (kv-members [_ k] (get (current state) k #{}))
  ;; a hash lookup into the stored set, the same read `kv-members` hands back
  (kv-member? [_ k m] (contains? (get (current state) k) m))
  (kv-count    [_ k]  (count (get (current state) k)))
  (kv-intersect [_ ks]
    (if (empty? ks)
      #{}
      (let [st (current state)]
        (apply set/intersection (map (fn [k] (get st k #{})) ks)))))
  ;; Every op of a batch folds through one transient (`fold-ops`): the bulk load's own,
  ;; or else one taken off the state map inside one swap!.  One assert's index write is
  ;; some twenty ops into one map, and folded persistently each op copies the path from
  ;; the root down; folded through a transient a node is copied once per batch.  The
  ;; replies are captured again on each swap attempt, so a retry (never, under
  ;; single-writer) cannot double-count.
  (kv-batch [_ ops]
    (if-let [tv (txn-for state)]
      (let [[t rs] (fold-ops @tv ops)] (vreset! tv t) rs)
      (let [replies (volatile! nil)]
        (swap! state (fn [m] (let [[t rs] (fold-ops (transient m) ops)]
                               (vreset! replies rs)
                               (persistent! t))))
        @replies)))
  ;; this backend's resident shape *is* the portable one — structured vector keys,
  ;; Clojure sets and Longs — so both directions are the map itself, with no key
  ;; reshaped on the way through.  A transient does not enumerate, so inside a load this
  ;; persists the accumulator and opens a new transient over the result, both O(1); the
  ;; load's next write to each path copies that path once more.
  (kv-entries [_]
    (if-let [tv (txn-for state)]
      (let [m (persistent! @tv)] (vreset! tv (transient m)) (seq m))
      (seq @state)))
  (kv-load [_ entries] (swap! state into entries) nil)

  (kv-clear! [_] (reset! state {}) nil))

(defn bulk-writes*
  "`with-bulk-writes`' body as a thunk — the macro is a wrapper over this, so the
  accumulator's whole life is one function's local and nothing about it is spliced into
  a caller's code.

  Three steps, in this order, and each is what makes the batch's accumulator **private**
  to the batch:

  - the state map is read **once**, into `base`, and the transient is built off that
    value.  `base` is what the install is checked against, so the batch knows what it
    was accumulating over rather than assuming;
  - the volatile is cleared before the install, so the binding a body conveyed
    elsewhere (a future, a lazy seq realized later) finds no accumulator and takes the
    atom — the correct home for a write outside the batch, and not a `persistent!`-ed
    transient that would throw;
  - the install is a **compare-and-set** against `base`, not a `reset!`.  The atom is
    per *space* and shared by every index store over that space, so a `reset!` would
    silently discard anything that reached it while the batch ran — a second bulk load
    stacked over this one being the way to get there without two threads.  Under the
    single-writer contract nothing does, which is exactly why the check is affordable:
    it is one CAS per batch, and it fires only where an overwrite would lose data.

  A failed install is `:stacked-batch`.  It is raised only when the body itself
  returned — a body that threw has a failure of its own to report, and replacing it with
  this one would hide it."
  [bk f]
  (let [state (:state bk)
        base  @state
        txn   (volatile! (transient base))
        done  (volatile! false)]
    (binding [*bulk-txn* {:state state :txn txn}]
      (try
        (let [r (f)] (vreset! done true) r)
        (finally
          (let [m (persistent! @txn)]
            (vreset! txn nil)
            (when (and (not (compare-and-set! state base m)) @done)
              (throw (ex-info (str "a bulk load's index state moved while the batch was"
                                   " accumulating, so installing the batch would discard"
                                   " whatever moved it — one bulk load at a time over a"
                                   " space, on the one writing thread")
                              {:type :stacked-batch})))))))))

(defmacro with-bulk-writes
  "Run `body` with `backend`'s index writes accumulated on one TRANSIENT of its state
  map, persisted back in a single step at the end — the write-side fast path for a bulk
  load (millions of trie `assoc!`s with no per-op HAMT path copy, one `persistent!`
  instead of a `swap!` per fact).  A no-op wrapper unless `backend` is a MemoryKvBackend,
  so a non-memory store (disk) just runs `body` on its own batched path.  A read of
  `backend` inside `body` sees the writes `body` made (`*bulk-txn*`); `bulk-writes*`,
  which this delegates to, keeps the accumulator the batch's own."
  [backend & body]
  `(let [bk# ~backend]
     (if (instance? vaelii.impl.memory.MemoryKvBackend bk#)
       (bulk-writes* bk# (fn [] ~@body))
       (do ~@body))))

(defn memory-kv-backend
  "An in-memory `KvBackend`.  Only `:space` in `opts` matters (it selects the shared
  state atom, so two index stores over the same space number share one map)."
  [{:keys [space] :or {space 0}}]
  (->MemoryKvBackend (space-atom index-spaces space {})))

(defn memory-index-store
  "An in-memory `IndexStore` — `KvIndexStore` over a `MemoryKvBackend`."
  [opts]
  (kv/->KvIndexStore (memory-kv-backend opts)))

(defn drop-index-space!
  "Forget the derived index state held under `space` — `core/close!`'s release of the RAM
  index a disk-backed KB derived, keyed by its directory
  (`vaelii.impl.kb/derived-index-space`), so a process opening durable KBs in a loop does
  not keep one derived index per directory it has finished with.  A no-op for a `space`
  nothing holds — every pure in-RAM KB keeps its space, which is its store rather than a
  derived cache.  Returns true when an entry was dropped."
  [space]
  (let [had? (contains? @index-spaces space)]
    (swap! index-spaces dissoc space)
    had?))
