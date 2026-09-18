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
            [vaelii.impl.kv :as kv]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]))

;; ---- per-space registries --------------------------------------------------
;; defonce so the registry survives REPL reloads and is shared across a JVM's test
;; namespaces — one shared store per space number, for the life of the JVM.

(defonce ^:private record-spaces   (atom {}))
(defonce ^:private record-counters (atom {}))
(defonce ^:private index-spaces    (atom {}))

(defn- space-atom
  "The state atom for `space` in `registry`, created once on first use so two stores
  over the same space number share one atom — space sharing, in RAM."
  [registry space init]
  (or (@registry space)
      (-> (swap! registry (fn [m] (if (m space) m (assoc m space (atom init)))))
          (get space))))

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
  (swap! state assoc-in [kind id] rec)
  (when (> (long id) (long @counter)) (swap! counter max (long id)))
  id)

(defrecord MemoryRecordStore [state counter]
  p/RecordStore
  (next-id [_] (long (swap! counter inc)))
  (put-sentex [this sentex]
    (let [id (or (:id sentex) (p/next-id this))]
      (store-record state counter :sentexes id (assoc sentex :id id))))
  ;; Every fetch is tallied by kind (`vaelii.impl.profile`), which is the record-store
  ;; half of the read tally the index keeps — a deref and a `nil?` check when nobody is
  ;; asking.  It sits on the protocol method and not on the state read below it, so this
  ;; store and the durable one count the same events (`mark-premise` reaches into the
  ;; state map here and re-`fetch`es there, and a tally that counted both would be a
  ;; reading of which backend is running).
  (get-sentex [_ id] (prof/record-fetch :sentex) (get-in @state [:sentexes id]))
  (delete-sentex! [_ id]
    (swap! state (fn [st] (-> st
                              (update :sentexes dissoc id)
                              (update :premises disj id)
                              (update :provenance dissoc id))))
    nil)
  (put-justification [this justification]
    (let [id (or (:id justification) (p/next-id this))]
      (store-record state counter :justifications id (assoc justification :id id))))
  (get-justification [_ id] (prof/record-fetch :justification) (get-in @state [:justifications id]))
  (delete-justification! [_ id]
    (swap! state (fn [st] (-> st
                              (update :justifications dissoc id)
                              (update :provenance dissoc id))))
    nil)
  (put-provenance    [_ id prov] (swap! state assoc-in [:provenance id] prov) prov)
  (get-provenance    [_ id]      (prof/record-fetch :provenance) (get-in @state [:provenance id]))
  (delete-provenance! [_ id]     (swap! state update :provenance dissoc id) nil)
  (sentex-ids    [_] (set (keys (:sentexes @state))))
  (justification-ids [_] (set (keys (:justifications @state))))
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
  (premise-ids [_] (set (:premises @state)))
  (premise-strength [_ id] (or (:strength (get-in @state [:sentexes id])) :default))
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
  (a-premise-id        [_] (first (:premises @state))))

(defn memory-record-store
  "An in-memory `RecordStore`.  Only `:space` in `opts` matters: it selects the shared
  state atom **and** the shared handle counter, which have to be the same pair for two
  stores over one space or the second would re-issue handles the first had already
  written."
  [{:keys [space] :or {space 0}}]
  (->MemoryRecordStore (space-atom record-spaces space empty-record-state)
                       (space-atom record-counters space 0)))

;; ---- index KV backend ----------------------------------------------------
;; One map keyed by the structured key vectors, holding a Long at each counter key
;; and a set at each set key.  `KvIndexStore` (vaelii.impl.kv) supplies all the trie
;; and index logic; this only says how a scalar, a counter, and a set live in a map.

(def ^:dynamic *bulk-txn*
  "During a bulk load, `{:state <the loaded backend's state atom> :txn <a volatile!
  holding a transient of its map>}`.  While bound, **that** backend's *writes* land on
  the transient (`assoc!` — no per-op HAMT path copy) and the whole load is one
  `persistent!` at the end, instead of a `swap!` per fact.  nil (the default) leaves
  every op on the persistent atom, so nothing outside a bulk load pays for the binding's
  existence — and *reads* go to the backing atom in both modes, so the query hot path
  never branches on it.  The backing atom is therefore stale for the life of
  the load: correct only because the sole mid-load reader (`note-opposed`'s `[:false b]`
  probe) reads the always-empty negative side, and every real read happens after the
  closing `persistent!`.  Use `with-bulk-writes` for a positive/monotonic, distinct load;
  a corpus with `(not …)` facts must `rebuild-opposed!` after it (the atom the opposed
  set is derived from was stale during the load).

  The binding names the backend it is for, because a dynamic binding is per *thread*,
  not per backend: a write this thread makes to any other `MemoryKvBackend` while the
  load runs — a second KB's index, a chaining callback asserting elsewhere — lands on
  that backend's own atom (`txn-for`), never on the loaded one's transient.

  **The accumulator's life is the batch's, and no longer.**  `with-bulk-writes` clears
  the volatile as it installs, so the binding a body conveyed somewhere — a future, a
  lazy seq realized afterwards — finds nothing to write on and takes the atom, which is
  where a write outside the batch belongs.  A transient reached after its `persistent!`
  is not a slow write but a thrown one, and on a path nobody expected to be able to throw."
  nil)

(defn- txn-for
  "The bulk transient for the backend whose state atom is `state`, or nil — nil too
  when the bound load is over another backend, whose transient must not take this
  backend's writes, and nil once the batch has installed its accumulator (`*bulk-txn*`)."
  [state]
  (when-let [b *bulk-txn*]
    (when (identical? (:state b) state)
      (when (some? @(:txn b)) (:txn b)))))

;; ---- the argument-column trie --------------------------------------------
;; The predicate-scoped argument roots (`[:argument-root pred pos term]`) are the one
;; family this backend does NOT hold as flat key→set entries.  A four-element vector key
;; pays `APersistentVector.doEquiv` per probe and is consed at the call site; the family
;; is also hierarchical (`pos → term → pred → handles`) and the settle's reads want its
;; subtrees — a scoped leaf, a `(pos, term)` union, a node count.  So it lives under the
;; reserved key `::arg` in this backend's own state map, as a counted nested map:
;;
;;   {pos {term {:union #{handles}          ; the disjoint union across preds — the
;;               :preds {pred #{handles}}}}} ; agnostic members AND its count as a node read
;;
;; `:union` is a *disjoint* union: a handle is one sentex with one functor, so at a fixed
;; `(pos, term)` it sits under exactly one predicate.  That makes the union maintainable by
;; an unconditional `conj`/`disj` (no reference count) and makes its cardinality the
;; agnostic count with no sum over the roster.
;;
;; Living in the same state map keeps the whole family inside one atom, so the bulk
;; transient, `kv-entries`/`kv-load`, `kv-clear!` and the snapshot's fallback blob all
;; carry it with no extra field.  Every generic op that can name an argument-root key
;; routes here; `kv-entries` re-emits the flat `[:argument-root pred pos term]` shape so a
;; dump and the columnar fallback blob are byte-identical to the flat layout's.

(def ^:private arg-state-key ::arg)

(defn- arg-root-key?
  "Is `k` an argument-root key `[:argument-root pred pos term]`?  The one family this
  backend routes to the counted trie rather than the flat map."
  [k]
  (and (vector? k) (= 4 (count k)) (= :argument-root (nth k 0))))

(defn- arg-scoped
  "The handle set stored for one scoped leaf `(pos, term, pred)`, or `#{}` — by reference,
  nil-safe at every level so an absent branch reads empty."
  [tree pos term pred]
  (or (-> tree (get pos) (get term) (get :preds) (get pred)) #{}))

(defn- arg-union
  "The disjoint union of handles at a `(pos, term)` node across every predicate, or `#{}`
  — the predicate-agnostic members, by reference."
  [tree pos term]
  (or (-> tree (get pos) (get term) (get :union)) #{}))

(defn- arg-tree-add [tree pred pos term h]
  (let [node  (or (get-in tree [pos term]) {:union #{} :preds {}})
        node' (-> node
                  (update :union conj h)
                  (update-in [:preds pred] (fnil conj #{}) h))]
    (assoc-in tree [pos term] node')))

(defn- arg-tree-remove
  "Drop handle `h` from the `(pos, term, pred)` leaf, pruning empties so an emptied leaf,
  node, or position vanishes — matching the flat map's disj-drops-the-key semantics, so a
  read of an emptied key answers `#{}` / 0 and `kv-entries` emits no dangling posting."
  [tree pred pos term h]
  (if-let [node (get-in tree [pos term])]
    (let [union' (disj (:union node) h)]
      (if (empty? union')
        (let [terms' (dissoc (get tree pos) term)]
          (if (empty? terms') (dissoc tree pos) (assoc tree pos terms')))
        (let [preds  (:preds node)
              pset'  (disj (get preds pred) h)
              preds' (if (empty? pset') (dissoc preds pred) (assoc preds pred pset'))]
          (assoc-in tree [pos term] {:union union' :preds preds'}))))
    tree))

(defn- arg-tree-put
  "Set the `(pos, term, pred)` leaf to exactly `hset`, recomputing the node union — the
  whole-set install `kv-put` performs (the columnar fallback's `kv-load` puts a posting at
  once rather than a handle at a time).  A disjoint union, so the old leaf's handles leave
  it and the new set's enter."
  [tree pred pos term hset]
  (let [node   (or (get-in tree [pos term]) {:union #{} :preds {}})
        old    (get (:preds node) pred #{})
        union' (into (reduce disj (:union node) old) hset)
        preds' (if (empty? hset) (dissoc (:preds node) pred) (assoc (:preds node) pred (set hset)))]
    (if (empty? union')
      (let [terms' (dissoc (get tree pos) term)]
        (if (empty? terms') (dissoc tree pos) (assoc tree pos terms')))
      (assoc-in tree [pos term] {:union union' :preds preds'}))))

(defn- arg-tree-delete
  "Drop the whole `(pos, term, pred)` leaf (every handle under it), pruning empties — the
  `kv-delete` twin of `arg-tree-put`."
  [tree pred pos term]
  (if-let [node (get-in tree [pos term])]
    (let [union' (reduce disj (:union node) (get (:preds node) pred #{}))
          preds' (dissoc (:preds node) pred)]
      (if (empty? union')
        (let [terms' (dissoc (get tree pos) term)]
          (if (empty? terms') (dissoc tree pos) (assoc tree pos terms')))
        (assoc-in tree [pos term] {:union union' :preds preds'})))
    tree))

(defn- arg-op
  "Fold one argument-root write op into the trie `tree`.

  All four set-shaped ops, because a batch and the protocol method may not disagree about
  what one op means: `kv-put` and `kv-delete` route an argument-root key to the trie, so
  `[:put …]` and `[:delete …]` inside a `kv-batch` have to reach the same two folds.  A
  flat-map backend answers both of them for this family with no arm of its own, so leaving
  them out here is one adapter refusing a batch the others apply."
  [tree [op k a]]
  (let [pred (nth k 1) pos (nth k 2) term (nth k 3)]
    (case op
      :add-to-set      (arg-tree-add    tree pred pos term a)
      :remove-from-set (arg-tree-remove tree pred pos term a)
      :put             (arg-tree-put    tree pred pos term a)
      :delete          (arg-tree-delete tree pred pos term)
      (p/unknown-op! op))))

(defn- arg-entries
  "The trie re-projected into the flat `[:argument-root pred pos term] → handle-set`
  entries the family is dumped and loaded as — one per scoped leaf, so the portable shape
  is byte-identical to the flat layout's."
  [tree]
  (for [[pos terms] tree
        [term node] terms
        [pred pset] (:preds node)]
    [[:argument-root pred pos term] pset]))

(defn- mem-op!
  "The transient twin of `kv/apply-op`: apply one write op to transient map `t`, returning
  the new transient (a transient op's return must be captured).  No reply is computed —
  the only bulk caller (`index-sentex`) ignores them.  The set *values* stay persistent;
  it is the millions-of-keys map that is transient.

  That trade is right for the trie's child and leaf sets, which are small.  It is not
  free for the secondary roots the same op writes: `[:context-root …]`,
  `[:functor-root …]` and the term index grow to the size of the KB, so each `conj` here
  is a path copy in a HAMT of that size, per fact loaded.  Making those transient too
  would mean a second representation for reads to know about, which is the cost this
  declines rather than one it avoids.

  An argument-root op folds into the `::arg` trie held at one transient slot instead of a
  flat key — the trie value stays persistent, so only that one slot is re-`assoc!`ed."
  [t [op k a :as op-vec]]
  (if (arg-root-key? k)
    (assoc! t arg-state-key (arg-op (get t arg-state-key) op-vec))
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
      (p/unknown-op! op))))

(defn- mem-apply-op
  "The persistent twin: apply one write op to map `m`, returning `[m' reply]`.  An
  argument-root op folds into the `::arg` trie (reply nil); everything else defers to
  `kv/apply-op`, which owns the shared op semantics."
  [m [_ k :as op-vec]]
  (if (arg-root-key? k)
    [(update m arg-state-key arg-op op-vec) nil]
    (kv/apply-op m op-vec)))

;; Writes consult `*bulk-txn*`: bound (a bulk load), they land on the transient; nil
;; (everything else), the persistent atom, byte-for-byte the unbatched path.  Reads are
;; NOT bulk-aware — they read the atom in both modes, so the query hot path is untouched;
;; the atom is stale only for the life of a bulk load, and `with-bulk-writes` documents
;; why that is sound (positive load; every real read is post-load).
(defrecord MemoryKvBackend [state]
  p/KvBackend
  ;; an argument-root key reads out of the `::arg` trie for every generic op too, so a
  ;; caller that still names the four-part vector — a direct test, the columnar fallback's
  ;; `kv-load` (which puts a whole posting), a snapshot round-trip — sees the same set the
  ;; flat layout held.  `kv-get` returns the scoped set (or nil when absent), which is
  ;; what a flat key→set map answers for a set key.
  (kv-get  [_ k]
    (if (arg-root-key? k)
      (let [s (arg-scoped (arg-state-key @state) (nth k 2) (nth k 3) (nth k 1))]
        (when (seq s) s))
      (get @state k)))
  (kv-put  [_ k v]
    (if (arg-root-key? k)
      (let [pred (nth k 1) pos (nth k 2) term (nth k 3)]
        (if-let [tv (txn-for state)]
          (vswap! tv assoc! arg-state-key (arg-tree-put (get @tv arg-state-key) pred pos term v))
          (swap! state update arg-state-key arg-tree-put pred pos term v)))
      (if-let [tv (txn-for state)] (vswap! tv assoc! k v) (swap! state assoc k v)))
    nil)
  (kv-delete  [_ k]
    (if (arg-root-key? k)
      (let [pred (nth k 1) pos (nth k 2) term (nth k 3)]
        (if-let [tv (txn-for state)]
          (vswap! tv assoc! arg-state-key (arg-tree-delete (get @tv arg-state-key) pred pos term))
          (swap! state update arg-state-key arg-tree-delete pred pos term)))
      (if-let [tv (txn-for state)] (vswap! tv dissoc! k) (swap! state dissoc k)))
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
  ;; an argument-root write folds into the `::arg` trie; everything else lands at its flat
  ;; key.  Both modes route, so the trie stays consistent whether a fact arrives through
  ;; the bulk transient or the ordinary swap.
  (kv-add-to-set [_ k m]
    (if (arg-root-key? k)
      (let [op [:add-to-set k m]]
        (if-let [tv (txn-for state)]
          (vswap! tv assoc! arg-state-key (arg-op (get @tv arg-state-key) op))
          (swap! state update arg-state-key arg-op op)))
      (if-let [tv (txn-for state)]
        (vswap! tv assoc! k (conj (get @tv k #{}) m))
        (swap! state update k (fnil conj #{}) m)))
    nil)
  (kv-remove-from-set [_ k m]
    (if (arg-root-key? k)
      (let [op [:remove-from-set k m]]
        (if-let [tv (txn-for state)]
          (vswap! tv assoc! arg-state-key (arg-op (get @tv arg-state-key) op))
          (swap! state update arg-state-key arg-op op)))
      (if-let [tv (txn-for state)]
        (vswap! tv (fn [t] (let [s (disj (get t k #{}) m)]
                             (if (empty? s) (dissoc! t k) (assoc! t k s)))))
        (swap! state (fn [st]
                       (let [s (disj (get st k) m)]
                         (if (empty? s) (dissoc st k) (assoc st k s)))))))
    nil)
  ;; the stored set by reference — the O(1) return the in-memory backend is for.  An
  ;; argument-root key descends the trie to its scoped leaf, still by reference.
  (kv-members [_ k]
    (if (arg-root-key? k)
      (arg-scoped (arg-state-key @state) (nth k 2) (nth k 3) (nth k 1))
      (get @state k #{})))
  ;; a hash lookup into the stored set, the same read `kv-members` hands back — bulk-blind
  ;; like every other read here, so it agrees with `kv-members` in both modes
  (kv-member? [_ k m]
    (if (arg-root-key? k)
      (contains? (arg-scoped (arg-state-key @state) (nth k 2) (nth k 3) (nth k 1)) m)
      (contains? (get @state k) m)))
  (kv-count    [_ k]
    (if (arg-root-key? k)
      (count (arg-scoped (arg-state-key @state) (nth k 2) (nth k 3) (nth k 1)))
      (count (get @state k))))
  (kv-intersect [_ ks]
    (if (empty? ks)
      #{}
      (let [st @state
            arg (arg-state-key st)]
        (apply set/intersection
               (map (fn [k]
                      (if (arg-root-key? k)
                        (arg-scoped arg (nth k 2) (nth k 3) (nth k 1))
                        (get st k #{})))
                    ks)))))
  (kv-batch [_ ops]
    (if-let [tv (txn-for state)]
      ;; bulk load: fold every op into the transient (no per-op path copy, no swap!);
      ;; index-sentex ignores the replies, so return the aligned nil placeholders.
      (do (vswap! tv (fn [t] (reduce mem-op! t ops))) (mapv (fn [_#] nil) ops))
      ;; apply every op in one swap!, capturing the per-op replies; the capture is
      ;; recomputed each swap attempt, so a retry (never, under single-writer) cannot
      ;; double-count.  `mem-apply-op` routes an argument-root op into the `::arg` trie.
      (let [replies (atom nil)]
        (swap! state
               (fn [m]
                 (let [[m' rs] (reduce (fn [[m rs] op]
                                         (let [[m2 r] (mem-apply-op m op)]
                                           [m2 (conj rs r)]))
                                       [m []] ops)]
                   (reset! replies rs)
                   m')))
        @replies)))
  ;; this backend's resident shape already *is* the portable one — structured vector
  ;; keys, Clojure sets and Longs — so both directions are the map itself, save the
  ;; argument roots: those live in the `::arg` trie and are re-projected to their flat
  ;; `[:argument-root pred pos term]` entries here (and routed back on load), so a dump
  ;; and the columnar fallback blob stay byte-identical to the flat layout's.
  (kv-entries [_]
    (let [st @state]
      (concat (arg-entries (arg-state-key st)) (seq (dissoc st arg-state-key)))))
  (kv-load [_ entries]
    (swap! state
           (fn [m]
             (reduce (fn [m [k v]]
                       (if (arg-root-key? k)
                         (update m arg-state-key
                                 (fn [tree] (reduce #(arg-tree-add %1 (nth k 1) (nth k 2) (nth k 3) %2)
                                                    tree v)))
                         (assoc m k v)))
                     m entries)))
    nil)

  (kv-clear! [_] (reset! state {}) nil)

  ;; The argument columns read straight off the `::arg` trie: a scoped leaf and the
  ;; agnostic union by reference, the agnostic count as a node read (`count` of the
  ;; maintained union), and a multi-column probe as an intersection of scoped leaves —
  ;; none consing an `[:argument-root …]` vector or touching the slot roster.
  p/ArgColumns
  (arg-scoped-members [_ pred pos term] (arg-scoped (arg-state-key @state) pos term pred))
  (arg-scoped-intersect [_ pred pos-terms]
    (let [tree (arg-state-key @state)
          sets (map (fn [[pos term]] (arg-scoped tree pos term pred)) pos-terms)]
      (if (nil? (next sets)) (first sets) (apply set/intersection sets))))
  (arg-agnostic-members [_ pos term] (arg-union (arg-state-key @state) pos term))
  (arg-agnostic-count   [_ pos term] (count (arg-union (arg-state-key @state) pos term))))

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
  so a non-memory store (disk) just runs `body` on its own batched path.  See `*bulk-txn*`
  for the read-staleness contract: a positive/monotonic, distinct load only; a corpus
  with `(not …)` facts must `rebuild-opposed!` after; and `bulk-writes*`, which this
  delegates to, for what keeps the accumulator the batch's own."
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
