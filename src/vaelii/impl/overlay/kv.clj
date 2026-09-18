;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.kv
  "`OverlayKv` — a composite `KvBackend` layering a private **writable** overlay over a
  shared **read-only** base.  Reads resolve overlay-first and fall through to the base;
  writes land only in the overlay; the base is never mutated, so several forks share one
  frozen base index while each keeps its own.  Within one JVM — a durable base's
  directory holds the exclusive single-writer lock, see `vaelii.impl.overlay.mount`.

  This is the index half of the `:overlay` backend (the record half is
  `vaelii.impl.overlay.store`), and it is the whole of it.  `KvIndexStore`
  (`vaelii.impl.kv`) writes *every* index family — the count-aware trie, the context /
  functor / argument roots, the rule index, the exception re-check index, the inverted
  term index and the term roster — in terms of this protocol and holds no state of its
  own, so one decorator here forks the entire index and the trie walker, the matcher, the
  planner and the query layers above it are unchanged.  That is what the `KvBackend` protocol
  was extracted for.

  ## The merge model, per key

  * **Sets.**  `members(K) = (base(K) ∪ overlay(K)) − removed(K)`, where `base(K)` is
    empty if `K` carries a tombstone, and `removed(K)` records the base members this
    overlay removed (a base set cannot be edited, so a removal is recorded rather than
    applied).
  * **Scalars and counters.**  An overlay value shadows the base's.  A counter is
    **copy-on-write**: the first `kv-increment` / `kv-decrement` seeds the overlay from
    the base value, so afterwards the overlay holds base+net and reads are exact.  An
    untouched counter reads straight through.
  * **Whole-key delete.**  A sticky tombstone in `::deleted-keys` shadows the base for
    that key.  A later `kv-add-to-set` repopulates it from the overlay *only* — the base
    stays shadowed, which is \"deleted, then re-added fresh\".  `kv-put` shadows the same
    way, because a put replaces a key rather than merging into it.
  * **Wholesale clear.**  `kv-clear!` empties the overlay and sets `::cleared`, after
    which every base key reads absent.  That is O(1) rather than a tombstone per base
    key, and it is what makes `reindex` work on a fork: clear the merged index, then
    rebuild it from the merged records.

  Bookkeeping lives in the overlay under reserved keys — `::cleared`, `::deleted-keys`,
  and `[::removed K]` — namespaced here, so they cannot collide with an index key (every
  one of those is a vector tagged with an unnamespaced keyword, or `[:term-roster]`).
  Because the bookkeeping *is* overlay data, a durable overlay carries it durably and a
  remount serves the same merged view with no separate recovery step.

  ## What has to be merged, and why

  `kv-count` answers the **merged** cardinality, never the overlay's.  The count-aware
  trie is a selectivity structure — `plan/order` costs every conjunct off `count-at`, and
  `provers/est-bindings` off the functor root — so a base-blind count would not be a
  wrong answer, it would be a silently wrong *plan* for every query touching inherited
  content.  `kv-intersect` merges for the same reason: `sentexes-with-args` intersects
  the predicate-scoped argument roots, and it must see the base's postings
  or a fork would stop finding its own inherited facts.

  Merging is not the same as *building* the merged set, and the difference is the cost of
  every query plan a fork makes.  A key the fork has not touched — no overlay members, no
  recorded removal, no tombstone — merges to the base's own value, so `inherited?` names
  that case and `kv-count` / `kv-members` hand the base's own answer straight back.  Over
  a flat-map base the two roads read the same, because its `kv-members` is a reference
  return; over a `:dense` base, where the posting has to be materialized into a set first,
  counting through the merge cost 12.6 ms per call on a 100,000-handle root — a selectivity
  read, per conjunct, on a key the fork had never written to.  `kv-member?` is the same
  observation at member granularity: `exception-rule?` probes both sides rather than
  merging, which is what keeps the firing-path gate O(1) across the `KvBackend` protocol.

  `kv-get` is the scalar/counter read and does **not** merge set values: an overlay value
  shadows the base's.  No key in the index is read both ways — the trie's counters are
  read by `kv-get` and its handle sets by `kv-members` — and a backend is free to hold a
  posting in a private representation (`vaelii.impl.dense-kv` returns an `IntPostings`
  here), so merging at this op would mean type-testing another backend's internals.
  `kv-entries`, whose contract *is* Clojure sets, merges properly.

  **Single writer.**  Pure runs one (docs/storage.md).  A batch is applied op by op
  through this decorator rather than as one atomic step the way `MemoryKvBackend` applies
  it, so the instance lock is held around the whole of `kv-batch` — an incidental reader
  beside the writer then sees a batch whole or not at all, as it does on every other
  backend."
  (:require [clojure.set :as set]
            [vaelii.impl.protocols :as p]))

;; ---- reserved bookkeeping keys --------------------------------------------

(def ^:private cleared-key
  "Set once `kv-clear!` has run: every base key reads absent from here on."
  ::cleared)

(def ^:private deleted-keys-key
  "A set of the keys whose base value is shadowed by a sticky tombstone."
  ::deleted-keys)

(defn- removed-key
  "Where the overlay records the base members it removed from the set at `k`."
  [k] [::removed k])

(defn- reserved-key? [k]
  (or (= k cleared-key)
      (= k deleted-keys-key)
      (and (vector? k) (= ::removed (first k)))))

;; ---- the merged view ------------------------------------------------------

(defn- cleared? [overlay] (some? (p/kv-get overlay cleared-key)))

(defn- shadowed?
  "Is the base's value at `k` invisible — wholesale-cleared, or tombstoned?

  The tombstone roster is **probed**, never materialized.  Every read through the `KvBackend` protocol asks
  this — `inherited?` is on the path of every `kv-count` and `kv-members`, and
  `merged-member?` is what keeps the `exception-rule?` gate O(1) — so building the whole
  set of tombstoned keys to test one of them would put the fork's delete count on the
  cost of every read it makes.  `kv-member?` is the op that answers it as a probe on
  every backend, which is the reason it is on the protocol."
  [overlay k]
  (or (cleared? overlay)
      (p/kv-member? overlay deleted-keys-key k)))

(defn- overlay-has? [overlay k] (some? (p/kv-get overlay k)))

(defn- inherited?
  "Is the merged view at `k` *exactly* the base's own value — nothing to merge in and
  nothing to take out?  Read the merge rule backwards: `(base ∪ own) − removed` collapses
  to `base` precisely when the base is visible (not cleared, not tombstoned), the overlay
  holds no members of its own at `k`, and it has recorded no removal there.  Emptiness is
  read through `kv-get` because every backend drops a set key as it empties, so a key it
  answers nil for holds nothing — and because `kv-count` is defined on set keys only,
  while `[::removed K]` and the trie's counters share one keyspace.

  This is the structure of nearly every key a fork touches: a fork inherits almost all of its
  content and writes a little (docs/overlay.md), so this is the case that decides what a
  read on a fork costs.  Answering it lets `kv-count` be the base's own `kv-count` and
  `kv-members` the base's own set — against a `:dense` base, an O(1) `pcard` and one
  materialization rather than a materialization plus a copy per call."
  [overlay k]
  (and (not (shadowed? overlay k))
       (not (overlay-has? overlay k))
       (not (overlay-has? overlay (removed-key k)))))

(defn- merged-members [overlay base k]
  (if (inherited? overlay k)
    (p/kv-members base k)                         ; nothing to merge: the base's own value
    (let [own     (p/kv-members overlay k)
          removed (p/kv-members overlay (removed-key k))]
      (if (shadowed? overlay k)
        own                                        ; base hidden: the overlay's own set is all
        (let [merged (into (p/kv-members base k) own)]
          (if (seq removed) (set/difference merged removed) merged))))))

(defn- merged-count
  "The merged cardinality.  An inherited key delegates to the base's own `kv-count`, which
  every backend answers without building anything; anything else is counted off the merged
  set, since a union minus a removal set has no cardinality shortcut."
  [overlay base k]
  (if (inherited? overlay k)
    (p/kv-count base k)
    (count (merged-members overlay base k))))

(defn- merged-member?
  "Membership in the merged view, transcribed from the same rule `merged-members` builds:
  shadowed, only the overlay's own set can hold it; otherwise either side may contribute
  it and a recorded removal takes it back out.  Three O(1) probes at worst, and never the
  merged set — which is the whole point, since the caller is `exception-rule?`."
  [overlay base k m]
  (if (shadowed? overlay k)
    (p/kv-member? overlay k m)
    (and (or (p/kv-member? overlay k m)
             (p/kv-member? base k m))
         (not (p/kv-member? overlay (removed-key k) m)))))

(defn- merged-get [overlay base k]
  (cond
    (overlay-has? overlay k) (p/kv-get overlay k)
    (shadowed? overlay k)    nil
    :else                    (p/kv-get base k)))

(defn- base-has?
  "Does the base hold a *visible* value at `k`?  Read through `kv-get`, which every
  backend under `KvIndexStore` answers non-nil for a key it holds whatever the value's
  private shape (`vaelii.impl.dense-kv` hands back its `IntPostings`) — `kv-count` is not
  an alternative here, since it is defined on set keys only and the trie's counters share
  the keyspace with them."
  [overlay base k]
  (and (not (shadowed? overlay k))
       (some? (p/kv-get base k))))

;; ---- the write primitives -------------------------------------------------

(defn- tombstone!
  "Shadow the base's value at `k` — sticky, so a later repopulation of `k` in the overlay
  does not resurrect what the base held."
  [overlay k]
  (p/kv-add-to-set overlay deleted-keys-key k))

(defn- seed-counter!
  "Copy-on-write for a counter: give the overlay an absolute value at `k`, seeded from the
  base (0 when the base is shadowed or absent), so every later increment returns base+net
  and no read has to add the two together."
  [overlay base k]
  (when-not (overlay-has? overlay k)
    (p/kv-put overlay k (long (or (when-not (shadowed? overlay k) (p/kv-get base k)) 0)))))

(defn- put*
  "A `kv-put` replaces the key rather than merging into it, so it shadows the base and
  drops the overlay's own removal bookkeeping for `k`."
  [overlay base k v]
  (when (base-has? overlay base k) (tombstone! overlay k))
  (p/kv-delete overlay (removed-key k))
  (p/kv-put overlay k v))

(defn- delete*
  [overlay base k]
  (p/kv-delete overlay k)
  (p/kv-delete overlay (removed-key k))
  (when (base-has? overlay base k) (tombstone! overlay k)))

(defn- add-to-set*
  "Adding a member un-records it as removed and lands it in the overlay's own set.  The
  tombstone is deliberately left in place: a deleted key that is re-populated holds what
  the overlay put there and nothing the base held."
  [overlay k m]
  ;; guarded: nearly every key a fork writes has no removal record at all, and on a
  ;; durable overlay half an unconditional remove is a WAL frame per posting that
  ;; removed nothing
  (when (p/kv-member? overlay (removed-key k) m)
    (p/kv-remove-from-set overlay (removed-key k) m))
  (p/kv-add-to-set overlay k m))

(defn- remove-from-set*
  "Drop `m` from the overlay's own set, and — when the base contributes it to the merged
  view — record it as removed, since the base's set cannot be edited.  The base is asked
  through `kv-member?`, never `kv-members`: a retract on a fork emits one of these per
  term of the sentex plus one per root key, and materializing the base's whole posting
  to answer each membership would cost a 100M-handle set walk per probe on a `:dense`
  base — the same rule `merged-member?` states, eight lines up."
  [overlay base k m]
  (p/kv-remove-from-set overlay k m)
  (when (and (not (shadowed? overlay k))
             (p/kv-member? base k m))
    (p/kv-add-to-set overlay (removed-key k) m)))

;; ---- the decorator --------------------------------------------------------

(defrecord OverlayKv [overlay base lock]
  p/KvBackend
  (kv-get  [_ k]   (locking lock (merged-get overlay base k)))
  (kv-put  [_ k v] (locking lock (put* overlay base k v)) nil)
  (kv-delete [_ k] (locking lock (delete* overlay base k)) nil)

  (kv-increment [_ k]
    (locking lock (seed-counter! overlay base k) (p/kv-increment overlay k)))
  (kv-decrement [_ k]
    (locking lock (seed-counter! overlay base k) (p/kv-decrement overlay k)))

  (kv-add-to-set      [_ k m] (locking lock (add-to-set* overlay k m)) nil)
  (kv-remove-from-set [_ k m] (locking lock (remove-from-set* overlay base k m)) nil)
  (kv-members [_ k]   (locking lock (merged-members overlay base k)))
  (kv-member? [_ k m] (locking lock (merged-member? overlay base k m)))
  (kv-count   [_ k]   (locking lock (merged-count overlay base k)))

  ;; the merged intersection: `sentexes-with-args` narrows on every named
  ;; predicate-scoped argument root at once, and each of those roots may be part base
  ;; and part fork.
  ;;
  ;; When *every* key is inherited the merged view is the base's view key for key, so the
  ;; whole narrowing goes to the base and is done in whatever representation it holds —
  ;; which on a `:dense` base is the postings themselves rather than the sets they would
  ;; make.  That is the structure of nearly every read on a fork (`inherited?`), and merging
  ;; first would throw the representation away before the base ever saw the question.
  (kv-intersect [_ ks]
    (locking lock
      (cond
        (empty? ks)                          #{}
        (every? #(inherited? overlay %) ks)  (p/kv-intersect base ks)
        :else (reduce set/intersection (map #(merged-members overlay base %) ks)))))

  ;; every op routed back through this decorator, so the merge model applies to a batched
  ;; write exactly as to a direct one; the lock is held around the whole batch (a Java
  ;; monitor is reentrant, so the per-op re-entry is free)
  (kv-batch [this ops]
    (locking lock
      (mapv (fn [[op k a]]
              (case op
                :put             (p/kv-put this k a)
                :delete          (p/kv-delete this k)
                :increment       (p/kv-increment this k)
                :decrement       (p/kv-decrement this k)
                :add-to-set      (p/kv-add-to-set this k a)
                :remove-from-set (p/kv-remove-from-set this k a)
                ;; the one refusal every backend spells (`p/unknown-op!`): a caller
                ;; discriminating on `:type` must not have to know which adapter it
                ;; reached
                (p/unknown-op! op)))
            ops)))

  ;; The portable projection of the *merged* view — what an export of a fork writes.  Set
  ;; values are merged (the contract says they arrive as Clojure sets, so this is the one
  ;; op at which merging a posting needs no knowledge of a backend's representation);
  ;; scalars shadow.  Both halves are realized, and the comment on the `concat` below
  ;; says why laziness is not available here — so this is the one read on the function that
  ;; costs a walk of the base, which is what a portable projection of a fork is worth.
  (kv-entries [_]
    (locking lock
      ;; `first`, not `key`: the contract says entries are pairs, and the tiered
      ;; backend yields plain vectors where the map-backed ones yield `MapEntry`s
      (let [own (into {} (remove (comp reserved-key? first)) (p/kv-entries overlay))
            own-merged (mapv (fn [[k v]]
                               [k (if (set? v) (merged-members overlay base k) v)])
                             own)
            inherited (when-not (cleared? overlay)
                        (into [] (keep (fn [[k v]]
                                         (when-not (or (contains? own k) (shadowed? overlay k))
                                           (if (set? v)
                                             (let [ms (merged-members overlay base k)]
                                               (when (seq ms) [k ms]))
                                             [k v]))))
                              (p/kv-entries base)))]
        ;; Realized **inside** the monitor, both halves.  A lazy `concat` handed back
        ;; from here realizes after the lock is released, and each element it then
        ;; produces calls `merged-members` / `shadowed?` / `cleared?` — the reads this
        ;; monitor exists to serialize, so a fork dumped while anything writes it
        ;; projected two states at once.  The base half costs a walk of the base, which
        ;; is what a portable projection of the merged view is worth.
        (concat own-merged inherited))))

  ;; an install lands in the overlay in *its* representation (that is the whole point of
  ;; `kv-load` over a `kv-put` of a raw set), shadowing whatever the base holds at those
  ;; keys — a load replaces, like the put it stands in for
  (kv-load [_ entries]
    (locking lock
      (doseq [batch (partition-all 4096 entries)]
        (doseq [[k _] batch]
          (when (base-has? overlay base k) (tombstone! overlay k))
          (p/kv-delete overlay (removed-key k)))
        (p/kv-load overlay batch)))
    nil)

  ;; O(1) rather than a tombstone per base key: the marker hides the base wholesale, and
  ;; it is set *after* the wipe because the wipe would otherwise take it with it
  (kv-clear! [_]
    (locking lock
      (p/kv-clear! overlay)
      (p/kv-put overlay cleared-key true))
    nil))

(defn overlay-kv
  "Compose a writable `overlay` `KvBackend` over a read-only `base` one."
  [overlay base]
  (->OverlayKv overlay base (Object.)))

(defn overlay-kv?
  "Is `backend` one of these — i.e. is it already a fork's index half?  Asked by
  `vaelii.impl.overlay.mount`, which refuses a base that is itself a fork."
  [backend]
  (instance? OverlayKv backend))
