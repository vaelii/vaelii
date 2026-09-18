;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.store
  "`OverlayRecordStore` — a composite `RecordStore` layering a private **writable**
  overlay over a shared **read-only** base.  Reads resolve overlay-first, skipping
  tombstoned base handles; writes land only in the overlay; the base is never mutated.
  The record half of the `:overlay` backend (the index half is
  `vaelii.impl.overlay.kv`).

  * **The id boundary.**  The overlay's handle counter is seeded above every handle the base
    holds, so a newly minted handle can never collide with a base one.  A record written
    at a handle the base *already* uses is therefore an **override** — the same handle,
    a different record — and the overlay's copy wins every read.  That is how a base
    record is edited without editing the base: `mark-premise` materializes an override
    before it writes, since the assumption strength lives on the record.
  * **Tombstones.**  Deleting a base handle cannot touch the base, so it is recorded and
    the read path filters it.  They are sticky: a base record cannot come back through
    fall-through, only by being written again into the overlay (a revival, at the same
    handle).
  * **Wholesale clear.**  `clear-records!` empties the overlay and marks the base
    hidden — one flag rather than a tombstone per base handle — so a fork can be reset
    to empty without walking what it inherited.
  * **Durable bookkeeping.**  The tombstone sets, the released premise marks and the
    hidden flag live in a small `KvBackend` under reserved keys, mirrored in atoms for
    the read path.  Every mutation writes through, and a mount rebuilds the atoms from
    it, so remounting a durable overlay over the same base serves the same merged view:
    a deleted base record stays deleted, a released premise stays released.  An
    ephemeral fork passes an in-RAM bookkeeping backend and pays nothing for the
    machinery.

  **Counts need no delta bookkeeping here.**  A `RecordStore` exposes handle
  *sets* rather than counts, and everything counted — `sentex-count`, `count-in-context`,
  `count-with-functor` — is read off the index, where the merge is the trie's own
  copy-on-write counters and the merged root sets (`vaelii.impl.overlay.kv`).  So the
  counts a fork reports are exact by construction rather than by a second, parallel
  accounting that could drift from the records.

  **The fork's belief is rebuilt, not overlaid.**  The JTMS is not storage — it is a
  separate protocol (`vaelii.impl.jtms`) over derived state — and the engine already has the
  operation that computes it from records: `recover`.  So a fork gets its own network by
  recovering over the merged view, and nothing here layers one truth-maintenance graph
  over another."
  (:require [clojure.set :as set]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.protocols :as p]))

;; ---- reserved bookkeeping keys --------------------------------------------

(def ^:private cleared-key      ::cleared)
(def ^:private sx-tombstone-key ::sentex-tombstoned)
(def ^:private jd-tombstone-key ::justification-tombstoned)
(def ^:private pv-tombstone-key ::provenance-tombstoned)
(def ^:private released-key     ::premise-released)

;; ---- the fast view + its write-through --------------------------------------
;; Each atom is a mirror of one bookkeeping key; every mutation writes both, and a mount
;; reads the atoms back out of the backend.  The atoms are what the read path touches, so
;; a durable bookkeeping backend costs the reads nothing.

(defn- handle
  "`id` as a long, or nil when it is not a handle at all.  Both concrete record stores
  read a nil or non-integer key as a **miss** rather than throwing
  (`vaelii.impl.memory`, `vaelii.impl.disk.record-store`), and the merge must not be the
  one layer that turns a documented nil answer into an NPE: `retract!`, `provenance` and
  `edit {:remove [nil]}` all reach here with whatever the caller passed, and `handle-of`
  answers nil for a sentence the KB does not hold."
  [id]
  (when (integer? id) (long id)))

(defn- sample
  "A handle the **merged** view holds, given the two halves' own samples and a predicate
  saying whether the merged view keeps one — `nil` only when neither half holds anything.

  `nil` is the part that decides it.  Every caller of a sampler reads it as *this store is
  empty* (`kb/write-hazards`, `kb/discharge-over-empty-store!`, `open-kb`'s recovery
  branch), so a fork that deleted the one record its base happened to sample must not read
  as an empty fork: where the sample is a handle this fork took out, the answer falls back
  to the merged enumeration, which is the walk the capability exists to avoid and is
  reached only in that case.  Which handle comes back is the store's own choice
  (`protocols/Tallying`), so preferring the overlay's adds no work and skips the base."
  [own inherited keeps? ids]
  (let [h (if (some? own) own inherited)]
    (cond
      (nil? h)   nil
      (keeps? h) h
      :else      (first (ids)))))

(defn- note! [a meta-kv k id]
  (swap! a conj id)
  (p/kv-add-to-set meta-kv k id))

(defn- unnote! [a meta-kv k id]
  (swap! a disj id)
  (p/kv-remove-from-set meta-kv k id))

(defrecord OverlayRecordStore [overlay base meta-kv counter
                               hidden? sx-tombstoned jd-tombstoned pv-tombstoned released]

  p/RecordStore
  ;; strictly above every handle the base holds, so a minted handle is never a base one
  ;; and a handle at or below the watermark is unambiguously an override
  (next-id [_] (long (swap! counter inc)))

  (put-sentex [this sentex]
    (let [id (long (or (:id sentex) (p/next-id this)))]
      ;; an explicit handle (an import, a revival) must carry the counter with it, or the
      ;; next mint would reissue it and overwrite a record with no error
      (swap! counter max id)
      (when (contains? @sx-tombstoned id) (unnote! sx-tombstoned meta-kv sx-tombstone-key id))
      (p/put-sentex overlay (assoc sentex :id id))))

  (get-sentex [_ id]
    (or (p/get-sentex overlay id)
        (when-not (or @hidden? (contains? @sx-tombstoned (handle id)))
          (p/get-sentex base id))))

  (delete-sentex! [_ id]
    (let [id (handle id)]
      (when (p/get-sentex overlay id) (p/delete-sentex! overlay id))
      ;; Provenance dies with its record on both concrete stores, and the overlay may
      ;; hold a stamp for a handle whose *record* it never overrode — `put-provenance`
      ;; writes to the overlay whatever side the record is on.  So the drop is stated
      ;; here rather than left to be a consequence of deleting the record.
      (p/delete-provenance! overlay id)
      (when-not @hidden?
        (when (p/get-sentex base id)
          (note! sx-tombstoned meta-kv sx-tombstone-key id)
          ;; the premise mark needs no separate release: `premise-ids` subtracts the
          ;; tombstoned handles, so a deleted base premise is already gone from it
          (when (p/get-provenance base id)
            (note! pv-tombstoned meta-kv pv-tombstone-key id)))))
    nil)

  (put-justification [this justification]
    (let [id (long (or (:id justification) (p/next-id this)))]
      (swap! counter max id)
      (when (contains? @jd-tombstoned id) (unnote! jd-tombstoned meta-kv jd-tombstone-key id))
      (p/put-justification overlay (assoc justification :id id))))

  (get-justification [_ id]
    (or (p/get-justification overlay id)
        (when-not (or @hidden? (contains? @jd-tombstoned (handle id)))
          (p/get-justification base id))))

  (delete-justification! [_ id]
    (let [id (handle id)]
      (when (p/get-justification overlay id) (p/delete-justification! overlay id))
      (p/delete-provenance! overlay id)         ; as in `delete-sentex!`
      (when-not @hidden?
        (when (p/get-justification base id) (note! jd-tombstoned meta-kv jd-tombstone-key id))
        (when (p/get-provenance base id) (note! pv-tombstoned meta-kv pv-tombstone-key id))))
    nil)

  (put-provenance [_ id prov]
    (when (contains? @pv-tombstoned (handle id))
      (unnote! pv-tombstoned meta-kv pv-tombstone-key id))
    (p/put-provenance overlay id prov))

  (get-provenance [_ id]
    (or (p/get-provenance overlay id)
        (when-not (or @hidden? (contains? @pv-tombstoned (handle id)))
          (p/get-provenance base id))))

  (delete-provenance! [_ id]
    (let [id (handle id)]
      (p/delete-provenance! overlay id)
      (when (and (not @hidden?) (p/get-provenance base id))
        (note! pv-tombstoned meta-kv pv-tombstone-key id)))
    nil)

  ;; an override lives in both halves, so the union dedups it to the one handle it is
  (sentex-ids [_]
    (let [own (p/sentex-ids overlay)]
      (if @hidden?
        own
        (set/difference (into (set (p/sentex-ids base)) own) @sx-tombstoned))))

  (justification-ids [_]
    (let [own (p/justification-ids overlay)]
      (if @hidden?
        own
        (set/difference (into (set (p/justification-ids base)) own) @jd-tombstoned))))

  ;; The strength is a field on the sentex record, so marking a base premise means
  ;; **writing** a base record — which is what an override is for.  Materialize the copy
  ;; first, then mark it in the overlay like any other handle.
  (mark-premise [this id strength]
    (let [id (long id)]
      (when-not (p/get-sentex overlay id)
        (when-let [sx (p/get-sentex this id)]
          (p/put-sentex overlay (assoc sx :id id))))
      (p/mark-premise overlay id strength)
      ;; guarded, so the ordinary assert writes nothing to the bookkeeping backend — the
      ;; release set is only ever consulted for a handle that is in it
      (when (contains? @released id) (unnote! released meta-kv released-key id)))
    nil)

  (unmark-premise! [this id]
    (let [id (long id)]
      (if (p/get-sentex overlay id)
        (p/unmark-premise! overlay id)
        ;; materialize the override only when there is a mark to remove — the teardown
        ;; unmarks every datum it retracts, and copying a derived base record here
        ;; would write a frame whose only fate is the tombstone that follows
        (when-let [sx (p/get-sentex this id)]
          (when (some? (:strength sx))
            (p/put-sentex overlay (assoc sx :id id))
            (p/unmark-premise! overlay id))))
      ;; The base's own mark cannot be removed, so it is released instead.  Whether the
      ;; base holds one is read off the record's `:strength`, which is what a premise mark
      ;; *is* on both record stores — `mark-premise` writes it there, and the disk store's
      ;; recovery rebuilds its whole premise set from it.
      (when (and (not @hidden?) (:strength (p/get-sentex base id)))
        (note! released meta-kv released-key id)))
    nil)

  (premise-ids [_]
    (let [own (p/premise-ids overlay)]
      (if @hidden?
        own
        ;; a tombstoned handle is not a premise: the record it marked is gone
        (set/difference (into (set (p/premise-ids base)) own) @released @sx-tombstoned))))

  (premise-strength [_ id]
    (cond
      (p/get-sentex overlay id) (p/premise-strength overlay id)
      (and (not @hidden?)
           (not (contains? @sx-tombstoned (handle id)))
           (p/get-sentex base id)) (p/premise-strength base id)
      :else :default))

  ;; O(1) rather than a tombstone per inherited handle: the flag hides the base
  ;; wholesale, and the bookkeeping is wiped with it (nothing is left to shadow).
  ;;
  ;; The handle counter restarts from 1, as both concrete stores' does — a cleared store
  ;; is a fresh one, and a handle allocation that depended on what the store *used* to
  ;; hold would make handles a function of history rather than of content.  Safe here
  ;; because the flag is sticky: no base handle is reachable again, so reissuing one
  ;; collides with nothing, and a remount takes the `max` over both watermarks so
  ;; anything minted after it stays above the base's range regardless.
  (clear-records! [_]
    (p/clear-records! overlay)
    (p/kv-clear! meta-kv)
    (p/kv-put meta-kv cleared-key true)
    (reset! counter 0)
    (reset! hidden? true)
    (reset! sx-tombstoned #{})
    (reset! jd-tombstoned #{})
    (reset! pv-tombstoned #{})
    (reset! released #{})
    nil)

  ;; **The samplers are what this is for; the tallies are the honest merged count.**
  ;; `Tallying` exists so a store whose enumeration is a *query* is not made to run one to
  ;; answer *how many* and *is there anything* — and a fork over such a base inherits that
  ;; question whole: `open-kb`'s recovery branch and `kb/write-hazards` both ask, and
  ;; without this the answer is `base ∪ overlay − tombstoned` materialized, which over a
  ;; `:pg` base is the table.  The samplers escape it by asking each half for one handle.
  ;;
  ;; The two tallies do not, and cannot: the merged cardinality is
  ;; `|base| + |own \ base| − |tombstoned|`, and the middle term needs both sets.  They are
  ;; implemented rather than left out because **this protocol cannot be half-implemented**
  ;; — `capabilities` branches on `satisfies?`, which a `defrecord` answers true for the
  ;; whole protocol however few methods it lists, so an omitted one is an
  ;; `AbstractMethodError` at the call rather than the fallback the entry point promises
  ;; (`protocols/BulkAnnotating` states the same rule one protocol over).  So they read exactly
  ;; what the fallback read, and the fork pays for the samplers alone.
  p/Tallying
  (sentex-tally        [this] (count (p/sentex-ids this)))
  (justification-tally [this] (count (p/justification-ids this)))
  (a-sentex-id [this]
    (sample (cap/some-sentex-id overlay)
            (when-not @hidden? (cap/some-sentex-id base))
            #(not (contains? @sx-tombstoned (handle %)))
            #(p/sentex-ids this)))
  (a-justification-id [this]
    (sample (cap/some-justification-id overlay)
            (when-not @hidden? (cap/some-justification-id base))
            #(not (contains? @jd-tombstoned (handle %)))
            #(p/justification-ids this)))
  (a-premise-id [this]
    ;; `premise-ids` subtracts the released marks as well as the tombstones, and the
    ;; subtraction there covers the union rather than the base half alone — so the same
    ;; predicate is applied to whichever half the sample came from
    (sample (cap/some-premise-id overlay)
            (when-not @hidden? (cap/some-premise-id base))
            #(let [h (handle %)]
               (not (or (contains? @released h) (contains? @sx-tombstoned h))))
            #(p/premise-ids this)))

  ;; **The hint is forwarded to both halves, and it is the base's that is worth having.**
  ;; A fork's own records are `:memory` or `:disk` (a `:pg` overlay is refused at
  ;; `open-kb`), neither of which prefetches, so the overlay arm is a no-op today and is
  ;; here so a later one is not silently skipped.  The base arm is the point: a fork
  ;; `recover`s over the merged view, which walks every record it inherits, and over a
  ;; `:pg` base that is a round trip apiece without the chunk hint.
  ;;
  ;; What it costs a fork over a base that does **not** prefetch: `cap/prefetcher` answers
  ;; non-nil for every fork now, so the two recovery walks wrap their enumeration in
  ;; `cap/hinting`'s lazy seq and issue a no-op call per chunk of 1,000.  Both walks
  ;; consume sequentially and neither keeps the enumeration, which is the condition
  ;; `hinting` states for that substitution.
  p/Prefetching
  (prefetch-sentexes! [_ ids]
    (when (satisfies? p/Prefetching overlay) (p/prefetch-sentexes! overlay ids))
    (when (and (not @hidden?) (satisfies? p/Prefetching base))
      (p/prefetch-sentexes! base ids))
    nil)
  (prefetch-justifications! [_ ids]
    (when (satisfies? p/Prefetching overlay) (p/prefetch-justifications! overlay ids))
    (when (and (not @hidden?) (satisfies? p/Prefetching base))
      (p/prefetch-justifications! base ids))
    nil))

(defn overlay-record-store
  "Compose a writable `overlay` `RecordStore` over a read-only `base` one, with `meta-kv`
  holding the overlay's record-level bookkeeping.

  The mount reads the bookkeeping back — so a durable overlay remounted over the same
  base serves the merged view it was left in — and seeds the handle counter above both
  stores' watermarks, which is what keeps a minted handle out of the base's range even
  after a restart."
  [overlay base meta-kv]
  (let [base-next (long (p/next-id base))          ; allocation, not mutation (see `frozen`)
        own-next  (long (p/next-id overlay))]
    (map->OverlayRecordStore
     {:overlay        overlay
      :base           base
      :meta-kv        meta-kv
      :counter        (atom (max base-next own-next))
      :hidden?        (atom (some? (p/kv-get meta-kv cleared-key)))
      :sx-tombstoned  (atom (set (p/kv-members meta-kv sx-tombstone-key)))
      :jd-tombstoned  (atom (set (p/kv-members meta-kv jd-tombstone-key)))
      :pv-tombstoned  (atom (set (p/kv-members meta-kv pv-tombstone-key)))
      :released       (atom (set (p/kv-members meta-kv released-key)))})))

(defn overlay-record-store?
  "Is `store` one of these — i.e. is it already a fork's record half?  Asked by
  `vaelii.impl.overlay.mount`, which refuses a base that is itself a fork."
  [store]
  (instance? OverlayRecordStore store))
