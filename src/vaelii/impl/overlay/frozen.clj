;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.frozen
  "The read-only mount: a `KvBackend` and a `RecordStore` that answer every read and
  **refuse every write**.

  A base shared by N forks is only shared if nothing can write it, and the honest way to
  guarantee that is structurally rather than by review: an overlay composes over one of
  these, so a write path that forgot to divert fails loudly at the boundary instead of
  silently mutating what every other fork is reading.  That is invariant 1 of
  docs/overlay.md, held by construction.

  Three calls are deliberately *not* refusals.

  * `next-id` on the frozen record store.  It hands out a handle nobody holds and
    stores no record, and it is what the overlay's id watermark is seeded from
    (`vaelii.impl.overlay.store`) — the alternative, a `max` over the base's whole live-id
    set, is O(base) at every mount.  It is not free of the base, though: it advances the
    base's monotonic counter, which a disk store persists at its next flush, so a mount
    skips one handle permanently.  Allocating-only is what keeps that safe — a skipped
    handle is never reused, and recovery takes `max(blob, 1 + highest slot)`.  One JVM
    holds the base's directory lock, so there is no second mounter to agree with.
  * `kv-entries` / `sentex-ids` and friends.  Enumeration is a read.
  * `prefetch-sentexes!` / `prefetch-justifications!`.  A hint returns nothing and warms
    a cache; every record still comes back through `get-sentex`, so it changes what the
    base *holds* not at all — and refusing it would cost a `:pg` base its one defence
    against a fork's recovery walk (`vaelii.impl.protocols`, `Prefetching`).

  This is a decorator, not a file mode: it says nothing about how the underlying store
  was opened.  Opening the base's files read-only at the OS level is the disk backend's
  business and orthogonal — this is what makes the *composition* safe whatever the base
  is (memory, disk, or a later SQL store)."
  (:require [vaelii.impl.capabilities :as cap]
            [vaelii.impl.protocols :as p]))

(defn- refuse [op]
  (throw (ex-info (str "the overlay's base is mounted read-only — " op " is refused."
                       "  A fork writes through its own half, so call it on the fork's"
                       " stores rather than on the base's")
                  {:type :frozen-base :op op})))

;; ---- the index half --------------------------------------------------------

(defrecord FrozenKv [base]
  p/KvBackend
  (kv-get       [_ k]   (p/kv-get base k))
  (kv-members   [_ k]   (p/kv-members base k))
  (kv-member?   [_ k m] (p/kv-member? base k m))
  (kv-count     [_ k]   (p/kv-count base k))
  (kv-intersect [_ ks]  (p/kv-intersect base ks))
  (kv-entries   [_]     (p/kv-entries base))

  (kv-put             [_ _ _] (refuse "kv-put"))
  (kv-delete          [_ _]   (refuse "kv-delete"))
  (kv-increment       [_ _]   (refuse "kv-increment"))
  (kv-decrement       [_ _]   (refuse "kv-decrement"))
  (kv-add-to-set      [_ _ _] (refuse "kv-add-to-set"))
  (kv-remove-from-set [_ _ _] (refuse "kv-remove-from-set"))
  (kv-batch           [_ _]   (refuse "kv-batch"))
  (kv-load            [_ _]   (refuse "kv-load"))
  (kv-clear!          [_]     (refuse "kv-clear!")))

(defn frozen-kv
  "`base` as a read-only `KvBackend`."
  [base]
  (if (instance? FrozenKv base) base (->FrozenKv base)))

;; ---- the record half -------------------------------------------------------

(defrecord FrozenRecords [base]
  p/RecordStore
  (get-sentex        [_ id] (p/get-sentex        base id))
  (get-justification [_ id] (p/get-justification base id))
  (get-provenance    [_ id] (p/get-provenance    base id))
  (sentex-ids        [_]    (p/sentex-ids        base))
  (justification-ids [_]    (p/justification-ids base))
  (premise-ids       [_]    (p/premise-ids       base))
  (premise-strength  [_ id] (p/premise-strength  base id))
  ;; allocation, not mutation — see the namespace docstring
  (next-id           [_]    (p/next-id base))

  (put-sentex           [_ _]   (refuse "put-sentex"))
  (delete-sentex!       [_ _]   (refuse "delete-sentex!"))
  (put-justification    [_ _]   (refuse "put-justification"))
  (delete-justification! [_ _]  (refuse "delete-justification!"))
  (put-provenance       [_ _ _] (refuse "put-provenance"))
  (delete-provenance!   [_ _]   (refuse "delete-provenance!"))
  (mark-premise         [_ _ _] (refuse "mark-premise"))
  (unmark-premise!      [_ _]   (refuse "unmark-premise!"))
  (clear-records!       [_]     (refuse "clear-records!"))

  ;; A frozen base is a read of its base, tallies included — and through the *helpers*,
  ;; not the protocol ops, so a base without the capability falls back to its own
  ;; enumeration here rather than throwing.  Always answering it is what lets the fork
  ;; above ask the question at all: `OverlayRecordStore` answers its own `Tallying` out of
  ;; these, and a base that refused them would put every `open-kb` emptiness probe back on
  ;; the merged roster — which over a `:pg` base is the whole table.
  p/Tallying
  (sentex-tally        [_] (cap/count-sentexes        base))
  (justification-tally [_] (cap/count-justifications  base))
  (a-sentex-id         [_] (cap/some-sentex-id        base))
  (a-justification-id  [_] (cap/some-justification-id base))
  (a-premise-id        [_] (cap/some-premise-id       base))

  ;; **Forwarded, not refused.**  A hint is a read — it returns nothing, and every record
  ;; still arrives through `get-sentex` — so freezing a base is no reason to withhold it,
  ;; and every reason to pass it on: the store a fork is most worth taking over is the one
  ;; whose fetch is a network round trip, which is the store `Prefetching` exists for
  ;; (docs/storage.md).  Guarded, so a base that does not prefetch — every store the engine
  ;; ships — is a no-op here rather than a throw.
  p/Prefetching
  (prefetch-sentexes! [_ ids]
    (when (satisfies? p/Prefetching base) (p/prefetch-sentexes! base ids))
    nil)
  (prefetch-justifications! [_ ids]
    (when (satisfies? p/Prefetching base) (p/prefetch-justifications! base ids))
    nil))

(defn frozen-records
  "`base` as a read-only `RecordStore`."
  [base]
  (if (instance? FrozenRecords base) base (->FrozenRecords base)))
