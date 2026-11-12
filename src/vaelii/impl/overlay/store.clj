;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.store
  "`OverlayRecordStore` — a composite `RecordStore` layering a private **writable**
  overlay over a shared **read-only** base.  Reads resolve overlay-first, skipping
  tombstoned base handles; writes land only in the overlay; the base is never mutated.
  The record half of the `:overlay` backend (the index half is
  `vaelii.impl.overlay.kv`).

  * **The id boundary.**  The overlay mints each handle from the base's counter, so a
    minted handle matches no base one, even one minted after the mount.  A record written
    at a handle the base *already* uses is therefore an **override** — the same handle,
    a different record — and the overlay's copy wins every read.  That is how a base
    record is edited without editing the base: `mark-premise` materializes an override
    before it writes, since the assumption strength lives on the record.  The boundary
    holds over the base the handles were minted against, so a mount checks the base
    against what the last one recorded (`check-base-overlap!`, `accept-growth`).
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
    it, so remounting a durable overlay over the same base serves the same merged contents:
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
  recovering over the merged contents, and nothing here layers one truth-maintenance graph
  over another."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p])
  (:import [java.util.concurrent.locks ReentrantReadWriteLock]))

;; ---- reserved bookkeeping keys --------------------------------------------

(def ^:private cleared-key      ::cleared)
(def ^:private sx-tombstone-key ::sentex-tombstoned)
(def ^:private jd-tombstone-key ::justification-tombstoned)
(def ^:private pv-tombstone-key ::provenance-tombstoned)
(def ^:private released-key     ::premise-released)
(def ^:private watermark-key    ::base-watermark)
(def ^:private digested-key     ::base-digested)
(def ^:private minted-key       ::minted-ranges)
;; A durable fork's bookkeeping may hold the same handle set under this second key, which
;; the mount reads beside `digested-key` and nothing writes.
(def ^:private digested-key-alt ::base-pinned)

(defn- digest-key
  "Where the digest of the base record at handle `h` is kept, once the fork has written
  something that depends on it (`record-base-digest!`)."
  [h]
  [::base-digest h])

;; ---- the atom mirror + its write-through ------------------------------------
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
  "A handle the **merged** contents hold, given the two halves' own samples and a predicate
  saying whether the merged contents keep one — `nil` only when neither half holds anything.

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

(defn- base-digest
  "The content digest of the base record at handle `h` — a sentex's or a justification's
  (`vaelii.impl.io.fingerprint`) — or nil when the base holds neither there."
  [base h]
  (if-let [sx (p/get-sentex base h)]
    (fp/record-hash h sx)
    (when-let [j (p/get-justification base h)] (fp/justification-hash h j))))

(defn- digested?
  "Does the bookkeeping hold a base digest for handle `h`, under either key?"
  [meta-kv h]
  (or (p/kv-member? meta-kv digested-key h) (p/kv-member? meta-kv digested-key-alt h)))

(defn- record-base-digest!
  "Record what the base holds at `id` before the fork writes something that depends on it
  — a tombstone, an override, a released mark — so a mount over a base that holds a
  different record there is refused (`changed-base-records`) instead of applying the write
  to it.  A handle at or above `base-top`, the base's `next-id` at the mount, is one the
  fork minted, so an ordinary write pays one comparison and nothing else; a handle already
  digested keeps its first digest, which is the record the fork's state was written over."
  [base meta-kv base-top hidden? id]
  (when-let [h (handle id)]
    (when (and (< h (long @base-top)) (not @hidden?) (not (digested? meta-kv h)))
      (when-let [d (base-digest base h)]
        (p/kv-put meta-kv (digest-key h) d)
        (p/kv-add-to-set meta-kv digested-key h)))))

(def ^:private minted-chunk
  "How far past a handle it mints a fork's recorded range reaches, so the bookkeeping takes
  one write per this many mints."
  1024)

(defn minted-ranges
  "The `[lo hi)` handle ranges holding every handle the fork whose bookkeeping is
  `meta-kv` has minted, as a vector, or nil when it has recorded none.  A base opened with
  the fork's directory under `:fork-dirs` skips them (`vaelii.impl.overlay.mount`)."
  [meta-kv]
  (p/kv-get meta-kv minted-key))

(defn- record-minted!
  "Merge `ranges` into the minted ranges in the bookkeeping and in `minted`, its mirror."
  [meta-kv minted ranges]
  (let [m (cap/reserve-ranges @minted ranges)]
    (when (not= m @minted)
      (p/kv-put meta-kv minted-key (mapv vec m))
      (reset! minted m))))

(defn- note-minted!
  "Record that the fork holds handle `id` before the handle is used.  A handle the recorded
  ranges hold costs one lookup; one past them extends the session's range, which starts at
  `session-lo`, to `minted-chunk` beyond `id`, in one write."
  [meta-kv minted session-lo id]
  (let [id (long id)]
    (when (= id (cap/skip-reserved @minted id))
      (let [lo (long @session-lo)]
        (record-minted! meta-kv minted [(if (>= id lo) [lo (+ id 1 minted-chunk)] [id (inc id)])])))))

(defrecord OverlayRecordStore [overlay base meta-kv counter base-top
                               hidden? sx-tombstoned jd-tombstoned pv-tombstoned released
                               minted session-lo durable? base-opts rebase-lock follow]

  p/RecordStore
  ;; drawn from the base's counter past every handle the fork holds, so no base handle minted
  ;; after the mount names a fork record; a cleared fork counts alone (`clear-records!`)
  (next-id [_]
    (if @hidden?
      (long (swap! counter inc))
      (let [id (loop [] (let [b (long (p/next-id base))] (if (> b (long @counter)) b (recur))))]
        (swap! counter max id)
        (note-minted! meta-kv minted session-lo id)
        id)))

  (put-sentex [this sentex]
    (let [id (long (or (:id sentex) (p/next-id this)))]
      (observe/keep-before! this [:sentex id] #(p/get-sentex this id))
      (record-base-digest! base meta-kv base-top hidden? id)
      (when (and (:id sentex) (>= id (long @base-top)) (not @hidden?))
        (note-minted! meta-kv minted session-lo id))
      ;; an explicit handle (an import, a revival) must carry the counter with it, or the
      ;; next mint would reissue it and overwrite a record with no error
      (swap! counter max id)
      ;; the record before the tombstone's release, so a read between the two finds the
      ;; overlay's record or the tombstone, never the base's record (`delete-sentex!`)
      (let [r (p/put-sentex overlay (assoc sentex :id id))]
        (when (contains? @sx-tombstoned id) (unnote! sx-tombstoned meta-kv sx-tombstone-key id))
        r)))

  (get-sentex [_ id]
    (or (p/get-sentex overlay id)
        (when-not (or @hidden? (contains? @sx-tombstoned (handle id)))
          (p/get-sentex base id))))

  ;; **The tombstone is written before the overlay's copy is deleted**, and every other
  ;; write here keeps the same order: a read on another thread between two of the writes
  ;; answers the record the fork held before the call or the one it holds after it.  In
  ;; the other order a read between them misses the overlay, finds no tombstone, and
  ;; answers the base's record, which the fork had overridden.
  (delete-sentex! [this id]
    (let [id (handle id)]
      (observe/keep-before! this [:sentex id] #(p/get-sentex this id))
      (record-base-digest! base meta-kv base-top hidden? id)
      (when-not @hidden?
        (when (p/get-sentex base id)
          (note! sx-tombstoned meta-kv sx-tombstone-key id)
          ;; the premise mark needs no separate release: `premise-ids` subtracts the
          ;; tombstoned handles, so a deleted base premise is already gone from it
          (when (p/get-provenance base id)
            (note! pv-tombstoned meta-kv pv-tombstone-key id))))
      (when (p/get-sentex overlay id) (p/delete-sentex! overlay id))
      ;; Provenance dies with its record on both concrete stores, and the overlay may
      ;; hold provenance for a handle whose *record* it never overrode — `put-provenance`
      ;; writes to the overlay whatever side the record is on.  So the drop is stated
      ;; here rather than left to be a consequence of deleting the record.
      (p/delete-provenance! overlay id))
    nil)

  (put-justification [this justification]
    (let [id (long (or (:id justification) (p/next-id this)))]
      (observe/keep-before! this [:justification id] #(p/get-justification this id))
      (record-base-digest! base meta-kv base-top hidden? id)
      (when (and (:id justification) (>= id (long @base-top)) (not @hidden?))
        (note-minted! meta-kv minted session-lo id))
      (swap! counter max id)
      (let [r (p/put-justification overlay (assoc justification :id id))]
        (when (contains? @jd-tombstoned id) (unnote! jd-tombstoned meta-kv jd-tombstone-key id))
        r)))

  (get-justification [_ id]
    (or (p/get-justification overlay id)
        (when-not (or @hidden? (contains? @jd-tombstoned (handle id)))
          (p/get-justification base id))))

  (delete-justification! [this id]
    (let [id (handle id)]
      (observe/keep-before! this [:justification id] #(p/get-justification this id))
      (record-base-digest! base meta-kv base-top hidden? id)
      (when-not @hidden?                        ; tombstones first, as in `delete-sentex!`
        (when (p/get-justification base id) (note! jd-tombstoned meta-kv jd-tombstone-key id))
        (when (p/get-provenance base id) (note! pv-tombstoned meta-kv pv-tombstone-key id)))
      (when (p/get-justification overlay id) (p/delete-justification! overlay id))
      (p/delete-provenance! overlay id))
    nil)

  (put-provenance [_ id prov]
    (record-base-digest! base meta-kv base-top hidden? id)
    (let [r (p/put-provenance overlay id prov)]
      (when (contains? @pv-tombstoned (handle id))
        (unnote! pv-tombstoned meta-kv pv-tombstone-key id))
      r))

  (get-provenance [_ id]
    (or (p/get-provenance overlay id)
        (when-not (or @hidden? (contains? @pv-tombstoned (handle id)))
          (p/get-provenance base id))))

  (delete-provenance! [_ id]
    (let [id (handle id)]
      (record-base-digest! base meta-kv base-top hidden? id)
      (when (and (not @hidden?) (p/get-provenance base id))
        (note! pv-tombstoned meta-kv pv-tombstone-key id))
      (p/delete-provenance! overlay id))
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
      (record-base-digest! base meta-kv base-top hidden? id)
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
      (record-base-digest! base meta-kv base-top hidden? id)
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
  ;;
  ;; The flag is set before the overlay is emptied, for `delete-sentex!`'s reason: a read
  ;; between the two answers the overlay's record or nothing, never the base's.
  (clear-records! [_]
    (reset! hidden? true)
    (p/clear-records! overlay)
    (p/kv-clear! meta-kv)
    (p/kv-put meta-kv cleared-key true)
    (reset! counter 0)
    (reset! minted nil)
    (reset! sx-tombstoned #{})
    (reset! jd-tombstoned #{})
    (reset! pv-tombstoned #{})
    (reset! released #{})
    nil)

  ;; **The samplers are what this is for; the tallies are the exact merged count.**
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
  ;; `recover`s over the merged contents, which walks every record it inherits, and over a
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

(defn- base-holds? [base h]
  (some? (or (p/get-sentex base h) (p/get-justification base h))))

(defn- first-grown
  "The lowest handle the base holds at or above `watermark`, or nil when it holds none.

  `watermark` is the base's `next-id` at the previous mount: a handle allocated and never
  stored, so a base that holds it, or anything above it, has grown since.  The walk stops
  at the first hit, and over a base that did not grow it probes only the handles other
  mounts allocated in between."
  [base watermark base-next]
  (first (filter #(base-holds? base %) (range (long watermark) (long base-next)))))

(defn- minted-shared
  "The handles this fork minted that the base now holds.  Every handle the fork minted lies
  above `watermark`, so only `(watermark, min(base-next, own-next))` can be shared.  The
  range covers a handle the fork minted and then deleted too, which an except can still
  name."
  [base watermark base-next own-next]
  (filterv #(base-holds? base %)
           (range (inc (long watermark)) (min (long base-next) (long own-next)))))

(defn- holds-state?
  "Has this fork written anything — a record of its own, a tombstone, a released mark, or
  a rebuilt index (`index-cleared?`, which hides the base's index wholesale)?  Each was
  computed against the base the fork was mounted over then."
  [overlay meta-kv index-cleared?]
  (boolean (or index-cleared?
               (cap/some-sentex-id overlay)
               (cap/some-justification-id overlay)
               (some #(seq (p/kv-members meta-kv %))
                     [sx-tombstone-key jd-tombstone-key pv-tombstone-key released-key]))))

(defn- changed-base-records
  "The digested handles (`record-base-digest!`) at which the base no longer holds the
  record the fork's state was written over — a base rebuilt in another order, or one that
  lost a record.  One read per digested handle."
  [base meta-kv]
  (into [] (remove #(= (base-digest base %) (p/kv-get meta-kv (digest-key %))))
        (sort (into (set (p/kv-members meta-kv digested-key))
                    (p/kv-members meta-kv digested-key-alt)))))

(defn- overridden-unlike
  "The handles at which this fork holds a record that the base also holds with different
  content — the check for a fork mounted before the watermark was recorded, which has no
  range to probe.  An override copies the base record (`mark-premise`, a revival), so it
  differs at most in its strength.  One pass over the fork's own records, on the one mount
  that records the watermark."
  [overlay base]
  (let [unlike (fn [get-rec h]
                 (when-let [b (get-rec base h)]
                   (not= (dissoc b :strength) (dissoc (get-rec overlay h) :strength))))]
    (into (filterv #(unlike p/get-sentex %) (sort (p/sentex-ids overlay)))
          (filter #(unlike p/get-justification %))
          (sort (p/justification-ids overlay)))))

(def ^:private base-end-key    ::base-end)
(def ^:private base-blocks-key ::base-blocks)

(def ^:private summary-block
  "How many handles one sum of a base summary's `:blocks` covers."
  1024)

(defn- base-summary
  "One pass over `base`'s records: `:end`, one above the highest handle it holds (0 when it
  holds none); `:blocks`, the sum of each record's content digest (`base-digest`) per
  `summary-block` handles, below `:end`; and, given `old-end`, `:old-blocks`, the same sums
  over the handles below it, and `:arrivals`, the handles at or above it in ascending order."
  [base old-end]
  (let [blocks  (java.util.HashMap.)
        old     (java.util.HashMap.)
        arrived (java.util.ArrayList.)
        top     (volatile! -1)
        add!    (fn [^java.util.HashMap m b d] (.put m b (unchecked-add (long (or (.get m b) 0)) (long d))))
        fold    (fn [h d]
                  (let [h (long h) b (quot h summary-block)]
                    (vswap! top max h)
                    (add! blocks b d)
                    (if (and old-end (>= h (long old-end)))
                      (.add arrived h)
                      (add! old b d))))
        vec-of  (fn [^java.util.HashMap m end]
                  (mapv #(long (or (.get m %) 0)) (range (quot (+ (long end) (dec summary-block)) summary-block))))]
    (doseq [h (p/sentex-ids base)]
      (when-let [sx (p/get-sentex base h)] (fold h (fp/record-hash h sx))))
    (doseq [h (p/justification-ids base)]
      (when-let [j (p/get-justification base h)] (fold h (fp/justification-hash h j))))
    (let [end (inc (long @top))]
      (cond-> {:end end :blocks (vec-of blocks end)}
        old-end (assoc :old-blocks (vec-of old old-end)
                       :arrivals   (vec (sort arrived)))))))

(defn- record-summary! [meta-kv {:keys [end blocks]}]
  (p/kv-put meta-kv base-blocks-key blocks)
  (p/kv-put meta-kv base-end-key end))

(def ^:private overlap-shown
  "How many shared handles a `:fork-base-overlap` refusal names."
  20)

(defn- refuse-overlap! [why handles watermark]
  (throw (ex-info (str "this fork's base has changed since the fork was last mounted over it: "
                       why (when (seq handles)
                             (str " (" (str/join ", " (take overlap-shown handles))
                                  (when (> (count handles) overlap-shown) ", …") ")"))
                       ".  A fork's records, removals and index counts are written against"
                       " the base it was mounted over, so over this one it would hide base"
                       " sentences.  Mount the fork over the base it was taken against, and"
                       " import this base's dump into it with :rebase? true, which asserts its"
                       " writes again by content")
                  {:type      :fork-base-overlap
                   :handles   (into [] (take overlap-shown) handles)
                   :watermark watermark})))

(defn- check-base-overlap!
  "Refuse a mount over a base that has changed since this fork was last mounted — a newer
  starter, more files loaded at startup, the same files loaded in another order — once
  the fork has written anything.  A record at a handle the base now also holds would be
  read as an override of a base record the fork never saw; a key the fork emptied stays
  deleted, hiding what the base has since added under it; a tombstone or override at a
  handle the base now fills with another record applies to that record.  Each way, a base
  sentence answers `unknown` through the fork.  A fork that has written nothing mounts,
  and growth under a `summarized?` one is `accept-growth`'s."
  [overlay base meta-kv {:keys [watermark base-next own-next index-cleared? summarized?]}]
  (let [changed (changed-base-records base meta-kv)]
    (when (seq changed)
      (refuse-overlap! (str "the base records at " (count changed) " handle(s) the fork removed"
                            " or overrode are not the ones it removed or overrode")
                       changed watermark)))
  (cond
    summarized? nil
    watermark
    (when-let [grown (first-grown base watermark base-next)]
      (when (holds-state? overlay meta-kv index-cleared?)
        (let [shared (minted-shared base watermark base-next own-next)]
          (refuse-overlap! (str "it now holds handle " grown ", and held none at or above "
                                watermark " then"
                                (when (seq shared)
                                  (str ", including " (count shared)
                                       " of the handles the fork's own records use")))
                           shared watermark))))
    :else
    (let [shared (overridden-unlike overlay base)]
      (when (seq shared)
        (refuse-overlap! (str "it now holds other records at " (count shared)
                              " of the handles the fork's own records use")
                         shared nil)))))

(def ^:private follow-key
  "A catch-up whose index ops are being applied: `{:end :blocks :ops :arrivals}`."
  ::follow)

(defn- first-changed-block
  "The `[lo hi)` handles of the first block whose sum differs between the summaries
  `blocks` and `now`, both over the handles below `end`; nil when none does."
  [blocks now end]
  (when-let [b (first (filter #(not= (nth blocks %) (nth now %)) (range (count blocks))))]
    [(* (long b) summary-block) (min (long end) (* (inc (long b)) summary-block))]))

(defn- accept-growth
  "A durable fork's mount over its base, against the summary its index describes: the one
  a pending catch-up (`follow-key`) records, else the last recorded one.  Over a base
  holding a record at or above that summary's end, a fork holding state is refused when a
  block below the end differs or an arrival lies in a range the fork minted, and else
  gets `{:arrivals :end :blocks}`, which `begin-follow!` takes.  Otherwise the summary is
  recorded and the answer is nil."
  [overlay base meta-kv base-next index-cleared?]
  (let [pending (p/kv-get meta-kv follow-key)
        end     (or (:end pending) (p/kv-get meta-kv base-end-key))]
    (if (and end (first-grown base end base-next) (holds-state? overlay meta-kv index-cleared?))
      (let [{:keys [old-blocks arrivals] :as now} (base-summary base end)
            minted (cap/reserve-ranges nil (minted-ranges meta-kv))
            hit    (filterv #(not= (long %) (cap/skip-reserved minted %)) arrivals)]
        (when-let [[lo hi] (first-changed-block (or (:blocks pending) (p/kv-get meta-kv base-blocks-key))
                                                old-blocks end)]
          (refuse-overlap! (str "its records at handles " lo " to " (dec (long hi))
                                " are not the ones the fork was written over")
                           [] end))
        (when (seq hit)
          (refuse-overlap! (str "it gained records at " (count hit) " handle(s) this fork"
                                " minted; open the base with :fork-dirs naming the fork's"
                                " directory, so the records it gains take handles no fork holds")
                           hit end))
        (select-keys now [:arrivals :end :blocks]))
      (when-not pending
        (when (or (nil? end) (first-grown base end base-next))
          (record-summary! meta-kv (base-summary base nil)))
        nil))))

(defn follow-owed
  "`{:arrivals :end :blocks}` for the base records the fork `store`'s mount accepted and its
  index does not yet describe, or nil."
  [store]
  @(:follow store))

(defn pending-follow
  "The catch-up a mount of the fork `store` found unfinished, `{:end :blocks :ops :arrivals}`,
  or nil."
  [store]
  (p/kv-get (:meta-kv store) follow-key))

(defn begin-follow!
  "Record in the bookkeeping that the fork `store`'s index takes `ops` (`kv-batch` ops) to
  describe the base its mount accepted (`follow-owed`), before the ops are applied."
  [store ops]
  (p/kv-put (:meta-kv store) follow-key
            (assoc (select-keys (follow-owed store) [:end :blocks :arrivals]) :ops ops))
  (reset! (:follow store) nil))

(def ^:private firings-key
  "The arrivals of finished catch-ups whose rule firings the fork has not run."
  ::firings-owed)

(defn end-follow!
  "Record the summary of the pending catch-up as the one the fork `store`'s index describes,
  move its arrivals to the ones owing firings (`firings-owed`), and drop it."
  [store]
  (let [meta-kv (:meta-kv store)]
    (when-let [pending (p/kv-get meta-kv follow-key)]
      (record-summary! meta-kv pending)
      (p/kv-put meta-kv firings-key (into (or (p/kv-get meta-kv firings-key) []) (:arrivals pending)))
      (p/kv-delete meta-kv follow-key))))

(defn firings-owed
  "The base handles the fork `store`'s index took in whose rule firings have not run, or nil."
  [store]
  (p/kv-get (:meta-kv store) firings-key))

(defn firings-done!
  "Drop the fork `store`'s owed firings (`firings-owed`)."
  [store]
  (p/kv-delete (:meta-kv store) firings-key))

(defn overlay-record-store
  "Compose a writable `overlay` `RecordStore` over a read-only `base` one, with `meta-kv`
  holding the overlay's record-level bookkeeping.

  The mount reads the bookkeeping back, so a durable overlay remounted over the same base
  serves the merged contents it was left in.  It records the base's watermark, and a
  `durable?` fork the base's summary (`base-summary`), and refuses (`:fork-base-overlap`)
  a base changed since in a way the fork cannot follow (`check-base-overlap!`,
  `accept-growth`).  `index-cleared?` says the fork's own index half has been rebuilt
  (`reindex`), which is state the record half cannot see.  `base-opts` are the opts the
  base was opened from, or nil when it arrived as open stores; `rebase!` replaces a base
  that has them."
  ([overlay base meta-kv] (overlay-record-store overlay base meta-kv false nil false))
  ([overlay base meta-kv index-cleared?]
   (overlay-record-store overlay base meta-kv index-cleared? nil false))
  ([overlay base meta-kv index-cleared? base-opts durable?]
   (let [base-next (long (p/next-id base))         ; allocation, not mutation (see `frozen`)
         own-next  (long (p/next-id overlay))
         hidden?   (some? (p/kv-get meta-kv cleared-key))
         watermark (p/kv-get meta-kv watermark-key)]
     ;; a cleared fork reads nothing of its base, so no base handle can be shadowed
     (when-not hidden?
       (check-base-overlap! overlay base meta-kv {:watermark      watermark
                                                  :base-next      base-next
                                                  :own-next       own-next
                                                  :index-cleared? index-cleared?
                                                  :summarized?    (and durable?
                                                                       (some? (or (p/kv-get meta-kv follow-key)
                                                                                  (p/kv-get meta-kv base-end-key))))}))
     (p/kv-put meta-kv watermark-key base-next)
     (let [follow (when (and durable? (not hidden?))
                    (accept-growth overlay base meta-kv base-next index-cleared?))
           stored (minted-ranges meta-kv)
           minted (atom (cap/reserve-ranges nil stored))]
       (when-not hidden?
         (record-minted! meta-kv minted
                         [(if (seq stored)
                            [(second (peek stored)) own-next]
                            [(inc (long (or watermark own-next))) own-next])]))
       (map->OverlayRecordStore
        {:overlay        overlay
         :base           base
         :meta-kv        meta-kv
         :counter        (atom (max base-next own-next))
         :base-top       (atom base-next)
         :hidden?        (atom hidden?)
         :sx-tombstoned  (atom (set (p/kv-members meta-kv sx-tombstone-key)))
         :jd-tombstoned  (atom (set (p/kv-members meta-kv jd-tombstone-key)))
         :pv-tombstoned  (atom (set (p/kv-members meta-kv pv-tombstone-key)))
         :released       (atom (set (p/kv-members meta-kv released-key)))
         :minted         minted
         :session-lo     (atom (inc (max base-next own-next)))
         :durable?       durable?
         :base-opts      base-opts
         :rebase-lock    (ReentrantReadWriteLock.)
         :follow         (atom follow)})))))

(defn rebase!
  "Empty the fork `store`'s own records and bookkeeping, call `refill!`, which replaces the
  contents of the base's stores, and mount the emptied half over the new base, returning
  what `refill!` returns.  The handle counter and the watermark are seeded from the
  base's `next-id`, as a mount seeds them.  Every record, tombstone, released mark and
  base digest the fork held is dropped, so nothing written against the old base is read
  against the new one.  The base reads as hidden until `refill!` returns."
  [{:keys [overlay base meta-kv counter base-top hidden? minted session-lo durable?
           sx-tombstoned jd-tombstoned pv-tombstoned released follow]} refill!]
  (reset! hidden? true)
  (p/clear-records! overlay)
  (p/kv-clear! meta-kv)
  (reset! minted nil)
  (reset! follow nil)
  (run! #(reset! % #{}) [sx-tombstoned jd-tombstoned pv-tombstoned released])
  (let [r         (refill!)
        base-next (long (p/next-id base))
        own-next  (long (p/next-id overlay))]
    (p/kv-put meta-kv watermark-key base-next)
    (when durable? (record-summary! meta-kv (base-summary base nil)))
    (reset! base-top base-next)
    (reset! counter (max base-next own-next))
    (reset! session-lo (inc (max base-next own-next)))
    (reset! hidden? false)
    r))

(defn excluding-readers
  "Call `f` holding the write side of fork `store`'s rebase lock, and return what `f`
  returns.  Every public read holds the read side (`kb/reading`), so a read on another
  thread waits for `f` to return, and the calling thread's own reads re-enter."
  [{:keys [^ReentrantReadWriteLock rebase-lock]} f]
  (let [l (.writeLock rebase-lock)]
    (.lock l)
    (try (f) (finally (.unlock l)))))

(defn overlay-record-store?
  "Is `store` one of these — i.e. is it already a fork's record half?  Asked by
  `vaelii.impl.overlay.mount`, which refuses a base that is itself a fork."
  [store]
  (instance? OverlayRecordStore store))
