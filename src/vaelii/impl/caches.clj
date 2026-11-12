;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.caches
  "What this process holds beside the stores: one register every derived, droppable
  structure declares itself in at namespace load, and one read over it (`rows`). The
  register requires only `config` and the logger, so it has no require edge down to a
  namespace holding a cache. A row's `:scope` says what `:entries` counts and `:counters`
  says the same for `:hits` and `:misses`; a nil `:entries` marks a scope-bound cache that
  cannot be counted from outside. A read that throws is reported as a row carrying
  `:error`. See docs/caches.md."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.config :as config])
  (:import [com.sun.management GarbageCollectionNotificationInfo]
           [java.lang.management ManagementFactory GarbageCollectorMXBean MemoryNotificationInfo
            MemoryPoolMXBean MemoryType MemoryUsage]
           [java.util.concurrent.atomic AtomicLongArray]
           [javax.management NotificationEmitter NotificationListener Notification]
           [javax.management.openmbean CompositeData]))

;; ---- the bound every registered cache takes ------------------------------

(defn assoc-bounded
  "Store `v` at `k` in map `m`, clearing `m` wholesale when it already holds `limit` entries.
  The one bound policy of the plain-map caches; see docs/caches.md, \"The bound\"."
  [m limit k v]
  (assoc (if (>= (count m) limit) {} m) k v))

(defn read-through
  "The value at `k` in the map held by atom `cache`, else `(compute)` — stored under
  `assoc-bounded`'s bound, and returned.

  `find` rather than `get`, so a computed `nil` is a hit rather than a miss recomputed
  forever.  `compute` runs outside the `swap!` because it is the expensive half and a
  `swap!` retry must not run it twice: two callers racing one key both compute and both
  store, and the second store is a no-op — the trade a memo of derived values wants over
  holding a lock across the computation."
  [cache limit k compute]
  (if-let [hit (find @cache k)]
    (val hit)
    (let [v (compute)]
      (swap! cache assoc-bounded limit k v)
      v)))

(defn get-or!
  "The value at `k` in the map held by volatile `memo`, else `(f)`, stored and returned.
  A computed nil or false counts as a hit."
  [memo k f]
  (if-let [hit (find @memo k)]
    (val hit)
    (let [v (f)]
      (vswap! memo assoc k v)
      v)))

(def ^:dynamic *open-mark*
  "nil outside a second-route search.  Inside one (`exc/route-answer`), a fn of a thunk
  answering `[value settled?]`: the thunk's value, and false when its computation read a
  route question still open, which makes the value provisional."
  nil)

(defn held-if-settled
  "`(compute)`, handed to `put!` (which answers the value it holds) unless its computation
  read a route question still open (`*open-mark*`): a provisional value is answered and
  not held, so no entry depends on which question a read asked first."
  [compute put!]
  (if-let [mark *open-mark*]
    (let [[v settled?] (mark compute)] (if settled? (put! v) v))
    (put! (compute))))

;; ---- the tunable bound: an operator scale, a guard pressure, overrides --
;;
;; Every count-bounded cache reads its limit through `limit-of`, so the bound a store path
;; enforces and the bound `rows` reports are one number. At scale 1.0, pressure 1.0 and no
;; override `limit-of` returns the shipped default.

(def ^:private min-limit
  "The fewest entries a scaled bound is taken to, whatever the scale.  Below this a cache
  forces the recompute of almost every read it is asked, so a scale that would compute a
  smaller bound is read as this instead."
  16)

(defonce ^:private the-profile
  ;; {:scale double :pressure double :overrides {cache-id absolute-limit}}.  A `defonce` for
  ;; the registry's reason: reloading this namespace must not reset a scale an operator set.
  ;; `:scale` is the operator's intent, seeded from VAELII_CACHE_SCALE (`config/switches`
  ;; marks it `:load` — this read is its first, so a bad value refuses at the engine's load);
  ;; `:pressure` is the memory-pressure guard's own multiplier, 1.0 until the guard lowers it
  ;; under a heap it is about to run out of and restores it as the heap frees.
  (atom {:scale (config/cache-scale) :pressure 1.0 :overrides {}}))

(defn profile
  "The cache profile in force: `{:scale <operator multiplier> :pressure <guard multiplier>
  :overrides {cache-id limit}}`.  A cache's effective bound is its shipped default times
  `:scale` times `:pressure` (an override replaces the default but the two multipliers still
  apply, so the guard can shrink an overridden cache under memory pressure)."
  []
  @the-profile)

(defn limit-of
  "The bound cache `id` enforces now, given its shipped default `default`. An override is an
  absolute limit that replaces `default`; `:scale` leaves it alone and `:pressure` still
  multiplies it. A `default` with no override is multiplied by `:scale` and `:pressure`.
  The result is floored at `min-limit` and saturates at `Long/MAX_VALUE`. A nil `default`
  with no override stays nil. Read on a cache's store path and by its `rows` entry, so the
  bound enforced and the bound reported are one number."
  [id default]
  (let [{:keys [scale pressure overrides]} @the-profile
        p (double (or pressure 1.0))]
    (if-let [ov (get overrides id)]
      (if (== 1.0 p) (long ov) (max min-limit (Math/round (Math/ceil (* p (double ov))))))
      (when default
        (let [s (* (double scale) p)]
          (if (== 1.0 s) default
              (max min-limit (Math/round (Math/ceil (* s (double default)))))))))))

(defn limit-thunk
  "`#(limit-of id default)`, for a descriptor's `:limit`, so its `rows` entry reports the
  effective bound rather than the shipped default.  A `default` that is a var, such as
  `#'*a-dynamic-limit*`, is dereferenced on each call, so the row reads the current
  binding.  See `register-cache`."
  [id default]
  ;; the metadata is what `override-problem` reads: a descriptor whose bound comes through
  ;; here is one an override moves, and no other is
  (with-meta (fn [] (limit-of id (if (var? default) @default default))) {::profile-id id}))

(defn set-scale
  "Multiply every count-bounded cache's shipped limit by `x`, and return the profile.
  Reversible — `1.0` restores the shipped bounds — so bare, not `!`, as `set-solver` is:
  it installs a setting the next cache store reads, and no belief moves."
  [x]
  (swap! the-profile assoc :scale (double x))
  @the-profile)

(defn set-limit
  "Override cache `id`'s bound with `n` regardless of scale, or clear the override when `n`
  is nil, and return the profile.  A caller who names both a cache and a number has stated the bound it
  wants, so the scale does not then move it."
  [id n]
  (swap! the-profile update :overrides (fn [o] (if n (assoc o id (long n)) (dissoc o id))))
  @the-profile)

(defn reset-profile
  "Restore the configured profile — the `VAELII_CACHE_SCALE` scale, pressure 1.0 and no
  overrides — and return it."
  []
  (reset! the-profile {:scale (config/cache-scale) :pressure 1.0 :overrides {}})
  @the-profile)

;; `{cache-id descriptor}`.  A `defonce` because registration happens at namespace load
;; and reloading *this* namespace must not empty what the namespaces already loaded put
;; here; keyed by id, so reloading one of *them* replaces its own entry rather than
;; doubling it.
(defonce ^:private registry (atom {}))

(defn register-cache
  "Declare that this namespace holds a cache. Called at namespace load, once per cache. Bare,
  not `!`: it installs a descriptor the next load replaces. The descriptor
  (docs/caches.md, \"The register\"):

    :cache     keyword, unique across the process
    :label     display name
    :scope     :kb or :process, what `:entries` counts
    :unit      what one entry is
    :limit     entries held before a wholesale clear, nil for a cache bounded by something
               else (say what in `:note`); a thunk where the bound is a dynamic var or
               profile-scaled (`limit-thunk`)
    :counters  :kb, :process, or nil
    :note      one line: what it holds and what retires an entry
    :read      (fn [kb]) -> {:entries n :hits h :misses m}, a key absent where there is no
               number. O(1). A `:limit` it answers replaces the descriptor's in the row.
    :clear     (fn [kb]) -> entries dropped, or absent. Scoped to `kb`.
    :trim      (fn [kb target]) -> entries dropped, or absent: the partial drop the
               memory-pressure guard uses (`trim-map!` for a plain map)
    :reset-counters (fn [kb]) -> the counters as they stood, or absent"
  [{:keys [cache] :as descriptor}]
  (swap! registry assoc cache descriptor)
  cache)

(defn registered?
  "Is `id` a cache registered in *this* process now?  A membership test rather than a
  refusal, because the register fills lazily: a cache is registered when its namespace
  loads, and a qualitative calculus or the metric-time reasoner may not be loaded yet.  So
  `set-limit` reads this to *warn* on an id nothing has registered rather than to refuse
  it — a not-yet-loaded cache would take the override when it registers, where a refusal would
  reject the very configuration a bulk load sets up before touching the calculus."
  [id]
  (contains? @registry id))

(defn override-problem
  "Why an override cannot move registered cache `id`'s bound, as a phrase, or nil when it can.
  An override moves a bound exactly when the descriptor's `:limit` is the `limit-thunk` for
  `id`. A nil-bound cache and a bound outside the profile (the symbol pool's and the
  scoped-closure budget's dynamic vars) fail, and `set-cache-limit` refuses an override on
  either. Nil for an id nothing has registered (`registered?`)."
  [id]
  (when-let [d (get @registry id)]
    (let [limit (:limit d)]
      (cond
        (nil? limit)                            "not a count the cache profile holds"
        (= id (::profile-id (meta limit)))      nil
        :else                                   "a dynamic var outside the cache profile"))))

;; ---- the derived-state tallies ------------------------------------------
;;
;; A row filled at a read keeps its tally beside the structure holding its entries, so a
;; KB's tally counts that KB's reads alone and a structure made again counts from zero.
;; The comparison that finds a spurious miss runs only while `start-tally!` is on.

(defonce ^:private derived (atom {}))

(defonce ^:private tallying
  ;; nil, or an atom of the running instrument's state
  (atom nil))

(def tally-slots
  "The slots of a tally, in order.  `:retired` is filled by `start-tally!`, `:compared` and
  `:spurious` only while it runs, `:evicted` by a weighted LRU."
  [:hits :misses :recompute-ns :retired :compared :spurious :evicted])

(defn tally
  "A zeroed tally."
  ^AtomicLongArray []
  (AtomicLongArray. (count tally-slots)))

(defn tallied
  "`r`, a reference, answered with a fresh tally for each row id of `ids` in its metadata."
  [r ids]
  (alter-meta! r assoc ::tallies (zipmap ids (repeatedly tally)))
  r)

(defn tally-of
  "Row `id`'s tally held by `x`: a weighted LRU's own, or the one `tallied` put in `x`'s
  metadata; nil when `x` holds none."
  ^AtomicLongArray [x id]
  (if (and (map? x) (not (sorted? x)) (:tally x))
    (:tally x)
    (get (::tallies (meta x)) id)))

(defn hit
  "Count a hit on tally `t`, when there is one."
  [^AtomicLongArray t]
  (when t (.incrementAndGet t 0))
  nil)

(defn missed
  "Count a miss on tally `t`, when there is one, whose recompute started at `start`
  (`System/nanoTime`)."
  [^AtomicLongArray t ^long start]
  (when t
    (.incrementAndGet t 1)
    (.addAndGet t 2 (- (System/nanoTime) start)))
  nil)

(defn spent
  "Add the time since `start` (`System/nanoTime`) to tally `t`'s recompute time, for a
  miss counted already whose recompute ended later."
  [^AtomicLongArray t ^long start]
  (when t (.addAndGet t 2 (- (System/nanoTime) start)))
  nil)

(defn miss
  "Count a miss on tally `t`, when there is one, whose time `spent` adds."
  [^AtomicLongArray t]
  (when t (.incrementAndGet t 1))
  nil)

(defmacro recomputed
  "`body`'s value, counted on tally `t` as a miss with the time `body` took."
  [t & body]
  `(let [t# ~t, s# (System/nanoTime), v# (do ~@body)]
     (missed t# s#)
     v#))

(defn tally-map
  "Tally `t` as `{slot n}`, or nil for no tally."
  [^AtomicLongArray t]
  (when t
    (into {} (map-indexed (fn [i k] [k (.get t (int i))])) tally-slots)))

(defn- reset-tally
  "Zero tally `t` and answer what it held."
  [^AtomicLongArray t]
  (let [m (tally-map t)]
    (dotimes [i (count tally-slots)] (.set t i 0))
    m))

(defn value-at
  "The value at `[field & keys]` in `kb`'s `Reasoning` value: the field's atom
  dereferenced, then `keys` followed into it."
  [kb [field & path]]
  (let [x (get @(:reasoning kb) field)]
    (get-in (if (instance? clojure.lang.IDeref x) @x x) path)))

(defn row-tally
  "Row `id`'s tally in `kb`, or nil: held by the structure at the row's first `:at`
  location, else by that location's `Reasoning` field.  A row held by the process rather
  than by a KB has none, since its tally would count every KB's reads."
  ^AtomicLongArray [kb id]
  (when-let [[field & path :as at] (first (:at (get @derived id)))]
    (when kb
      (or (when path (tally-of (value-at kb at) id))
          (tally-of (get @(:reasoning kb) field) id)))))

(defn- hit-rate
  "Hits over lookups, or nil when nothing has been counted.  Nil rather than zero for an
  untouched cache: a rate of 0.0 is indistinguishable from a cache that is missing everything."
  [hits misses]
  (when (and hits misses)
    (let [total (+ (long hits) (long misses))]
      (when (pos? total) (/ (double hits) (double total))))))

(defn- bound
  "A descriptor's `:limit`, called where it is a thunk over a dynamic var."
  [limit]
  (if (fn? limit) (limit) limit))

(defn- failed
  "What a row says when its own read threw.  A cache that cannot answer is reported as
  one that cannot answer, and never as a cache that is empty: this register is open —
  any namespace may put a descriptor in it — and a page whose worth is highest while
  something is already wrong must not be the thing that fails."
  [^Throwable t]
  (let [m (.getMessage t)]
    (str (.getSimpleName (class t)) (when (seq m) (str ": " m)))))

(defn rows
  "Every registered cache, read against `kb`, ranked by entries descending with ties on the
  cache's name; a row that cannot be counted sorts last. A row is the descriptor's static
  half (`:cache :label :scope :unit :limit :counters :note`) plus what its `:read` answered,
  `:hit-rate` and `:clearable?`; the function slots are dropped. A read that throws costs
  its own row, which carries `:error`. A cache a derived-state row counts (`row-tally`)
  reports that row's tally: `:hits` and `:misses` where its `:read` gives none,
  `:recompute-ns`, `:retired`, `:compared`, `:spurious`, `:evicted`, with `:counters :kb`."
  [kb]
  (let [row-of (into {} (keep (fn [[id d]] (when (:cache d) [(:cache d) id]))) @derived)]
    (->> (vals @registry)
         (mapv (fn [{:keys [cache read clear] :as d}]
                 (let [{:keys [entries hits misses error] :as r}
                       (try (read kb) (catch Throwable t {:error (failed t)}))
                       counts (try (some-> (row-of cache) (->> (row-tally kb)) tally-map)
                                   (catch Throwable _ nil))
                       hits   (if (contains? r :hits) hits (:hits counts))
                       misses (if (contains? r :misses) misses (:misses counts))]
                   (-> (dissoc d :read :clear :reset-counters :trim)
                       (merge (dissoc counts :hits :misses) (dissoc r :entries :hits :misses :error))
                       (assoc :entries    entries
                              :hits       hits
                              :misses     misses
                              :hit-rate   (hit-rate hits misses)
                              :clearable? (some? clear)
                              :limit      (if (contains? r :limit)
                                            (:limit r)
                                            (try (bound (:limit d))
                                                 (catch Throwable _ nil))))
                       (cond-> (and counts (nil? (:counters d))) (assoc :counters :kb))
                       (cond-> error (assoc :error error))))))
         (sort-by (juxt #(- (long (or (:entries %) -1))) #(name (:cache %))))
         vec)))

(defn clear-caches
  "Drop every cache that offers a clear: `{:cleared [{:cache :label :entries} …] :entries
  total}`, ranked like `rows`. Bare, not `!`: every entry is derived and no belief moves.
  Scoped to `kb`. `{:counters? true}` also zeroes the process-wide hit and miss counters
  and `kb`'s derived-state tallies (`row-tally`); the answer then carries `:counters-reset`
  and `:tallies-reset` (`[{:row id …what it held}]`). A cache with no `:clear` is not in the
  answer. A clear that throws gives its row `:error` and an entry count of zero."
  ([kb] (clear-caches kb nil))
  ([kb {:keys [counters?]}]
   (let [cleared (->> (vals @registry)
                      (filter :clear)
                      (mapv (fn [{:keys [cache label clear]}]
                              (try {:cache cache :label label
                                    :entries (long (or (clear kb) 0))}
                                   (catch Throwable t
                                     {:cache cache :label label :entries 0
                                      :error (failed t)}))))
                      (sort-by (juxt #(- (long (:entries %))) #(name (:cache %))))
                      vec)
         reset   (when counters?
                   (->> (vals @registry)
                        (filter :reset-counters)
                        (mapv (fn [{:keys [cache label reset-counters]}]
                                (try (merge {:cache cache :label label}
                                            (reset-counters kb))
                                     (catch Throwable t
                                       {:cache cache :label label :error (failed t)}))))
                        (sort-by #(name (:cache %)))
                        vec))]
     (cond-> {:cleared cleared
              :entries (reduce + 0 (map :entries cleared))}
       counters? (assoc :counters-reset reset
                        :tallies-reset (vec (for [id (sort (keys @derived))
                                                  :let [t (row-tally kb id)]
                                                  :when t]
                                              (assoc (reset-tally t) :row id))))))))

;; ---- partial trim: freeing memory without discarding the warm half ------

(defn trim-map!
  "Drop entries from the plain map held by atom `a` until it holds at most `target`, keeping
  the `target` that iteration reaches first, and answer how many went.  The kept set is
  arbitrary rather than the most recent — a plain map records no recency — which is the trade
  against a wholesale clear: half the entries survive a trim where none survive a clear, so
  the reads they serve are not all recomputed at once.  A cache whose entries carry recency
  or a different shape supplies its own `:trim` rather than calling this."
  [a ^long target]
  (let [before (count @a)]
    (when (> before target)
      (swap! a (fn [m] (if (> (count m) target) (into (empty m) (take target) m) m))))
    (max 0 (- before (count @a)))))

;; ---- the weighted LRU: a bound on what is held, evicting the coldest ----
;;
;; A cache whose entries differ in size by orders of magnitude bounds the **sum** of their
;; weights: an access-ordered map, a running weight, and eviction from the cold end until
;; the weight is under the bound.

(defn weighted-lru
  "An empty weighted LRU.  `limit` is a thunk answering the most weight it holds — a
  `limit-thunk`, so the profile's scale and the memory guard's pressure move it — and
  `weigh` answers an entry's weight from its value.  Read and written through `lru-get`
  and `lru-put!`; an access-ordered map reorders on a read, so every operation holds its
  monitor, uncontended on a single writer."
  [limit weigh]
  {:map (java.util.LinkedHashMap. 16 0.75 true) :weight (long-array 1)
   :limit limit :weigh weigh :tally (tally)})

(defn- evict-to!
  "Drop entries from the cold end of `lru` until its weight is at most `target`, count them
  on its tally, and answer how many went.  Called under the map's monitor."
  [{:keys [^java.util.LinkedHashMap map ^longs weight weigh ^AtomicLongArray tally]} ^long target]
  (let [it (.iterator (.entrySet map))
        n  (loop [n 0]
             (if (and (> (aget weight 0) target) (.hasNext it))
               (let [^java.util.Map$Entry e (.next it)]
                 (aset weight 0 (- (aget weight 0) (long (weigh (.getValue e)))))
                 (.remove it)
                 (recur (inc n)))
               n))]
    (when (and tally (pos? (long n))) (.addAndGet tally 6 n))
    n))

(defn lru-get
  "The value `lru` holds at `k`, or nil, marking it the most recently used; a hit or a
  miss on its tally."
  [{:keys [^java.util.LinkedHashMap map tally]} k]
  (let [v (locking map (.get map k))]
    (if (some? v) (hit tally) (miss tally))
    v))

(defn lru-peek
  "The value `lru` holds at `k`, or nil, marking it the most recently used and leaving
  the tally unchanged: for a reader that never computes the value on a miss."
  [{:keys [^java.util.LinkedHashMap map]} k]
  (locking map (.get map k)))

(defn lru-put!
  "Hold `v` at `k` in `lru`, evicting the least recently used entries until the weight is
  back under the bound, and answer `v`.  A value heavier than the whole bound is evicted
  by its own insertion: answered, and not held."
  [{:keys [^java.util.LinkedHashMap map ^longs weight weigh limit] :as lru} k v]
  (locking map
    (when-some [old (.put map k v)]
      (aset weight 0 (- (aget weight 0) (long (weigh old)))))
    (aset weight 0 (+ (aget weight 0) (long (weigh v))))
    (evict-to! lru (long (limit))))
  v)

(defn lru-trim!
  "Evict from the cold end of `lru` until it weighs at most `target`; answer how many
  entries went.  The weighted cache's `:trim`: the recent half survives a trim."
  [{:keys [map] :as lru} target]
  (locking map (evict-to! lru (long target))))

(defn lru-evict-if!
  "Drop every entry of `lru` whose key both `pick?` and `drop?` hold of, and answer how many
  went.  `pick?` runs under the map's monitor and must not read `lru`; `drop?` runs over
  the keys `pick?` kept, outside it, so it may."
  [{:keys [^java.util.LinkedHashMap map ^longs weight weigh]} pick? drop?]
  (let [ks (filterv drop? (locking map (into [] (filter pick?) (.keySet map))))]
    (locking map
      (reduce (fn [n k]
                (if-some [v (.remove map k)]
                  (do (aset weight 0 (- (aget weight 0) (long (weigh v)))) (inc n))
                  n))
              0 ks))))

(defn lru-evict!
  "Drop the entries of `lru` at the keys `ks`, and answer how many went."
  [{:keys [^java.util.LinkedHashMap map ^longs weight weigh]} ks]
  (locking map
    (reduce (fn [n k]
              (if-some [v (.remove map k)]
                (do (aset weight 0 (- (aget weight 0) (long (weigh v)))) (inc n))
                n))
            0 ks)))

(defn lru-clear!
  "Empty `lru`, and answer how many entries went."
  [{:keys [^java.util.LinkedHashMap map ^longs weight]}]
  (locking map
    (let [n (.size map)]
      (.clear map)
      (aset weight 0 0)
      n)))

(defn lru-weight
  "What `lru` holds, in its weight's unit."
  ^long [{:keys [map ^longs weight]}]
  (locking map (aget weight 0)))

(defn lru-size
  "How many entries `lru` holds."
  ^long [{:keys [^java.util.LinkedHashMap map]}]
  (locking map (.size map)))

;; ---- the memory-pressure guard ------------------------------------------
;;
;; A post-collection listener moves the profile's `:pressure` between `pressure-low` and
;; `pressure-high` and trims the caches partially (`trim-map!`, or a cache's own `:trim`).
;; The host installs it; the disk hot-record cache stays on `vaelii.disk.cache`. The heap
;; mark (`arm-heap-mark!`) is separate. See docs/caches.md, "The memory-pressure guard".

(def ^:private pressure-high
  "The old-generation fraction, measured after a collection, over which the guard shrinks.
  0.85 rather than higher because a shrink is worth making only while there is still headroom
  to collect into."
  0.85)

(def ^:private pressure-low
  "The fraction under which the guard grows the caches back — held well below `pressure-high`
  so a reading bouncing around one mark does not shrink and grow on alternate collections."
  0.60)

(def ^:private pressure-critical
  "The fraction over which a chaining run refuses to go on (`heap-critical?`).  0.92 leaves
  the rest of the old generation for the rollback the refusal runs."
  0.92)

(defonce ^:private critical
  ;; whether a collection left the old generation over `pressure-critical`, as the guard's
  ;; listener or the heap mark's threshold notification read it
  (volatile! false))

(def ^:private pressure-shrink-factor 0.5)
(def ^:private pressure-grow-factor 1.5)

(def ^:private pressure-min
  "The least the guard drives pressure to, so a heap under sustained pressure keeps a
  fraction of each cache rather than running every read cold."
  0.125)

(defn pressure-response
  "What a post-collection old-generation `frac` (used over max) asks of the caches at the
  current `pressure`: `:shrink` over `pressure-high`, `:grow` under `pressure-low` while
  pressure is still below the operator's ceiling of 1.0, else `:hold`.  A pure function of
  the two readings, so the decision is tested without a heap that is actually full."
  [^double frac ^double pressure]
  (cond
    (>= frac pressure-high)                       :shrink
    (and (<= frac pressure-low) (< pressure 1.0)) :grow
    :else                                         :hold))

(defonce ^:private guard
  ;; {:installed? bool :emitters [NotificationEmitter…] :listener NotificationListener
  ;;  :kbs (fn [] <seq of live KB records>)}.  A defonce so a namespace reload does not
  ;; strand a listener still attached to the JVM's collectors.
  (atom {:installed? false :emitters nil :listener nil :kbs (constantly nil)}))

(defonce ^:private guard-lifecycle
  ;; The monitor `install-memory-guard!` and `uninstall-memory-guard!` run under, so two
  ;; host starts at once cannot both find the guard uninstalled and arm two listeners.
  (Object.))

(defn- set-pressure!
  "Set the guard's pressure multiplier, clamped to [pressure-min 1.0], and answer it."
  [^double p]
  (let [p' (-> p (max pressure-min) (min 1.0))]
    (swap! the-profile assoc :pressure p')
    p'))

(defn- trim-to-bounds!
  "Trim every cache that offers a `:trim` down to its current effective limit — a process
  cache once, a KB-scoped one for each live KB in `kbs` — and answer how many entries went.
  A trim that throws costs its own cache and no other, the way a read or a clear does, and
  is logged at `:warn`."
  [kbs]
  (reduce
   (fn [total {:keys [cache scope trim] :as d}]
     (let [target (long (or (bound (:limit d)) 0))
           one    (fn [kb]
                    (long (or (try (trim kb target)
                                   (catch Throwable t
                                     (trove/log! {:level :warn :id ::trim-failed :error t
                                                  :msg (str "trimming cache " cache " to "
                                                            target " failed: " (ex-message t))})
                                     0))
                              0)))]
       (+ total (if (= :process scope) (one nil) (reduce + 0 (map one (seq kbs)))))))
   0
   (filter :trim (vals @registry))))

(defn shrink!
  "Lower pressure one step and trim the caches to the new, lower bound; answer
  `{:pressure p :dropped n}`.  Public so the guard's response can be driven in a test without
  a heap that is actually full."
  [kbs]
  (let [p (set-pressure! (* (double (:pressure @the-profile)) pressure-shrink-factor))]
    {:pressure p :dropped (trim-to-bounds! kbs)}))

(defn grow!
  "Raise pressure one step back toward the operator's scale, and answer the new pressure.  No
  trim: growing a bound drops nothing, it only lets the next store hold more."
  []
  (set-pressure! (* (double (:pressure @the-profile)) pressure-grow-factor)))

(defn- old-gen-name?
  "Does pool name `nm` name an old generation?  The old generation is the heap pool whose
  filling precedes an out-of-memory; among the pools a collector names, the one matched by
  this name with a positive `getMax` and the largest `getMax` is the tenured space on every
  collector the JVM ships a generational heap for.  A non-generational collector (Shenandoah,
  Epsilon, ZGC before JDK 21's generational mode) names no such pool."
  [nm]
  (boolean (re-find #"(?i)old|tenured" (str nm))))

(defn- old-gen-fraction
  "The fraction of the old generation left in use after a collection, read from a GC
  notification's after-collection usage map, or nil when no pool there is a collected old
  generation (`old-gen-name?`); the guard then holds pressure."
  [^java.util.Map after]
  (let [cands (for [^java.util.Map$Entry e (.entrySet after)
                    :let [^MemoryUsage u (.getValue e)]
                    :when (and u (pos? (.getMax u)) (old-gen-name? (.getKey e)))]
                [(.getMax u) (/ (double (.getUsed u)) (double (.getMax u)))])]
    (when (seq cands) (second (apply max-key first cands)))))

;; ---- the heap mark ------------------------------------------------------

(defonce ^:private heap-mark
  ;; nil until `arm-heap-mark!` first runs, then `{:pool MemoryPoolMXBean-or-nil :max
  ;; bytes}`.  A defonce so a namespace reload neither re-arms the JVM-wide threshold nor
  ;; strands the listener attached to the memory bean.
  (atom nil))

(defn- old-gen-pool
  "The `MemoryPoolMXBean` the guard's `old-gen-fraction` reads, when it supports a
  collection-usage threshold, or nil."
  ^MemoryPoolMXBean []
  (let [cands (for [^MemoryPoolMXBean p (ManagementFactory/getMemoryPoolMXBeans)
                    :let [mx (.getMax (.getUsage p))]
                    :when (and (= MemoryType/HEAP (.getType p)) (pos? mx)
                               (old-gen-name? (.getName p))
                               (.isCollectionUsageThresholdSupported p))]
                [mx p])]
    (when (seq cands) (second (apply max-key first cands)))))

(defn- armed-pool-name
  "The name of the pool the heap mark armed, or nil."
  []
  (when-let [^MemoryPoolMXBean pool (:pool @heap-mark)] (.getName pool)))

(defn- on-threshold
  "The heap mark listener's body: a `MEMORY_COLLECTION_THRESHOLD_EXCEEDED` notification
  for `pool-name`, the armed pool, sets `critical`.  Lifted out of the listener so a test
  drives it without filling the heap."
  [notif-type pool-name]
  (when (and (= MemoryNotificationInfo/MEMORY_COLLECTION_THRESHOLD_EXCEEDED notif-type)
             (some-> (armed-pool-name) (= pool-name)))
    (vreset! critical true)))

(defn- pool-fraction
  "The lower of the armed pool's usage after its last collection and its usage now, as a
  fraction of its max, or nil when the pool reports no collection usage.  The usage now
  is under the collection usage once a young collection reclaims a dead humongous object
  G1 counted in the old pool at its last concurrent cycle."
  [^MemoryPoolMXBean pool max-bytes]
  (when-let [u (.getCollectionUsage pool)]
    (/ (double (min (.getUsed u) (.getUsed (.getUsage pool)))) (double max-bytes))))

(defn arm-heap-mark!
  "Set the old generation's collection-usage threshold at `pressure-critical` and attach a
  listener that sets `heap-critical?` when a collection leaves the pool over it; answer the
  armed pool's name, or nil. `kb/open-kb` calls it unless `vaelii.heap.mark` is off. Arms
  once per JVM and is never disarmed; a collector with no old-generation pool arms nothing.
  `!` because it sets a JVM-wide threshold. See docs/caches.md, \"The heap mark\"."
  []
  (locking guard-lifecycle
    (when-not @heap-mark
      (reset! heap-mark {:pool nil :max 0})
      (try
        (when-let [pool (old-gen-pool)]
          (let [mx (.getMax (.getUsage pool))]
            (.setCollectionUsageThreshold pool (long (* (double pressure-critical) (double mx))))
            (.addNotificationListener
             ^NotificationEmitter (ManagementFactory/getMemoryMXBean)
             (reify NotificationListener
               (handleNotification [_ notif _]
                 (let [ud (.getUserData ^Notification notif)]
                   (when (instance? CompositeData ud)
                     (on-threshold (.getType ^Notification notif)
                                   (.getPoolName (MemoryNotificationInfo/from ^CompositeData ud)))))))
             nil nil)
            (reset! heap-mark {:pool pool :max mx})))
        (catch Throwable t
          (trove/log! {:level :warn :id ::heap-mark-failed :error t
                       :msg (str "arming the heap mark failed, so a chaining run will not"
                                 " refuse over a nearly full heap: " (ex-message t))})))))
  (armed-pool-name))

(defn heap-critical?
  "Did the last collection read leave the old generation over `pressure-critical`?  Set by
  the heap mark's threshold notification and by the memory guard's listener; false when
  neither is armed (docs/caches.md, \"The heap mark\").

  One volatile read while the flag is clear.  While it is set, the call reads the armed
  pool (`pool-fraction`) and clears the flag when the reading is under the mark, under the
  guard as without it.  The guard sets the flag from a young collection's after-usage,
  which counts dead tenured objects, so the pool's own reading decides."
  []
  (boolean
   (and @critical
        (let [{:keys [pool] mx :max} @heap-mark]
          (or (nil? pool)
              (let [f (pool-fraction pool mx)]
                (if (and f (< (double f) (double pressure-critical)))
                  (vreset! critical false)
                  true)))))))

(defn- on-collection
  "Respond to one collection whose after-usage map is `after`: read the old-generation
  fraction and shrink, grow, or hold.  The listener's body, lifted out so a test drives it
  with a usage map rather than a real collection."
  [after]
  (when-let [frac (old-gen-fraction after)]
    (vreset! critical (>= (double frac) pressure-critical))
    (case (pressure-response frac (double (:pressure @the-profile)))
      :shrink (shrink! ((:kbs @guard)))
      :grow   (grow!)
      :hold   nil)))

(defn memory-guard
  "Whether the guard is attached to the collectors, the pressure it currently holds, and the
  pool the heap mark armed: `{:installed? bool :pressure p :heap-mark pool-name-or-nil}`.
  Pressure below 1.0 says the guard has shrunk the caches under a heap it is watching fill."
  []
  {:installed? (:installed? @guard) :pressure (:pressure @the-profile)
   :heap-mark  (armed-pool-name)})

(defn install-memory-guard!
  "Attach a post-collection listener that moves the cache profile's `:pressure` with how full
  the old generation is: over `pressure-high` it shrinks the caches, under `pressure-low` it
  grows them back. `:kbs` is a thunk answering the live KB records whose per-KB caches the
  trim reaches. Idempotent: a second call replaces the `:kbs` thunk and arms no second
  listener (`guard-lifecycle`). A JVM whose collectors emit no such notification keeps
  pressure at 1.0. `!` because it attaches to the process's collectors;
  `uninstall-memory-guard!` detaches."
  [{:keys [kbs]}]
  (locking guard-lifecycle
    (swap! guard assoc :kbs (or kbs (constantly nil)))
    (when-not (:installed? @guard)
      (try
        (let [listener (reify NotificationListener
                         (handleNotification [_ notif _]
                           (when (= GarbageCollectionNotificationInfo/GARBAGE_COLLECTION_NOTIFICATION
                                    (.getType ^Notification notif))
                             (let [info  (GarbageCollectionNotificationInfo/from
                                          ^CompositeData (.getUserData ^Notification notif))
                                   after (.getMemoryUsageAfterGc (.getGcInfo info))]
                               (on-collection after)))))
              emitters (for [^GarbageCollectorMXBean b (ManagementFactory/getGarbageCollectorMXBeans)
                             :when (instance? NotificationEmitter b)]
                         (doto ^NotificationEmitter b (.addNotificationListener listener nil nil)))]
          (swap! guard assoc :installed? true :listener listener :emitters (vec emitters)))
        (catch Throwable _ (swap! guard assoc :installed? false)))))
  (memory-guard))

(defn uninstall-memory-guard!
  "Detach the guard's listener from every collector it armed and restore pressure to 1.0;
  answer the guard state.  Safe when nothing is installed."
  []
  (locking guard-lifecycle
    (let [{:keys [emitters listener]} @guard]
      (doseq [^NotificationEmitter e emitters]
        (try (.removeNotificationListener e ^NotificationListener listener) (catch Throwable _ nil))))
    (set-pressure! 1.0)
    (swap! guard assoc :installed? false :emitters nil :listener nil))
  (memory-guard))

;; ---- the derived-state register -----------------------------------------
;;
;; A cache row above states a bound.  A derived-state row states a dependency: what the
;; structure is keyed by, what it is computed from, and which write event retires it at
;; which granularity.  Every structure the engine keeps between writes, or across one pass,
;; has a row, whether or not it is a cache `clear-caches` may drop (docs/caches.md, "The
;; derived-state register").

(def events
  "The closed set of write events that move derived state, `{event {:n n :at [var-symbol
  …] :names what-the-event-names}}`.  `:n` numbers the event in the generated table, and
  `:at` names the vars the event passes through, each called through its var, so a test
  can wrap them (`derived_state_test`)."
  {:stored          {:n 1  :names "handle, sentence, context"
                     :at '[vaelii.impl.kb/create-sentex]}
   :integrated      {:n 2  :names "handle, functor"
                     :at '[vaelii.impl.special/integrate-sentex
                           vaelii.impl.special/derived-sentex-added
                           vaelii.impl.special/integrate-twin]}
   :removed         {:n 3  :names "record, except target"
                     :at '[vaelii.impl.integrate/sentex-removed!]}
   :respelled       {:n 4  :names "old and new sentex, one handle"
                     :at '[vaelii.impl.kb/respell-sentex!]}
   :relabelled      {:n 5  :names "the handles of the region, held in the network"
                     :at '[vaelii.impl.jtms/supersede vaelii.impl.jtms/ensure-node
                           vaelii.impl.jtms/add-premise vaelii.impl.jtms/suspend-premise
                           vaelii.impl.jtms/add-justification
                           vaelii.impl.jtms/restrength-informant vaelii.impl.jtms/set-forced
                           vaelii.impl.jtms/relabel vaelii.impl.jtms/set-blocked
                           vaelii.impl.jtms/retract! vaelii.impl.jtms/sweep!
                           vaelii.impl.jtms/drop-justification!]}
   :held            {:n 6  :names "hold token"
                     :at '[vaelii.impl.settle/hold-belief! vaelii.impl.settle/publish-belief!]}
   :edge            {:n 7  :names "handle, edge, context"
                     :at '[vaelii.impl.taxonomy/add-genl vaelii.impl.taxonomy/del-genl!
                           vaelii.impl.taxonomy/add-genlCx vaelii.impl.taxonomy/del-genlCx!]}
   :edge-belief     {:n 8  :names "moved handles, or nil for all"
                     :at '[vaelii.impl.special/reconcile-belief-change
                           vaelii.impl.taxonomy/refresh-beliefs]}
   :declared        {:n 9  :names "handle, [kind key], context"
                     :at '[vaelii.impl.taxonomy/add-supported
                           vaelii.impl.taxonomy/del-supported!]}
   :forced-monotonic {:n 10 :names "predicate"
                      :at '[vaelii.impl.checks/force-reach!]}
   :equality        {:n 11 :names "handle, pair"
                     :at '[vaelii.impl.taxonomy/add-equality vaelii.impl.taxonomy/del-equality!]}
   :except          {:n 12 :names "except, target, context"
                     :at '[vaelii.impl.special/recheck-except]}
   :rule-indexed    {:n 13 :names "rule, antecedent predicates, context"
                     :at '[vaelii.impl.special/index-rule-sentex]}
   :recheck         {:n 14 :names "rules; a trigger, :all or :all-rejoin"
                     :at '[vaelii.impl.special/mark-recheck]}
   :inherited       {:n 15 :names "clash rows"
                     :at '[vaelii.impl.decide.inherited/install-inherited!
                           vaelii.impl.decide.inherited/update-inherited!]}
   :settle-exit     {:n 16 :names "region"
                     :at '[vaelii.impl.settle/settle-finish]}
   :recover         {:n 17 :names "the whole store"
                     :at '[vaelii.impl.recovery/recover-from-records
                           vaelii.impl.recovery/install-rebuilt!]}
   :image-install   {:n 18 :names "the image"
                     :at '[vaelii.impl.reasoning-image/install-from!]}
   :cleared         {:n 19 :names "the stores, wiped"
                     :at '[vaelii.core/clear! vaelii.impl.reindex/reindex
                           vaelii.impl.io.import/clearing-on-refusal]}
   :closed          {:n 20 :names "the KB"
                     :at '[vaelii.core/close!]}
   :caches-cleared  {:n 21 :names "the KB, or every live KB"
                     :at '[vaelii.impl.caches/clear-caches vaelii.impl.caches/shrink!]}
   :settle-pass     {:n 22 :names "the region, the queues a pass drains"
                     :at '[vaelii.impl.settle/pass-work vaelii.impl.settle/apply-pass!]}})

(defn on-every
  "`{event code}` for every event in `events`: the `:retired-by` of a row any write
  retires, such as one keyed by the change clock."
  [code]
  (into {} (map (fn [e] [e code])) (keys events)))

(def codes
  "How an event retires a row's entries, the values of a row's `:retired-by`."
  {:K  "per key: the write names the entries it moves"
   :S  "per key part: the write moves one part of a composite key"
   :G  "generation: a counter bump retires every entry keyed on it"
   :G* "the change clock, which any write in any KB bumps"
   :I  "identity: compared with `identical?` against a value the write replaces"
   :W  "wholesale clear"
   :Q  "take-and-empty: the consumer drains the queue"
   :C  "content-keyed: never stale"
   :P  "pass-scoped: garbage when the scope returns"
   :R  "rebuilt whole"})

(def kinds
  "What a row is: `:cache` (droppable without moving a belief), `:index` (kept at the
  write, rebuilt only by recover), `:journal`, `:queue`, `:counter`, `:pass`."
  #{:cache :index :journal :queue :counter :pass})

(def ^:private keyed-by-values
  #{:handle :functor :type :context :reader :node :term :literal :value :global})

(def ^:private computed-values #{:write :settle :read :pass})

(def ^:private imaged-values
  "`:state` and `:cache` name the image's two atom sections, `:taxonomy` and `:network`
  its taxonomy and network sections; false is a row the image leaves as the open made it."
  #{:state :cache :taxonomy :network false})

(def stores
  "The ids a row's `:reads` may name beside other rows' ids."
  #{:records :index :justifications :source})

(defn- refuse-descriptor
  [id why]
  (throw (IllegalArgumentException. (str "derived-state row " id ": " why))))

(defn- check-descriptor
  "`d`, or a throw naming the first slot outside its closed set."
  [{:keys [id label kind holds-content? keyed-by reads retired-by computed imaged? at value
           covered-by]
    :as d}]
  (cond
    (not (keyword? id))                     (refuse-descriptor id "no keyword :id")
    (not (string? label))                   (refuse-descriptor id "no :label")
    (not (kinds kind))                      (refuse-descriptor id (str "kind " kind))
    (not (boolean? holds-content?))         (refuse-descriptor id "no boolean :holds-content?")
    (not (keyed-by-values keyed-by))        (refuse-descriptor id (str "keyed-by " keyed-by))
    (not (computed-values computed))        (refuse-descriptor id (str "computed " computed))
    (not (contains? imaged-values imaged?)) (refuse-descriptor id (str "imaged? " imaged?))
    (not (and (vector? reads) (every? keyword? reads)))
    (refuse-descriptor id "reads is not a vector of ids")
    (not (and (map? retired-by) (every? events (keys retired-by))
              (every? codes (vals retired-by))))
    (refuse-descriptor id (str "retired-by " retired-by))
    (not (or (= :pass kind) value (seq at)))
    (refuse-descriptor id "neither :at nor :value, so nothing can read it")
    (not (or (nil? covered-by)
             (and (map? covered-by) (every? #{:perf :perf-ab} (keys covered-by))
                  (every? #(and (vector? %) (every? keyword? %)) (vals covered-by)))))
    (refuse-descriptor id (str "covered-by " covered-by))
    :else d))

(defn register-derived
  "Declare a row of derived state. Called at namespace load, once per row; the loading
  namespace is recorded as its `:owner`. The descriptor (docs/caches.md, \"The derived-state
  register\"):

    :id :label     the row's id and name
    :kind          one of `kinds`
    :holds-content? true when an entry holds a sentence the KB holds or would hold that no
                   store holds; `lein lint`'s `derived` check fails such a row unless its
                   allowlist names it
    :keyed-by      what an entry is keyed by
    :reads         ids of the rows and `stores` it is computed from
    :retired-by    `{event code}`: each event in `events` that retires entries, and how
    :computed      :write, :settle, :read or :pass
    :imaged?       which section of a reasoning image carries it, or false
    :at            its locations, each `[reasoning-field & keys]`; a reader symbol in a key
                   is written `::caches/reader`
    :var :cache    the var holding it; the `register-cache` id it is also registered under
    :bound         its bound as a phrase, where `:cache` gives none
    :value         `(fn [kb])` -> its current value, where `:at` does not reach it
    :covered-by    `{:perf [check …] :perf-ab [probe …]}` that fail when a recompute at the
                   read replaces the row; the `derived` check requires it of the files it lists
    :live          `(fn [kb])` -> how many entries are current, for a row whose retired entries
                   stay held until a read; `start-tally!` counts a retirement as a fall in it
    :note          one line"
  [descriptor]
  (let [d (check-descriptor descriptor)]
    (swap! derived assoc (:id d) (assoc d :owner (str (ns-name *ns*))))
    (:id d)))

(defn derived-value
  "Row `id`'s current value in `kb`: its `:value` called on `kb`, else the values at its
  `:at` locations.  Nil for a row that cannot be read from outside its pass."
  [kb id]
  (when-let [{:keys [value at]} (get @derived id)]
    (cond value     (value kb)
          (next at) (mapv #(value-at kb %) at)
          (seq at)  (value-at kb (first at))
          :else     nil)))

(defn image-fields
  "The `Reasoning` fields a row imaged as `section` (`:state` or `:cache`) is located in
  by its first `:at` location, sorted."
  [section]
  (into (sorted-set) (for [d (vals @derived) :when (= section (:imaged? d))
                           [field] (:at d)]
                       field)))

(defn- row-order
  "Sort key for a row's name: its letter group in the order `S T M J N X W D Q R K`, then
  its number.  The name is content: a row's id is the name the register gives it."
  [row-name]
  (let [[_ g n] (re-matches #"([A-Z]+)(\d+)" (name row-name))]
    [(if g (.indexOf "STMJNXWDQRK" ^String g) 99)
     (or (some-> n parse-long) 0) (name row-name)]))

(defn derived-state
  "The register as data: `{:rows [row …] :events [event …] :edges [[reader read] …]}`.
  A row is its descriptor less `:value`, ordered by id.  With `kb`, a row that is a
  registered cache also carries that cache's `:entries`."
  ([] (derived-state nil))
  ([kb]
   (let [caches (when kb (into {} (map (juxt :cache identity)) (rows kb)))
         st     (when kb (some-> @tallying deref))
         st     (when (identical? (:reasoning kb) (:reasoning (:kb st))) st)
         rows'  (->> (sort-by (comp row-order key) @derived)
                     (map #(cond-> (dissoc (val %) :value :live)
                             (:var (val %)) (update :var str)
                             (and kb (:cache (val %)))
                             (assoc :entries (:entries (caches (:cache (val %)))))
                             kb (assoc :tally (tally-map (row-tally kb (key %))))))
                     vec)]
     {:rows   rows'
      :events (->> events
                   (map (fn [[k v]]
                          (cond-> (assoc v :event k)
                            st (assoc :fired (get-in st [:fired k] 0)
                                      :retired (into (sorted-map)
                                                     (keep (fn [[[e r] n]] (when (= e k) [r n])))
                                                     (:retired st))))))
                   (sort-by :n) vec)
      :edges  (vec (for [r rows' x (:reads r)] [(:id r) x]))})))

(defn tally-ranking
  "The rows of `kb` that hold a tally, ranked for the consolidation plan, as `{:by-spurious-cost
  [row …] :by-hit-rate [row …]}`.  A row is `{:row :recompute-ns :hit-rate
  :spurious-fraction :spurious-cost}`: `:spurious-fraction` is `:spurious` over `:compared`,
  nil when nothing was compared, and `:spurious-cost` is `:recompute-ns` times it.
  `:by-spurious-cost` is descending, a row with no fraction last; `:by-hit-rate` is
  ascending, a row with no lookup last.  Ties are broken on the row's name."
  [kb]
  (let [rows (for [id (keys @derived)
                   :let [{:keys [hits misses recompute-ns compared spurious]}
                         (tally-map (row-tally kb id))]
                   :when recompute-ns]
               (let [frac (when (pos? (long compared)) (/ (double spurious) (double compared)))]
                 {:row               id
                  :recompute-ns      recompute-ns
                  :hit-rate          (hit-rate hits misses)
                  :spurious-fraction frac
                  :spurious-cost     (when frac (* frac (double recompute-ns)))}))
        by   (fn [k sign] (sort-by (juxt #(if (k %) 0 1) #(* sign (double (or (k %) 0))) #(name (:row %)))
                                   rows))]
    {:by-spurious-cost (vec (by :spurious-cost -1.0))
     :by-hit-rate      (vec (by :hit-rate 1.0))}))

;; ---- the event instrument ------------------------------------------------
;;
;; `start-tally!` wraps every var `events` names, reads every row of one KB at each
;; wrapped call's entry and exit, and charges the entries a row retired between two reads
;; to the innermost event open then.  It costs a read of every row per event, so it runs
;; only when asked; `derived_state_test` checks each row's `:retired-by` with it.

(def ^:private retired-values-limit
  "The most retired values one tally keeps for `compare-retired` while the instrument runs."
  65536)

(defn tallying?
  "Is the instrument running, so that a miss compares what it recomputed?"
  []
  (some? @tallying))

(defn compared
  "While the instrument runs, count on tally `t` a miss compared with the value it
  replaced, and a spurious one when `same?`."
  [^AtomicLongArray t same?]
  (when (and t @tallying)
    (.incrementAndGet t 4)
    (when same? (.incrementAndGet t 5)))
  nil)

(defn compare-retired
  "While the instrument runs, compare `v`, recomputed at key `k` of the row whose tally is
  `t`, with an earlier value there (`compared`).  `under` nil compares with the entry an
  event retired at `k`, which the instrument keeps, and takes it: for a row whose entry is
  the value read.  A non-nil `under` compares with the last value computed at `k` when
  that was computed under another value of `under`, and keeps `v` under `under` in its
  place: for a row whose entries are keyed by such a value.  A value is kept as its hash
  and compared by it, so the instrument holds no closure the cache itself has evicted."
  [^AtomicLongArray t k under v]
  (when-let [st (and t @tallying)]
    (let [^java.util.Map g (:retired-values @st)]
      (locking g
        (let [m (or (.get g t) (let [m (java.util.HashMap.)] (.put g t m) m))
              [s0 h0 :as e] (.get ^java.util.Map m k)
              h (hash v)]
          (cond
            (nil? under) (when e (.remove ^java.util.Map m k) (compared t (= h0 h)))
            :else        (do (when (and s0 (not= s0 under)) (compared t (= h0 h)))
                             (when (>= (.size ^java.util.Map m) retired-values-limit)
                               (.clear ^java.util.Map m))
                             (.put ^java.util.Map m k [under h])))))))
  nil)

(defn retired-entries
  "The `[key value]` entries `before` held that `after` drops or replaces: a map's by key,
  a set's members, a vector of locations' per location, else `[[nil before]]` when the
  two differ.  A nil `before` held no entry, so a structure made where none was retires
  nothing."
  [before after]
  (cond
    (identical? before after)        nil
    (nil? before)                    nil
    (and (map? before) (map? after)) (into [] (remove (fn [[k x]]
                                                        ;; a sorted map refuses a key it
                                                        ;; cannot compare, which it holds none of
                                                        (let [e (try (find after k)
                                                                     (catch ClassCastException _ nil))]
                                                          (and e (= x (val e))))))
                                           before)
    (and (set? before) (set? after)) (into [] (comp (remove #(contains? after %))
                                                    (map (fn [x] [x x])))
                                           before)
    (and (vector? before) (vector? after) (= (count before) (count after)))
    (into [] cat (map retired-entries before after))
    (= before after)                 nil
    :else                            [[nil before]]))

(defn- read-rows
  [kb rows]
  (into {} (map (fn [{:keys [id]}]
                  [id (try (derived-value kb id)
                           (catch Throwable t [::unreadable (.getMessage t)]))]))
        rows))

(defn- live-counts
  "`{id n}`: `:live` of each row of `rows` holding one that `event` retires."
  [kb rows event]
  (into {} (for [{:keys [id live retired-by]} rows
                 :when (and live (contains? retired-by event))]
             [id (try (long (live kb)) (catch Throwable _ 0))])))

(defn- charge!
  "Charge `n` entries of row `id` to `event`, and keep the values `kvs` for
  `compare-retired`."
  [st kb id event n kvs]
  (when (pos? (long n))
    (swap! st update-in [:retired [event id]] (fnil + 0) n)
    (when-let [^AtomicLongArray t (row-tally kb id)]
      (.addAndGet t 3 (long n))
      (when (seq kvs)
        (let [^java.util.Map g (:retired-values @st)]
          (locking g
            (let [^java.util.Map m (or (.get g t) (let [m (java.util.HashMap.)] (.put g t m) m))]
              (when (> (+ (.size m) (count kvs)) retired-values-limit) (.clear m))
              (doseq [[k v] kvs] (.put m k [nil (hash v)])))))))))

(defn- moved?
  "Did row `d` move from `before` to `after`?  A cache or a queue moves when an entry is
  retired, any other row when its value changes."
  [{:keys [kind]} before after]
  (if (#{:cache :queue} kind)
    (boolean (seq (retired-entries before after)))
    (not= before after)))

(defn- checkpoint!
  "Read every row of `st`'s KB.  A row that moved since the last read has its retired
  entries charged to the innermost open event, and is handed to `:observe` with the events
  it is charged to: the innermost, and for a row filled at a read or a move outside every
  event, the events since that row last moved.  A row with `:live` is charged the fall in
  it, at an `event` entering or leaving that retires it."
  [st event]
  (locking st
    (when-let [kb (:kb @st)]
      (let [{:keys [rows diffed last stack pending observe live]} @st
            now  (read-rows kb diffed)
            top  (peek stack)
            lv   (when event (live-counts kb rows event))]
        (doseq [{:keys [id computed] :as d} diffed
                :when (and (contains? last id) (moved? d (last id) (now id)))]
          (let [lazy?   (or (empty? stack) (#{:read :pass} computed))
                charged (cond-> (if lazy? (get pending id #{}) #{})
                          top (conj top))]
            (when (and top (not (:live d)))
              (let [kvs (retired-entries (last id) (now id))]
                (charge! st kb id top (count kvs) (when (= :cache (:kind d)) kvs))))
            (when observe (observe d charged))
            (swap! st assoc-in [:pending id] #{})))
        (doseq [[id n] lv
                :let [was (get live id)]
                :when (and was top (> (long was) (long n)))]
          (charge! st kb id top (- (long was) (long n)) nil))
        (swap! st (fn [s] (-> s (assoc :last now) (update :live merge lv))))))))

(defn- enter!
  [st event]
  (swap! st (fn [s] (-> s
                        (update :stack conj event)
                        (update-in [:fired event] (fnil inc 0))
                        (update :pending (fn [p] (reduce #(update %1 (:id %2) (fnil conj #{}) event)
                                                         p (:rows s))))))))

(defn- wrap
  "Event `event`'s var value `f`, wrapped: a read of every row before and after, unless the
  call is a self-call of the event already open."
  [st event f]
  (fn [& args]
    (if (= event (peek (:stack @st)))
      (apply f args)
      (do (when (and (nil? (:kb @st)) (some-> (first args) :reasoning))
            (swap! st assoc :kb (first args) :last (read-rows (first args) (:diffed @st))))
          (checkpoint! st event)
          (enter! st event)
          (try (apply f args)
               (finally (checkpoint! st event)
                        (swap! st update :stack pop)))))))

(defn- event-vars
  "`[event var]` for every var `events` names whose namespace is loaded, among the events
  `only` names (every event for nil): an event of a namespace this process never loaded
  cannot fire."
  [only]
  (for [[event {:keys [at]}] events
        :when (or (nil? only) (contains? only event))
        sym at
        :let [v (find-var sym)]
        :when v]
    [event v]))

(defn start-tally!
  "Run the event instrument over `kb`, or over the first KB an event is handed when `kb` is
  nil, until `stop-tally!`.  Every var `events` names is wrapped process-wide; one
  instrument runs at a time, and a second start refuses.  Each event's firings, and the
  entries it retired of each row, are counted: in `derived-state`'s `:events` while it
  runs, and in each row's tally (`:retired`).  A miss compares what it recomputed while
  it runs (`compare-retired`).

  `opts`: `:rows`, the row ids to read (default every row not of kind `:pass`), for a KB
  whose rows are too large to read at every event; `:observe`, `(fn [row charged])`
  called for each row that moved with the set of events it is charged to.  Without
  `:observe`, a row with `:live` is counted by it alone and its value is not read.
  `:events`, the event ids to wrap (default every one): each wrapped call reads the rows
  twice, so a KB whose write fires an event a million times leaves that event out."
  ([kb] (start-tally! kb nil))
  ([kb {:keys [rows observe events]}]
   (let [rs (vec (filter #(and (not= :pass (:kind %)) (or (nil? rows) (contains? (set rows) (:id %))))
                         (map (fn [[id d]] (assoc d :id id)) @derived)))
         df (if observe rs (vec (remove :live rs)))
         st (atom {:kb kb :rows rs :diffed df :last (when kb (read-rows kb df)) :live {} :stack []
                   :pending {} :fired {} :retired {} :observe observe
                   :retired-values (java.util.HashMap.)})
         vs (vec (event-vars (some-> events set)))]
     (when-not (compare-and-set! tallying nil st)
       (throw (IllegalStateException. "the derived-state instrument is already running")))
     (swap! st assoc :originals (mapv (fn [[_ v]] [v @v]) vs))
     (doseq [[event v] vs] (alter-var-root v #(wrap st event %)))
     nil)))

(defn stop-tally!
  "Stop the instrument and restore every var it wrapped; answer `{:kb :fired {event n}
  :retired {[event row] n}}`, or nil when none runs."
  []
  (when-let [st @tallying]
    (doseq [[v f] (:originals @st)] (alter-var-root v (constantly f)))
    (reset! tallying nil)
    (checkpoint! st nil)
    (select-keys @st [:kb :fired :retired])))

(defn with-tally
  "`(f)` run under the instrument over `kb` (`start-tally!` with `opts`); answers what
  `stop-tally!` answers."
  [kb opts f]
  (let [out (volatile! nil)]
    (start-tally! kb opts)
    (try (f) (finally (vreset! out (stop-tally!))))
    @out))
