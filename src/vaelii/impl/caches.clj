;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.caches
  "What this process is holding beside the stores — one register every derived,
  droppable structure declares itself in, and one read over the lot.

  The stores are measured elsewhere: `catalog/heap` reports the JVM's own figure and
  `catalog/footprint` estimates what a loaded KB costs.  Neither says anything about the
  **caches** — the atoms and plain maps holding answers the engine would otherwise
  recompute — and a hit rate is the only evidence a cost model has.  \"The
  second query was fast\" is a demo; \"the second query was fast because it was served
  from a cache, and here is the rate\" is a measurement.

  **A register rather than a dozen accessors.**  This namespace requires only `config`, a
  leaf that holds no cache, so the reader still has no require edge down to a namespace
  holding one: every such namespace requires *this* one and declares itself at load, and
  there is no list here that a new cache has to be added to twice.  The `config` edge reads
  one switch, `VAELII_CACHE_SCALE`, and `limit-of` applies it to every count-bounded
  cache's limit.  A cache in a namespace this
  process never loaded — a qualitative calculus nobody registered, the metric-time
  reasoner — is absent from the read because it is absent from the process, which is the
  honest answer rather than a row of zeroes.

  **Two scopes, and never one wearing the other's clothes.**  `:scope` says what a row's
  `:entries` counts: `:kb` for a cache hanging off a KB record, `:process` for a static
  one every KB in the JVM shares.  `:counters` says the same about `:hits` / `:misses`,
  separately, because the literal cache is exactly the awkward case — its entries are
  per-KB and its counters are global `AtomicLong`s, \"since they measure the mechanism
  rather than a store\" (`literal-cache/stats`).  Rendering that as one per-KB row would
  attribute another KB's hits to this one.  The closure neighbours are awkward the other
  way round — process counters over entries only a live search step can count — which is
  the same argument for keeping the two fields apart.

  **`:unit` is not decoration.**  One cache counts literals, another counts networks, a
  third counts symbols, and a column of bare integers compares none of them.

  A row whose `:entries` is nil is one that cannot be counted from outside — the
  scope-bound caches, bound for the length of one chaining run or one search step and
  garbage when it returns.  They are registered all the same, with the reason in
  `:note`, so the list is complete rather than merely finite.

  **A row answers for itself, and fails for itself.**  The register is open, so a read
  here runs code this namespace has never seen; one that throws is reported as a row
  carrying `:error` rather than allowed to take the answer down with it.  A diagnostic
  is worth most while something is already wrong, which is exactly when it must not be
  the next thing to break."
  (:require [vaelii.impl.config :as config])
  (:import [com.sun.management GarbageCollectionNotificationInfo]
           [java.lang.management ManagementFactory GarbageCollectorMXBean MemoryUsage]
           [javax.management NotificationEmitter NotificationListener Notification]
           [javax.management.openmbean CompositeData]))

;; ---- the bound every registered cache takes ------------------------------

(defn assoc-bounded
  "Store `v` at `k` in map `m`, **clearing `m` wholesale** when it already holds `limit`
  entries.

  The bound policy, in one place rather than spelled out at each cache.  Wholesale
  clearing rather than eviction is `literal-cache/cache-limit`'s argument and
  `observe/resident-limit`'s before it: evicting exactly the right entry costs more
  bookkeeping than the entry saved, and a cache that has grown past its bound is one
  whose queries have moved on.  That is a judgement about every cache here at once, so
  it is worth being able to revisit in one edit rather than six."
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

;; ---- the tunable bound: an operator scale, a guard pressure, overrides --
;;
;; Every count-bounded cache reads its limit through `limit-of`, so the operator's profile
;; and the memory-pressure guard move numbers that both the store path that enforces the
;; bound and the `rows` entry that reports it read.  At the default profile — scale 1.0,
;; pressure 1.0 and no override — `limit-of` returns the shipped default unchanged, so the
;; process holds the bounds it held before a scale existed, and the goldens and cost budgets
;; are unmoved.

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
  apply, so the guard can shrink a pinned cache under memory pressure)."
  []
  @the-profile)

(defn limit-of
  "The bound cache `id` enforces now, given its shipped default `default`.  An override names
  an absolute limit and replaces `default`: the operator's `:scale` leaves it alone, but the
  guard's `:pressure` still multiplies it, so a filling heap shrinks a pinned cache like every
  other.  A `default` with no override is multiplied by both `:scale` and `:pressure`.  Either
  result is floored at `min-limit` and saturates at `Long/MAX_VALUE`: `set-cache-scale`
  takes any number 0 or more, `##Inf` included, and a product past the range of a long
  is a bound no cache reaches rather than a throw on every store.  A nil `default` with no
  override — a cache bounded by something other than a count — stays nil, since no
  multiplier acts on it.

  Read on a cache's store path and by its `rows` entry, so the bound enforced and the bound
  reported are one number.  At scale 1.0 and pressure 1.0 with no override the shipped
  `default` is returned as it stands."
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
  effective bound rather than the shipped default.  See `register-cache`."
  [id default]
  (fn [] (limit-of id default)))

(defn set-scale
  "Multiply every count-bounded cache's shipped limit by `x`, and return the profile.
  Reversible — `1.0` restores the shipped bounds — so bare, not `!`, as `set-solver` is:
  it installs a setting the next cache store reads, and no belief moves."
  [x]
  (swap! the-profile assoc :scale (double x))
  @the-profile)

(defn set-limit
  "Pin cache `id`'s bound to `n` regardless of scale, or clear the pin when `n` is nil, and
  return the profile.  A caller who names both a cache and a number has stated the bound it
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
  "Declare that this namespace holds a cache.  Called at namespace load, once per cache.
  Bare, not `!`: it installs a descriptor the next load replaces, the way `set-solver`
  installs a setting.

  The descriptor:

    :cache     a keyword naming it, unique across the process
    :label     what to call it on screen
    :scope     :kb or :process — what `:entries` counts
    :unit      what one entry *is*, since entries mix units across caches
    :limit     entries held before it is cleared wholesale, or nil for a cache
               bounded by something other than a count (say what, in `:note`).
               **A thunk where the bound is a dynamic var or profile-scaled** —
               `limit-thunk` builds the profile-scaled one; see below
    :counters  :kb, :process, or nil when nothing counts hits and misses
    :note      one line: what it holds, and what retires an entry
    :read      (fn [kb]) -> {:entries n :hits h :misses m}, any key absent where
               there is no number.  **O(1)** — this runs on a page that polls.
               A nil `:entries` says the cache cannot be counted from here.
    :clear     (fn [kb]) -> entries dropped, or absent when nothing drops it by hand.
               **Scoped to `kb`.**  A clear that reached past its argument would make
               `clear-caches` a process-wide control wearing a per-KB signature
    :trim      (fn [kb target]) -> entries dropped, or absent.  The **partial** drop the
               memory-pressure guard uses: bring the cache down to `target` entries while
               keeping the rest, where `:clear` drops everything.  A `:process` cache
               ignores `kb`; `trim-map!` is the plain-map one, the LRU trims by recency
    :reset-counters (fn [kb]) -> the counters as they stood, or absent.  Only a cache
               whose `:counters` are `:process` has one, and it is separate from `:clear`
               precisely because it is wider than `kb`

  `:read`, `:clear` and `:reset-counters` all take the KB even when the cache is
  process-wide, so a caller needs no second calling convention for the static ones; they
  ignore it.

  **`:limit` takes a thunk for the same reason `:read` is a function.**  A descriptor is
  built once, at namespace load, so a constant captured into it is that constant forever
  — which is right for a `def` and wrong for a `^:dynamic` var, since being rebindable is
  the only reason such a var is dynamic.  Reporting the root bound while the engine
  enforces a bound somebody rebound would misreport the one field a reader uses to judge
  whether a cache is about to flush.  Write `:limit (fn [] *the-var*)` and the row reads
  it where it is read."
  [{:keys [cache] :as descriptor}]
  (swap! registry assoc cache descriptor)
  cache)

(defn registered?
  "Is `id` a cache registered in *this* process now?  A membership test rather than a
  refusal, because the register fills lazily: a cache is registered when its namespace
  loads, and a qualitative calculus or the metric-time reasoner may not be loaded yet.  So
  `set-limit` reads this to *warn* on an id nothing has registered rather than to refuse
  it — a not-yet-loaded cache would take the pin when it registers, where a refusal would
  reject the very configuration a bulk load sets up before touching the calculus."
  [id]
  (contains? @registry id))

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
  "Every registered cache, read against `kb`, ranked by entries.

  A row is the descriptor's static half — `:cache :label :scope :unit :limit :counters
  :note` — plus whatever its `:read` answered, plus `:hit-rate` and `:clearable?`.  No
  row walks the KB: each is a count off a map the engine is already holding, which is
  what makes this pollable.

  **A row is data all the way down.**  The descriptor's three function slots — `:read`,
  `:clear`, `:reset-counters` — are dropped, and what a caller needs of the last two is
  the `:clearable?` flag and the `:counters` scope beside it.  This is a public read
  (`vaelii.core/caches`), served over RPC and rendered on a page, so a function left in a
  row is a value neither can carry.

  **A read that throws costs its own row and no other**, and the row carries `:error`
  saying what went wrong.  One broken descriptor taking the whole answer down would fail
  the read exactly when the process is in the state it exists to describe.

  Ranked by entries **descending, ties broken on the cache's own name**, so the order is
  a function of the content and two processes holding the same caches list them the
  same way.  A row that cannot be counted sorts last, since a nil is not a small number."
  [kb]
  (->> (vals @registry)
       (mapv (fn [{:keys [read clear] :as d}]
               (let [{:keys [entries hits misses error]}
                     (try (read kb) (catch Throwable t {:error (failed t)}))]
                 (-> (dissoc d :read :clear :reset-counters :trim)
                     (assoc :entries    entries
                            :hits       hits
                            :misses     misses
                            :hit-rate   (hit-rate hits misses)
                            :clearable? (some? clear)
                            :limit      (try (bound (:limit d))
                                             (catch Throwable _ nil)))
                     (cond-> error (assoc :error error))))))
       (sort-by (juxt #(- (long (or (:entries %) -1))) #(name (:cache %))))
       vec))

(defn clear-caches
  "Drop every cache that offers a clear, and say what went: `{:cleared [{:cache :label
  :entries} …] :entries total}`, ranked like `rows`.

  Not `!`, and the reason is the whole point of the control: every entry is derived, the
  next read recomputes it, and no belief moves.  That makes a clear a measuring
  instrument rather than an edit — clear, ask the same question again, and watch the
  miss the second ask no longer gets to skip.

  **Scoped to `kb`, because the argument says so.**  Every `:clear` drops that cache's
  entries *for this KB* and nothing else.  The hit and miss counters some caches keep are
  process-wide — they measure the mechanism rather than a store — and zeroing one would
  reset a rate every other KB in the JVM is reporting, mid-measurement.  So it is not
  done here: `{:counters? true}` asks for it, in a call that says out loud it is reaching
  past its argument, and the answer then carries `:counters-reset` naming the caches it
  touched.  A function whose signature names one KB must not quietly be a per-process
  control; `caches`' `:counters` column is how a caller knows which rows the option is
  about.

  A cache with no `:clear` is left alone and is not in the answer.  Those are the
  structural ones — the symbol pool, the compiled relation algebras — where dropping the
  entries costs the sharing they exist for and buys no measurement.

  A clear that throws costs its own entry and no other, the way a read does: its row
  carries `:error` and an entry count of zero."
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
       counters? (assoc :counters-reset reset)))))

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
      (swap! a (fn [m] (if (> (count m) target) (into {} (take target) m) m))))
    (max 0 (- before (count @a)))))

;; ---- the memory-pressure guard ------------------------------------------
;;
;; A post-collection listener reads how full the old generation is after each garbage
;; collection and moves the profile's `:pressure` between two marks: over `pressure-high` it
;; halves pressure and trims the caches to the new, lower bound, so the next collection has
;; something to reclaim; under `pressure-low` it raises pressure back toward the operator's
;; scale, so a transient spike does not leave the caches small for the life of the process.
;; The trim is partial (`trim-map!`, or a cache's own shape-aware `:trim`), not a wholesale
;; clear, so the work behind the surviving half is not thrown away and recomputed the moment
;; pressure passes.  The host installs the listener (it holds the roster of live KBs the trim
;; needs); nothing attaches it at engine load, so a library embedding pays for no listener it
;; did not ask for.  The pure-heap caches are the guard's charge; the disk hot-record cache
;; stays on its own `vaelii.disk.cache` cap, since its records are re-thawable from disk and
;; its bound is set at store open.

(def ^:private pressure-high
  "The old-generation fraction, measured after a collection, over which the guard shrinks.
  0.85 rather than higher because a shrink is worth making only while there is still headroom
  to collect into."
  0.85)

(def ^:private pressure-low
  "The fraction under which the guard grows the caches back — held well below `pressure-high`
  so a reading bouncing around one mark does not shrink and grow on alternate collections."
  0.60)

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

(defn- set-pressure!
  "Set the guard's pressure multiplier, clamped to [pressure-min 1.0], and answer it."
  [^double p]
  (let [p' (-> p (max pressure-min) (min 1.0))]
    (swap! the-profile assoc :pressure p')
    p'))

(defn- trim-to-bounds!
  "Trim every cache that offers a `:trim` down to its current effective limit — a process
  cache once, a KB-scoped one for each live KB in `kbs` — and answer how many entries went.
  A trim that throws costs its own cache and no other, the way a read or a clear does."
  [kbs]
  (reduce
   (fn [total {:keys [scope trim] :as d}]
     (let [target (long (or (bound (:limit d)) 0))
           one    (fn [kb] (long (or (try (trim kb target) (catch Throwable _ 0)) 0)))]
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

(defn- old-gen-fraction
  "The fraction of the old generation left in use after a collection, read from a GC
  notification's after-collection usage map, or nil when no pool there is a collected old
  generation.  The old generation is the heap pool whose filling precedes an out-of-memory;
  among the pools a collector names, the one matched by name with a positive `getMax` and the
  largest `getMax` is the tenured space on every collector the JVM ships a generational heap
  for.  A non-generational collector names no such pool, and the guard then holds pressure."
  [^java.util.Map after]
  (let [cands (for [^java.util.Map$Entry e (.entrySet after)
                    :let [^MemoryUsage u (.getValue e)
                          nm (str (.getKey e))]
                    :when (and u (pos? (.getMax u)) (re-find #"(?i)old|tenured" nm))]
                [(.getMax u) (/ (double (.getUsed u)) (double (.getMax u)))])]
    (when (seq cands) (second (apply max-key first cands)))))

(defn- on-collection
  "Respond to one collection whose after-usage map is `after`: read the old-generation
  fraction and shrink, grow, or hold.  The listener's body, lifted out so a test drives it
  with a usage map rather than a real collection."
  [after]
  (when-let [frac (old-gen-fraction after)]
    (case (pressure-response frac (double (:pressure @the-profile)))
      :shrink (shrink! ((:kbs @guard)))
      :grow   (grow!)
      :hold   nil)))

(defn memory-guard
  "Whether the guard is attached to the collectors, and the pressure it currently holds:
  `{:installed? bool :pressure p}`.  Pressure below 1.0 says the guard has shrunk the caches
  under a heap it is watching fill."
  []
  {:installed? (:installed? @guard) :pressure (:pressure @the-profile)})

(defn install-memory-guard!
  "Attach a post-collection listener to the JVM's garbage collectors that moves the cache
  profile's `:pressure` with how full the old generation is: over `pressure-high` it shrinks
  the caches so the next collection reclaims, under `pressure-low` it grows them back.

  `:kbs` is a thunk answering the live KB records whose per-KB caches the trim reaches — the
  host supplies it from its catalog, since the engine holds no roster of open KBs.

  Attached by the servers and by nothing at engine load, so a library embedding pays for no
  listener it did not ask for.  Idempotent: a second call replaces the `:kbs` thunk and arms
  no second listener.  A JVM whose collectors emit no such notification keeps pressure at 1.0
  — the guard is a best-effort relief, not a guarantee.  `!` because it attaches to the
  process's collectors; `uninstall-memory-guard!` detaches."
  [{:keys [kbs]}]
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
      (catch Throwable _ (swap! guard assoc :installed? false))))
  (memory-guard))

(defn uninstall-memory-guard!
  "Detach the guard's listener from every collector it armed and restore pressure to 1.0;
  answer the guard state.  Safe when nothing is installed."
  []
  (let [{:keys [emitters listener]} @guard]
    (doseq [^NotificationEmitter e emitters]
      (try (.removeNotificationListener e ^NotificationListener listener) (catch Throwable _ nil))))
  (set-pressure! 1.0)
  (swap! guard assoc :installed? false :emitters nil :listener nil)
  (memory-guard))
