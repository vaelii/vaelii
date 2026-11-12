;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.observe
  "The leaf extension point the engine's mutation choke points notify without a require
  cycle. Two independent things ride on it: named observers of the stored fact set, and one
  counter saying that something changed.

  Observers: the incremental rule-matcher (`vaelii.impl.rete`) keeps RAM alpha memories that
  mirror the stored fact set. `kb/create-sentex` (add) and `integrate/sentex-removed!` (remove)
  sit below `rete`, so they call the atoms here and `rete` installs itself into them when
  engaged. When nothing is engaged the atoms hold nil and `notify-*` is a deref and a `nil?`
  check. The observer is global, not per-KB; the installed functions dispatch on `kb`.

  The change clock (`note-change`) is the coarse counter a cache keys on, and the resident
  caches it serves (`cached`) declare themselves to `vaelii.impl.caches` at the bottom of
  this file. See docs/inference.md."
  (:refer-clojure :exclude [])
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.util.concurrent.atomic AtomicLong AtomicReference]))

(defonce ^{:private true
           :doc "A `(fn [kb sentex handle])` run after a sentex is stored + indexed, or nil."}
  on-add
  (atom nil))

(defonce ^{:private true
           :doc "A `(fn [kb sentex])` run as a sentex leaves the store, or nil."}
  on-remove
  (atom nil))

(defn install!
  "Register the add/remove observers (called by `rete` when it engages).

  Two atoms written in two steps, which is sound because both ends of the pair belong to
  the writer: `rete/engage!` and `rete/disengage!` are the only callers, and the only
  readers are `notify-add` / `notify-remove` at the store's own choke points and the
  `installed?` check those two callers branch on — all of them on the writing thread, under the
  single-writer contract (docs/storage.md).  Nothing beside the writer can land between
  the two."
  [add-fn remove-fn]
  (reset! on-add add-fn)
  (reset! on-remove remove-fn))

(defn uninstall!
  "Clear the observers, so the store choke points go back to doing nothing extra.
  `install!`'s pair, written in two steps for `install!`'s reason."
  []
  (reset! on-add nil)
  (reset! on-remove nil))

(defn installed?
  "Is any observer currently engaged?"
  []
  (boolean (or @on-add @on-remove)))

(defn notify-add
  "A sentex `sentex` (handle `h`) just landed in `kb`'s store.  Cheap no-op when
  nothing is engaged."
  [kb sentex h]
  (when-let [f @on-add] (f kb sentex h)))

(defn notify-remove
  "A sentex `sentex` is leaving `kb`'s store.  Cheap no-op when nothing is engaged."
  [kb sentex]
  (when-let [f @on-remove] (f kb sentex)))

(def ^:dynamic *chain-fast-paths*
  "One switch over the placement-path fast paths forward chaining leans on — the
  justification dedup index (`jtms/*dedup-cache*`), the `ensure-node` no-op skip, and
  the single-context placement answer (`taxonomy/maximal-common-descendant-contexts`).
  Each computes exactly what its reference path computes, so — like
  `res/*arg-root-retrieval*` — this is a pure cost decision that must never change
  the answer set.  Bind it **false** to run the reference paths, which is what
  `chain_fast_paths_test` compares against, and what `vaelii.bench.pyramid`'s `-ref`
  modes measure.  On by default."
  true)

;; ---- the change clock ----------------------------------------------------

(defonce ^{:private true
           :tag AtomicLong
           :doc "A monotone counter bumped by every mutation that could move what a derived,
  resident structure computes.  An `AtomicLong` rather than an atom: the engine is
  single-writer, so this is an increment, not a compare-and-swap — and it sits on every
  mutating `jtms` entry point, so it has to added no work at all."}
  clock
  (AtomicLong. 0))

(defn note-change
  "Something a resident derived structure is a function of has changed. Three places bump
  it: the two store choke points (`kb/create-sentex`, `integrate/sentex-removed!`), every
  mutating `jtms` entry point (before and after, `jtms/moving`), and a watch on the
  taxonomy's atom. `core/clear!` and `reindex/reindex` bump by hand. Global and coarse: it
  says only that something moved, so a reader keyed on it re-derives more often than it must
  and never less. Bare, not `!`: it destroys nothing."
  []
  (.incrementAndGet clock))

(def ^:dynamic *fired-sink*
  "Nil, or a `java.util.Set` that `jtms/add-justification` adds the consequence of each
  rule firing's justification to (an integer informant, the rule's handle).
  `core/undoing-refusal` binds it while `assert-entry/*write-check*` is bound."
  nil)

(def ^:dynamic *route-gain-sink*
  "Nil, or `{:mirrors? m :note f}`: `jtms/add-justification` and `jtms/add-premise` call `f`
  with each datum of a network `m` holds of that is believed and gains a route, a
  justification or a premise mark it did not hold.  A write binds `special/route-gain-sink`'s."
  nil)

;; ---- the write record -------------------------------------------------------------
;;
;; A write that owes a report records, at each choke point, what the structure it moves
;; held before the move, and the report reads the KB as it stood off those values after
;; the write (`vaelii.impl.kb/prior-kb`, docs/nmtms.md, "The published set").

(def ^:dynamic *write-record*
  "Nil, or the open write record: an `IdentityHashMap` from each structure a choke point
  moved since the record opened (a network, a taxonomy atom, the candidate index, a
  record store, an index backend, a trie) to what that structure held before its first
  move.  Bound by the write entry points while a report is wanted
  (`vaelii.impl.settle/write-record`), and emptied by `settle-finish` once it has
  reported."
  nil)

(defn record-of
  "What the open write record keeps for `owner`, made by `(make)` at the first call since
  the record opened or was emptied, so `make` reads `owner` before its first move; nil
  when no record is open."
  [owner make]
  (when-let [^java.util.IdentityHashMap r *write-record*]
    (or (.get r owner)
        (let [v (make)] (.put r owner v) v))))

(defn recorded
  "What the open write record keeps for `owner`, or nil."
  [owner]
  (when-let [^java.util.IdentityHashMap r *write-record*] (.get r owner)))

(defn keep-before!
  "Record `(read)` under `k` in `owner`'s map of the open write record, a volatile of a
  map keyed by `=`, unless an earlier move recorded `k`.  A nil value records that `k`
  held nothing."
  [owner k read]
  (when-let [v (record-of owner #(volatile! {}))]
    (when-not (contains? @v k) (vswap! v assoc k (read)))))

(defn kept
  "The map `keep-before!` recorded for `owner` in the open write record, or nil."
  [owner]
  (some-> (recorded owner) deref))

;; ---- the published state: a settle's holds -----------------------------------
;;
;; A settle holds the belief it started from for every other thread and publishes what it
;; decided in one step when it ends (`vaelii.impl.settle/settle`). The network records the
;; labels the settle moves (`vaelii.impl.jtms/hold!`), the held sets keep their value
;; (`held-atom`), and this registry says which holds are open and which thread owns each.
;; Closing a hold is one swap here, so a reader switches from held to published belief in
;; one step across the network, the held sets and the clock.

(defonce ^{:private true
           :tag AtomicReference
           :doc "The open holds, as `{token owner-thread}`.  Empty on nearly every read."}
  holds
  (AtomicReference. {}))

(def ^:dynamic *live*
  "True where a thread reads what the writer holds now even while a hold is open.  The
  taxonomy's visibility callbacks bind it (`live`): the closures they decide are memoized
  where the writer reads them, so they must describe the network the writer is deciding."
  false)

(defn- owns-a-hold?
  "Does thread `t` own one of the holds in `m`?"
  [m t]
  (reduce-kv (fn [_ _ owner] (if (identical? owner t) (reduced true) false)) false m))

(defn held-reader?
  "Does the current thread read held belief: a hold is open, this thread owns none, and
  it is not reading live (`*live*`)?"
  []
  (let [m (.get holds)]
    (and (not (zero? (count m)))
         (not (owns-a-hold? m (Thread/currentThread)))
         (not *live*))))

(defn hold-owner?
  "Does the current thread own an open hold?"
  []
  (owns-a-hold? (.get holds) (Thread/currentThread)))

(defn registry
  "The open holds, as one value.  Every open and every close replaces it, so a reader
  that reads it before and after a read of live state, and finds the same value both
  times, knows no hold opened or closed in between."
  []
  (.get holds))

(defn reads-held-in?
  "Does the current thread read the belief hold `h` keeps, by `registry` value `m`: `h`
  is open in `m`, this thread owns no hold there, and it is not reading live?  The
  network and the held atoms ask this after their own owner check, so the writer's reads
  never reach it."
  [m h]
  (and (contains? m (:token h))
       (not (owns-a-hold? m (Thread/currentThread)))
       (not *live*)))

(defn reads-held?
  "`reads-held-in?` against the registry as it is now."
  [h]
  (reads-held-in? (.get holds) h))

(defn new-hold
  "A hold owned by the current thread, not yet open: `{:token :owner}`."
  []
  {:token (Object.) :owner (Thread/currentThread)})

(defn open-hold!
  "Open hold `h`: move the change clock, then register `h`, after which every thread that
  owns no hold reads the belief `h` keeps.  The clock moves first so a cache entry a held
  reader installs under this hold carries a clock value no earlier hold's reader used
  (`change-clock`)."
  [h]
  (note-change)
  (loop []
    (let [m (.get holds)]
      (when-not (.compareAndSet holds m (assoc m (:token h) (:owner h))) (recur))))
  h)

(defn close-hold!
  "Close hold `h`: from this call on, every thread reads the belief its writer published."
  [h]
  (loop []
    (let [m (.get holds)]
      (when-not (.compareAndSet holds m (dissoc m (:token h))) (recur))))
  nil)

(defmacro live
  "Run `body` reading what the writer holds now, whatever hold is open.  Binds `*live*`
  only on a thread that reads held belief (`held-reader?`), so the writer and every read
  outside a settle pay one registry read."
  [& body]
  `(if (held-reader?) (binding [*live* true] ~@body) (do ~@body)))

(defn- keep-value!
  "Record the value `a`, the atom inside the held atom `ha`, holds in the open write
  record before its first write there."
  [ha ^clojure.lang.Atom a]
  (when *write-record*
    (record-of ha #(.deref a))))

(deftype HeldAtom [^clojure.lang.Atom a ^AtomicReference held]
  ;; `held` is nil, or `{:hold h :value v}`: the value `a` held when hold `h` began.  Every
  ;; write goes to `a`; a deref answers `v` to a thread that reads `h`'s belief.
  ;;
  ;; A deref that answers `a`'s own value reads the registry before and after it, and
  ;; reads again when a hold opened or closed in between: a settle writes the held sets only
  ;; while its hold is open, so a value read with no hold open on either side is one no
  ;; settle was deciding.
  clojure.lang.IDeref
  (deref [_]
    (let [p (.get held)]
      (if (and p (identical? (:owner (:hold p)) (Thread/currentThread)))
        (.deref a)
        (loop []
          (let [m (.get holds)
                p (.get held)]
            (if (and p (reads-held-in? m (:hold p)))
              (:value p)
              (let [v (.deref a)]
                (if (identical? m (.get holds)) v (recur)))))))))
  ;; every write first offers the value it replaces to the open write record
  clojure.lang.IAtom2
  (swap [this f] (keep-value! this a) (.swap a f))
  (swap [this f x] (keep-value! this a) (.swap a f x))
  (swap [this f x y] (keep-value! this a) (.swap a f x y))
  (swap [this f x y args] (keep-value! this a) (.swap a f x y args))
  (compareAndSet [this o n] (keep-value! this a) (.compareAndSet a o n))
  (reset [this v] (keep-value! this a) (.reset a v))
  (swapVals [this f] (keep-value! this a) (.swapVals a f))
  (swapVals [this f x] (keep-value! this a) (.swapVals a f x))
  (swapVals [this f x y] (keep-value! this a) (.swapVals a f x y))
  (swapVals [this f x y args] (keep-value! this a) (.swapVals a f x y args))
  (resetVals [this v] (keep-value! this a) (.resetVals a v)))

(defn held-atom
  "An atom holding `v` that keeps its value for a hold's readers (`hold-atom!`)."
  [v]
  (HeldAtom. (atom v) (AtomicReference. nil)))

(defn hold-atom!
  "Keep `ha`'s current value for the readers of hold `h`, until `release-atom!`."
  [^HeldAtom ha h]
  (.set ^AtomicReference (.-held ha) {:hold h :value (.deref ^clojure.lang.Atom (.-a ha))})
  nil)

(defn release-atom!
  "Stop keeping a value for a hold's readers: every deref reads `ha`'s own value."
  [^HeldAtom ha]
  (.set ^AtomicReference (.-held ha) nil)
  nil)

(defn change-clock
  "The current value of the change clock. A reader records what it derived under this and
  re-derives when it has moved. A thread that reads held belief (`held-reader?`) reads
  `-1 - clock` instead, so what it derives under the hold never shares an entry with the
  writer's. `open-hold!` moves the clock, so two holds' readers do not share one either."
  ^long []
  (let [c (.get clock)]
    (if (held-reader?) (- -1 c) c)))

;; ---- the stored-handle cache --------------------------------------------

(def ^:dynamic *handle-cache*
  "A mutable `{[sentence context] handle}` map, or nil (the default: off). A positive
  lookup cache over `kb/find-sentex-handle` for forward chaining, where a conclusion reached
  by k witnesses is looked up once per witness. Only hits are cached: a cached absence would
  be wrong once a firing stores the sentence, and `integrate/sentex-removed!` clears an entry.
  The key is the sentence as the caller spelled it, and canonicalization reads only the
  `symmetric` predicate set (`resolution/kb-sentex`), so every entry carries that set as its
  cache key and the map drops when the set is replaced. Bound per run (`chain/chain`). A
  `java.util.HashMap`, because the engine is single-writer. See docs/inference.md."
  nil)

(def ^:private filled-under-key
  "Where the map holds the cache key it was filled under — a keyword, so it cannot
  collide with a `[sentence context]` key."
  ::filled-under)

(def ^:private generation-key
  "Where the cache's **generation** lives: a counter stepped at every wholesale clear,
  so a reader that recorded it can tell whether the entries it saw filled are still
  the entries the map holds.  Beside the cache key for the same reason the cache key is
  there — a keyword cannot collide with a `[sentence context]` key."
  ::generation)

(defn- current-under?
  "Was the cache `c` filled under `cache-key`?  `=`, not `identical?`: the key is a
  composite (the KB's record store, then the symmetric-predicate set), rebuilt per call
  — the store half compares by identity inside it, which is the isolation the composite
  exists for."
  [^java.util.Map c cache-key]
  (= cache-key (.get c filled-under-key)))

(defn cached-handle
  "The cached handle for `sentence` in `context` under `cache-key`, or nil — including
  whenever the cache was filled under a different key, which is a miss and not a
  wrong answer."
  [cache-key sentence context]
  (when-let [^java.util.Map c *handle-cache*]
    (when (current-under? c cache-key)
      (.get c [sentence context]))))

(defn cache-handle!
  "Record that `sentence` in `context` is stored at `handle`, valid while `cache-key`
  holds; returns `handle`.  A key the cache was not filled under empties it first —
  everything in it was keyed on a canonicalization that has since moved — and steps
  the generation (`cache-generation`).  A no-op when no cache is bound."
  [cache-key sentence context handle]
  (when-let [^java.util.Map c *handle-cache*]
    (when-not (current-under? c cache-key)
      (let [gen (long (or (.get c generation-key) 0))]
        (.clear c)
        (.put c filled-under-key cache-key)
        (.put c generation-key (inc gen))))
    (.put c [sentence context] handle))
  handle)

(defn cache-generation
  "Which filling of the handle cache is current under `cache-key`, a counter that steps at
  every wholesale clear, or nil when no cache is bound or it was filled under another key.
  A cache nothing has filled yet is claimed for `cache-key` here at generation 1, so a reader
  can record the filling before the first store lands. For a reader whose claim rests on every
  store since some moment being in the cache (`kb/find-sentex-handle`'s authority memo): an
  equal generation says no clear has happened since."
  [cache-key]
  (when-let [^java.util.Map c *handle-cache*]
    (cond
      (current-under? c cache-key)     (.get c generation-key)
      (nil? (.get c filled-under-key)) (do (.put c filled-under-key cache-key)
                                           (.put c generation-key 1)
                                           1)
      :else                            nil)))

(defn forget-handle!
  "Drop `sentence`/`context` from the cache — the removal choke point's half of the
  contract above.  It reads no cache key on purpose: a removal falsifies the entry under every
  key, and the choke point should not have to know which one is current."
  [sentence context]
  (when-let [^java.util.Map c *handle-cache*] (.remove c [sentence context]))
  nil)

(defmacro with-handle-cache
  "Run `body` with the stored-handle cache engaged.  An outer cache is reused rather
  than shadowed, so a nested run shares the entries its parent has already paid for —
  the same composition `with-held-values` makes."
  [& body]
  `(binding [*handle-cache* (or *handle-cache* (java.util.HashMap.))] ~@body))

(def ^:private resident-limit
  "The most entries a resident cache holds before it is cleared wholesale — the same
  bound, and the same wholesale clearing, the content-keyed caches take."
  256)

(def ^:dynamic *held-values*
  "An atom, or nil. While one is bound, whatever `cached` derives inside that scope is held
  fixed for the rest of it and the clock is not consulted again. A caller that writes while
  it reads (forward chaining places each solution of a lazy join before the next is realized)
  would otherwise re-derive per solution and join against states the other half never saw.
  Bound where a step runs (`chain/process-datum`, `inference/step!`) and never wider; a
  backward search binds it too (`with-search-scope`, `res/prove-seq`). See
  docs/inference.md."
  nil)

(defn clocked
  "The value of `k` in the resident `cache`, an atom of `{k {:value v :clock n}}`, with
  `build` run whenever the change clock has moved since `v` was derived. A nil `cache` runs
  `build` every time. `build` is called with the stale value it replaces, or nil, for a
  caller that derives the new answer from the old (`qcn-kb`'s warm-started pass). The clock
  is read before `build` and the entry recorded under that reading. Nothing here is
  content-keyed: the derivations over a resident value stay keyed on that value, so two KBs
  reaching one network share one pass."
  [cache k build]
  (if (nil? cache)
    (build nil)
    (let [now (change-clock)
          hit (get @cache k)
          t   (caches/tally-of cache :R3)]
      (if (and hit (== now (long (:clock hit))))
        (do (caches/hit t) (:value hit))
        (let [v (caches/recomputed t (build (:value hit)))]
          (when (and hit (caches/tallying?))
            (caches/compared t (= (:value hit) v)))
          (swap! cache caches/assoc-bounded
                 (caches/limit-of :resident resident-limit)
                 k {:value v :clock now})
          v)))))

(defn cached
  "`clocked`, overridden by a bound `*held-values*`: the value that scope holds for `k`, or
  the one `clocked` answers now, held for the rest of the scope."
  [cache k build]
  (let [held *held-values*
        pk   (when held [cache k])]              ; the atom's identity is the KB's identity
    (if-let [found (and held (find @held pk))]
      (val found)
      (let [v (clocked cache k build)]
        (when held (swap! held assoc pk v))
        v))))

(defn newly-seen?
  "Record `v` as the value now held under `k` in the resident `cache`, and answer whether it
  is new there: true the first time, false while it is still the one held. A nil cache is no
  memory, so everything is new. For a report that fires once per KB rather than once per
  computation, since the derivations over a network are shared across KBs. Errs toward
  reporting: a wholesale clear drops the entry, so a report can repeat and cannot go
  missing. The marker is held under `[::seen k]` (`restore-seen!`)."
  [cache k v]
  (if (nil? cache)
    true
    (let [k [::seen k]]
      (if (= v (get @cache k ::absent))
        false
        (do (swap! cache caches/assoc-bounded (caches/limit-of :resident resident-limit) k v)
            true)))))

(defn- seen-marker? [entry]
  (let [k (key entry)] (and (vector? k) (= ::seen (nth k 0 nil)))))

(defn restore-seen!
  "Put the `newly-seen?` markers of the resident `cache` back to those `baseline`, a value
  `cache` held earlier, holds, and keep every other entry as it stands. A rollback calls it
  beside the ledger's restore, so a network whose entry the rollback dropped is reported
  again."
  [cache baseline]
  (when cache
    (swap! cache (fn [cur] (-> (into {} (remove seen-marker?) cur)
                               (into (filter seen-marker?) baseline)))))
  nil)

(defonce ^{:private true
           :tag AtomicLong}
  neighbour-hits
  (AtomicLong. 0))
(defonce ^{:private true
           :tag AtomicLong}
  neighbour-misses
  (AtomicLong. 0))

(defn note-neighbours!
  "Record one neighbour-set read by the closure walk: `hit?` true where `*reach-memo*`
  answered it, false where it was computed (every read with no memo bound included).
  `misses` is the walk's real cost, one store retrieval each, and feeds the
  `:closure-neighbours` row's `:hit-rate`. Process-wide `AtomicLong`s, as `literal-cache`'s
  are, since they measure the mechanism and not a store."
  [hit?]
  (if hit? (.incrementAndGet neighbour-hits) (.incrementAndGet neighbour-misses))
  nil)

(defn neighbour-counts
  "`{:hits :misses}` for the neighbour memo — hits served, neighbour sets computed."
  []
  {:hits (.get neighbour-hits) :misses (.get neighbour-misses)})

(defn reset-neighbour-counters
  "Zero the neighbour counters and answer them as they stood.  Wider than one KB, like
  the counters themselves, which is why it is its own control and not part of a clear."
  []
  (let [h (.get neighbour-hits) m (.get neighbour-misses)]
    (.set neighbour-hits 0)
    (.set neighbour-misses 0)
    {:hits h :misses m}))

(def ^:dynamic *reach-memo*
  "A per-query cache for the transitive-predicate closure's per-node neighbour lookups
  (`succs` / `preds-of`), an atom of `{[dir pred node context] -> set}`, or nil for none.
  A rule with two transitive antecedents solves the second once per binding of the join
  variable over nodes the bindings share. A backward search establishes one memo per search
  step (`res/prove-from` segment, `inference/step!`), created fresh and never invalidated,
  since a query mutates no belief. See docs/inference.md."
  nil)

(defmacro with-held-values
  "Run `body` with the resident values it reads held fixed — see `*held-values*`.  An outer
  binding is reused rather than shadowed, so a nested step joins against the state its
  parent is joining against, which is what makes the two binding sites compose."
  [& body]
  `(binding [*held-values* (or *held-values* (atom {}))] ~@body))

(defmacro with-search-scope
  "Run `body` as one step of a backward search: resident values held fixed
  (`with-held-values`) and one transitive-closure memo (`*reach-memo*`) open for its length.
  Both compose with an outer scope, so a nested expansion shares what its parent paid for.
  `inference/step!` binds it per node and `res/prove-from` per segment. `body` must be eager:
  a lazy seq escaping the scope realizes later with the bindings gone."
  [& body]
  `(with-held-values (binding [*reach-memo* (or *reach-memo* (atom {}))] ~@body)))

;; ---- what this extension point holds, declared -------------------------------------
;;
;; One resident cache a reader can count, and three that are bound for the length of a
;; step and garbage when it returns.  The three are registered all the same: a page
;; listing only the countable ones would imply the engine holds nothing else, and
;; "cannot be counted from outside a run" is a fact about the cache rather than a gap in
;; the list.

(caches/register-cache
 {:cache    :resident
  :label    "Resident derived values"
  :scope    :kb
  :unit     "networks and passes"
  :limit    (caches/limit-thunk :resident resident-limit)
  :counters :kb
  :note     (str "What this KB's derived structures cost to read out of the store — a "
                 "qualitative constraint network per calculus and context, the metric "
                 "problem behind it, and the closures over each. Keyed by the "
                 "change clock, so one mutation retires every entry; past the limit it "
                 "is cleared wholesale.")
  :read     (fn [kb] {:entries (some-> (reasoning/qcn kb) deref count)})
  :clear    (fn [kb] (let [a (reasoning/qcn kb)
                           n (if a (count @a) 0)]
                       (some-> a (reset! {}))
                       n))
  :trim     (fn [kb target] (when-let [a (reasoning/qcn kb)] (caches/trim-map! a target)))})

(caches/register-cache
 {:cache    :stored-handles
  :label    "Stored handles"
  :scope    :process
  :unit     "sentences"
  :limit    nil
  :counters nil
  :note     (str "Which handle a sentence already has, for the one caller that asks "
                 "thousands of times about the same sentence. Bound for the length of "
                 "one forward-chaining run and garbage when it returns, so a read from "
                 "anywhere else — this page included — sees nothing to count.")
  :read     (fn [_] {:entries (some-> ^java.util.Map *handle-cache* .size)})})

(caches/register-cache
 {:cache    :closure-neighbours
  :label    "Closure neighbours"
  :scope    :process
  :unit     "neighbour sets"
  :limit    nil
  :counters :process
  :note     (str "A transitive predicate's per-node neighbour lookups, so a join over "
                 "one solves each node once rather than once per binding. Bound per "
                 "backward-search step, so its ENTRIES are uncountable from outside one "
                 "for the same reason the stored handles are — the counters are not, and "
                 "a miss is one neighbour set built against the store.")
  :read     (fn [_] (assoc (neighbour-counts)
                           :entries (some-> *reach-memo* deref count)))
  :reset-counters (fn [_] (reset-neighbour-counters))})

(caches/register-cache
 {:cache    :held-values
  :label    "Held values"
  :scope    :process
  :unit     "resident values"
  :limit    nil
  :counters nil
  :note     (str "The resident values one inference step holds fixed while it writes, "
                 "so a join reads one state rather than a moving one. A step's scope, "
                 "and so uncountable between steps.")
  :read     (fn [_] {:entries (some-> *held-values* deref count)})})

(caches/register-derived
 {:id :X3 :label "Change clock" :kind :counter :keyed-by :global :reads []
  :holds-content? false
  :retired-by (caches/on-every :G*) :computed :write :imaged? false :var #'clock
  :value (fn [_] (.get clock))
  :note "bumped by every mutation of any KB in the process; R1, R2 and R3 key entries by it"})

(caches/register-derived
 {:id :R3 :label "Resident derived values" :cache :resident :kind :cache :keyed-by :context
  :holds-content? false
  :reads [:index :M1]
  :retired-by (assoc (caches/on-every :G*) :caches-cleared :W :cleared :W)
  :computed :read :imaged? false :at [[:qcn]]
  :live (fn [kb] (let [now (change-clock)]
                   (count (filter #(and (map? %) (== now (long (:clock % -1))))
                                  (vals @(reasoning/qcn kb))))))
  :note "networks and passes by `[calc ctx]`, each keyed by the change clock and rebuilt from its stale value; `newly-seen?` markers carry no clock"})

(caches/register-derived
 {:id :R7 :label "Search-step memos" :cache :closure-neighbours :kind :pass :keyed-by :node
  :holds-content? false
  :reads [:index :M1] :retired-by {} :computed :pass :imaged? false :var #'*reach-memo*
  :note "`*reach-memo*` (neighbour sets) and `*held-values*` (resident values held fixed), bound for one search step or one datum"})

(caches/register-derived
 {:id :R8 :label "Stored handles" :cache :stored-handles :kind :pass :keyed-by :literal
  :holds-content? false
  :reads [:index :records] :retired-by {:removed :K :respelled :K} :computed :pass
  :imaged? false :var #'*handle-cache*
  :note "`[sentence ctx]` to handle for one chaining run, and the chain authority memo (`kb/*chain-authoritative-functors*`); a removal forgets its handle and a `handle-cache-key` step clears both"})

(caches/register-derived
 {:id :R14 :label "Write record" :kind :pass :keyed-by :value :holds-content? false
  :reads [:records :index :M1 :T1 :J1] :retired-by {} :computed :pass :imaged? false
  :var #'*write-record*
  :note "what each structure a write moves held before its first move, bound for one write and read by its report (`kb/prior-kb`)"})
