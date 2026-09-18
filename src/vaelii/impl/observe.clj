;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.observe
  "The leaf extension point the engine's mutation choke points notify **without a require cycle**.
  Two things ride on it, and they are independent: named observers of the stored fact
  set, and one counter saying that *something* changed.

  **Observers.**  The incremental rule-matcher (`vaelii.impl.rete`) keeps RAM alpha
  memories that must mirror the stored fact set exactly.  The only structural mutations
  to that set are `kb/create-sentex` (add) and `integrate/sentex-removed!` (remove), but
  both of those namespaces sit *below* `rete` in the layering — `rete` needs `kb`,
  `resolution`, and `plan` to match — so they cannot call it directly.  They call the atoms
  here instead, and `rete` installs itself into them when it is engaged.

  When nothing is engaged the atoms hold `nil` and `notify-*` is a single deref plus
  a `nil?` check, so the reference forward chainer pays essentially nothing.  The
  observer is global rather than per-KB (single-writer, like the rest of the engine);
  the installed functions dispatch on `kb` themselves, so several KBs can be live at
  once and each keeps its own alpha memories.

  **The change clock** is the cheapest possible version of the same idea, for a cache
  that has to notice a change nobody registered to hear about.  See `note-change`.

  **The resident caches** the clock exists for are here too (`cached`), and each declares
  itself to `vaelii.impl.caches` at the bottom of this file so a reader can see what the
  process is holding."
  (:refer-clojure :exclude [])
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.util.concurrent.atomic AtomicLong]))

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
  `installed?` those two callers gate on — all of them on the writing thread, under the
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
  "Something that a resident derived structure is a function of has just changed.  Three
  places bump it, and together they are the *whole* of what such a structure can depend
  on: the two store choke points (`kb/create-sentex`, `integrate/sentex-removed!`), every
  mutating `jtms` entry point, and a watch on the taxonomy's atom — which sentexes exist,
  which of them are believed, and what the closures say.  Two bulk operations bump by hand
  because they move a store without passing either choke point: `core/clear!` and
  `reindex/reindex`.

  Global and deliberately coarse.  It says only *that* something moved — never what,
  and not even which KB — so a reader keyed on it re-derives more often than it
  strictly must, and never less.  That is the direction a correctness argument wants:
  a cache is reused only across a stretch in which the engine performed no mutation at
  all, which is exactly the stretch a settle pass, a query, or a prover loop spends
  reading.  Making it finer would mean deciding, at each choke point, which caches a
  change is relevant to — the judgement that gets a cache wrong.

  Bare, not `!`: it destroys nothing (the `!` convention marks losing knowledge)."
  []
  (.incrementAndGet clock))

(defn change-clock
  "The current value of the change clock.  A reader stamps what it derived with this
  and re-derives when it has moved."
  ^long []
  (.get clock))

;; ---- the stored-handle cache --------------------------------------------

(def ^:dynamic *handle-cache*
  "A mutable `{[sentence context] handle}` map, or nil — the default, and the cache is
  off.

  A **positive** lookup cache over `kb/find-sentex-handle`: which handle a sentence
  already has in a context.  It exists for the one caller that asks that question about
  the same sentence thousands of times — forward chaining, where a conclusion reached by
  k witnesses is looked up once per witness, and every look after the first runs the
  canonicalizer and walks the trie to arrive at a handle the run itself minted moments
  earlier.

  **Only hits are cached, never misses**, and that asymmetry is the whole correctness
  argument.  A sentence absent now is one a firing is about to store, so a cached
  absence would be wrong within microseconds; a cached presence stays true until the
  sentex is removed, and removal is a choke point (`integrate/sentex-removed!`) that
  clears the entry.  A miss and an unbound cache are therefore the same answer — fall
  through and ask the index.

  The key is the sentence **as the caller spelled it**, which is the second thing to
  invalidate on and the reason every entry carries a `stamp`.  A raw sentence reaches
  its handle by way of canonicalization, and canonicalization reads exactly one thing
  off the KB: which predicates are `symmetric` (`resolution/kb-sentex`).  So a cached
  answer is valid precisely while that set is — hand the set itself in as the stamp and
  the whole map is dropped the moment it is replaced, whether by a declaration arriving,
  one leaving, or one changing belief.  Nothing else in a sentex's key is a function of
  the KB.

  Bound per forward-chaining run (`chain/chain`), which is also what bounds its size:
  an entry is only ever added beside a sentex the store already holds, so the cache
  cannot outgrow the store it mirrors, and it is garbage the moment the run returns.
  A `java.util.HashMap` rather than an atom because the engine is single-writer and
  this sits on the placement path — a CAS per conclusion is part of the cost being
  removed, not a synchronization the caller needs."
  nil)

(def ^:private stamp-key
  "Where the current stamp lives in the cache map — a keyword, so it cannot collide
  with a `[sentence context]` key."
  ::stamp)

(def ^:private generation-key
  "Where the cache's **generation** lives: a counter stepped at every wholesale clear,
  so a reader that recorded it can tell whether the entries it saw filled are still
  the entries the map holds.  Beside the stamp for the same reason the stamp is there —
  a keyword cannot collide with a `[sentence context]` key."
  ::generation)

(defn- current-under?
  "Was the cache `c` filled under `stamp`?  `=`, not `identical?`: the stamp is a
  composite (the KB's record store, then the symmetric-predicate set), rebuilt per call
  — the store half compares by identity inside it, which is the isolation the composite
  exists for."
  [^java.util.Map c stamp]
  (= stamp (.get c stamp-key)))

(defn cached-handle
  "The cached handle for `sentence` in `context` under `stamp`, or nil — including
  whenever the cache was filled under a different stamp, which is a miss and not a
  wrong answer."
  [stamp sentence context]
  (when-let [^java.util.Map c *handle-cache*]
    (when (current-under? c stamp)
      (.get c [sentence context]))))

(defn cache-handle!
  "Record that `sentence` in `context` is stored at `handle`, valid while `stamp`
  holds; returns `handle`.  A stamp the cache was not filled under empties it first —
  everything in it was keyed on a canonicalization that has since moved — and steps
  the generation (`cache-generation`).  A no-op when no cache is bound."
  [stamp sentence context handle]
  (when-let [^java.util.Map c *handle-cache*]
    (when-not (current-under? c stamp)
      (let [gen (long (or (.get c generation-key) 0))]
        (.clear c)
        (.put c stamp-key stamp)
        (.put c generation-key (inc gen))))
    (.put c [sentence context] handle))
  handle)

(defn cache-generation
  "Which filling of the handle cache is current under `stamp` — a counter that steps
  at every wholesale clear — or nil when no cache is bound, or when the cache was
  filled under another stamp (its entries answer nothing under this one, and the next
  `cache-handle!` empties it).  A cache nothing has filled yet is claimed for `stamp`
  here, at generation 1, so a reader can record the filling *before* the first store
  lands in it.  For a reader whose claim rests on *every* store since some moment
  being in the cache (`kb/find-sentex-handle`'s authority memo): a generation equal to
  the one it recorded says no clear has happened since, and a different one — or nil
  — says the entries it counted on are not there."
  [stamp]
  (when-let [^java.util.Map c *handle-cache*]
    (cond
      (current-under? c stamp)    (.get c generation-key)
      (nil? (.get c stamp-key))   (do (.put c stamp-key stamp)
                                      (.put c generation-key 1)
                                      1)
      :else                       nil)))

(defn forget-handle!
  "Drop `sentence`/`context` from the cache — the removal choke point's half of the
  contract above.  Stamp-blind on purpose: a removal falsifies the entry under every
  stamp, and the choke point should not have to know which one is current."
  [sentence context]
  (when-let [^java.util.Map c *handle-cache*] (.remove c [sentence context]))
  nil)

(defmacro with-handle-cache
  "Run `body` with the stored-handle cache engaged.  An outer cache is reused rather
  than shadowed, so a nested run shares the entries its parent has already paid for —
  the same composition `with-pin` makes."
  [& body]
  `(binding [*handle-cache* (or *handle-cache* (java.util.HashMap.))] ~@body))

(def ^:private resident-limit
  "The most entries a resident cache holds before it is cleared wholesale — the same
  bound, and the same wholesale clearing, the content-keyed caches take."
  256)

(def ^:dynamic *pin*
  "An atom, or nil.  While one is bound, whatever `cached` derives inside that scope is
  **held fixed** for the rest of it — the clock is not consulted again.

  The clock alone is not enough for a caller that *writes while it reads*, and forward
  chaining is exactly that: a rule's join is a lazy seq, and each solution taken off it is
  placed — a store and a justification — before the next is realized.  So a join over one
  network with the clock as the only stamp would re-derive that network per solution, and
  join half of its bindings against a state the other half never saw.

  Holding it fixed is not an approximation of the fixpoint, it *is* the fixpoint: an
  immediate-consequence step is by definition computed from one state, and what a step
  enables is picked up by the next round rather than mid-step.  So the pin is bound where
  a step runs — one agenda datum (`chain/process-datum`), one node expansion
  (`inference/expand-node`) — and never wider than the thing whose answer must come from
  one state.  Outside such a scope there is nothing to hold fixed and the clock answers
  alone.

  A **backward search** binds it too (`with-search-scope`, from `res/prove-from`), and
  there the argument is the weaker one: a query mutates no belief, so nothing needs
  holding still for correctness, and what the pin buys is that a consumer placing
  conclusions off a lazy seq joins against one state rather than a moving one.  A
  lazily-driven search therefore scopes it per segment rather than per query, which is
  sound for exactly that reason — see `res/prove-seq`."
  nil)

(defn cached
  "The value of `k` in the resident `cache` — an atom of `{k {:value v :clock n}}` — with
  `build` run whenever the change clock has moved since `v` was derived.  `nil` for
  `cache` runs `build` every time, which is what a caller holding no residency does.  A
  bound `*pin*` overrides both: within its scope the first answer is the answer.

  `build` is called with the **stale value** it is replacing, or nil — what this cache
  held before the clock moved.  A caller that can derive its new answer from its old one
  more cheaply than from nothing takes it (`qcn-kb`'s warm-started path-consistency pass);
  one that cannot ignores the argument.

  The clock is read **before** `build`, and it is that earlier reading the entry is
  stamped with.  Should anything mutate while a build is in flight, the entry is stamped
  older than the clock and the next read rebuilds; stamping it afterwards would claim the
  value describes a state it was never computed from.  (The engine is single-writer, so
  this is the argument rather than the scenario.)

  Nothing here is content-keyed, and it does not need to be: the expensive *derivations*
  over a resident value — a path-consistency pass, a shortest-path closure — stay keyed on
  that value, so two KBs reaching the same network still share one pass.  This layer is
  about not reading the KB again, and reading the KB again is a per-KB question."
  [cache k build]
  (let [pin *pin*
        pk  (when pin [cache k])]                ; the atom's identity is the KB's identity
    (if-let [pinned (and pin (find @pin pk))]
      (val pinned)
      (let [v (if (nil? cache)
                (build nil)
                (let [now (change-clock)
                      hit (get @cache k)]
                  (if (and hit (== now (long (:clock hit))))
                    (:value hit)
                    (let [v (build (:value hit))]
                      (swap! cache caches/assoc-bounded
                             (caches/limit-of :resident resident-limit)
                             k {:value v :clock now})
                      v))))]
        (when pin (swap! pin assoc pk v))
        v))))

(defn newly-seen?
  "Record `v` as the value now held under `k` in the resident `cache`, and answer whether
  it is **new** there — true the first time a value is seen, false while it is still the
  one held.  A nil cache is no memory at all, so everything is new.

  For a report that must fire once per KB rather than once per computation.  The expensive
  derivations over a network — a shortest-path closure, a path-consistency pass — are keyed
  on the network *value* and shared across KBs, which is what lets two of them reaching the
  same network share one pass.  A report hung off that pass therefore fires for whichever
  KB ran it and for no other, and the second KB answers nothing with an empty ledger
  explaining why.  Hung off this instead the question becomes \"has *this* KB said this
  yet\", which is the one a ledger is answering — and the same for two contexts of one KB
  that see the same constraints.

  Errs toward reporting: the entry is dropped with the rest when the cache is cleared
  wholesale, so a report can repeat, and cannot go missing."
  [cache k v]
  (if (nil? cache)
    true
    (if (= v (get @cache k ::absent))
      false
      (do (swap! cache caches/assoc-bounded (caches/limit-of :resident resident-limit) k v)
          true))))

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
  answered it, false where it was **computed** — which includes every read taken with no
  memo bound at all, since a compute is a compute whatever scope it happens in.

  Counted here rather than inferred from outside.  `misses` is the walk's real cost —
  neighbour sets built, one store retrieval each — and the only alternative is to
  intercept `res/matches-visible` and guess which of its calls are the walk's by the
  `?rv` its patterns carry, a heuristic that cannot separate a walk's probe from a
  `FactProver` lookup of the same predicate.
  A counter on the memo answers the question the caches page asks anyway (`:hit-rate` on
  the `:closure-neighbours` row) and the question a test asks, in the same number.

  Process-wide `AtomicLong`s, `literal-cache`'s arrangement and for its reason: they
  measure the mechanism, not a store, and a per-KB split would bill one KB for a walk
  another ran."
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
  "A per-query cache for the transitive-predicate closure's per-node neighbour
  lookups (`succs` / `preds-of`) — an atom of `{[dir pred node context] -> set}`, or
  nil for no memoization.

  A rule with two transitive antecedents — `(implies (and (before ?a ?b) (before ?b
  ?c)) …)` over a transitive `before` — solves the *second* antecedent once per
  binding of the join variable, and each solve walks the closure over nodes many of
  those seeds share, re-hitting the store for the same `(pred node)` neighbour set.
  A backward search establishes one memo per search step — one `res/prove-from` segment,
  one `inference/expand-node` — so each neighbour lookup touches the store once instead of
  once per binding of the join variable.  The step is the scope because that is where the
  repetition is; a session-wide binding could not survive the node engine's laziness
  anyway.  Created fresh per step and a query never mutates belief, so it cannot go
  stale — no invalidation, and no cross-query leakage."
  nil)

(defmacro with-pin
  "Run `body` with the resident values it reads held fixed — see `*pin*`.  An outer pin is
  reused rather than shadowed, so a nested step joins against the state its parent is
  joining against, which is what makes the two binding sites compose."
  [& body]
  `(binding [*pin* (or *pin* (atom {}))] ~@body))

(defmacro with-search-scope
  "Run `body` as one step of a backward search: resident values held fixed (`with-pin`)
  and one transitive-closure memo (`*reach-memo*`) open for its length.

  The two go together because a search step is where both problems appear at once — a
  rule's join solves one antecedent per binding of the join variable, so the closure walk
  repeats over nodes those bindings share, and a caller placing conclusions as it
  consumes the join would otherwise re-derive a network per solution.  Both compose with
  an outer scope rather than shadowing it, so a nested expansion shares what its parent
  already paid for.

  A *step*, not a query: `inference/expand-node` binds it per node and `res/prove-from`
  per segment of its loop, so a lazily driven search opens one per pull.  That is the
  finest scope at which the repetition above still collapses, and the widest at which a
  lazy consumer can still be handed a seq — see `res/prove-seq`.

  **`body` must be eager.**  A lazy seq escaping this scope realizes later with the
  bindings gone, which for the memo is a silent slowdown and for the pin is a join
  against a state that moved."
  [& body]
  `(with-pin (binding [*reach-memo* (or *reach-memo* (atom {}))] ~@body)))

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
  :counters nil
  :note     (str "What this KB's derived structures cost to read out of the store — a "
                 "qualitative constraint network per calculus and context, the metric "
                 "problem behind it, and the closures over each. Stamped with the "
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
 {:cache    :pinned-values
  :label    "Pinned values"
  :scope    :process
  :unit     "resident values"
  :limit    nil
  :counters nil
  :note     (str "The resident values one inference step holds fixed while it writes, "
                 "so a join reads one state rather than a moving one. A step's scope, "
                 "and so uncountable between steps.")
  :read     (fn [_] {:entries (some-> *pin* deref count)})})
