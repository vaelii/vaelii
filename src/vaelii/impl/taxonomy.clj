;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.taxonomy
  "Cached transitive closures for the two transitivity relations at the heart of
  common-sense reasoning:

    genl    relates predicates       (genl dog animal)   — types are its unary case
    genlCx  relates *contexts*       (genlCx CxA CxB)     — context inheritance

  Transitivity is not done with rules (too central, too hot); instead we store the
  **direct adjacency** of each relation and answer the reflexive-transitive up/down
  closure *on demand*.  `genls` is ancestors-incl-self, `specs` is descendants-
  incl-self.

  We deliberately do **not** materialize the full closure.  A materialized closure
  is Θ(V²) for a deep hierarchy — a 10k-node `genl` chain stores ~50M pairs — so
  building it incrementally makes a bulk load quadratic no matter how clever each
  insert is: the representation itself is the cost.  Storing only the O(V+E)
  adjacency makes a closure read O(reachable-subgraph) and an insert the adjacency
  write plus a depth repair — O(1) for an edge arriving parent-before-child, and
  proportional to the *descendants* of the node `raise-depth` lifts for one arriving
  child-first, so that order is quadratic in the hierarchy and `*defer-depths?*` is
  the trade written for it.  Reads are memoized per closure
  *generation* (bumped on every edge change), so a shallow hierarchy — where the
  reachable subgraph is tiny — still answers each repeat read in O(1).

  - **Insertion** records the edge in `:fwd` / `:rev` and, so cycle checks stay
    cheap, maintains a topological `:depth` potential (`edge x→y ⇒ depth[x] >
    depth[y]`).  No closure is touched.
  - **Deletion** drops the edge from the adjacency and prunes any node left with no
    edge.  Depths are left as loose upper bounds — a deletion only relaxes the
    ordering, so the invariant survives untouched.
  - **Cycle safety.** `genl?` / `sees?` answer reachability with an early-exit walk
    pruned by `:depth`: a real path `x → … → y` has strictly decreasing depth, so
    `depth[x] ≤ depth[y]` rejects the pair in O(1).  `wff` rejects `genl` /
    `genlCx` cycles up front, so the closures stay acyclic; `reach` guards with a `seen` set
    regardless, so a stray cycle terminates rather than being subtly wrong.

  `closures` (the from-scratch materialized build) survives as the **reference
  implementation** the on-demand reads are tested against — the oracle test in
  `taxonomy_test` compares `genls` / `specs` for every node against it after every
  random edit.

  Context semantics: (genlCx Sub Super) means Sub *sees* Super's assertions, so a
  context K sees a sentex in context Y iff Y is in genls-of-contexts(K).

  ## Edges are supported, and support is belief-sensitive

  Every sentex that asserts an edge is a **supporter**, stored in the index's supporter
  families under the key `[:genl a b]` (`post!`) with its context; a nil
  context means the writer had none to record (a probe) and the edge constrains
  everywhere.  A relation is `{:edges #{[a b]} :edge-ctxs {} :fwd {} :rev {} :nodes #{}
  :depth {} :gen n}`, and `:edges` is the *active* set the closures are computed from — an
  edge with no believed supporter is not in it.  That distinction is what keeps three
  things right:

  - **Belief.** A defeated `(genl dog animal)` leaves the closure, so `isa?` cannot
    outrun belief.  Matching is belief-sensitive everywhere in the engine, the
    taxonomy included; `refresh-beliefs` reconciles after a relabel.
  - **Reference counting.** The same edge asserted in two contexts is two sentexes.
    Retracting one must not remove the edge while the other still asserts it.
  - **Idempotence.** Re-asserting an edge that is already active is a no-op —
    `activate` returns early rather than touching the adjacency at all.

  ## Equality is the third supported relation, and it is not a partial order

  `rewriteOf` / `sameAs` / `equals` all feed one **equivalence** closure, so it is
  stored as a partition — member → class, class → members and representative —
  rather than as up/down closures.  It shares the supporter discipline above, keeping its
  own `:support` map, and nothing else: insertion is a union, and deletion can *split* a
  class, which no union-find can undo, so it rebuilds the affected class from its
  surviving edges.
  See the section below and docs/equality.md.

  The same belief discipline reaches the six flat caches too — `disjoint`, the
  disjoint metatypes and their members, the sibling-disjoint marks, the predicate
  properties, `inverse`, and the declared arities.
  Their supporters are stored in the same families under each entry's `[kind key]`, and
  `refresh-beliefs` reconciles each cache entry against belief exactly as
  `refresh-relation` does for genl — an entry is active iff some supporter is stored
  *and* believed.  So a
  defeated `(disjoint dog cat)` stops constraining, a defeated `(functional P)` stops
  merging, and a defeated `(inverse P Q)` stops answering the swapped goal, the way a
  defeated genl edge leaves the closure.  See docs/taxonomy.md."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- term-key
  "A total order on terms keyed on **content only**.  Representative choice may never
  key on a handle: handles are allocated in assertion order, so that would smuggle
  arrival order back into belief (docs/nmtms.md — it was a real bug in the Nixon
  diamond).  The class name is a second key so a symbol and a string that print
  alike still order deterministically."
  [t]
  (if (nil? t) ["" ""] [(str t) (.getName (class t))]))

(defn- term-min [terms]
  ;; keyed once per term, not twice per comparison: `term-key` allocates two strings, so
  ;; a plain reduce rebuilds it on both operands at every step.  Tie keeps the later, as
  ;; the reduce did (a tie is two terms that print alike under the same class anyway).
  (second (reduce (fn [a b] (if (neg? (long (compare (first a) (first b)))) a b))
                  (map (fn [t] [(term-key t) t]) terms))))

(defn- reach-all
  "Reflexive-transitive reachable set from every node of `starts` over adjacency `adj` (a
  fn node → neighbours).  Guards with a `seen` set, so a cyclic `adj` terminates, and
  each node is expanded once however many starts reach it."
  [starts adj]
  (loop [seen (transient (set starts)), stack (vec starts)]
    (if-let [n (peek stack)]
      (let [fresh (remove #(get seen %) (adj n))]
        (recur (reduce conj! seen fresh) (into (pop stack) fresh)))
      (persistent! seen))))

(defn- reach
  "Reflexive-transitive reachable set from `start` over adjacency `adj`: `reach-all` from
  one node."
  [start adj]
  (reach-all [start] adj))

(defn- reachable?
  "Is `tgt` in the reflexive-transitive reach of `src` over adjacency map `adj`,
  given topological potentials `depth` and the component map `scc`?

  `depth` is a potential over the **condensation** — the DAG of strongly connected
  components — so it obeys `edge x→y ⇒ depth[x] ≥ depth[y]`, strictly when `x` and
  `y` lie in different components and by equality inside one.  `scc` maps a node to
  its component's representative, and holds an entry **only for a node in a
  non-trivial component**; an acyclic relation (which `genl` always is, and
  `genlCx` usually is) has an empty one and pays a nil check.

  Three O(1) consequences make this cheap in the overwhelmingly common case:

  - same component ⇒ mutually reachable, by definition.  No walk at all.
  - otherwise a real path `src → … → tgt` must leave `src`'s component, so it
    strictly descends at least once: `depth[src] ≤ depth[tgt]` ⇒ unreachable.  For a
    hierarchy built roughly parent-before-child — the load order of a taxonomy — the
    node being checked against is always shallower, so the pair is rejected outright.
  - during the walk, a neighbour *below* `tgt`'s depth cannot lie on a path to it, and
    neither can one *level* with it in a different component (that path would have to
    descend too), so both are pruned — and a neighbour level with it in `tgt`'s own
    component answers true outright.

  Depths are only ever grown, never shrunk (deletion leaves them loose), so the
  invariant — hence soundness — holds regardless of edit history.  A missing depth is
  treated as `-1` (below everything): a non-node `tgt` is unreachable, a non-node
  `src` reaches only itself.

  **`depth` may be nil**, meaning no usable potential: a deferred batch insert whose
  `local-lift` broke an edge above it, or an edge that closed a cycle, leaves the
  relation `:loose?` until `restore-depths` runs.  The pruning is then dropped and the
  walk is plain — the same answer, paid for by visiting `src`'s whole reach instead of
  a prefix of it.  Pruning with a potential that is no longer sound would answer
  *false* for a real path, which here means `genl?` silently losing a subtype and
  `sees?` silently losing a context.

  Walking unpruned is **much** more expensive than it looks — on a deep hierarchy it
  is the difference between an O(1) rejection and a full ancestor walk, and `wff` pays
  one per taxonomy edge asserted — so going loose is a last resort, not the deferred
  path's normal state (see `local-lift`)."
  ([src tgt adj depth] (reachable? src tgt adj depth nil))
  ([src tgt adj depth scc]
   (let [ctgt (get scc tgt)]
     (or (= src tgt)
         (and (some? ctgt) (= ctgt (get scc src)))
         (if (nil? depth)
           (loop [seen #{src}, stack [src]]
             (if-let [n (peek stack)]
               (let [nbrs (get adj n)]
                 (if (contains? nbrs tgt)
                   true
                   (let [fresh (into [] (remove seen) nbrs)]
                     (recur (into seen fresh) (into (pop stack) fresh)))))
               false))
           (let [dt (get depth tgt)]
             (and (some? dt)
                  (> (get depth src -1) dt)
                  (loop [seen #{src}, stack [src]]
                    (if-let [n (peek stack)]
                      (let [nbrs (get adj n)]
                        (if (or (contains? nbrs tgt)
                                (and (some? ctgt)
                                     (some #(= ctgt (get scc %)) nbrs)))
                          true
                          (let [fresh (into [] (comp (remove seen)
                                                     (filter #(> (get depth % -1) dt)))
                                            nbrs)]
                            (recur (into seen fresh) (into (pop stack) fresh)))))
                      false)))))))))

(defn- reached-from?
  "`reachable?` answered from the other end: does `src` reach `tgt`, by a walk down from
  `tgt` over the reverse adjacency `radj`?  The walk enters `tgt`'s descendants where
  `reachable?` enters `src`'s ancestors, and the potential prunes the mirror image: a
  descendant not above `src`'s depth, outside `src`'s component, lies on no path from
  `src`.  A nil `depth` walks unpruned."
  [src tgt radj depth scc]
  (let [csrc (get scc src)]
    (or (= src tgt)
        (and (some? csrc) (= csrc (get scc tgt)))
        (let [ds    (get depth src)
              keep? (if (nil? depth)
                      (constantly true)
                      #(when-some [d (get depth %)] (< (long d) (long ds))))]
          (and (or (nil? depth)
                   (and (some? ds) (> (long ds) (long (get depth tgt Long/MAX_VALUE)))))
               (loop [seen #{tgt}, stack [tgt]]
                 (if-let [n (peek stack)]
                   (let [nbrs (get radj n)]
                     (if (or (contains? nbrs src)
                             (and (some? csrc) (some #(= csrc (get scc %)) nbrs)))
                       true
                       (let [fresh (into [] (comp (remove seen) (filter keep?)) nbrs)]
                         (recur (into seen fresh) (into (pop stack) fresh)))))
                   false)))))))

(defn- adjacency [edges]
  (reduce (fn [m [a b]] (update m a (fnil conj #{}) b)) {} edges))

(defn closures
  "Compute {:edges :up :down} from scratch, for a set of [sub super] edges — the
  fully materialized closure this namespace deliberately does *not* keep.

  O(V·(V+E)) — a DFS per node.  This is the **reference implementation**: the
  on-demand `genls` / `specs` reads must answer exactly as it would, and the oracle
  test in `taxonomy_test` checks that node by node over random graphs."
  [edges]
  (let [nodes (into #{} (mapcat (fn [[a b]] [a b])) edges)
        adj   (adjacency edges)
        up    (into {} (map (fn [n] [n (reach n adj)])) nodes)
        down  (reduce (fn [m [n ups]]
                        (reduce (fn [m2 u] (update m2 u (fnil conj #{}) n)) m ups))
                      {} up)]
    {:edges (set edges) :up up :down down}))

;; A relation's supporters are not held here: the index's supporter families hold them,
;; keyed by the edge (`[:genl a b]`) and by the handle (`[:tax-installs h]`, the edges it
;; installs), and `:supporters` caches what the reconcile reads.  The second family is
;; what lets `refresh-beliefs` read the edges a settle could have moved **off the moved
;; region** rather than off the relation (`moved-keys`): belief moves by handle, and only
;; an edge some moved handle supports can have changed its believed-supporter set.
;;
;; `:dirty` is the other half of that scope, and it exists because the edge writers are
;; **belief-blind**: `add-edge` and `del-edge` run on the assert/retract path, where no
;; `believed?` is in hand, so they recompute `:edge-ctxs` from every stored supporter
;; rather than from the believed ones.  On an edge with a single supporter that is exact.
;; On a shared edge it is a superset — a disbelieved supporter's context reads as
;; asserting — and only a reconcile can narrow it.  So a writer leaving a shared edge
;; behind names it here, and the next reconcile takes it whether or not belief moved
;; there.  A superset is the safe interim reading (a scoped read sees an edge it should
;; not, never misses one it should), and the set stays proportional to the edits: the
;; single-supporter edge that is nearly every edge, and all of a bulk load, never enters
;; it.
;; Beside the edge set, `:edge-ctxs {[a b] #{ctx}}` is **derived context state**, a
;; function of the supporters and belief the way `:edges` is: the supporting contexts of each
;; *active* edge (keys ≡ `:edges`); nil in the set marks a supporter with no recorded
;; context, which constrains everywhere.  `:gen` bumps whenever an entry moves, not only
;; when an edge appears or disappears — a scoped closure read is a function of these, so
;; they retire the read memo exactly as the edge set does.  The contexts that state a
;; supporter at all are read from the index (`census-in`).
;;
;; `:depth` is a potential over the **condensation**, and `:scc` is what makes it one:
;; a node in a strongly connected component maps to that component's representative
;; (`term-min`, so the choice is content-keyed and cannot depend on arrival order).
;; Only a node in a *non-trivial* component has an entry, so an acyclic relation
;; carries an empty map and reads exactly as it did.  `:scc-members` is its inverse,
;; representative → members, written wherever `:scc` is, so a repair that moves one
;; component reads that component's members and not the whole map.
(defn- empty-relation []
  {:dirty #{} :edges #{} :edge-ctxs {}
   :fwd {} :rev {} :nodes #{} :depth {} :scc {} :scc-members {} :gen 0
   ;; `note-move`'s log
   :moves (sorted-map) :move-gen {}})

;; The equality partition, defined here only so `create-taxonomy` can name it; its
;; machinery is the "equality" section further down.
(defn- empty-equality []
  {:support {} :handles #{} :handle-edge {} :out #{} :edges #{} :edge-idx {} :edge-prefs {}
   :class {} :members {}})

(def closure-memo-limit
  "How many terms, summed over the closures it holds, one taxonomy's closure cache keeps
  before it evicts the least recently used — the shipped default the cache profile scales
  and the memory guard shrinks.  A closure is a persistent set, tens of bytes a term, so
  this is on the order of a few gigabytes.  It is a bound rather than the vocabulary
  because a large import can hold millions of types with closures of hundreds to
  thousands, and an unbounded memo of every type's supertypes grows with that product."
  50000000)

(defn- closure-lru
  "A taxonomy's empty closure cache: weighted by the terms each closure holds (a closure
  needs set by its contexts, a flag by one), bounded through the cache profile."
  []
  (assoc (caches/weighted-lru (caches/limit-thunk :taxonomy-closures closure-memo-limit)
                              (fn [v] (inc (if (coll? v) (count v) 0))))
         ;; the up-closures `closure-of` built from their parents' (`reach-by-parents`), and
         ;; those that fell back to a walk: a parent evicted mid-build, or a cycle `:scc`
         ;; has not recorded
         :walks (java.util.concurrent.atomic.AtomicLongArray. 2)))

(defn- private-index
  "An empty in-memory index store, holding the supporter families of a raw taxonomy."
  []
  (kv/->KvIndexStore (mem/->MemoryKvBackend (atom {}))))

(def supporter-cache-limit
  "How many entries the supporter cache (`:supporters`) holds, keys and handles together,
  before it is cleared wholesale: the shipped default the cache profile scales."
  1000000)

(def ^:private empty-supporters
  "The supporter cache with nothing held: `{:by-key {k {handle ctx}} :by-handle {handle
  #{k}}}`."
  {:by-key {} :by-handle {}})

;; The supporters of a taxonomy key are the index's supporter families
;; (`post!`), and `:supporters` caches the two reads the reconcile makes per
;; moved handle and per touched key.  An entry holds the whole stored answer: the
;; writers drop the entries their post moves and read the family afresh, and the
;; reconcile (`recover`'s included) fills an entry it misses.  A reader outside a write
;; reads through without filling.  Past `supporter-cache-limit` the cache is cleared
;; wholesale.

(defn- supporters-of
  "Taxonomy key `k`'s stored supporters in taxonomy state `t`, as `{handle ctx}`: the
  cache's entry, else the supporter family."
  [t k]
  (or (get-in t [:supporters :by-key k]) (reads/as-stored-supporters-global (:index t) k)))

(defn- keys-of
  "The taxonomy keys stored handle `h` installs, as a set: the cache's entry, else the
  supporter family."
  [t h]
  (or (get-in t [:supporters :by-handle h]) (reads/as-stored-installed-keys (:index t) h)))

(defn- hold
  "`t` with `v` cached as `side`'s (`:by-key` or `:by-handle`) entry for `k`, the cache
  cleared first when it holds the cache profile's bound on `supporter-cache-limit`."
  [t side k v]
  (let [c (:supporters t)
        c (if (>= (+ (count (:by-key c)) (count (:by-handle c)))
                  (long (caches/limit-of :taxonomy-supporters supporter-cache-limit)))
            empty-supporters
            c)]
    (assoc t :supporters (assoc-in c [side k] v))))

(defn- held-supporters
  "`[t' sup]`: key `k`'s supporters read through the cache, with `t'` holding them."
  [t k]
  (let [sup (supporters-of t k)]
    [(cond-> t (not (contains? (get-in t [:supporters :by-key]) k)) (hold :by-key k sup)) sup]))

(defn- held-keys
  "`[t' ks]`: the keys handle `h` installs read through the cache, with `t'` holding a
  non-empty answer."
  [t h]
  (if-let [ks (get-in t [:supporters :by-handle h])]
    [t ks]
    (let [ks (reads/as-stored-installed-keys (:index t) h)]
      [(cond-> t (seq ks) (hold :by-handle h ks)) ks])))

(defn- drop-held
  "`t` with the cached entries for key `k` and handle `h` dropped: a writer's post moved
  them."
  [t k h]
  (-> t
      (update-in [:supporters :by-key] dissoc k)
      (update-in [:supporters :by-handle] dissoc h)))

(defn supporters
  "Taxonomy key `k`'s stored supporters, believed or not, as `{handle ctx}`: `k` is
  `[:genl a b]`, `[:genlCx a b]` or a flat-cache key (`[:disjoint #{a b}]`, `[:prop kind
  pred]`, …)."
  [tax k]
  (supporters-of @tax k))

(defn create-taxonomy
  "A KB's taxonomy: one atom holding the cached relations, plus a **watch** bumping
  `observe/note-change` on every write to it.

  The clock is what a structure derived from the taxonomy — a qualitative constraint
  network reads `context-up` and the `genl` spec closure — stamps itself with.  A watch
  rather than a bump per mutator, because there are two dozen of those and the whole
  point of a clock is that no write can forget it.  `detached-copy` deliberately carries
  no watch: its purpose is to be mutated where nothing learns of it.  The two side atoms
  need none either: no writer writes them, and each entry is keyed or stamped by the
  relation's own `:gen` or, for a read of supporter belief, by the change clock."
  []
  (doto
   (atom {:genl (empty-relation) :genlCx (empty-relation)
          :equality (empty-equality)
          :disjoint #{} :disjoint-index {} :disjoint-metatypes #{} :metatype-members {}
          :sibling-disjoint #{} :sib-exception-index {}
          :covers {} :cover-parts {} :partitions #{}
          :props {} :inverse {} :genl-inverse-down {} :genl-inverse-up {} :arity {} :functional-in-arg {} :commuting {}
          :cache-dirty #{} :cache-ctxs {}
          ;; The supporter cache (`supporters-of`), over the index's supporter families
          :supporters empty-supporters
          ;; The index store the supporter families are posted to and read from
          ;; (`post!`).  A raw taxonomy holds a private in-memory one and
          ;; `:raw?`; `install-index!` sets the KB's, where `census-in` also reads the
          ;; contexts stating a supporter.
          :index (private-index) :raw? true
          ;; A KB installs two read-only callbacks after construction: whether any
          ;; supporter needs exception-aware scoping, and whether one supporter is
          ;; effective from a concrete reader context. Raw taxonomies (the unit-test
          ;; and what-if surface) install neither and retain the original context-only
          ;; path byte-for-byte.
          :supporter-filter-active? nil :supporter-visible? nil
          :network-filter-active? nil :network-visible? nil :supporter-reaches? nil
          ;; how many times `clear-relations!` rebuilt the relations, whose `:gen`s it
          ;; restarts at 0 (`relation-epoch`)
          :epoch 0
          ;; Oriented schematic rewrite rules (docs/equality.md, symbolic equational
          ;; reasoning).  `:rewrite-support` records every asserted rule keyed by its
          ;; equation handle; `:rewrite-active` is the believed subset `refresh-beliefs`
          ;; keeps in sync — the same support/active discipline as the equality
          ;; partition.  Retraction is the only write that takes a schematic equation
          ;; out of belief (docs/equational.md, "The write path").
          :rewrite-support {} :rewrite-active {}
          ;; A side atom of the small memoized reads beside the closures — the
          ;; exception-filter gate and the exception-filtered context down-sets — keyed
          ;; per relation, under that relation's `:gen`, and stamped with the change
          ;; clock.  Kept *beside* the main map, not inside it, so a read that memoizes
          ;; never contends with the writer on the main atom and never mutates the
          ;; snapshot a concurrent reader is holding.  Stale entries are ignored on read
          ;; and overwritten on the next miss.
          :closure-memo (caches/tallied (atom {}) [:T7])
          ;; The closures themselves, global and scoped, in one weighted LRU
          ;; (`closure-lru`), keyed with the relation's `:gen` so an edge change retires
          ;; them by never asking for them again; a scope that reads supporter belief
          ;; carries the change clock (`relation-scope`), so any write retires its
          ;; closures the same way.  A side object for the memo's reasons.
          :closure-lru (closure-lru)
          ;; The content-ordered rewrite rules (`rewrite-rules`), memoized as
          ;; `{:for <the :rewrite-active map it sorted> :rules <sorted seq>}`.  A side
          ;; atom for the same reasons as the other two, stamped on the *object* it
          ;; sorted rather than on a counter — see `rewrite-rules`.
          :rewrite-order (atom nil)})
    (add-watch ::change (fn [_ _ _ _] (observe/note-change)))))

(defn install-supporter-visibility!
  "Install the KB-owned visibility callbacks on `tax`.

  `active?` is the cheap whole-KB gate: nil or false while no `except` or placed `defeat`
  is stored, else truthy — and when truthy, the roster's entries, a seq of `[key
  #{target-handle …}]`, which is what lets `relation-filter-active?` ask whether a
  supporter of the relation being read rests on a target (a bare truthy value is honoured
  as \"every relation\").  `reaches?` answers that, given the roster, a view of a
  relation's stored supporters (`supporter-view`) and whether the placed defeats count: they do not for `genlCx`, whose
  supporters rest only on forced-monotonic sentences, which no defeat targets.  Without
  it a target must be a supporter itself.  `visible?`
  answers whether one stored supporter handle is believed and seen from one concrete
  reader context.  `network-active?` and `network-visible?` are the same two reads over
  the network and the `except` roster alone, with no placed `defeat` read: what a
  firing's witness search reads (`*network-belief*`).  Taxonomy remains independent of
  the JTMS and exception grammar; the KB owns those facts and supplies the reads after
  its mutually-referential parts exist."
  ([tax active? visible?] (install-supporter-visibility! tax active? visible? active? visible? nil))
  ([tax active? visible? network-active? network-visible? reaches?]
   (swap! tax assoc :supporter-filter-active? active? :supporter-visible? visible?
          :network-filter-active? network-active? :network-visible? network-visible?
          :supporter-reaches? reaches?)
   tax))

(defn install-index!
  "Install the KB's index store on `tax`: the supporter families are posted to it and
  read from it, and `census-in` reads the contexts that state a supporter there."
  [tax index]
  (swap! tax assoc :index index :raw? false)
  tax)

(defn detached-copy
  "The current taxonomy state in a fresh atom, for a what-if probe: mutate the copy,
  read its closures, and the real taxonomy never learns any of it.

  The `:closure-memo` must be the copy's **own** — it is a side atom, so copying the
  map alone would share it by reference, and the probe's reads would write entries
  stamped with the probe's bumped `:gen` into the live memo.  Those entries are not
  merely wasted: the moment the live relation's gen catches up (its next real edge
  change), they answer real reads with closures computed over the probe's
  hypothetical edge — and a *second* probe copies the live gen, bumps to the same
  number, and reads them as its own.  `:closure-lru` is a side object with the same
  stamp discipline, so it gets the same isolation.

  `:rewrite-order` is stamped on the map object it sorted rather than on a number, so a
  probe's entry could never be *mistaken* for the live one's — but a shared atom would
  still have the two evicting each other's single slot on every alternation, and a side
  atom belonging to whoever reads it is the rule here rather than the exception.

  `:index` is a fork of the original's (`mount/fork-families`), so the supporters a probe posts land
  where only the copy reads them."
  [tax]
  (let [t @tax]
    (atom (assoc t :index (mount/fork-families (:index t))
                 :closure-memo (atom {}) :closure-lru (closure-lru) :rewrite-order (atom nil)))))

;; ---- on-demand closures, memoized per generation ------------------------
;;
;; `:fwd` / `:rev` hold direct adjacency; the reflexive-transitive closure is
;; computed — up from the parents' closures (`reach-by-parents`), down by `reach` — and
;; cached in `:closure-lru` under the relation's current `:gen`.  Every edge change bumps `:gen`, which retires every closure of that
;; relation without touching them — a read keys on the new gen, misses, and recomputes,
;; and the stale entries are the coldest the LRU holds.  This keeps a repeated read on a
;; shallow hierarchy O(1) while never paying to materialize a deep one, and holds what a
;; deep one does materialize to `closure-memo-limit`.
;;
;; **A membership test does not need a closure.**  `genl?` / `sees?` answer through the
;; depth-pruned `reachable?`, which rejects most pairs in O(1) and holds nothing; a caller
;; that only asks whether one type is above another asks them, and a closure is read only
;; by a caller that walks or intersects the set (`separation-frame`, `covers-over`).

(defn- reach-by-parents
  "The up-closure of `node`, built as `C ∪ ⋃ closure(p)` over the parents `p` outside its
  component `C`, bottom-up from the nearest ancestors `held` answers.  Each closure it
  builds is handed to `hold!` under its component's representative — one entry for a
  component of thousands, which every member reads — so the ancestors many types share
  are built once, and a type's closure shares structure with its largest
  parent's rather than copying it.  `reach` instead climbs the whole ancestry again for
  every type, which is the clash pass's cost on a deep taxonomy.

  Components come from `scc` (node → representative, non-trivial components only), so the
  walk is over the condensation, which is acyclic.  `scc` never names a false component —
  an edge removal repairs it eagerly — but a deferred cycle-closing edge can leave a real
  one out.  Such a cycle brings a unit back to the top of the stack still waiting on a
  parent, and the build answers nil, as it does when a parent's closure `held` answered
  was evicted before it was read; the caller walks instead.

  With a transducer `xf` other than nil, each answer is the union of what `xf` makes of
  the closure's terms, by the same recurrence: what `xf` makes of a union is the union of
  what it makes of the parts (`genls-global-union`).

  `walk`, when given, answers a unit with two or more parents not yet built, in place of
  building them: a whole closure built from two parents costs the smaller parent's
  closure, so building every ancestor of one cold type costs the sum of their closures,
  quadratic on a braid, where one walk costs the type's own."
  [node adj scc held hold! xf walk]
  (let [unit    #(get scc % %)
        members (fn [u] (if (contains? scc u)
                          (reach u (fn [x] (filter #(= u (get scc %)) (adj x))))
                          #{u}))
        parents (fn [ms u] (into #{} (comp (mapcat adj) (map unit) (remove #(= u %))) ms))]
    (loop [stack (list (unit node)), built (transient {}), entered (transient #{})]
      (if-let [u (first stack)]
        (if (get built u)
          (recur (rest stack) built entered)
          (let [ms      (members u)
                ps      (parents ms u)
                pending (remove #(or (get built %) (held %)) ps)]
            (cond
              (and (seq pending) (get entered u)) nil
              (and (seq pending) walk (next ps))
              (let [cl (walk u)]
                (hold! u cl)
                (recur (rest stack) (assoc! built u cl) entered))
              (seq pending) (recur (into stack pending) built (conj! entered u))
              :else
              (let [pcs (mapv #(or (get built %) (held %)) ps)]
                (when (every? some? pcs)
                  (let [big (reduce (fn [a b] (if (> (count b) (count a)) b a)) #{} pcs)
                        ms  (if xf (sequence xf ms) ms)
                        ;; an empty answer adds nothing, and skipping it keeps an answer
                        ;; with nothing new identical to its parent's
                        cl  (reduce (fn [acc c] (if (or (identical? c big) (empty? c)) acc (into acc c)))
                                    big pcs)
                        cl  (if (seq ms) (into cl ms) cl)]
                    (hold! u cl)
                    (recur (rest stack) (assoc! built u cl) entered)))))))
        (get built (unit node))))))

(defn- closure-of
  "The reflexive-transitive reach of `node` in relation `rel-key`, direction
  `dir-key` (`:fwd` up, `:rev` down), memoized per generation in the taxonomy's weighted
  LRU.  `tax` is the taxonomy atom.

  An up-closure is built from its parents' (`reach-by-parents`) and held under the
  representative of the component `node` sits in, which every member shares; a
  down-closure is walked, since building it that way would hold the down-closure of every
  type under a broad one."
  [tax rel-key dir-key node]
  (let [t    @tax
        rel  (get t rel-key)
        lru  (:closure-lru t)
        key  (fn [n] [rel-key (:gen rel) dir-key n])
        adj  #(get (dir-key rel) %)
        up?  (= dir-key :fwd)
        node (if up? (get (:scc rel) node node) node)]
    (or (caches/lru-get lru (key node))
        (let [t0 (System/nanoTime)
              ^java.util.concurrent.atomic.AtomicLongArray walks (:walks lru)
              v  (or (when up?
                       (let [v (reach-by-parents node adj (:scc rel)
                                                 #(caches/lru-get lru (key %))
                                                 #(caches/lru-put! lru (key %1) %2)
                                                 nil #(reach % adj))]
                         (when walks (.incrementAndGet walks (if v 0 1)))
                         v))
                     (caches/lru-put! lru (key node) (reach node adj)))]
          (caches/spent (:tally lru) t0)
          (caches/compare-retired (:tally lru) [rel-key dir-key node] (:gen rel) v)
          v))))

;; ---- scoped reads: the visibility filter over the same closures ----------
;;
;; A read asked from context K uses exactly the edges K can see — an edge counts
;; iff some believed supporter asserts it from a context in K's genlCx
;; ancestor set (`:edge-ctxs`), the same filter `matches-visible` applies to facts.
;; The genlCx closure itself is never filtered: visibility scoped by
;; visibility would be circular, and `forced_decontextualized_predicate` already
;; forces every genlCx edge universal.
;;
;; The filter is keyed on `vis = up(K) ∩ ctxs`, where `ctxs` is the relation's
;; context census: the contexts that state a supporter (`census-in`).  Since every
;; edge's context set is a subset of `ctxs`, two contexts with the same `vis` induce the
;; identical filtered edge set — so `vis` is the memo key, a function of the answer
;; rather than a proxy for it.  nil `vis` means the answer cannot differ from the global
;; one (no context given, or K sees every asserting context): the caller takes the
;; global path and the global memo slot.

(def edge-installing-functors
  "The functors of the sentences `installed-edges` reads a `genl` edge off."
  '#{genl covering separating partition})

(def ^:private flat-functors
  "The functors whose declarations the flat caches record, read off their storage in
  `vaelii.impl.predicates`: every property, mark, keyed pair other than equality, roster,
  per-position and commuting declaration.  A disjoint metatype's members are stated under
  the metatype, which is data, so `census-functors` adds those."
  (into #{} (comp (filter (fn [[_ spec]]
                            (let [[kind target] (:storage spec)]
                              (and (contains? #{:prop :mark :keyed-pair :roster :pred-position
                                                :pred-commuting}
                                              kind)
                                   (not= :equality target)))))
                  (map first))
        pr/entries))

(defn- census-functors
  "The functors whose stored facts state a supporter of `rel-key`: `:genl`, `:genlCx`, or
  `:flat` for the flat caches, whose functors include each disjoint metatype with a member."
  [t rel-key]
  (case rel-key
    :genl   edge-installing-functors
    :genlCx '#{genlCx}
    :flat   (into flat-functors (keys (:metatype-members t)))))

(defn- of-relation?
  "Does taxonomy key `k` belong to `rel-key`: `:genl`, `:genlCx`, or `:flat` for every
  flat-cache key (`kv/key-relation`)?"
  [rel-key k]
  (= rel-key (kv/key-relation k)))

(defn- raw-supporters
  "`{k {handle ctx}}` for every key of `rel-key` with a stored supporter in a raw
  taxonomy's private store: a walk of the store (`reads/as-stored-supporter-map`)."
  [t rel-key]
  (into {} (filter #(of-relation? rel-key (key %))) (reads/as-stored-supporter-map (:index t))))

(defn- support-census
  "The contexts every stored supporter of `rel-key` is stated in, nil excluded: the census
  of a raw taxonomy, whose store holds no predicate extent."
  [t rel-key]
  (into #{} (comp (mapcat vals) (remove nil?)) (vals (raw-supporters t rel-key))))

(defn- extent-handles
  "Every stored handle of a fact of one of the functors `fs`, either polarity."
  [t fs]
  (into #{} (mapcat #(reads/as-stored-with-functor (:index t) %)) fs))

(defn- relation-supporters
  "Every handle stored as a supporter of a `rel-key` key (`of-relation?`): a raw
  taxonomy's walk, else the handles of `census-functors`' facts that install one."
  [t rel-key]
  (if (:raw? t)
    (into #{} (mapcat (comp keys val)) (raw-supporters t rel-key))
    (into #{} (filter (fn [h] (some #(of-relation? rel-key %) (keys-of t h))))
          (extent-handles t (census-functors t rel-key)))))

(defn- supporter-total
  "How many stored facts state a supporter of `rel-key`, a count that moves whenever a
  supporter is stored or removed: one count read per `census-functors` functor, which
  counts either polarity, or a raw taxonomy's walk."
  [t rel-key]
  (if (:raw? t)
    (transduce (map (comp count val)) + 0 (raw-supporters t rel-key))
    (transduce (map #(reads/stored-count-with-functor (:index t) %)) + 0
               (census-functors t rel-key))))

(defn- supporter-view
  "What the reach callback reads of `rel-key`'s stored supporters
  (`install-supporter-visibility!`): `:rel`, `rel-key`; `:supports?`, whether a handle is one; `:count`, a
  count of them (`supporter-total`); `:handles`, a thunk answering every one."
  [t rel-key]
  {:rel       rel-key
   :supports? (fn [h] (boolean (some #(of-relation? rel-key %) (keys-of t h))))
   :count     (supporter-total t rel-key)
   :handles   (fn [] (relation-supporters t rel-key))})

(defn- census-in
  "`[in all?]`: the contexts of the set `ctxs` that state a supporter of `rel-key`
  (`census-functors`), and whether `ctxs` holds every context that states one.  Read from
  the predicate extents in the installed index store (`install-index!`): per functor, one
  child count and, when it is not zero, min(|contexts stating it|, |ctxs|) membership
  probes.  The extent
  holds every stored fact of the functor, either polarity and whatever its belief, so the
  census is a superset of the contexts of the believed supporters, which is all a scoped
  read needs.  A raw taxonomy reads `support-census`."
  [t rel-key ctxs]
  (let [idx (:index t)
        fs  (census-functors t rel-key)]
    (if-some [per (when-not (:raw? t)
                    (let [seen (mapv #(reads/as-stored-contexts-with-functor idx % ctxs) fs)]
                      (when (every? some? seen) seen)))]
      [(into #{} (mapcat first) per)
       (every? (fn [[s n]] (= (count s) n)) per)]
      (let [all (support-census t rel-key)
            in  (into #{} (filter #(contains? ctxs %)) all)]
        [in (= (count in) (count all))]))))

(defn- census-among
  "The contexts of the set `ctxs` that state a supporter of `rel-key` (`census-in`), or nil
  when `ctxs` holds every context that states one."
  [t rel-key ctxs]
  (let [[in all?] (census-in t rel-key ctxs)]
    (when-not all? in)))

(defn- scoped-context?
  "A concrete context to scope by — a symbol that is not a `?var`.  nil and `'?ctx`
  both mean unscoped."
  [context]
  (and (symbol? context) (not (.startsWith (name context) "?"))))

;; Forward declarations: `relation-scope` and `scope-admits-supporter?` reference
;; these before their definitions because the scope machinery sits above the walk
;; but below the closure, creating a mutual dependency.
(declare visible-ctxs context-up sees?)

(def ^:dynamic *network-belief*
  "True while a firing's witness search reads the scoped closures (`chain`'s placement):
  a supporter is read at its network label and through the `except` roster, and no
  placed `defeat` is read (`:network-filter-active?`, `:network-visible?`).  The scope
  key carries the callback it reads, so the two readings never share a memo entry."
  false)

(def ^:dynamic *search*
  "nil outside a second-route search (`exc/route-answer`), else `:belief` while the search
  answers a belief read and `:visibility` otherwise.  A scope that reads supporter belief
  carries the value in its key, as the effective ancestor set does, so a walk inside a
  search and one outside it never share a memo entry."
  nil)

(defn- roster-fn
  "The whole-KB gate callback the reading in force reads (`*network-belief*`)."
  [t]
  (if *network-belief* (:network-filter-active? t) (:supporter-filter-active? t)))

(defn- visible-fn
  "The supporter callback the reading in force reads (`*network-belief*`)."
  [t]
  (if *network-belief* (:network-visible? t) (:supporter-visible? t)))

(defn- supporter-filter-active?
  "Does this KB currently need supporter-level filtering anywhere?  The whole-KB gate:
  true once any visibility `except`, or for a reader's belief any placed `defeat`, is
  stored, whatever it targets."
  [t]
  (boolean (when-let [active? (roster-fn t)] (active?))))

(defn- targets-supporter?
  "Is a target of a `roster` entry a supporter in `view` (`supporter-view`)?  The reach
  callback of a taxonomy with none installed (`install-supporter-visibility!`), which
  reads every entry whatever `_defeats?`.  An entry's targets may be a delay."
  [roster view _defeats?]
  (boolean (some (fn [e] (some (:supports? view) (force (val e)))) roster)))

(defn- relation-filter-active?
  "Does a scoped read of `rel-key` need supporter-level exception filtering — does some
  supporter of it, or of `genlCx` (whose holes move every reader's ancestor set), rest on
  the target of a stored `except` or placed `defeat` (the reach callback,
  `install-supporter-visibility!`)?

  The whole-KB gate above says an except exists *somewhere*; this one says it reaches
  this relation.  The distinction is exact, not a heuristic: a supporter no except
  targets is visible from a reader iff it is believed, and belief is already what the
  active edge set and `:edge-ctxs` record, so the filtered walk over such a relation
  answers what the context-only walk answers — at the cost of a `supporter-visible?`
  probe per supporter per neighbour, unmemoized.  Without this gate one except on an
  unrelated fact buys a filtered walk per candidate for every `context-down`.

  The roster's targets are what the gate callback returns when truthy
  (`install-supporter-visibility!`, `roster-fn`); an installer returning a bare truthy
  value keeps the whole-KB reading.  Memoized per relation and per reading in the closure
  memo, stamped on the change clock and both relations' generations: the roster, the
  supporters and their justifications move only at a write, which moves the clock."
  [t rel-key]
  (when-let [active? (roster-fn t)]
    (let [cx     (:genlCx t)
          rel    (get t rel-key)
          slot   (if *network-belief* :filter-active-network :filter-active)
          stamp  [(observe/change-clock) (:gen cx) (:gen rel)]
          memo   (:closure-memo t)
          tl     (caches/tally-of memo :T7)
          cached (get-in @memo [rel-key slot])]
      ;; the stamp is read before the roster: a hit reads no index
      (if (= stamp (:stamp cached))
        (do (caches/hit tl) (:active? cached))
        (when-let [roster (active?)]
          (if-not (sequential? roster)
            true
            (let [reach    (or (:supporter-reaches? t) targets-supporter?)
                  cx-view  (supporter-view t :genlCx)
                  rel-view (when (not= rel-key :genlCx) (supporter-view t rel-key))
                  active (caches/recomputed
                          tl (boolean (or (reach roster cx-view false)
                                          (and rel-view (reach roster rel-view true)))))]
              (when cached (caches/compared tl (= active (:active? cached))))
              (swap! memo (fn [mm]
                            (let [e (get mm rel-key)
                                  e (if (= (:gen rel) (:gen e)) e {:gen (:gen rel) :fwd {} :rev {}})]
                              (assoc mm rel-key (assoc e slot {:stamp stamp :active? active})))))
              active)))))))

(defn- scope-admits-supporter?
  "Does `scope` admit supporter `[handle context]`?

  `scope` is the exception-aware map every caller builds: the visible-context set (nil
  means every asserting context), the concrete reader, and the KB-owned supporter
  predicate."
  [{:keys [contexts context supporter-visible?]} handle supporter-context]
  (and (or (nil? supporter-context)
           (nil? contexts)
           (contains? contexts supporter-context))
       (supporter-visible? handle context)))

(defn- relation-scope
  "The scoped-read key for `rel-key` from `context`, or nil for the global fast path.

  With no `except` reaching the relation (`relation-filter-active?`) this is exactly
  `visible-ctxs`'s set/nil answer.  Once one does, it is a map holding the reader's
  exception-filtered ancestor set and the concrete reader, because two readers with the
  same inherited asserting contexts may hide different handles, and the reading
  (`*network-belief*`'s callback, `*search*`) and the change clock, because the walk reads
  each supporter's belief, which any write can move.  A read under the map is held for one
  stretch of the clock under one reading, and equals a fresh read by construction."
  [tax rel-key context]
  (when (scoped-context? context)
    (let [t   @tax
          ;; An exception on genlCx changes which assertion contexts an ordinary
          ;; reader inherits.  genlCx itself starts from the raw ancestor set, and the
          ;; read is stratified with no fixpoint: the excepts in force at a reader are
          ;; those stated in its raw ancestor set, so an edge's visibility reads no
          ;; genlCx edge's visibility, and an edge resting on a genlCx edge an except
          ;; hides there has no second route (`exc/witness-paths`).  Every other
          ;; relation uses the effective ancestor set.
          active? (relation-filter-active? t rel-key)
          vis (cond
                ;; genlCx declarations are forced into CxUniverse and therefore
                ;; globally visible as declarations. Their *edges* can still be
                ;; excepted per reader, but assertion-context filtering must never
                ;; turn the whole context hierarchy off.
                (= rel-key :genlCx) nil
                ;; the scope below carries the reader, so its key is per reader whatever
                ;; the set, and a supporter's context is in `up(K) ∩ ctxs` iff it is in
                ;; `up(K)`: the exception-filtered ancestor set is the whole filter
                active?             (context-up tax context)
                :else               (visible-ctxs tax rel-key context))]
      (if active?
        {:contexts vis
         :context context
         :supporter-visible? (visible-fn t)
         :search *search*
         :clock (observe/change-clock)}
        vis))))

(defn read-scope
  "The scope a read of `rel-key` from `context` walks under (`relation-scope`), as a key:
  a walk's answer is a function of the scope and not of the context, so two contexts
  whose scopes are equal read one answer."
  [tax rel-key context]
  (relation-scope tax rel-key context))

(defn visible-ctxs
  "`up(K) ∩ ctxs` for relation `rel-key` — the supporting contexts `context` can
  see — or nil when the scoped answer could not differ from the global one: the ancestor
  set from the closure cache, then `census-among`.  Memoized per context in the closure
  memo under the relation's generation, stamped on the change clock and the `genlCx`
  generation, as `context-down-visible` is: the census reads stored extents, which move
  only at a write."
  [tax rel-key context]
  (when (scoped-context? context)
    (let [t     @tax
          gen   (:gen (get t rel-key))
          stamp [(observe/change-clock) (:gen (:genlCx t))]
          memo  (:closure-memo t)
          m     @memo
          cur   (when (= gen (get-in m [rel-key :gen])) (get m rel-key))
          vis   (:visible cur)
          tl    (caches/tally-of memo :T7)]
      (if-some [hit (when (= stamp (:stamp vis)) (find (:by-ctx vis) context))]
        (do (caches/hit tl) (val hit))
        (caches/held-if-settled
         #(caches/recomputed tl (census-among t rel-key (closure-of tax :genlCx :fwd context)))
         (fn [s]
           (swap! memo
                  (fn [mm]
                    (let [e   (get mm rel-key)
                          e   (if (= gen (:gen e)) e {:gen gen :fwd {} :rev {}})
                          vis (:visible e)
                          vis (if (= stamp (:stamp vis)) vis {:stamp stamp :by-ctx {}})]
                      (assoc mm rel-key (assoc e :visible (assoc-in vis [:by-ctx context] s))))))
           s))))))

(defn- ctxs-visible?
  "Does the supporting-context set `cs` reach a reader whose visible set is `visq`
  (a set, or a predicate built from one)?  nil in `cs` is a supporter with no
  recorded context and constrains everywhere."
  [cs visq]
  (boolean (some (fn [c] (or (nil? c) (visq c))) cs)))

(def ^:dynamic *visible-neighbours-cache*
  "An optional atom holding a `{[dir-key vis n] neighbours}` map for a **read-only**
  pass over a still taxonomy.  The closure memo keys whole closures per
  `(node, vis)`, so a shared upper ancestor set is re-filtered under every distinct root
  that walks through it — the cost the closure cache structurally cannot fold and
  the one this one does: each node's edges are context-filtered once per pass, not
  once per walk.  Bound and dropped by the pass, which holds the taxonomy still, so
  the filtered set is gen-stable for its span; nil off such a pass."
  nil)

(defn with-neighbours
  "Run `f` with `nc`, an atom, as the scoped walks' neighbour cache
  (`*visible-neighbours-cache*`) when none is bound: for a caller that asks many scoped
  walks over a taxonomy and a belief that hold still for as long as it keeps `nc`."
  [nc f]
  (if *visible-neighbours-cache*
    (f)
    (binding [*visible-neighbours-cache* nc] (f))))

(defn- pass-held
  "`(read)`, held under `k` in the reading pass's neighbour cache
  (`*visible-neighbours-cache*`) when one is bound: the pass holds the taxonomy and
  belief still, so `k` need name only what the read is asked of."
  [k read]
  (if-let [nc *visible-neighbours-cache*]
    (or (get @nc k)
        (caches/held-if-settled read #(do (swap! nc assoc k %) %)))
    (read)))

(defn- visible-neighbours
  "The `dir-key` neighbours of `n` reachable through an edge some supporter makes
  effective in `scope` — the scoped walk's adjacency. Edge orientation: `:fwd` n→x is edge
  [n x], `:rev` n→x is edge [x n].  Filtered once per pass when a neighbour cache
  is bound (an empty result caches as `[]`, still truthy, so it is not re-walked).
  `rel-key` names the relation of taxonomy state `t` walked: it keys the cache, since one
  pass scopes more than one relation (`:genl` and the `:genlCx` witness walk) and their
  filtered neighbours must not collide on a shared `[dir vis n]`.  A scope carrying
  supporter visibility (a map) reads each edge's stored supporters (`supporters-of`)."
  [t rel-key dir-key scope n]
  (let [nc *visible-neighbours-cache*
        k  (when nc [rel-key dir-key scope n])]
    (or (when nc (get @nc k))
        (let [rel     (get t rel-key)
              ectxs   (:edge-ctxs rel)
              e-of    (if (= dir-key :fwd) (fn [x] [n x]) (fn [x] [x n]))
              pred    (if (map? scope)
                        (fn [x]
                          (let [[a b] (e-of x)]
                            (some (fn [[h c]] (scope-admits-supporter? scope h c))
                                  (supporters-of t [rel-key a b]))))
                        (fn [x] (ctxs-visible? (get ectxs (e-of x)) scope)))
              nbrs  (get (dir-key rel) n)]
          (if nc
            (caches/held-if-settled #(filterv pred nbrs) #(do (swap! nc assoc k %) %))
            (filter pred nbrs))))))

(defn- closure-needs
  "The contexts `node`'s global `dir-key` closure in `rel-key` rests on: for every edge
  out of a node of that closure, the one context supporting it, or `::several` when an
  edge has more than one supporting context or none recorded.  An edge with a supporter
  of no context (nil) is effective everywhere and needs nothing.  So a set scope holding
  every context of the answer makes every edge the closure walks effective, and the scoped
  closure is the global one (`closure-of-vis`).  Memoized per generation in the closure
  LRU, as a set of at most the relation's asserting contexts."
  [tax rel-key dir-key node]
  (let [t   @tax
        rel (get t rel-key)
        lru (:closure-lru t)
        k   [rel-key (:gen rel) ::needs dir-key node]]
    (or (caches/lru-get lru k)
        (let [ectxs (:edge-ctxs rel)
              adj   (dir-key rel)
              e-of  (if (= dir-key :fwd) (fn [m x] [m x]) (fn [m x] [x m]))
              need  (fn [acc m x]
                      (let [cs (get ectxs (e-of m x))]
                        (cond (contains? cs nil) acc
                              (= 1 (count cs))   (conj acc (first cs))
                              :else              (reduced ::several))))]
          (caches/lru-put! lru k
                           (reduce (fn [acc m]
                                     (let [acc (reduce #(need %1 m %2) acc (get adj m))]
                                       (if (= ::several acc) (reduced acc) acc)))
                                   #{} (closure-of tax rel-key dir-key node)))))))

(defn- closure-of-vis
  "`closure-of` over only the edges effective in `scope`, memoized in the same LRU under
  the interned scope key and the relation's `:gen`, so an edge or context change retires
  scoped and unscoped reads together.

  **The answer is a subset of `closure-of`'s** for the same node: the same walk over a
  filtered adjacency.

  **A set scope that sees every context the global closure rests on reads the global
  closure** (`closure-needs`): the same set object, walked and held once, and the LRU
  takes no copy.  A scope carrying `except` visibility (a map) always walks."
  [tax rel-key dir-key node scope]
  (or (when (set? scope)
        (let [r (closure-needs tax rel-key dir-key node)]
          (when (and (not= ::several r) (every? scope r))
            (closure-of tax rel-key dir-key node))))
      (let [t   @tax
            rel (get t rel-key)
            lru (:closure-lru t)
            k   [rel-key (:gen rel) dir-key node scope]]
        (or (caches/lru-get lru k)
            (let [t0 (System/nanoTime)
                  v  (caches/held-if-settled #(reach node (fn [n] (visible-neighbours t rel-key dir-key scope n)))
                                             #(caches/lru-put! lru k %))]
              (caches/spent (:tally lru) t0)
              ;; compared across clock stretches: a map scope's clock goes into the stamp
              (caches/compare-retired (:tally lru)
                                      [rel-key dir-key node (if (map? scope) (dissoc scope :clock) scope)]
                                      [(:gen rel) (:clock scope)] v)
              v)))))

(defn- reachable-filtered?
  "`reachable?` over only the edges effective in `scope` — the sibling walk the scoped
  `genl?` runs.  The depth potential holds over the *global* edge set and the
  visible set is a subset of it, so both prunings stay sound with no per-context
  depths; and because the neighbour set is filtered before the direct-edge test, a
  direct but invisible edge cannot answer true while the transitive paths filter.

  `scc` is read for the same reason `reachable?` reads it, and used for **less**.  The
  potential ranks the condensation, not the graph, so a node on a path to `tgt` is
  either strictly above it or level with it *inside `tgt`'s own component*; pruning on
  `depth > depth[tgt]` alone rejects the second, which is a real path, and the scoped
  read would then deny what the scoped `genls` walking the same edges returns.  What it
  may **not** borrow is `reachable?`'s other half — answering true off a shared
  component.  Mutual reachability there is a fact about the *global* edge set, and the
  whole question here is which of those edges the reader can see, so a component is a
  reason to keep walking and never an answer."
  [src tgt t rel-key scope depth scc]
  (let [nbrs #(visible-neighbours t rel-key :fwd scope %)]
    (or (= src tgt)
        (if (nil? depth)
          (loop [seen #{src}, stack [src]]
            (if-let [n (peek stack)]
              (let [ns (nbrs n)]
                (if (some #(= tgt %) ns)
                  true
                  (let [fresh (into [] (remove seen) ns)]
                    (recur (into seen fresh) (into (pop stack) fresh)))))
              false))
          (let [dt    (get depth tgt)
                ctgt  (get scc tgt)
                ;; Could `x` still lie on a path to `tgt`?  Two spellings of one rule.
                ;; When `tgt` is in no component the level arm cannot fire at all — a
                ;; path into it comes from another component and so descends strictly —
                ;; so the bare comparison is not an approximation there, it is the whole
                ;; rule.  That is every node of an acyclic relation, which `genl` is in
                ;; any KB that has not defeated an edge to get around the check, and this
                ;; predicate runs per neighbour beneath a per-assert caller.  The cost of
                ;; carrying the component arm is then one `scc` lookup per call rather
                ;; than a second comparison per neighbour.
                over? (if (nil? ctgt)
                        (fn [x] (> (get depth x -1) dt))
                        (fn [x] (let [d (get depth x -1)]
                                  (or (> d dt) (and (= d dt) (= ctgt (get scc x)))))))]
            (and (some? dt)
                 (over? src)
                 (loop [seen #{src}, stack [src]]
                   (if-let [n (peek stack)]
                     (let [ns (nbrs n)]
                       (if (some #(= tgt %) ns)
                         true
                         (let [fresh (into [] (comp (remove seen) (filter over?)) ns)]
                           (recur (into seen fresh) (into (pop stack) fresh)))))
                     false))))))))

;; ---- supporter reference counting for the non-transitive caches ---------
;;
;; The six flat caches — `disjoint`, the disjoint metatypes, the sibling-disjoint marks,
;; the predicate properties, `inverse`, and the declared arities — are sets and maps keyed
;; by `[kind key]`.  None of their predicates is forced universal (only `genlCx` is,
;; core_context.clj), so `(disjoint dog cat)` asserted in two contexts is two sentexes
;; folding into one entry, and retracting either must leave the entry while the other is
;; stored and believed.  So an entry is counted by its supporters, which are the index's
;; supporter family under its key (`post!`), exactly as a `genl` edge's are:
;; an entry is active iff some supporter is stored *and* believed, and
;; `refresh-cache-support` reconciles it after every relabel the way `refresh-relation`
;; does the closures.  `cache-install` / `cache-uninstall` are the one definition of an
;; active entry, shared by the assert-time `add-*` / `mark-*` functions and that reconcile.
;;
;; `:cache-ctxs {[kind key] #{ctx}}` mirrors `:edge-ctxs`: the supporting contexts of each
;; entry, written by the writers from every stored supporter and narrowed to the believed
;; ones by `refresh-cache-support`.  No generation rides on it — the flat caches are point
;; lookups, never memoized closures.
;;
;; `:cache-dirty` exists because the writers are belief-blind, as `add-edge` / `del-edge`
;; are: they set `:cache-ctxs` from every stored supporter, and `supported-del` uninstalls
;; only when the last stored supporter is gone.  On an entry with one supporter both are
;; exact; on a shared one a disbelieved co-supporter's context reads as asserting, and
;; losing the last *believed* supporter is an uninstall only a `believed?` can make.  So a
;; writer leaving a shared entry behind names it here and the next reconcile takes it.
;; The first-supporter write that is nearly every write, and all of a bulk load, never
;; enters the set.

(defn- set-cache-ctxs
  "Record `cs` as entry `k`'s supporting contexts, or drop the entry's contexts when `cs`
  is nil, journaling `k` in `:cache-moves` when the contexts move (`flat-moves`)."
  [t k cs]
  (let [old (get-in t [:cache-ctxs k] #{})
        new (or cs #{})]
    (if (= old new)
      (cond-> t (nil? cs) (update :cache-ctxs dissoc k))
      (-> (if cs (assoc-in t [:cache-ctxs k] cs) (update t :cache-ctxs dissoc k))
          (update :cache-moves journal/note [k])))))

(defn- written-supporters
  "`[t' sup]` after a writer's post moved key `k` and handle `handle`: `t` with their
  cached entries dropped, then `k`'s supporters, held — `sole` when the post answered it
  (`post!`), else read through the cache."
  [t k handle sole]
  (let [t (drop-held t k handle)]
    (if sole [(hold t :by-key k sole) sole] (held-supporters t k))))

(defn- support-add
  "`t` after `handle` was posted as a supporter of flat-cache key `k`: the entry's
  contexts read from the stored supporters (`sole`, when the post answered them), and `k`
  dirty when it has more than one."
  [t k handle sole]
  (let [[t sup] (written-supporters t k handle sole)]
    (-> t
        (set-cache-ctxs k (into #{} (vals sup)))
        (cond-> (> (count sup) 1) (update :cache-dirty conj k)))))

(defn- support-drop
  "`[state last-supporter-gone?]` after `handle` was retired from flat-cache key `k`."
  [t k handle]
  (let [[t left] (written-supporters t k handle nil)]
    [(if (seq left)
       (-> t
           (set-cache-ctxs k (into #{} (vals left)))
           ;; the survivors may include one nothing believes, and the caller uninstalls
           ;; only when the last supporter is gone
           (update :cache-dirty conj k))
       (-> t
           (set-cache-ctxs k nil)
           (update-in [:supporters :by-key] dissoc k)
           ;; the entry is gone outright, so it owes no reconcile — and reconciling it
           ;; would write an empty `:cache-ctxs` back under a key nothing supports
           (update :cache-dirty disj k)))
     (empty? left)]))

(defn- supported-add
  "Install-side bookkeeping for `handle`, posted as a supporter of `k`, then `f` to install
  the cache entry."
  [t k handle sole f]
  (-> t (support-add k handle sole) f))

(defn- supported-del
  "Drop `handle`'s support for `k`, applying `f` to remove the cache entry only when
  the last supporter is gone."
  [t k handle f]
  (let [[t' gone?] (support-drop t k handle)]
    (cond-> t' gone? f)))

(defn- inverse-key
  "The flat-cache key for an inverse declaration between `p` and `q`.

  `(hash-set p q)`, never the `#{p q}` literal: a self-inverse `(inverse P P)` is a
  legal declaration — it says `(P a b)` iff `(P b a)`, which is what `symmetric` says —
  and the literal is the checked `RT.set`, so it throws `Duplicate key` rather than
  folding to the one-element set the key wants."
  [p q]
  [:inverse (hash-set p q)])

(defn- declared-pair
  "The two terms a `[:inverse #{p q}]` or `[:disjoint #{x y}]` key names, as `[x y]`.  A
  self-pair — `(inverse P P)`, `(disjoint T T)` — collapses to `#{p}`, so `y` falls back
  to `x`: both directions of the index write then name the same pair, which is
  idempotent.  One extractor for both, because the key is a set in both."
  [s]
  (let [x (first s)] [x (or (second s) x)]))

(defn- index-symmetric
  "Add or drop both directions of a declared symmetric pair in the adjacency at `k`,
  `{term -> #{terms declared to stand in the relation to it}}`.  `:inverse` (predicates)
  and `:disjoint-index` (types) are the two, and this is the whole of what they share:
  the relation is symmetric, so it is written both ways; the entry is a *set*; and an
  emptied entry is dissoc'd rather than left behind, so `get` returning nil means what
  it says — `:arity`'s discipline.

  **A set per term, not one partner.**  Nothing refuses a second `(inverse P R)` beside
  a standing `(inverse P Q)`, so a single-valued entry would answer whichever was
  installed last — making the read a function of assertion order, and `inverses-of`
  decides which hops a transitive walk sees.  Order independence is not negotiable
  (README, \"The model in one page\"), so the relation is stored as the many-to-many it
  is and the readers pick from it by content.  It is also what makes the *drop*
  correct: retiring `(inverse P R)` while `(inverse P Q)` still holds must leave
  `P → #{Q}` rather than clearing `P`."
  [t k s add?]
  (let [[x y] (declared-pair s)
        one   (fn [t a b]
                (if add?
                  (update-in t [k a] (fnil conj #{}) b)
                  (let [left (disj (get-in t [k a] #{}) b)]
                    (if (empty? left)
                      (update t k dissoc a)
                      (assoc-in t [k a] left)))))]
    (-> t (one x y) (one y x))))

(defn cover-parts
  "The `[whole parts]` one `(covering W P …)`, `(separating W P …)` or `(partition W P
  …)` sentence declares, or nil when the stored sentence is not one.

  `reindex` replays **stored** sentexes rather than checked ones, so a foreign or stale
  store reaches the rebuild arm with a two-element row or a non-symbol part, and reading
  it positionally would record a cover over nil.  The guard `special/replay-edge` applies to a
  taxonomy edge, applied to a roster: at least three elements, every one of them a
  symbol, and at least two distinct parts."
  [sentence]
  (let [[_ whole & parts] sentence]
    (when (and (>= (count sentence) 3)
               (symbol? whole)
               (every? symbol? parts)
               (> (count (distinct parts)) 1))
      [whole (distinct parts)])))

(defn installed-edges
  "The `[sub super]` pairs `sentence` adds to the `genl` closure: one for a `(genl sub
  super)` edge with a symbol `sub`, one per part for a `covering`, `separating` or
  `partition` declaration (`special/cover-arms` installs them against the declaration's handle),
  and none for any other sentence.  A part equal to the whole gives no pair, as it
  installs no edge.

  Every reader asking which edges a datum put into or took out of the closure reads
  this, so a cover's edges seed and re-join the rules an asserted edge in the same
  place does (docs/taxonomy.md, \"A cover states the specialization it rests on\")."
  [sentence]
  (when (seq? sentence)
    (case (nm/functor sentence)
      genl (when (and (= 3 (count sentence)) (symbol? (nth sentence 1)))
             [[(nth sentence 1) (nth sentence 2)]])
      (covering separating partition)
      (when-let [[whole parts] (cover-parts sentence)]
        (into [] (comp (remove #{whole}) (map (fn [p] [p whole]))) parts))
      nil)))

(def cover-kinds
  "The three claims a whole-and-parts declaration can make about its roster, as the
  keyword each is cached under.  Closed, and the two questions below are the whole of
  what a reader asks of one: `covering` says the parts leave nothing of the whole
  uncovered, `separating` says no two of them share an instance, and `partition` says
  both.  Two independent claims, so the third kind is their conjunction rather than a
  mechanism of its own."
  #{:covering :separating :partition})

(defn covering-kind?
  "Does a declaration of this kind claim that its parts exhaust the whole?"
  [kind] (not= kind :separating))

(defn separating-kind?
  "Does a declaration of this kind claim that no two of its parts share an instance?"
  [kind] (not= kind :covering))

(defn- cache-install
  "Install the derived cache entry for support key `k` into taxonomy state `t`.  The
  single definition of what an *active* entry is, shared by the assert-time
  `add-*` / `mark-*` functions (via `supported-add`) and by the belief reconcile in
  `refresh-beliefs`.  Idempotent: installing an entry already present is a no-op."
  [t [kind a b]]
  (case kind
    ;; `:disjoint` holds the relation as a set of unordered pairs and `:disjoint-index`
    ;; the same relation as adjacency, because `disjoint?` reads the second: the pair set
    ;; can only be consulted by building a `#{x y}` per candidate, so a walk over two genl
    ;; closures allocates a two-element hash set |as|·|bs| times to ask what is one map
    ;; lookup per supertype here.  Most types are declared disjoint from nothing at all,
    ;; so the outer walk short-circuits on a nil and never touches the inner closure.
    :disjoint (-> t (update :disjoint conj a)                      ; a = #{x y}
                  (index-symmetric :disjoint-index a true))
    :metatype (update t :disjoint-metatypes conj a)                ; a = m
    :member   (update-in t [:metatype-members a] (fnil conj #{}) b)  ; a = m, b = type
    ;; `:sib-disjoint` records only the marked parent; the pairs it separates are
    ;; read off the genl closure (`separation-frame`), never materialized, exactly
    ;; as the metatype clique reads its members.
    :sib-disjoint (update t :sibling-disjoint conj a)              ; a = c
    ;; `:sib-exception` exempts one pair from the separation marks; stored as adjacency
    ;; exactly as `:disjoint-index` is, so the read is one map lookup behind each arm's
    ;; guards.
    :sib-exception (index-symmetric t :sib-exception-index a true)   ; a = #{x y}
    ;; `:cover` is one whole-and-parts declaration: `a` is `[whole parts]` with the parts
    ;; sorted and `b` is the `cover-kinds` keyword saying which of the two claims it
    ;; makes.  Three tables, because three readers ask three different questions of one
    ;; roster: `:covers` answers what covers a whole (the contradiction check),
    ;; `:cover-parts` answers what covers name a part (`CoveringProver`), and
    ;; `:partitions` is the separating subset `separation-frame` walks the way it walks
    ;; `:disjoint-metatypes`.  A declaration enters the first two only if it *covers* and
    ;; the third only if it *separates*, so `separating` reaches the disjointness test and
    ;; no coverage inference, and `covering` the reverse.  The part roster is the member
    ;; set of a `disjoint_metatype` under another name, so it is recorded here and never
    ;; written out as a `(disjoint …)` sentex per pair.
    :cover (let [[whole parts] a]
             (as-> t t'
               (cond-> t' (covering-kind? b)
                       (update-in [:covers whole] (fnil conj #{}) [parts b]))
               (cond-> t' (covering-kind? b)
                       (as-> t'' (reduce (fn [t p] (update-in t [:cover-parts p]
                                                              (fnil conj #{}) [whole parts b]))
                                         t'' parts)))
               (cond-> t' (separating-kind? b) (update :partitions conj [whole parts b]))))
    :prop     (update-in t [:props a] (fnil conj #{}) b)             ; a = prop-kind, b = pred
    :inverse  (index-symmetric t :inverse a true)                  ; a = #{p q}
    ;; a `(genlInverse p q)` edge, held both ways round for the signed closure's two walks
    :genl-inverse (-> t (update-in [:genl-inverse-down b] (fnil conj #{}) a)
                      (update-in [:genl-inverse-up a] (fnil conj #{}) b))      ; a = p, b = q
    :arity    (update-in t [:arity a] (fnil conj #{}) b)                          ; a = pred, b = n
    ;; `:functional-in-arg` is `:arity`'s shape and not `:prop`'s, because the
    ;; declaration carries an integer and a `:props` roster is a set of predicates with
    ;; nowhere to put one.  A predicate may hold several positions at once, so this
    ;; accumulates rather than replacing — `(functionalInArg P 2)` and
    ;; `(functionalInArg P 3)` are two constraints, both live.
    :functional-in-arg (update-in t [:functional-in-arg a] (fnil conj #{}) b)      ; a = pred, b = n
    ;; `:commuting` is `:functional-in-arg`'s shape over a richer value: `b` is a group
    ;; descriptor — `[:rest f]` for `(commutativeInArgAndRest P f)`, `[:args [p1 p2 …]]`
    ;; for `(commutativeInArgs P p1 p2 …)`.  One predicate may carry several groups at
    ;; once, so this accumulates: `(commutativeInArgs P 1 2)` and `(commutativeInArgs P
    ;; 3 4)` are two independent permutation licences, both live.  `commutative` reaches
    ;; this table too: it is a `:props` mark *and* a group, and its arm installs `[:rest 1]`
    ;; here beside the prop rather than deriving `(commutativeInArgAndRest P 1)` through a
    ;; rule (`special/arms` says why the derivation went).
    :commuting (update-in t [:commuting a] (fnil conj #{}) b)))                    ; a = pred, b = group

(defn- cache-uninstall
  "Remove the derived cache entry for support key `k` — the exact inverse of
  `cache-install`.  This is the **belief** removal: plain and reversible, so a
  defeated declaration drops out and a revived one returns.  Retracting the *last*
  supporter of a metatype does more (its members and their support go too — see
  `forget-metatype`), but that is teardown of the mark itself, not what belief toggles.
  Idempotent."
  [t [kind a b]]
  (case kind
    :disjoint (-> t (update :disjoint disj a)
                  (index-symmetric :disjoint-index a false))
    :metatype (update t :disjoint-metatypes disj a)
    :member   (update-in t [:metatype-members a] (fnil disj #{}) b)
    :sib-disjoint (update t :sibling-disjoint disj a)
    :sib-exception (index-symmetric t :sib-exception-index a false)
    ;; The exact inverse of the install, with the emptied-key discipline `:arity` and
    ;; `:commuting` follow: a part whose last cover left must not linger as a key mapping
    ;; to `#{}`, since `covers-naming` gates on the entry being present.
    :cover (let [[whole parts] a
                 drop-in (fn [t path v]
                           (let [left (disj (get-in t path #{}) v)]
                             (if (seq left)
                               (assoc-in t path left)
                               (update-in t (pop path) dissoc (peek path)))))]
             (as-> t t'
               (cond-> t' (covering-kind? b) (drop-in [:covers whole] [parts b]))
               (cond-> t' (covering-kind? b)
                       (as-> t'' (reduce (fn [t p] (drop-in t [:cover-parts p] [whole parts b]))
                                         t'' parts)))
               (cond-> t' (separating-kind? b) (update :partitions disj [whole parts b]))))
    :prop     (update-in t [:props a] (fnil disj #{}) b)
    :inverse  (index-symmetric t :inverse a false)
    :genl-inverse (let [drop-in (fn [t path v]
                                  (let [left (disj (get-in t path #{}) v)]
                                    (if (seq left)
                                      (assoc-in t path left)
                                      (update-in t (pop path) dissoc (peek path)))))]
                    (-> t (drop-in [:genl-inverse-down b] a) (drop-in [:genl-inverse-up a] b)))
    :arity    (let [ns' (disj (get-in t [:arity a] #{}) b)]
                (if (seq ns') (assoc-in t [:arity a] ns') (update t :arity dissoc a)))
    ;; Dropping the last position drops the predicate's whole entry, so
    ;; `functional-in-arg-over`'s `(filter table)` gate stays exact and an emptied
    ;; predicate does not linger as a key mapping to `#{}`.
    :functional-in-arg
    (let [ns' (disj (get-in t [:functional-in-arg a] #{}) b)]
      (if (seq ns')
        (assoc-in t [:functional-in-arg a] ns')
        (update t :functional-in-arg dissoc a)))
    ;; The same emptied-key discipline, for the same reason: `commuting-groups` gates on
    ;; the predicate's entry being present, so a predicate whose last group left must not
    ;; linger as a key mapping to `#{}` — a literal would then take the group-aware
    ;; canonicalization path and pay for a licence it no longer has.
    :commuting
    (let [gs' (disj (get-in t [:commuting a] #{}) b)]
      (if (seq gs')
        (assoc-in t [:commuting a] gs')
        (update t :commuting dissoc a)))))

(defn- named-ops
  "`op` (`:post` or `:retire`) for each stored positive `except` and `defeat` naming
  `handle`, under `[rel functor ctx]` of the `:tax-named` family: two count reads, and the
  naming facts' contexts and handles when one is stored.  A probe's handle, which is not
  an integer, reads nothing."
  [idx op rel handle]
  (when (integer? handle)
    (for [f     [sx/except-functor sx/defeat-functor]
          :when (reads/stored-naming? idx f handle)
          [c hs] (reads/as-stored-naming-by-context idx f handle)
          h     hs]
      [op :tax-named [rel f c] h])))

(defn- post!
  "Post `handle`, stated in `ctx`, as a supporter of taxonomy key `k` in `tax`'s index
  store, in one batch: the `:tax-support` leaf `(conj k ctx)`, `handle`'s
  `:tax-installs` set and the `:tax-named` entries of the facts naming it, before the
  in-memory write that installs `k`.  Answers `k`'s supporters when the post made `handle`
  the only one, `{handle ctx}`, which the write then needs no read for; else nil."
  [tax k handle ctx]
  (let [idx (:index @tax)]
    (when (= 1 (first (p/family-apply! idx (into [[:post :tax-support (conj k ctx) handle]
                                                  [:post :tax-installs [handle] k]]
                                                 (named-ops idx :post (kv/key-relation k) handle)))))
      {handle ctx})))

(defn- retire!
  "Take `handle` out of taxonomy key `k`'s supporters in `tax`'s index store, from
  whichever context it is stated in, and the facts naming it out of `k`'s relation in the
  `:tax-named` family when `handle` installs no other key of the relation: true when it
  was one."
  [tax k handle]
  (let [idx (:index @tax)
        rel (kv/key-relation k)
        was (some? (first (p/family-apply! idx [[:retire :tax-support (conj k p/any-context) handle]
                                                [:retire :tax-installs [handle] k]])))]
    (when-let [ops (seq (named-ops idx :retire rel handle))]
      (when-not (some #(= rel (kv/key-relation %)) (reads/as-stored-installed-keys idx handle))
        (p/family-apply! idx (vec ops))))
    was))

(defn- add-supported
  "Record `handle` as asserting the flat-cache key `k` from `ctx`, installing the entry,
  and answer `tax`.  The one body behind every `add-*` / `mark-*` whose cache entry is its
  key alone; each of those names only how its arguments spell the key."
  [tax k handle ctx]
  (let [sole (post! tax k handle ctx)]
    (swap! tax supported-add k handle sole #(cache-install % k)))
  tax)

(defn- del-supported!
  "Drop `handle`'s support for `k`, uninstalling the entry when the last supporter goes,
  and answer `tax`.  `add-supported`'s inverse, behind every matching `del-*!` /
  `unmark-*!`."
  [tax k handle]
  (retire! tax k handle)
  (swap! tax supported-del k handle #(cache-uninstall % k))
  tax)

;; ---- incremental adjacency maintenance ----------------------------------
;; Only the O(V+E) direct adjacency is stored; the closure is answered on demand
;; (`closure-of` above) and read-memoized per generation.  So an insert is O(1) plus a
;; depth repair whose size is the lift `raise-depth` forces — nothing at all for the
;; parent-before-child order, the node's descendants for the child-first one, which is
;; what `*defer-depths?*` trades away — and a delete is O(1) plus a node re-scan.
;; Neither pays to materialize the closure, which is what makes a deep or bulk load
;; sub-quadratic.  Every mutation bumps `:gen`, retiring the read memo.

(defn- bump-gen [rel] (update rel :gen inc))

(defn- note-move
  "`rel` with node `a` recorded as the lower end of an edge whose activation or supporting
  contexts moved at the current generation: `:moves` is `(sorted-map gen #{node})`,
  holding each node at the last generation that moved it (`:move-gen`), so the log is
  bounded by the nodes.  Every closure a move changes is a closure of a node at or below
  a recorded one (`moves-since`)."
  [rel a]
  (let [g   (:gen rel)
        old (get-in rel [:move-gen a])
        ms  (or (:moves rel) (sorted-map))
        ms  (if (and old (not= old g))
              (let [left (disj (get ms old) a)]
                (if (seq left) (assoc ms old left) (dissoc ms old)))
              ms)]
    (-> rel
        (assoc :moves (update ms g (fnil conj #{}) a))
        (assoc-in [:move-gen a] g))))

(defn- ensure-depth
  "Give `n` a depth if it has none.  A fresh node starts at 0; the invariant
  `edge x→y ⇒ depth[x] > depth[y]` is restored by `raise-depth` on insert."
  [rel n]
  (cond-> rel (not (contains? (:depth rel) n)) (assoc-in [:depth n] 0)))

(defn- component-members
  "The inverse of a node → representative map: representative → that component's
  members.  O(size of `scc`), so it runs only where a component map is computed —
  `repair-depths` and a split in `repair-component` — and every other reader looks up
  `:scc-members`."
  [scc]
  (reduce-kv (fn [m n r] (update m r (fnil conj #{}) n)) {} scc))

(defn- lift-components
  "Raise components until every `[node depth]` seed holds — the node's whole component
  sitting at least that deep — pushing each raise up through `:rev`, since a component
  with an edge into a raised one has to stay strictly above it.  A component is
  re-enqueued whenever a deeper one lifts it, so a diamond is handled correctly.

  It moves whole **components** because the potential is one over the condensation:
  depth is equal inside a component and strict between two, so a member raised alone
  would break the equality its component's depth is defined by — and, in a cyclic
  relation, would then raise its own mates forever, each lift forcing the next around
  the cycle.  Termination is the condensation being a DAG: every step raises a
  component strictly and climbs an edge of that DAG, so no component can force itself.
  (Depths are never *capped* — a cap keyed on the node count is unsound once deletion
  has left depths loose, since a legitimate lift can then legitimately exceed it.)"
  [rel seeds]
  (loop [rel rel, stack (vec seeds)]
    (if-let [[y dy] (peek stack)]
      (let [stack (pop stack)
            dy    (long dy)]
        (if (>= (long (get-in rel [:depth y] 0)) dy)
          (recur rel stack)
          (let [mem (if-let [r (get-in rel [:scc y])] (get-in rel [:scc-members r]) #{y})
                rel (reduce (fn [r m] (assoc-in r [:depth m] dy)) rel mem)
                up  (into [] (comp (mapcat #(get-in rel [:rev %]))
                                   (remove mem)
                                   (map (fn [u] [u (inc dy)])))
                          mem)]
            (recur rel (into stack up)))))
      rel)))

(defn- raise-depth
  "Restore `edge x→y ⇒ depth[x] > depth[y]` after adding edge a→b: lift `a` above `b`
  if it is not already, and push that lift up through `:rev` as far as it forces
  anything.  `lift-components` is the walk, so the lift moves `a`'s whole component
  when `a` sits in one."
  [rel a b]
  (if (> (long (get-in rel [:depth a])) (long (get-in rel [:depth b])))
    rel
    (lift-components rel [[a (inc (long (get-in rel [:depth b])))]])))

(def ^:dynamic *defer-depths?*
  "When true, an edge insert skips `raise-depth` and lifts only the edge's own source
  (`local-lift`), going `:loose?` if that breaks an edge above it; `restore-depths`
  rebuilds every depth in one pass when the batch settles.

  `raise-depth` is proportional to the *descendants* of the node it lifts, which is
  the one thing an insert is not supposed to be: adding a hundred thousand edges in an
  order that repeatedly lifts high nodes re-walks their subtrees over and over, so a
  bulk load arriving child-first is quadratic in the hierarchy.  Deferring makes the
  insert O(1) plus the source's in-degree, and pays one O(V+E) repair per batch.

  Going loose is **not** free, which is why `local-lift` exists rather than a blanket
  `:loose?`: while loose `reachable?` drops its pruning, and `wff` runs one such walk
  per taxonomy edge asserted.  Trading the eager repair for a blanket loose potential
  would only swap which arrival order is quadratic — child-first would get cheap and
  parent-first, the *natural* order for a hierarchy, would get expensive.  The local
  lift keeps the potential sound for exactly the orders `raise-depth` was already cheap
  on, so neither order pays.

  Bound by `vaelii.core/with-deferred-settle`, whose settle does the repair — the same
  bargain that scope already makes for belief."
  false)

(def ^:dynamic *defer-cycle-scc?*
  "When true, an edge that closes a cycle marks the relation `:loose?` and leaves the
  strong-component recompute to `restore-depths`, instead of running `repair-depths`
  outright inside `activate`.

  `activate` repairs a cycle-closing edge eagerly by default, even under
  `*defer-depths?*`: a forward firing seeded by that edge reads `:scc` through
  `placement-rep` before the batch settles, so a deferred `:scc` would place one
  conclusion on two members of a `genlCx` cycle (see `activate`).  Recovery has no such
  reader.  `rebuild-taxonomy` and the belief reconcile that follows it read `:scc` only
  through `reachable?`, which walks unpruned while `:loose?` and so answers correctly
  from a stale `:scc`; the first `placement-rep` read is `settle`, which runs after
  `restore-depths`.  So recovery binds this true and pays one O(V+E) repair for the
  whole replay, not one per cycle-closing edge.  A corpus decides how many those are,
  and a foreign or bulk writer, or a store replayed past the assert-time cycle checks
  (`wff/genl-problems`, `wff/genlCx-problems`), can leave a large strong component whose
  every internal edge would otherwise repair the whole relation again.

  A caller that binds this must call `restore-depths` before any `placement-rep` reader
  runs, as `vaelii.impl.recovery/recover` does; a bind without that closing repair would
  leave `:scc` stale for the life of the KB."
  false)

(defn- local-lift
  "Restore `depth[a] > depth[b]` for the newly-inserted edge a→b **alone**: lift `a`
  just above `b` and check only the edges *into* `a`, never its descendants.

  That is the whole difference from `raise-depth`, which pushes the lift down through
  `:rev` until it stops forcing anything.  Raising `depth[a]` can never break an edge
  `a→x` (the source only moved up), so the only edges at risk are `u→a` for `u` in
  `:rev a` — an in-degree scan, not a descendant walk.  If none is broken the global
  invariant still holds and the potential stays sound, so reads keep their pruning; if
  one is, the relation goes `:loose?` and `restore-depths` owns the repair.

  Edges arriving **parent-before-child** — a hierarchy's natural load order, and the
  order `reachable?`'s pruning is written for — never break one: the child is a fresh
  node, nothing points at it yet.  So the common bulk load keeps an O(1) insert *and*
  an O(1) pruned read, which a blanket `:loose?` would have cost it."
  [rel a b]
  (let [da (get-in rel [:depth a])
        db (get-in rel [:depth b])]
    (if (> da db)
      rel                                          ; already satisfied — nothing moved
      (let [da' (inc db)
            rel (assoc-in rel [:depth a] da')]
        (if (some (fn [u] (<= (get-in rel [:depth u] 0) da')) (get-in rel [:rev a]))
          (assoc rel :loose? true)
          rel)))))

(defn- strong-components
  "The strongly connected components of `nodes` under adjacency `fwd`, as a map
  node → representative — **only** for the nodes in a component of more than one, so
  an acyclic relation gets `{}` and every read past this point pays a nil lookup.

  Tarjan's algorithm, iterated over an explicit work stack rather than recursed: the
  recursion depth is the graph's depth, and a context lattice is thousands deep.  The
  representative is `term-min` of the component, so which name stands for a component
  is a function of its content and not of the order its edges arrived."
  [nodes fwd]
  (let [idx   (java.util.HashMap.)              ; node → discovery index
        low   (java.util.HashMap.)
        on    (java.util.HashSet.)              ; nodes currently on the Tarjan stack
        stk   (java.util.ArrayDeque.)
        out   (volatile! {})
        n     (volatile! 0)]
    (doseq [root nodes :when (not (.containsKey idx root))]
      ;; each frame is [node remaining-neighbours]; a frame is pushed on descent and
      ;; popped once its neighbours are exhausted, which is where the low-link folds up
      (let [work (java.util.ArrayDeque.)
            visit (fn [v]
                    (.put idx v @n) (.put low v @n) (vswap! n inc)
                    (.push stk v) (.add on v)
                    (.push work (object-array [v (seq (get fwd v))])))]
        (visit root)
        (while (not (.isEmpty work))
          (let [^objects frame (.peek work)
                v              (aget frame 0)
                remaining      (aget frame 1)]
            (if-let [w (first remaining)]
              (do (aset frame 1 (next remaining))
                  (cond
                    (not (.containsKey idx w)) (visit w)
                    (.contains on w)           (.put low v (min (long (.get low v))
                                                                (long (.get idx w))))))
              (do (.pop work)
                  (when (= (.get low v) (.get idx v))
                    ;; v roots a component: everything above it on the stack is in it
                    (let [members (loop [acc []]
                                    (let [w (.pop stk)]
                                      (.remove on w)
                                      (if (= w v) (conj acc w) (recur (conj acc w)))))]
                      (when (> (count members) 1)
                        (let [rep (term-min members)]
                          (vswap! out into (map (fn [m] [m rep])) members)))))
                  (when-let [^objects parent (.peek work)]
                    (let [p (aget parent 0)]
                      (.put low p (min (long (.get low p)) (long (.get low v))))))))))))
    @out))

(defn- repair-depths
  "Recompute every depth of `rel` in one pass, restoring the potential `edge x→y ⇒
  depth[x] ≥ depth[y]`, strict between components and equal inside one.

  The pass runs over the **condensation**: `components` first, then components are
  settled in reverse topological order — one is ready once every component it points
  at is — and each takes `1 + max` of what it points at, so the potential is the
  component's height above the sinks.  A node's depth is its component's.  O(V+E),
  against the O(descendants) *per edge* that repairing on insert costs.

  Condensing is what makes the pass total.  Walking the raw graph, a node on a cycle
  is never ready and would keep a stale depth — sound only for an acyclic graph.
  `wff` refuses a `genl` or `genlCx` cycle at assert, but a recovered or foreign
  store replays its stored edges past those checks (`recovery/recover`), so the pass
  must condense a cycle such a store presents rather than assume none exists."
  [rel]
  (let [nodes (:nodes rel)
        fwd   (:fwd rel)
        scc   (strong-components nodes fwd)
        ;; the condensation: a component keyed by its representative, a lone node by
        ;; itself.  Self-loops within a component are dropped — a component points at
        ;; itself by construction and would never be ready.
        cof   (fn [x] (get scc x x))
        cnodes (into #{} (map cof) nodes)
        cfwd  (reduce (fn [m x]
                        (let [cx (cof x)
                              ys (into #{} (comp (filter nodes) (map cof) (remove #{cx}))
                                       (get fwd x))]
                          (if (seq ys) (update m cx (fnil into #{}) ys) m)))
                      {} nodes)
        crev  (reduce (fn [m [x ys]] (reduce (fn [m2 y] (update m2 y (fnil conj #{}) x)) m ys))
                      {} cfwd)
        pending (into {} (map (fn [x] [x (count (get cfwd x))])) cnodes)]
    (loop [cdepth  (transient {})
           pending pending
           ready   (into [] (comp (filter #(zero? (long (pending %))))) cnodes)]
      (if-let [x (peek ready)]
        (let [ready (pop ready)
              dx    (reduce (fn [d y] (max d (inc (long (get cdepth y 0)))))
                            0 (get cfwd x))
              cdepth (assoc! cdepth x dx)
              ;; every component pointing at x may now be ready
              [pending ready]
              (reduce (fn [[p r] u]
                        (let [n (dec (long (get p u 1)))]
                          [(assoc p u n) (if (zero? n) (conj r u) r)]))
                      [pending ready]
                      (get crev x))]
          (recur cdepth pending ready))
        (let [cdepth  (persistent! cdepth)
              settled (into {} (keep (fn [x] (when-let [d (get cdepth (cof x))] [x d]))) nodes)]
          (-> rel
              (assoc :depth (merge (select-keys (:depth rel) (remove settled nodes)) settled))
              (assoc :scc scc :scc-members (component-members scc))
              (dissoc :loose?)))))))

(defn- activate
  "Bring [a b] into the active edge set: record the direct adjacency, the node set,
  and repair the depth potential.  A no-op when the edge is already active, so a
  redundant re-assert adds no work and leaves the read memo valid.

  `wff` (assert path) and `special/wff-violation` (derivation path) both refuse a
  `genl` or `genlCx` edge that would close a cycle before it reaches here, so a fresh
  assert never takes the cyclic branch.  An edge reaches it only past those checks: a
  store replayed by `recovery/recover`, a foreign or bulk writer, or a belief-race
  revival (defeat an edge, assert its reverse, revive the first — the checks read the
  active adjacency).  The `reachable?` guard is O(1) in the common case (`a` is a
  fresh or shallower node, rejected outright).

  An edge that **closes a cycle** merges two components, which is a question about the
  whole graph rather than about this edge: `raise-depth`'s termination assumes
  acyclicity, so the relation is repaired outright with `repair-depths` — one O(V+E)
  pass, for an event a corpus has a few dozen of — and leaves here with `:scc` already
  holding the merged component.  Repairing now rather than at the batch's settle is
  what `placement-rep` needs: the cycle-closing edge chains *before* the batch settles,
  and a firing seeded by it reads `:scc` to land its conclusion on the component's one
  representative.  Left to `restore-depths`, that firing would
  read the pre-merge map and land on whichever member it happened to see, and the same
  firing re-derived later would land on the representative — two sentexes for one
  claim in contexts that see each other.

  Under `*defer-depths?*` the acyclic repair is `local-lift` instead — the edge's own
  source, not its descendants.

  Under `*defer-cycle-scc?*` — recovery's replay, where no `placement-rep` reader runs
  before `restore-depths` — the cyclic repair is deferred as well: the first cycle marks
  the relation `:loose?`, `restore-depths` computes `:scc` once for the whole batch, and
  every edge after that first cycle skips the detection walk (the branch is `loose?`
  either way).  So the whole replay is O(V+E), not this branch recomputing `:scc` — nor
  the loose detection walking `b`'s reach — per cycle-closing edge (see the var).

  An **already-loose** relation short-circuits the *acyclic* repair, whether or not this
  insert is deferred: with no sound potential `raise-depth` would build on a stale base,
  so the adjacency is recorded and `restore-depths` is left to own it.  Reading
  `:loose?` rather than the dynamic var alone is what keeps that true for an insert
  arriving *after* a batch aborted — the settle that would have repaired never ran.
  What refuses a `genl` or `genlCx` cycle throughout is `wff`, which reads through
  `reachable-in?` and stays correct while loose.

  A **cycle is still detected while loose**, and paid for, because `:scc` is not a
  pruning: the deferral may postpone a depth, but a firing seeded by the closing edge
  reads `:scc` through `placement-rep` the moment it is placed, and the whole reason
  the cyclic branch repairs outright is that leaving it to the batch's settle puts one
  claim in two mutually-visible contexts.  The guard then walks unpruned — `b`'s whole
  up-closure rather than a prefix of it — which is why it is gated on `a` already being
  a node: nothing can reach the sub an edge is introducing, so an edge arriving
  parent-before-child costs one `contains?`, and that is the order a loose batch is
  still mostly made of.  The repair that follows also lifts `:loose?`, so the batch pays
  it once at the cycle rather than once per edge after it."
  [rel a b]
  (if (contains? (:edges rel) [a b])
    rel                                            ; already active — nothing to do
    (let [loose?  (boolean (:loose? rel))
          cyclic? (cond
                    ;; Recovery defers the cycle repair (`*defer-cycle-scc?*`), and once
                    ;; the relation is loose the branch below is `loose?` whether or not
                    ;; this edge closes a cycle — so the detection walk, unpruned while
                    ;; loose, decides nothing and is skipped.  `restore-depths` recomputes
                    ;; `:scc` from the final graph regardless.  This is what keeps the
                    ;; deferred replay O(V+E): without it every edge after the first cycle
                    ;; pays a walk of `b`'s whole reach, which in a large component is the
                    ;; component, restoring the per-edge cost the deferral removes.
                    (and loose? *defer-cycle-scc?*) false
                    loose? (and (contains? (:nodes rel) a)
                                (reachable? b a (:fwd rel) nil (:scc rel)))
                    :else  (reachable? b a (:fwd rel) (:depth rel) (:scc rel)))
          rel     (-> rel
                      (ensure-depth a) (ensure-depth b)
                      (update-in [:fwd a] (fnil conj #{}) b)
                      (update-in [:rev b] (fnil conj #{}) a)
                      (update :nodes conj a b)
                      (update :edges conj [a b]))]
      (-> (cond
            (and cyclic? *defer-cycle-scc?*) (assoc rel :loose? true)
            cyclic?          (repair-depths rel)
            loose?           rel
            *defer-depths?*  (local-lift rel a b)
            :else            (raise-depth rel a b))
          bump-gen
          (note-move a)))))

(defn restore-depths
  "Repair the depth potential of every relation a deferred batch left `:loose?`.
  Idempotent, and free when no relation is loose — which includes the common deferred
  batch, whose `local-lift` kept the potential sound throughout — so `settle` can call
  it unconditionally, and so can a caller unwinding from an aborted batch."
  [tax]
  (swap! tax (fn [t]
               (reduce (fn [t k]
                         (if (get-in t [k :loose?])
                           (update t k (comp bump-gen repair-depths))
                           t))
                       t
                       [:genl :genlCx])))
  tax)

(defn- prune-node
  "Drop `n` from `:nodes` / `:depth` / `:scc` / `:scc-members` if no active edge touches
  it any more."
  [rel n]
  (if (or (seq (get-in rel [:fwd n])) (seq (get-in rel [:rev n])))
    rel
    (let [r   (get-in rel [:scc n])
          rel (-> rel (update :nodes disj n) (update :depth dissoc n) (update :scc dissoc n))]
      (if (nil? r)
        rel
        (let [left (disj (get-in rel [:scc-members r]) n)]
          (if (seq left)
            (assoc-in rel [:scc-members r] left)
            (update rel :scc-members dissoc r)))))))

(defn- split-depths
  "Depths for the members of a component that has just split, given `sub` — the
  components of its own induced subgraph.  `{node depth}` over `members`.

  Each new sub-component sits one above the highest thing it points at, whether that is
  another sub-component or a node outside the old component entirely; sinks are settled
  first, so each is settled once.  Tight rather than merely sound, which is what keeps
  the answer from drifting upward every time a component splits: the sub-component
  holding the old component's deepest external edge keeps the depth the whole component
  had, and only a chain **above** it rises at all."
  [rel members sub]
  (let [fwd    (:fwd rel)
        depth  (:depth rel)
        cof    #(get sub % %)
        cnodes (into #{} (map cof) members)
        ;; the sub-condensation, and per sub-component the highest depth it points at
        ;; outside the old component — the floor its own depth has to clear
        [cfwd floor]
        (reduce (fn [acc x]
                  (let [cx (cof x)]
                    (reduce (fn [[cf fl] y]
                              (if (contains? members y)
                                (let [cy (cof y)]
                                  (if (= cx cy) [cf fl] [(update cf cx (fnil conj #{}) cy) fl]))
                                [cf (update fl cx (fnil max 0) (inc (long (get depth y 0))))]))
                            acc (get fwd x))))
                [{} {}] members)
        crev    (reduce-kv (fn [m x ys]
                             (reduce (fn [m2 y] (update m2 y (fnil conj #{}) x)) m ys))
                           {} cfwd)
        pending (into {} (map (fn [x] [x (count (get cfwd x))])) cnodes)]
    (loop [cd      (transient {})
           pending pending
           ready   (into [] (filter #(zero? (long (pending %)))) cnodes)]
      (if-let [x (peek ready)]
        (let [ready (pop ready)
              dx    (reduce (fn [d y] (max d (inc (long (get cd y 0)))))
                            (long (get floor x 0)) (get cfwd x))
              cd    (assoc! cd x dx)
              [pending ready]
              (reduce (fn [[p r] u]
                        (let [n (dec (long (get p u 1)))]
                          [(assoc p u n) (if (zero? n) (conj r u) r)]))
                      [pending ready] (get crev x))]
          (recur cd pending ready))
        (let [cd (persistent! cd)]
          (into {} (map (fn [x] [x (long (get cd (cof x) 0))])) members))))))

(defn- repair-component
  "Repair the component a removed edge sat inside, and the depths its split invalidates.
  A stale `:scc` entry is the one thing in this relation that would answer *true* for a
  pair no longer connected, so it is never left standing.

  **Only an edge whose two endpoints share a component can change one.** A component's
  strong connectivity is a property of its own induced subgraph, and an edge with an
  endpoint outside — or with none in a component at all — is not in that subgraph. So
  every other deletion, which is every deletion in an acyclic relation and most of them
  in a cyclic one, is left alone here: nothing to recompute, and the potential stays
  sound, since removing an edge only relaxes the ordering it has to satisfy.

  When they do share one, the component's own induced subgraph is re-run through
  `strong-components` — the new components of the whole graph refine the old ones, so
  what a split produces is contained in the component that split, and the answer is
  proportional to it rather than to the relation. A component that survives the deletion
  intact leaves everything as it was. A split takes new depths from `split-depths`, and
  a sub-component whose new depth is higher than the one it is replacing pushes that
  rise up through `lift-components`.

  The relation therefore does **not** go `:loose?`, and reads keep their pruning
  through a deletion that would otherwise have cost a whole-relation `repair-depths`.
  The one case that does surrender is a relation **already** loose: there is no sound
  potential to repair against, so the component is dropped whole and the batch's own
  `restore-depths` rebuilds it.  Dropping is not optional there — a loose relation
  still reads `:scc` for the \"same component ⇒ mutually reachable\" answer, which is
  the one thing an unpruned walk cannot correct."
  [rel a b]
  (let [scc     (:scc rel)
        rep     (get scc a)
        members (get-in rel [:scc-members rep])]
    (cond
      (or (nil? rep) (not= rep (get scc b))) rel
      (:loose? rel) (-> rel
                        (assoc :scc (apply dissoc scc members))
                        (update :scc-members dissoc rep))
      :else
      (let [fwd     (:fwd rel)
            sub-fwd (into {} (map (fn [x] [x (into #{} (filter members) (get fwd x))])) members)
            sub     (strong-components members sub-fwd)]
        (if (= 1 (count (into #{} (map #(get sub % %)) members)))
          rel                                          ; still one component — nothing moved
          (let [depths (split-depths rel members sub)
                scc'   (merge (apply dissoc scc members) sub)
                cof    #(get scc' % %)
                risen  (filterv #(> (long (depths %)) (long (get-in rel [:depth %] 0))) members)
                rel    (-> rel
                           (assoc :scc scc')
                           (update :scc-members #(merge (dissoc % rep) (component-members sub)))
                           (update :depth merge depths))
                seeds  (into [] (mapcat (fn [x]
                                          (let [d (inc (long (depths x)))]
                                            (keep (fn [u] (when (not= (cof u) (cof x)) [u d]))
                                                  (get-in rel [:rev x])))))
                             risen)]
            (lift-components rel seeds)))))))

(defn- deactivate
  "Drop [a b] from the active edge set.  Depths are left as loose upper bounds — a
  deletion only relaxes the ordering, so the invariant survives — and a node left
  with no edge is pruned so `types` / `contexts` match a from-scratch build.  A
  component the edge sat inside is recomputed rather than trusted (see
  `repair-component`)."
  [rel a b]
  (if-not (contains? (:edges rel) [a b])
    rel
    (let [drop-adj (fn [rel k x y]
                     (let [s (disj (get-in rel [k x]) y)]
                       (if (seq s) (assoc-in rel [k x] s) (update rel k dissoc x))))]
      (-> rel
          (update :edges disj [a b])
          (drop-adj :fwd a b)
          (drop-adj :rev b a)
          (repair-component a b)
          (prune-node a) (prune-node b)
          bump-gen
          (note-move a)))))

(defn- set-edge-ctxs
  "Record `ctxs` as active edge `e`'s supporting contexts, bumping `:gen` iff the set
  moved — a scoped read's answer is a function of these, so a context-only move must
  retire the read memo even though the edge set did not change."
  [rel e ctxs]
  (if (= ctxs (get-in rel [:edge-ctxs e]))
    rel
    (-> rel (assoc-in [:edge-ctxs e] ctxs) bump-gen (note-move (first e)))))

(defn- mark-dirty
  "Note that `e`'s `:edge-ctxs` was recomputed belief-blind and owes a reconcile.  Only
  a **shared** edge does: with one supporter the writers' reading is already the believed
  one, either because the supporter is believed or because nothing else claims the edge.
  Costs the common single-supporter write nothing, which is what keeps a bulk load out of
  the set entirely."
  [rel e shared?]
  (cond-> rel shared? (update :dirty conj e)))

(defn- add-edge
  "`t` after `handle` was posted as a supporter of `rel-key` edge [a b]: the edge active,
  with the contexts of every stored supporter, and dirty when it has more than one."
  [t rel-key a b handle sole]
  (let [k       [rel-key a b]
        [t sup] (written-supporters t k handle sole)]
    (update t rel-key #(-> %
                           (activate a b)
                           (set-edge-ctxs [a b] (into #{} (vals sup)))
                           (mark-dirty [a b] (> (count sup) 1))))))

(defn- del-edge
  "`t` after `handle` was retired from `rel-key` edge [a b] (`retired?` false when it was
  not a supporter, which leaves `t` as it is).  The edge survives while any other stored
  sentex supports it."
  [t rel-key a b handle retired?]
  (if-not retired?
    t
    (let [k        [rel-key a b]
          [t left] (written-supporters t k handle nil)]
      (if (seq left)
        ;; retarget only an *active* edge: a refresh may have deactivated this one with its
        ;; (disbelieved) supporters still stored, and `:edge-ctxs` keys exactly the active
        ;; set.  Belief-blind either way, so the edge owes a reconcile: the survivors may
        ;; include one nothing believes, and losing the last *believed* supporter of a
        ;; still-supported edge is a deactivation only a `believed?` can see.
        (update t rel-key #(-> %
                               (cond-> (contains? (:edges %) [a b])
                                 (set-edge-ctxs [a b] (into #{} (vals left))))
                               (mark-dirty [a b] true)))
        (-> t
            (update-in [:supporters :by-key] dissoc k)
            (update rel-key #(-> % (deactivate a b) (update :edge-ctxs dissoc [a b])
                                 (update :dirty disj [a b]))))))))

(defn- moved-touches?
  "Should a cache be reconciled against belief?  Yes when `moved` is nil — the caller
  holds no region and wants an unconditional reconcile — or when one of the cache's
  supporters is in `moved`, the set of handles whose belief just flipped.  When no
  supporter moved, the cache's active set cannot have changed, so the scan is skipped.

  `supporters` is the cache's own record of them: a set of handles, or the map they key.
  Either answers `contains?` by handle and `count` in O(1), which is what lets the
  intersection test walk **whichever side is smaller** — the two are independently sized,
  and a settle relabelling a large region over a cache holding few entries is as ordinary
  a shape as the reverse.  Walking the cache unconditionally is what made deciding a
  32k-entry cache was untouched cost 5 ms, in a settle that had nothing to do there.

  A gate, so a hit still pays the whole scan.  That is the right trade only where the
  scan is small — the equality partition and the rewrite rules, which hold the KB's
  asserted term-identity claims rather than its vocabulary.  The two transitive relations
  and the flat caches are the vocabulary's own size, so they do not gate at all:
  `moved-keys` reads the affected keys straight off `moved`, and skipping falls out of
  finding none."
  [moved supporters]
  (or (nil? moved)
      (boolean
       (if (and (counted? moved) (< (count moved) (count supporters)))
         (some #(contains? supporters %) moved)
         (some #(contains? moved %) (if (map? supporters) (keys supporters) supporters))))))

(defn- believed-ctxs
  "The contexts of the believed supporters in map `hs` (`{handle ctx}`), nil kept —
  a believed supporter with no recorded context still constrains everywhere.  Empty
  when no supporter is believed, which is what deactivates the edge."
  [hs believed?]
  (reduce-kv (fn [s h c] (if (believed? h) (conj s c) s)) #{} hs))

(defn- stored-metatypes
  "Every metatype a stored sentex marks, believed or not: the keys the stored
  `disjoint_metatype` facts install, or a raw taxonomy's walk."
  [t]
  (let [mt (fn [k] (when (= :metatype (nth k 0)) (nth k 1)))]
    (if (:raw? t)
      (into #{} (keep mt) (keys (reads/as-stored-supporter-map (:index t))))
      (into #{} (comp (mapcat #(keys-of t %)) (keep mt))
            (extent-handles t '[disjoint_metatype])))))

(def ^:private supporter-functors
  "The functors whose stored facts install a taxonomy key, but for the disjoint
  metatypes, which are data (`stored-metatypes`)."
  (into (conj edge-installing-functors 'genlCx) flat-functors))

(defn- all-keys
  "`[t' ks]`: every taxonomy key with a stored supporter, `t'` holding each key's
  supporters and each supporter's keys.  The stored facts of `supporter-functors` and of
  each stored metatype are every supporter there is, and the predicate extent lists each
  under its context, so the walk reads one installed-key set per stored fact and no
  supporter read: a key's supporters are the facts of the walk that install it."
  [t]
  (let [idx (:index t)
        [t sup]
        (reduce (fn [acc f]
                  (reduce (fn [acc c]
                            (reduce (fn [[t sup] h]
                                      (let [[t ks] (held-keys t h)]
                                        [t (reduce #(assoc-in %1 [%2 h] c) sup ks)]))
                                    acc (reads/as-stored-with-functor-in idx f #{c})))
                          acc (first (reads/as-stored-contexts-with-functor-global idx f))))
                [t {}] (into supporter-functors (stored-metatypes t)))]
    [(reduce-kv (fn [t k hs] (hold t :by-key k hs)) t sup) (set (keys sup))]))

(defn- moved-keys
  "`[t' ks]`: the taxonomy keys a handle in `moved` installs — the only keys whose
  believed supporters can have changed, so the whole scope a reconcile owes — read
  through the supporter cache, `t'` holding what it read.  Every key with a stored
  supporter when `moved` is nil (`all-keys`, or a raw taxonomy's walk):
  `refresh-beliefs`' two-arity, which a caller holding no region takes.

  `moved` is a superset of the handles whose belief flipped (`jtms/touched`), so a handle
  in it that installs nothing costs one read and never an answer.  The smaller side is
  walked: `moved`, one read per handle, or the handles of the facts that can install a key
  (`supporter-functors`, `stored-metatypes`) kept where `moved` holds them.  The second
  is read only when `moved` outnumbers the functors, whose stored facts it then counts
  first; a settle relabelling a large region over a KB declaring little is an ordinary
  shape (`perf`'s `negation-arbitration` measures one)."
  [t moved]
  (let [walk (fn [t hs]
               (reduce (fn [[t ks] h] (let [[t hks] (held-keys t h)] [t (into ks hks)]))
                       [t #{}] hs))]
    (cond
      (and (nil? moved) (:raw? t))
      [t (set (keys (reads/as-stored-supporter-map (:index t))))]
      (nil? moved)
      (all-keys t)
      (or (:raw? t) (not (counted? moved)) (<= (count moved) (count supporter-functors)))
      (walk t moved)
      :else
      (let [fs (into supporter-functors (stored-metatypes t))
            n  (transduce (map #(reads/stored-count-with-functor (:index t) %)) + 0 fs)]
        (if (<= (count moved) n)
          (walk t moved)
          (walk t (filter #(contains? moved %) (extent-handles t fs))))))))

(defn- refresh-relation
  "Active edges are those with at least one *believed* supporter, carrying the
  believed supporters' contexts.  Applies the difference edge by edge rather than
  rebuilding, so a settle whose region names no edge returns the relation untouched.
  Where it names edges the pass is not free of belief: one classifying pass evaluates
  `believed-ctxs` over every named edge's supporters before any arm runs, so a settle
  that changed no belief still pays one belief test per supporter of every edge in its
  region and the three arms then find nothing to apply.

  The classifying pass keeps only the edges whose state changes, each under the arm it
  needs.  The memory the pass holds is therefore proportional to the edges that change,
  not to the region.  A recovery names every edge, and holds no per-edge context map of
  the whole taxonomy while the arms run.

  Scoped to `edges` (`moved-keys`) and `:dirty`, the edges a belief-blind writer left
  owing a reconcile — an edge no moved handle supports and no writer left dirty is
  provably unchanged, so belief is never evaluated for it.  That is the locality
  invariant for this cache: the reconcile costs what moved, not what is stored.  This is
  the pass that discharges `:dirty`, so it clears the set on the way in.  Each edge's
  supporters are read through the supporter cache, which holds them.

  Three arms, not two.  An edge can keep its liveness while its *contexts* move —
  supported from A by h1 and from B by h2, h2 defeated: the edge stays active and B
  must leave `:edge-ctxs`, or a scoped read from B would answer through a defeated
  supporter.  Liveness alone cannot see that case, so the still-active edges are
  retargeted explicitly (`set-edge-ctxs` bumps the gen only when a set actually
  moved, so the arm is free for the common belief-preserving settle).

  The arms run in that order — deactivate, activate, retarget — rather than edge by
  edge, and it is not presentation.  `activate` condenses the whole relation across an
  edge that would close a cycle, so an activation reading a graph that still holds the
  edges this same pass is about to drop can pay a repair, and record a component, that
  the settled graph never has.  Draining the deactivations first is what keeps the
  potential's fate a function of the settled edge set rather than of the order two arms
  happened to run in."
  [t rel-key believed? edges]
  (let [rel     (get t rel-key)
        touched (into (:dirty rel) edges)]
    (if (empty? touched)
      t
      (let [have (:edges rel)
            ctxs (:edge-ctxs rel)
            ;; `drops` is a hash set and `adds` a hash map (`hash-map`, never an array map),
            ;; so the deactivate and activate arms meet their edges in hash order, the order
            ;; they take.  `retarget` skips an active edge whose believed contexts equal its
            ;; recorded ones: `set-edge-ctxs` would leave it untouched, and neither earlier
            ;; arm writes another edge's `:edge-ctxs`.
            [t drops adds retarget]
            (reduce (fn [[t drops adds retarget] [a b :as e]]
                      (let [[t sup] (held-supporters t [rel-key a b])
                            cs      (believed-ctxs sup believed?)]
                        (cond
                          (contains? have e)
                          (cond (empty? cs)         [t (conj! drops e) adds retarget]
                                (= cs (get ctxs e)) [t drops adds retarget]
                                :else               [t drops adds (assoc! retarget e cs)])
                          ;; an edge with a value endpoint stays inactive: `wff` refuses
                          ;; one at assert, and an older writer's store can hold one
                          (and (seq cs) (not (nm/value? a)) (not (nm/value? b)))
                          [t drops (assoc! adds e cs) retarget]
                          :else    [t drops adds retarget])))
                    [t (transient #{}) (transient (hash-map)) (transient (hash-map))]
                    touched)]
        (update t rel-key
                (fn [rel]
                  (as-> (assoc rel :dirty #{}) r     ; this pass is what discharges them
                    (reduce (fn [r [a b :as e]]
                              (-> r (deactivate a b) (update :edge-ctxs dissoc e)))
                            r (persistent! drops))
                    (reduce-kv (fn [r [a b :as e] cs]
                                 (-> r (activate a b) (set-edge-ctxs e cs)))
                               r (persistent! adds))
                    (reduce-kv set-edge-ctxs r (persistent! retarget)))))))))

;; The add writers take the asserting sentex's context; the one-shorter arity is for
;; a caller with none to record — a probe, or a test driving the closure math — and
;; stores nil, the constrains-everywhere reading.  Deletion is keyed by handle alone.
(defn add-genl
  ([tax sub super handle] (add-genl tax sub super handle nil))
  ([tax sub super handle ctx]
   (let [sole (post! tax [:genl sub super] handle ctx)]
     (swap! tax add-edge :genl sub super handle sole))
   tax))
(defn del-genl! [tax sub super handle]
  (let [r (retire! tax [:genl sub super] handle)]
    (swap! tax del-edge :genl sub super handle r))
  tax)
(defn add-genlCx
  ([tax sub super handle] (add-genlCx tax sub super handle nil))
  ([tax sub super handle ctx]
   (let [sole (post! tax [:genlCx sub super] handle ctx)]
     (swap! tax add-edge :genlCx sub super handle sole))
   tax))
(defn del-genlCx! [tax sub super handle]
  (let [r (retire! tax [:genlCx sub super] handle)]
    (swap! tax del-edge :genlCx sub super handle r))
  tax)

;; ---- equality: rewriteOf / sameAs / equals, one partition ----------------
;;
;; `genl` is a partial order, so it caches up/down closures.  Equality is an
;; **equivalence**, and copying that shape would store every class as a complete
;; graph — quadratic, and it still would not answer "who represents this class?",
;; which is the only question the rewrite path actually asks.  So this is a
;; **partition**: member → class, class → members and representative.
;;
;; All three assertable relations feed it.  They differ in what they say *about* the
;; members, not in the classes they produce, and the whole of that difference rides
;; in one argument: `preferred` names the term a `rewriteOf` puts on top, and is nil
;; for `sameAs` / `equals`.  The edge itself is therefore undirected while the
;; preference belongs to the *supporter* that made the claim — which is what lets a
;; `(sameAs A B)` and a `(rewriteOf B A)` support one edge while only the second
;; deprecates anything, and lets belief withdraw the preference without withdrawing
;; the merge.
;;
;; Support is belief-following exactly as it is for genl.  `:out` is the disbelieved
;; supporter set; `refresh-beliefs` recomputes it wholesale from the current support
;; keys, so it cannot accumulate handles whose sentex has since gone.
;;
;; Insertion is a union, and it costs the **joined class** rather than a pointer:
;; `install-class` re-keys every member and `class-rep` scans each member's incident
;; edges for the preference claims on them, so merging a term into a class of n costs n
;; and n asserts growing one class to n cost Θ(n²) between them.  That is the price of
;; storing the representative rather than deriving it per read, and the bound is the
;; class rather than the relation.  **Deletion can split a class**, which union-find
;; cannot undo, so it rebuilds the affected class from its surviving believed edges —
;; the same bound, the same shape as the ancestor-set-local `genl` deletion, never the whole
;; relation.

(defn- pair
  "The canonical undirected edge key for `a` and `b`.  Equality is symmetric, so
  `(sameAs A B)` and `(sameAs B A)` must land on one edge."
  [a b]
  (if (neg? (compare (term-key a) (term-key b))) [a b] [b a]))

(defn- pref-pair
  "The directed [preferred dispreferred] claim that naming `p` makes about edge
  [x y].  nil when `p` is nil (a `sameAs` / `equals` supporter names no preference)."
  [[x y] p]
  (cond (= p x) [x y]
        (= p y) [y x]))

(defn- idx-conj [idx k v] (update idx k (fnil conj #{}) v))
(defn- idx-disj [idx k v]
  (let [s (disj (get idx k #{}) v)]
    (if (seq s) (assoc idx k s) (dissoc idx k))))

(defn- class-members
  "The class `t` belongs to, or `#{t}` when nothing has merged it."
  [rel t]
  (if-let [r (get (:class rel) t)] (get (:members rel) r #{t}) #{t}))

(defn- class-rep
  "The representative of a class, from its members and the preference claims carried
  by the active edges inside it.

  1. A term some `rewriteOf` names preferred wins, and **chains compose**: the heads
     are the preferred terms that nothing else deprecates, so `rewriteOf A B` plus
     `rewriteOf B C` leaves only `A` and it represents all three.
  2. A tie among heads — and a class with no `rewriteOf` at all — falls back to the
     lexicographically smallest term.  Arbitrary, but content-keyed and stable, the
     same discipline as `solve/content-key`: one class yields one representative no
     matter what order its edges arrived in.

  A `rewriteOf` cycle deprecates every preferred term and so has no head.  `wff`
  rejects it like a `genl` cycle; the second fallback is here so this stays total
  rather than returning nil if it ever becomes reachable."
  [rel members]
  (let [ps        (into #{}
                        (mapcat (fn [m] (mapcat #(get (:edge-prefs rel) % #{})
                                                (get (:edge-idx rel) m #{}))))
                        members)
        preferred (into #{} (map first) ps)
        heads     (set/difference preferred (into #{} (map second) ps))]
    (term-min (cond (seq heads) heads (seq preferred) preferred :else members))))

(defn- install-class
  "Install `members` as one class under its freshly-computed representative, dropping
  whatever classes those members used to key under."
  [rel members]
  (let [rep (class-rep rel members)]
    (-> rel
        (update :members #(apply dissoc % (keep (:class rel) members)))
        (assoc-in [:members rep] members)
        (update :class into (map (fn [t] [t rep])) members))))

(defn- components
  "The connected components the active edges induce on `terms`.  A term left with no
  active edge gets no component at all, so the key set matches what a from-scratch
  build produces — an unmerged term represents itself and is not stored."
  [rel terms]
  (let [nbrs (fn [t] (into #{} (mapcat identity) (get (:edge-idx rel) t #{})))]
    (loop [todo (into #{} (filter #(seq (get (:edge-idx rel) % #{}))) terms), acc []]
      (if-let [n (first todo)]
        (let [c (reach n nbrs)]
          (recur (set/difference todo c) (conj acc c)))
        acc))))

(defn- set-edge
  "Make edge `e` active carrying preference claims `ps`, unioning the two classes it
  joins.  Also the path a *second* supporter takes when it adds a preference to an
  edge that was already active: the partition does not move, the representative may."
  [rel [a b :as e] ps]
  (let [rel (-> rel
                (update :edges conj e)
                (update :edge-idx idx-conj a e)
                (update :edge-idx idx-conj b e)
                (update :edge-prefs #(if (seq ps) (assoc % e ps) (dissoc % e))))]
    (install-class rel (into (class-members rel a) (class-members rel b)))))

(defn- unset-edge
  "Deactivate edge `e`.  This is the half union-find cannot do: dropping an edge can
  **split** the class in two, so the class is torn down and rebuilt from the edges
  that survive it.  The work is bounded by the class, not by the relation."
  [rel [a b :as e]]
  (if-not (contains? (:edges rel) e)
    rel
    (let [members  (class-members rel a)               ; == (class-members rel b)
          old-reps (keep (:class rel) members)
          rel      (-> rel
                       (update :edges disj e)
                       (update :edge-idx idx-disj a e)
                       (update :edge-idx idx-disj b e)
                       (update :edge-prefs dissoc e)
                       ;; forget the class wholesale, then re-install whatever the
                       ;; surviving edges still hold together — one component if the
                       ;; edge was redundant, two if it was the only bridge, none at
                       ;; all if both ends are now isolated
                       (update :members #(apply dissoc % old-reps))
                       (update :class #(apply dissoc % members)))]
      (reduce install-class rel (components rel members)))))

(defn- edge-state
  "The preference claims believed supporters make about `e`, or nil when no believed
  sentex asserts the edge at all."
  [rel e]
  (let [live (into {} (remove (fn [[h _]] (contains? (:out rel) h)))
                   (get (:support rel) e))]
    (when (seq live)
      (into #{} (keep (fn [[_ p]] (pref-pair e p))) live))))

(defn- apply-edge
  "Reconcile one edge with what its believed supporters now say.  An edge whose state
  did not move adds no work — the common case for a settle that defeated nothing."
  [rel e]
  (let [want (edge-state rel e)
        have (when (contains? (:edges rel) e) (get (:edge-prefs rel) e #{}))]
    (cond (= want have) rel
          (nil? want)   (unset-edge rel e)
          :else         (set-edge rel e want))))

(def ^:private equality-move-readers
  "The readers `note-moved` keeps a copy of the moved terms for, each emptied by its own
  `take-equality-moves!`: `special/supersession-map`."
  [:supersessions])

(defn- note-moved
  "Add the classes of edge `e`'s two ends to each reader's `:moved` set
  (`take-equality-moves!`).  Read after the edge is applied: a union's class holds both
  old classes, and a split's two classes make up the old one."
  [rel [a b]]
  (let [ms (into (class-members rel a) (class-members rel b))]
    (reduce (fn [r k] (update-in r [:moved k] (fnil into #{}) ms)) rel equality-move-readers)))

(defn- refresh-equality
  "Reconcile the equality partition with belief, scoped to what `moved` names: only a
  moved supporter can change its believed status or its own edge's state, so the
  reconcile updates `:out` for `moved ∩ handles` and re-applies exactly those edges,
  through the reverse map `:handle-edge`, walked from whichever side is smaller.
  Unscoped, the i-th merge of a load re-asked belief of every supporter and re-derived
  the live state of every edge, Θ(N²) across the load.  nil `moved` is the unconditional reconcile
  (`refresh-beliefs`' two-arity): every supporter re-asked, every edge re-applied.  The
  edge of each supporter whose `:out` entry flipped is noted in `:moved`, and each
  supporter that left `:out` is added to `:believed-again` (`take-believed-again!`)."
  [rel believed? moved]
  (if-not (moved-touches? moved (:handles rel))
    rel
    (let [he       (:handle-edge rel)
          affected (cond (nil? moved) (vec (keys he))
                         (and (counted? moved) (<= (count moved) (count he)))
                         (filterv #(contains? he %) moved)
                         :else (filterv #(contains? moved %) (keys he)))
          out      (:out rel)
          flipped  (filterv #(not= (contains? out %) (not (believed? %))) affected)
          back     (filterv #(contains? out %) flipped)
          rel      (reduce (fn [r h]
                             (if (contains? out h)
                               (update r :out disj h)
                               (update r :out conj h)))
                           rel flipped)
          rel      (reduce apply-edge rel (if (nil? moved)
                                            (keys (:support rel))
                                            (distinct (keep he affected))))]
      (cond-> (reduce note-moved rel (distinct (keep he flipped)))
        (seq back) (update :believed-again (fnil into #{}) back)))))

(defn equality-partition
  "Compute `{:class :members}` from scratch, given the active undirected `edges` and
  the active `[preferred dispreferred]` claims.

  This is the **reference implementation**, the equality analogue of `closures`: the
  incremental union above and the class-local rebuild below must agree with it edge
  for edge, and the oracle test in `taxonomy_test` checks exactly that after every
  edit of a random sequence."
  [edges prefs]
  (let [rel (reduce (fn [r [a b :as e]]
                      (-> r (update :edges conj e)
                          (update :edge-idx idx-conj a e)
                          (update :edge-idx idx-conj b e)))
                    (empty-equality) edges)
        rel (reduce (fn [r [p d :as pp]]
                      (update-in r [:edge-prefs (pair p d)] (fnil conj #{}) pp))
                    rel prefs)]
    (-> (reduce install-class rel (components rel (into #{} (mapcat identity) edges)))
        (select-keys [:class :members]))))

(defn add-equality
  "Record `handle` as asserting that `a` and `b` denote one thing, merging their
  classes.  `preferred` names the term a `rewriteOf` puts on top (`a`, `b`, or nil
  for `sameAs` / `equals`, which deprecate nothing)."
  [tax a b handle preferred]
  (let [e (pair a b)]
    (swap! tax update :equality
           (fn [rel] (-> rel
                         (assoc-in [:support e handle] preferred)
                         (update :handles conj handle)
                         (update :handle-edge assoc handle e)
                         (update :out disj handle)
                         (apply-edge e)
                         (note-moved e)))))
  tax)

(defn del-equality!
  "Drop `handle`'s support for the merge of `a` and `b`.  The merge survives while any
  other sentex still asserts it; when the last one goes the class splits back into
  whatever its remaining edges still connect."
  [tax a b handle]
  (let [e (pair a b)]
    (swap! tax update :equality
           (fn [rel]
             (let [hs (dissoc (get-in rel [:support e] {}) handle)]
               (-> (if (seq hs)
                     (assoc-in rel [:support e] hs)
                     (update rel :support dissoc e))
                   (update :handles disj handle)
                   (update :handle-edge dissoc handle)
                   ;; a retracted supporter is no supporter, believed or defeated:
                   ;; `:out` is read against `:support`, so a stale member costs a
                   ;; set entry per retracted-while-defeated merge for the KB's life
                   (update :out disj handle)
                   (apply-edge e)
                   (note-moved e))))))
  tax)

(defn equality-moves?
  "Does `reader` hold moved terms `take-equality-moves!` has not taken?"
  [tax reader]
  (boolean (seq (get-in @tax [:equality :moved reader]))))

(defn take-equality-moves!
  "Empty `reader`'s copy of the equality partition's moved terms and return it: every
  term in the class of either end of an edge a supporter joined, left, or moved in or out
  of belief on since `reader`'s last call, read after the edge was applied.  A term whose
  class, representative or scoped class moved is among them, and so is a term whose class
  did not move.  nil when nothing moved.  The one reader (`equality-move-readers`) is
  `:supersessions`, for `special/supersession-map`."
  [tax reader]
  (let [m (get-in @tax [:equality :moved reader])]
    (when (seq m)
      (swap! tax update :equality
             (fn [rel] (let [left (dissoc (:moved rel) reader)]
                         (if (seq left) (assoc rel :moved left) (dissoc rel :moved)))))
      m)))

(defn take-believed-again!
  "Empty and return the equality supporters `refresh-equality` found believed since the
  last call while `:out` held them, or nil when there are none.  A supporter is in `:out`
  only after a reconcile found it disbelieved, so each of these became believed by a
  relabel and not by its arrival (`special/believed-again-sweeps`)."
  [tax]
  (let [hs (get-in @tax [:equality :believed-again])]
    (when (seq hs)
      (swap! tax update :equality dissoc :believed-again)
      hs)))

(defn representative
  "The term that stands for `term`'s equivalence class — `term` itself when nothing
  has merged it."
  [tax term]
  (get-in @tax [:equality :class term] term))

(defn scoped-class
  "`[members representative]` for `term` counting only the equality edges some
  supporter `visible?` admits — the equality analogue of the scoped closure reads,
  and the form a **context-scoped** rewrite needs.

  It has to be recomputed rather than filtered out of the global partition, because
  dropping an edge can *split* a class: `A~B~C` with only `A~B` visible is the class
  `{A B}`, and its representative is elected among those two alone, not inherited from
  the class `C` was in.  The election rule is `class-rep`'s, over the visible edges'
  preference claims — so a `rewriteOf` this context cannot see neither retires a term
  nor promotes one.

  Recomputed per call and not memoized: a class is a handful of terms, and the callers
  already pay a record fetch per supporter to decide `visible?`.  The **global** read
  is `representative` above and stays the fast path — nothing that has not merged ever
  reaches here."
  [tax term visible?]
  (let [rel  (:equality @tax)
        out  (:out rel #{})
        vis  (fn [e] (some (fn [[h _]] (and (not (contains? out h)) (visible? h)))
                           (get (:support rel) e {})))
        nbrs (fn [t] (into #{} (comp (filter vis) (mapcat identity))
                           (get (:edge-idx rel) t #{})))
        members (reach term nbrs)]
    (if (= 1 (count members))
      [members term]
      (let [ps (into #{}
                     (comp (mapcat (fn [m] (get (:edge-idx rel) m #{})))
                           (distinct)
                           (filter vis)
                           (mapcat (fn [e]
                                     (keep (fn [[h p]]
                                             (when (and (not (contains? out h)) (visible? h))
                                               (pref-pair e p)))
                                           (get (:support rel) e {})))))
                     members)
            preferred (into #{} (map first) ps)
            heads     (set/difference preferred (into #{} (map second) ps))]
        [members (term-min (cond (seq heads) heads (seq preferred) preferred :else members))]))))

(defn class-fully-visible?
  "Does `visible?` admit **every believed supporter of every active edge** in `term`'s
  class?  When it does, the scoped election *is* the global one — same members, because
  no edge drops, and same representative, because no preference claim drops — so the
  caller can take `representative`'s O(1) map lookup instead of rebuilding the class.

  The condition is per *supporter*, not per edge, and that is what makes it sound.  One
  edge may carry a `sameAs` and a `rewriteOf` at once; hiding only the `rewriteOf` leaves
  the class intact and moves the head, so an edge-level test would licence the fast path
  on exactly the case that needs the slow one.

  This is the common shape rather than an optimisation for a corner: a KB states its
  merges in `CxUniverse`, or in the context doing the reading, and either way every
  supporter is visible.  A reader pays one memoized `visible?` per supporter of a class
  that is a handful of terms — against `scoped-class`'s reachability walk and preference
  election, which is the cost this exists to skip."
  [tax term visible?]
  (let [rel (:equality @tax)
        out (:out rel #{})]
    (every? (fn [m]
              (every? (fn [e]
                        (every? (fn [[h _]] (or (contains? out h) (visible? h)))
                                (get (:support rel) e {})))
                      (get (:edge-idx rel) m #{})))
            (get (:members rel) (get (:class rel) term term) #{term}))))

(defn same-class? "Do `a` and `b` denote the same thing?" [tax a b]
  (= (representative tax a) (representative tax b)))

(defn equiv-class "Every term known equal to `term`, incl. itself." [tax term]
  (let [rel (:equality @tax)]
    (get (:members rel) (get (:class rel) term term) #{term})))

(defn retirable?
  "Can some reader's scoped election (`scoped-class`) retire `term`?  Every merged member
  but the representative can.  The representative can when a `rewriteOf` names it
  preferred and its class holds a supporter that is not such a claim: a reader that sees
  that supporter and not the claim elects another member.  A representative no claim
  names preferred is the smallest member, and every reader's election keeps it."
  [tax term]
  (let [head (representative tax term)]
    (or (not= term head)
        (let [rel    (:equality @tax)
              claims (for [m      (equiv-class tax term)
                           e      (get (:edge-idx rel) m)
                           [_ p]  (get (:support rel) e)]
                       (= head (first (pref-pair e p))))]
          (boolean (and (some true? claims) (some false? claims)))))))

(defn merged?
  "Has anything merged `term` at all?  The O(1) gate every scoped read takes first: a
  KB with no equalities, and a term in none of them, never pays for `scoped-class`."
  [tax term]
  (boolean (seq (get-in @tax [:equality :edge-idx term]))))

(defn merged-term-pred
  "A `term -> boolean` closed over **one** snapshot of the partition, or nil when the
  closure is empty — the gate for a caller asking `merged?` of many terms in a row.

  `merged?` derefs per call, which is the right shape for the single question a scoped
  class read asks and the wrong one for a filter running over every symbol of every
  match in a query's answer set.  Returning nil rather than a constantly-false predicate
  is what lets such a caller drop the whole filter, which is what every KB that has
  merged nothing does."
  [tax]
  (let [rel (:equality @tax)]
    (when (seq (:edges rel))
      (let [idx (:edge-idx rel)]
        (fn [term] (contains? idx term))))))

(defn deprecated?
  "Did a believed `rewriteOf` name `term` the dispreferred side?  False for a `sameAs`
  or `equals` member — those merge without deprecating either name.

  With a `visible?` supporter predicate, only the `rewriteOf`s that reader inherits
  count — the same scoping `representative` / `same-class?` / `equiv-class` take, and
  necessary for the same reason: a retirement is a sentex, so a context that cannot see
  it has not been told, and reporting the term deprecated there would contradict the
  representative that same context elects for it.  Read per supporter rather than off
  the aggregated `:edge-prefs`, since one edge may carry a `rewriteOf` and a `sameAs`
  at once and only the first deprecates."
  ([tax term] (deprecated? tax term nil))
  ([tax term visible?]
   (let [rel (:equality @tax)]
     (boolean
      (some (fn [e]
              (if-not visible?
                (some (fn [[_ d]] (= d term)) (get (:edge-prefs rel) e))
                (some (fn [[h p]]
                        (and (not (contains? (:out rel #{}) h))
                             (visible? h)
                             (= term (second (pref-pair e p)))))
                      (get (:support rel) e {}))))
            (get (:edge-idx rel) term #{}))))))

(defn- edge-pref-claims
  "The `[preferred dispreferred]` rewriteOf claims on edge `e` — all of them unscoped,
  only the believed and visible ones under `visible?`.  A `sameAs` / `equals`-only edge
  yields none, since its supporters name no preference (`pref-pair` returns nil)."
  [rel e visible?]
  (if-not visible?
    (get (:edge-prefs rel) e #{})
    (into #{}
          (keep (fn [[h p]]
                  (when (and (not (contains? (:out rel #{}) h)) (visible? h))
                    (pref-pair e p))))
          (get (:support rel) e {}))))

(defn spelling-representative
  "`term`'s representative considering only `rewriteOf` (spelling) edges — a `sameAs` /
  `equals` identity merge is **not** followed.  This is the mention read: a quoted term
  tracks a *spelling* rename of its symbol but not a *coreference* merge of its referent,
  so `res/representative-term` uses it inside a `quoting_function`'s arguments.

  The rewriteOf edges form their own sub-partition; the answer is the representative of
  `term`'s rewriteOf-connected component, elected by the same rule `class-rep` uses — a
  preferred term nothing deprecates, else the lexicographically smallest.  A term no
  rewriteOf touches — including one merged only by `sameAs` — is its own representative,
  returned unchanged.  With `visible?`, only the believed edges that reader inherits
  count, the scoping `deprecated?` / `representative` take.  Recomputed per call: a class
  is a handful of terms, and the caller's `merged?` gate skips it entirely for an
  unmerged one."
  ([tax term] (spelling-representative tax term nil))
  ([tax term visible?]
   (let [rel (:equality @tax)]
     (loop [seen #{term} frontier [term] claims #{}]
       (if-let [t (peek frontier)]
         (let [cs  (into #{}
                         (mapcat #(edge-pref-claims rel % visible?))
                         (get (:edge-idx rel) t #{}))
               nxt (into #{} (comp (mapcat (fn [[p d]] [p d])) (remove seen)) cs)]
           (recur (into seen nxt) (into (pop frontier) nxt) (into claims cs)))
         (let [preferred  (into #{} (map first) claims)
               deprecated (into #{} (map second) claims)
               heads      (set/difference preferred deprecated)]
           (cond (seq heads)     (term-min heads)
                 (seq preferred) (term-min preferred)
                 :else           term)))))))

(defn equality-edges [tax] (get-in @tax [:equality :edges] #{}))

(defn equality-prefs
  "Every active `[preferred dispreferred]` claim — the directed `rewriteOf` graph,
  flattened out of the per-edge preference sets.  `wff` walks it to reject a cycle;
  nothing else needs the direction, since the partition itself is undirected."
  [tax]
  (into #{} (mapcat identity) (vals (get-in @tax [:equality :edge-prefs] {}))))

(defn equality-supporters
  "The handles of the sentexes asserting an **active** equality edge incident on
  `term` — the merges that put `term` in a class other than its own.

  Migration reads this to justify a rewritten twin: each incident edge is an
  independent witness for the rewrite, so the twin gets one justification per
  supporter and survives losing any single one."
  [tax term]
  (let [rel (:equality @tax)]
    (into #{}
          (comp (mapcat (fn [e] (keys (get (:support rel) e {}))))
                (remove (:out rel #{})))
          (get (:edge-idx rel) term #{}))))

;; ---- schematic rewrite rules (oriented equational rewriting) -------------
;; A schematic `(equals L R)` is oriented once (by `vaelii.impl.rewrite/orient`, at
;; the assert layer) into a rewrite `[lhs rhs]` and cached here.  The cache holds
;; only the oriented pair, its handle, and the equation's context — the term algebra
;; is `vaelii.impl.rewrite`'s and stays out of the taxonomy.  Belief rides on the
;; handle: `:rewrite-active` is the subset of `:rewrite-support` whose equation is
;; believed, reconciled by `refresh-beliefs`.

(defn add-rewrite-rule
  "Cache the oriented rewrite `lhs → rhs` asserted by equation `handle` in `context`.
  Recorded in both the support map (for revival) and the active map (assumed believed
  on assert; a settle reconciles)."
  [tax handle lhs rhs context]
  (let [entry {:handle handle :lhs lhs :rhs rhs :context context}]
    (swap! tax (fn [t] (-> t
                           (assoc-in [:rewrite-support handle] entry)
                           (assoc-in [:rewrite-active handle] entry)))))
  tax)

(defn del-rewrite-rule!
  "Drop equation `handle`'s rewrite rule entirely — the last (and only) supporter is
  gone, so the rule leaves both maps."
  [tax handle]
  (swap! tax (fn [t] (-> t
                         (update :rewrite-support dissoc handle)
                         (update :rewrite-active dissoc handle))))
  tax)

(defn rewrite-rules
  "The active oriented rewrite rules — a seq of `{:handle :lhs :rhs :context}` for
  every schematic equation currently believed.  `vaelii.impl.kb/rewrite-term` reads
  these to normalize terms; the empty case is the gate that keeps normalization a
  no-op for a KB with no schematic equations.

  **Content-ordered, not insertion-ordered.**  Normalization tries rules in this
  order at each redex, so two overlapping rules that could rewrite one term must be
  ordered by *content* and not by which equation was asserted first — otherwise the
  normal form (and thus the stored twin) would depend on arrival order, which
  order-independence (docs/nmtms.md) forbids.  The key is the LHS then the RHS,
  arbitrary but stable and handle-free, so the same rule *set* always yields the same
  normal form, confluent or not.

  **The key is structural**, compared by `nm/compare-form` rather than printed.  A
  printed key is where this ordering would leak: `rewrite-active` is a map keyed by
  handle, so a caller with an ambient `*print-length*` — a REPL's, typically — would
  elide two long left-hand sides to one prefix, collapse the key, and drop the choice
  between two overlapping rules back onto that map's iteration order, which is a fact
  about which equation was asserted first.

  **Sorted once per rule set, not once per call.**  `kb/rewrite-term` calls this and
  `kb/rewrite-goal` calls that, so an unmemoized sort would put a key-build-per-rule
  cost on every `query` carrying a context — a cost the empty case (no schematic
  equations, the KB the gate above is written for) does not have but every KB with one
  would pay on every read.
  The order is memoized in the `:rewrite-order` side atom, beside the main map for the
  reasons `:closure-memo` is (a read that memoizes must not contend with the writer, or
  mutate the snapshot a concurrent reader holds).

  Stamped on the **identity** of the `:rewrite-active` map, not on a generation counter.
  A persistent map is its own change detector: every writer here already replaces it
  (`add-rewrite-rule`, `del-rewrite-rule!`, `refresh-rewrite`, `clear-relations!`) and
  none can replace it without producing a different object, so no writer has to remember
  to bump anything — the failure mode a counter has, and the one that matters most for a
  field three separate paths write.  It is also ABA-free where a counter is not:
  `clear-relations!` installs a fresh empty map, which is a *new* object, whereas a
  counter reset to 0 would make a cleared taxonomy read as the pre-clear one (exactly why
  `clear-relations!` has to drop the gen-stamped memo by hand).  The cost is a re-sort
  when `refresh-rewrite` rebuilds an equal set, which is a handful of rules."
  [tax]
  (let [t      @tax
        active (:rewrite-active t)
        memo   (:rewrite-order t)
        cur    @memo]
    (if (identical? active (:for cur))
      (:rules cur)
      (let [rs (nm/sort-by-content-key (juxt :lhs :rhs) (vals active))]
        (reset! memo {:for active :rules rs})
        rs))))

(defn- refresh-rewrite
  "Reconcile `:rewrite-active` with belief: a rule is active iff its equation handle is
  believed.  Recomputed rather than diffed — the rule set is tiny."
  [t believed? moved]
  (if-not (moved-touches? moved (:rewrite-support t))
    t
    (assoc t :rewrite-active
           (into {} (filter (fn [[h _]] (believed? h))) (:rewrite-support t)))))

(defn- names-a-value?
  "Does flat-cache key `k` name a value (`nm/value?`) where its declaration names a type?
  `wff` refuses such a declaration at assert, and an older writer's store can hold one;
  its key stays inactive."
  [[kind a]]
  (case kind
    (:disjoint :sib-exception) (some nm/value? a)               ; a = #{x y}
    (:metatype :sib-disjoint)  (nm/value? a)
    :cover                     (let [[whole parts] a]
                                 (or (nm/value? whole) (some nm/value? parts)))
    false))

(defn- refresh-cache-support
  "Reconcile the seven flat caches — `disjoint`, the disjoint metatypes and their
  members, the sibling-disjoint marks, the `siblingDisjointException` pairs, the
  predicate properties, `inverse` and the declared arities — with current
  belief, the way `refresh-relation` does for genl.  Each key in `ks` (`moved-keys`) and
  `:cache-dirty` is active iff some stored supporter is believed; install or uninstall its
  cache entry to match, reusing the very `cache-install` / `cache-uninstall` the assert
  path uses so the two can never disagree on what an active entry is.

  Every op here is O(1) and idempotent, so a reconciled entry is re-affirmed rather than
  diffed: there is no closure to rebuild, and `cache-install` on an entry already present
  changes nothing.  (genl's `refresh-relation` diffs only because rebuilding a *closure*
  is expensive.)

  An entry no moved handle supports and no writer left dirty is provably unchanged, so
  belief is never evaluated for it: the reconcile costs what moved, not what the KB
  declares.  This is the pass that discharges `:cache-dirty`, so it clears the set on the
  way in.  A key with no stored supporter left is skipped rather than reconciled: an empty
  `:cache-ctxs` written back under it would read as an entry asserted from nowhere."
  [t believed? ks]
  (let [touched (into (:cache-dirty t) ks)]
    (if (empty? touched)
      t
      (reduce (fn [t k]
                (let [[t sup] (held-supporters t k)]
                  (if (seq sup)
                    (let [cs (believed-ctxs sup believed?)]
                      (-> (if (and (seq cs) (not (names-a-value? k)))
                            (cache-install t k)
                            (cache-uninstall t k))
                          ;; the flat-cache twin of refresh-relation's third arm: an entry
                          ;; that stays active can still change contexts when one of
                          ;; several supporters moves belief
                          (set-cache-ctxs k cs)))
                    t)))
              (assoc t :cache-dirty #{})    ; this pass is what discharges them
              touched))))

(defn- key-edges
  "The edges `[a b]` of relation `rel-key` among the taxonomy keys `ks`."
  [ks rel-key]
  (into #{} (comp (filter #(= rel-key (nth % 0))) (map (fn [[_ a b]] [a b]))) ks))

(defn refresh-beliefs
  "Reconcile the cached relations with current belief: an edge (or a flat-cache entry)
  is active iff some sentex asserting it is believed.  Called after a relabel (from
  `settle`), which is the only thing that can flip a supporter's label without adding
  or removing one.

  Cheap in the common case — `believed?` is an in-memory JTMS lookup, the closures are
  only rebuilt if the active edge set actually moved, an equality edge whose supporters
  did not change label is skipped outright, and the flat caches are single-op
  idempotent reconciles.  So a settle that defeats nothing applies no difference; what it
  still pays is its **region**.  Only the equality partition and the rewrite rules decline
  to look at all (the gate below), while the two transitive relations and the flat caches
  evaluate `believed-ctxs` for every edge and entry the region names before finding that
  none of them moved.  Zero work is a region naming nothing, not a belief that held still.

  Every cache follows belief here — the two transitive relations, the equality
  partition, and the seven flat caches (`disjoint`, disjoint metatypes + members, the
  sibling-disjoint marks, the `siblingDisjointException` pairs, the predicate properties,
  `inverse`, the declared arities) — so a defeated declaration stops taking effect the
  moment `settle` relabels, and a revived one takes effect again.

  `moved` is the set of handles whose belief just flipped (`jtms/touched`, a superset),
  and the caches read it two ways.  The two transitive relations and the flat caches
  **scope** by it — `moved-keys` turns the moved handles into the keys they install,
  read from the supporter families, and a settle reconciles those and nothing else, which
  is what keeps a flip in a 100k-edge taxonomy the price of a flip.

  The equality partition and the rewrite rules **gate** on it instead: a cache no moved
  handle supports is left alone, and a hit rescans it.  Both hold the KB's asserted
  term-identity claims rather than its vocabulary, and the gate reads whichever of the two
  sides is smaller, so a settle that moves neither pays the size of its own region.

  `nil` reconciles every key with a stored supporter, for a caller holding no region.
  `recover` is that caller and passes it: a settle's reconcile is scoped *and* gated on
  belief having moved, so a declaration nothing supports — OUT from the moment its node is
  made, opposed by nothing — has no settle event to lean on (`core/recover`).  Every
  `settle` path names a region instead; the supersession pass widens its own by hand
  rather than dropping it, because a supersession flip is a belief change with no relabel
  to record it."
  ([tax believed?] (refresh-beliefs tax believed? nil))
  ([tax believed? moved]
   (swap! tax (fn [t]
                (let [[t ks] (moved-keys t moved)
                      g-es   (key-edges ks :genl)
                      cx-es  (key-edges ks :genlCx)]
                  (-> t
                      (refresh-relation :genl believed? g-es)
                      (refresh-relation :genlCx believed? cx-es)
                      (update :equality refresh-equality believed? moved)
                      (refresh-rewrite believed? moved)
                      (refresh-cache-support believed?
                                             (into #{} (filter #(of-relation? :flat %)) ks))))))
   tax))

(defn clear-relations!
  "Drop **every** cache and the supporter cache.  `recover` rebuilds them from the
  durable store and must not merge into whatever the in-memory taxonomy already had —
  otherwise a stale entry outlives the data it came from.

  Clearing must cover **every** cache, not just the two transitive relations:
  because `recover` merges into whatever it clears, a merge can only ever *add*, so a
  disjoint pair, a predicate property, an inverse or a declared arity whose sentex is
  gone would survive the recovery that is supposed to re-derive it.  The equality
  partition is the same story and worse — a stale merge makes two individuals one.
  Clearing all of them is what makes `recover` a rebuild rather than a top-up.  The
  supporters themselves are stored content in the index, which this leaves alone."
  [tax]
  (swap! tax (comp #(update % :epoch (fnil inc 0)) assoc)
         :genl (empty-relation) :genlCx (empty-relation)
         :equality (empty-equality)
         :disjoint #{} :disjoint-index {} :disjoint-metatypes #{} :metatype-members {}
         :sibling-disjoint #{} :sib-exception-index {}
         :covers {} :cover-parts {} :partitions #{}
         :props {} :inverse {} :genl-inverse-down {} :genl-inverse-up {} :arity {} :functional-in-arg {} :commuting {}
         :cache-dirty #{} :cache-ctxs {}
         :supporters empty-supporters
         :cache-moves (journal/restart nil)
         :rewrite-support {} :rewrite-active {})
  ;; The read memo is stamped with each relation's `:gen`, which the fresh
  ;; `empty-relation`s just reset to 0, so drop the memo too — otherwise a lingering
  ;; entry could be mistaken for a current one.  The rewrite order is stamped on the map object it
  ;; sorted, and the fresh `{}` above can never be that object, so dropping it
  ;; releases the rules it retains rather than correcting an answer.
  (reset! (:closure-memo @tax) {})
  (caches/lru-clear! (:closure-lru @tax))
  (reset! (:rewrite-order @tax) nil)
  tax)

;; ---- introspection (for rendering) --------------------------------------

(defn genl-edges   [tax] (get-in @tax [:genl :edges] #{}))
(defn genlCx-edges [tax] (get-in @tax [:genlCx :edges] #{}))

(defn edge-contexts
  "The supporting contexts of active edge `[a b]` in relation `rel-key` — the
  believed supporters' after a settle, every supporter's between a write and the
  settle (the same discipline as `:edges` liveness).  nil in the set is a supporter
  with no recorded context, which constrains everywhere.  Empty when the edge is
  not active."
  [tax rel-key e]
  (get-in @tax [rel-key :edge-ctxs e] #{}))

(defn derives-from?
  "Does `handle` assert something the taxonomy derives an answer from — an edge of a
  cached relation (`genl`, `genlCx`), or a flat-cache entry (a separation, a metatype
  mark and its memberships, a sibling-disjointness mark, a `siblingDisjointException` pair, a cover roster, a
  predicate property, an inverse, an arity)?

  **One read**, of the keys `handle` installs (`keys-of`), which the reconcile reads
  forward and the supporter family holds.  The equality partition is left out: it holds no definitional grounds a clash convicts
  through, and a caller asking about one is asking about `genl` and the flat caches.

  It names a handle the taxonomy reads *at all* rather than the grounds of one nogood."
  [tax handle]
  (boolean (seq (keys-of @tax handle))))

(defn cache-contexts
  "The supporting contexts of flat-cache entry `k` (`[:disjoint #{a b}]`,
  `[:prop kind pred]`, …) — the flat-cache twin of `edge-contexts`."
  [tax k]
  (get-in @tax [:cache-ctxs k] #{}))

(defn asserting-contexts-among
  "The contexts of `ctxs` that state a `genl` edge or a flat-cache declaration, as a set:
  `census-in` over the two, with no belief callback."
  [tax ctxs]
  (let [t  @tax
        cs (set ctxs)]
    (into (first (census-in t :genl cs)) (first (census-in t :flat cs)))))

(defn visible-supporters
  "The handles of flat-cache entry `k`'s recorded supporters a reader at `context` sees:
  each stated from a context in `context`'s ancestor set or with no recorded context,
  through the `except`-aware check while an `except` is stored
  (`scope-admits-supporter?`).  Every supporter for an unscoped `context`.  Belief is the
  caller's filter, except where that check reads it."
  [tax k context]
  (let [t   @tax
        sup (supporters-of t k)]
    (cond
      (empty? sup)                    #{}
      (not (scoped-context? context)) (set (keys sup))
      (supporter-filter-active? t)
      (let [scope {:contexts (context-up tax context) :context context
                   :supporter-visible? (visible-fn t)}]
        (into #{} (keep (fn [[h c]] (when (scope-admits-supporter? scope h c) h))) sup))
      :else
      (let [up (context-up tax context)]
        (into #{} (keep (fn [[h c]] (when (or (nil? c) (contains? up c)) h))) sup)))))

(defn flat-contexts
  "Each flat-cache entry mapped to the contexts its recorded supporters assert it from, as
  one value: a memo diffs two of them to find the entries a declaration stated, withdrawn
  or moved to another context moved, where `flat-moves` does not reach back."
  [tax]
  (:cache-ctxs @tax))

(defn flat-moves
  "`[pos moved]`: the position of the journal `set-cache-ctxs` writes, and the flat-cache
  keys whose supporting contexts moved since the position `since` (an earlier `pos`), nil
  when the journal does not reach back that far or `since` is nil."
  [tax since]
  (let [j (:cache-moves @tax)]
    [(journal/position j) (when (some? since) (journal/since j since))]))

(defn supported-keys
  "The flat-cache keys the handles `hs` support, as a set."
  [tax hs]
  (let [t @tax]
    (into #{} (comp (mapcat #(keys-of t %)) (filter #(of-relation? :flat %))) hs)))

(defn separation-ends
  "The types a move of flat-cache entry `k` can change `disjoint?` between: a type whose
  global `genls` hold none of them reads the same separations either side of the move.
  The pair of a `disjoint` or `siblingDisjointException` key, a `sibling_disjoint`
  parent, a metatype's members, a member, and a cover's whole and parts.  nil for a key
  no separation reads."
  [tax k]
  (case (first k)
    (:disjoint :sib-exception) (set (second k))
    :sib-disjoint              #{(second k)}
    :metatype                  (get-in @tax [:metatype-members (second k)] #{})
    :member                    #{(nth k 2)}
    :cover                     (let [[whole parts] (second k)] (conj (set parts) whole))
    nil))

(defn- cache-entry-visible?
  "Does flat-cache entry `k` have a believed supporter visible from `context`?

  Without exceptions, a context-set intersection is sufficient.  With exception
  filtering active, each supporter is checked individually: the exception-aware
  context ancestor set handles excepted genlCx links and the KB callback handles belief
  plus exceptions targeting the declaration itself."
  [tax k context]
  (if-not (scoped-context? context)
    true
    (let [t @tax]
      (if (supporter-filter-active? t)
        (let [scope {:contexts (context-up tax context)
                     :context context
                     :supporter-visible? (visible-fn t)}]
          (boolean
           (some (fn [[h c]] (scope-admits-supporter? scope h c))
                 (supporters-of t k))))
        (ctxs-visible? (get-in t [:cache-ctxs k])
                       (closure-of tax :genlCx :fwd context))))))
(defn types
  "Every type currently in the genl hierarchy — the nodes of the closure, i.e. every
  type named by some believed `genl` edge.  With a `context`, only a node touched by
  an edge visible from it counts: the same visibility `genl?` and `disjoint?` read,
  applied to every edge instead of to one pair's walk."
  ([tax] (get-in @tax [:genl :nodes] #{}))
  ([tax context]
   (let [rel   (:genl @tax)
         scope (relation-scope tax :genl context)]
     (if (nil? scope)
       (:nodes rel)
       (let [t      @tax
             ectxs  (:edge-ctxs rel)
             visible? (if (map? scope)
                        (fn [[a b]] (some (fn [[h c]] (scope-admits-supporter? scope h c))
                                          (supporters-of t [:genl a b])))
                        (fn [e] (ctxs-visible? (get ectxs e) scope)))]
         (into #{} (comp (filter visible?) (mapcat identity)) (:edges rel)))))))
(defn contexts     [tax] (get-in @tax [:genlCx :nodes] #{}))
(defn disjoint-pairs [tax] (:disjoint @tax))

(defn separation-stamp
  "What a separation or a cover over two types reads of `tax` besides the `genl` closures,
  as one value compared with `=`: the separating and covering declarations with the
  `siblingDisjointException` pairs that exempt a pair from the separation marks.  A declaration moving
  replaces its roster's value, so an unmoved stamp compares on identity.  The closures that moved are `moves-since`'s."
  [tax]
  (let [t @tax]
    [(:disjoint t) (:disjoint-metatypes t) (:metatype-members t)
     (:sibling-disjoint t) (:partitions t) (:covers t) (:sib-exception-index t)]))

(defn separation-moves
  "The types whose separations can differ between two `separation-stamp` values `old` and
  `new`, as a set: the pair of each `disjoint` and `siblingDisjointException` entry one holds and the
  other does not, the members of a disjoint metatype that moved and each member that
  moved, a `sibling_disjoint` parent that moved, and the parts of a partition that moved.
  A type whose global `genls` hold none of them reads the same separation of every
  partner under both values.  A cover moving separates nothing and adds no type.  Reads
  a roster only when the two values hold different ones, and then costs its entries."
  [old new]
  (let [[dj mt mm sib parts _ exc]       old
        [dj' mt' mm' sib' parts' _ exc'] new
        moved   (fn [a b] (when-not (identical? a b)
                            (concat (remove #(contains? b %) a) (remove #(contains? a %) b))))
        changed (fn [a b] (when-not (identical? a b)
                            (filter #(not= (get a %) (get b %)) (distinct (concat (keys a) (keys b))))))]
    (-> #{}
        (into cat (moved dj dj'))
        (into (mapcat #(concat (get mm %) (get mm' %))) (moved mt mt'))
        (into (mapcat #(moved (get mm %) (get mm' %))) (changed mm mm'))
        (into (moved sib sib'))
        (into (mapcat second) (moved parts parts'))
        (into (mapcat #(cons % (moved (get exc %) (get exc' %)))) (changed exc exc')))))

(defn cover-moves
  "The wholes of the covering declarations one of two `separation-stamp` values `old` and
  `new` holds and the other does not, as a set.  Reads the cover roster only when the two
  values hold different ones."
  [old new]
  (let [a (nth old 5) b (nth new 5)]
    (if (identical? a b)
      #{}
      (into #{} (filter #(not= (get a %) (get b %))) (concat (keys a) (keys b))))))

(defn moves-since
  "The lower ends of the edges of relation `rel-key` whose activation or supporting
  contexts moved after generation `gen` (`note-move`), as a set.  A closure that moved
  since `gen` is one of a node at or below one of them.  A relation rebuilt from nothing
  (`clear-relations!`) restarts its generation, and its log holds only what the rebuild
  moved."
  [tax rel-key gen]
  (let [ms (:moves (get @tax rel-key))]
    (into #{} (mapcat val) (if (sorted? ms) (subseq ms > gen) (filter #(> (key %) gen) ms)))))

(defn relation-gen
  "The generation counter of a cached relation (`:genl` / `:genlCx`), bumped on
  every edge change.  A caller memoizing something derived from a closure reads this to
  notice it must recompute, without comparing edge sets — which is the whole point,
  since the edge set is the thing that is too big to compare."
  [tax rel-key]
  (get-in @tax [rel-key :gen] 0))

(defn relation-epoch
  "How many times `clear-relations!` has rebuilt `tax`'s relations.  A rebuild restarts
  each `relation-gen` at 0, so a stamp that must not compare equal across a `recover`
  carries this beside the generations (`special/taxonomy-generations`)."
  [tax]
  (:epoch @tax 0))

(defn- reachable-in?
  "Does `src` reach `tgt` in relation `rel-key`, following `:fwd`?  The depth-pruned
  `reachable?` rejects most pairs in O(1) and never materializes a closure — the cheap
  path shared by `genl?` / `sees?` and the assert-time cycle checks in `wff`.

  A relation left `:loose?` by a deferred batch has no sound potential yet, so the
  depth is withheld and the walk runs unpruned: slower, and the same answer."
  [tax rel-key src tgt]
  (let [rel (get @tax rel-key)]
    (reachable? src tgt (:fwd rel) (when-not (:loose? rel) (:depth rel)) (:scc rel))))

;; ---- genl (types) --------------------------------------------------------
;;
;; Each read comes in two, and the pair is the third invariant made visible in the
;; names (`context scoping`, README.md): the **scoped** one walks only the edges
;; visible from a context (`visible-ctxs`), and the `-global` one walks every active
;; edge whoever can see it.  A scoped read whose visible set comes back nil — no
;; context, a `?var`, or a context that sees every asserting context — is
;; byte-identical to the global one, which is exactly why they must not share a name:
;; on that KB the two agree, and the caller that meant to scope and did not finds out
;; on the KB where they differ.  An empty visible set still walks: an edge with a
;; nil-context supporter constrains everywhere, including from a context that sees no
;; asserting context at all.
;;
;; `-global` is the deliberate read and not the convenient one — `lein lint`'s **E17**
;; rosters the callers, so a new one is a decision somebody wrote down.

(defn genls-global
  "Supertypes of t, incl t, through **every** active edge — no context scope.

  For a caller that has no vantage to read from, or one whose answer must not depend on
  having one: an assert-time refusal, a re-check trigger that must over-approximate, a
  rebuild.  A caller holding a context wants `genls`."
  [tax t]
  (closure-of tax :genl :fwd t))

(defn genls
  "Supertypes of t, incl t, through the edges visible from `context` (docs/contexts.md).

  `genls-global` is the unscoped read, and it is spelled out rather than reached by
  dropping the argument."
  [tax t context]
  (if-some [scope (relation-scope tax :genl context)]
    (closure-of-vis tax :genl :fwd t scope)
    (closure-of tax :genl :fwd t)))

(defn genls-asserted-in
  "Supertypes of t, incl t, through the active edges some supporter asserts from a
  context in the set `ctxs`, with no belief callback.  A predicate `genl` edge is forced
  monotonic, so for a predicate this is `genls` from a reader whose ancestor set is
  `ctxs`.  It reads no belief, so a caller that must not re-enter the supporter callback
  (`res/supporter-believed?`) reads it in place of a scoped `genls`."
  [tax t ctxs]
  (closure-of-vis tax :genl :fwd t ctxs))

(defn- genl-path
  "One path of active `genl` edges from `sub` to `super`, as the nodes along it, or nil
  when there is none: a walk pruned by the depth potential as `reachable-filtered?`'s
  is, keeping each node's parent so the path reads back."
  [rel sub super]
  (let [adj   (:fwd rel)
        depth (when-not (:loose? rel) (:depth rel))
        scc   (:scc rel)
        dt    (some-> depth (get super))
        ctgt  (get scc super)
        over? (cond (nil? depth) (constantly true)
                    (nil? ctgt)  #(> (get depth % -1) dt)
                    :else        #(let [d (get depth % -1)]
                                    (or (> d dt) (and (= d dt) (= ctgt (get scc %))))))]
    (cond
      (= sub super)                        [sub]
      (and depth (or (nil? dt) (not (over? sub)))) nil
      :else
      (loop [parent {sub nil}, stack [sub]]
        (when-let [n (peek stack)]
          (let [ns (get adj n)]
            (if (contains? ns super)
              (loop [path (list n super), p (parent n)]
                (if (some? p) (recur (conj path p) (parent p)) (vec path)))
              (let [fresh (into [] (remove #(or (contains? parent %) (not (over? %)))) ns)]
                (recur (into parent (map #(vector % n)) fresh) (into (pop stack) fresh))))))))))

(defn genl-asserted-in?
  "Is `sub` at or below `super` through the active edges some supporter asserts from a
  context in the set `ctxs`, with no belief callback?  Membership in
  `genls-asserted-in`'s answer, walked depth-pruned (`reachable-filtered?`) with no
  closure built.

  The answer is a function of the relation's edges and their supporting contexts, which
  `:gen` moves with, and of `ctxs`, so it is held in the closure cache under both: a
  reader's arity read asks it of every stored pair of related predicates, and readers
  whose ancestor sets assert the same `genl` contexts ask the same pairs.  Before the
  walk it reads one path through every active edge (`genl-path`, held in the closure
  cache too): none is a no for every set, and one whose every edge `ctxs` states is a
  yes, so the walk runs only for a set stating part of that path."
  [tax sub super ctxs]
  (let [t   @tax
        rel (:genl t)
        lru (:closure-lru t)
        k   [:genl (:gen rel) :asserted-in ctxs sub super]
        hit (caches/lru-get lru k)]
    (if (some? hit)
      hit
      (let [pk   [:genl (:gen rel) :path sub super]
            held (caches/lru-get lru pk)
            path (if (some? held)
                   held
                   (caches/lru-put! lru pk (or (genl-path rel sub super) ::none)))
            ectx (:edge-ctxs rel)]
        (caches/lru-put! lru k
                         (boolean
                          (and (not= ::none path)
                               (or (every? (fn [[a b]] (ctxs-visible? (get ectx [a b]) ctxs))
                                           (partition 2 1 path))
                                   (reachable-filtered? sub super t :genl ctxs
                                                        (when-not (:loose? rel) (:depth rel))
                                                        (:scc rel))))))))))

(defn genls-asserted-among
  "The terms of the set `among` at or above `sub` through the active edges some supporter
  asserts from a context in the set `ctxs`, with no belief callback: `genl-asserted-in?`
  of each, read off one walk up from `sub`.  The walk is pruned by the depth potential at
  the shallowest term of `among`, keeping a node level with it when the node sits in a
  component, as `reachable-filtered?` keeps one level with its target, and it stops once
  every term of `among` is reached.  For a caller asking one term against many above it,
  where a walk per pair costs the pairs times the reach."
  [tax sub among ctxs]
  (if (empty? among)
    #{}
    (let [t     @tax
          rel   (:genl t)
          depth (when-not (:loose? rel) (:depth rel))
          scc   (:scc rel)
          self  (if (contains? among sub) #{sub} #{})
          ;; a term the potential does not rank is reached by no walk
          among (cond->> (disj among sub)
                  depth (into #{} (filter #(some? (get depth %)))))
          mind  (when (and depth (seq among)) (reduce min (map #(get depth %) among)))
          over? (cond (nil? depth) (constantly true)
                      (nil? mind)  (constantly false)
                      :else        #(let [d (get depth % -1)]
                                      (or (> d mind) (and (= d mind) (some? (get scc %))))))
          want  (count among)]
      (if (or (zero? want) (not (over? sub)))
        self
        (loop [seen #{sub}, stack [sub], found #{}]
          (if-let [n (peek stack)]
            (let [ns    (visible-neighbours t :genl :fwd ctxs n)
                  found (into found (filter among) ns)]
              (if (= want (count found))
                (into self found)
                (let [fresh (into [] (remove #(or (contains? seen %) (not (over? %)))) ns)]
                  (recur (into seen fresh) (into (pop stack) fresh) found))))
            (into self found)))))))

(defn supporter-count-in
  "How many facts stating a supporter of a `rel-key` edge are stored in the contexts of
  the set `ctxs`, either polarity and whatever their belief: one leaf count per context
  stating one, per functor (`census-functors`).  A raw taxonomy counts its recorded
  supporters."
  [tax rel-key ctxs]
  (let [t   @tax
        idx (:index t)
        fs  (census-functors t rel-key)
        per (when-not (:raw? t) (mapv #(reads/stored-count-with-functor-in idx % ctxs) fs))]
    (if (and per (every? some? per))
      (reduce + 0 per)
      (transduce (comp (mapcat vals) (filter #(contains? ctxs %)) (map (constantly 1))) + 0
                 (vals (raw-supporters t rel-key))))))

(defn asserting-contexts-in
  "The contexts of the set `ctxs` that assert a supporter of a `rel-key` edge, or nil when
  `ctxs` holds every context asserting one: a closure over the edges asserted in `ctxs` is
  then the global closure, and the set answers the same as `ctxs` does otherwise."
  [tax rel-key ctxs]
  (census-among @tax rel-key ctxs))

(defn specs-global
  "Subtypes of t, incl t, through **every** active edge — no context scope.
  `genls-global`'s reasoning, the other direction."
  [tax t]
  (closure-of tax :genl :rev t))

(defn- reach-within
  "The reach of `node` over `adj` (a fn node → neighbours) when it holds at most `lim`
  terms, else nil: the walk stops at the first term past `lim`."
  [node adj ^long lim]
  (when (<= 1 lim)                                    ; the reflexive answer alone is over it
    ;; one neighbour at a time, so a node with a million children stops at `lim` rather
    ;; than after adding all of them
    (loop [seen (transient #{node}), stack [node]]
      (if-let [n (peek stack)]
        (let [[seen stack] (reduce (fn [[seen stack :as acc] x]
                                     (cond
                                       (get seen x)          acc
                                       (>= (count seen) lim) (reduced nil)
                                       :else                 [(conj! seen x) (conj stack x)]))
                                   [seen (pop stack)]
                                   (adj n))]
          (when seen (recur seen stack)))
        (persistent! seen)))))

(defn- closure-within
  "`closure-of`'s answer for `node` when it holds at most `limit` terms, else nil.  A
  closure the closure cache already holds is counted there; otherwise the walk stops
  at the first term past `limit` and stores nothing, so asking about a node with a
  million descendants costs `limit` steps rather than a million."
  [tax rel-key dir-key node limit]
  (let [t    @tax
        rel  (get t rel-key)
        memo (caches/lru-get (:closure-lru t) [rel-key (:gen rel) dir-key node])
        lim  (long limit)]
    (if memo
      (when (<= (count memo) lim) memo)
      (reach-within node #(get (get rel dir-key) %) lim))))

(defn- closure-within-vis
  "`closure-of-vis`'s answer for `node` when it holds at most `limit` terms, else nil:
  `closure-within` over the edges effective in `scope`.  A scoped closure the cache
  already holds is counted there; otherwise the walk stops past `limit` and stores
  nothing."
  [tax rel-key dir-key node scope limit]
  (let [t    @tax
        rel  (get t rel-key)
        memo (caches/lru-get (:closure-lru t) [rel-key (:gen rel) dir-key node scope])
        lim  (long limit)]
    (if memo
      (when (<= (count memo) lim) memo)
      (reach-within node #(visible-neighbours t rel-key dir-key scope %) lim))))

(defn genls-global-within
  "`genls-global` of `t` when it holds at most `limit` terms, else nil — for a caller that
  wants the closure only when it is small, and must not pay for building a large one to
  find out."
  [tax t limit]
  (closure-within tax :genl :fwd t limit))

;; ---- genls-global-union: something small of every type above each of many ----

(defn genls-global-union
  "The union of what the transducer `xf` makes of each term of `genls-global` of `t`, for
  a caller asking something small of every type above each of many: `arity/recompute-arity`
  asks which exact lengths are bound at or above every tracked functor at a rebuild.  Built
  like the closure, from the parents' answers (`reach-by-parents`), but each answer holds
  only what `xf` makes, which is a few terms or none where the closure holds every
  ancestor, so reading it for every type costs the edges rather than the sum of the
  closures.

  Nothing enters the closure cache.  `memo`, a volatile map the caller makes for one `xf`
  over one still taxonomy, keeps the answers by component representative across the
  caller's reads.  A cycle `:scc` has not recorded reads the closure instead."
  [tax t xf memo]
  (let [rel  (:genl @tax)
        scc  (:scc rel)
        node (get scc t t)]
    (or (get @memo node)
        (reach-by-parents node #(get (:fwd rel) %) scc
                          #(get @memo %) #(vswap! memo assoc %1 %2) xf nil)
        (into #{} xf (closure-of tax :genl :fwd t)))))

(defn genls-global-union-held
  "`genls-global-union` of `t` with the answers by component representative read from
  `(held node)` and handed to `(hold! node answer)`, for a caller keeping them past one
  pass in a store it retires itself: `arity/entry` holds them in a weighted LRU, and the
  ancestors a type shares with one read before are not read again.  An answer held by one
  call is read by the next, so a call whose `xf` makes something else of a term replaces
  the answers it held under the terms that differ."
  [tax t xf held hold!]
  (let [rel  (:genl @tax)
        scc  (:scc rel)
        node (get scc t t)]
    (or (held node)
        (reach-by-parents node #(get (:fwd rel) %) scc held hold! xf nil)
        (into #{} xf (closure-of tax :genl :fwd t)))))

(defn genl-representative
  "The representative of the `genl` component `t` sits in, which `genls-global-union` keys
  its answers by: `t` itself outside a cycle."
  [tax t]
  (get-in @tax [:genl :scc t] t))

(defn genls-global-among
  "`genls-global` of `t` cut to the terms the set `among` holds: `genls-global-union` with
  a filter, and `memo` is kept for one `among`.  Without `memo`, a walk down from each
  term of `among` to `t` (`reached-from?`) answers the same cut, for a caller asking one
  `t` about a few terms: it costs the terms' descendants above `t`'s depth, not `t`'s
  ancestors, so a `t` deep in a chain is not walked to the top."
  ([tax t among]
   (let [rel   (:genl @tax)
         depth (when-not (:loose? rel) (:depth rel))]
     (into #{} (filter #(reached-from? t % (:rev rel) depth (:scc rel))) among)))
  ([tax t among memo]
   (if (empty? among)
     #{}
     (genls-global-union tax t (filter among) memo))))

(defn- closure-while
  "The nodes a walk from `t` along `dir-key` (`:fwd` up, `:rev` down) through **every**
  active edge of `rel-key` enters, when it enters a node only if `(enter? node)`, `t`
  included, and empty when `enter?` refuses `t`.  Nothing enters the closure cache, and
  the walk costs the nodes it enters and their edges."
  [tax rel-key dir-key t enter?]
  (if-not (enter? t)
    #{}
    (let [adj (get-in @tax [rel-key dir-key])]
      (loop [seen (transient #{t}), stack [t]]
        (if-let [n (peek stack)]
          (let [[seen stack] (reduce (fn [[seen stack :as acc] x]
                                       (if (or (get seen x) (not (enter? x)))
                                         acc
                                         [(conj! seen x) (conj stack x)]))
                                     [seen (pop stack)]
                                     (get adj n))]
            (recur seen stack))
          (persistent! seen))))))

(defn specs-global-while
  "`specs-global` of `t` cut below each type `enter?` refuses (`closure-while`), for a
  caller keeping a property of every subtype that a subtype holding it passes down
  unchanged, which stops where the property is already held: `arity/spread-lengths`."
  [tax t enter?]
  (closure-while tax :genl :rev t enter?))

(defn genls-global-while
  "`genls-global` of `t` cut above each type `enter?` refuses (`closure-while`), for a
  caller keeping a set closed upward that stops where the set already holds a type:
  `arity/conflict-raised`."
  [tax t enter?]
  (closure-while tax :genl :fwd t enter?))

(defn genls-global-meets?
  "Does `genls-global` of `t` hold a term of the set `among`?  A walk up that returns at the
  first such term and stores nothing, so it costs the types it enters before the hit, where
  `genls-global` builds and caches `t`'s whole closure from its ancestors' closures.

  `missed`, when given, is a volatile set the caller keeps for one `among` over one still
  taxonomy: the walk enters no type it holds, and a walk that finds no term adds every
  type it entered, since the closure of each lies in what the walk entered and in
  `missed`.  Asked of many types, the walks then enter each type below no term of `among`
  once."
  ([tax t among] (genls-global-meets? tax t among nil))
  ([tax t among missed]
   (let [adj  (get-in @tax [:genl :fwd])
         gone (if missed @missed #{})]
     (if (contains? gone t)
       false
       (loop [seen (transient #{t}), stack [t]]
         (if-let [n (peek stack)]
           (or (contains? among n)
               (let [fresh (remove #(or (get seen %) (contains? gone %)) (get adj n))]
                 (recur (reduce conj! seen fresh) (into (pop stack) fresh))))
           (do (when missed (vswap! missed into (persistent! seen)))
               false)))))))

(defn specs-global-within
  "`specs-global` of `t` when it holds at most `limit` terms, else nil.
  `genls-global-within`'s reasoning, the other direction."
  [tax t limit]
  (closure-within tax :genl :rev t limit))

(defn genls-within
  "`genls` of `t` from `context` when it holds at most `limit` terms, else nil:
  `genls-global-within` through the edges visible from `context`, which stores nothing
  and stops past `limit`."
  [tax t context limit]
  (if-some [scope (relation-scope tax :genl context)]
    (closure-within-vis tax :genl :fwd t scope limit)
    (closure-within tax :genl :fwd t limit)))

(defn specs-within
  "`specs` of `t` from `context` when it holds at most `limit` terms, else nil.
  `genls-within`'s reasoning, the other direction."
  [tax t context limit]
  (if-some [scope (relation-scope tax :genl context)]
    (closure-within-vis tax :genl :rev t scope limit)
    (closure-within tax :genl :rev t limit)))

(defn specs
  "Subtypes of t, incl t, through the edges visible from `context`.  `specs-global` is
  the unscoped read."
  [tax t context]
  (if-some [scope (relation-scope tax :genl context)]
    (closure-of-vis tax :genl :rev t scope)
    (closure-of tax :genl :rev t)))

(defn- direct-neighbours
  "`t`'s `dir-key` neighbours across **one** edge of `rel-key` (`:genl` or `:genlCx`),
  scoped like the relation's closures (`genls` / `specs`, `context-up`).  Not reflexive:
  the closures include `t` because transitivity is reflexive, and a step is not."
  [tax rel-key dir-key t context]
  (if-some [scope (relation-scope tax rel-key context)]
    (into #{} (visible-neighbours @tax rel-key dir-key scope t))
    (get-in @tax [rel-key dir-key t] #{})))

(defn direct-genls
  "The types `t` is a subtype of by **one** `genl` edge of the closure — its direct
  parents, where `genls` is everything those parents in turn reach.  An edge counts
  whatever installed it: a stated `(genl t super)` or a cover roster naming `t` as a part.

  O(degree), off the `:fwd` adjacency the closure walk is built on, against a closure
  read that is O(1) only because it is memoized.  The closure is what a subsumption check
  needs, and the parents are what a reader is shown."
  [tax t context]
  (direct-neighbours tax :genl :fwd t context))

(defn direct-specs
  "The types that are a subtype of `t` by **one** `genl` edge of the closure — its direct
  children.  `direct-genls`' reasoning, the other direction."
  [tax t context]
  (direct-neighbours tax :genl :rev t context))

(defn direct-genls-global
  "`direct-genls` through **every** active edge — no context scope.  `genls-global`'s
  reasoning: a caller holding a context wants `direct-genls`."
  [tax t]
  (direct-neighbours tax :genl :fwd t nil))

(defn direct-specs-global
  "`direct-specs` through **every** active edge — no context scope."
  [tax t]
  (direct-neighbours tax :genl :rev t nil))

(defn- extremal-types
  "The members of `types` at one end of the subsumption order among themselves: with
  `low?` the minimal ones, which have no other member strictly below them, and without
  `low?` the maximal ones, which have no other member strictly above them.  `above` maps a
  type to its reflexive up-closure.  A set.

  Member `a` is strictly below member `b` when `b` is in `a`'s up-closure and `a` is not
  in `b`'s.  Two members that subsume each other are therefore not strictly ordered, and
  neither drops the other.  Only a member drops a member: a supertype of `a` outside
  `types` is not read as being above it.

  Fewer than two distinct members are returned with no `above` read.  Otherwise the cost
  is one `above` read per member, and for each member the smaller of its up-closure and
  `types` in set lookups."
  [above low? types]
  (let [among (set types)]
    (if (< (count among) 2)
      among
      (let [over    (into {} (map (juxt identity above)) among)
            ;; the members strictly above `t`.  The smaller of the two sets is walked, and
            ;; an element is tested against both: `up` also holds every supertype of `t`
            ;; that is no member
            supers  (fn [t]
                      (let [up (over t)]
                        (into [] (comp (filter #(and (contains? among %) (contains? up %)))
                                       (remove #(or (= t %) (contains? (over %) t))))
                              (if (< (count up) (count among)) up among))))
            dropped (reduce (fn [acc t]
                              (let [ss (supers t)]
                                (cond low?     (into acc ss)
                                      (seq ss) (conj acc t)
                                      :else    acc)))
                            #{} among)]
        (reduce disj among dropped)))))

(defn- up-closure-fn
  "The read `extremal-types` takes as `above`: a node's reflexive up-closure in `rel-key`
  (`:genl` or `:genlCx`) through the edges visible from `context`, or through every
  active edge for a nil `context`."
  [tax rel-key context]
  (if-some [scope (relation-scope tax rel-key context)]
    #(closure-of-vis tax rel-key :fwd % scope)
    #(closure-of tax rel-key :fwd %)))

(defn min-types
  "The **minimal** members of `types`, a collection of types: the members with no other
  member strictly below them, through the edges visible from `context`.  A set.

  `(min-types tax '[dog mammal animal] c)` is `#{dog}` where `dog ⊂ mammal ⊂ animal`.
  Members no `genl` path relates all stay.  Two members that subsume each other both stay.
  A member is compared with the other members only, so a supertype or subtype of it
  outside `types` drops nothing.  A member that is not a node of the hierarchy stays.

  No closure is read for fewer than two distinct members.  Otherwise the cost is one
  memoized up-closure read per member.  `min-types-global` is the unscoped read."
  [tax types context]
  (extremal-types (up-closure-fn tax :genl context) true types))

(defn max-types
  "The **maximal** members of `types`: the members with no other member strictly above
  them, through the edges visible from `context`.  `min-types`' reasoning, the other
  direction, and `#{animal}` in its example.  `max-types-global` is the unscoped read."
  [tax types context]
  (extremal-types (up-closure-fn tax :genl context) false types))

(defn min-types-global
  "`min-types` through **every** active edge — no context scope."
  [tax types]
  (extremal-types (up-closure-fn tax :genl nil) true types))

(defn max-types-global
  "`max-types` through **every** active edge — no context scope."
  [tax types]
  (extremal-types (up-closure-fn tax :genl nil) false types))

(defn- nearest-of
  "The members of `nbrs`, the one-step neighbours of `node`, that no other member stands
  between.  `ends` reduces a collection of types to one end of the order among them:
  `min-types` going up (`up?`), `max-types` going down.  `above` maps a type to its
  reflexive up-closure.

  A neighbour that subsumes and is subsumed by `node` is kept and is not passed to
  `ends`.  Every other neighbour of `node` is strictly on the far side of such a
  neighbour, so `ends` over all of them would keep that neighbour alone.

  Fewer than two neighbours are returned with no read.  Otherwise the cost is `ends`'
  and one `above` read per neighbour going up, or one for `node` going down."
  [above ends up? node nbrs]
  (let [among (set nbrs)]
    (if (< (count among) 2)
      among
      (let [twin? (if up?
                    #(contains? (above %) node)
                    (let [mine (above node)] #(contains? mine %)))
            twins (into #{} (filter twin?) among)]
        (into twins (ends (reduce disj among twins)))))))

(defn- nearest-neighbours
  "`direct-neighbours` in `rel-key` reduced to the nearest ones (`nearest-of`): the
  minimal parents, the maximal children (`extremal-types`, which for `:genl` is
  `min-types` / `max-types`), scoped like the relation's closures."
  [tax rel-key dir-key t context]
  (let [up?   (= :fwd dir-key)
        above (up-closure-fn tax rel-key context)]
    (nearest-of above #(extremal-types above up? %)
                up? t (direct-neighbours tax rel-key dir-key t context))))

(defn min-genls
  "The minimal supertypes of `t` through the edges visible from `context`: `min-types` of
  `t`'s direct parents, the direct parents with no other one strictly below them.  Every other
  strict supertype of `t` is a supertype of one of these.  A stated `(genl dog animal)`
  beside `dog ⊂ mammal ⊂ animal` leaves `animal` out.  An edge counts whatever installed
  it, as for `direct-genls`.  One memoized up-closure read per direct parent."
  [tax t context]
  (nearest-neighbours tax :genl :fwd t context))

(defn max-specs
  "The maximal subtypes of `t` through the edges visible from `context`: `max-types` of
  `t`'s direct children, the direct children with no other one strictly above them.  `min-genls`'
  reasoning, the other direction.  One memoized up-closure read per direct child."
  [tax t context]
  (nearest-neighbours tax :genl :rev t context))

(defn min-genls-global
  "`min-genls` through **every** active edge — no context scope."
  [tax t]
  (nearest-neighbours tax :genl :fwd t nil))

(defn max-specs-global
  "`max-specs` through **every** active edge — no context scope."
  [tax t]
  (nearest-neighbours tax :genl :rev t nil))

(defn specs-of-all
  "The union of `specs` over every node in `nodes`, walked **once**.

  `specs` memoizes per node, which is the right shape for one question asked repeatedly
  and the wrong one for many questions asked together: n nodes are n closures, and where
  the nodes nest — a chain, which is what a batch of `genl` edges written by a load is —
  those closures sum to n²/2 elements though their union holds n.  The memo cannot help,
  since it is keyed on the node a walk started from and every walk starts somewhere else.

  So this seeds one traversal with all of them and guards with one `seen`, making the cost
  the union plus the edges under it rather than the sum of the parts.  Reflexive like
  `specs`, and unscoped like its two-arity: a caller wanting the visibility filter wants
  `specs` per node and the memo that comes with it.

  Deliberately not memoized.  The key would be the seed set, which is a different set
  almost every time and would hold every predicate it ever named."
  [tax nodes]
  (let [adj (:rev (get @tax :genl))]
    (loop [seen (transient (set nodes)), stack (vec nodes)]
      (if-let [n (peek stack)]
        (let [fresh (remove #(get seen %) (get adj n))]
          (recur (reduce conj! seen fresh) (into (pop stack) fresh)))
        (persistent! seen)))))

(defn genl?-global
  "Is sub a (transitive) subtype of super through **any** active edge — no context
  scope.  `genls-global`'s reasoning, as a membership test."
  [tax sub super]
  (reachable-in? tax :genl sub super))

(defn genl?-global-held
  "`genl?-global`, held in the closure cache under the `genl` generation, for a caller
  that asks one pair once per fact of a sweep: a pair the depth potential does not reject
  walks `sub`'s ancestors on every ask (`checks/mintable-type?`)."
  [tax sub super]
  (let [t   @tax
        rel (:genl t)
        lru (:closure-lru t)
        k   [:genl (:gen rel) :reaches sub super]
        hit (caches/lru-get lru k)]
    (if (some? hit)
      hit
      (caches/lru-put! lru k (boolean (reachable? sub super (:fwd rel)
                                                  (when-not (:loose? rel) (:depth rel))
                                                  (:scc rel)))))))

(defn genl?
  "Is sub a (transitive) subtype of super through the edges visible from `context`?
  `genl?-global` is the unscoped read."
  [tax sub super context]
  (if-some [scope (relation-scope tax :genl context)]
    (let [t   @tax
          rel (:genl t)]
      (reachable-filtered? sub super t :genl scope
                           (when-not (:loose? rel) (:depth rel))
                           (:scc rel)))
    (reachable-in? tax :genl sub super)))

;; ---- what a reachability rests on ---------------------------------------
;;
;; `genls` / `genl?` answer *whether* one type reaches another; a caller that is
;; going to **depend** on that reachability needs to name the sentexes it rests on,
;; so the dependency can be withdrawn when they are.  A forward firing matched by
;; subsumption is exactly such a caller (docs/contexts.md).
;;
;; The witness is **one path, one supporter per edge** — a justification is a
;; conjunction of supports, not a proof that no other support exists.  A second route
;; (another path, or the same edge asserted from a second context) therefore does not
;; appear; when the named witness goes, what rested on it goes with it and is
;; re-derived from the surviving route.  That is the bargain the qualitative support
;; already makes for the same reason (docs/qcn.md): every route re-derives what the
;; first one reached, so carrying them all would be one justification per path in a
;; hierarchy where paths multiply.
;;
;; The choice is keyed on **content** — the walk expands neighbours in name order and
;; the supporter is picked by asserting context — never on handle id, which is
;; allocated in assertion order and would smuggle arrival order into belief.
;;
;; Each step also reports the **context** its supporter was asserted from, because a
;; caller that depends on a reachability inherits its visibility: a conclusion resting
;; on an edge stated somewhere belongs no higher than a context that can see where it
;; was stated.  So the witness prefers, per edge, the **most general** supporter
;; available — the one every other supporter of that edge sees — since a needlessly
;; specific choice would drag its dependant down with it.  Across *paths* the witness is
;; still the shortest one; a longer route through more general contexts might carry
;; further, and is deliberately not searched for.

(defn- more-general-supporter
  "The member of `cands` (`[handle ctx]` pairs) whose context every other candidate's
  context sees — the one that constrains a dependant least — or nil when no member is
  comparable to all of them.  A nil context is recorded by a writer that had none and
  is seen from everywhere, so it wins outright."
  [tax cands]
  (or (first (filter (fn [[_ c]] (nil? c)) cands))
      (first (filter (fn [[_ c]]
                       (every? (fn [[_ c2]] (contains? (closure-of tax :genlCx :fwd c2) c))
                               cands))
                     cands))))

(defn- visible-edge-supporters
  "The believed supporters of active edge `e` a reader seeing `vis` can use, as a vector
  of `[handle ctx]` — the candidate set `edge-supporter` chooses the most general of, and
  the strength-aware pickers below read for class.  A supporter is believed iff its own
  context is in `:edge-ctxs` (an edge is stored once per context, so the context
  identifies it); nil `vis` is the unscoped read where every asserting context is visible.
  Held for a reading pass (`pass-held`)."
  [t rel-key [a b :as e] scope]
  (pass-held
   [::supporters rel-key e scope]
   #(into [] (filter (let [live (get-in t [rel-key :edge-ctxs e] #{})]
                       (fn [[h c]]
                         (if (map? scope)
                           (scope-admits-supporter? scope h c)
                           (and (contains? live c)
                                (or (nil? scope) (nil? c) (scope c)))))))
          (supporters-of t [rel-key a b]))))

(defn genl-edge-supporters
  "The handles of the believed supporters of `genl` edge `[sub super]` a reader at
  `context` can use: each `(genl sub super)` sentex, and each `covering`, `separating` or
  `partition` roster that installs the edge, that `genl?` from `context` would walk the
  edge through.  Empty when the edge is not active.  Belief is read as `:edge-ctxs` records it, so a caller wanting the
  JTMS's word filters again."
  [tax sub super context]
  (into #{} (map first)
        (visible-edge-supporters @tax :genl [sub super] (relation-scope tax :genl context))))

(defn- most-general-of
  "The most general of `cands` (a non-empty vector of `[handle ctx]`), since its context is
  inherited by whatever depends on the edge; asserting-context name breaks a tie between
  incomparable ones, so the choice is a function of the contexts rather than of the order
  the supporters arrived in.  The key is that name and **nothing else** — never a handle,
  which is allocated in assertion order and would decide where a dependant's conclusion
  lands by which supporter was loaded first (`term-key`, and docs/nmtms.md).

  That name orders the candidates **completely**, and the reason is sentex identity: a
  sentence and a context are what a handle is allocated for, so one edge stated twice from
  one context is one sentex and two supporters of an edge never share a context
  (`subsumption_support_test/an-edge-has-one-supporter-per-context`).  Nothing is left for
  the stable sort to decide, which is what the choice needs — the handle named here enters
  a dependant's justification and reads back out of `why`'s `:because`, so a tie broken by
  arrival would be observable there even where the placement is identical
  (`subsumption_support_test/the-witness-does-not-depend-on-assertion-order`).

  A **single** candidate takes neither the ordering nor the comparison: it is trivially the
  most general, and that is the overwhelming common case.  The short-circuit is not a
  micro-optimization — `more-general-supporter` reads the genlCx closure, whose memo a bulk
  load retires on every context edge it asserts, so paying it per edge per subsuming firing
  cost a fifth of the schema load.

  Both pickers below narrow to a candidate set and then ask this: `edge-supporter` over
  every visible supporter, `strongest-edge-supporter` over the ones at the edge's own
  strength class.  One definition, so the two cannot choose differently."
  [tax cands]
  (if (nil? (next cands))
    (nth cands 0)
    ;; keyed through the guarded printer because a context may be a NAT
    (let [ordered (nm/sort-by-content-key (fn [[_ c]] (nm/print-key c)) compare cands)]
      (or (more-general-supporter tax ordered) (nth ordered 0)))))

(defn- edge-supporter
  "A believed supporter of active edge `e` that a reader seeing `vis` can use, as
  `[handle ctx]`, or nil.  `:edge-ctxs` is the believed supporters' context set, so a
  supporter is believed iff its own context is in it — an edge is stored once per
  context, so that identifies it.

  The **most general** visible supporter (`most-general-of`), since its context is
  inherited by whatever depends on the edge."
  [tax t rel-key e vis]
  (let [cands (visible-edge-supporters t rel-key e vis)]
    (when (seq cands) (most-general-of tax cands))))

(defn- top-supporter-class
  "The **strongest** class among a non-empty `cands` (`strength/max`), `:default` when none
  is monotonic.  `supporter-class` is `handle → class` — a live JTMS `defeat-class` read —
  and a supporter it cannot classify (OUT, or mid-settle) counts as `:default`, the
  weakest, so a walk never over-claims `:monotonic` for an edge it cannot confirm holds
  that strongly.  The two readers below take that reading: the one that reports an
  edge's class, and the one that picks a witness holding an edge's."
  [cands supporter-class]
  (reduce (fn [c [h _]] (strength/max c (or (supporter-class h) :default))) :default cands))

(defn- edge-class
  "The defeat class active edge `e` holds at, as `vis` sees it, or nil when no supporter is
  visible at all."
  [t rel-key e vis supporter-class]
  (let [cands (visible-edge-supporters t rel-key e vis)]
    (when (seq cands) (top-supporter-class cands supporter-class))))

(defn- strongest-edge-supporter
  "A `[handle ctx]` witness for edge `e` that holds at the edge's own strength: the most
  general supporter *among those at the maximum class*.  So the justification records a
  supporter as strong as the edge is, and where two supporters tie on strength the
  placement-relevant (most general) one is named — `edge-supporter`'s own choice, applied
  after the strength filter.  nil when the edge has no visible supporter."
  [tax t rel-key e vis supporter-class]
  (let [cands (visible-edge-supporters t rel-key e vis)]
    (when (seq cands)
      (let [top (top-supporter-class cands supporter-class)]
        (most-general-of tax (filterv (fn [[h _]] (= top (or (supporter-class h) :default)))
                                      cands))))))

(def ^:private prune-after
  "Expansions `bfs-witness-path` makes before it reads the types between the source and
  the target and keeps only the neighbours among them: a walk shorter than this reads no
  closure."
  64)

(defn- bfs-witness-path
  "Shortest path `sub →* super` over neighbours `nbrs`, admitting an edge `[p x]` only
  when `admit?` allows it (asked of an unvisited neighbour only) and mapping each
  traversed edge to a `[handle ctx]` supporter via `witness`.  Returns the vector of witnesses (one per edge, `super`-end first) or nil —
  unreachable, or an admitted edge whose `witness` came back nil.  Neighbours are expanded
  in the order `nbrs` imposes (name order), so the path is a function of the hierarchy
  rather than of the order it was built in, and the first path to `super` is a shortest
  one.

  Past `prune-after` expansions a node is expanded, and a neighbour kept, only when
  `@reaches?` holds of it, a test that holds of every node above `sub` with a path to
  `super`.  A node with none has no neighbour with one either, so no node on a path to `super` is reached
  through it, and the dropped nodes leave the order the others are reached in, and the
  path, unchanged."
  [sub super nbrs admit? witness reaches?]
  (loop [q (conj clojure.lang.PersistentQueue/EMPTY sub), parent {sub nil}, i 0]
    (when-let [n (peek q)]
      (cond
        (= n super)
        (loop [x n, acc []]
          (if (= x sub)
            acc
            (let [p (get parent x)]
              (when-let [s (witness [p x])]
                (recur p (conj acc s))))))

        (and (>= i prune-after) (not (@reaches? n)))
        (recur (pop q) parent i)

        :else
        (let [fresh (filter #(admit? [n %])
                            (cond->> (remove #(contains? parent %) (nbrs n))
                              (>= i prune-after) (filter @reaches?)))]
          (recur (into (pop q) fresh)
                 (into parent (map (fn [x] [x n])) fresh)
                 (inc i)))))))

(defn- direct-witness
  "The witness `bfs-witness-path` names from `sub` to `super` over the adjacency `adj` when
  `sub` has an edge straight to `super` that `admit?` allows, or nil for the walk to
  answer.  The walk pops `sub`, queues `super` as the end of that edge, and pops it as the
  end of a one-edge path, so the path is that edge and its witness is `(witness [sub
  super])`; a nil witness is left to the walk."
  [adj sub super admit? witness]
  (when (and (some #(= super %) (adj sub)) (admit? [sub super]))
    (when-let [w (witness [sub super])] [w])))

(defn- reach-support*
  "`reach-support`'s walk.  The six- and seven-argument arities call it directly rather
  than one another through the var, so a walk is one call to either of them."
  [tax rel-key sub super context supporter-class thresholds]
  (if (= sub super)
    []
    (let [t   @tax
          rel (get t rel-key)
          scope (relation-scope tax rel-key context)
          ;; nil `vis` is the unscoped walk — every asserting context is visible, so
          ;; the plain adjacency *is* the visible one, exactly as in `genls`
          adj (if (nil? scope) #(get (:fwd rel) %) #(visible-neighbours t rel-key :fwd scope %))
          ;; `nm/print-key` keeps a node that is not a symbol (a NAT) sortable, and
          ;; prints it with the bounds released — a bare `str` would let an ambient
          ;; `*print-length*` elide two nested nodes to one prefix and expand the
          ;; adjacency in the set's own order, which is what the witness path (and so a
          ;; justification's antecedents) would then rest on.  Built once per adjacency,
          ;; and a node with 0/1 neighbour — common in a sparse relation — sorts nothing
          nbrs (fn [n] (pass-held [::sorted rel-key scope n]
                                  #(nm/sort-by-content-key nm/print-key compare (adj n))))
          ;; the walk enters only types above `sub` under any scope, since a scoped
          ;; adjacency is a subset of the global one, and every type on a path from one
          ;; of them to `super` is above `sub` too: a walk down from `super` through
          ;; `sub`'s global ancestors enters exactly those with a path to `super`, and
          ;; it is held by this call alone
          reaches? (delay (let [up      (closure-of tax rel-key :fwd sub)
                                between (closure-while tax rel-key :rev super #(contains? up %))]
                            #(contains? between %)))
          direct #(direct-witness adj sub super %1 %2)]
      ;; a walk from a source with no edge it sees finds no path
      (cond
        (empty? (adj sub))     nil
        (nil? supporter-class)
        (let [witness #(edge-supporter tax t rel-key % scope)]
          (or (direct (fn [_] true) witness)
              (bfs-witness-path sub super nbrs (fn [_] true) witness reaches?)))
        :else
        ;; each edge's class read once for both thresholds
        (let [ranks (java.util.HashMap.)
              rank  (fn [e]
                      (or (.get ranks e)
                          (let [r (strength/rank-of (edge-class t rel-key e scope supporter-class))]
                            (.put ranks e r)
                            r)))
              admit (fn [threshold] (fn [e] (>= (long (rank e)) (long (strength/rank-of threshold)))))
              witness #(strongest-edge-supporter tax t rel-key % scope supporter-class)]
          ;; the first threshold's walk is the one an edge straight to `super` ends
          (or (direct (admit :monotonic) witness)
              (some (fn [threshold]
                      (bfs-witness-path sub super nbrs (admit threshold) witness reaches?))
                    thresholds)))))))

(defn reach-support
  "A witness for `sub →* super` in relation `rel-key`, as the `[handle ctx]` of one
  supporter per edge along a single path — or nil when `context` sees no such path.
  Empty for `sub` = `super`, which rests on nothing.  A nil `context` walks
  unscoped, which is what a caller wanting the witness *before* it knows its vantage
  asks for.

  Walks the same visible adjacency the scoped closure reads do, so it finds a witness for
  exactly the pairs `genl?` answers true from that context, and the two can never disagree
  about what a context can reach.  Neighbours are expanded in name order, so the answer is
  a function of the hierarchy rather than of the order it was built in.

  **Without `supporter-class`** it is breadth-first — the witness is a *shortest* path (the
  fewest supports the reachability can be made to depend on), and each edge names its most
  general supporter (`edge-supporter`), the choice placement wants.  This is the read the
  `genlCx` visibility walk and every unstrengthened caller take.

  **With `supporter-class`** (a `handle → defeat-class` read) it is a *widest-bottleneck*
  path: the route whose floor — the `min` defeat class along it — is highest, tie-broken by
  depth then by the same name order.  Each edge names its **strongest** supporter
  (`strongest-edge-supporter`), so the conclusion a firing builds over these handles is
  capped at the floor and no lower.  Since there are exactly two classes
  (`strength.clj`), the widest floor is found by trying each class as a threshold, highest
  first, and taking the first shortest path made only of edges that clear it — a threshold
  scan that stays correct for any fixed number of classes and is two passes for two.
  `thresholds` names the classes tried, highest first: `[:monotonic]` asks for a path
  every edge of which holds at `:monotonic` and walks no second pass when there is none
  (`monotonic-route-witness`)."
  ([tax rel-key sub super context] (reach-support tax rel-key sub super context nil))
  ([tax rel-key sub super context supporter-class]
   (reach-support* tax rel-key sub super context supporter-class [:monotonic :default]))
  ([tax rel-key sub super context supporter-class thresholds]
   (reach-support* tax rel-key sub super context supporter-class thresholds)))

(defn context-specificity
  "How specific context `c` is, as the size of its `genlCx` ancestor set; 0 for a supporter
  with no recorded context, which is seen from everywhere.  A context strictly below
  another has the larger ancestor set, so the number orders every comparable pair the way
  `sees?` does, and gives the incomparable ones one total order to be tie-broken in.
  A function of the topology alone, so no arrival order reaches it."
  [tax c]
  (if (nil? c) 0 (count (closure-of tax :genlCx :fwd c))))

;; ---- every route a reader can hold a dependant through --------------------
;;
;; A witness names one route, and the route decides where a dependant is placed.  Two
;; routes stated in contexts neither of which sees the other place it in two different
;; readers, and neither placement is above the other: the route through CxA places a
;; conclusion CxA reads and CxB does not, the route through CxB the reverse.  A search
;; that named one of them would leave the other reader without the conclusion except in
;; the orders where a firing over its own route was placed before the named route
;; arrived, since such a firing stays stored.
;;
;; The searches below return **every route no other route covers**.  Route R1 covers
;; R2 when each reader that sees every asserting context of R2 also sees every one of
;; R1's, and the test reads that as each of R1's contexts being seen from one of R2's
;; (`floor-covers?`).  A caller places a dependant once per returned route, so each
;; reader that reaches over its own edges reads the placement its own route decides.
;; Where every edge is stated in contexts one reader sees, one route covers the rest
;; and the search returns one route.

(defn- seen-from?
  "Is context `a` seen from context `b` — `b` itself or one of its `genlCx` ancestors?
  A nil `a` was recorded by a writer with no context and is seen from everywhere."
  [tax a b]
  (or (nil? a)
      (= a b)
      (and (some? b) (contains? (closure-of tax :genlCx :fwd b) a))))

(defn context-floor
  "The most specific members of `ctxs`, as a set: a nil member and every member another
  member sees are dropped, since a reader seeing the rest sees those too.  Two members
  that see each other count once, and the member kept is the first in printed order."
  [tax ctxs]
  (let [cs (into [] (comp (remove nil?) (distinct)) ctxs)]
    (if (nil? (next cs))
      (set cs)
      (reduce (fn [acc c]
                (if (some #(seen-from? tax c %) acc)
                  acc
                  (conj (into #{} (remove #(seen-from? tax % c)) acc) c)))
              #{}
              (nm/sort-by-content-key nm/print-key compare cs)))))

(defn floor-covers?
  "Does a reader that sees every context of floor `f2` see every context of floor `f1`?
  Answered by each member of `f1` being seen from some member of `f2`, which is what the
  `genlCx` ancestor sets decide without enumerating readers."
  [tax f1 f2]
  (or (= f1 f2)
      (every? (fn [a] (some #(seen-from? tax a %) f2)) f1)))

(defn- covers?
  "Does label `[rank1 floor1 hid1]` cover `[rank2 floor2 hid2]`: at least as strong, seen
  from every reader that sees the other, and resting on no handle an except can hide
  (`hid`, a set or nil) that the other does not rest on too?  A nil rank takes no part in
  the comparison."
  [tax [r1 f1 h1] [r2 f2 h2]]
  (and (or (nil? r1) (nil? r2) (>= r1 r2))
       (or (empty? h1) (every? #(contains? h2 %) h1))
       (floor-covers? tax f1 f2)))

(defn uncovered
  "The members of `alts` whose label no other member's label covers, in their given
  order.  `label` maps a member to `[rank floor]` (rank nil where strength takes no
  part), or to `[rank floor hid]`, `hid` the set of its handles an except can hide.  Of
  two members that cover each other, the earlier is kept, so a caller that hands `alts`
  over in content order gets a result that is a function of the content."
  [tax label alts]
  (if (nil? (next alts))
    (vec alts)
    (let [ls (mapv label alts)
          n  (count ls)]
      (into []
            (keep-indexed
             (fn [i a]
               (let [li (nth ls i)]
                 (when-not (some (fn [j]
                                   (let [lj (nth ls j)]
                                     (and (not= i j)
                                          (covers? tax lj li)
                                          (or (< j i) (not (covers? tax li lj))))))
                                 (range n))
                   a))))
            alts))))

(defn- floor-specificity
  "The specificity of the most specific member of floor `f`, 0 for an empty floor."
  [tax f]
  (reduce (fn [m c] (max m (context-specificity tax c))) 0 f))

(defn- trail-order
  "The content order of two partial routes the queue key of `uncovered-routes` ties, each
  a trail of `[node [handle ctx] key]` steps from the start: by each step's printed node,
  then its supporter's key, or its printed context where it has none.  Two trails equal
  here name the same route."
  [a b]
  (let [n (min (count a) (count b))]
    (loop [i 0]
      (if (< i n)
        (let [[na wa ka] (nth a i)
              [nb wb kb] (nth b i)
              c (compare [(nm/print-key na) (or ka (nm/print-key (nth wa 1)))]
                         [(nm/print-key nb) (or kb (nm/print-key (nth wb 1)))])]
          (if (zero? c) (recur (inc i)) c))
        (compare (count a) (count b))))))

(defn uncovered-routes
  "Every route `start →* goal` whose label no other route's covers (`covers?`), as a
  vector of routes, each the `[handle ctx]` supporters along it with the `goal` end
  first.  `[[]]` when `start` is `goal`, which rests on nothing; `[]` when no route
  exists.

  `step` maps a node to its outgoing steps `[next [handle ctx] rank hid?]` in content
  order, one per supporter a route may name for that edge, with an optional fifth
  element: the supporter's content key, which orders the supporters of one step where
  their contexts do not (the printed context otherwise).  `rank` is the supporter's
  strength rank, or nil where strength takes no part, and `hid?` is true when an except
  can hide the supporter.  A route's label is its weakest rank, the floor of its
  supporters' contexts (`context-floor`) and the set of its hidable supporters.
  Extending a route never makes its label cover more, so the walk drops a partial route
  whose label a route already held at the same node covers, or one a route already found
  at `goal` covers.
  A node therefore holds one partial route per uncovered label, and where every edge is
  stated in contexts one reader sees, that is one route per node.

  The queue orders by rank, then by the specificity of the floor's most specific member,
  then by length, then by the printed terms of the step and the printed floor, and two
  routes equal on all of those by their printed terms and supporter keys from `start`
  on (`trail-order`), so the order is total.  Of two routes with equal labels the walk
  keeps the one it pops first, so the kept route is a function of the content, and the
  routes come back in that order."
  [tax start goal step]
  (if (= start goal)
    [[]]
    (let [pq       (java.util.PriorityQueue. 16 ^java.util.Comparator
                                             (fn [a b] (let [c (compare (nth a 0) (nth b 0))]
                                                         (if (zero? c) (trail-order (nth a 5) (nth b 5)) c))))
          ;; a walk meets few distinct labels — one, where every edge is stated in
          ;; contexts one reader sees — so a label carries its own queue key, is built
          ;; once, and is passed along unchanged by every step that does not move the
          ;; floor.  `one?` holds while every label built is that first one, and a route
          ;; found then covers every entry still queued.
          labels   (java.util.HashMap.)
          one?     (volatile! true)
          label    (fn [rank floor hid]
                     (let [k [rank floor hid]]
                       (or (.get labels k)
                           (let [l [rank floor hid (- (or rank 0)) (floor-specificity tax floor)
                                    (vec (sort (map nm/print-key floor)))]]
                             (when (pos? (.size labels)) (vreset! one? false))
                             (.put labels k l)
                             l))))
          push!    (fn [l node from path len trail]
                     (.add pq [[(nth l 3) (nth l 4) len (nm/print-key node)
                                (nm/print-key from) (nth l 5)]
                               node l path len trail]))
          lcovers? (fn [a b] (covers? tax a b))
          covered? (fn [ls l] (some #(lcovers? % l) ls))
          keep-in  (fn [ls l] (conj (filterv #(not (lcovers? l %)) ls) l))
          routes   (fn [found] (mapv (fn [[_ path]] (vec (rseq path))) found))]
      (push! (label nil #{} nil) start "" [] 0 [])
      (loop [held {}, found [], flabels []]
        ;; one label in the whole walk and a route found under it: every entry still
        ;; queued carries that label, which the route covers, so the walk is over
        (if (and (seq found) @one?)
          (routes found)
          (if-let [[_ node l path len trail] (.poll pq)]
            (let [rank (nth l 0), floor (nth l 1), hid (nth l 2)]
              (cond
                (or (covered? flabels l) (covered? (get held node) l))
                (recur held found flabels)

                (= node goal)
                (let [kept (filterv #(not (lcovers? l (first %))) found)]
                  (recur held (conj kept [l path]) (conj (mapv first kept) l)))

                :else
                (let [held (update held node (fnil keep-in []) l)
                      len2 (inc len)]
                  (doseq [[n2 w r hid? k] (step node)
                          :let  [c  (nth w 1)
                                 h? (and hid? (not (contains? hid (nth w 0))))
                                 l2 (if (and (or (nil? r) (and rank (<= rank r)))
                                             (or (nil? c) (contains? floor c))
                                             (not h?))
                                      l
                                      (label (cond (nil? r) rank (nil? rank) r :else (min rank r))
                                             (if (or (nil? c) (contains? floor c))
                                               floor
                                               (context-floor tax (conj floor c)))
                                             (if h? (conj (or hid #{}) (nth w 0)) hid)))]
                          :when (not (or (covered? (get held n2) l2)
                                         (covered? flabels l2)))]
                    (push! l2 n2 node (conj path w) len2 (conj trail [n2 w k])))
                  (recur held found flabels))))
            (routes found)))))))

(defn- edge-steps
  "`step` for `uncovered-routes` over relation `rel-key` as `context` sees it: from a
  node, each visible neighbour once per visible supporter of the edge that no other
  visible supporter covers.  With `supporter-class` each supporter carries its strength
  rank, so a stronger supporter in a more specific context is a step of its own.

  Built eagerly into a vector, and an edge with one visible supporter — nearly every
  edge — takes neither the ordering nor the covering comparison: the walk reads one step
  per edge on the hot path, and a lazy seq per neighbour is what it costs to produce
  them one at a time.  With `hidable` (`handle → boolean`) each supporter an except can
  hide is marked so (`uncovered-routes`' `hid?`).  A node's sorted neighbours are held for
  a reading pass under `reach-support`'s key (`pass-held`)."
  [tax rel-key context supporter-class hidable]
  (let [t     @tax
        rel   (get t rel-key)
        scope (relation-scope tax rel-key context)
        adj   (if (nil? scope) #(get (:fwd rel) %) #(visible-neighbours t rel-key :fwd scope %))
        rank  (when supporter-class
                #(strength/rank-of (or (supporter-class %) :default)))
        hid?  (if hidable #(boolean (hidable %)) (constantly false))
        label (fn [[h c]] [(when rank (rank h)) (if (nil? c) #{} #{c}) (when (hid? h) #{h})])
        step  (fn [acc n2 w] (conj! acc [n2 w (when rank (rank (nth w 0))) (hid? (nth w 0))]))]
    (fn [node]
      (persistent!
       (reduce (fn [acc n2]
                 (let [cands (visible-edge-supporters t rel-key [node n2] scope)]
                   (cond
                     (empty? cands)      acc
                     (nil? (next cands)) (step acc n2 (nth cands 0))
                     :else               (reduce #(step %1 n2 %2)
                                                 acc
                                                 (uncovered tax label
                                                            (nm/sort-by-content-key
                                                             (fn [[_ c]] (nm/print-key c))
                                                             compare cands))))))
               (transient [])
               (pass-held [::sorted rel-key scope node]
                          #(nm/sort-by-content-key nm/print-key compare (adj node))))))))

(defn- every-uncovered-route
  "`uncovered-routes` from `start` to `goal` over `step`, answered without the walk when
  `start`'s one step ends at `goal`: every route begins with a step from `start`, and the
  walk returns the route it finds at `goal` through that step alone."
  [tax start goal step]
  (let [s (when (not= start goal) (step start))]
    (if (and (= 1 (count s)) (= goal (nth (first s) 0)))
      [[(nth (first s) 1)]]
      (uncovered-routes tax start goal step))))

(defn general-reach-supports
  "Every witness for `sub →* super` in `rel-key` that `context` sees and no other witness
  covers (`uncovered-routes`), each the `[handle ctx]` of one supporter per edge along a
  single path.  `[[]]` for `sub` = `super`, which rests on nothing; `[]` when `context`
  sees no path.

  `reach-support` names a *shortest* path, and a shorter route through a specific context
  drags a conclusion resting on it down there while a longer route through general
  contexts would have left it above.  Here a route is judged by the contexts it was
  stated in, so the route through general contexts covers the short one and is the one
  returned.  Routes stated in contexts neither of which sees the other are each returned,
  since each places a dependant in a reader the other does not reach.

  Ties are settled on content: the specificity of the route's most specific context,
  then its length, then the printed terms.  Nothing keys on a handle, so two KBs holding
  the same edges name the same witnesses whatever order they were built in
  (docs/nmtms.md)."
  [tax rel-key sub super context]
  (every-uncovered-route tax sub super (edge-steps tax rel-key context nil nil)))

(defn reach-supports
  "Every witness for `sub →* super` in `rel-key` that `context` sees and no other witness
  covers, weighing the defeat class of each supporter (`supporter-class`) beside its
  context: a route covers another only if its floor class is at least as strong and it
  is seen wherever the other is.  The routes a placement that has to descend below the
  firing's other ingredients chooses among (`chain/placement-ingredients`).  With
  `hidable` (`handle → boolean`), a route resting on a supporter an except can hide
  covers only the routes resting on that supporter too."
  ([tax rel-key sub super context supporter-class]
   (reach-supports tax rel-key sub super context supporter-class nil))
  ([tax rel-key sub super context supporter-class hidable]
   (every-uncovered-route tax sub super (edge-steps tax rel-key context supporter-class hidable))))

(defn reach-strength
  "The defeat class of the **strongest** route `sub →* super` in `rel-key` that `context`
  sees — `:monotonic` / `:default`, or nil when unreachable.  `:monotonic` for `sub` =
  `super`, which rests on nothing and so holds as strongly as anything can.
  `supporter-class` is the same `handle → class` read `reach-support` takes.

  Derived from `reach-support`'s widest-bottleneck path so the number and the witness can
  never disagree: the floor of the path it names *is* the strength, since each edge on it
  contributes its strongest supporter (docs/taxonomy.md, \"Strength of a subsumption
  path\")."
  [tax rel-key sub super context supporter-class]
  (if (= sub super)
    :monotonic
    (when-let [path (reach-support tax rel-key sub super context supporter-class)]
      (reduce (fn [floor [h _]] (strength/min floor (or (supporter-class h) :default)))
              :monotonic path))))

(def ^:dynamic *exposure-instance-budget*
  "How many candidate instances one bounded merge sweep will enumerate:
  `vaelii.impl.special/equate-under-context-edge`, which a `genlCx` edge arriving over
  stored facts runs, and the sweep a revived `genl` edge under a merge mark runs
  (`special/revived-declaration-sweeps`).  A small edge can make a large, already-stored
  extent jointly visible, and the walk that decides whether any of it merges must not
  grow with the extent once it is past the cap.  A sweep cut short is never silent: each
  caller files its own notice naming its trigger.

  **Where a cut can see arrival order, and why it is left there.**  Below the trigger
  level — the down-closure, the context ancestor set, the posting list of one type or
  predicate — nothing is sorted: the enumerations are lazy so a budgeted consumer
  realizes only its prefix, and sorting to choose that prefix forces the whole extent,
  which is the cost the cap was added to refuse.

  That is measured rather than assumed.  Sorting the context ancestor set took
  `retract-context-cycle-scaling` from 0.08 to 0.28 ms/op at 2048 contexts — a 3.4x
  growth against a 2x bound — because a context cycle makes the ancestor set the whole graph.
  The check exists to say a retraction is flat in the graph it is not about, and a sort
  is exactly what stops it being.

  **The residual is stated on each sweep.**  The cap selects a handle-ordered prefix, and
  a merge a sweep fails to reach is not derived by a later settle, so past the cap the
  order-dependence is in whether a merge is derived at all.  It is bounded and reported
  (a `:context-edge-exposure-truncated` or `:genl-edge-revival-truncated` violation per
  cut), and below the cap it is exact.

  **Why 8192 and not 4096.**  The cap bounds a sweep against a *large* extent, and 4096
  sat within 3% of what the shipped ontology plus a 200-fact generated corpus
  (`generate_test/a-generated-kb-derives-cleanly`) enumerated.  A cap a mid-size KB
  reaches by existing truncates a normal sweep rather than refusing an unbounded one.
  8192 restores the headroom."
  8192)

;; ---- genlCx (contexts) ---------------------------------------------------

(defn context-up-global
  "Contexts `c` inherits from through the active genlCx cache, with **no** `except`
  holes — the unscoped read, and named for it the way `genls-global` is.

  For `genlCx` the scope *is* the except filter, so this and `context-up` agree on every
  KB where nothing excepts a genlCx supporter — which is why the two carry different
  names rather than one name and an option.  Exception evaluation reads this
  non-recursive base relation to decide which exception declarations a reader can see,
  and that is what it is for: the filter cannot be asked to answer the question it is
  itself derived from.  Every other caller wants `context-up`."
  [tax c]
  (closure-of tax :genlCx :fwd c))

(defn context-down-global
  "Contexts that inherit from `c`, incl `c`, through the active genlCx cache, with **no**
  `except` holes: `context-down`'s unscoped read, for `context-up-global`'s callers."
  [tax c]
  (closure-of tax :genlCx :rev c))

(defn context-up
  "Contexts c inherits from, incl c, after context-visible genlCx exceptions."
  [tax c]
  (if-some [scope (relation-scope tax :genlCx c)]
    (closure-of-vis tax :genlCx :fwd c scope)
    (context-up-global tax c)))

(defn context-parents-global
  "The contexts `c` reaches over **one** active `genlCx` edge, with no `except` holes."
  [tax c]
  (get-in @tax [:genlCx :fwd c] #{}))

(defn context-children-global
  "The contexts that reach `c` over **one** active `genlCx` edge, with no `except` holes:
  `context-parents-global`'s reverse, an adjacency read with no closure walk."
  [tax c]
  (get-in @tax [:genlCx :rev c] #{}))

(defn min-context-parents
  "The minimal contexts `c` inherits from: the contexts `c` reaches over **one** `genlCx`
  edge with no other such context strictly below them.  `min-genls`' reduction over
  `genlCx`, read as `context-up` reads: `c` is the reader, so both the edges out of `c`
  and the ancestor sets the parents are compared by are the ones effective for `c` after
  the `except` holes `c` reads (`relation-scope`).  Every other context of `context-up`
  but `c` is therefore reached through one of these.  A `(genlCx CxLeaf CxTop)` held
  beside `CxLeaf → CxMid → CxTop` leaves `CxTop` out, and an `except` that hides
  `CxLeaf → CxMid` from `CxLeaf` makes `CxTop` the answer.  Not reflexive.  One memoized
  up-closure read per direct parent."
  [tax c]
  (nearest-neighbours tax :genlCx :fwd c c))

(defn max-context-children
  "The maximal contexts that inherit from `c`: the contexts that reach `c` over **one**
  `genlCx` edge with no other such context strictly above them.  `max-specs`' reduction
  over `genlCx`, and `min-context-parents`' reverse.

  Reverse visibility has no single reader (`context-down`).  So while some `except`
  targets a `genlCx` supporter (`relation-filter-active?`), each direct child is judged
  by its own forward answer, as `context-down` judges a candidate: a child is a member
  when `c` is one of its `min-context-parents`.  Every member is then in `context-down`
  of `c`, and a context is drawn below `c` exactly when `c` is drawn above the context.
  With no except reaching `genlCx` the reduction over the raw adjacency is the answer,
  and the two readings agree on every acyclic edge set.

  One memoized up-closure read for `c` on the raw path.  On the filtered path one
  `min-context-parents` read per direct child, which is not memoized here."
  [tax c]
  (if-not (relation-filter-active? @tax :genlCx)
    (nearest-neighbours tax :genlCx :rev c nil)
    (into #{}
          (filter #(contains? (min-context-parents tax %) c))
          (context-children-global tax c))))

(defn- up-besides
  "The contexts `c` inherits from, incl `c`, over the `genlCx` edges effective in `scope`
  (`relation-scope`; the active adjacency when nil) but the edge `[sub super]` and every
  edge `usable?` refuses.  A walk that comes back to `c` has found a cycle, whose members
  already see what the edge shows, and answers `#{c}`."
  [t scope c [sub super] usable?]
  (let [up1 (fn [n] (filter #(and (not (and (= n sub) (= % super))) (usable? n %))
                            (if (some? scope)
                              (visible-neighbours t :genlCx :fwd scope n)
                              (get-in t [:genlCx :fwd n] #{}))))]
    (loop [acc #{c}, todo (into [] (up1 c))]
      (if-let [n (peek todo)]
        (cond (= n c)           #{c}
              (contains? acc n) (recur acc (pop todo))
              :else             (recur (conj acc n) (into (pop todo) (up1 n))))
        acc))))

(defn- reader-classes
  "The reader classes under `sub` (the contexts in `under`, `sub`'s global descendant set),
  as a sorted map from each class's key to its representative reader.  A reader's key is
  the set of contexts of `except-ctxs` in its global ancestor set; readers with one key read
  every `genlCx` supporter alike, since the excepts in force are read off the raw ancestor
  set (`relation-scope`).  `sub` represents the readers whose key is its own; each other
  class is represented by its least member in content order."
  [tax sub under except-ctxs]
  (let [base   (into (sorted-set) (filter (set (context-up-global tax sub))) except-ctxs)
        others (remove base except-ctxs)
        member (reduce (fn [m c]
                         (let [dn (context-down-global tax c)
                               in (if (< (count dn) (count under))
                                    (filter #(contains? under %) dn)
                                    (filter #(contains? dn %) under))]
                           (reduce #(update %1 %2 (fnil conj base) c) m in)))
                       {} others)]
    (reduce (fn [acc [d k]]
              (update acc k #(if (or (nil? %) (pos? (long (compare (term-key %) (term-key d))))) d %)))
            (sorted-map-by #(compare (vec %1) (vec %2)) base sub)
            member)))

(defn context-move
  "What the move of the `genlCx` edge `[sub super]` (stored, removed, or flipped in label)
  shows or hides, read from the taxonomy as it stands, whichever direction the move took:
  the edge's contribution, the contexts some reader under `sub` sees through the edge and
  through no other route.  `except-ctxs` holds the contexts stating an `except` that reaches
  a `genlCx` supporter's support, its meta-excepts' contexts included
  (`exc/genlCx-except-contexts`); `usable?` refuses an edge the walks without the edge must
  not cross (`(usable? a b)`).  Two strata:

  - `:raw`, over the global relation: `super`'s global ancestor set, `super` included,
    less `sub`'s global ancestor set without the edge.  Every reader under `sub` reads a
    subset of it, so the excepts in force, which are read off the raw ancestor set, move
    only in these contexts.
  - `:moved`, the effective stratum: per reader class (`reader-classes`), `super`'s
    ancestor set under the class's scope less the class's ancestor set of `sub` without
    the edge under that scope, unioned over the classes.  Every reader under `sub` gains
    or loses visibility of facts in these contexts and no others.

  `:shown` is `:moved` when the edge is active now and `:hidden` when it is not, each
  empty otherwise.  `:readers` holds each class's representative.  `:up` is `super`'s
  global ancestor set with `super`.  Three delays: `:under`, `sub`'s global descendant
  set, whose ancestor sets the move changed; `:seen`, every context a context of `:under`
  sees globally; and `:below`, the contexts of `:seen` that `:up` does not hold.  A placement the move creates or retires lies in
  `:under`, with an ingredient in `:moved` or `:below`.  `:gained-below` is the part of
  `:below` the readers that gain or lose a context see without the edge: a reader of
  `:under` that reaches `super` without the edge sees what it saw before.  While an
  `except` reaches a `genlCx` supporter (`except-ctxs` not empty) it is `:below`.  See
  docs/contexts.md, \"One context move\"."
  [tax sub super except-ctxs usable?]
  (let [t       @tax
        edge    [sub super]
        active? (contains? (get-in t [:genlCx :fwd sub] #{}) super)
        up      (conj (set (context-up-global tax super)) super)
        raw     (into #{} (remove (up-besides t nil sub edge usable?)) up)
        under   (delay (set (context-down-global tax sub)))
        ;; one walk up from all of `under`: a union of each member's cached ancestor set
        ;; costs |under| × |ancestors|, cubic over a chain of moves in one pass
        seen    (delay (let [fwd (get-in @tax [:genlCx :fwd])]
                         (reach-all @under #(get fwd % #{}))))
        below   (delay (into #{} (remove up) @seen))
        classes (if (empty? except-ctxs)
                  {#{} sub}
                  (reader-classes tax sub @under except-ctxs))
        moved   (into #{}
                      (mapcat (fn [r]
                                (let [scope (relation-scope tax :genlCx r)]
                                  (if (nil? scope)
                                    raw
                                    (remove (up-besides t scope sub edge usable?)
                                            (conj (set (closure-of-vis tax :genlCx :fwd super scope))
                                                  super))))))
                      (vals classes))]
    {:edge    edge
     :active? active?
     :raw     raw
     :moved   moved
     :shown   (if active? moved #{})
     :hidden  (if active? #{} moved)
     :readers (set (vals classes))
     :up      up
     :under   under
     :seen    seen
     :below   below
     :gained-below
     (if (seq except-ctxs)
       below
       (delay (let [{:keys [fwd rev]} (:genlCx @tax)
                    off?    (fn [a b] (and (= a sub) (= b super)))
                    ;; the contexts that reach `super` without the edge, `super` included
                    kept    (reach-all [super] (fn [n] (filter #(and (not (off? % n)) (usable? % n))
                                                               (get rev n #{}))))
                    gainers (remove kept @under)]
                (into #{} (remove up)
                      (reach-all gainers (fn [n] (remove #(off? n %) (get fwd n #{}))))))))}))

(defn context-down
  "Contexts that inherit from c, incl c, after context-visible genlCx exceptions.

  Reverse visibility has no single reader: every candidate descendant brings its own
  exception ancestor set.  So while some `except` targets a `genlCx` supporter
  (`relation-filter-active?`), the raw candidates are filtered by each candidate's own
  forward answer rather than by one static reverse scope — a filtered walk per
  candidate, which is why the answer is **memoized** per context and per reading
  (`*network-belief*`, `*search*`), one level beside the raw closure in the `genlCx` memo
  entry under the relation's generation and stamped on the change clock, as a map scope is
  (`relation-scope`).  With no except reaching `genlCx` the raw closure is the answer."
  [tax c]
  (let [raw (closure-of tax :genlCx :rev c)
        t   @tax]
    (if-not (relation-filter-active? t :genlCx)
      raw
      (let [rel  (:genlCx t)
            gen  (:gen rel)
            clock (observe/change-clock)
            memo (:closure-memo t)
            m    @memo
            cur  (when (= gen (get-in m [:genlCx :gen])) (get m :genlCx))
            dv   (:down-vis cur)
            k    [c *network-belief* *search*]
            tl   (caches/tally-of memo :T7)]
        (or (when-let [s (when (= clock (:clock dv)) (get (:by-ctx dv) k))]
              (caches/hit tl)
              s)
            (caches/held-if-settled
             #(caches/recomputed tl (into #{} (filter (fn [d] (sees? tax d c))) raw))
             (fn [s]
               (caches/compare-retired tl k [gen clock] s)
               (swap! memo
                      (fn [mm]
                        (let [e  (get mm :genlCx)
                              e  (if (= gen (:gen e)) e {:gen gen :fwd {} :rev {}})
                              dv (:down-vis e)
                              dv (if (= clock (:clock dv)) dv {:clock clock :by-ctx {}})]
                          (assoc mm :genlCx
                                 (assoc e :down-vis (assoc-in dv [:by-ctx k] s))))))
               s)))))))

(defn genlCx?-global
  "Does context sub see context super through **any** active edge — no context
  scope.  The `genlCx` twin of `genl?-global`, and `sees?`'s unscoped read; `wff`
  uses it to refuse a cycle, which is a property of the whole edge set."
  [tax sub super]
  (reachable-in? tax :genlCx sub super))

(defn contexts-seen-with-global
  "The contexts of `xs` that a context at or below `c` sees, through every active
  `genlCx` edge: `x` at or above `c`, at or below `c`, or sharing a descendant with `c`.
  The last test walks the contexts below `c` and those below `x` one step each in turn
  and stops when one walk ends.  The walk below `c` is one for the call, and once it ends
  one walk up from its contexts answers every `x`, so the call costs the smaller of
  `c`'s down-set and the `xs`' down-sets together, plus that upward walk, and never
  builds the larger down-set."
  [tax c xs]
  (let [up    (context-up-global tax c)
        kids  #(seq (context-children-global tax %))
        ;; one step of a depth-first walk of the contexts at or below a start: the stack
        ;; holds child seqs, so a context with n children costs one step, not n
        step  (fn [[seen stack]]
                (let [s     (peek stack)
                      n     (first s)
                      stack (if-let [more (next s)] (conj (pop stack) more) (pop stack))]
                  (if (contains? seen n)
                    [seen stack]
                    [(conj seen n) (if-let [cs (kids n)] (conj stack cs) stack)])))
        start (fn [a] [#{a} (if-let [cs (kids a)] (list cs) ())])
        done? #(empty? (second %))
        ;; the walk below `c`, one for the whole call: each `x`'s walk advances it a step
        ;; per step of its own, so the `xs` together advance it through `c`'s down-set at
        ;; most once
        wc    (volatile! (start c))
        ;; the contexts at or above a context at or below `c`, once that walk ended: one
        ;; upward walk, each context visited once
        above (delay (loop [seen (first @wc), stack (vec (first @wc))]
                       (if-let [n (peek stack)]
                         (let [ps (into [] (remove seen) (context-parents-global tax n))]
                           (recur (into seen ps) (into (pop stack) ps)))
                         seen)))
        ;; `x` and `c` share a descendant, found in the smaller of their down-sets
        shares? (fn [x]
                  (loop [wx (start x)]
                    (cond (done? @wc) (contains? @above x)
                          (done? wx)  (boolean (some #(genlCx?-global tax % c) (first wx)))
                          :else       (do (vswap! wc step) (recur (step wx))))))]
    (into #{} (filter #(or (contains? up %) (genlCx?-global tax % c) (shares? %))) xs)))

(defn sees? "Does context k see assertions in context y?" [tax k y]
  (if-some [scope (relation-scope tax :genlCx k)]
    (let [t   @tax
          rel (:genlCx t)]
      (reachable-filtered? k y t :genlCx scope
                           (when-not (:loose? rel) (:depth rel))
                           (:scc rel)))
    (reachable-in? tax :genlCx k y)))

(defn- seeing-member
  "The member of `ctxs` that sees every other member, or nil.  When one exists it is a
  **maximal common descendant**: any common descendant sees every member, so it sees
  the found `k`, making `k` its ancestor-or-self.  A rule and its antecedent facts
  sitting on one chain — nearly every forward firing — is answered here by |ctxs|²
  depth-pruned `sees?` probes, no closure read at all.

  It is *the* maximum unless two members see each other, in which case both qualify
  and they are the same place to stand; the tie is broken by `term-min` rather than by
  position, so a firing does not place its conclusion in whichever mutually-visible
  context its antecedents happened to be listed in first."
  [tax ctxs]
  (let [seers (filter (fn [k] (every? #(sees? tax k %) ctxs)) ctxs)]
    (when (seq seers) (term-min seers))))

(defn- placement-rep
  "The one context that stands for `k`'s mutually-visible group, or `k` itself when it
  is in no cycle.

  Every context in `k`'s component sees exactly what `k` sees, so if `k` can hold a
  conclusion so can every one of them, and all of them equally: the group is one place
  to stand wearing several names.  Which name is `term-min`'s — content, never arrival
  order — and it is applied to **both** of the function below's exits, or the same
  firing would land in `CxAlpha` when its antecedents named the cycle and in
  `CxBeta` when they named something above it."
  [tax k]
  (get (:scc (:genlCx @tax)) k k))

(defn- common-descendant-set
  "Every context that sees all of `cs` — the intersection of the down closures,
  stopping at the first empty intermediate rather than intersecting the rest into
  nothing."
  [tax cs]
  (if (seq cs)
    (reduce (fn [acc c]
              (let [i (set/intersection acc (context-down tax c))]
                (if (seq i) i (reduced i))))
            (context-down tax (first cs)) (rest cs))
    #{}))

(defn- maximal-in
  "The most general members of the candidate **set** `cands`, each collapsed to its
  cycle's one name.

  A member `k` is struck out when some *other* candidate stands above it — an element of
  `k`'s ancestor set that is itself a candidate — unless that ancestor sees `k` back, since two
  mutually visible contexts are equally general and would otherwise strike each other out
  and empty the set.  `placement-rep` then names the survivor's group, so a cycle
  contributes one member rather than all of them.

  Factored out because two callers want the same filter over different candidates:
  `maximal-common-descendants*` runs it over the common descendants of several contexts,
  and `maximal-contexts` over a set the caller has already filtered by a stronger
  predicate.  A copy each would drift; sharing one is what keeps a `CxInference` witness, a
  forward placement and an exception-aware placement one notion of *most general*.

  With `member?`, an ancestor strikes `k` when `member?` holds of it rather than when it
  is in `cands`: the candidates are then a subset of the set `member?` names that holds
  every maximum of it (`descendant-frontier`)."
  ([tax cands] (maximal-in tax cands #(contains? cands %)))
  ([tax cands member?]
   (into #{}
         (comp (remove (fn [k]
                         (some (fn [anc] (and (not= anc k)
                                              (member? anc)
                                              (not (sees? tax anc k))))
                               (context-up tax k))))
               (map (fn [k] (placement-rep tax k))))
         cands)))

(defn- descendant-frontier
  "The common descendants that a walk down the `genlCx` edges from `c0` meets first:
  the walk descends through the contexts `in?` rejects and stops at each it accepts.

  Every maximal common descendant is among them.  The common descendants are closed
  downward, so each context on a path from `c0` down to a maximum sits outside them, and
  the walk passes through it.  The walk visits `c0`'s descendants that are not common
  descendants, which the intersection of the down closures reads as well, and none of the
  common descendants below the ones it meets."
  [tax c0 in?]
  (let [rev (get-in @tax [:genlCx :rev])]
    (loop [todo [c0] seen #{c0} found #{}]
      (if-let [k (peek todo)]
        (if (in? k)
          (recur (pop todo) seen (conj found k))
          (let [kids (remove seen (get rev k))]
            (recur (into (pop todo) kids) (into seen kids) found)))
        found))))

(defn- maximal-common-descendants*
  "The general path of `maximal-common-descendant-contexts`, below — every case its
  one-context fast exit does not answer."
  [tax ctxs]
  ;; `into []` with the transducer, not `(vec (distinct ctxs))`: `clojure.core/distinct`
  ;; destructures its argument with `[f :as xs]`, which is `nth`, so the seq arity throws
  ;; on a **set** — and a set is exactly what a caller accumulating the contexts it used
  ;; has in hand (`vaelii.impl.vantage`).  The transducer arity reduces instead.
  (let [cs (into [] (distinct) ctxs)]
    (if-let [k (seeing-member tax cs)]
      #{(placement-rep tax k)}
      (if (relation-filter-active? @tax :genlCx)
        ;; an except on a `genlCx` supporter hides edges the raw adjacency still holds,
        ;; which the walk would pass through
        (maximal-in tax (common-descendant-set tax cs))
        (let [downs (mapv #(context-down tax %) cs)
              in?   (fn [k] (every? #(contains? % k) downs))
              c0    (nth cs (apply min-key #(count (nth downs %)) (range (count cs))))]
          (maximal-in tax (descendant-frontier tax c0 in?) in?))))))

(defn maximal-common-descendant-contexts
  "The *maximal* elements of the **common descendants** of `ctxs`: the contexts K
  that see every ctx (each ctx in up(K)) — i.e. the intersection of the down
  closures — keeping only the most general.  Returns a set: possibly empty (no
  common view), possibly several (incomparable maxima).  Used to place a
  forward-derived sentex given the contexts of the rule and its antecedent facts.

  Two exits ahead of the closure work, because this runs on every forward firing: a
  member that sees every other member is the maximum (`seeing-member`), and an
  intersection that empties part-way skips the maximality filter, whose `context-up`
  read per survivor is the expensive half on a wide lattice.

  **Mutually visible contexts are one maximum, not none and not two.**  A common
  ancestor only dominates `k` if it does not see `k` back; two contexts in a
  `genlCx` cycle are equally general, so each would otherwise strike the other
  out and the firing would have nowhere to land.  They are collapsed to one by
  `term-min` — the same content-keyed choice `seeing-member` makes — since placing the
  conclusion in every member of a cycle would store one claim several times over in
  contexts that already see each other."
  [tax ctxs]
  (let [c0 (first ctxs)]
    (if (and observe/*chain-fast-paths*
             (some? c0)
             (every? #(= c0 %) (next ctxs)))
      ;; every member is the one context — the general path's `seeing-member` answer
      ;; (its `sees?` probe is reflexive, so a single distinct member always passes
      ;; it), reached without building the distinct vector or filtering it.  This is
      ;; nearly every forward firing (rule and facts in one context).  `placement-rep`
      ;; still runs: a member of a `genlCx` cycle places at the group's one name
      ;; here as everywhere, and a context the taxonomy has never heard of comes back
      ;; as itself on both paths.
      #{(placement-rep tax c0)}
      (maximal-common-descendants* tax ctxs))))

(defn common-descendants
  "Every context that sees all of `ctxs` — the intersection of their down closures.
  The set `maximal-common-descendant-contexts` takes the maxima of, for a caller that
  needs to ask something *of each member* rather than only where the most general ones
  are (`clashes/exposed-clashes` asks each whether it can prove a disjointness)."
  [tax ctxs]
  (common-descendant-set tax (into [] (distinct) ctxs)))

(defn maximal-contexts
  "The maximal (most general) contexts in the supplied `ctxs` under the current
  context-visibility relation.

  Unlike `maximal-common-descendant-contexts`, this does not manufacture a candidate
  set from assertion contexts.  It maximizes a set a caller has already filtered by a
  stronger predicate — notably forward placement while visibility exceptions are
  active, where a sentex can be hidden at its assertion context and restored only in a
  descendant by a meta-exception.  Mutually visible contexts are collapsed through the
  same stable representative used by ordinary placement.

  A `CxInference` fan is the other caller (`vaelii.impl.vantage`): it has the set of
  readers that answered, and the readers *below* one that answered add no claim — a more
  specific context sees a superset of the same knowledge, so it answers whatever its
  ancestor did and for the same reasons.  Reporting all of them would make the answer
  count a fact about how finely the KB happens to be divided rather than about the
  question."
  [tax ctxs]
  (maximal-in tax (set ctxs)))

(defn common-descendant?
  "Does any context see every member of `ctxs` — is the common-descendant-set
  non-empty?  The boolean of `maximal-common-descendant-contexts`, for the callers
  that only ever ask existence (`settle`'s nogood pairing asks it of every opposed
  belief pair): the maximality filter never runs, the comparable case never reads a
  closure, and the fallback intersection stops at the first empty."
  [tax ctxs]
  ;; `into []` with the transducer rather than `(vec (distinct ctxs))`, for the reason
  ;; `maximal-common-descendants*` takes the same shape: `clojure.core/distinct`
  ;; destructures with `[f :as xs]`, which is `nth`, so its seq arity throws on a **set** —
  ;; and a set is what a caller accumulating the contexts an answer rests on has in hand.
  (let [cs (into [] (distinct) ctxs)]
    (boolean (and (seq cs)
                  (or (seeing-member tax cs)
                      (seq (common-descendant-set tax cs)))))))

(defn meet-closure
  "`ctxs` closed under `maximal-common-descendant-contexts` of its pairs: every context
  where two or more of them meet, plus the members themselves.

  The form a reader enumeration needs.  Knowledge stated in several contexts is read
  by whoever inherits some combination of them, and *which* combination changes the
  answer — a qualitative network composes only the constraints one reader can see
  (docs/qcn.md), an equality election runs only over the edges one reader can see
  (docs/equality.md).  So the parties are the fact-holding contexts and the contexts
  where they meet, and both callers want exactly this set.

  **Pairs reach every subset.**  A common descendant of `{a b c}` is a common
  descendant of `{a b}`, so it lies under some maximal one `m`, and under `c`; hence
  under a maximal common descendant of `{m c}`, which the next round adds.  The closure
  may therefore hold a context that is maximal for no subset — harmless for both
  callers, since a more specific reader sees a superset of the knowledge and so either
  agrees with a more general one or refines it.

  **Fewer than two contexts closes immediately**, which is every KB that has not
  divided the knowledge in question between contexts: there is nothing for a
  second to meet, so no closure is read at all."
  [tax ctxs]
  (let [start (set ctxs)]
    (if (< (count start) 2)
      start
      (loop [acc start]
        (let [more (into acc
                         ;; contexts are symbols, so order them directly — a `str` would be
                         ;; rebuilt for both on every pair of an n² sweep, and the result
                         ;; is a set, so the pair-dedup order is immaterial anyway
                         (for [a acc, b acc
                               :when (neg? (compare a b))
                               m (maximal-common-descendant-contexts tax [a b])]
                           m))]
          (if (= more acc) acc (recur more)))))))

;; ---- disjointness --------------------------------------------------------

(defn add-disjoint
  ([tax a b handle] (add-disjoint tax a b handle nil))
  ([tax a b handle ctx] (add-supported tax [:disjoint #{a b}] handle ctx)))
(defn del-disjoint! [tax a b handle] (del-supported! tax [:disjoint #{a b}] handle))

;; ---- sibling-disjoint exceptions: the exemption from the separation marks --------
;;
;; `(siblingDisjointException x y)` exempts the one pair `x`,`y` from the separation marks:
;; a `partition` / `separating` roster naming both (whose coverage half stands), a
;; `disjoint_metatype` and a `sibling_disjoint` parent, without disturbing either type's
;; disjointness from anything else.  A stated `(disjoint x y)` is not exempted.  The
;; exemption is read where a separation is: against the separated pair of supertypes, so
;; exempting two parts of a roster or two members of a metatype lifts what their
;; separation reached below them as well.  A `sibling_disjoint` parent separates every pair
;; of its specializations, so a subtype of `x` stays separated from `y`.  Keyed as an unordered
;; pair exactly like `disjoint`, belief-following through the same `cache-install` /
;; `cache-uninstall` refcount, and read by `exemption` inside `disjointness-test` behind
;; each mark arm's own guards, at the reader: a reader is exempted only by an exception
;; some supporter states where it reads.  An `orthogonal` exempts nothing.

;; `hash-set`, not a set literal: `(siblingDisjointException a a)` is stored (the
;; related-types family reports it), and a literal over two equal values throws.
(defn add-sib-exception
  ([tax a b handle] (add-sib-exception tax a b handle nil))
  ([tax a b handle ctx] (add-supported tax [:sib-exception (hash-set a b)] handle ctx)))
(defn del-sib-exception! [tax a b handle] (del-supported! tax [:sib-exception (hash-set a b)] handle))

(defn- member-keys
  "The `[:member m t]` keys with a stored supporter: those the stored facts of functor `m`
  install, or a raw taxonomy's walk."
  [t m]
  (let [member? (fn [k] (and (= :member (nth k 0)) (= m (nth k 1))))]
    (if (:raw? t)
      (into #{} (filter member?) (keys (reads/as-stored-supporter-map (:index t))))
      (into #{} (comp (mapcat #(keys-of t %)) (filter member?)) (extent-handles t [m])))))

(defn- forget-metatype
  "Drop `m` entirely: the mark, its recorded members, and their contexts and dirty marks
  under the member keys `ks`, whose supporters `unmark-disjoint-metatype!` retires from the
  index store.  Retiring them matters — a re-declaration rescans the store for members
  and posts them again, so a leftover supporter from the previous life would keep a
  membership alive after the sentex stating it had gone."
  [t m ks]
  (-> t
      (update :disjoint-metatypes disj m)
      (update :metatype-members dissoc m)
      (as-> t (reduce #(set-cache-ctxs %1 %2 nil) t ks))
      (update :cache-dirty #(reduce disj % ks))
      (update-in [:supporters :by-key] #(apply dissoc % ks))))

(defn mark-disjoint-metatype
  ([tax m handle] (mark-disjoint-metatype tax m handle nil))
  ([tax m handle ctx] (add-supported tax [:metatype m] handle ctx)))
(defn unmark-disjoint-metatype!
  "Drop `handle`'s support for the mark on `m`.  The last supporter going forgets `m`
  (`forget-metatype`), and its members' supporters leave the index store with it."
  [tax m handle]
  (retire! tax [:metatype m] handle)
  (let [t       @tax
        members (when (zero? (long (reads/stored-supporter-count-global (:index t) [:metatype m])))
                  (into {} (map (fn [k] [k (supporters-of t k)])) (member-keys t m)))]
    (doseq [[k sup] members, h (keys sup)] (retire! tax k h))
    (swap! tax (fn [t]
                 (let [t (update-in t [:supporters :by-handle]
                                    #(apply dissoc % (mapcat (comp keys val) members)))]
                   (supported-del t [:metatype m] handle #(forget-metatype % m (keys members)))))))
  tax)
(defn disjoint-metatype? [tax m] (contains? (:disjoint-metatypes @tax) m))
(defn disjoint-metatypes [tax] (:disjoint-metatypes @tax))

(def separation-functors
  "The functors whose sentence moves which pairs are separated, beside a stated
  `disjoint`, a `genl` edge (a cover's installed ones included) and a membership in a
  disjoint metatype: the two separating rosters, the two marks and an exception."
  '#{partition separating disjoint_metatype sibling_disjoint siblingDisjointException})

(defn stored-disjoint-metatype?
  "Whether some **stored** sentex marks `m` a disjoint metatype, believed or not: the
  supporter family under `[:metatype m]` counts one.  This is the gate the member arms
  read (`special/structural-integrate` and its disintegrate mirror), and it is storage
  rather than belief by the same discipline the `disjoint_metatype` integrate sweep
  follows: a membership is a *supporter*, recorded whatever the mark's label, so that
  belief can follow it through `refresh-cache-support`.  Gated on the believed set
  instead, a member asserted while the mark is defeated would never be recorded and
  reviving the mark would not separate it, and one retracted while the mark is defeated
  would leave its supporter behind for the life of the KB."
  [tax m]
  (pos? (long (reads/stored-supporter-count-global (:index @tax) [:metatype m]))))
(defn stored-disjoint-metatypes
  "Every metatype some stored sentex marks, believed or not — the set
  `special/post-taxonomy-supporters!`' member pass walks, so a defeated mark's members are
  posted exactly as the live member arm posts them."
  [tax]
  (stored-metatypes @tax))

;; A metatype's members are **recorded, not materialized**.  `(disjoint_metatype M)`
;; makes every pair of M's members disjoint.  Materializing that clique would mean
;; n(n-1)/2 real `(disjoint a b)` sentexes: quadratic in the member count and stored
;; as independent premises with no justification linking them back to M, so retracting
;; M could not withdraw them and the KB would fill with derived-looking content nobody
;; wrote.
;;
;; Instead membership is cached here and `disjoint?` consults it directly.  The
;; clique becomes a property of the code rather than of the store: nothing is
;; written, retracting M releases every pair at once, and retracting a single
;; `(M T)` releases exactly T's pairs.

(defn add-metatype-member
  ([tax m t handle] (add-metatype-member tax m t handle nil))
  ([tax m t handle ctx] (add-supported tax [:member m t] handle ctx)))
(defn del-metatype-member! [tax m t handle] (del-supported! tax [:member m t] handle))
(defn metatype-members [tax m] (get-in @tax [:metatype-members m] #{}))

;; ---- sibling disjointness ------------------------------------------------
;;
;; `(sibling_disjoint C)` marks `C` so that any two of its **specializations** — the
;; types below `C` under genl — share no instance, *unless one is itself a genl of
;; the other*.  It is the metatype clique keyed off the genl closure rather than a
;; recorded membership set: the mark alone is stored, and the pairs it separates are
;; read off `specs` in `separation-frame`, so nothing quadratic is materialized,
;; dropping the mark releases every pair at once, and `disjoint?` stays scopable.
;;
;; The genl-relatedness exception is what makes the derived member set safe.  A
;; specialization and its own supertype are both specializations of `C`, so without
;; the exception the mark would separate a subtype from the very type it refines; the
;; exception excludes exactly the genl-related pairs, leaving each specialization
;; disjoint from its siblings and no one else's ancestor.  Whether the
;; specializations *cover* `C` is a different claim this mark does not make.
;;
;; No recorded members means no teardown beyond the mark: `unmark` is the plain
;; `cache-uninstall` `del-disjoint!` uses, not the member-purging `forget-metatype`.

(defn mark-sibling-disjoint
  ([tax c handle] (mark-sibling-disjoint tax c handle nil))
  ([tax c handle ctx] (add-supported tax [:sib-disjoint c] handle ctx)))
(defn unmark-sibling-disjoint! [tax c handle] (del-supported! tax [:sib-disjoint c] handle))
(defn sibling-disjoints [tax] (:sibling-disjoint @tax))

;; ---- covering: the parts that exhaust a whole ----------------------------
;;
;; `(covering W P1 P2 …)` says that every instance of `W` is an instance of some named
;; part; `(partition W P1 P2 …)` says that and separates the parts.  The roster is
;; recorded here rather than expanded: a partition's separation is read by
;; `separation-frame` the way a metatype's member set is, and the coverage inference
;; belongs to `provers/CoveringProver`, so neither writes a sentex per pair.  The `genl`
;; edge each part owes the whole *is* installed, by the integrate arm and against the
;; covering sentex's own handle — a subtype relation the closure cannot see is one every
;; other reader disagrees about.

(defn cover-key
  "The support key one whole-and-parts declaration is held under: `[:cover [whole parts]
  kind]`, with `parts` deduplicated and sorted by printed name.  Sorted here rather than
  trusted from the sentence, so a KB whose commutativity marks are absent records the key
  a canonicalized one records."
  [whole parts kind]
  [:cover [whole (vec (sort-by nm/print-key (distinct parts)))] kind])

(defn add-cover
  ([tax whole parts kind handle] (add-cover tax whole parts kind handle nil))
  ([tax whole parts kind handle ctx] (add-supported tax (cover-key whole parts kind) handle ctx)))

(defn del-cover! [tax whole parts kind handle]
  (del-supported! tax (cover-key whole parts kind) handle))

(defn separating-covers
  "Every declaration whose parts separate each other, as `[whole parts kind]` — the
  `partition` and `separating` spellings, and not `covering`, which claims no separation
  (`separating-kind?`).  The roster `separation-frame` reads its parts arm off, and the
  fourth way this KB spells disjointness: a caller asking whether the KB separates any two
  types at all has to read it beside `disjoint-pairs`, `disjoint-metatypes` and
  `sibling-disjoints`."
  [tax] (:partitions @tax))

(defn coverings
  "Every declaration whose parts exhaust its whole, as `{whole #{[parts kind]}}` — the
  `covering` and `partition` spellings, and not `separating` (`covering-kind?`).  The
  roster a cover refutation is convicted against (`checks/cover-refutations`)."
  [tax] (:covers @tax))

(defn covers-naming
  "Every **covering** declaration naming `part` among its parts, as `[whole parts kind]`.
  Empty for every type no cover mentions, which is the lookup `CoveringProver` declines
  on — and empty for a `separating` roster, which claims no coverage to infer from."
  [tax part]
  (get-in @tax [:cover-parts part] #{}))

(defn covers-naming-visible
  "`covers-naming` filtered to the declarations `context` can see — the scoped read a
  query takes, as `disjoint?` takes `separation-frame`'s.  An unscoped context sees every
  declaration, exactly as it sees every disjointness."
  [tax part context]
  (let [ds (covers-naming tax part)]
    (if (scoped-context? context)
      (filterv (fn [[whole parts kind]]
                 (cache-entry-visible? tax [:cover [whole parts] kind] context))
               ds)
      (vec ds))))

(defn- genls-at
  "`t`'s supertypes as `context` reads them: through the edges some supporter states in
  an ancestor set (`genls-asserted-in`), from a concrete context (`genls`), or through
  every edge (`genls-global`)."
  [tax t context]
  (cond (set? context)            (genls-asserted-in tax t context)
        (scoped-context? context) (genls tax t context)
        :else                     (genls-global tax t)))

(defn- entry-visible-at?
  "Does flat-cache entry `k` have a supporter `context` reads: stated in an ancestor set,
  with no belief callback, or believed and visible from a concrete context
  (`cache-entry-visible?`)."
  [tax k context]
  (if (set? context)
    (ctxs-visible? (get-in @tax [:cache-ctxs k]) context)
    (cache-entry-visible? tax k context)))

(defn- exemption
  "`(fn [x y])` → does a `siblingDisjointException` over the pair `x`, `y` exempt it from
  the separation marks for a reader at `context`: one with a supporter `context` reads
  (`entry-visible-at?`), or, for an unscoped `context`, any stored one.  One map lookup
  when no exception names `x`."
  [tax context]
  (let [idx (:sib-exception-index @tax)]
    (cond
      (empty? idx)
      (constantly false)

      (or (set? context) (scoped-context? context))
      (fn [x y] (and (contains? (get idx x) y)
                     (entry-visible-at? tax [:sib-exception (hash-set x y)] context)))

      :else
      (fn [x y] (contains? (get idx x) y)))))

(defn sib-exceptions?
  "Is any `siblingDisjointException` stored?"
  [tax]
  (boolean (seq (:sib-exception-index @tax))))

(defn covers-of
  "Every covering declaration over `whole`, as `[parts kind]`."
  [tax whole]
  (get-in @tax [:covers whole] #{}))

(defn covers-over
  "Every declaration covering `t` or any of its supertypes, as `[whole parts]` — what a
  membership `(t x)` puts `x` under.  Scoped: the declarations `context` cannot see are
  dropped, as they are in `covers-naming-visible`.  `context` may be an ancestor set, read
  as `disjoint?` reads one.

  Walks the smaller of the two sides: the covered wholes tested against `t`'s closure,
  or the closure looked up in the cover table.  A clash pass asks this of every
  membership, and a KB's covers are usually far fewer than a type's supertypes."
  [tax t context]
  (let [covers  (:covers @tax)]
    (if (empty? covers)
      []
      (let [scoped? (or (set? context) (scoped-context? context))
            as      (genls-at tax t context)
            wholes  (if (< (count covers) (count as))
                      (filter #(contains? as %) (keys covers))
                      (filter #(contains? covers %) as))]
        (into []
              (mapcat (fn [whole]
                        (keep (fn [[parts kind]]
                                (when (or (not scoped?)
                                          (entry-visible-at?
                                           tax [:cover [whole parts] kind] context))
                                  [whole parts]))
                              (get covers whole))))
              wholes)))))

(defn- separable-terms
  "The types a separation can reach another through: those declared disjoint from
  something, the members of a disjoint metatype, the sibling-disjoint parents and the
  parts of a partition.  `separation-frame` reads nothing of a supertype outside it but
  the sibling arm's chain.  Held in the closure cache under the separation stamp, so the
  declarations are read once per stamp."
  [tax stamp]
  (let [t   @tax
        lru (:closure-lru t)
        k   [:separable-terms stamp]]
    (or (caches/lru-get lru k)
        (caches/lru-put! lru k
                         (-> (set (keys (:disjoint-index t)))
                             (into (mapcat #(get (:metatype-members t) %)) (:disjoint-metatypes t))
                             (into (:sibling-disjoint t))
                             (into (mapcat second) (:partitions t)))))))

(defn- separable-genls
  "`genls-global` of `a` cut to `separable-terms`: what the unscoped `separation-frame`
  reads of `a`'s supertypes.  Built like the closure, from the parents' cuts
  (`reach-by-parents`), and held beside the closures in the closure cache, keyed by the
  `genl` generation and the separation stamp and weighed by the terms each holds.  Most
  types sit under no separable type, so a frame over every type of a large KB costs the
  edges and an empty set a type, where a closure a type overran the cache.  A build
  handed back (a cycle `:scc` has not recorded, a parent's cut evicted) cuts the closure."
  [tax a]
  (let [t     @tax
        rel   (:genl t)
        lru   (:closure-lru t)
        stamp (separation-stamp tax)
        terms (separable-terms tax stamp)
        key   (fn [n] [:genl (:gen rel) :separable stamp n])
        scc   (:scc rel)
        node  (get scc a a)]
    (if (empty? terms)
      #{}
      (or (caches/lru-get lru (key node))
          (reach-by-parents node #(get (:fwd rel) %) scc
                            #(caches/lru-get lru (key %))
                            #(caches/lru-put! lru (key %1) %2)
                            (filter terms) nil)
          (into #{} (filter terms) (genls-global tax a))))))

(defn separable?
  "Does a separation reach `t` from above: is `t` or one of its supertypes declared
  disjoint from something, a member of a disjoint metatype, a sibling-disjoint parent or
  a part of a partition (`separable-genls`)?  A `genl` edge whose upper end answers false
  places its lower end under no separated type."
  [tax t]
  (boolean (seq (separable-genls tax t))))

(defn sentence-separation-ends
  "The types `sentence` names whose subtypes' separations it moves, arriving or leaving,
  as a set: the lower end of each `genl` edge it installs (`installed-edges`) whose upper
  end is `separable?`, the types a stated `disjoint`, a `siblingDisjointException` or a
  `sibling_disjoint` mark names, the parts of a `partition` or `separating` roster, the
  members of a `disjoint_metatype` mark, and for a membership in a disjoint metatype the
  type it names and the metatype's members.  An edge places its lower end under every
  supertype of its upper end, and makes two marked types genl-related only when the upper
  one is marked, so an edge whose upper end is not separable names nothing.  The sentence
  twin of `separation-ends`, which reads a flat-cache key: it needs no record, so it
  answers for a sentence that has left.  Taxonomy reads alone, and none for a sentence of
  no such shape."
  [tax sentence]
  (let [f (when (seq? sentence) (nm/functor sentence))]
    (if-not (symbol? f)
      #{}
      (let [args (nm/args sentence)]
        (cond-> (into #{} (keep (fn [[sub super]] (when (separable? tax super) sub)))
                      (installed-edges sentence))
          (contains? '#{disjoint siblingDisjointException sibling_disjoint} f)
          (into (filter symbol?) args)
          (contains? '#{partition separating} f)
          (into (second (cover-parts sentence)))
          (= 'disjoint_metatype f)
          (into (metatype-members tax (first args)))
          (and (= 1 (count args)) (disjoint-metatype? tax f))
          (-> (into (metatype-members tax f)) (into (filter symbol?) args)))))))

(defn- intact-scc
  "The part of `rel`'s component map (`:scc`) whose components stay strongly connected
  through the edges effective in `scope`: those where every edge between two members is
  one `scope` sees, held through `held` / `hold!` under `k`.  A build over the visible
  edges may read such a component as one unit, as the unscoped build reads every one; a
  component the scope breaks is left out, and a build meeting its cycle hands back."
  [t rel scope held hold! k]
  (let [scc (:scc rel)]
    (if (empty? scc)
      scc
      (or (held k)
          (let [whole? (fn [[r ms]]
                         (every? (fn [[m]]
                                   (let [vis (set (visible-neighbours t :genl :fwd scope m))]
                                     (every? #(or (not= r (get scc %)) (contains? vis %))
                                             (get (:fwd rel) m))))
                                 ms))
                v      (into {} (comp (filter whole?) (mapcat val)) (group-by val scc))]
            (hold! k v)
            v)))))

(defn- separable-genls-at
  "`genls-at` of `a` from `context` cut to `separable-terms`, or a superset of that cut
  holding no other separable type: what a scoped `separation-frame` and
  `disjointness-test` read of a type's supertypes, which is only which separable types
  are among them.  Built from the parents' cuts through the edges `context` sees
  (`reach-by-parents`), reading a component the scope leaves whole as one unit
  (`intact-scc`), so framing many types costs the edges above them once rather than a
  scoped closure a type.  An ancestor set (a set `context`) carries no belief callback,
  so its cuts are held in the closure cache under the relation's `:gen`, as the unscoped
  ones are (`separable-genls`); a concrete context's scope reads belief, so it answers
  the scoped closure.  A type whose build hands back (a cycle through a component the scope
  breaks) answers the scoped closure itself, uncut, since cutting it would cost more
  than reading it, and the hand back is remembered.  A reader whose scope filters no
  edge reads the unscoped cut."
  [tax a context]
  (let [scope (cond (set? context)            context
                    (scoped-context? context) (relation-scope tax :genl context))
        stamp (separation-stamp tax)
        terms (separable-terms tax stamp)
        t     @tax
        rel   (:genl t)
        lru   (:closure-lru t)
        held  #(caches/lru-get lru %)
        hold! #(caches/lru-put! lru %1 %2)]
    (cond
      (empty? terms)                           #{}
      (and (nil? scope) (not (set? context)))  (separable-genls tax a)
      (not (set? context))                     (genls-at tax a context)
      :else
      (let [scc  (intact-scc t rel scope held hold! [:genl (:gen rel) :intact-scc scope])
            node (get scc a a)
            key  (fn [n] [:genl (:gen rel) :separable-at scope stamp n])
            got  (held (key node))]
        (cond
          (= ::uncut got) (genls-at tax a context)
          (some? got)     got
          :else
          (or (reach-by-parents node #(visible-neighbours t :genl :fwd scope %) scc
                                #(let [h (held (key %))] (when-not (= ::uncut h) h))
                                #(hold! (key %1) %2)
                                (filter terms) nil)
              (do (hold! (key node) ::uncut)
                  (genls-at tax a context))))))))

(defn- separation-frame
  "Everything a disjointness question about `a` settles before any candidate is named:
  `a`'s supertype closure, the declarations that reach it, and the visibility
  predicates its context imposes.  The closure is read cut to the types a separation can
  reach through (`separable-genls`, `separable-genls-at` scoped), and whole only for the
  sibling arm's chain under a marked parent above `a`.

  What survives the build is only what `a` can possibly be separated *by*: the
  supertypes of `a` that are declared disjoint from something (`:seps`, each with the
  set it is declared disjoint from), and the metatypes some supertype of `a` belongs
  to (`:metas`, each as `[m members members-above-a]`).  Both are usually empty — most
  types are declared disjoint from nothing and belong to no metatype — and when they
  are, no candidate is looked at at all, not even to read its closure.

  Two readers ask it in opposite directions: `disjointness-test` closes over it and
  tests a candidate, `separating-partners` reads the same two rosters to *enumerate*
  the other side.  One prologue, because the failure two copies of it would have is a
  candidate the predicate convicts and the enumeration never reaches.

  A nil, variable, or otherwise unscoped `context` gives visibility predicates that are
  constantly true *and take no key*, so the unscoped path never builds the `#{x y}` a
  visibility lookup would need — the whole reason the pair set is not what disjointness
  is asked of."
  [tax a context]
  (let [scoped? (or (set? context) (scoped-context? context))
        ;; `a`'s supertypes cut to the separable ones: every arm but the sibling arm's
        ;; chain asks only whether a separable type is among them
        as      (if scoped? (separable-genls-at tax a context) (separable-genls tax a))
        all-as  (if scoped? (delay (genls-at tax a context)) (delay (genls-global tax a)))
        t       @tax
        members (:metatype-members t)
        pair-vis?   (if scoped?
                      (fn [x y] (entry-visible-at? tax [:disjoint #{x y}] context))
                      (fn [_ _] true))
        meta-vis?   (if scoped?
                      (fn [m] (entry-visible-at? tax [:metatype m] context))
                      (fn [_] true))
        member-vis? (if scoped?
                      (fn [m ty] (entry-visible-at? tax [:member m ty] context))
                      (fn [_ _] true))
        sib-vis?    (if scoped?
                      (fn [c] (entry-visible-at? tax [:sib-disjoint c] context))
                      (fn [_] true))
        part-vis?   (if scoped?
                      (fn [whole ps kind]
                        (entry-visible-at? tax [:cover [whole ps] kind] context))
                      (fn [_ _ _] true))
        ;; `a`'s separable supertypes, each with what it is declared disjoint from
        seps  (let [didx (:disjoint-index t)]
                (into [] (keep (fn [x] (when-let [ys (get didx x)] [x ys]))) as))
        ;; and the metatypes that hold some supertype of `a` — a metatype holding none
        ;; can separate `a` from nothing, so it leaves the roster here rather than
        ;; being re-examined per candidate
        metas (into []
                    (keep (fn [m]
                            (let [ms (get members m)]
                              (when (and (seq ms) (meta-vis? m))
                                (let [in-a (filterv #(and (contains? as %) (member-vis? m %)) ms)]
                                  (when (seq in-a) [m ms in-a]))))))
                    (:disjoint-metatypes t))
        ;; the sibling-disjoint parents `a` sits under, each as `[c under-c? below-a]`:
        ;; the parent, a test of whether a type is a specialization of `c` (which a
        ;; candidate's side is tested with), and the specializations of `c` that are
        ;; supertypes of `a`.  The test reads the type's own supertype closure rather than
        ;; `c`'s spec closure, which holds the whole clique and is rebuilt after every
        ;; `genl` edge.  Empty unless a marked parent stands above `a`, so an ordinary
        ;; assert reads nothing here — the same short-circuit the two rosters above give.
        sibs  (into []
                    (keep (fn [c]
                            (when (and (contains? as c) (sib-vis? c))
                              (let [under-c? (fn [x]
                                               (contains? (genls-at tax x context) c))
                                    below-a  (filterv #(and (not= % c) (under-c? %)) @all-as)]
                                (when (seq below-a) [c under-c? below-a])))))
                    (:sibling-disjoint t))
        ;; the partitions holding some supertype of `a`, each as `[parts above-a key]`,
        ;; `key` the declaration's flat-cache key.  A partition's part roster is a
        ;; metatype's member set under another name, so this is the metatype arm's roster
        ;; read off `:partitions` — and it is empty unless a partition names a supertype
        ;; of `a`, giving the same short-circuit.
        parts (into []
                    (keep (fn [[whole ps kind]]
                            (when (part-vis? whole ps kind)
                              (let [in-a (filterv #(contains? as %) ps)]
                                (when (seq in-a) [ps in-a [:cover [whole ps] kind]])))))
                    (:partitions t))]
    {:scoped? scoped? :seps seps :metas metas :sibs sibs :parts parts
     :pair-vis? pair-vis? :member-vis? member-vis?}))

(defn separation-test
  "`disjointness-test`, or nil when no declaration reaches `a`: a caller testing many
  candidates against `a` learns from the nil that every one answers false, and tests
  none.  Unscoped (`context` nil), the test is symmetric: when `a`'s answers `b`,
  `b`'s answers `a`, so a nil for `a` also means no candidate's test answers `a`."
  ([tax a context] (separation-test tax a context (exemption tax context)))
  ([tax a context exempt?]
   (let [{:keys [scoped? seps metas sibs parts pair-vis? member-vis?]}
         (separation-frame tax a context)]
     (when-not (and (empty? seps) (empty? metas) (empty? sibs) (empty? parts))
       ;; genl-relatedness is read **globally**, never through the reader's ancestor set: the
       ;; exception is the same one `wff/disjoint-problems` applies to an explicit pair,
       ;; and reading it scoped would let a descendant context that cannot see an
       ;; `(genl x y)` edge separate a pair the whole KB knows overlaps.
       ;; `exempt?` sits behind the `not=` / `genl-related?` guards, so the negative path
       ;; pays one map lookup only for a pair those tests already admitted.  The three
       ;; mark arms read it; a stated `disjoint` names its pair and no exception lifts it.
       (let [genl-related? (fn [x y] (or (genl?-global tax x y) (genl?-global tax y x)))]
         (fn [b]
           ;; `b`'s supertypes cut to the separable ones as `a`'s are, and whole only for
           ;; the sibling arm's chain
           (let [bs     (if scoped? (separable-genls-at tax b context) (separable-genls tax b))
                 all-bs (if scoped? (delay (genls-at tax b context)) (delay (genls-global tax b)))]
             (boolean
              (or (some (fn [[x ys]]
                          (some (fn [y] (and (not= x y) (contains? bs y) (pair-vis? x y)))
                                ys))
                        seps)
                  ;; a metatype separates when it holds a supertype of `a` and a *different*
                  ;; supertype of `b`.  Driven from the members, not from `as × bs`: a
                  ;; metatype has a handful where a closure has a chain's worth, and the
                  ;; question is a set intersection whichever side it is read from.
                  (some (fn [[m ms in-a]]
                          (let [in-b (filterv #(and (contains? bs %) (member-vis? m %)) ms)]
                            (some (fn [x]
                                    (some #(and (not= x %) (not (genl-related? x %))
                                                (not (exempt? x %)))
                                          in-b))
                                  in-a)))
                        metas)
                  ;; a sibling-disjoint parent `c` separates when a supertype of `a` and a
                  ;; *different, non-genl-related, non-exempted* supertype of `b` are both
                  ;; proper specializations of `c`.  Read from the two closures like the
                  ;; metatype arm; the genl-relatedness guard is what leaves a subtype
                  ;; separated from its siblings but not from its own supertype, and
                  ;; `exempt?` is what spares a declared pair without disturbing either.
                  (some (fn [[c under-c? below-a]]
                          (let [below-b (filterv #(and (not= % c) (under-c? %)) @all-bs)]
                            (some (fn [x]
                                    (some (fn [y] (and (not= x y) (not (genl-related? x y))
                                                       (not (exempt? x y))))
                                          below-b))
                                  below-a)))
                        sibs)
                  ;; a partition separates on its part roster exactly as a metatype
                  ;; separates on its members: a part above `a` and a *different*,
                  ;; non-genl-related, non-exempted part above `b`.  `covering` alone
                  ;; records no partition, so its parts reach nothing here and may overlap.
                  (some (fn [[ps in-a]]
                          (let [in-b (filterv #(contains? bs %) ps)]
                            (some (fn [x]
                                    (some #(and (not= x %) (not (genl-related? x %))
                                                (not (exempt? x %)))
                                          in-b))
                                  in-a)))
                        parts))))))))))

(defn disjointness-test
  "A predicate `type -> boolean` answering `(disjoint? tax a <type> context)` — the
  question with everything that depends on `a` and `context` alone read once
  (`separation-frame`).  `disjoint?` is this asked once; `checks/disjoint-problem`
  asks it of every type the term already holds, which is the shape it exists for.

  A type `a` no declaration reaches answers false without looking at the candidate at
  all; one that *is* separable pays a set lookup per declaration rather than a walk
  over the closure product.

  `exempt?` is the `siblingDisjointException` read, `(fn [x y])`, consulted by the three
  mark arms over the separated pair of supertypes and never by the `disjoint` arm: by
  default the exceptions `context` reads (`exemption`); `(constantly false)` reads none,
  which answers true for every pair some reader can read separated."
  ([tax a context] (disjointness-test tax a context (exemption tax context)))
  ([tax a context exempt?]
   (or (separation-test tax a context exempt?) (constantly false))))

(defn separating-partners
  "The types a **visible declaration** separates `a` from: every `y` such that some
  supertype of `a` is declared `(disjoint x y)` with `x` ≠ `y`, shares a disjoint
  metatype with `y`, stands beside `y` as a proper specialization of one
  `(sibling_disjoint C)` parent, or stands beside `y` in one `partition` roster —
  the same four arms `disjointness-test` tests, with the same global genl-relatedness
  guard and the same `siblingDisjointException` exemptions at `context` on the latter three.

  This is the enumeration `disjointness-test` is the membership test of, and the two
  read one frame so they cannot disagree.  Every type disjoint from `a` is a **subtype
  of one of these and nothing else is** — disjointness is inherited downward through
  `genl` and reaches a candidate no other way — so `(disjoint a ?t)` is answered by
  `specs` of this set.  What that buys is the bound: the answer is a function of the
  declarations, which are few, rather than of the vocabulary, which is not.

  Belief and context are the frame's, so a retracted declaration has already left
  `:disjoint-index` / `:metatype-members`, and a declaration the reader's context
  cannot see is dropped by the same visibility predicate that decides the pair for
  `disjoint?`.  The index is *not* itself context-scoped, which is why the filter is
  applied here rather than trusted to the lookup.

  `exempt?` is the `siblingDisjointException` read, as for `disjointness-test`."
  ([tax a context] (separating-partners tax a context (exemption tax context)))
  ([tax a context exempt?]
   (let [{:keys [scoped? seps metas sibs parts pair-vis? member-vis?]} (separation-frame tax a context)
         ;; global genl-relatedness, for the reason `disjointness-test` states
         genl-related? (fn [x y] (or (genl?-global tax x y) (genl?-global tax y x)))]
     (persistent!
      (as-> (transient #{}) acc
        (reduce (fn [acc [x ys]]
                  (reduce (fn [acc y]
                            (if (and (not= x y) (pair-vis? x y)) (conj! acc y) acc))
                          acc ys))
                acc seps)
        (reduce (fn [acc [m ms in-a]]
                  (reduce (fn [acc y]
                            (if (and (member-vis? m y)
                                     (some #(and (not= % y) (not (genl-related? % y)) (not (exempt? % y)))
                                           in-a))
                              (conj! acc y)
                              acc))
                          acc ms))
                acc metas)
        ;; a sibling-disjoint parent separates `a` from every proper specialization of
        ;; `c` a non-genl-related, non-exempted supertype of `a` sits beside — the
        ;; enumeration side of the same guarded clique `disjointness-test` tests.
        (reduce (fn [acc [c _ below-a]]
                  (reduce (fn [acc y]
                            (if (and (not= y c)
                                     (some (fn [x] (and (not= x y) (not (genl-related? x y))
                                                        (not (exempt? x y))))
                                           below-a))
                              (conj! acc y)
                              acc))
                          acc (if scoped? (specs tax c context) (specs-global tax c))))
                acc sibs)
        ;; a partition separates `a` from every other part of a roster holding a
        ;; non-genl-related, non-exempted supertype of `a` — the enumeration side of the
        ;; partition arm, written as the metatype arm above is.
        (reduce (fn [acc [ps in-a]]
                  (reduce (fn [acc y]
                            (if (some #(and (not= % y) (not (genl-related? % y))
                                            (not (exempt? % y)))
                                      in-a)
                              (conj! acc y)
                              acc))
                          acc ps))
                acc parts))))))

(defn separating-keys
  "The flat-cache keys of the declarations `context` sees that separate `a` from `b`, as a
  set: each `[:disjoint #{x y}]` pair, each disjoint metatype's `[:metatype m]` mark with
  its two `[:member m _]` memberships, each `[:sib-disjoint c]` parent and each separating
  cover's `[:cover [whole parts] kind]`, over a supertype `x` of `a` and a different
  supertype `y` of `b`.  The entries `disjointness-test` answers true through, under its
  guards, read off the same frame; empty when `a` and `b` are not disjoint at `context`.

  `exempt?` is the `siblingDisjointException` read, as for `disjointness-test`: by default
  the pairs `context` reads exempted; `(constantly false)` names every separation stated
  over the pair, the marks an exception lifts included."
  ([tax a b context] (separating-keys tax a b context (exemption tax context)))
  ([tax a b context exempt?]
   (let [{:keys [seps metas sibs parts pair-vis? member-vis?]} (separation-frame tax a context)]
     (if (and (empty? seps) (empty? metas) (empty? sibs) (empty? parts))
       #{}
       ;; global genl-relatedness, for the reason `disjointness-test` states
       (let [bs      (genls-at tax b context)
             sep?    (fn [x y] (and (not= x y)
                                    (not (genl?-global tax x y)) (not (genl?-global tax y x))
                                    (not (exempt? x y))))]
         (into #{}
               cat
               [(for [[x ys] seps, y ys
                      :when (and (not= x y) (contains? bs y) (pair-vis? x y))]
                  [:disjoint #{x y}])
                (for [[m ms in-a] metas
                      x in-a
                      y ms
                      :when (and (contains? bs y) (member-vis? m y) (sep? x y))
                      k [[:metatype m] [:member m x] [:member m y]]]
                  k)
                (for [[c under-c? below-a] sibs
                      :when (some (fn [x] (some #(and (not= % c) (under-c? %) (sep? x %)) bs))
                                  below-a)]
                  [:sib-disjoint c])
                (for [[ps in-a k] parts
                      :when (some (fn [x] (some #(and (contains? bs %) (sep? x %)) ps)) in-a)]
                  k)]))))))

(defn separation-routes
  "Each way the declarations separate `a` from `b` over the unscoped closures with no
  `siblingDisjointException` read, as `{:keys #{k} :links [[sub super]] :pair [x y]}`: the flat-cache
  keys it reads (`separating-keys`' entries), the separated supertypes `x` of `a` and `y`
  of `b`, and the `genl` subsumptions it climbs, `a` to `x` and `b` to `y`, and for a
  `sibling_disjoint` parent `c` also `x` and `y` to `c`.  A reflexive subsumption is left
  out.  Empty exactly when `disjointness-test` reading no exemption answers false from
  `a`'s side.  A placed nogood names one route's supporters and edges as its grounds
  (docs/nmtms.md).  A route through a mark carries `:mark? true`: an exception can exempt
  it (`route-exempted?`)."
  [tax a b]
  (let [{:keys [seps metas sibs parts]} (separation-frame tax a nil)
        bs     (genls-global tax b)
        unrel? (fn [x y] (and (not= x y) (not (genl?-global tax x y)) (not (genl?-global tax y x))))
        route  (fn [ks x y & links]
                 {:keys ks :pair [x y] :mark? true
                  :links (into [] (remove (fn [[s t]] (= s t))) (concat [[a x] [b y]] links))})]
    (concat
     (for [[x ys] seps, y ys :when (and (not= x y) (contains? bs y))]
       (dissoc (route #{[:disjoint #{x y}]} x y) :mark?))
     (for [[m ms in-a] metas, x in-a, y ms :when (and (contains? bs y) (unrel? x y))]
       (route #{[:metatype m] [:member m x] [:member m y]} x y))
     (for [[c under-c? below-a] sibs, x below-a, y bs
           :when (and (not= y c) (under-c? y) (unrel? x y))]
       (route #{[:sib-disjoint c]} x y [x c] [y c]))
     (for [[ps in-a k] parts, x in-a, y ps :when (and (contains? bs y) (unrel? x y))]
       (route #{k} x y)))))

(defn route-exempted?
  "Does a `siblingDisjointException` that `context` reads (a context or an ancestor set)
  exempt the separated pair of the mark route `route` (`separation-routes`, `:mark?`)?
  False for a route through a stated `disjoint` and for a route with no `:pair`."
  [tax {:keys [pair mark?]} context]
  (boolean (and mark? pair ((exemption tax context) (first pair) (second pair)))))

(defn monotonic-route-witness
  "What a reader at `context` reads the separation route `route` (`separation-routes`)
  through when the route answers a denial, or nil when the reader reads no denial off
  it.  Three conditions, the soundness rule of docs/taxonomy.md, \"A separation answers a
  denial\":

  * every flat-cache key of the route has a supporter the reader sees
    (`visible-supporters`) that `supporter-class` reads `:monotonic`.  The declarations
    are on the forced-monotonic roster, which `res/holding-class` reads `:monotonic`
    while believed, so for them the test is belief and visibility.  A disjoint
    metatype's `[:member m y]` membership is an ordinary fact, and a `:default` one
    separates nothing here;
  * no `siblingDisjointException` the reader sees exempts the route's separated pair
    (`route-exempted?`);
  * each subsumption the route climbs has a path the reader sees whose every edge holds
    at `:monotonic` (`reach-support` with `supporter-class`, the widest bottleneck).  A
    `:default` edge on either side applies forward and does not contrapose.

  `supporter-class` is `handle → class`, a live JTMS `defeat-class` read, nil for a handle
  that is OUT.  The witness is `{:keys :pair :supports :edges}`: the route's keys and
  separated pair, one `:monotonic` supporter handle per key, and the `[handle ctx]`
  supporters of the edges climbed."
  [tax {:keys [keys links pair] :as route} context supporter-class]
  (let [mono? #(= :monotonic (supporter-class %))]
    (when-not (route-exempted? tax route context)
      (when-let [sups (reduce (fn [acc k]
                                (if-let [h (first (filter mono? (sort (visible-supporters tax k context))))]
                                  (conj acc h)
                                  (reduced nil)))
                              [] (nm/sort-by-content-key nm/print-key compare keys))]
        (when-let [edges (reduce (fn [acc [sub super]]
                                   (let [path (reach-support tax :genl sub super context
                                                             supporter-class [:monotonic])]
                                     (if (and path (every? #(mono? (first %)) path))
                                       (into acc path)
                                       (reduced nil))))
                                 [] links)]
          {:keys keys :pair pair :supports sups :edges edges})))))

(defn separation-routes-held
  "`separation-routes` of `a` and `b`, as a vector held in the closure cache under the
  `genl` generation and the separation stamp: the routes are read over the unscoped
  closures and the declarations alone, so a reader asking one pair again before either
  moves reads a map entry (`res/separation-denials`, `membership/cover-routes`)."
  [tax a b]
  (let [t   @tax
        lru (:closure-lru t)
        k   [:separation-routes (:gen (:genl t)) (separation-stamp tax) a b]]
    (or (caches/lru-get lru k)
        (caches/lru-put! lru k (vec (separation-routes tax a b))))))

(defn pair-separated?
  "Does a declaration separate the type `a` from the type `b` over the unscoped closures,
  with no `siblingDisjointException` read: `separation-test` with no reader and no
  exemption, a superset over every reader, and symmetric.  Held in the closure cache
  under the `genl` generation and the separation stamp, so the membership family's cover
  arm (`membership/term-nogoods`) tests a held type against a part once per stamp and
  reads a map entry after."
  [tax a b]
  (let [t   @tax
        lru (:closure-lru t)
        k   [:pair-separated (:gen (:genl t)) (separation-stamp tax) a b]
        v   (caches/lru-get lru k)]
    (if (some? v)
      v
      (caches/lru-put! lru k (boolean (some-> (separation-test tax a nil (constantly false))
                                              (apply [b])))))))

(defn separating-pairs
  "Every **ordered** pair `[x y]`, `x` ≠ `y`, that a visible declaration separates —
  the declared pairs in both directions, plus each disjoint metatype's members against
  each other.

  `separating-partners` with neither side given, and it answers the same question for
  the goal that gives nothing away: `(disjoint ?x ?y)` is `specs(x) × specs(y)` over
  these.  Bounded by the declaration set by construction, which is what keeps a
  two-variable goal — a shape a user types by accident — from being a walk over the
  vocabulary squared."
  [tax context]
  (let [scoped? (scoped-context? context)
        t       @tax
        exempt? (exemption tax context)
        vis?    (if scoped? #(cache-entry-visible? tax % context) (fn [_] true))]
    (concat
     (for [s (:disjoint t)
           :let  [[x y] (declared-pair s)]
           :when (and (not= x y) (vis? [:disjoint s]))
           pair  [[x y] [y x]]]
       pair)
     (for [m  (:disjoint-metatypes t)
           :when (vis? [:metatype m])
           :let  [ms (filterv #(vis? [:member m %]) (get (:metatype-members t) m))]
           x  ms
           y  ms
           :when (and (not= x y)
                      (not (genl?-global tax x y))       ; global, per disjointness-test
                      (not (genl?-global tax y x))
                      (not (exempt? x y)))]
       [x y])
     ;; each sibling-disjoint parent contributes its proper specializations against each
     ;; other, minus the genl-related pairs and the exempted pairs the clique spares
     (for [c  (:sibling-disjoint t)
           :when (vis? [:sib-disjoint c])
           :let  [ss (disj (if scoped? (specs tax c context) (specs-global tax c)) c)]
           x  ss
           y  ss
           :when (and (not= x y)
                      (not (genl?-global tax x y))       ; global, per disjointness-test
                      (not (genl?-global tax y x))
                      (not (exempt? x y)))]
       [x y])
     ;; each partition contributes its parts against each other, under the same two
     ;; guards — the metatype arm's roster, read off a `partition` declaration
     (for [[whole ps kind] (:partitions t)
           :when (vis? [:cover [whole ps] kind])
           x  ps
           y  ps
           :when (and (not= x y)
                      (not (genl?-global tax x y))       ; global, per disjointness-test
                      (not (genl?-global tax y x))
                      (not (exempt? x y)))]
       [x y]))))

(defn disjoint?
  "Are types a and b provably disjoint?  True when some supertype of a and some
  *different* supertype of b are separated — by a declared `(disjoint x y)`, by both
  being members of one disjoint metatype, by both being non-genl-related proper
  specializations of one `(sibling_disjoint C)` parent, or by both being parts of one
  `partition` roster.  Every way, disjointness is
  inherited downward through genl (subtypes of disjoint types are disjoint), which
  is what the walk over both up-closures buys.

  The sibling arm is the metatype arm keyed off the genl closure rather than a
  recorded membership set: `(sibling_disjoint C)` separates C's specializations by
  being consulted, and its one added guard skips a separator pair `x`,`y` when one is
  a genl of the other — read **globally**, so a reader that cannot see a `genl` edge
  does not separate a pair the KB knows overlaps.

  The metatype arm is why no clique is stored: `(disjoint_metatype M)` separates
  M's members by being *consulted*, not by materializing a `(disjoint a b)` per
  pair.  Only metatypes still marked are consulted, so unmarking one releases every
  pair it separated in a single step.  Being consulted is also what makes the arm
  *scopable* at all — a materialized clique would have frozen each pair in whatever
  context the expansion ran from.

  The context arity scopes on three levels: the two `genls` closures walk only
  visible edges, a `(disjoint x y)` pair counts only when some supporter's context
  is visible, and the metatype arm asks the same of the mark and of each of the two
  memberships.  Every added visibility probe sits *behind* an existing cheap
  membership guard, so the negative path — the overwhelming majority, since this
  runs on every unary assert — costs what the global read costs over the (smaller)
  scoped closures.

  `context` may be an ancestor set instead: the closures and declarations read are those
  some supporter states in the set, with no belief callback (`genls-asserted-in`), so the
  read does not re-enter the supporter callback.

  Monotone on the visibility of declarations and edges: seeing more of them only adds
  witnesses.  A `siblingDisjointException` is the one read that removes one: the three
  mark arms spare the separated pair it names at a reader that sees it, so a context below
  the exception reads the pair apart and a context above it, or beside it, reads it
  separated.  An unscoped read sees every exception."
  ([tax a b] ((disjointness-test tax a nil) b))
  ([tax a b context] ((disjointness-test tax a context) b)))

;; ---- disjointness witnesses: what a clash's joint visibility rests on ----

(defn- requirement
  "The context choices a supporting-context set imposes on a witness — nil when it
  imposes none (a supporter with no recorded context is seen from everywhere, so
  the ingredient never constrains the reader)."
  [cs]
  (when-not (contains? cs nil) (not-empty cs)))

(defn- path-requirements
  "Lazy seq of per-path requirement vectors from `sub` up to `tgt` over `:fwd` —
  one element per path, each a vector of context-choice sets, one per constraining
  edge on that path.  Reflexive: `sub` = `tgt` yields the single empty vector.
  Cycle-guarded, so a stray cycle terminates."
  [rel sub tgt seen]
  (if (= sub tgt)
    (list [])
    (lazy-seq
     (mapcat (fn [nxt]
               (when-not (contains? seen nxt)
                 (let [req (requirement (get (:edge-ctxs rel) [sub nxt] #{}))]
                   (map (fn [tail] (if req (into [req] tail) tail))
                        (path-requirements rel nxt tgt (conj seen sub))))))
             (get (:fwd rel) sub)))))

(defn- requirement-choices
  "Lazy cartesian product over requirement sets: each yield is one concrete witness
  context set — one context chosen per constraining ingredient."
  [reqs]
  (if (empty? reqs)
    (list #{})
    (for [c     (first reqs)
          rest* (requirement-choices (rest reqs))]
      (conj rest* c))))

(defn- leg-witnesses
  "Lazy seq of witness context sets, one per choice of a path for each `[from to]` leg in
  `legs` and of a context per requirement: the path requirements accumulate onto `acc`,
  followed by `extra`.  The legs recurse instead of nesting one `for` binding each: every
  nested binding lengthens the AOT class file name, and eight of them pass the 255-byte
  limit of ext4 and APFS."
  [rel legs acc extra]
  (if-let [[[from to] & more] (seq legs)]
    (for [p (path-requirements rel from to #{})
          w (leg-witnesses rel more (into acc p) extra)]
      w)
    (requirement-choices (into acc extra))))

(defn disjointness-witnesses
  "Lazy seq of **witness context sets** for the provable disjointness of `a` and
  `b`: each is the supporting contexts of one complete derivation — a genl path
  from `a` up to one separated type, a path from `b` up to the other, and the
  separating declaration (a `(disjoint x y)` pair, a metatype mark plus both
  memberships, a `sibling_disjoint` mark plus the steps down to it, or a `partition` /
  `separating` roster naming both).  All four spellings are here because a caller reads
  emptiness as *not disjoint*, and one left out would make that reading disagree with
  `disjoint?` about one KB.  A reader sees the clash iff it sees every context in *some*
  witness; a supporter with no recorded context imposes nothing and never appears.

  Lazy on every level — paths, separated pairs, and per-ingredient supporter
  choices can all multiply, and a node can have exponentially many ancestor paths
  — so a consumer that finds its witness early never pays for the tail.

  No `siblingDisjointException` is read: an exemption removes a separation at the readers that see it,
  which a set of contexts to see cannot state, so a caller tests the reader it names with
  `disjoint?`.  Empty exactly when no reader separates the pair, `disjointness-test`
  reading no exemption, which is the guard a caller runs first."
  [tax a b]
  (let [t       @tax
        rel     (:genl t)
        cctxs   (:cache-ctxs t)
        req     (fn [k] (requirement (get cctxs k #{})))
        pairs   (:disjoint t)
        members (:metatype-members t)
        as      (genls-global tax a)
        bs      (genls-global tax b)]
    (concat
     (for [x as, y bs
           :when (and (not= x y) (contains? pairs #{x y}))
           w (leg-witnesses rel [[a x] [b y]] [] (keep req [[:disjoint #{x y}]]))]
       w)
     (for [m (:disjoint-metatypes t)
           :let  [ms (get members m #{})]
           :when (seq ms)
           x as, y bs
           :when (and (not= x y) (contains? ms x) (contains? ms y)
                      (not (genl?-global tax x y)) (not (genl?-global tax y x)))  ; genl-related overlap, never disjoint
           w (leg-witnesses rel [[a x] [b y]] [] (keep req [[:metatype m] [:member m x] [:member m y]]))]
       w)
     ;; the sibling-disjoint arm: `x` and `y` are non-genl-related proper specializations
     ;; of a marked parent `c`, so the derivation rests on the paths up to each separated
     ;; type, the paths making each a specialization of `c`, and the mark itself.
     (for [c (:sibling-disjoint t)
           :let  [mreq (req [:sib-disjoint c])]
           x as, y bs
           :when (and (not= x y) (not= x c) (not= y c)
                      (genl?-global tax x c) (genl?-global tax y c)
                      (not (genl?-global tax x y)) (not (genl?-global tax y x)))
           w (leg-witnesses rel [[a x] [b y] [x c] [y c]] [] (when mreq [mreq]))]
       w)
     ;; the cover arm: `(partition W P1 P2 …)` and `(separating W P1 P2 …)` separate their
     ;; parts, so the roster reads the way a metatype's member set does and the derivation
     ;; rests on the paths up to two distinct parts and the declaration naming them.  The
     ;; parts vector is the one `cover-key` normalized, so it keys the support entry as
     ;; stored.
     (for [[whole ps kind] (:partitions t)
           :let  [creq (req [:cover [whole ps] kind])
                  psx  (set ps)]
           x as, y bs
           :when (and (not= x y) (contains? psx x) (contains? psx y)
                      (not (genl?-global tax x y)) (not (genl?-global tax y x)))
           w (leg-witnesses rel [[a x] [b y]] [] (when creq [creq]))]
       w))))

;; ---- predicate properties -----------------------------------------------

(defn mark-prop
  ([tax kind pred handle] (mark-prop tax kind pred handle nil))
  ([tax kind pred handle ctx] (add-supported tax [:prop kind pred] handle ctx)))
(defn unmark-prop! [tax kind pred handle] (del-supported! tax [:prop kind pred] handle))
(def ^:private keyed-kinds
  "The property kinds that sort a sentex's arguments at the entry point — `symmetric` and
  `commutative` — and so are read from every context (`has-prop?`)."
  #{:symmetric :commutative})

(defn- keyed-entry-believed?
  "Does `context` believe a supporter of flat-cache entry `k`, each supporter read as
  visible from every context?  A permuting mark is read from every context, so only a
  `defeat` or an `except` the reader sees takes it away there (docs/canonicalization.md,
  \"A mark a reader does not believe\")."
  [tax k context]
  (let [t @tax]
    (or (not (supporter-filter-active? t))
        (let [vis? (visible-fn t)]
          (boolean (some #(vis? % context) (keys (supporters-of t k))))))))

(defn has-prop?
  "Does `pred` carry property `kind` — anywhere, or (with `context`) declared from
  a context the reader can see?

  `:symmetric` and `:commutative` are read from every context, as the store sorts a fact
  stated in a context that sees no statement of the mark — one with no `genlCx` edge, or
  one above CxUniverse, where the lifted copy sits.  With a context they answer whether
  that context believes a statement (`keyed-entry-believed?`), which a `defeat` or an
  `except` it sees takes away."
  ([tax kind pred] (contains? (get (:props @tax) kind) pred))
  ([tax kind pred context]
   (let [t @tax]
     (and (contains? (get (:props t) kind) pred)
          (or (not (scoped-context? context))
              (if (contains? keyed-kinds kind)
                (keyed-entry-believed? tax [:prop kind pred] context)
                (cache-entry-visible? tax [:prop kind pred] context)))))))
(defn props "The set of predicates carrying property `kind`." [tax kind] (get (:props @tax) kind #{}))

(defn quoting-function?
  "Is `head` declared a `quoting_function`?  Its arguments are a **mention**, held opaque
  to identity congruence (`res/representative-term` spelling mode)."
  [tax head]
  (and (symbol? head) (has-prop? tax :quoting head)))

(defn mention-marks
  "The two declarations that make a position a **mention** — a term named as syntax rather
  than one the sentence refers with — as `{:quoting #{…} :modal #{…}}`, or **nil** when the
  KB declares
  neither.  Nil is the gate: `res/representative-term` then takes the ordinary
  full-representative walk with no per-node check, and the sets are read once per walk
  rather than a taxonomy deref per compound node.

  A `quoting_function` quotes its arguments (`Quote`, `Quasiquote`).  A `modal_predicate`
  quotes the **proposition** it attributes to its agent: an attitude is opaque, so the
  merges the asker believes may not rewrite a term inside what somebody else holds true
  (docs/belief.md).  Both are opaque to *identity* congruence and both follow a `rewriteOf`
  *spelling* rename.

  Read **globally**, where `BeliefProjectionProver` reads the same `:modal` mark scoped
  from the asking context.  The two questions differ: whether a belief *projects* is a
  policy of the context granting the marker, while whether an argument is a quotation is a
  fact about the sentence — and a reader-scoped answer to the second would migrate a stored
  belief for one context while holding it for another, after which neither could retrieve
  what the other had renamed.  Same reasoning as `kb-sentex`'s global symmetry read."
  [tax]
  (let [q (props tax :quoting)
        m (props tax :modal)]
    (when (or (seq q) (seq m)) {:quoting q :modal m})))

(defn props-over
  "`p` and every **super-predicate** of it carrying property `kind` — anywhere, or (with
  `context`) declared from a context the reader can see, walking only the `genl` edges
  visible from it.  Empty when none does.

  For the properties a violation is convicted **against**, and only those.  A `genl` edge
  between predicates says the sub's tuples *are* the super's, so a clash among the sub's
  tuples is a clash among the super's: `(fatherOf a b)` beside `(fatherOf b a)` breaks
  `(asymmetric parentOf)`, and two `fatherOf` mothers for one child are two `parentOf`
  values against `(functional parentOf)`.  Read the mark off the exact functor and those
  become bypassable through a sub-predicate entry point while the *converse probe* fans down the
  same hierarchy, so which spelling arrived second would decide whether the pair is
  found.

  **Not for the generative ones.**  `transitive`, `symmetric`, `reflexive` and
  `transitiveInArg` license tuples rather than refusing them, and a licence read for a
  predicate nobody declared it of manufactures knowledge — `inherit-test`'s
  `the-licence-stays-with-the-predicate-it-names` and `provers-test`'s
  `the-walk-reads-hops-through-the-subsumption-fan` pin that, and both call `has-prop?`
  for the goal's own predicate.  The direction is what separates the two families, and it
  is also why this walks **up** where `inverses-under` walks down: an inverse recorded on
  a sub-predicate is a hop of the super, and a constraint declared of a super binds the
  sub.

  The `:props` roster is empty for the kind on nearly every KB, so the common case is one
  map read and no closure walk — the gate `inverses-under` takes on the empty `:inverse`
  map, and it is what keeps a descending read off the goal paths that ask `has-prop?` per
  goal."
  ([tax kind p] (props-over tax kind p nil))
  ([tax kind p context]
   (let [marked (get-in @tax [:props kind])]
     (if (empty? marked)
       #{}
       (into #{}
             (comp (filter marked) (filter #(has-prop? tax kind % context)))
             (if (some? context) (genls tax p context) (genls-global tax p)))))))

(defn props-over-among
  "`props-over` with no context, read off the `kind` roster's cut of `p`'s global closure
  (`genls-global-among`) rather than the closure: `memo` is a volatile map the caller
  keeps for one roster over one still taxonomy, so a caller asking it of many predicates
  pays the edges once rather than a closure per predicate."
  [tax kind p memo]
  (let [marked (get-in @tax [:props kind])]
    (if (empty? marked)
      #{}
      (into #{} (filter #(has-prop? tax kind % nil)) (genls-global-among tax p marked memo)))))

(def closure-relations
  "The two relations whose transitive closure the engine caches and answers itself —
  `genl` and `genlCx`.  They are held **out** of the generic `:transitive` prop
  machinery, so a `(transitive genl)` fact stays queryable but *inert*: it never routes
  genl to the generic closure prover, never sets `has-prop? :transitive genl`, and the
  taxonomy answers genl-transitivity from its own cache as it always has.
  `provers/transitive-predicates` and `inherit/virtual-relations` are both this set, and
  `special`'s mark ingestion reads it as the skip-set.

  Read off the declarations rather than written: `:edge` is the storage kind for a
  relation the engine closes itself, so being in this set and being cached as a closure
  are one fact rather than two lists that have to agree."
  (set (keys (pr/by-storage :edge))))

(def arg-declaration-props
  "Per argument-constraint kind, the `:props` roster its **subject** is marked under —
  `(arg parentOf 1 person)` marks `parentOf` as declaring `arg`.

  A declaration constrains the tuples of every predicate beneath the one it names, so
  reading it means asking, per super-predicate of the sentence's own functor, whether it
  declares anything at all.  Asked of the index that is one argument-root probe per
  super per assert — proportional to how deep in the type hierarchy the predicate sits,
  on the path `assert` names its dominant per-fact cost.  Marked here it is a set
  membership, which is the same trade `(arity P n)` takes one screen up and for the same
  reason: a declaration is not something to re-derive per write.

  The roster is the **global** one, so a filter built on it is a superset of what any
  context can see; the scoped retrieval it gates is what decides which declarations
  actually speak for a reader.

  Read off the declarations: the family is `predicates/:argument-constraint` and the
  keyword is each spelling's own `:prop` storage target, so a fifth constraint is
  declared once and arrives here."
  (into (sorted-map)
        (map (juxt identity pr/prop-kind))
        (pr/family :argument-constraint)))

(def functional-family-marks
  "The spellings of the **functional** mark, each with its written shape: `:mark` for
  the one-place `(functional P)`, `:mark-in-arg` for the two-place `(functionalInArg P
  n)`.  The marked predicate is argument 1 of either, which is what lets a reader that
  only wants the predicate ignore the shape entirely.

  **One roster because the family lives in two lanes and has twice been joined to only
  one** — the argument, with #52 and #54, is on `predicates/mark-families`, which is
  where a third spelling is now added and where this reads it back from.

  What a lane still owns for itself is what it does with the shape: `settle` also checks
  the argument *kinds* because its triggers come off a moved region and may be malformed,
  where `special`'s entry point is downstream of well-formedness and checks only the arity.

  Not `:props`-keyed, and that is the point of the split from `settle`'s
  `definitional-marks`: `functional` stores under the `:functional` prop where
  `functionalInArg` stores `[pred n]` pairs in the `:functional-in-arg` table, so the two
  have no common storage to be rostered by — only a common family and a common argument
  1."
  (pr/by-family :functional))

;; The supporters behind a flat-cache entry, read back.  A consumer that *justifies*
;; something on a declaration needs the declaring sentexes as antecedents, and reading
;; them here beats re-querying the store for a sentence the cache was built from.
;; Every stored supporter is returned, believed or not: a justification's antecedents
;; are labelled by the JTMS, so handing it a defeated supporter is how a derivation
;; revives by itself when that supporter does.
(defn- cache-supporters [tax k] (into #{} (keys (supporters-of @tax k))))
(defn prop-supporters
  "The **handles** of the sentexes declaring property `kind` of `pred`, as a set —
  every one of them, defeated members included, which is what lets a derivation resting
  on one revive by itself when that supporter does.

  Handles, not sentexes: the callers put these straight into a justification's
  antecedents, and a set has no order for such a list to inherit."
  [tax kind pred] (cache-supporters tax [:prop kind pred]))

(defn prop-supporter-contexts
  "`prop-supporters` with the context each was stated in, as `{handle context}` — for a
  caller that names only the statements its reader sees."
  [tax kind pred] (supporters-of @tax [:prop kind pred]))

(defn add-inverse
  ([tax p q handle] (add-inverse tax p q handle nil))
  ([tax p q handle ctx] (add-supported tax (inverse-key p q) handle ctx)))
(defn del-inverse! [tax p q handle] (del-supported! tax (inverse-key p q) handle))
(defn add-arity
  ([tax pred n handle] (add-arity tax pred n handle nil))
  ([tax pred n handle ctx] (add-supported tax [:arity pred n] handle ctx)))
(defn del-arity! [tax pred n handle] (del-supported! tax [:arity pred n] handle))

(def exact-arity-classes
  "What each exact-arity class membership says the arity is: `sx/exact-arity-classes`,
  read here by `kb/relation?` and the quality and integrity passes."
  sx/exact-arity-classes)

(defn declared-arity
  "The arity `pred` is declared with, or nil — anywhere, or (with `context`) declared
  from a context the reader can see.

  `(arity P n)` is a declaration the engine interprets, so it is cached here beside
  `transitive` and `inverse` rather than re-queried: the arity check runs on **every**
  assertion, and answering it from the index walked 16 candidate postings per
  assertion — 13.3M over an OpenCyc load, nearly all of them finding nothing, and 22%
  of the whole load's allocation.

  Nil when the KB has been told **two different arities** for one predicate.  That is
  not the same as being told nothing, but the answer to \"which arity does this
  predicate have\" is genuinely unsettled, and refusing an assertion on whichever of
  two contradictory declarations was found first would be arbitrary — open-world is
  the same stance the check takes toward a predicate nobody has declared.

  Scoped, that uniqueness is asked of what the reader can **see** rather than of the
  whole KB: two contexts declaring different arities leave each reader with one answer,
  and only a reader seeing both has none.  Testing uniqueness first and filtering after
  would instead let a declaration a reader cannot see suppress the one it can."
  ([tax pred] (declared-arity tax pred nil))
  ([tax pred context]
   (let [ns'  (get-in @tax [:arity pred])
         seen (if (scoped-context? context)
                (filterv #(cache-entry-visible? tax [:arity pred %] context) ns')
                (vec ns'))]
     (when (= 1 (count seen)) (first seen)))))

(defn add-functional-in-arg
  ([tax pred n handle] (add-functional-in-arg tax pred n handle nil))
  ([tax pred n handle ctx] (add-supported tax [:functional-in-arg pred n] handle ctx)))
(defn del-functional-in-arg! [tax pred n handle]
  (del-supported! tax [:functional-in-arg pred n] handle))

(defn functional-in-arg-supporters
  "The **handles** of the sentexes declaring `(functionalInArg pred n)`, as a set.

  The `functionalInArg` twin of `prop-supporters`, and it keys on the *pair*: a merge
  derived under `(functionalInArg P 3)` rests on the declarations naming position 3, not
  on every `functionalInArg` declaration `P` happens to carry.  Defeated members
  included, for the reason `prop-supporters` gives."
  [tax pred n] (cache-supporters tax [:functional-in-arg pred n]))

(defn functional-in-arg-over
  "`[pred n]` pairs — `p` and every **super-predicate** of it carrying a
  `(functionalInArg pred n)` declaration, anywhere or (with `context`) declared from a
  context the reader can see.  Empty when none does.

  This is `props-over`'s shape and it walks **up** for `props-over`'s reason: the
  constraint refuses tuples rather than licensing them, so a declaration on a super
  binds the sub.  `(functionalInArg parentOf 2)` has to convict two `fatherOf` mothers
  exactly as `(functional parentOf)` does, or the generalization would be weaker than
  the arity-2 case it generalizes — which the regression half of
  `functional-in-arg-test` forbids.

  Storage is `arity`'s rather than `:props`': the declaration carries an integer, and a
  `:props` roster is a set of predicates with nowhere to put one.  `::prop-kind` is
  therefore **not** extended — `arity` is not in it either, and the spec is the `:prop`
  storage targets read off the declarations, which a kind derived from `n` has none of.

  Unlike `declared-arity` this does **not** collapse to a single `n`.  Two arities for
  one predicate are a genuine ambiguity about which one it has; two functional positions
  are two independent constraints, both of which hold, and a KB is free to say
  `(functionalInArg P 2)` and `(functionalInArg P 3)` of the same predicate.  Visibility
  is asked per `[pred n]` entry, which is what scopes a declaration to the vantage that
  can see it without any machinery of its own."
  ([tax p] (functional-in-arg-over tax p nil))
  ([tax p context]
   (let [table (get @tax :functional-in-arg {})]
     (if (empty? table)
       #{}
       (into #{}
             (comp (filter table)
                   (mapcat (fn [q]
                             (for [n     (get table q)
                                   :when (or (not (scoped-context? context))
                                             (cache-entry-visible?
                                              tax [:functional-in-arg q n] context))]
                               [q n]))))
             (if (some? context) (genls tax p context) (genls-global tax p)))))))

(defn functional-in-arg-predicates
  "Every predicate carrying **any** `functionalInArg` mark, at any position, as a set —
  the twin of `props` for a table keyed `pred -> #{n1 n2 …}` rather than membership
  alone, and read the same ungated way: one map read, no closure walk.

  `functional-in-arg-over` answers a different question and cannot stand in for this
  one — it walks *up* from one probe predicate to the marks that reach it, so there is
  no predicate to start it from when the question is the reverse: which predicates carry
  the mark at all, with no probe in hand yet.  `special/equate-under-context-edge` is
  exactly that caller — a `genlCx` edge names two contexts, not a predicate, and needs
  the whole marked roster to walk each one's stored extent, the same way it already
  reads `props :functional` for the arity-2 mark."
  [tax] (set (keys (get @tax :functional-in-arg {}))))

(defn add-commuting
  "Install a commutativity group on `pred`.  `group` is `[:rest f]` or `[:args [p1 p2 …]]`
  — the two written spellings reduced to the one descriptor `commuting-components` reads."
  ([tax pred group handle] (add-commuting tax pred group handle nil))
  ([tax pred group handle ctx] (add-supported tax [:commuting pred group] handle ctx)))

(defn del-commuting! [tax pred group handle] (del-supported! tax [:commuting pred group] handle))

(defn commuting-supporters
  "The handles of the sentexes installing commuting `group` on `pred`, as a set, defeated
  members included — `prop-supporters` for the `:commuting` table."
  [tax pred group] (cache-supporters tax [:commuting pred group]))

(defn commuting-groups
  "The commutativity group descriptors declared of `pred` itself, as a set.  Empty when
  none are, which is the answer for all but a handful of predicates.

  **The exact functor, and global**, unlike `functional-in-arg-over`, which walks up.
  Two separate reasons, and they point the same way:

  - A commutativity mark *canonicalizes* where the argument constraints *convict*.  The
    store keys a fact by the sort every stored mark gives it (`res/kb-sentex`); a reader
    that does not believe a group reads through `res/spelling-planner`.
  - A `genl` edge below a commutative predicate does not make the sub-predicate
    commutative, exactly as it does not make it symmetric (`integrate/commute-existing`,
    `constraint_descension_test`).  A row re-spelled at a sub-predicate would be one the
    assert entry point stores the other way round on the very next write.

  One map read, no closure walk, so an unmarked predicate pays a single miss — which is
  what lets this sit on the canonicalization path every assert runs."
  [tax pred] (get (:commuting @tax) pred #{}))

(defn commuting-predicates-among
  "The members of `specs` carrying any commutativity group, as a set, or **nil** when none
  do — `commuting-groups` mirrored for a caller holding a whole spec closure rather than
  one probe predicate.

  **Driven from the table, and in one pass.**  The marked predicates are a handful where a
  broad functor's spec closure is the whole type hierarchy, so the membership test runs
  the small side against the large one — `props`' own trade, and `matches-hierarchical`
  makes it for `symmetric` a few lines above the caller.  Iterating the entries rather
  than the key set is what keeps a retrieval off an allocation: the key set would be built
  and thrown away once per matched literal, and on a KB carrying core.txt's bridge every
  symmetric predicate is in this table.

  Nil rather than an empty set, so the caller's gate is a `nil?` and the common answer
  allocates nothing at all."
  [tax specs]
  (let [table (get @tax :commuting {})]
    (when (seq table)
      (not-empty (into #{} (comp (map key) (filter #(contains? specs %))) table)))))

(defn commuting-declared?
  "Does any predicate carry a commutativity group?  The table-wide gate a caller opens on
  before it builds the spec closure `commuting-predicates-among` would be asked over."
  [tax]
  (boolean (seq (get @tax :commuting))))

(defn functional-family-declared?
  "Does the taxonomy carry a functional-family mark of **either** spelling — the global,
  unscoped gate every merge entry point of that family opens on, before it reads any extent?

  One predicate rather than the `or` written at each entry point, because the two spellings
  store in different places (`props :functional` and the `:functional-in-arg` table) and
  an entry point that asks only the first is closed to the generalized mark while reporting
  itself as free-for-a-KB-that-declares-nothing.  That is not hypothetical: it is what
  `equate-under-edge` did, so a `genl` edge arriving last under `(functionalInArg P 2)`
  merged nothing where the same edge under `(functional P)` merged — the arity-2
  behaviour the generalization is not allowed to move.  See
  `functional-family-marks` for the spelling roster this is the storage half of.

  Two set-emptiness reads and no walk, the `or` short-circuiting on the commoner
  spelling, which is what lets it sit in front of every extent sweep."
  [tax]
  (boolean (or (seq (props tax :functional))
               (seq (functional-in-arg-predicates tax)))))

(defn inverses-of
  "**Every** predicate declared inverse to `p`, as a set — anywhere, or (with `context`)
  the ones declared from a context the reader can see.  Empty when none is.

  Nearly every predicate has none, so a caller probing per partner does one map read and
  no work; the set has more than one member only where a KB declared `(inverse P Q)` and
  `(inverse P R)`, which nothing refuses.  This is the reader a *step relation* wants —
  a hop somebody recorded on any declared partner is a hop, and answering off one of them
  would leave the others silently off the graph."
  ([tax p] (get-in @tax [:inverse p] #{}))
  ([tax p context]
   (let [qs (get-in @tax [:inverse p] #{})]
     ;; the empty case first, and it is the overwhelmingly common one: a transitive walk
     ;; asks this per node, so reaching `closure-of` before finding out there is no
     ;; partner would charge every ordinary walk a genlCx closure lookup per hop for
     ;; an answer that is empty either way
     (if (or (empty? qs) (not (scoped-context? context)))
       qs
       (into #{} (filter #(cache-entry-visible? tax (inverse-key p %) context)) qs)))))

(defn inverse-of
  "The declared inverse of `p`, or nil — anywhere, or (with `context`) declared
  from a context the reader can see.

  **One partner, chosen by content.**  A predicate may carry several declared inverses,
  and this answers the lexicographically smallest of them so the answer is a function of
  the knowledge rather than of the order it arrived in — the tie-break every other
  many-to-one read here takes, and for the reason the README gives.  A caller that must
  see all of them asks `inverses-of`; this one exists for the callers that want *a*
  partner (the applicability tests, the vocabulary reports) and are not walking a graph."
  ([tax p] (first (sort (inverses-of tax p))))
  ([tax p context] (first (sort (inverses-of tax p context)))))

(defn inverses-under
  "Every predicate declared inverse to `p` **or to a sub-predicate of `p`**, as a set —
  anywhere, or (with `context`) declared from a context the reader can see, walking
  only the `genl` edges visible from it.

  A hop somebody recorded on a partner of a sub-predicate is a hop of the super too:
  `(Q y x)` under `(inverse P' Q)` is `(P' x y)`, and a `P'` tuple is a `P` tuple by
  subsumption, however it is spelled.  A step relation or a swapped-goal delegate
  reading only `p`'s own partners leaves those edges silently off the graph — a claim
  then answers under the sub-predicate and not under its super, which no reading of
  `genl` admits.

  The `:inverse` map is empty for nearly every KB, so the common case is one map read
  and no closure walk; the spec closure is consulted only when some inverse exists."
  ([tax p] (inverses-under tax p nil))
  ([tax p context]
   (if (empty? (get @tax :inverse))
     #{}
     (let [ps  (if (some? context) (specs tax p context) (specs-global tax p))
           inv (if (some? context) #(inverses-of tax % context) #(inverses-of tax %))]
       (into #{} (mapcat inv) ps)))))

;; ---- genlInverse: binary genl with the arguments swapped ----------------
;;
;; `(genlInverse P Q)` says a `(P x y)` tuple is a `(Q y x)` tuple: binary `genl` with
;; arguments 1 and 2 swapped.  The edges are a flat-cache entry, held both ways round —
;; `:genl-inverse-down` maps `Q` to the `P`s below it and `:genl-inverse-up` maps `P` to
;; the `Q`s above it — and they are never edges of the `genl` relation, whose closure every
;; type read, placement and disjointness check walks.  What reads them is the signed
;; closure below, which the matching fan-out takes in place of `specs` / `genls`: it walks
;; `genl` edges keeping a parity bit and crosses a `genlInverse` edge flipping it, so a
;; predicate reached over an odd number of `genlInverse` edges is read with its arguments
;; swapped and one reached over an even number is read as a `genl` spec is.

(defn genl-inverse-key
  "The flat-cache key a `(genlInverse p q)` declaration installs."
  [p q]
  [:genl-inverse p q])

(defn add-genl-inverse
  ([tax p q handle] (add-genl-inverse tax p q handle nil))
  ([tax p q handle ctx] (add-supported tax (genl-inverse-key p q) handle ctx)))
(defn del-genl-inverse! [tax p q handle] (del-supported! tax (genl-inverse-key p q) handle))

(defn genl-inverse-free?
  "True when no `genlInverse` edge is installed — one map read, and the answer for nearly
  every KB.  The signed closure is the plain `genl` closure then."
  [tax]
  (empty? (get @tax :genl-inverse-up)))

(defn- genl-inverse-hop
  "The predicates one `genlInverse` edge away from `p` — `dir` `:down` reads the specs
  `x` of a `(genlInverse x p)`, `:up` the generals `y` of a `(genlInverse p y)` — whose
  edge is visible from `context` (any edge, for an unscoped one)."
  [tax dir p context]
  (let [xs (get-in @tax [(if (= dir :down) :genl-inverse-down :genl-inverse-up) p] #{})]
    (if (or (empty? xs) (not (scoped-context? context)))
      xs
      (into #{} (filter #(cache-entry-visible?
                          tax (if (= dir :down) (genl-inverse-key % p) (genl-inverse-key p %))
                          context))
            xs))))

(defn signed-closure
  "`[straight swapped]`: the predicates `p`'s matching fan reaches through the `genl` and
  `genlInverse` edges visible from `context` — `dir` `:down` the specs, `:up` the
  generals.  `straight` holds those reached over an even number of `genlInverse` edges,
  read with their arguments as written; `swapped` those reached over an odd number, read
  with arguments 1 and 2 exchanged.  A predicate reached both ways is in both.

  With no `genlInverse` edge installed this is `[(specs tax p context) #{}]` (or `genls`
  for `:up`), the same set object the plain read answers, so a KB declaring none reads
  the fan it always read.  Otherwise a walk over `[predicate parity]` states, each state
  taking the `genl` closure of its predicate and crossing every visible `genlInverse` edge
  out of a member of it with the parity flipped, so a chain composes however its `genl`
  and `genlInverse` edges alternate and terminates on a cycle of either."
  [tax dir p context]
  (let [close (if (= dir :down) #(specs tax % context) #(genls tax % context))]
    (if (genl-inverse-free? tax)
      [(close p) #{}]
      (loop [todo [[p false]] seen #{[p false]} straight #{} swapped #{}]
        (if-let [[n odd] (peek todo)]
          (let [cl   (close n)
                nxt  (into [] (comp (mapcat (fn [s] (genl-inverse-hop tax dir s context)))
                                    (distinct)
                                    (map (fn [x] [x (not odd)]))
                                    (remove seen))
                           cl)]
            (recur (into (pop todo) nxt)
                   (into seen nxt)
                   (if odd straight (into straight cl))
                   (if odd (into swapped cl) swapped)))
          [straight swapped])))))

(defn- visible-flat-supporters
  "The supporters of flat-cache key `k` a reader at `context` can use, as `[handle ctx]`
  pairs — every stored one for an unscoped read, else those `cache-entry-visible?` would
  admit."
  [tax t k context]
  (let [sup (supporters-of t k)]
    (cond
      (not (scoped-context? context)) (vec sup)
      (supporter-filter-active? t)
      (let [scope {:contexts (context-up tax context) :context context
                   :supporter-visible? (visible-fn t)}]
        (filterv (fn [[h c]] (scope-admits-supporter? scope h c)) sup))
      :else
      (let [up (closure-of tax :genlCx :fwd context)]
        (filterv (fn [[_ c]] (or (nil? c) (contains? up c))) sup)))))

(defn- genl-inverse-witness
  "A `[handle ctx]` supporter for the `genlInverse` edge `p → q` a reader at `context`
  sees: the strongest class's most general, as `strongest-edge-supporter` picks for a
  `genl` edge; nil when none is visible."
  [tax p q context supporter-class]
  (let [cands (visible-flat-supporters tax @tax (genl-inverse-key p q) context)]
    (when (seq cands)
      (most-general-of
       tax (if supporter-class
             (let [top (top-supporter-class cands supporter-class)]
               (filterv (fn [[h _]] (= top (or (supporter-class h) :default))) cands))
             cands)))))

(defn signed-reach-support
  "A witness for `sub` reaching `super` through the signed closure with parity `swapped?`
  — the `[handle ctx]` supporters of one path's `genl` and `genlInverse` edges, as
  `reach-support` names a `genl` path's — or nil when `context` sees no such path.

  A pair the `genl` closure relates with `swapped?` false is `reach-support`'s answer
  unchanged.  Otherwise the path is the one with the fewest `genlInverse` edges, found
  breadth-first over `[predicate parity]` states in name order, each `genl` stretch of it
  witnessed by `reach-support` (widest-bottleneck under `supporter-class`, as there)."
  [tax sub super swapped? context supporter-class]
  (if (and (not swapped?) (contains? (genls tax sub context) super))
    (reach-support tax :genl sub super context supporter-class)
    (when-not (genl-inverse-free? tax)
      (let [sorted #(nm/sort-by-content-key nm/print-key compare %)
            start  [sub false]
            goal?  (fn [[n odd]] (and (= odd (boolean swapped?))
                                      (contains? (genls tax n context) super)))
            path   (loop [q (conj clojure.lang.PersistentQueue/EMPTY start) parent {start nil}]
                     (when-let [[n odd :as st] (peek q)]
                       (if (goal? st)
                         ;; walk the parents back: each hop is [from-node x y], the `genl`
                         ;; stretch from-node →* x then the `genlInverse` edge x → y
                         (loop [s st acc ()]
                           (if-let [[prev x y] (get parent s)]
                             (recur prev (cons [(first prev) x y] acc))
                             [acc n]))
                         (let [[q parent]
                               (reduce (fn [[q parent :as acc] [x y]]
                                         (let [s' [y (not odd)]]
                                           (if (contains? parent s')
                                             acc
                                             [(conj q s') (assoc parent s' [st x y])])))
                                       [(pop q) parent]
                                       (for [x (sorted (genls tax n context))
                                             y (sorted (genl-inverse-hop tax :up x context))]
                                         [x y]))]
                           (recur q parent)))))]
        (when-let [[hops last-node] path]
          (reduce (fn [acc seg]
                    (if (nil? seg) (reduced nil) (into acc seg)))
                  []
                  (concat
                   (mapcat (fn [[from x y]]
                             [(reach-support tax :genl from x context supporter-class)
                              (when-let [w (genl-inverse-witness tax x y context supporter-class)] [w])])
                           hops)
                   [(reach-support tax :genl last-node super context supporter-class)])))))))

;; ---- what the taxonomy holds, declared ----------------------------------
;;
;; Two structures with two different bounds, which is why they are two rows and not one.
;; The closures — global and scoped, and the contexts each rests on — are one weighted
;; LRU, bounded by the terms it holds (`closure-memo-limit`, through the cache profile, so
;; the memory guard shrinks it).  The visibility index is bounded by the context census,
;; never by the read count.

(caches/register-cache
 {:cache    :taxonomy-closures
  :label    "Taxonomy closures"
  :scope    :kb
  :unit     "closure terms"
  :limit    (caches/limit-thunk :taxonomy-closures closure-memo-limit)
  :counters :kb
  :note     (str "The reflexive-transitive reach sets the taxonomy has walked, up and "
                 "down, global and scoped to what one context sees, weighed by the terms "
                 "each holds. Retired by a genl or genlCx edge changing, which moves the "
                 "generation they are keyed on; past the bound, and under memory "
                 "pressure, the least recently used go first.")
  :read     (fn [kb] (let [lru (some-> (reasoning/taxonomy kb) deref :closure-lru)
                           ^java.util.concurrent.atomic.AtomicLongArray w (:walks lru)]
                       (cond-> {:entries (some-> lru caches/lru-weight)}
                         w (assoc :builds (.get w 0) :fallbacks (.get w 1)))))
  :clear    (fn [kb] (or (some-> (reasoning/taxonomy kb) deref :closure-lru caches/lru-clear!)
                         0))
  :trim     (fn [kb target]
              (or (some-> (reasoning/taxonomy kb) deref :closure-lru (caches/lru-trim! target))
                  0))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(defn- relation-value
  "Relation `r`'s map in `kb`'s taxonomy less its moves (J5)."
  [kb r]
  (-> (caches/value-at kb [:taxonomy r]) (dissoc :moves :move-gen)))

(def ^:private flat-keys
  [:disjoint :disjoint-index :disjoint-metatypes :metatype-members :sibling-disjoint
   :sib-exception-index :covers :cover-parts :partitions :props :inverse :genl-inverse-down :genl-inverse-up :arity
   :functional-in-arg :commuting :cache-dirty :cache-ctxs])

(caches/register-derived
 {:id :T1 :label "genl and genlCx relations" :kind :index :keyed-by :node
  :holds-content? false
  :reads [:records :M1]
  :retired-by {:edge :K :edge-belief :K :settle-exit :K :recover :R :image-install :R}
  :computed :write :imaged? :taxonomy
  :at [[:taxonomy :genl] [:taxonomy :genlCx] [:taxonomy :epoch]]
  :value (fn [kb] [(relation-value kb :genl) (relation-value kb :genlCx)
                   (caches/value-at kb [:taxonomy :epoch])])
  :note "the active edges with their believed contexts, closure adjacency, depths and components; `:gen` moves at every edge change, and `clear-relations!` sets it to 0 and moves `:epoch`"})

(caches/register-derived
 {:id :T2 :label "Flat declaration caches" :kind :index :keyed-by :value
  :holds-content? false
  :reads [:records :M1]
  :retired-by {:declared :K :edge-belief :K :recover :R :image-install :R}
  :computed :write :imaged? :taxonomy :at (mapv #(vector :taxonomy %) flat-keys)
  :value (fn [kb] (select-keys (caches/value-at kb [:taxonomy]) flat-keys))
  :note "disjointness, covers, partitions, predicate properties, inverses, arities, functional arguments and commuting pairs, with their contexts"})

(caches/register-cache
 {:cache    :taxonomy-supporters
  :label    "Taxonomy supporters"
  :scope    :kb
  :unit     "taxonomy keys and handles"
  :limit    (caches/limit-thunk :taxonomy-supporters supporter-cache-limit)
  :counters nil
  :note     (str "The stored supporters of the taxonomy keys and the keys of the handles the "
                 "belief reconcile has read, from the index's supporter families. A writer "
                 "drops the entries its post moves; past the bound the cache is cleared "
                 "wholesale, and recover's reconcile fills it as it reads.")
  :read     (fn [kb] {:entries (some-> (reasoning/taxonomy kb) deref :supporters
                                       (as-> c (+ (count (:by-key c)) (count (:by-handle c)))))})
  :clear    (fn [kb] (if-let [tax (reasoning/taxonomy kb)]
                       (let [c (:supporters @tax)]
                         (swap! tax assoc :supporters empty-supporters)
                         (+ (count (:by-key c)) (count (:by-handle c))))
                       0))})

(caches/register-derived
 {:id :T11 :label "Taxonomy supporters" :cache :taxonomy-supporters :kind :cache :keyed-by :value
  :holds-content? false
  :reads [:index]
  :retired-by {:edge :K :declared :K :edge-belief :K :recover :W :caches-cleared :W}
  :computed :read :imaged? false :at [[:taxonomy :supporters]]
  :note "`{:by-key {k {handle ctx}} :by-handle {handle #{k}}}` over the supporter families; a writer drops the entries its post moves, the settle's reconcile fills what it reads, and past the bound it is cleared"})

(caches/register-derived
 {:id :T3 :label "Equality partition" :kind :index :keyed-by :term :reads [:records :M1]
  :holds-content? false
  :retired-by {:equality :K :edge-belief :K :recover :R :image-install :R}
  :computed :write :imaged? :taxonomy :at [[:taxonomy :equality]]
  :value (fn [kb] (dissoc (caches/value-at kb [:taxonomy :equality]) :moved :believed-again))
  :note "the classes of `rewriteOf`, `sameAs` and `equals`: a union at an add, the class rebuilt at a delete"})

(caches/register-derived
 {:id :T4 :label "Rewrite rules" :kind :index :keyed-by :handle :reads [:records :M1]
  :holds-content? false
  :retired-by {:integrated :K :removed :K :edge-belief :K :recover :R :image-install :R}
  :computed :write :imaged? :taxonomy
  :at [[:taxonomy :rewrite-support] [:taxonomy :rewrite-active] [:taxonomy :rewrite-order]]
  :value (fn [kb] (let [t (caches/value-at kb [:taxonomy])]
                    {:support (:rewrite-support t) :active (:rewrite-active t)
                     :order   (some-> (:rewrite-order t) deref)}))
  :note "the equations by handle and the active ones; `:rewrite-order` is one slot compared by identity against `:rewrite-active`"})

(caches/register-derived
 {:id :T5 :label "Taxonomy closures" :cache :taxonomy-closures :kind :cache :keyed-by :node
  :holds-content? false
  :reads [:T1 :M1]
  :retired-by (merge (caches/on-every :G*) {:edge :G :edge-belief :G :recover :W :caches-cleared :W})
  :computed :read :imaged? false :at [[:taxonomy :closure-lru]]
  :value (fn [kb] (when-let [^java.util.LinkedHashMap m (:map (caches/value-at kb [:taxonomy :closure-lru]))]
                    (locking m (into {} m))))
  :live (fn [kb] (let [t @(reasoning/taxonomy kb)
                       ^java.util.LinkedHashMap m (:map (:closure-lru t))]
                   (count (filter (fn [k] (and (vector? k)
                                               (= (nth k 1 nil) (:gen (get t (nth k 0 nil))))))
                                  (locking m (vec (.keySet m)))))))
  :note "reach sets, needs-sets, `:asserted-in`, `:reaches`, `:path` and separable entries keyed `[rel gen …]`: a generation bump orphans the keys, and the LRU ages them out; a scope that reads supporter belief carries the change clock, so any write orphans its entries"})

(caches/register-derived
 {:id :T7 :label "Closure filter memo" :kind :cache :keyed-by :context :reads [:T1 :M1 :index]
  :holds-content? false
  :retired-by (assoc (caches/on-every :G*) :recover :W)
  :computed :read :imaged? false :at [[:taxonomy :closure-memo]]
  :value (fn [kb] (some-> (caches/value-at kb [:taxonomy :closure-memo]) deref))
  :note "per relation, whether the supporter filter is active and the down-closure by context and reading, under the relation generation and stamped by the change clock"})

(caches/register-derived
 {:id :T10 :label "Taxonomy pass caches" :kind :pass :keyed-by :node :reads [:T1 :M1]
  :holds-content? false
  :retired-by {} :computed :pass :imaged? false
  :note "`*visible-neighbours-cache*`, bound for one reading pass (`with-neighbours`): the filtered and sorted neighbours and edge supporters the walks read (`pass-held`); `chain/*witnesses*`, the witnesses and supporter classes one `place-nogoods!` reads, answered while the change clock holds"})

(caches/register-derived
 {:id :J4 :label "Flat context moves" :kind :journal :keyed-by :value :reads [:T2]
  :holds-content? false
  :retired-by {:declared :K :edge-belief :K :recover :R}
  :computed :write :imaged? false :at [[:taxonomy :cache-moves]]
  :note "the flat keys whose contexts moved, by position; the discovery memo keeps its position"})

(caches/register-derived
 {:id :J5 :label "Relation moves" :kind :journal :keyed-by :node :reads [:T1]
  :holds-content? false
  :retired-by {:edge :K :edge-belief :K :recover :R :image-install :R}
  :computed :write :imaged? :taxonomy
  :at [[:taxonomy :genl :moves] [:taxonomy :genl :move-gen]
       [:taxonomy :genlCx :moves] [:taxonomy :genlCx :move-gen]]
  :note "`{gen #{node}}` and `{node gen}` per relation, which `moves-since` reads (the `genlCx` lower ends for the settle's context-move drain); a reader whose generation is older than the first kept reads whole"})

(caches/register-derived
 {:id :Q5 :label "Equality moves" :kind :queue :keyed-by :term :reads [:T3]
  :holds-content? false
  :retired-by {:equality :K :edge-belief :K :settle-exit :Q :settle-pass :Q :recover :R
               :image-install :R}
  :computed :write :imaged? :taxonomy
  :at [[:taxonomy :equality :moved] [:taxonomy :equality :believed-again]]
  :note "the class members moved per reader and the handles believed again; `take-equality-moves!` and `take-believed-again!` drain them"})
