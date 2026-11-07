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
            [vaelii.impl.graph :as graph]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.progress :as progress]
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

(defn- reach
  "Reflexive-transitive reachable set from `start` over adjacency `adj`: `graph/reach-all` from
  one node."
  [start adj]
  (graph/reach-all [start] adj))

(defn- walk-hits?
  "Depth-first walk from `start` over `(nbrs node)`, true once `(hit? neighbours)` holds
  of some visited node's neighbour collection. A neighbour enters the walk when `keep?`
  (nil admits every one) holds of it and it is unvisited; the walk never sorts."
  [start nbrs hit? keep?]
  (loop [seen #{start}, stack [start]]
    (if-let [n (peek stack)]
      (let [ns (nbrs n)]
        (or (boolean (hit? ns))
            (let [fresh (into [] (cond->> (remove seen ns) keep? (filter keep?)))]
              (recur (into seen fresh) (into (pop stack) fresh)))))
      false)))

(defn- reachable?
  "Is `tgt` in the reflexive-transitive reach of `src` over adjacency map `adj`, given
  topological potentials `depth` and the component map `scc`?  `depth` is a potential over
  the condensation: `edge x->y` implies `depth[x] >= depth[y]`, strictly across
  components.  `scc` maps a node of a non-trivial component to its representative, and is
  empty for an acyclic relation.  The same component answers true; `depth[src] <=
  depth[tgt]` across components answers false; the walk prunes neighbours below `tgt`'s
  depth.  A missing depth is `-1`.  A nil `depth` (a `:loose?` relation, see `local-lift`)
  drops the pruning and walks `src`'s whole reach: the same answer, at much higher cost.
  See docs/taxonomy.md, \"What a batch does to the depth potential\"."
  ([src tgt adj depth] (reachable? src tgt adj depth nil))
  ([src tgt adj depth scc]
   (let [ctgt (get scc tgt)]
     (or (= src tgt)
         (and (some? ctgt) (= ctgt (get scc src)))
         (let [nbrs #(get adj %)
               hit? #(contains? % tgt)]
           (if (nil? depth)
             (walk-hits? src nbrs hit? nil)
             (let [dt (get depth tgt)]
               (and (some? dt)
                    (> (get depth src -1) dt)
                    (walk-hits? src nbrs
                                (fn [ns] (or (contains? ns tgt)
                                             (and (some? ctgt) (some #(= ctgt (get scc %)) ns))))
                                #(> (get depth % -1) dt))))))))))

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
              keep? #(when-some [d (get depth %)] (< (long d) (long ds)))]
          (and (or (nil? depth)
                   (and (some? ds) (> (long ds) (long (get depth tgt Long/MAX_VALUE)))))
               (walk-hits? tgt #(get radj %)
                           (fn [ns] (or (contains? ns src)
                                        (and (some? csrc) (some #(= csrc (get scc %)) ns))))
                           (when-not (nil? depth) keep?)))))))

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

;; A relation's supporters are held in the index's supporter families, keyed by the edge
;; (`[:genl a b]`) and by the handle (`[:tax-installs h]`); `:supporters` caches what the
;; reconcile reads, so `refresh-beliefs` reads the edges a settle could have moved off
;; the moved region (`moved-keys`).  `:dirty` names the shared edges the belief-blind
;; writers (`add-edge`, `del-edge`) left with a superset `:edge-ctxs`, which the next
;; reconcile narrows.  `:edge-ctxs {[a b] #{ctx}}` holds the supporting contexts of each
;; active edge (nil marks a supporter with no recorded context, which constrains
;; everywhere); `:gen` bumps whenever an entry moves.  `:depth` is a potential over the
;; condensation and `:scc` maps a node of a non-trivial component to its representative
;; (`term-min`, content-keyed); `:scc-members` is its inverse.  See docs/taxonomy.md.
(defn- empty-relation []
  {:dirty #{} :edges #{} :edge-ctxs {}
   :fwd {} :rev {} :nodes #{} :depth {} :scc {} :scc-members {} :gen 0
   ;; `note-move`'s log, and `note-shrink`'s of the ends that lost an edge or moved its
   ;; supporting contexts
   :moves (sorted-map) :move-gen {} :shrinks (sorted-map) :shrink-gen {}
   ;; `note-grow`'s log of the edges that entered the active set
   :grows (sorted-map) :grow-gen {}})

;; The equality partition, defined here only so `create-taxonomy` can name it; its
;; machinery is the "equality" section further down.
(defn- empty-equality []
  {:support {} :handles #{} :handle-edge {} :out #{} :edges #{} :edge-idx {} :edge-prefs {}
   :class {} :members {}})

(def closure-memo-limit
  "The most terms, summed over the closures it holds, a taxonomy's closure cache keeps in
  any KB: one term per 256 bytes of the JVM's maximum heap.  A closure is a persistent
  set: about 24 bytes a term held alone, and about 1 byte a term built on its parent's
  set (`reach-by-parents`), so the bound holds under a tenth of the heap.  It is a bound
  rather than the vocabulary because a large import can hold millions of types with
  closures of hundreds to thousands, and an unbounded memo of every type's supertypes
  grows with that product.  `closure-bound` scales it down to one taxonomy's size."
  (quot (.maxMemory (Runtime/getRuntime)) 256))

(def ^:private closure-terms-per-node
  "Closure terms a taxonomy's cache holds per node of its `genl` and `genlCx` relations.
  See docs/taxonomy.md for the starter's measurement."
  256)

(def ^:private closure-terms-floor
  "The fewest closure terms a taxonomy's cache holds, however few nodes it has."
  65536)

(defn- relation-nodes
  "How many nodes taxonomy state `t`'s `genl` and `genlCx` relations hold."
  ^long [t]
  (+ (count (get-in t [:genl :nodes])) (count (get-in t [:genlCx :nodes]))))

(defn- closure-bound
  "The weight a closure cache over `nodes` relation nodes holds before it evicts the
  least recently used: `closure-terms-per-node` a node, at least `closure-terms-floor`
  and at most `closure-memo-limit`, through the cache profile."
  [^long nodes]
  (caches/limit-of :taxonomy-closures
                   (min closure-memo-limit
                        (max closure-terms-floor (* closure-terms-per-node nodes)))))

(defn- closure-lru
  "A taxonomy's empty closure cache over taxonomy state `t`: weighted by the terms each
  closure holds (a closure needs set by its contexts, a flag by one), and bounded by
  `closure-bound` over the node count in `:nodes`, which `create-taxonomy`'s watch
  keeps current.  A put past the bound evicts from the cold end, where the closures an
  edge change retired sit."
  ([] (closure-lru nil))
  ([t]
   (let [nodes (java.util.concurrent.atomic.AtomicLong. (relation-nodes t))]
     (assoc (caches/weighted-lru #(closure-bound (.get nodes))
                                 (fn [v] (inc (if (coll? v) (count v) 0))))
            :nodes nodes
            ;; the up-closures `closure-of` built from their parents' (`reach-by-parents`),
            ;; and those that fell back to a walk: a parent evicted mid-build, or a cycle
            ;; `:scc` has not recorded
            :walks (java.util.concurrent.atomic.AtomicLongArray. 2)))))

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

;; `:supporters` caches the reconcile's two reads per moved handle and per touched key,
;; filled by the reconcile and dropped by the writers; past `supporter-cache-limit` it is
;; cleared (docs/taxonomy.md).

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
  "A KB's taxonomy: one atom holding the cached relations, plus a watch bumping
  `observe/note-change` on every write.  `detached-copy` carries no watch.  The side atoms
  need none (docs/taxonomy.md, \"Side atoms, probe copies and symmetric entries\")."
  []
  (doto
   (atom {:genl (empty-relation) :genlCx (empty-relation)
          :equality (empty-equality)
          :disjoint #{} :disjoint-index {} :disjoint-metatypes #{} :metatype-members {}
          :sibling-disjoint #{} :sib-exception-index {}
          :covers {} :cover-parts {} :partitions #{}
          :props {} :inverse {} :negates {} :genl-inverse-down {} :genl-inverse-up {} :arity {} :functional-in-arg {} :commuting {} :meet {} :distinct {}
          :cache-dirty #{} :cache-ctxs {}
          ;; The supporter cache (`supporters-of`), over the index's supporter families
          :supporters empty-supporters
          ;; the index store the supporter families are posted to and read from (`post!`); a raw taxonomy holds a private one
          :index (private-index) :raw? true
          ;; two read-only callbacks a KB installs: whether any supporter needs exception-aware scoping, and whether one is effective from a reader; a raw taxonomy keeps the context-only path
          :supporter-filter-active? nil :supporter-visible? nil
          :network-filter-active? nil :network-visible? nil :supporter-reaches? nil
          :supporter-sentence nil
          ;; how many times `clear-relations!` rebuilt the relations, whose `:gen`s it
          ;; restarts at 0 (`relation-epoch`)
          :epoch 0
          ;; oriented schematic rewrite rules (docs/equality.md): `:rewrite-support` by equation handle, `:rewrite-active` the believed subset `refresh-beliefs` keeps in sync
          :rewrite-support {} :rewrite-active {}
          ;; side atom of memoized reads beside the closures (see docs/taxonomy.md, "Side atoms, probe copies and symmetric entries")
          :closure-memo (caches/tallied (atom {}) [:T7])
          ;; the closures, global and scoped, in one weighted LRU keyed with the relation's `:gen`; a scope reading supporter belief also carries the change clock (`relation-scope`)
          :closure-lru (closure-lru)
          ;; the content-ordered rewrite rules (`rewrite-rules`), keyed by the map object they sorted
          :rewrite-order (atom nil)})
    ;; the value a write replaces is also the open write record's value for this atom,
    ;; the first time a write since the record opened replaces one (`before-copy`)
    (add-watch ::change (fn [_ r old new]
                          (observe/note-change)
                          (when-let [^java.util.concurrent.atomic.AtomicLong n
                                     (:nodes (:closure-lru new))]
                            (.set n (relation-nodes new)))
                          (when observe/*write-record* (observe/record-of r (constantly old)))))))

(defn install-supporter-visibility!
  "Install the KB-owned visibility callbacks on `tax`.  `active?` is the O(1) whole-KB
  presence check: falsy while no `except` or placed `defeat` is stored, else truthy, and
  then the stored target entries, a seq of `[key #{target-handle …}]` (a bare truthy value
  means every relation).  `reaches?` answers whether a supporter of the relation being read
  rests on a target, given the entries, a `supporter-summary` and whether placed defeats
  count (they do not for `genlCx`).  `visible?` answers whether one stored supporter
  handle is believed and seen from one reader context.  `network-active?` and
  `network-visible?` read the network and stored `except`s alone (`*network-belief*`).
  `sentence-of` answers the sentence a supporter handle states, for `most-general-of`.
  The taxonomy stays independent of the JTMS and exception grammar."
  ([tax active? visible?] (install-supporter-visibility! tax active? visible? active? visible? nil nil))
  ([tax active? visible? network-active? network-visible? reaches? sentence-of]
   (swap! tax assoc :supporter-filter-active? active? :supporter-visible? visible?
          :network-filter-active? network-active? :network-visible? network-visible?
          :supporter-reaches? reaches? :supporter-sentence sentence-of)
   tax))

(defn install-index!
  "Install the KB's index store on `tax`: the supporter families are posted to it and
  read from it, and `census-in` reads the contexts that state a supporter there."
  [tax index]
  (swap! tax assoc :index index :raw? false)
  tax)

(defn before-copy
  "The value `tax` held when the open write record first recorded it, or its value now
  when the record holds none, in a fresh atom with side caches of its own and no watch,
  as `detached-copy` builds them: the taxonomy of `kb/prior-kb`, which installs its
  index store and callbacks."
  [tax]
  (let [t (or (observe/recorded tax) @tax)]
    (atom (assoc t :closure-memo (atom {}) :closure-lru (closure-lru t) :rewrite-order (atom nil)))))

(defn detached-copy
  "The current taxonomy state in a fresh atom, for a what-if probe: mutate the copy and
  the real taxonomy never learns it.  `:closure-memo`, `:closure-lru` and `:rewrite-order`
  are the copy's own, and `:index` is a fork of the original's (`mount/fork-families`).
  See docs/taxonomy.md, \"Side atoms, probe copies and symmetric entries\"."
  [tax]
  (let [t @tax]
    (atom (assoc t :index (mount/fork-families (:index t))
                 :closure-memo (atom {}) :closure-lru (closure-lru t) :rewrite-order (atom nil)))))

;; ---- on-demand closures, memoized per generation ------------------------
;; `:fwd` / `:rev` hold direct adjacency; the closure is computed up from the parents'
;; closures (`reach-by-parents`) or down by `reach` and cached in `:closure-lru` under
;; the relation's `:gen`.  `genl?` / `sees?` answer through the depth-pruned
;; `reachable?` and hold nothing; only a caller that walks or intersects the set reads a
;; closure (docs/taxonomy.md, "The closure is not materialized").

(defn- reach-by-parents
  "The up-closure of `node`, built as `C ∪ ⋃ closure(p)` over the parents `p` outside its
  component `C`, bottom-up from the nearest ancestors `held` answers.  Each closure built
  is handed to `hold!` under its component's representative.  Components come from `scc`.
  Answers nil when a unit returns to the stack top still waiting on a parent (a deferred
  cycle `scc` does not yet name) or a parent's closure was evicted; the caller walks
  instead.  With a transducer `xf` other than nil, each answer is the union of what `xf`
  makes of the closure's terms (`genls-global-union`).  `walk`, when given, answers a unit
  with two or more parents not yet built, in place of building them."
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

(defn- stored-closure-of
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

(def ^:private root-cx sx/root-context)

(defn root-context?
  "Is `c` CxUniverse, the context every other context sees with no stored edge?  A walk
  down from it would visit every context, so its callers answer that case directly.
  See docs/contexts.md, \"CxUniverse is the implicit root\"."
  [c]
  (= c root-cx))

(defn- rooted?
  "Does `c` see CxUniverse through the implicit edge: `c` is neither CxUniverse nor a query
  context (`nm/query-contexts`), `CxNothing` reading nothing at all?"
  [c]
  (not (or (root-context? c) (nm/query-context? c))))

(defn- reachable-in?
  "Does `src` reach `tgt` in relation `rel-key` over the stored edges, following `:fwd`?
  The depth-pruned `reachable?` rejects most pairs in O(1) and never materializes a
  closure: the path shared by `genl?` / `sees?` and the assert-time cycle checks in `wff`.
  A relation left `:loose?` by a deferred batch has no sound potential yet, so the depth
  is withheld and the walk runs unpruned: the same answer at a higher cost."
  [tax rel-key src tgt]
  (let [rel (get @tax rel-key)]
    (reachable? src tgt (:fwd rel) (when-not (:loose? rel) (:depth rel)) (:scc rel))))

(defn- implicit-reach?
  "Does context `k` reach context `y` through the implicit edge: `k` is not CxUniverse,
  and `y` is CxUniverse or a context CxUniverse reaches over stored edges?"
  [tax k y]
  (and (rooted? k) (reachable-in? tax :genlCx root-cx y)))

(defn- with-root-parents
  "Context `c`'s parents `ps` over one `genlCx` edge, with the implicit edge to CxUniverse
  added for every context other than CxUniverse: the parent read every upward walk of
  the context relation takes."
  [c ps]
  (if (rooted? c) (conj (set ps) root-cx) ps))

(defn- with-root
  "`closure`, `node`'s stored `genlCx` closure in direction `dir-key`, with the implicit
  edges added, memoized under the relation's generation.  Up: a node other than
  CxUniverse gains `up`, CxUniverse's closure (a thunk).  Down: CxUniverse and a context
  it reaches gain every context node of the relation.  A context no edge names is a
  node of no closure, so no caller that must reach every context walks down from
  CxUniverse (`root-context?`).  A map scope is not memoized."
  [tax dir-key node scope closure up]
  (let [t   @tax
        rel (:genlCx t)
        lru (:closure-lru t)
        k   [:genlCx (:gen rel) ::rooted dir-key node scope]
        held (fn [make] (if (map? scope)
                          (make)
                          (or (caches/lru-get lru k) (caches/lru-put! lru k (make)))))]
    (if (= dir-key :fwd)
      (if (or (not (rooted? node)) (contains? closure root-cx))
        closure
        (held #(into closure (up))))
      (if-not (reachable-in? tax :genlCx root-cx node)
        closure
        (held #(into closure (:nodes rel)))))))

(defn- closure-of
  "`stored-closure-of`, with `genlCx`'s implicit edges to CxUniverse added (`with-root`)."
  [tax rel-key dir-key node]
  (let [v (stored-closure-of tax rel-key dir-key node)]
    (if (= rel-key :genlCx)
      (with-root tax dir-key node nil v #(stored-closure-of tax :genlCx :fwd root-cx))
      v)))

;; ---- scoped reads: the visibility filter over the same closures ----------
;; A read from context K uses the edges some believed supporter asserts from a context in
;; K's genlCx ancestor set (`:edge-ctxs`).  The genlCx closure itself is never filtered.
;; The filter is keyed on `vis = up(K) ∩ ctxs`, `ctxs` the relation's context census
;; (`census-in`): two contexts with the same `vis` induce the same filtered edge set.  nil
;; `vis` means the global path.  See docs/taxonomy.md, "Reads are scoped by the asking context".

(def edge-installing-functors
  "The functors of the sentences `installed-edges` reads a `genl` edge off."
  '#{genl covering separating partition})

(def ^:private flat-functors
  "The functors whose declarations the flat caches record, read off their storage in
  `vaelii.impl.predicates`: every property, mark, keyed pair other than equality, cover,
  per-position and commuting declaration.  A disjoint metatype's members are stated under
  the metatype, which is data, so `census-functors` adds those."
  (into #{} (comp (filter (fn [[_ spec]]
                            (let [[kind target] (:storage spec)]
                              (and (contains? #{:prop :mark :keyed-pair :cover :pred-position
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

(defn- supporter-summary
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

(def ^:dynamic *visible-neighbours-cache*
  "An optional atom holding a `{[dir-key vis n] neighbours}` map for a read-only pass
  over a still taxonomy, bound and dropped by the pass.  It also holds the other reads a
  pass repeats (`pass-held`).  nil off such a pass.  See docs/taxonomy.md, \"Side atoms,
  probe copies and symmetric entries\"."
  nil)

(defn with-neighbours
  "Run `f` with `nc`, an atom, as the scoped walks' neighbour cache
  (`*visible-neighbours-cache*`) when none is bound: for a caller that asks many scoped
  walks over a taxonomy and a belief that hold still for as long as it keeps `nc`."
  [nc f]
  (if *visible-neighbours-cache*
    (f)
    (binding [*visible-neighbours-cache* nc] (f))))

(defn pass-held
  "`(read)`, held under `k` in the reading pass's neighbour cache
  (`*visible-neighbours-cache*`) when one is bound: the pass holds the taxonomy, belief
  and the stored records still, so `k` need name only what the read is asked of and the
  dynamic readings it depends on (`*network-belief*`, `*search*`).  A nil or false
  answer is held as any other."
  [k read]
  (if-let [nc *visible-neighbours-cache*]
    (if-let [e (find @nc k)]
      (val e)
      (caches/held-if-settled read #(do (swap! nc assoc k %) %)))
    (read)))

;; Forward declarations: `relation-scope` and `scope-admits-supporter?` reference
;; these before their definitions because the scope machinery sits above the walk
;; but below the closure, creating a mutual dependency.
(declare visible-ctxs context-up sees?)

(def ^:dynamic *network-belief*
  "True while a firing's witness search reads the scoped closures (`chain`'s placement):
  a supporter is read at its network label and through the stored `except`s, and no
  placed `defeat` is read (`:network-filter-active?`, `:network-visible?`).  The scope
  key carries the callback it reads, so the two readings never share a memo entry."
  false)

(def ^:dynamic *search*
  "nil outside a second-route search (`exc/route-answer`), else `:belief` while the search
  answers a belief read and `:visibility` otherwise.  A scope that reads supporter belief
  carries the value in its key, as the effective ancestor set does, so a walk inside a
  search and one outside it never share a memo entry."
  nil)

(defn- entries-fn
  "The whole-KB presence-check callback the reading in force reads (`*network-belief*`)."
  [t]
  (if *network-belief* (:network-filter-active? t) (:supporter-filter-active? t)))

(defn- visible-fn
  "The supporter callback the reading in force reads (`*network-belief*`)."
  [t]
  (if *network-belief* (:network-visible? t) (:supporter-visible? t)))

(defn- supporter-filter-active?
  "Does this KB currently need supporter-level filtering anywhere?  This is the whole-KB
  presence check: true once any visibility `except`, or for a reader's belief any placed `defeat`, is
  stored, whatever it targets."
  [t]
  (boolean (when-let [active? (entries-fn t)] (active?))))

(defn- targets-supporter?
  "Is a target of an entry of `entries` a supporter in `sups` (`supporter-summary`)?  The reach
  callback of a taxonomy with none installed (`install-supporter-visibility!`), which
  reads every entry whatever `_defeats?`.  An entry's targets may be a delay."
  [entries sups _defeats?]
  (boolean (some (fn [e] (some (:supports? sups) (force (val e)))) entries)))

(defn- relation-filter-active?
  "Does a scoped read of `rel-key` need supporter-level exception filtering: does some
  supporter of it, or of `genlCx`, rest on the target of a stored `except` or placed
  `defeat` (the reach callback, `install-supporter-visibility!`)?  A supporter no except
  targets is visible from a reader iff it is believed, so the context-only walk answers
  the same.  Memoized per relation in the closure memo, keyed by the change clock and both
  relations' generations."
  [t rel-key]
  (when-let [active? (entries-fn t)]
    (let [cx     (:genlCx t)
          rel    (get t rel-key)
          slot   (if *network-belief* :filter-active-network :filter-active)
          under  [(observe/change-clock) (:gen cx) (:gen rel)]
          memo   (:closure-memo t)
          tl     (caches/tally-of memo :T7)
          cached (get-in @memo [rel-key slot])]
      ;; the clock and generations are read before the excepts and defeats: a hit reads no index
      (if (= under (:read-under cached))
        (do (caches/hit tl) (:active? cached))
        (when-let [entries (active?)]
          (if-not (sequential? entries)
            true
            (let [reach    (or (:supporter-reaches? t) targets-supporter?)
                  cx-sups  (supporter-summary t :genlCx)
                  rel-sups (when (not= rel-key :genlCx) (supporter-summary t rel-key))
                  active (caches/recomputed
                          tl (boolean (or (reach entries cx-sups false)
                                          (and rel-sups (reach entries rel-sups true)))))]
              (when cached (caches/compared tl (= active (:active? cached))))
              (swap! memo (fn [mm]
                            (let [e (get mm rel-key)
                                  e (if (= (:gen rel) (:gen e)) e {:gen (:gen rel) :fwd {} :rev {}})]
                              (assoc mm rel-key (assoc e slot {:read-under under :active? active})))))
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
  With no `except` reaching the relation (`relation-filter-active?`) this is
  `visible-ctxs`'s set/nil answer.  Otherwise a map holding the reader's
  exception-filtered ancestor set, the concrete reader, the reading (`*network-belief*`'s
  callback, `*search*`) and the change clock.  Held for a reading pass (`pass-held`)."
  [tax rel-key context]
  (when (scoped-context? context)
    (pass-held
     [::scope rel-key context *network-belief* *search*]
     #(let [t   @tax
            ;; An exception on genlCx changes the assertion contexts a reader inherits.  genlCx
            ;; starts from the raw ancestor set, so an edge's visibility reads no genlCx edge's
            ;; visibility (`exc/witness-paths`); every other relation uses the effective set.
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
          vis)))))

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
  memo under the relation's generation, keyed by the change clock and the `genlCx`
  generation, as `context-down-visible` is: the census reads stored extents, which move
  only at a write."
  [tax rel-key context]
  (when (scoped-context? context)
    (let [t     @tax
          gen   (:gen (get t rel-key))
          under [(observe/change-clock) (:gen (:genlCx t))]
          memo  (:closure-memo t)
          m     @memo
          cur   (when (= gen (get-in m [rel-key :gen])) (get m rel-key))
          vis   (:visible cur)
          tl    (caches/tally-of memo :T7)]
      (if-some [hit (when (= under (:read-under vis)) (find (:by-ctx vis) context))]
        (do (caches/hit tl) (val hit))
        (caches/held-if-settled
         #(caches/recomputed tl (census-among t rel-key (closure-of tax :genlCx :fwd context)))
         (fn [s]
           (swap! memo
                  (fn [mm]
                    (let [e   (get mm rel-key)
                          e   (if (= gen (:gen e)) e {:gen gen :fwd {} :rev {}})
                          vis (:visible e)
                          vis (if (= under (:read-under vis)) vis {:read-under under :by-ctx {}})]
                      (assoc mm rel-key (assoc e :visible (assoc-in vis [:by-ctx context] s))))))
           s))))))

(defn- ctxs-visible?
  "Does the supporting-context set `cs` reach a reader whose visible set is `visq`
  (a set, or a predicate built from one)?  nil in `cs` is a supporter with no
  recorded context and constrains everywhere."
  [cs visq]
  (boolean (some (fn [c] (or (nil? c) (visq c))) cs)))

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
                                   #{} (stored-closure-of tax rel-key dir-key node)))))))

(defn- stored-closure-of-vis
  "`closure-of` over only the edges effective in `scope`, memoized in the same LRU under
  the interned scope key and the relation's `:gen`.  The answer is a subset of
  `closure-of`'s.  A set scope that sees every context the global closure rests on reads
  the global closure (`closure-needs`); a map scope (`except` visibility) always walks."
  [tax rel-key dir-key node scope]
  (or (when (set? scope)
        (let [r (closure-needs tax rel-key dir-key node)]
          (when (and (not= ::several r) (every? scope r))
            (stored-closure-of tax rel-key dir-key node))))
      (let [t   @tax
            rel (get t rel-key)
            lru (:closure-lru t)
            k   [rel-key (:gen rel) dir-key node scope]]
        (or (caches/lru-get lru k)
            (let [t0 (System/nanoTime)
                  v  (caches/held-if-settled #(reach node (fn [n] (visible-neighbours t rel-key dir-key scope n)))
                                             #(caches/lru-put! lru k %))]
              (caches/spent (:tally lru) t0)
              ;; compared across clock stretches: a map scope's clock goes into the key
              (caches/compare-retired (:tally lru)
                                      [rel-key dir-key node (if (map? scope) (dissoc scope :clock) scope)]
                                      [(:gen rel) (:clock scope)] v)
              v)))))

(defn- closure-of-vis
  "`stored-closure-of-vis`, with `genlCx`'s implicit edges to CxUniverse added
  (`with-root`).  The implicit edge has no supporter, so every scope admits it."
  [tax rel-key dir-key node scope]
  (let [v (stored-closure-of-vis tax rel-key dir-key node scope)]
    (if (= rel-key :genlCx)
      (with-root tax dir-key node scope v #(stored-closure-of-vis tax :genlCx :fwd root-cx scope))
      v)))

(defn- reachable-filtered?
  "`reachable?` over only the edges effective in `scope`, the sibling walk of the scoped
  `genl?`.  The depth potential holds over the global edge set, so both prunings stay
  sound.  The neighbour set is filtered before the direct-edge test.  `scc` serves only
  the level-in-`tgt`'s-component pruning: a shared component is never an answer, since
  mutual reachability is a fact about the global edge set."
  [src tgt t rel-key scope depth scc]
  (let [nbrs #(visible-neighbours t rel-key :fwd scope %)]
    (or (= src tgt)
        (if (nil? depth)
          (walk-hits? src nbrs (fn [ns] (some #(= tgt %) ns)) nil)
          (let [dt    (get depth tgt)
                ctgt  (get scc tgt)
                ;; Could `x` still lie on a path to `tgt`?  With `tgt` in no component (every node of
                ;; an acyclic relation) the bare comparison is the whole rule, and the component arm
                ;; would cost one `scc` lookup per neighbour.
                over? (if (nil? ctgt)
                        (fn [x] (> (get depth x -1) dt))
                        (fn [x] (let [d (get depth x -1)]
                                  (or (> d dt) (and (= d dt) (= ctgt (get scc x)))))))]
            (and (some? dt)
                 (over? src)
                 (walk-hits? src nbrs (fn [ns] (some #(= tgt %) ns)) over?)))))))

;; ---- supporter reference counting for the non-transitive caches ---------
;; The six flat caches (`disjoint`, the disjoint metatypes, the sibling-disjoint marks,
;; the predicate properties, `inverse`, the declared arities) are keyed by `[kind key]`
;; and counted by their supporters in the index's supporter family: an entry is active iff
;; some supporter is stored and believed, and `refresh-cache-support` reconciles it after
;; a relabel.  `cache-install` / `cache-uninstall` define an active entry for the
;; `add-*` / `mark-*` writers and the reconcile.  `:cache-ctxs {[kind key] #{ctx}}`
;; mirrors `:edge-ctxs`, and `:cache-dirty` mirrors `:dirty` for a shared entry the
;; belief-blind writers left behind (docs/taxonomy.md).

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

(defn negates-key
  "The flat-cache key for a `negates` declaration between `p` and `q`, `inverse-key`'s
  shape: `(negates P P)` keys `#{P}`."
  [p q]
  [:negates (hash-set p q)])

(defn- declared-pair
  "The two terms a `[:inverse #{p q}]`, `[:negates #{p q}]` or `[:disjoint #{x y}]` key
  names, as `[x y]`.  A self-pair — `(inverse P P)`, `(disjoint T T)` — collapses to
  `#{p}`, so `y` falls back to `x`: both directions of the index write then name the same
  pair, which is idempotent.  One extractor for all three, because the key is a set in
  each."
  [s]
  (let [x (first s)] [x (or (second s) x)]))

(defn- index-symmetric
  "Add or drop both directions of a declared symmetric pair in the adjacency at `k`,
  `{term -> #{terms declared to stand in the relation to it}}`: `:inverse` and `:negates`
  (predicates) and `:disjoint-index` (types).  An emptied entry is dissoc'd.  The entry is
  a set (docs/taxonomy.md, \"Side atoms, probe copies and symmetric entries\")."
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
  taxonomy edge, applied to a part list: at least three elements, every one of them a
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
  `partition` declaration (`special/cover-arms`), none for any other sentence.  A part
  equal to the whole gives no pair.  See docs/taxonomy.md, \"A cover states the
  specialization it rests on\"."
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
  "The three claims a whole-and-parts declaration can make about its parts, as the
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
    ;; `:cover` is one whole-and-parts declaration: `a` is `[whole parts]` (parts sorted) and `b`
    ;; is the `cover-kinds` keyword.  Three tables: `:covers` (what covers a whole, the
    ;; contradiction check), `:cover-parts` (what covers name a part, `CoveringProver`) and
    ;; `:partitions` (the separating subset `separation-frame` walks).  A declaration enters
    ;; the first two only if it covers and the third only if it separates.  The part list is
    ;; never written out as a `(disjoint …)` sentex per pair.
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
    :negates  (index-symmetric t :negates a true)                  ; a = #{p q}
    ;; a `(genlInverse p q)` edge, held both ways round for the signed closure's two walks
    :genl-inverse (-> t (update-in [:genl-inverse-down b] (fnil conj #{}) a)
                      (update-in [:genl-inverse-up a] (fnil conj #{}) b))      ; a = p, b = q
    :arity    (update-in t [:arity a] (fnil conj #{}) b)                          ; a = pred, b = n
    ;; `:functional-in-arg` is `:arity`'s shape and not `:prop`'s, because the
    ;; declaration carries an integer and a `:props` set holds predicates with
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
    :commuting (update-in t [:commuting a] (fnil conj #{}) b)                     ; a = pred, b = group
    ;; `:meet` holds the orders a `(meetFunctionOf F R)` names for `F`, the shape
    ;; `:arity` has: one function may be declared the meet of two orders.
    :meet      (update-in t [:meet a] (fnil conj #{}) b)                          ; a = fn, b = order
    :distinct  (update-in t [:distinct a] (fnil conj #{}) b)))                    ; a = fn, b = n

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
    ;; to `#{}`, since `covers-naming` reads only a present entry.
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
    :negates  (index-symmetric t :negates a false)
    :genl-inverse (let [drop-in (fn [t path v]
                                  (let [left (disj (get-in t path #{}) v)]
                                    (if (seq left)
                                      (assoc-in t path left)
                                      (update-in t (pop path) dissoc (peek path)))))]
                    (-> t (drop-in [:genl-inverse-down b] a) (drop-in [:genl-inverse-up a] b)))
    :arity    (let [ns' (disj (get-in t [:arity a] #{}) b)]
                (if (seq ns') (assoc-in t [:arity a] ns') (update t :arity dissoc a)))
    ;; Dropping the last position drops the predicate's whole entry, so
    ;; `functional-in-arg-over`'s `(filter table)` candidate filter stays exact and an
    ;; emptied predicate does not linger as a key mapping to `#{}`.
    :functional-in-arg
    (let [ns' (disj (get-in t [:functional-in-arg a] #{}) b)]
      (if (seq ns')
        (assoc-in t [:functional-in-arg a] ns')
        (update t :functional-in-arg dissoc a)))
    ;; The same emptied-key discipline, for the same reason: `commuting-groups` reads
    ;; only a present entry for the predicate, so a predicate whose last group left must
    ;; not linger as a key mapping to `#{}` — a literal would then take the group-aware
    ;; canonicalization path and pay for a licence it no longer has.
    :commuting
    (let [gs' (disj (get-in t [:commuting a] #{}) b)]
      (if (seq gs')
        (assoc-in t [:commuting a] gs')
        (update t :commuting dissoc a)))
    :meet
    (let [rs' (disj (get-in t [:meet a] #{}) b)]
      (if (seq rs')
        (assoc-in t [:meet a] rs')
        (update t :meet dissoc a)))
    :distinct
    (let [ns' (disj (get-in t [:distinct a] #{}) b)]
      (if (seq ns')
        (assoc-in t [:distinct a] ns')
        (update t :distinct dissoc a)))))

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

(defn- retire-posting!
  "Take `handle` out of taxonomy key `k`'s supporters in index store `idx`, from
  whichever context it is stated in, and the facts naming it out of `k`'s relation in the
  `:tax-named` family when `handle` installs no other key of the relation: true when it
  was one."
  [idx k handle]
  (let [rel (kv/key-relation k)
        was (some? (first (p/family-apply! idx [[:retire :tax-support (conj k p/any-context) handle]
                                                [:retire :tax-installs [handle] k]])))]
    (when-let [ops (seq (named-ops idx :retire rel handle))]
      (when-not (some #(= rel (kv/key-relation %)) (reads/as-stored-installed-keys idx handle))
        (p/family-apply! idx (vec ops))))
    was))

(defn- retire!
  "`retire-posting!` in `tax`'s index store."
  [tax k handle]
  (retire-posting! (:index @tax) k handle))

(defn retire-stored-supporter!
  "Take stored handle `h` out of the supporters of every taxonomy key it installs, in
  index store `idx` alone: the index half of a declaration's departure, for a KB whose
  taxonomy is not built (`vaelii.impl.record-edit`).  The taxonomy's in-memory entries
  are untouched.  Returns the number of keys."
  [idx h]
  (let [ks (vec (reads/as-stored-installed-keys idx h))]
    (doseq [k ks] (retire-posting! idx k h))
    (count ks)))

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
;; Only the direct adjacency is stored; the closure is answered on demand and memoized
;; per generation.  An insert is O(1) plus the depth repair `raise-depth` forces
;; (`*defer-depths?*` trades it away); a delete is O(1) plus a node re-scan.  Every
;; mutation bumps `:gen`.

(defn- bump-gen [rel] (update rel :gen inc))

(defn- note-at
  "`rel` with `x` logged at the current generation in the `(sorted-map gen #{x})` under
  `log-key`, holding each `x` at the last generation that logged it (`gen-key`), so the
  log is bounded by the distinct `x`."
  [rel log-key gen-key x]
  (let [g   (:gen rel)
        old (get-in rel [gen-key x])
        ms  (or (get rel log-key) (sorted-map))
        ms  (if (and old (not= old g))
              (let [left (disj (get ms old) x)]
                (if (seq left) (assoc ms old left) (dissoc ms old)))
              ms)]
    (-> rel
        (assoc log-key (update ms g (fnil conj #{}) x))
        (assoc-in [gen-key x] g))))

(defn- note-move
  "`rel` with node `a` recorded as the lower end of an edge whose activation or supporting
  contexts moved at the current generation, in `:moves`. Every closure a move changes is
  a closure of a node at or below a recorded one (`moves-since`)."
  [rel a]
  (note-at rel :moves :move-gen a))

(defn- note-shrink
  "`rel` with node `a` recorded as the lower end of an edge that left the active set or
  whose supporting contexts moved after the first set, in `:shrinks`, logged as
  `note-move` logs `:moves` (`shrinks-since`)."
  [rel a]
  (note-at rel :shrinks :shrink-gen a))

(defn- note-grow
  "`rel` with edge `e` recorded as entering the active set at the current generation, in
  `:grows`, logged per edge as `note-move` logs per node (`grows-since`)."
  [rel e]
  (note-at rel :grows :grow-gen e))

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
  "Raise components until every `[node depth]` seed holds (the node's whole component
  at least that deep), pushing each raise up through `:rev`.  A component is re-enqueued
  whenever a deeper one lifts it.  See docs/taxonomy.md, \"Depth repair and the reconcile's
  arms\"."
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
  rebuilds every depth in one pass when the batch settles.  Bound by
  `vaelii.core/with-deferred-settle`.  See docs/taxonomy.md, \"What a batch does to the
  depth potential\"."
  false)

(def ^:dynamic *defer-cycle-scc?*
  "When true, an edge that closes a cycle marks the relation `:loose?` and leaves the
  strong-component recompute to `restore-depths`, instead of running `repair-depths` inside
  `activate`.  A caller that binds this must call `restore-depths` before any
  `placement-rep` reader runs, as `vaelii.impl.recovery/recover` does.  See
  docs/taxonomy.md, \"Depth repair and the reconcile's arms\"."
  false)

(defn- local-lift
  "Restore `depth[a] > depth[b]` for the newly inserted edge a->b alone: lift `a` just
  above `b` and check only the edges into `a` (`:rev a`), never its descendants.  If an
  edge is broken the relation goes `:loose?` and `restore-depths` owns the repair.  A
  parent-before-child arrival never breaks one.  See docs/taxonomy.md, \"What a batch does
  to the depth potential\"."
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
  (let [out (volatile! {})]
    (graph/scc nodes #(get fwd %)
               (fn [members]
                 (when (> (count members) 1)
                   (let [rep (term-min members)]
                     (vswap! out into (map (fn [m] [m rep])) members)))))
    @out))

(defn- repair-depths
  "Recompute every depth of `rel` in one O(V+E) pass over the condensation, restoring
  `edge x->y` implies `depth[x] >= depth[y]`, strict between components and equal inside
  one.  Each component takes `1 + max` of what it points at.  See docs/taxonomy.md,
  \"Depth repair and the reconcile's arms\"."
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
  "Bring [a b] into the active edge set: record the direct adjacency, the node set, and
  repair the depth potential.  A no-op when the edge is already active.  `wff` and
  `special/wff-violation` refuse a cycle-closing edge before it reaches here; one arrives
  past them from `recovery/recover`, a foreign or bulk writer, or a belief-race revival.
  An edge that closes a cycle (guarded by `reachable?`, run only when `a` is already a
  node, and still run while loose) is repaired outright with `repair-depths`, so `:scc`
  holds the merged component before `placement-rep` reads it.  Under `*defer-depths?*` the
  acyclic repair is `local-lift`; under `*defer-cycle-scc?*` the cyclic repair is deferred
  too.  An already-loose relation records the adjacency and leaves the repair to
  `restore-depths`.  See docs/taxonomy.md, \"What a batch does to the depth potential\"."
  [rel a b]
  (if (contains? (:edges rel) [a b])
    rel                                            ; already active — nothing to do
    (let [loose?  (boolean (:loose? rel))
          cyclic? (cond
                    ;; a deferred replay on a loose relation skips the cycle-detection walk, which is
                    ;; unpruned and decides nothing (`*defer-cycle-scc?*`); `restore-depths` recomputes
                    ;; `:scc` from the final graph
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
          (note-move a)
          (note-grow [a b])))))

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
  "Depths for the members of a component that has just split, given `sub`, the
  components of its own induced subgraph: `{node depth}` over `members`.  Each
  sub-component sits one above the highest thing it points at, so the answer is tight."
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
  Acts only when the edge's two endpoints share a component, re-running `strong-components`
  over its induced subgraph (`split-depths`, `lift-components`).  A relation already
  loose drops the component whole for `restore-depths`.  The relation does not go
  `:loose?`.  See docs/taxonomy.md, \"Depth repair and the reconcile's arms\"."
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
          (note-move a)
          (note-shrink a)))))

(defn- set-edge-ctxs
  "Record `ctxs` as active edge `e`'s supporting contexts, bumping `:gen` iff the set
  moved — a scoped read's answer is a function of these, so a context-only move must
  retire the read memo even though the edge set did not change."
  [rel e ctxs]
  (if (= ctxs (get-in rel [:edge-ctxs e]))
    rel
    (cond-> (-> rel (assoc-in [:edge-ctxs e] ctxs) bump-gen (note-move (first e)))
      ;; the first supporting contexts an edge records come with its arrival; a later
      ;; set moves what the readers under it see
      (some? (get-in rel [:edge-ctxs e])) (note-shrink (first e)))))

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
        ;; retarget only an active edge; a refresh may have deactivated this one with its
        ;; supporters still stored.  The edge owes a reconcile either way (belief-blind).
        (update t rel-key #(-> %
                               (cond-> (contains? (:edges %) [a b])
                                 (set-edge-ctxs [a b] (into #{} (vals left))))
                               (mark-dirty [a b] true)))
        (-> t
            (update-in [:supporters :by-key] dissoc k)
            (update rel-key #(-> % (deactivate a b) (update :edge-ctxs dissoc [a b])
                                 (update :dirty disj [a b]))))))))

(defn- moved-touches?
  "Should a cache be reconciled against belief?  True when `moved` is nil, or when one of
  the cache's supporters (a set of handles, or the map they key) is in `moved`, the
  handles whose belief just flipped.  Walks the smaller side.  Used only for the equality
  partition and rewrite rules (docs/taxonomy.md, \"Depth repair and the reconcile's
  arms\")."
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
  "`[t' ks]`: the taxonomy keys a handle in `moved` installs, the whole scope a reconcile
  owes, read through the supporter cache with `t'` holding what it read.  Every key with a
  stored supporter when `moved` is nil (`all-keys`, or a raw taxonomy's walk).  `moved` is
  a superset of the handles whose belief flipped (`jtms/touched`).  Walks the smaller of
  `moved` and the handles of the facts that can install a key (`supporter-functors`,
  `stored-metatypes`)."
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
  "Reconcile one relation's active edges with belief: an edge is active when some
  supporter is believed, and carries those supporters' contexts.  Applies the difference
  by three arms in order (deactivate, activate, retarget) and keeps only the edges whose
  state changes.  Scoped to `edges` (`moved-keys`) and `:dirty`, which it clears.  A
  settle whose region names no edge returns the relation untouched.  See
  docs/taxonomy.md, \"Depth repair and the reconcile's arms\"."
  [t rel-key believed? edges]
  (let [rel     (get t rel-key)
        touched (into (:dirty rel) edges)]
    (if (empty? touched)
      t
      (let [have (:edges rel)
            ctxs (:edge-ctxs rel)
            ;; `drops` is a hash set and `adds` a hash map (never an array map), so the arms meet
            ;; their edges in hash order.  `retarget` skips an active edge whose believed contexts
            ;; equal its recorded ones.
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
;; A partition, member → class and class → members and representative, over undirected
;; edges whose `rewriteOf` preference belongs to each supporter (docs/equality.md,
;; "Storage").  A union re-keys the joined class, so n asserts growing one class to n
;; cost Θ(n²); a deletion rebuilds the class it can split.

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
  "The representative of a class, from its members and the preference claims its active
  edges carry (docs/equality.md, \"Choosing the representative\"): the smallest head, a
  preferred term nothing deprecates; else, for a `rewriteOf` cycle `wff` refuses, the
  smallest preferred term; else the smallest member.  Total."
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
  `take-equality-moves!`: `special/supersession-map` and `special/covered-merges`."
  [:supersessions :covers])

(defn- note-moved
  "Add the classes of edge `e`'s two ends to each reader's `:moved` set
  (`take-equality-moves!`).  Read after the edge is applied: a union's class holds both
  old classes, and a split's two classes make up the old one."
  [rel [a b]]
  (let [ms (into (class-members rel a) (class-members rel b))]
    (reduce (fn [r k] (update-in r [:moved k] (fnil into #{}) ms)) rel equality-move-readers)))

(defn- refresh-equality
  "Reconcile the equality partition with belief, scoped to the supporters `moved` names:
  `:out` is updated for `moved ∩ handles` and only their edges are re-applied, through
  `:handle-edge`, walked from the smaller side.  nil `moved` re-asks every supporter
  (`refresh-beliefs`' two-arity).  The edge of each supporter whose `:out` entry flipped
  is noted in `:moved`, and each supporter that left `:out` joins `:believed-again`
  (`take-believed-again!`)."
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
  did not move.  nil when nothing moved.  The readers (`equality-move-readers`) are
  `:supersessions`, for `special/supersession-map`, and `:covers`, for
  `special/covered-merges`."
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
  "`[members representative]` for `term` over the equality edges some supporter
  `visible?` admits, elected by `class-rep`'s rule over the visible preference claims.
  Recomputed per call rather than filtered from the global partition, since dropping an
  edge can split a class: `A~B~C` with only `A~B` visible is the class `{A B}`."
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

(defn scoped-path-supporters
  "The supporters of one path joining `a` and `b` over the equality edges some supporter
  `visible?` admits, as a vector holding each edge's admitted supporters in path order;
  nil when no such path joins them.  The path is a shortest one, searched breadth-first
  with each term's edges in content order, so the path chosen does not depend on the
  order the edges arrived in."
  [tax a b visible?]
  (when (not= a b)
    (let [rel  (:equality @tax)
          out  (:out rel #{})
          sup  (fn [e] (into (sorted-set)
                             (keep (fn [[h _]] (when (and (not (contains? out h)) (visible? h)) h)))
                             (get (:support rel) e {})))
          ekey (memoize (fn [e] (mapv term-key e)))]
      (let [{:keys [found tree]}
            (graph/bfs-tree [[a nil]]
                            (fn [t prev]
                              (for [e (sort-by ekey compare (get (:edge-idx rel) t #{}))
                                    :let [[x y] e, n (if (= x t) y x)]
                                    :when (and (not (contains? prev n)) (seq (sup e)))]
                                [n [t e]]))
                            #(= % b))]
        (when found
          (loop [t b acc ()]
            (if-let [[p e] (get tree t)] (recur p (conj acc (sup e))) (vec acc))))))))

(defn path-alternatives
  "The handle sets a path's per-edge supporter sets give (`scoped-path-supporters`): one
  supporter of each edge, in every combination."
  [path]
  (reduce (fn [acc hs] (for [a acc, h hs] (conj a h))) [#{}] path))

(defn class-fully-visible?
  "Does `visible?` admit every believed supporter of every active edge in `term`'s class?
  Then the scoped election equals the global one, and a caller takes `representative`'s
  map lookup.  The test is per supporter, not per edge: hiding only the `rewriteOf` of an
  edge that a `sameAs` also supports keeps the class and moves the head."
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

(defn class-supporters
  "The supporters, believed or not, of every active edge in `term`'s class."
  [tax term]
  (let [rel (:equality @tax)]
    (into #{} (comp (mapcat #(get (:edge-idx rel) % #{}))
                    (distinct)
                    (mapcat #(keys (get (:support rel) %))))
          (class-members rel term))))

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
  "Has anything merged `term` at all?  The O(1) presence check every scoped read takes
  first: a KB with no equalities, and a term in none of them, never pays for
  `scoped-class`."
  [tax term]
  (boolean (seq (get-in @tax [:equality :edge-idx term]))))

(defn merged-term-pred
  "A `term -> boolean` closed over one snapshot of the partition, or nil when the closure
  is empty, so a caller filtering every symbol of an answer set drops the filter
  outright for a KB that has merged nothing."
  [tax]
  (let [rel (:equality @tax)]
    (when (seq (:edges rel))
      (let [idx (:edge-idx rel)]
        (fn [term] (contains? idx term))))))

(defn deprecated?
  "Did a believed `rewriteOf` name `term` the dispreferred side?  False for a `sameAs`
  or `equals` member.  With `visible?`, only the supporters that reader admits count,
  read per supporter, since one edge may carry a `rewriteOf` and a `sameAs` at once."
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
  "`term`'s representative over the `rewriteOf` edges alone, a `sameAs` / `equals` merge
  not followed: the mention read `res/representative-term` takes inside a quoted
  position.  Elected by `class-rep`'s rule over the `rewriteOf`-connected component; a
  term no `rewriteOf` touches is returned unchanged.  With `visible?`, only the believed
  edges that reader admits count."
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
  "The handles of the believed sentexes asserting an active equality edge incident on
  `term`: the equalities migration reads a reader's copy's witnesses from."
  [tax term]
  (let [rel (:equality @tax)]
    (into #{}
          (comp (mapcat (fn [e] (keys (get (:support rel) e {}))))
                (remove (:out rel #{})))
          (get (:edge-idx rel) term #{}))))

;; ---- schematic rewrite rules (oriented equational rewriting) -------------
;; A schematic `(equals L R)` is oriented once (`vaelii.impl.rewrite/orient`) into a
;; rewrite `[lhs rhs]` and cached here with its handle and context.  `:rewrite-active` is
;; the believed subset of `:rewrite-support`, reconciled by `refresh-beliefs`.

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
  "The active oriented rewrite rules: a seq of `{:handle :lhs :rhs :context}` for every
  schematic equation currently believed, which `vaelii.impl.kb/rewrite-term` reads to
  normalize terms.  Empty is the presence check that keeps normalization a no-op.
  Content-ordered by LHS then RHS (`nm/compare-form`, never printed), and memoized in the
  `:rewrite-order` side atom keyed by the identity of the `:rewrite-active` map.  See
  docs/equational.md, \"Order independence\"."
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
  "Does flat-cache key `k` name a value (`nm/value?`) where its declaration names a type,
  a predicate or a function?  `wff` refuses such a declaration at assert, and an older
  writer's store can hold one; its key stays inactive."
  [[kind a b]]
  (case kind
    (:disjoint :sib-exception :inverse) (some nm/value? a)      ; a = #{x y}
    (:metatype :sib-disjoint :distinct) (nm/value? a)
    :prop                               (nm/value? b)           ; b = pred
    (:genl-inverse :meet)               (or (nm/value? a) (nm/value? b))
    :cover                              (let [[whole parts] a]
                                          (or (nm/value? whole) (some nm/value? parts)))
    false))

(defn- refresh-cache-support
  "Reconcile the seven flat caches (`disjoint`, the disjoint metatypes and their members,
  the sibling-disjoint marks, the `siblingDisjointException` pairs, the predicate
  properties, `inverse`, the declared arities) with current belief, as `refresh-relation`
  does for genl.  Each key in `ks` (`moved-keys`) and `:cache-dirty` is active iff some
  stored supporter is believed; install or uninstall its entry through `cache-install` /
  `cache-uninstall`, the assert path's own fns.  Every op is idempotent.  Discharges
  `:cache-dirty`.  A key with no stored supporter left is skipped."
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
  "Reconcile the cached relations with current belief: an edge or flat-cache entry is
  active iff some sentex asserting it is believed.  Called after a relabel (from
  `settle`).  `moved` is the set of handles whose belief just flipped (`jtms/touched`, a
  superset): the two transitive relations and the flat caches scope by it (`moved-keys`);
  the equality partition and rewrite rules run a presence check (`moved-touches?`).  `nil`
  reconciles every key with a stored supporter, for a caller holding no region
  (`core/recover`).  The supersession pass widens its region by hand.  See docs/taxonomy.md,
  \"The belief reconcile is scoped to the moved region\"."
  ([tax believed?] (refresh-beliefs tax believed? nil))
  ([tax believed? moved]
   ;; `recover` is the only caller holding no region
   (with-open [_ (progress/start ::reconcile (str (if (nil? moved) "recover" "settle")
                                                  ": reconcile the taxonomy with belief")
                                 nil)]
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
                                               (into #{} (filter #(of-relation? :flat %)) ks)))))))
   tax))

(defn clear-relations!
  "Drop every cache and the supporter cache, so `recover` rebuilds them from the durable
  store and a stale entry (a disjoint pair, a property, an inverse, an arity, an equality
  merge) cannot outlive its sentex.  The supporters are stored content in the index and
  stay."
  [tax]
  (swap! tax (comp #(update % :epoch (fnil inc 0)) assoc)
         :genl (empty-relation) :genlCx (empty-relation)
         :equality (empty-equality)
         :disjoint #{} :disjoint-index {} :disjoint-metatypes #{} :metatype-members {}
         :sibling-disjoint #{} :sib-exception-index {}
         :covers {} :cover-parts {} :partitions #{}
         :props {} :inverse {} :negates {} :genl-inverse-down {} :genl-inverse-up {} :arity {} :functional-in-arg {} :commuting {} :meet {} :distinct {}
         :cache-dirty #{} :cache-ctxs {}
         :supporters empty-supporters
         :cache-moves (journal/restart nil)
         :rewrite-support {} :rewrite-active {})
  ;; the read memo is keyed by `:gen`, which the fresh `empty-relation`s reset to 0, so
  ;; it is dropped too; dropping `:rewrite-order` releases the rules it retains
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
  "Does `handle` assert something the taxonomy derives an answer from: an edge of a cached
  relation (`genl`, `genlCx`), or a flat-cache entry (a separation, a metatype mark and its
  memberships, a sibling-disjointness mark, a `siblingDisjointException` pair, a cover
  declaration, a predicate property, an inverse, an arity)?  One read of the keys `handle`
  installs (`keys-of`).  The equality partition is excluded."
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

(defn grounds-stated-in
  "The handles stated in a context of `ctxs` whose functor states a `genl` edge or a
  flat-cache declaration (`census-functors`), read per functor from the predicate extents
  of the installed index store; a raw taxonomy's store holds no extent, so there each
  context of `ctxs` is read whole."
  [tax ctxs]
  (let [t   @tax
        idx (:index t)]
    (if (:raw? t)
      (into [] (mapcat #(reads/as-stored-in-context idx %)) ctxs)
      (into [] (mapcat #(reads/as-stored-with-functor-in idx % (set ctxs)))
            (sort (into (census-functors t :genl) (census-functors t :flat)))))))

(defn- supporter-scope
  "The scope `scope-admits-supporter?` reads for a reader at `context` while an `except`
  is stored: the reader's ancestor set, the reader, and the belief-plus-`except` callback."
  [tax t context]
  {:contexts (context-up tax context) :context context :supporter-visible? (visible-fn t)})

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
      (let [scope (supporter-scope tax t context)]
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

(defn installed-keys
  "The taxonomy keys the stored handle `h` installs, as a set, every family included."
  [tax h]
  (keys-of @tax h))

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
        (let [scope (supporter-scope tax t context)]
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

(defn separation-inputs
  "What a separation or a cover over two types reads of `tax` besides the `genl` closures,
  as one value compared with `=`: the separating and covering declarations with the
  `siblingDisjointException` pairs that exempt a pair from the separation marks.  A
  declaration moving replaces its kind's value, so an unchanged value compares on
  identity.  The closures that moved are `moves-since`'s."
  [tax]
  (let [t @tax]
    [(:disjoint t) (:disjoint-metatypes t) (:metatype-members t)
     (:sibling-disjoint t) (:partitions t) (:covers t) (:sib-exception-index t)]))

(defn separation-moves
  "The types whose separations can differ between two `separation-inputs` values `old` and
  `new`, as a set: the pair of each `disjoint` and `siblingDisjointException` entry one holds and the
  other does not, the members of a disjoint metatype that moved and each member that
  moved, a `sibling_disjoint` parent that moved, and the parts of a partition that moved.
  A type whose global `genls` hold none of them reads the same separation of every
  partner under both values.  A cover moving separates nothing and adds no type.  Reads
  a member or part set only when the two values hold different ones, and then costs its entries."
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
  "The wholes of the covering declarations one of two `separation-inputs` values `old` and
  `new` holds and the other does not, as a set.  Reads the cover declarations only when the two
  values hold different ones."
  [old new]
  (let [a (nth old 5) b (nth new 5)]
    (if (identical? a b)
      #{}
      (into #{} (filter #(not= (get a %) (get b %))) (concat (keys a) (keys b))))))

(defn- logged-since
  "The members logged under `log-key` of `rel` after generation `gen`, as a set."
  [rel log-key gen]
  (let [ms (get rel log-key)]
    (into #{} (mapcat val) (if (sorted? ms) (subseq ms > gen) (filter #(> (key %) gen) ms)))))

(defn moves-since
  "The lower ends of the edges of relation `rel-key` whose activation or supporting
  contexts moved after generation `gen` (`note-move`), as a set.  A closure that moved
  since `gen` is one of a node at or below one of them.  A relation rebuilt from nothing
  (`clear-relations!`) restarts its generation, and its log holds only what the rebuild
  moved."
  [tax rel-key gen]
  (logged-since (get @tax rel-key) :moves gen))

(defn shrinks-since
  "The lower ends of the edges of relation `rel-key` that left the active set, or whose
  supporting contexts moved, after generation `gen` (`note-shrink`), as a set: the ends
  of `moves-since` that did not only gain edges.  A relation whose log predates the
  shrink log (an image written before it) reads every moved end."
  [tax rel-key gen]
  (let [rel (get @tax rel-key)]
    (if (:shrinks rel)
      (logged-since rel :shrinks gen)
      (moves-since tax rel-key gen))))

(defn grows-since
  "The edges `[a b]` of relation `rel-key` that entered the active set after generation
  `gen` (`note-grow`), as a set, nil when the relation keeps no such log."
  [tax rel-key gen]
  (let [rel (get @tax rel-key)]
    (when (:grows rel) (logged-since rel :grows gen))))

(defn relation-gen
  "The generation counter of a cached relation (`:genl` / `:genlCx`), bumped on
  every edge change.  A caller memoizing something derived from a closure reads this to
  notice it must recompute, without comparing edge sets — which is the whole point,
  since the edge set is the thing that is too big to compare."
  [tax rel-key]
  (get-in @tax [rel-key :gen] 0))

(defn relation-epoch
  "How many times `clear-relations!` has rebuilt `tax`'s relations.  A rebuild restarts
  each `relation-gen` at 0, so a key that must not compare equal across a `recover`
  carries this beside the generations (`special/taxonomy-generations`)."
  [tax]
  (:epoch @tax 0))

;; ---- genl (types) --------------------------------------------------------
;; Each read comes in two: the scoped one walks the edges visible from a context
;; (`visible-ctxs`), and the `-global` one walks every active edge.  A scoped read whose
;; visible set is nil equals the global one, so the two must not share a name.  An empty
;; visible set still walks: an edge with a nil-context supporter constrains everywhere.
;; `lein lint`'s E17 allowlists the `-global` callers.

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

(defn genl-path-edges
  "The `[a b]` edges of one path of active `genl` edges from `sub` up to `super`
  (`genl-path`), held in the closure cache under the relation's `:gen`, or nil when there
  is none."
  [tax sub super]
  (let [t    @tax
        rel  (:genl t)
        lru  (:closure-lru t)
        pk   [:genl (:gen rel) :path sub super]
        held (caches/lru-get lru pk)
        path (if (some? held) held (caches/lru-put! lru pk (or (genl-path rel sub super) ::none)))]
    (when-not (= ::none path) (into [] (partition 2 1 path)))))

(defn genl-asserted-in?
  "Is `sub` at or below `super` through the active edges some supporter asserts from a
  context in the set `ctxs`, with no belief callback?  Membership in `genls-asserted-in`'s
  answer, walked depth-pruned (`reachable-filtered?`) with no closure built, and held in
  the closure cache (docs/taxonomy.md, \"What the pure reads of the hierarchy promise\")."
  [tax sub super ctxs]
  (let [t   @tax
        rel (:genl t)
        lru (:closure-lru t)
        k   [:genl (:gen rel) :asserted-in ctxs sub super]
        hit (caches/lru-get lru k)]
    (if (some? hit)
      hit
      (let [edges (genl-path-edges tax sub super)
            ectx  (:edge-ctxs rel)]
        (caches/lru-put! lru k
                         (boolean
                          (and edges
                               (or (every? (fn [[a b]] (ctxs-visible? (get ectx [a b]) ctxs)) edges)
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
  "The union of what the transducer `xf` makes of each term of `genls-global` of `t`
  (`arity/bound-above` asks which predicates above a functor store a binding).  `memo`, a
  volatile map the caller makes for one `xf` over one still taxonomy, keeps answers by
  component representative.  Nothing enters the closure cache.  A cycle `:scc` has not
  recorded reads the closure."
  [tax t xf memo]
  (let [rel  (:genl @tax)
        scc  (:scc rel)
        node (get scc t t)]
    (or (get @memo node)
        (reach-by-parents node #(get (:fwd rel) %) scc
                          #(get @memo %) #(vswap! memo assoc %1 %2) xf nil)
        (into #{} xf (closure-of tax :genl :fwd t)))))

(defn- union-held
  "The walk `genls-global-union-held` and `specs-global-union-held` share, along the
  `genl` adjacency `dir` (`:fwd` up, `:rev` down)."
  [tax t xf held hold! dir]
  (let [rel  (:genl @tax)
        scc  (:scc rel)
        node (get scc t t)]
    (or (held node)
        (reach-by-parents node #(get (dir rel) %) scc held hold! xf nil)
        (into #{} xf (closure-of tax :genl dir t)))))

(defn genls-global-union-held
  "`genls-global-union` of `t` with the answers by component representative read from
  `(held node)` and handed to `(hold! node answer)`, for a caller keeping them past one
  pass in a store it retires itself: `arity/entry` holds them in a weighted LRU, and the
  ancestors a type shares with one read before are not read again.  An answer held by one
  call is read by the next, so a call whose `xf` makes something else of a term replaces
  the answers it held under the terms that differ."
  [tax t xf held hold!]
  (union-held tax t xf held hold! :fwd))

(defn specs-global-union-held
  "`genls-global-union-held` downward: the union of what `xf` makes of each term of
  `specs-global` of `t`, built from the children's answers, read from `(held node)` and
  handed to `(hold! node answer)` by component representative."
  [tax t xf held hold!]
  (union-held tax t xf held hold! :rev))

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
  caller whose question a subtype answers for every type below it: `arity/drain!` stops
  at a subtype whose own binding gives the length a moved binding gave."
  [tax t enter?]
  (closure-while tax :genl :rev t enter?))

(defn genls-global-meets?
  "Does `genls-global` of `t` hold a term `among` accepts, a set or a predicate?  A walk
  up that returns at the first such term and stores nothing.  `missed`, when given, is a
  volatile set kept by the caller for one `among` over one still taxonomy."
  ([tax t among] (genls-global-meets? tax t among nil))
  ([tax t among missed]
   (let [adj  (get-in @tax [:genl :fwd])
         gone (if missed @missed #{})
         hit? (if (fn? among) among #(contains? among %))]
     (if (contains? gone t)
       false
       (loop [seen (transient #{t}), stack [t]]
         (if-let [n (peek stack)]
           (or (hit? n)
               (let [fresh (remove #(or (get seen %) (contains? gone %)) (get adj n))]
                 (recur (reduce conj! seen fresh) (into (pop stack) fresh))))
           (do (when missed (vswap! missed into (persistent! seen)))
               false)))))))

(defn genls-global-meets-without?
  "Does `t` reach a term of the set `among` up every active `genl` edge but the one from
  `a` to `b`?  A walk up that returns at the first such term and stores nothing."
  [tax t among a b]
  (let [adj (get-in @tax [:genl :fwd])]
    (loop [seen (transient #{t}), stack [t]]
      (if-let [n (peek stack)]
        (or (contains? among n)
            (let [fresh (remove #(or (get seen %) (and (= n a) (= % b))) (get adj n))]
              (recur (reduce conj! seen fresh) (into (pop stack) fresh))))
        false))))

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
  (cond-> (if-some [scope (relation-scope tax rel-key context)]
            (into #{} (visible-neighbours @tax rel-key dir-key scope t))
            (get-in @tax [rel-key dir-key t] #{}))
    (and (= rel-key :genlCx) (= dir-key :fwd)) (->> (with-root-parents t))))

(defn direct-genls
  "The types `t` is a subtype of by **one** `genl` edge of the closure — its direct
  parents, where `genls` is everything those parents in turn reach.  An edge counts
  whatever installed it: a stated `(genl t super)` or a cover declaration naming `t` as a part.

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

(defn- extremal
  "The members of `xs` at one end of the order `above` reads, `above` mapping a node to its
  reflexive up-closure: with `low?` the minimal ones (no other member strictly below),
  without it the maximal ones.  A node is strictly above `t` when it is in `t`'s
  up-closure and `t` is not in its own, so two members above each other both stay.  With
  `member?`, at the maximal end, a node `member?` holds of strikes the members below it,
  and `xs` must hold every maximal such node.  A set.  Fewer than two distinct members, with
  no `member?`, are returned with no `above` read."
  ([above low? xs] (let [among (set xs)] (extremal above low? among among)))
  ([above low? member? xs]
   (let [among (set xs)]
     (if (and (< (count among) 2) (identical? member? xs))
       among
       (let [over    (volatile! (into {} (map (juxt identity above)) among))
             up-of   (fn [t] (or (get @over t) (let [u (above t)] (vswap! over assoc t u) u)))
             ;; the nodes strictly above `t`.  Over a member set the smaller of it and `up`
             ;; is walked, and an element is tested against both: `up` also holds every
             ;; node above `t` that is no member
             supers  (fn [t]
                       (let [up (up-of t)]
                         (into [] (comp (filter #(and (member? %) (contains? up %)))
                                        (remove #(or (= t %) (contains? (up-of %) t))))
                               (if (and (set? member?) (< (count member?) (count up))) member? up))))
             dropped (reduce (fn [acc t]
                               (let [ss (supers t)]
                                 (cond low?     (into acc ss)
                                       (seq ss) (conj acc t)
                                       :else    acc)))
                             #{} among)]
         (reduce disj among dropped))))))

(defn- up-closure-fn
  "The read `extremal` takes as `above`: a node's reflexive up-closure in `rel-key`
  (`:genl` or `:genlCx`) through the edges visible from `context`, or through every
  active edge for a nil `context`."
  [tax rel-key context]
  (if-some [scope (relation-scope tax rel-key context)]
    #(closure-of-vis tax rel-key :fwd % scope)
    #(closure-of tax rel-key :fwd %)))

(defn min-types
  "The minimal members of `types`, a collection of types: the members with no other
  member strictly below them, through the edges visible from `context`.  A set.
  `(min-types tax '[dog mammal animal] c)` is `#{dog}` where `dog ⊂ mammal ⊂ animal`.
  Members that subsume each other both stay; a member that is not a node stays.  No
  closure is read for fewer than two distinct members.  `min-types-global` is the
  unscoped read."
  [tax types context]
  (extremal (up-closure-fn tax :genl context) true types))

(defn max-types
  "The **maximal** members of `types`: the members with no other member strictly above
  them, through the edges visible from `context`.  `min-types`' reasoning, the other
  direction, and `#{animal}` in its example.  `max-types-global` is the unscoped read."
  [tax types context]
  (extremal (up-closure-fn tax :genl context) false types))

(defn min-types-global
  "`min-types` through **every** active edge — no context scope."
  [tax types]
  (extremal (up-closure-fn tax :genl nil) true types))

(defn max-types-global
  "`max-types` through **every** active edge — no context scope."
  [tax types]
  (extremal (up-closure-fn tax :genl nil) false types))

(defn- nearest-of
  "The members of `nbrs`, the one-step neighbours of `node`, that no other member stands
  between.  `ends` reduces a collection of types to one end of the order: `min-types`
  going up (`up?`), `max-types` going down.  `above` maps a type to its reflexive
  up-closure.  A neighbour that subsumes and is subsumed by `node` is kept and not passed
  to `ends`.  Fewer than two neighbours are returned with no read."
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
  minimal parents, the maximal children (`extremal`, which for `:genl` is
  `min-types` / `max-types`), scoped like the relation's closures."
  [tax rel-key dir-key t context]
  (let [up?   (= :fwd dir-key)
        above (up-closure-fn tax rel-key context)]
    (nearest-of above #(extremal above up? %)
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

(defn- common-closure
  "The intersection of `closure` over the distinct members of `types`, a collection of
  types: the smallest closure first, so each step walks a set no larger than the
  answer so far.  `#{}` for an empty `types`."
  [closure types]
  (if-some [sets (seq (sort-by count (map closure (set types))))]
    (reduce set/intersection sets)
    #{}))

(defn common-genls
  "The types that are supertypes of **every** member of `types`, through the edges visible
  from `context`: the intersection of the members' `genls`.  Reflexive, as `genls` is, so
  a member above all the others is in the set, and one type's common genls are its
  `genls`.  A set; `#{}` for an empty `types`.  One memoized up-closure read per distinct
  member.  A nil `context` reads every active edge, as `common-genls-global` does."
  [tax types context]
  (common-closure #(genls tax % context) types))

(defn common-specs
  "The types that are subtypes of **every** member of `types`, through the edges visible
  from `context`: the intersection of the members' `specs`.  Reflexive, as `specs` is.
  `common-genls`' reasoning, the other direction."
  [tax types context]
  (common-closure #(specs tax % context) types))

(defn- minimal-common
  "The body `min-common-genls` and `max-common-specs` share: `extreme` of the one member
  of `types`, else `extremes` of `common` less the members."
  [extreme extremes common tax types context]
  (let [members (set types)]
    (if (= 1 (count members))
      (extreme tax (first members) context)
      (extremes tax (reduce disj (common tax members context) members) context))))

(defn min-common-genls
  "The **minimal** strict common supertypes of `types`, through the edges visible from
  `context`: `min-types` of `common-genls` with the members of `types` removed.  Every
  other type strictly above all the members is above one of these.  For `dog` and `cat`
  under `mammal ⊂ animal` it is `#{mammal}`; for `dog` and `mammal` it is `#{animal}`,
  since a member is never its own answer.  One distinct member is `min-genls` of it,
  exactly.  A set; `#{}` for an empty `types` or for members with no common supertype
  above them.  The cost is one memoized up-closure read per distinct member and one per
  common genl."
  [tax types context]
  (minimal-common min-genls min-types common-genls tax types context))

(defn max-common-specs
  "The **maximal** strict common subtypes of `types`, through the edges visible from
  `context`: `max-types` of `common-specs` with the members of `types` removed.  One
  distinct member is `max-specs` of it, exactly.  `min-common-genls`' reasoning, the other
  direction."
  [tax types context]
  (minimal-common max-specs max-types common-specs tax types context))

(defn common-genls-global
  "`common-genls` through **every** active edge — no context scope."
  [tax types]
  (common-genls tax types nil))

(defn common-specs-global
  "`common-specs` through **every** active edge — no context scope."
  [tax types]
  (common-specs tax types nil))

(defn min-common-genls-global
  "`min-common-genls` through **every** active edge — no context scope."
  [tax types]
  (min-common-genls tax types nil))

(defn max-common-specs-global
  "`max-common-specs` through **every** active edge — no context scope."
  [tax types]
  (max-common-specs tax types nil))

(defn specs-of-all
  "The union of `specs` over every node in `nodes`, walked once with one `seen`.
  Reflexive and unscoped, and not memoized (docs/taxonomy.md, \"What the pure reads of the
  hierarchy promise\")."
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
  walks `sub`'s ancestors on every ask."
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

(defn strict-genl?
  "Is `sub` a strict subtype of `super` through the edges visible from `context`: at or
  below it, and not above it?  Two types in a `genl` cycle are coextensive at a reader that
  sees the cycle, so neither is strictly below the other there."
  [tax sub super context]
  (and (not= sub super) (genl? tax sub super context) (not (genl? tax super sub context))))

(defn genls-among
  "`genls` of `t` from `context` cut to the set `among`: `genls-global-among` over `memo`,
  then each term `genl?` from `context` when a scope applies there, for a caller asking
  many terms about one `among` over one still taxonomy.  A pass costs the `genl` edges
  above its terms once rather than a closure per term."
  [tax t context among memo]
  (let [up (genls-global-among tax t among memo)]
    (if (relation-scope tax :genl context)
      (into #{} (filter #(or (= t %) (genl? tax t % context))) up)
      up)))

;; ---- what a reachability rests on ---------------------------------------
;; A caller that depends on a reachability (a forward firing matched by subsumption,
;; docs/contexts.md) names the sentexes it rests on, so the dependency can be withdrawn.
;; The witness is one path with one supporter per edge, so a second route does not
;; appear and what rested on a departed witness is re-derived from the surviving route
;; (docs/qcn.md).  The choice is keyed on content (neighbours in name order, supporter by
;; asserting context), never on handle id.  Each step reports its supporter's context,
;; and the witness prefers the most general supporter per edge, since a dependant
;; inherits its visibility.  Across paths the witness is the shortest one.

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
  `partition` declaration that installs the edge, that `genl?` from `context` would walk the
  edge through.  Empty when the edge is not active.  Belief is read as `:edge-ctxs` records it, so a caller wanting the
  JTMS's word filters again."
  [tax sub super context]
  (into #{} (map first)
        (visible-edge-supporters @tax :genl [sub super] (relation-scope tax :genl context))))

(defn- most-general-of
  "The most general of `cands` (a non-empty vector of `[handle ctx]`), since its context
  is inherited by whatever depends on the edge.  The asserting context's name orders the
  candidates; the printed sentence each supporter states (the `:supporter-sentence`
  callback) orders two that share a context.  The key is never a handle.  A single
  candidate takes neither ordering nor comparison.  `edge-supporter` and
  `strongest-edge-supporter` narrow to a candidate set and then ask this."
  [tax cands]
  (if (nil? (next cands))
    (nth cands 0)
    ;; keyed through the guarded printer because a context may be a NAT
    (let [sentence (when-not (apply distinct? (map second cands)) (:supporter-sentence @tax))
          ordered  (nm/sort-by-content-key
                    (if sentence
                      (fn [[h c]] [(nm/print-key c) (nm/print-key (sentence h))])
                      (fn [[_ c]] (nm/print-key c)))
                    compare cands)]
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
  "Shortest path `sub ->* super` over neighbours `nbrs`, admitting an edge `[p x]` only
  when `admit?` allows it (asked of an unvisited neighbour only) and mapping each
  traversed edge to a `[handle ctx]` supporter via `witness`.  Returns the vector of
  witnesses (one per edge, `super`-end first), or nil when unreachable or an admitted
  edge's `witness` is nil.  Neighbours expand in the order `nbrs` imposes (name order), so
  the path is a function of the hierarchy.  Past `prune-after` expansions a node is
  expanded only when `@reaches?` holds of it; the path is unchanged."
  [sub super nbrs admit? witness reaches?]
  (let [i    (volatile! 0)
        step (fn [n tree]
               (let [pruned? (>= @i prune-after)]
                 (when-not (and pruned? (not (@reaches? n)))
                   (vswap! i inc)
                   (for [x (filter #(admit? [n %])
                                   (cond->> (remove #(contains? tree %) (nbrs n))
                                     pruned? (filter @reaches?)))]
                     [x n]))))
        {:keys [found tree]} (graph/bfs-tree [[sub nil]] step #(= % super))]
    (when found
      (loop [x found, acc []]
        (if (= x sub)
          acc
          (let [p (get tree x)]
            (when-let [s (witness [p x])]
              (recur p (conj acc s)))))))))

(def ^:private no-route
  "The length `route-length` holds for a type with no admitted path to the target."
  Long/MAX_VALUE)

(defn- route-length
  "The fewest edges `admit?` allows on a path from `n` to the target over `nbrs`, or
  `no-route`, read from and held in the HashMap `lengths`, which holds the target at 0.
  The walk is depth first, enters only types `reaches?` holds of, and holds the length of
  every type it leaves, so a `lengths` kept across walks to one target enters each type
  once.  nil when the walk meets a type it is still inside: a cycle, which a length
  recurrence cannot read."
  [n nbrs admit? reaches? ^java.util.HashMap lengths]
  (or (.get lengths n)
      (let [inside (java.util.HashSet.)
            stack  (java.util.ArrayDeque.)
            step   (fn [d] (if (= no-route d) no-route (inc (long d))))
            enter! (fn [x] (.add inside x) (.push stack (object-array [x (seq (nbrs x)) no-route])))]
        (enter! n)
        (loop []
          (if-let [^objects fr (.peek stack)]
            (let [x (aget fr 0)]
              (if-let [ns (aget fr 1)]
                (let [p (first ns)]
                  (aset fr 1 (next ns))
                  (if-not (admit? [x p])
                    (recur)
                    (if-some [d (.get lengths p)]
                      (do (aset fr 2 (Long/valueOf (min (long (aget fr 2)) (long (step d))))) (recur))
                      (cond
                        (.contains inside p) nil
                        (reaches? p)         (do (enter! p) (recur))
                        :else                (do (.put lengths p no-route) (recur))))))
                (let [d (aget fr 2)]
                  (.pop stack)
                  (.remove inside x)
                  (.put lengths x d)
                  (when-let [^objects up (.peek stack)]
                    (aset up 2 (Long/valueOf (min (long (aget up 2)) (long (step d))))))
                  (recur))))
            (.get lengths n))))))

(defn- routed-witness-path
  "`bfs-witness-path`'s answer read off route lengths held in `lengths`
  (`route-length`), or `::unrouted` when the walk meets a cycle.  The breadth-first walk
  expands neighbours in `nbrs` order, so the path it names is the first of the shortest
  paths in that order: from each type, the first neighbour one edge nearer `super`.  The
  lengths are a function of the admitted edges alone, so a `lengths` kept for one
  `super`, `nbrs` and `admit?` answers every source below it, and the types two sources
  share are entered once."
  [sub super nbrs admit? witness reaches? ^java.util.HashMap lengths]
  (when-not (.containsKey lengths super) (.put lengths super 0))
  (let [d (route-length sub nbrs admit? reaches? lengths)]
    (cond
      (nil? d)          ::unrouted
      (= no-route d)    nil
      :else
      (loop [x sub, d (long d), acc []]
        (if (= x super)
          (into [] (rseq acc))
          (let [p (first (filter #(and (admit? [x %]) (= (dec d) (.get lengths %))) (nbrs x)))]
            (when-let [s (witness [x p])]
              (recur p (dec d) (conj acc s)))))))))

(defn- direct-witness
  "The witness `bfs-witness-path` names from `sub` to `super` over the adjacency `adj` when
  `sub` has an edge straight to `super` that `admit?` allows, or nil for the walk to
  answer.  The walk pops `sub`, queues `super` as the end of that edge, and pops it as the
  end of a one-edge path, so the path is that edge and its witness is `(witness [sub
  super])`; a nil witness is left to the walk."
  [adj sub super admit? witness]
  (when (and (some #(= super %) (adj sub)) (admit? [sub super]))
    (when-let [w (witness [sub super])] [w])))

(defn- reaches-target
  "A test that is false of a type with no path to `super` in relation `rel-key` by the
  potential alone (`reachable?`): a type outside `super`'s component at or above its
  depth.  It is true of some types with no path, for which `route-length` holds
  `no-route` once per `lengths`; it reads no closure."
  [tax rel-key super]
  (let [rel   (get @tax rel-key)
        depth (when-not (:loose? rel) (:depth rel))
        scc   (:scc rel)
        dt    (get depth super)]
    (fn [p]
      (or (nil? dt)
          (> (long (get depth p -1)) (long dt))
          (and (some? (get scc p)) (= (get scc p) (get scc super)))))))

(defn- reach-support*
  "`reach-support`'s walk.  The six- and seven-argument arities call it directly rather
  than one another through the var, so a walk is one call to either of them.  Given a
  `router` (a HashMap), the walk reads the edge ranks, the edge witnesses and the route
  lengths (`routed-witness-path`) held there per relation, scope, threshold and target, so the
  walks one caller asks under one supporter-class reading enter each type once per
  target; a route through a cycle falls back to `bfs-witness-path`."
  [tax rel-key sub super context supporter-class thresholds ^java.util.HashMap router]
  (cond
    (= sub super) []
    (and (= rel-key :genlCx) (implicit-reach? tax sub super))
    (reach-support* tax rel-key root-cx super context supporter-class thresholds router)
    :else
    (let [t   @tax
          rel (get t rel-key)
          scope (relation-scope tax rel-key context)
          ;; nil `vis` is the unscoped walk — every asserting context is visible, so
          ;; the plain adjacency *is* the visible one, exactly as in `genls`
          adj (if (nil? scope) #(get (:fwd rel) %) #(visible-neighbours t rel-key :fwd scope %))
          ;; `nm/print-key` keeps a node that is not a symbol (a NAT) sortable and prints it with the
          ;; bounds released, so an ambient `*print-length*` cannot reorder the adjacency the
          ;; witness path rests on.  Built once per adjacency.
          nbrs (fn [n] (pass-held [::sorted rel-key scope n]
                                  #(nm/sort-by-content-key nm/print-key compare (adj n))))
          ;; the walk enters only types above `sub`, since a scoped adjacency is a subset of the
          ;; global one: a walk down from `super` through `sub`'s global ancestors enters exactly
          ;; those with a path to `super`
          reaches? (delay (let [up      (closure-of tax rel-key :fwd sub)
                                between (closure-while tax rel-key :rev super #(contains? up %))]
                            #(contains? between %)))
          held    (fn [k make] (or (.get router k) (let [v (make)] (.put router k v) v)))
          target  (when router (delay (reaches-target tax rel-key super)))
          walk    (fn [threshold admit? witness]
                    (let [r (when router
                              (routed-witness-path sub super nbrs admit? witness @target
                                                   (held [::lengths rel-key scope threshold super]
                                                         #(java.util.HashMap.))))]
                      (if (or (nil? router) (= ::unrouted r))
                        (bfs-witness-path sub super nbrs admit? witness reaches?)
                        r)))
          direct #(direct-witness adj sub super %1 %2)]
      ;; a walk from a source with no edge it sees finds no path
      (cond
        (empty? (adj sub))     nil
        (nil? supporter-class)
        (let [witness #(edge-supporter tax t rel-key % scope)]
          (or (direct (fn [_] true) witness)
              (walk nil (fn [_] true) witness)))
        :else
        ;; each edge's class read once for both thresholds, and once per router
        (let [^java.util.HashMap ranks (if router
                                         (held [::ranks rel-key scope] #(java.util.HashMap.))
                                         (java.util.HashMap.))
              rank  (fn [e]
                      (or (.get ranks e)
                          (let [r (strength/rank-of (edge-class t rel-key e scope supporter-class))]
                            (.put ranks e r)
                            r)))
              admit (fn [threshold] (fn [e] (>= (long (rank e)) (long (strength/rank-of threshold)))))
              witness (fn [e] (if router
                                (let [^java.util.HashMap ws (held [::witnesses rel-key scope] #(java.util.HashMap.))]
                                  (if (.containsKey ws e)
                                    (.get ws e)
                                    (let [w (strongest-edge-supporter tax t rel-key e scope supporter-class)]
                                      (.put ws e w)
                                      w)))
                                (strongest-edge-supporter tax t rel-key e scope supporter-class)))]
          ;; the first threshold's walk is the one an edge straight to `super` ends
          (or (direct (admit :monotonic) witness)
              (some (fn [threshold] (walk threshold (admit threshold) witness))
                    thresholds)))))))

(defn reach-support
  "A witness for `sub ->* super` in relation `rel-key`, as the `[handle ctx]` of one
  supporter per edge along a single path, or nil when `context` sees no such path.  Empty
  for `sub` = `super`.  A nil `context` walks unscoped.  It walks the same visible
  adjacency as the scoped closure reads, so it finds a witness exactly for the pairs
  `genl?` answers true.  Neighbours expand in name order.  Without `supporter-class` it is
  breadth-first, a shortest path, each edge naming its most general supporter
  (`edge-supporter`).  With `supporter-class` (a `handle -> defeat-class` read) it is a
  widest-bottleneck path: each defeat class is tried as a threshold, highest first, and
  the first shortest path whose edges all clear it is taken, each edge naming its
  strongest supporter (`strongest-edge-supporter`).  `thresholds` names the classes tried
  (`[:monotonic]` walks no second pass; `monotonic-route-witness`)."
  ([tax rel-key sub super context] (reach-support tax rel-key sub super context nil))
  ([tax rel-key sub super context supporter-class]
   (reach-support* tax rel-key sub super context supporter-class [:monotonic :default] nil))
  ([tax rel-key sub super context supporter-class thresholds]
   (reach-support* tax rel-key sub super context supporter-class thresholds nil))
  ([tax rel-key sub super context supporter-class thresholds router]
   (reach-support* tax rel-key sub super context supporter-class thresholds router)))

(defn context-specificity
  "How specific context `c` is, as the size of its `genlCx` ancestor set; 0 for a supporter
  with no recorded context, which is seen from everywhere.  A context strictly below
  another has the larger ancestor set, so the number orders every comparable pair the way
  `sees?` does, and gives the incomparable ones one total order to be tie-broken in.
  A function of the topology alone, so no arrival order reaches it."
  [tax c]
  (if (nil? c) 0 (count (closure-of tax :genlCx :fwd c))))

;; ---- every route a reader can hold a dependant through --------------------
;; A witness names one route, which decides where a dependant is placed.  The searches
;; below return every route no other route covers: R1 covers R2 when each of R1's contexts
;; is seen from one of R2's (`floor-covers?`).  A caller places a dependant once per
;; returned route.  Where every edge is stated in contexts one reader sees, one route
;; covers the rest (docs/inherit.md).

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
  "Every route `start ->* goal` whose label no other route's covers (`covers?`), as a
  vector of routes, each the `[handle ctx]` supporters along it with the `goal` end first.
  `[[]]` when `start` is `goal`; `[]` when no route exists.  `step` maps a node to its
  outgoing steps `[next [handle ctx] rank hid?]` in content order, with an optional fifth
  element, the supporter's content key.  `rank` is the supporter's strength rank or nil, and
  `hid?` is true when an except can hide the supporter.  A route's label is its weakest
  rank, the floor of its supporters' contexts (`context-floor`) and its hidable
  supporters; a partial route a held label covers is dropped.  The queue order is total
  (`trail-order`), so the kept route is a function of content.  `goal` is a node, or a
  predicate a node satisfies.  See docs/inherit.md."
  [tax start goal step]
  (if (if (fn? goal) (goal start) (= start goal))
    [[]]
    (let [pq       (java.util.PriorityQueue. 16 ^java.util.Comparator
                                             (fn [a b] (let [c (compare (nth a 0) (nth b 0))]
                                                         (if (zero? c) (trail-order (nth a 5) (nth b 5)) c))))
          ;; a walk meets few distinct labels, so a label carries its own queue key; `one?` holds
          ;; while every label built is the first one, and a route found then covers every entry
          ;; still queued
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

                (if (fn? goal) (goal node) (= node goal))
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

(defn edge-steps
  "`step` for `uncovered-routes` over relation `rel-key` as `context` sees it: from a
  node, each visible neighbour once per visible supporter of the edge that no other visible
  supporter covers.  `dir-key` `:fwd` steps along the edges and `:rev` against them.  With
  `supporter-class` each supporter carries its strength rank; with `hidable` (`handle ->
  boolean`) each supporter an except can hide is marked; with the class `floor`, only the
  supporters `supporter-class` reads at least that strong.  Built eagerly into a vector, and
  a node's sorted neighbours are held for a reading pass under `reach-support`'s key
  (`pass-held`)."
  ([tax rel-key context supporter-class hidable]
   (edge-steps tax rel-key context supporter-class hidable :fwd nil))
  ([tax rel-key context supporter-class hidable dir-key]
   (edge-steps tax rel-key context supporter-class hidable dir-key nil))
  ([tax rel-key context supporter-class hidable dir-key floor]
   (let [t     @tax
         rel   (get t rel-key)
         scope (relation-scope tax rel-key context)
         adj   (if (nil? scope) #(get (dir-key rel) %) #(visible-neighbours t rel-key dir-key scope %))
         e-of  (if (= :fwd dir-key) (fn [n n2] [n n2]) (fn [n n2] [n2 n]))
         rank  (when supporter-class
                 #(strength/rank-of (or (supporter-class %) :default)))
         hid?  (if hidable #(boolean (hidable %)) (constantly false))
         label (fn [[h c]] [(when rank (rank h)) (if (nil? c) #{} #{c}) (when (hid? h) #{h})])
         step  (fn [acc n2 w] (conj! acc [n2 w (when rank (rank (nth w 0))) (hid? (nth w 0))]))]
     (fn [node]
       (persistent!
        (reduce (fn [acc n2]
                  (let [cands (cond->> (visible-edge-supporters t rel-key (e-of node n2) scope)
                                floor (filterv #(>= (long (rank (nth % 0))) (strength/rank-of floor))))]
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
                (pass-held [::sorted rel-key dir-key scope node]
                           #(nm/sort-by-content-key nm/print-key compare (adj node)))))))))

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
  "Every witness for `sub ->* super` in `rel-key` that `context` sees and no other witness
  covers (`uncovered-routes`), each the `[handle ctx]` of one supporter per edge along a
  single path.  `[[]]` for `sub` = `super`; `[]` when `context` sees no path.  A route
  through general contexts covers a shorter one through a specific context, and routes
  whose contexts neither sees are each returned.  Ties are settled on content, never a
  handle (docs/nmtms.md)."
  [tax rel-key sub super context]
  (every-uncovered-route tax sub super (edge-steps tax rel-key context nil nil)))

(defn reach-supports
  "Every witness for `sub →* super` in `rel-key` that `context` sees and no other witness
  covers, weighing the defeat class of each supporter (`supporter-class`) beside its
  context: a route covers another only if its floor class is at least as strong and it
  is seen wherever the other is.  The routes a placement that has to descend below the
  firing's other ingredients chooses among (`chain/placement-ingredients`).  With
  `hidable` (`handle → boolean`), a route resting on a supporter an except can hide
  covers only the routes resting on that supporter too.  With the class `floor`, only the
  routes every supporter of which reads that strong, which no weaker route covers."
  ([tax rel-key sub super context supporter-class]
   (reach-supports tax rel-key sub super context supporter-class nil nil))
  ([tax rel-key sub super context supporter-class hidable]
   (reach-supports tax rel-key sub super context supporter-class hidable nil))
  ([tax rel-key sub super context supporter-class hidable floor]
   (every-uncovered-route tax sub super
                          (edge-steps tax rel-key context supporter-class hidable :fwd floor))))

(defn reach-strength
  "The defeat class of the strongest route `sub ->* super` in `rel-key` that `context`
  sees: `:monotonic`, `:default`, or nil when unreachable.  `:monotonic` for `sub` = `super`.
  `supporter-class` is the read `reach-support` takes.  Derived from `reach-support`'s
  widest-bottleneck path (docs/taxonomy.md, \"Strength of a subsumption path\")."
  [tax rel-key sub super context supporter-class]
  (if (= sub super)
    :monotonic
    (when-let [path (reach-support tax rel-key sub super context supporter-class)]
      (reduce (fn [floor [h _]] (strength/min floor (or (supporter-class h) :default)))
              :monotonic path))))

(def ^:dynamic *exposure-instance-budget*
  "How many candidate instances one bounded merge sweep will enumerate:
  `vaelii.impl.special/equate-under-context-edge` and the sweep a revived `genl` edge
  under a merge mark runs (`special/revived-declaration-sweeps`).  A sweep cut short files
  a `:context-edge-exposure-truncated` or `:genl-edge-revival-truncated` violation.  The
  cap selects a handle-ordered prefix, so past it the order dependence is in whether a
  merge is derived at all (docs/defenses.md; docs/nmtms.md for the cap's value)."
  8192)

;; ---- genlCx (contexts) ---------------------------------------------------

(defn context-up-global
  "Contexts `c` inherits from through the active genlCx cache, with no `except` holes:
  the unscoped read, which exception evaluation uses.  Every other caller wants
  `context-up` (docs/contexts.md)."
  [tax c]
  (closure-of tax :genlCx :fwd c))

(defn context-down-global
  "Contexts that inherit from `c`, incl `c`, through the active genlCx cache, with **no**
  `except` holes: `context-down`'s unscoped read, for `context-up-global`'s callers."
  [tax c]
  (closure-of tax :genlCx :rev c))

(defn context-routed-global
  "The contexts joined to `c` by stored `genlCx` edges in direction `dir-key` (`:fwd` up,
  `:rev` down), unscoped, less CxUniverse: `reach-support` takes the implicit edge to
  CxUniverse, so it names no supporter for a path there."
  [tax dir-key c]
  (disj (stored-closure-of tax :genlCx dir-key c) root-cx))

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
  "The minimal contexts `c` inherits from: the contexts `c` reaches over one `genlCx` edge
  with no other such context strictly below them.  `min-genls` over `genlCx`, read as
  `context-up` reads, after the `except` holes `c` reads (`relation-scope`).  Not
  reflexive.  One memoized up-closure read per direct parent."
  [tax c]
  (nearest-neighbours tax :genlCx :fwd c c))

(defn max-context-children
  "The maximal contexts that inherit from `c`: the contexts that reach `c` over one
  `genlCx` edge with no other such context strictly above them.  `max-specs` over `genlCx`,
  and `min-context-parents`' reverse.  While some `except` targets a `genlCx` supporter
  (`relation-filter-active?`) each direct child is judged by its own `min-context-parents`;
  otherwise the raw adjacency is the answer (docs/contexts.md)."
  [tax c]
  (if-not (relation-filter-active? @tax :genlCx)
    (nearest-neighbours tax :genlCx :rev c nil)
    (into #{}
          (filter #(contains? (min-context-parents tax %) c))
          (context-children-global tax c))))

(defn- up-besides
  "The contexts `c` inherits from, incl `c`, over the `genlCx` edges effective in `scope`
  (`relation-scope`; the active adjacency when nil) but the edge `[sub super]` and every
  edge `usable?` refuses.  The implicit edge to CxUniverse stays, so an edge to CxUniverse
  moves no context.  A walk that comes back to `c` has found a cycle, whose members already
  see what the edge shows, and answers `#{c}`."
  [t scope c [sub super] usable?]
  (let [up1 (fn [n] (with-root-parents
                      n (filter #(and (not (and (= n sub) (= % super))) (usable? n %))
                                (if (some? scope)
                                  (visible-neighbours t :genlCx :fwd scope n)
                                  (get-in t [:genlCx :fwd n] #{})))))]
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

(def ^:private move-gain-readers
  "The most readers under a moved edge's `sub` that `context-move`'s `:gains` splits by
  what each gains: one walk up each, so past this many the move reads `:gains` nil and
  its sweeps read the whole of `:below`."
  1024)

(defn- move-gains
  "`context-move`'s `:gains` and `:displaced` over the snapshot `t`, as `{:groups
  :displaced :seen}`, or nil past `move-gain-readers`.  `:groups`: the readers of `under`
  that see a context through the edge `[sub super]` alone, grouped by that set, as `[{:gain
  G :readers R :seen S :below B} …]` in content order of the gain: `G` the contexts each
  reader of `R` sees now and not without the edge and the edges of `off` (the others moved
  with it), `S` the contexts a reader of `R` sees now, `B` the part of `S` that `up` does
  not hold.  `:displaced`: the contexts of `under` where a placement can lose its place to
  a more general one (`special/surplus-placements`), assuming no `except` hides an
  ingredient.  `:seen`: the contexts the readers of `under` see now."
  [t under up edge off usable?]
  (when (<= (count under) move-gain-readers)
    (let [fwd     (get-in t [:genlCx :fwd])
          off     (conj (set off) edge)
          memo    (fn [f] (let [m (volatile! {})]
                            (fn [r] (or (get @m r) (let [v (f r)] (vswap! m assoc r v) v)))))
          after   (memo (fn [r] (graph/reach-all [r] #(with-root-parents % (get fwd % #{})))))
          without (memo (fn [r] (graph/reach-all [r] (fn [n] (filter #(and (not (contains? off [n %]))
                                                                           (usable? n %))
                                                                     (with-root-parents n (get fwd n #{})))))))
          gain    (fn [r] (into #{} (remove (without r)) (after r)))
          by-gain (reduce (fn [acc r]
                            (let [s (after r)
                                  g (gain r)]
                              (if (empty? g)
                                acc
                                (update acc g (fn [e] (-> (or e {:readers #{} :seen #{}})
                                                          (update :readers conj r)
                                                          (update :seen into s)))))))
                          {} under)
          gainers (into #{} (comp (map (comp :readers val)) cat) by-gain)
          moves?  (fn [p]
                    (let [ap (after p)
                          wp (without p)
                          gp (gain p)
                          cs (filter #(and (not= % p) (or (contains? gp %) (contains? gainers %))) ap)
                          k  (into #{} (comp (mapcat after) (filter wp)) cs)]
                      (and (seq k)
                           (not-any? #(and (not= % p) (every? (without %) k)) k))))]
      {:groups    (->> by-gain
                       (map (fn [[g {:keys [readers seen]}]]
                              {:gain g :readers readers :seen seen :below (into #{} (remove up) seen)}))
                       (sort-by #(mapv term-key (sort-by term-key (:gain %))))
                       vec)
       :displaced (into #{} (filter moves?) under)
       :seen      (into #{} (mapcat after) under)})))

(defn context-move
  "What the move of the `genlCx` edge `[sub super]` (stored, removed or flipped in label)
  shows or hides, read from the taxonomy as it stands: the contexts some reader under `sub`
  sees through the edge and no other route.  `except-ctxs` holds the contexts stating an
  `except` that reaches a `genlCx` supporter's support (`exc/genlCx-except-contexts`);
  `usable?` refuses an edge the walks without the edge must not cross.  Keys: `:raw` (the
  global stratum), `:moved` (per reader class, `reader-classes`), `:shown` / `:hidden`,
  `:readers`, `:up`, and the delays `:under`, `:seen`, `:below`, `:gained-below`, `:gains`
  and `:displaced` (`move-gains`; both nil while an `except` reaches a `genlCx` supporter,
  and past `move-gain-readers`).  See docs/contexts.md, \"One context move\"."
  ([tax sub super except-ctxs usable?] (context-move tax sub super except-ctxs usable? nil))
  ([tax sub super except-ctxs usable? off]
   (let [t       @tax
         edge    [sub super]
         active? (contains? (get-in t [:genlCx :fwd sub] #{}) super)
         up      (conj (set (context-up-global tax super)) super)
         raw     (into #{} (remove (up-besides t nil sub edge usable?)) up)
         under   (delay (set (context-down-global tax sub)))
         ;; one walk up from all of `under`: a union of each member's cached ancestor set
         ;; costs |under| × |ancestors|, cubic over a chain of moves in one pass
         seen    (delay (let [fwd (get-in @tax [:genlCx :fwd])]
                          (graph/reach-all @under #(with-root-parents % (get fwd % #{})))))
         below   (delay (into #{} (remove up) @seen))
         walk    (delay (when (empty? except-ctxs) (move-gains t @under up edge off usable?)))
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
      :gains   (delay (:groups @walk))
      :displaced (delay (some-> @walk (dissoc :groups)))
      :up      up
      :under   under
      :seen    seen
      :below   below
      :gained-below
      (cond
        (root-context? super) (delay #{})
        (seq except-ctxs) below
        :else
        (delay (let [{:keys [fwd rev]} (:genlCx @tax)
                     off?    (fn [a b] (and (= a sub) (= b super)))
                     ;; the contexts that reach `super` without the edge, `super` included
                     kept    (graph/reach-all [super] (fn [n] (filter #(and (not (off? % n)) (usable? % n))
                                                                      (get rev n #{}))))
                     gainers (remove kept @under)]
                 (into #{} (remove up)
                       (graph/reach-all gainers (fn [n] (remove #(off? n %) (with-root-parents n (get fwd n #{})))))))))})))

(defn context-down
  "Contexts that inherit from `c`, including `c`, after context-visible genlCx
  exceptions.  While some `except` targets a `genlCx` supporter (`relation-filter-active?`)
  the raw candidates are filtered by each candidate's own forward answer, memoized per
  context and reading (`*network-belief*`, `*search*`) and keyed by the change clock;
  otherwise the raw closure is the answer.  At CxUniverse the raw closure is the answer:
  no `except` removes the implicit edge."
  [tax c]
  (let [raw (closure-of tax :genlCx :rev c)
        t   @tax]
    (if (or (root-context? c) (not (relation-filter-active? t :genlCx)))
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
  (or (reachable-in? tax :genlCx sub super) (implicit-reach? tax sub super)))

(defn genlCx-stored?-global
  "Does context sub reach context super over the stored active edges alone, without the
  implicit edge to CxUniverse?  `wff` refuses a `genlCx` edge that closes a stored cycle
  with it."
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
  (if (root-context? c)
    (set xs)
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
      (into #{} (filter #(or (contains? up %) (genlCx?-global tax % c) (shares? %))) xs))))

(defn sees? "Does context k see assertions in context y?" [tax k y]
  (or (if-some [scope (relation-scope tax :genlCx k)]
        (let [t   @tax
              rel (:genlCx t)]
          (reachable-filtered? k y t :genlCx scope
                               (when-not (:loose? rel) (:depth rel))
                               (:scc rel)))
        (reachable-in? tax :genlCx k y))
      (and (rooted? k) (sees? tax root-cx y))))

(defn seeing-member
  "The member of `ctxs` that sees every other member, or nil.  It is a maximal common
  descendant; two members that see each other tie by `term-min` (docs/contexts.md,
  \"Context placement of justifications\")."
  [tax ctxs]
  (let [seers (filter (fn [k] (every? #(sees? tax k %) ctxs)) ctxs)]
    (when (seq seers) (term-min seers))))

(defn- placement-rep
  "The one context that stands for `k`'s mutually-visible group (`term-min`), or `k` when it
  is in no cycle.  Applied to both exits of its callers (docs/contexts.md)."
  [tax k]
  (get (:scc (:genlCx @tax)) k k))

(defn- common-descendant-set
  "Every context that sees all of `cs` — the intersection of the down closures,
  stopping at the first empty intermediate rather than intersecting the rest into
  nothing.  CxUniverse is dropped first, since every context sees it; `cs` holding
  CxUniverse alone answers `#{CxUniverse}`, the one member a caller can place at."
  [tax cs]
  (let [cs' (remove root-context? cs)]
    (cond
      (seq cs') (reduce (fn [acc c]
                          (let [i (set/intersection acc (context-down tax c))]
                            (if (seq i) i (reduced i))))
                        (context-down tax (first cs')) (rest cs'))
      (seq cs)  #{root-cx}
      :else     #{})))

(defn max-cxs
  "The maximal (most general) contexts in `ctxs` under the current visibility relation,
  for a set the caller already filtered: `extremal` over each one's `context-up`, each
  survivor collapsed to its cycle's one name (`placement-rep`).  With `member?`, any
  context `member?` holds of strikes one below it (`extremal`).  See docs/contexts.md."
  ([tax ctxs] (let [s (set ctxs)] (max-cxs tax s s)))
  ([tax ctxs member?]
   (into #{} (map #(placement-rep tax %)) (extremal #(context-up tax %) false member? ctxs))))

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
  one-context fast exit does not answer.  The answer is a function of the context set,
  the `genlCx` relation and its supporters' visibility under the reading
  (`*network-belief*`, `*search*`), so a reading pass holds it under those
  (`pass-held`)."
  [tax ctxs]
  ;; `into []` with the transducer: `clojure.core/distinct`'s seq arity throws on a set
  (let [cs (into [] (distinct) ctxs)]
    (pass-held
     [::maximal-common-descendants (set cs) *network-belief* *search*]
     #(if-let [k (seeing-member tax cs)]
        #{(placement-rep tax k)}
        (if (relation-filter-active? @tax :genlCx)
          ;; an except on a `genlCx` supporter hides edges the raw adjacency still holds,
          ;; which the walk would pass through
          (max-cxs tax (common-descendant-set tax cs))
          (let [cs    (into [] (remove root-context?) cs)
                downs (mapv (fn [c] (context-down tax c)) cs)
                in?   (fn [k] (every? (fn [d] (contains? d k)) downs))
                c0    (nth cs (apply min-key (fn [i] (count (nth downs i))) (range (count cs))))]
            (max-cxs tax (descendant-frontier tax c0 in?) in?)))))))

(defn maximal-common-descendant-contexts
  "The maximal elements of the common descendants of `ctxs` (the contexts K with each ctx
  in up(K)), as a set: possibly empty, possibly several.  Places a forward-derived sentex
  given the contexts of the rule and its antecedent facts.  Early exits: a member that sees
  every other (`seeing-member`), and an intersection that empties.  Mutually visible
  contexts collapse to one by `term-min`.  See docs/contexts.md."
  [tax ctxs]
  (let [c0 (first ctxs)]
    (if (and observe/*chain-fast-paths*
             (some? c0)
             (every? #(= c0 %) (next ctxs)))
      ;; every member is the one context: the general path's `seeing-member` answer, without
      ;; building the distinct vector.  `placement-rep` still runs.
      #{(placement-rep tax c0)}
      (maximal-common-descendants* tax ctxs))))

(defn common-descendants
  "Every context that sees all of `ctxs` — the intersection of their down closures.
  The set `maximal-common-descendant-contexts` takes the maxima of, for a caller that
  needs to ask something *of each member* rather than only where the most general ones
  are (`clashes/exposed-clashes` asks each whether it can prove a disjointness)."
  [tax ctxs]
  (common-descendant-set tax (into [] (distinct) ctxs)))

(defn common-descendant?
  "Does any context see every member of `ctxs` — is the common-descendant-set
  non-empty?  The boolean of `maximal-common-descendant-contexts`, for the callers
  that only ever ask existence (`settle`'s nogood pairing asks it of every opposed
  belief pair): the maximality filter never runs, the comparable case never reads a
  closure, and the fallback intersection stops at the first empty."
  [tax ctxs]
  ;; `into []` with the transducer, for `maximal-common-descendants*`'s reason
  (let [cs (into [] (distinct) ctxs)]
    (boolean (and (seq cs)
                  (or (seeing-member tax cs)
                      (seq (common-descendant-set tax cs)))))))

(defn meet-closure
  "`ctxs` closed under `maximal-common-descendant-contexts` of its pairs: every context
  where two or more of them meet, plus the members.  Fewer than two contexts close with no
  read.  See docs/contexts.md."
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
;; `(siblingDisjointException x y)` exempts the pair `x`,`y` from a `partition` /
;; `separating` declaration naming both, a `disjoint_metatype` and a `sibling_disjoint`
;; parent.  A stated `(disjoint x y)` is not exempted, and an `orthogonal` exempts nothing.
;; The exemption is read where a separation is, against the separated pair of supertypes,
;; so it lifts what the separation reached below them too.  Keyed as an unordered pair
;; like `disjoint`, belief-following through `cache-install` / `cache-uninstall`, and
;; read by `exemption` at the reader inside `disjointness-test`.

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
  disjoint metatype: the two separating declarations, the two marks and an exception."
  '#{partition separating disjoint_metatype sibling_disjoint siblingDisjointException})

(defn stored-disjoint-metatype?
  "Whether some stored sentex marks `m` a disjoint metatype, believed or not: the
  supporter family under `[:metatype m]` counts one.  The presence check the member arms
  read (`special/structural-integrate`), on storage rather than belief so that belief can
  follow a recorded membership through `refresh-cache-support`."
  [tax m]
  (pos? (long (reads/stored-supporter-count-global (:index @tax) [:metatype m]))))
(defn stored-disjoint-metatypes
  "Every metatype some stored sentex marks, believed or not — the set
  `special/post-taxonomy-supporters!`' member pass walks, so a defeated mark's members are
  posted exactly as the live member arm posts them."
  [tax]
  (stored-metatypes @tax))

;; A metatype's members are recorded, not materialized: `(disjoint_metatype M)` would
;; otherwise write n(n-1)/2 `(disjoint a b)` sentexes with no justification to M.
;; Membership is cached here and `disjoint?` consults it, so retracting M releases every
;; pair and retracting `(M T)` releases T's pairs (docs/taxonomy.md, "Disjointness").

(defn add-metatype-member
  ([tax m t handle] (add-metatype-member tax m t handle nil))
  ([tax m t handle ctx] (add-supported tax [:member m t] handle ctx)))
(defn del-metatype-member! [tax m t handle] (del-supported! tax [:member m t] handle))
(defn metatype-members [tax m] (get-in @tax [:metatype-members m] #{}))

;; ---- sibling disjointness ------------------------------------------------
;; `(sibling_disjoint C)` separates any two specializations of `C` unless one is a genl
;; of the other.  Only the mark is stored; the pairs are read off `specs` in
;; `separation-frame`, so `unmark` is the plain `cache-uninstall` `del-disjoint!` uses
;; and not `forget-metatype`.  It makes no coverage claim (docs/taxonomy.md).

(defn mark-sibling-disjoint
  ([tax c handle] (mark-sibling-disjoint tax c handle nil))
  ([tax c handle ctx] (add-supported tax [:sib-disjoint c] handle ctx)))
(defn unmark-sibling-disjoint! [tax c handle] (del-supported! tax [:sib-disjoint c] handle))
(defn sibling-disjoints [tax] (:sibling-disjoint @tax))

;; ---- covering: the parts that exhaust a whole ----------------------------
;; The part list of `(covering W P1 P2 …)` / `(partition W P1 P2 …)` is recorded here
;; and not expanded: `separation-frame` reads a partition's separation as it reads a
;; metatype's members, and `provers/CoveringProver` owns the coverage inference.  The
;; `genl` edge each part owes the whole is installed by the integrate arm against the
;; covering sentex's handle.

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
  (`separating-kind?`).  The table `separation-frame` reads its parts arm off, and the
  fourth way this KB spells disjointness: a caller asking whether the KB separates any two
  types at all has to read it beside `disjoint-pairs`, `disjoint-metatypes` and
  `sibling-disjoints`."
  [tax] (:partitions @tax))

(defn coverings
  "Every declaration whose parts exhaust its whole, as `{whole #{[parts kind]}}` — the
  `covering` and `partition` spellings, and not `separating` (`covering-kind?`).  The
  table a cover refutation is convicted against (`checks/cover-problem`)."
  [tax] (:covers @tax))

(defn covers-naming
  "Every **covering** declaration naming `part` among its parts, as `[whole parts kind]`.
  Empty for every type no cover mentions, which is the lookup `CoveringProver` declines
  on — and empty for a `separating` declaration, which claims no coverage to infer from."
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

(defn covers-over-global-fn
  "`(fn [t])` → `covers-over` of `t` unscoped, for a caller asking it of many types over
  one still taxonomy: the wholes above `t` are read by `genls-global-among` over one memo
  the fn holds, so a type's closure is not built, and an ancestor two types share is read
  once.  The memo is dropped when the `genl` relation or the stored covers move."
  [tax]
  (let [memo (volatile! nil)]
    (fn [t]
      (let [{:keys [covers genl]} @tax]
        (if (empty? covers)
          []
          (let [[c g among m] @memo
                [among m]     (if (and (identical? c covers) (identical? g genl))
                                [among m]
                                (let [fresh [(set (keys covers)) (volatile! {})]]
                                  (vreset! memo (into [covers genl] fresh))
                                  fresh))]
            (into [] (mapcat (fn [whole] (map (fn [[parts _]] [whole parts]) (get covers whole))))
                  (genls-global-among tax t among m))))))))

(defn- separable-terms
  "The types a separation can reach another through: those declared disjoint from
  something, the members of a disjoint metatype, the sibling-disjoint parents and the
  parts of a partition.  `separation-frame` reads nothing of a supertype outside it but
  the sibling arm's chain.  Held in the closure cache under the separation inputs, so the
  declarations are read once per value of the inputs."
  [tax inputs]
  (let [t   @tax
        lru (:closure-lru t)
        k   [:separable-terms inputs]]
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
  `genl` generation and the separation inputs and weighed by the terms each holds.  Most
  types sit under no separable type, so a frame over every type of a large KB costs the
  edges and an empty set a type, where a closure a type overran the cache.  A build
  handed back (a cycle `:scc` has not recorded, a parent's cut evicted) cuts the closure."
  [tax a]
  (let [t     @tax
        rel   (:genl t)
        lru   (:closure-lru t)
        sep   (separation-inputs tax)
        terms (separable-terms tax sep)
        key   (fn [n] [:genl (:gen rel) :separable sep n])
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
  as a set: the lower end of each `genl` edge it installs (`installed-edges`) whose upper end
  is `separable?`, the types a stated `disjoint`, `siblingDisjointException` or
  `sibling_disjoint` mark names, the parts of a `partition` or `separating` declaration, the
  members of a `disjoint_metatype` mark, and for a membership in a disjoint metatype the
  type it names and the metatype's members.  The sentence twin of `separation-ends`;
  taxonomy reads alone."
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
  "`genls-at` of `a` from `context` cut to `separable-terms`, or a superset holding no
  other separable type: what a scoped `separation-frame` and `disjointness-test` read of a
  type's supertypes.  Built from the parents' cuts through the edges `context` sees
  (`reach-by-parents`, `intact-scc`).  An ancestor set (a set `context`) is held in the
  closure cache under the relation's `:gen` (`separable-genls`); a concrete context
  answers the scoped closure.  A type whose build hands back answers the scoped closure
  uncut, and the hand back is remembered."
  [tax a context]
  (let [scope (cond (set? context)            context
                    (scoped-context? context) (relation-scope tax :genl context))
        sep   (separation-inputs tax)
        terms (separable-terms tax sep)
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
            key  (fn [n] [:genl (:gen rel) :separable-at scope sep n])
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
  `a`'s supertype closure read cut to the types a separation can reach through
  (`separable-genls`, `separable-genls-at` scoped; whole only for the sibling arm), the
  supertypes of `a` declared disjoint from something (`:seps`), the metatypes some supertype
  of `a` belongs to (`:metas`), and the visibility predicates its context imposes.  When
  `:seps` and `:metas` are empty no candidate is looked at.  `disjointness-test` and
  `separating-partners` read the one frame so they cannot disagree.  A nil, variable or
  unscoped `context` gives constantly-true visibility predicates that take no key."
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
        ;; can separate `a` from nothing, so it leaves the metatype set here rather than
        ;; being re-examined per candidate
        metas (into []
                    (keep (fn [m]
                            (let [ms (get members m)]
                              (when (and (seq ms) (meta-vis? m))
                                (let [in-a (filterv #(and (contains? as %) (member-vis? m %)) ms)]
                                  (when (seq in-a) [m ms in-a]))))))
                    (:disjoint-metatypes t))
        ;; the sibling-disjoint parents `a` sits under, each as `[c under-c? below-a]`: the parent,
        ;; a test of whether a type is a specialization of `c` (read off the type's own supertype
        ;; closure), and the specializations of `c` that are supertypes of `a`.  Empty unless a
        ;; marked parent stands above `a`.
        sibs  (into []
                    (keep (fn [c]
                            (when (and (contains? as c) (sib-vis? c))
                              (let [under-c? (fn [x]
                                               (contains? (genls-at tax x context) c))
                                    below-a  (filterv #(and (not= % c) (under-c? %)) @all-as)]
                                (when (seq below-a) [c under-c? below-a])))))
                    (:sibling-disjoint t))
        ;; the partitions holding some supertype of `a`, each as `[parts above-a key]`: a
        ;; metatype's member set under another name, empty unless a partition names a
        ;; supertype of `a`
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
       ;; genl-relatedness is read globally, as `wff/disjoint-problems` reads it for an explicit
       ;; pair: a scoped read would let a descendant context that cannot see an `(genl x y)`
       ;; edge separate a pair the whole KB knows overlaps.  `exempt?` sits behind the `not=` /
       ;; `genl-related?` guards and is read by the three mark arms, never by a stated `disjoint`.
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
                  ;; a metatype separates when it holds a supertype of `a` and a different supertype of `b`,
                  ;; driven from the members, not from `as × bs`
                  (some (fn [[m ms in-a]]
                          (let [in-b (filterv #(and (contains? bs %) (member-vis? m %)) ms)]
                            (some (fn [x]
                                    (some #(and (not= x %) (not (genl-related? x %))
                                                (not (exempt? x %)))
                                          in-b))
                                  in-a)))
                        metas)
                  ;; a sibling-disjoint parent `c` separates when a supertype of `a` and a different,
                  ;; non-genl-related, non-exempted supertype of `b` are both proper specializations of `c`
                  (some (fn [[c under-c? below-a]]
                          (let [below-b (filterv #(and (not= % c) (under-c? %)) @all-bs)]
                            (some (fn [x]
                                    (some (fn [y] (and (not= x y) (not (genl-related? x y))
                                                       (not (exempt? x y))))
                                          below-b))
                                  below-a)))
                        sibs)
                  ;; a partition separates on its part list as a metatype does on its members; `covering`
                  ;; alone records no partition, so its parts may overlap
                  (some (fn [[ps in-a]]
                          (let [in-b (filterv #(contains? bs %) ps)]
                            (some (fn [x]
                                    (some #(and (not= x %) (not (genl-related? x %))
                                                (not (exempt? x %)))
                                          in-b))
                                  in-a)))
                        parts))))))))))

(defn disjointness-test
  "A predicate `type -> boolean` answering `(disjoint? tax a <type> context)` with
  everything that depends on `a` and `context` alone read once (`separation-frame`).
  `disjoint?` is this asked once; `checks/disjoint-problem` asks it of every type the term
  already holds.  A type `a` no declaration reaches answers false without looking at the
  candidate.  `exempt?` is the `siblingDisjointException` read `(fn [x y])`, consulted by the
  three mark arms and never by the `disjoint` arm: by default the exceptions `context`
  reads (`exemption`); `(constantly false)` reads none."
  ([tax a context] (disjointness-test tax a context (exemption tax context)))
  ([tax a context exempt?]
   (or (separation-test tax a context exempt?) (constantly false))))

(defn separating-partners
  "The types a visible declaration separates `a` from: every `y` such that some supertype
  of `a` is declared `(disjoint x y)` with `x` not `y`, shares a disjoint metatype with `y`,
  stands beside `y` as a proper specialization of one `(sibling_disjoint C)` parent, or
  stands beside `y` in one `partition` declaration: the four arms of `disjointness-test`,
  with the same global genl-relatedness guard and `siblingDisjointException` exemptions on
  the latter three.  Every type disjoint from `a` is a subtype of one of these and of
  nothing else, so `(disjoint a ?t)` is `specs` of this set.  `exempt?` is as for
  `disjointness-test`."
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
        ;; a partition separates `a` from every other part of a declaration holding a
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
  set: each `[:disjoint #{x y}]` pair, each disjoint metatype's `[:metatype m]` mark with its
  two `[:member m _]` memberships, each `[:sib-disjoint c]` parent and each separating
  cover's `[:cover [whole parts] kind]`, over a supertype `x` of `a` and a different
  supertype `y` of `b`.  Empty when `a` and `b` are not disjoint at `context`.  `exempt?` is
  as for `disjointness-test`; `(constantly false)` names every separation stated over the
  pair."
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
  `siblingDisjointException` read, as `{:keys #{k} :links [[sub super]] :pair [x y]}`:
  `separating-keys`' entries, the separated supertypes `x` of `a` and `y` of `b`, and the
  `genl` subsumptions climbed (`a` to `x`, `b` to `y`, and for a `sibling_disjoint` parent
  `c` also `x` and `y` to `c`; a reflexive one is left out).  Empty exactly when
  `disjointness-test` reading no exemption answers false from `a`'s side.  A route through a
  mark carries `:mark? true`, which an exception can exempt (`route-exempted?`).  A placed
  nogood names one route as its grounds (docs/nmtms.md)."
  [tax a b]
  (let [{:keys [seps metas sibs parts]} (separation-frame tax a nil)
        bs     (separable-genls tax b)
        all-bs (delay (genls-global tax b))
        unrel? (fn [x y] (and (not= x y) (not (genl?-global tax x y)) (not (genl?-global tax y x))))
        route  (fn [ks x y & links]
                 {:keys ks :pair [x y] :mark? true
                  :links (into [] (remove (fn [[s t]] (= s t))) (concat [[a x] [b y]] links))})]
    (concat
     (for [[x ys] seps, y ys :when (and (not= x y) (contains? bs y))]
       (dissoc (route #{[:disjoint #{x y}]} x y) :mark?))
     (for [[m ms in-a] metas, x in-a, y ms :when (and (contains? bs y) (unrel? x y))]
       (route #{[:metatype m] [:member m x] [:member m y]} x y))
     (for [[c under-c? below-a] sibs, x below-a, y @all-bs
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
  through when the route answers a denial, or nil when the reader reads no denial off it.
  Three conditions (docs/taxonomy.md, \"A separation answers a denial\"): every flat-cache
  key of the route has a supporter the reader sees (`visible-supporters`) that
  `supporter-class` reads believed, and a disjoint metatype's `[:member m y]` membership
  reads `:monotonic`; no `siblingDisjointException` the reader sees exempts the pair
  (`route-exempted?`); each subsumption the route climbs has a path whose every edge holds
  at `:monotonic` (`reach-support` with `supporter-class`).  `supporter-class` is a live
  `handle -> defeat-class` read, nil for OUT.  The witness is `{:keys :pair :supports
  :edges}`."
  [tax {:keys [keys links pair] :as route} context supporter-class]
  (let [mono? #(= :monotonic (supporter-class %))]
    (when-not (route-exempted? tax route context)
      (when-let [sups (reduce (fn [acc k]
                                (if-let [h (first (filter (if (= :member (first k)) mono? supporter-class)
                                                          (sort (visible-supporters tax k context))))]
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
  `genl` generation and the separation inputs: the routes are read over the unscoped
  closures and the declarations alone, so a reader asking one pair again before either
  moves reads a map entry (`res/separation-denials`, `membership/cover-routes`)."
  [tax a b]
  (let [t   @tax
        lru (:closure-lru t)
        k   [:separation-routes (:gen (:genl t)) (separation-inputs tax) a b]]
    (or (caches/lru-get lru k)
        (caches/lru-put! lru k (vec (separation-routes tax a b))))))

(defn pair-separated?
  "Does a declaration separate the type `a` from the type `b` over the unscoped closures,
  with no `siblingDisjointException` read: `separation-test` with no reader and no
  exemption, a superset over every reader, and symmetric.  Held in the closure cache
  under the `genl` generation and the separation inputs, so the membership family's cover
  arm (`membership/term-nogoods`) tests a held type against a part once per value and
  reads a map entry after."
  [tax a b]
  (let [t   @tax
        lru (:closure-lru t)
        k   [:pair-separated (:gen (:genl t)) (separation-inputs tax) a b]
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
     ;; guards — the metatype arm's member set, read off a `partition` declaration
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
  "Are types a and b provably disjoint?  True when some supertype of a and some different
  supertype of b are separated: by a declared `(disjoint x y)`, by both being members of one
  disjoint metatype, by both being non-genl-related proper specializations of one
  `(sibling_disjoint C)` parent (genl-relatedness read globally), or by both being parts of
  one `partition` declaration.  Disjointness is inherited downward through `genl`.  The
  context arity scopes the two `genls` closures, a `(disjoint x y)` pair's supporters and the
  metatype arm's mark and memberships.  `context` may be an ancestor set: the closures and
  declarations read are those some supporter states in the set, with no belief callback
  (`genls-asserted-in`).  Monotone in the visibility of declarations and edges, except a
  `siblingDisjointException`, which spares its pair at a reader that sees it.  An unscoped
  read sees every exception.  See docs/taxonomy.md, \"Disjointness\"."
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
  "Lazy seq of witness context sets for the provable disjointness of `a` and `b`: each is
  the supporting contexts of one complete derivation (a genl path from `a` to one separated
  type, a path from `b` to the other, and the separating declaration in any of the four
  spellings).  A reader sees the clash iff it sees every context in some witness; a
  supporter with no recorded context imposes nothing.  Lazy on every level.  Reads no
  `siblingDisjointException`: empty exactly when no reader separates the pair,
  `disjointness-test` reading no exemption."
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
     ;; the cover arm: `(partition W P1 P2 …)` and `(separating W P1 P2 …)` separate their parts,
     ;; so the derivation rests on the paths up to two distinct parts and the declaration;
     ;; the parts vector is the one `cover-key` normalized
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
  stated in a context that sees no statement of the mark.  With a context they answer whether
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

(def ^:private no-props
  "The one empty set `props` answers.  `checks/stratification-graph-current?` compares a
  mark set by identity, and cloverage's rewrite of a literal `#{}` builds a new set at each
  evaluation."
  #{})

(defn props "The set of predicates carrying property `kind`." [tax kind] (get (:props @tax) kind no-props))

(defn mention-marks
  "The two kinds of head that make a position a mention (a term named as syntax), as
  `{:quoting #{…} :modal #{…}}`, read once per walk.  `:quoting` is `sx/quoting-functors`
  (`Quote`, `Quasiquote`); `:modal` is the `modal_predicate` marks, read globally
  (docs/belief.md).  Both are opaque to identity congruence and follow a `rewriteOf`
  spelling rename.  See docs/taxonomy.md, \"Predicate metadata reads\"."
  [tax]
  {:quoting sx/quoting-functors :modal (props tax :modal)})

(defn props-over
  "`p` and every super-predicate of it carrying property `kind`, anywhere or (with
  `context`) declared from a context the reader can see, walking only the `genl` edges
  visible from it.  Empty when none does.  For the properties a violation is convicted
  against, not for the generative ones (`transitive`, `symmetric`, `reflexive`,
  `transitiveInArg`).  See docs/taxonomy.md, \"Predicate metadata reads\"."
  ([tax kind p] (props-over tax kind p nil))
  ([tax kind p context]
   (let [marked (get-in @tax [:props kind])]
     (if (empty? marked)
       #{}
       (into #{}
             (comp (filter marked) (filter #(has-prop? tax kind % context)))
             (if (some? context) (genls tax p context) (genls-global tax p)))))))

(defn props-over-among
  "`props-over` with no context, read off the `kind` `:props` set's cut of `p`'s global
  closure (`genls-global-among`) rather than the closure: `memo` is a volatile map the
  caller keeps for one `:props` value over one still taxonomy, so a caller asking it of many predicates
  pays the edges once rather than a closure per predicate."
  [tax kind p memo]
  (let [marked (get-in @tax [:props kind])]
    (if (empty? marked)
      #{}
      (into #{} (filter #(has-prop? tax kind % nil)) (genls-global-among tax p marked memo)))))

(def closure-relations
  "The two relations whose transitive closure the engine caches and answers itself,
  `genl` and `genlCx`.  They are held out of the generic `:transitive` prop machinery, so a
  `(transitive genl)` fact stays queryable but inert.  `provers/transitive-predicates` and
  `inherit/virtual-relations` are both this set, and `special`'s mark ingestion reads it as
  the skip-set.  Read off the declarations (`:edge` storage kind)."
  (set (keys (pr/by-storage :edge))))

(def arg-declaration-props
  "Per argument-constraint kind, the `:props` set its subject is marked under:
  `(arg parentOf 1 person)` marks `parentOf` as declaring `arg`.  The set is global, so a
  filter built on it is a superset of what any context sees.  Read off the declarations: the
  family is `predicates/:argument-constraint` and the keyword is each spelling's `:prop`
  storage target.  See docs/taxonomy.md, \"Predicate metadata reads\"."
  (into (sorted-map)
        (map (juxt identity pr/prop-kind))
        (pr/family :argument-constraint)))

(def functional-family-marks
  "The spellings of the functional mark, each with its written shape: `:mark` for
  `(functional P)`, `:mark-in-arg` for `(functionalInArg P n)`.  The marked predicate is
  argument 1 of either.  Read back from `predicates/mark-families`, where a third spelling
  is added.  The spellings store apart (`:functional` prop, `:functional-in-arg` table), so
  they share a family and argument 1 and no storage."
  (pr/by-family :functional))

;; The supporters behind a flat-cache entry, read back, for a consumer that justifies
;; something on a declaration.  Every stored supporter is returned, believed or not, so a
;; derivation revives when its supporter does.
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
(defn add-negates
  ([tax p q handle] (add-negates tax p q handle nil))
  ([tax p q handle ctx] (add-supported tax (negates-key p q) handle ctx)))
(defn del-negates! [tax p q handle] (del-supported! tax (negates-key p q) handle))
(defn add-arity
  ([tax pred n handle] (add-arity tax pred n handle nil))
  ([tax pred n handle ctx] (add-supported tax [:arity pred n] handle ctx)))
(defn del-arity! [tax pred n handle] (del-supported! tax [:arity pred n] handle))

(def exact-arity-classes
  "What each exact-arity class membership says the arity is: `sx/exact-arity-classes`,
  read here by `kb/relation?` and the quality and integrity passes."
  sx/exact-arity-classes)

(defn declared-arity
  "The arity `pred` is declared with, or nil: anywhere, or (with `context`) declared from
  a context the reader can see.  Nil when the visible declarations give two different
  arities.  Cached because the arity check runs on every assertion (docs/taxonomy.md,
  \"Predicate metadata reads\")."
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
  "`[pred n]` pairs: `p` and every super-predicate of it carrying a
  `(functionalInArg pred n)` declaration, anywhere or (with `context`) declared from a
  context the reader can see.  Empty when none does.  `props-over`'s shape, walking up for
  its reason.  Storage is `arity`'s table; `::prop-kind` is not extended.  Does not collapse
  to a single `n`."
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
  "Every predicate carrying any `functionalInArg` mark, at any position, as a set: one map
  read, no closure walk.  For callers with no probe predicate
  (`special/equate-under-context-edge`)."
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
  "The commutativity group descriptors declared of `pred` itself, as a set; empty for all
  but a handful of predicates.  The exact functor, and global: a commutativity mark
  canonicalizes (`res/kb-sentex`, `res/spelling-planner`) and a `genl` edge below it does not
  make the sub-predicate commutative.  One map read."
  [tax pred] (get (:commuting @tax) pred #{}))

(defn add-meet
  "Install `(meetFunctionOf f order)`: `f` is the meet of `order`."
  ([tax f order handle] (add-meet tax f order handle nil))
  ([tax f order handle ctx] (add-supported tax [:meet f order] handle ctx)))

(defn del-meet! [tax f order handle] (del-supported! tax [:meet f order] handle))

(defn meet-orders
  "The orders `f` is declared the meet of, as a set; empty for nearly every function.
  The exact functor, and global, for `commuting-groups`' reasons: the mark decides the
  stored key of an application of `f`, which every reader shares."
  [tax f] (get (:meet @tax) f #{}))

(defn meet-supporters
  "The handles of the sentexes stating `(meetFunctionOf f order)`, defeated members
  included."
  [tax f order] (cache-supporters tax [:meet f order]))

(defn add-distinct
  "Install `(distinctInArgAndRest f n)`: `f`'s arguments from position `n` on are distinct."
  ([tax f n handle] (add-distinct tax f n handle nil))
  ([tax f n handle ctx] (add-supported tax [:distinct f n] handle ctx)))

(defn del-distinct! [tax f n handle] (del-supported! tax [:distinct f n] handle))

(defn distinct-positions
  "The positions `f` is declared distinct from, as a set; empty for nearly every function.
  The exact functor, and global, for `commuting-groups`' reasons."
  [tax f] (get (:distinct @tax) f #{}))

(defn distinct-supporters
  "The handles of the sentexes stating `(distinctInArgAndRest f n)`, defeated members
  included."
  [tax f n] (cache-supporters tax [:distinct f n]))

(defn commuting-predicates-among
  "The members of `specs` carrying any commutativity group, as a set, or nil when none do:
  `commuting-groups` mirrored for a caller holding a spec closure.  Iterates the table's
  entries, so a miss allocates nothing."
  [tax specs]
  (let [table (get @tax :commuting {})]
    (when (seq table)
      (not-empty (into #{} (comp (map key) (filter #(contains? specs %))) table)))))

(defn commuting-declared?
  "Does any predicate carry a commutativity group?  The table-wide presence check a caller
  reads before it builds the spec closure `commuting-predicates-among` is asked over."
  [tax]
  (boolean (seq (get @tax :commuting))))

(defn functional-family-declared?
  "Does the taxonomy carry a functional-family mark of either spelling: the global,
  unscoped presence check every merge entry point of that family reads before it reads any
  extent?  Two set-emptiness reads; see `functional-family-marks`."
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
     ;; the empty case first: a transitive walk asks this per node, and reaching `closure-of`
     ;; before finding no partner would charge every walk a genlCx closure lookup per hop
     (if (or (empty? qs) (not (scoped-context? context)))
       qs
       (into #{} (filter #(cache-entry-visible? tax (inverse-key p %) context)) qs)))))

(defn inverse-of
  "The declared inverse of `p`, or nil: anywhere, or (with `context`) declared from a
  context the reader can see.  The lexicographically smallest of several, so the answer
  does not depend on arrival order.  `inverses-of` answers all of them."
  ([tax p] (first (sort (inverses-of tax p))))
  ([tax p context] (first (sort (inverses-of tax p context)))))

(defn inverses-under
  "Every predicate declared inverse to `p` or to a sub-predicate of `p`, as a set:
  anywhere, or (with `context`) declared from a context the reader can see, walking only
  the `genl` edges visible from it.  One map read when the `:inverse` map is empty."
  ([tax p] (inverses-under tax p nil))
  ([tax p context]
   (if (empty? (get @tax :inverse))
     #{}
     (let [ps  (if (some? context) (specs tax p context) (specs-global tax p))
           inv (if (some? context) #(inverses-of tax % context) #(inverses-of tax %))]
       (into #{} (mapcat inv) ps)))))

;; ---- negates: two relations that never hold of the same arguments --------
;; `(negates P Q)` is a symmetric pair in the `:negates` adjacency (`index-symmetric`),
;; keyed `[:negates #{P Q}]`; readers walk up from a tuple's functor, as `props-over` does.

(defn negates?
  "Does the taxonomy hold a `negates` declaration?  One map read."
  [tax]
  (boolean (seq (:negates @tax))))

(defn negating-predicates
  "Every predicate a `negates` declaration names."
  [tax]
  (set (keys (:negates @tax))))

(defn negates-of
  "Every predicate declared to negate `p`, as a set: anywhere, or (with `context`)
  declared from a context the reader can see."
  ([tax p] (get-in @tax [:negates p] #{}))
  ([tax p context]
   (let [qs (get-in @tax [:negates p] #{})]
     (if (or (empty? qs) (not (scoped-context? context)))
       qs
       (into #{} (filter #(cache-entry-visible? tax (negates-key p %) context)) qs)))))

(defn negates-over
  "`[P R]` for each predicate `P` at or above `q` and each `R` declared to negate `P`: a
  tuple of `q` is a tuple of `P`, so no tuple of `R`'s spec subtree holds of its
  arguments.  Over the unscoped closure, or (with `context`) the edges and declarations
  the reader sees.  One map read on a KB with no declaration."
  ([tax q] (negates-over tax q nil))
  ([tax q context]
   (let [table (:negates @tax)]
     (if (empty? table)
       #{}
       (into #{}
             (comp (filter table)
                   (mapcat (fn [p] (map #(vector p %) (if (some? context)
                                                        (negates-of tax p context)
                                                        (negates-of tax p))))))
             (if (some? context) (genls tax q context) (genls-global tax q)))))))

;; ---- genlInverse: binary genl with the arguments swapped ----------------
;; `(genlInverse P Q)` says a `(P x y)` tuple is a `(Q y x)` tuple.  The edges are a
;; flat-cache entry held both ways (`:genl-inverse-down`, `:genl-inverse-up`) and never
;; edges of the `genl` relation.  The signed closure reads them, keeping a parity bit that
;; a `genlInverse` edge flips, so an odd-parity predicate is read with its arguments
;; swapped.

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

(defn- signed-walk
  "`[straight swapped]` from `p` over `[predicate parity]` states: `close` takes a
  predicate's `genl` closure, and `hop` the predicates one `genlInverse` edge from a
  member of it, reached with the parity flipped."
  [p close hop]
  (loop [todo [[p false]] seen #{[p false]} straight #{} swapped #{}]
    (if-let [[n odd] (peek todo)]
      (let [cl  (close n)
            nxt (into [] (comp (mapcat hop)
                               (distinct)
                               (map (fn [x] [x (not odd)]))
                               (remove seen))
                      cl)]
        (recur (into (pop todo) nxt)
               (into seen nxt)
               (if odd straight (into straight cl))
               (if odd (into swapped cl) swapped)))
      [straight swapped])))

(defn clock-held
  "`(read)`, held in the closure memo's `slot` under `k` for one stretch of the change
  clock: a new clock value drops the slot's entries of the old one.  Read afresh when the
  taxonomy holds no memo.

  Public so a reader above this namespace can hold a value it derives from the taxonomy
  and the store for the same stretch, under a slot of its own (`res/arg-constraints`)."
  [tax slot k read]
  (if-let [memo (:closure-memo @tax)]
    (let [clock (observe/change-clock)
          held  (get @memo slot)]
      (if-let [e (when (= clock (:read-under held)) (find (:closures held) k))]
        (val e)
        (let [v (read)]
          (swap! memo update slot
                 (fn [h] (if (= clock (:read-under h))
                           (assoc-in h [:closures k] v)
                           {:read-under clock :closures {k v}})))
          v)))
    (read)))

(defn signed-closure
  "`[straight swapped]`: the predicates `p`'s matching fan reaches through the `genl` and
  `genlInverse` edges visible from `context`, `dir` `:down` the specs or `:up` the
  generals.  `straight` holds those reached over an even number of `genlInverse` edges, read
  with arguments as written; `swapped` those over an odd number, read with arguments 1 and 2
  exchanged.  With no `genlInverse` edge installed this is `[(specs tax p context) #{}]`
  (or `genls`).  Otherwise a walk over `[predicate parity]` states, memoized in the closure
  memo for one stretch of the change clock."
  [tax dir p context]
  (let [close (if (= dir :down) #(specs tax % context) #(genls tax % context))]
    (if (genl-inverse-free? tax)
      [(close p) #{}]
      (clock-held tax ::signed [dir p context]
                  #(signed-walk p close (fn [s] (genl-inverse-hop tax dir s context)))))))

(defn- monotonic-genls
  "The supertypes of `p`, incl `p`, through the `genl` edges visible from `context` whose
  strongest visible supporter `supporter-class` reads `:monotonic` (`edge-class`)."
  [tax p context supporter-class]
  (let [t     @tax
        scope (relation-scope tax :genl context)
        adj   (if (nil? scope) #(get-in t [:genl :fwd %]) #(visible-neighbours t :genl :fwd scope %))]
    (loop [todo [p] seen #{p}]
      (if-let [n (peek todo)]
        (let [nxt (into [] (comp (remove seen)
                                 (distinct)
                                 (filter #(= :monotonic (edge-class t :genl [n %] scope supporter-class))))
                        (adj n))]
          (recur (into (pop todo) nxt) (into seen nxt)))
        seen))))

(defn contrapositive-closure
  "`[straight swapped]`: `signed-closure` `:up` of `p` from `context`, over only the
  `genl` and `genlInverse` edges a reader holds at `:monotonic`: the predicates a negated
  pattern on `p` fans over.  A `genl` edge's class is its strongest visible supporter's
  (`edge-class`); a `genlInverse` hop needs one visible supporter that `supporter-class`
  reads `:monotonic` (`handle -> class`, nil for OUT; `res/holding-class`).  A `p` with no
  supertype answers `signed-closure`'s set.  See docs/inference.md, \"Under a negation the fan
  reverses\"."
  [tax p context supporter-class]
  (let [full (signed-closure tax :up p context)]
    (if (and (nil? (next (first full))) (empty? (second full)))
      full
      (clock-held tax ::contrapositive [p context]
                  #(signed-walk p
                                (fn [n] (monotonic-genls tax n context supporter-class))
                                (fn [s]
                                  (filter (fn [y]
                                            (some (fn [h] (= :monotonic (supporter-class h)))
                                                  (visible-supporters tax (genl-inverse-key s y) context)))
                                          (genl-inverse-hop tax :up s context))))))))

(defn inverses-over
  "The partners a denial of `p` reads: each `Q` an `(inverse P' Q)` declares for a `P'`
  at or above `p`.  `(not (Q y x))` is `(not (P' x y))`, and a denial of `P'` denies `p`.
  With `context` and `supporter-class` (`contrapositive-closure`'s), `P'` ranges over
  the straight half of `contrapositive-closure` and the declaration needs a visible
  supporter `supporter-class` reads `:monotonic`, since a `:default` declaration does not
  contrapose.  Without them, the unscoped superset over every `genl` edge and declaration,
  for a trigger."
  ([tax p]
   (if (empty? (get @tax :inverse))
     #{}
     (into #{} (mapcat #(inverses-of tax %)) (genls-global tax p))))
  ([tax p context supporter-class]
   (if (empty? (get @tax :inverse))
     #{}
     (into #{}
           (mapcat (fn [t]
                     (filter (fn [q] (some #(= :monotonic (supporter-class %))
                                           (visible-supporters tax (inverse-key t q) context)))
                             (inverses-of tax t))))
           (first (contrapositive-closure tax p context supporter-class))))))

(defn- visible-flat-supporters
  "The supporters of flat-cache key `k` a reader at `context` can use, as `[handle ctx]`
  pairs — every stored one for an unscoped read, else those `cache-entry-visible?` would
  admit."
  [tax t k context]
  (let [sup (supporters-of t k)]
    (cond
      (not (scoped-context? context)) (vec sup)
      (supporter-filter-active? t)
      (let [scope (supporter-scope tax t context)]
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
            {:keys [found tree]}
            (graph/bfs-tree [[start nil]]
                            (fn [[n odd :as st] _]
                              (for [x (sorted (genls tax n context))
                                    y (sorted (genl-inverse-hop tax :up x context))]
                                [[y (not odd)] [st x y]]))
                            goal?)
            ;; walk the parents back: each hop is [from-node x y], the `genl`
            ;; stretch from-node →* x then the `genlInverse` edge x → y
            path   (when found
                     (loop [s found acc ()]
                       (if-let [[prev x y] (get tree s)]
                         (recur prev (cons [(first prev) x y] acc))
                         [acc (first found)])))]
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
;; The closures (global and scoped) are one weighted LRU bounded by the terms it holds
;; (`closure-memo-limit`, through the cache profile).  The visibility index is bounded by
;; the context census, never by the read count.

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
                 "generation they are keyed on; past the bound, which follows the "
                 "taxonomy's node count, and under memory pressure, the least recently "
                 "used go first.")
  :read     (fn [kb] (let [lru (some-> (reasoning/taxonomy kb) deref :closure-lru)
                           ^java.util.concurrent.atomic.AtomicLongArray w (:walks lru)]
                       (cond-> {:entries (some-> lru caches/lru-weight)}
                         lru (assoc :limit ((:limit lru)))
                         w (assoc :builds (.get w 0) :fallbacks (.get w 1)))))
  :clear    (fn [kb] (or (some-> (reasoning/taxonomy kb) deref :closure-lru caches/lru-clear!)
                         0))
  :trim     (fn [kb target]
              (or (when-let [lru (some-> (reasoning/taxonomy kb) deref :closure-lru)]
                    (caches/lru-trim! lru (min (long target) (long ((:limit lru))))))
                  0))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(defn- relation-value
  "Relation `r`'s map in `kb`'s taxonomy less its moves (J5)."
  [kb r]
  (-> (caches/value-at kb [:taxonomy r]) (dissoc :moves :move-gen :shrinks :shrink-gen :grows :grow-gen)))

(def ^:private flat-keys
  [:disjoint :disjoint-index :disjoint-metatypes :metatype-members :sibling-disjoint
   :sib-exception-index :covers :cover-parts :partitions :props :inverse :negates :genl-inverse-down :genl-inverse-up :arity
   :functional-in-arg :commuting :meet :distinct :cache-dirty :cache-ctxs])

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
 {:id :T7 :label "Closure filter memo" :kind :cache :keyed-by :context :reads [:T1 :M1 :index :records]
  :holds-content? false
  :retired-by (assoc (caches/on-every :G*) :recover :W)
  :computed :read :imaged? false :at [[:taxonomy :closure-memo]]
  :value (fn [kb] (some-> (caches/value-at kb [:taxonomy :closure-memo]) deref))
  :note "per relation, whether the supporter filter is active and the down-closure by context and reading, under the relation generation and keyed by the change clock; the signed closure (`::signed`) and the `:monotonic` one a negated pattern fans over (`::contrapositive`, `contrapositive-chain`), whether a defeat a context sees reaches a permuting mark (`except/mark-hazard?`) and the argument constraints binding a predicate's tuples (`res/arg-constraints`), each held for one stretch of the change clock; and whether a denial of a forced-monotonic literal is stored beside it (`except/yielding-reads?`), held across writes while no forced-monotonic fact leaves the index and the index and the forced-monotonic sets stand"})

(caches/register-derived
 {:id :T10 :label "Taxonomy pass caches" :kind :pass :keyed-by :node :reads [:T1 :M1 :index :records]
  :holds-content? false
  :retired-by {} :computed :pass :imaged? false
  :note "`*visible-neighbours-cache*`, bound for one reading pass (`with-neighbours`): the filtered and sorted neighbours and edge supporters the walks read, a reader's scope, the maximal common descendants of a context set, a flat-cache key's believed supporters and whether an except reaches a handle (`pass-held`); `chain/*witnesses*`, the witnesses, supporter classes and `genl` route lengths (`reach-support`'s router) one `place-nogoods!` reads, answered while the change clock holds"})

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
       [:taxonomy :genlCx :moves] [:taxonomy :genlCx :move-gen]
       [:taxonomy :genl :shrinks] [:taxonomy :genl :shrink-gen]
       [:taxonomy :genlCx :shrinks] [:taxonomy :genlCx :shrink-gen]
       [:taxonomy :genl :grows] [:taxonomy :genl :grow-gen]
       [:taxonomy :genlCx :grows] [:taxonomy :genlCx :grow-gen]]
  :note "`{gen #{node}}` and `{node gen}` per relation, which `moves-since` reads (the `genlCx` lower ends for the settle's context-move drain); a reader whose generation is older than the first kept reads whole.  `:shrinks` logs the ends that lost an edge or moved its supporting contexts, which `shrinks-since` reads, and `:grows` the edges that entered the active set, which `grows-since` reads (the argument holds read an end that only gained edges by what its readers gain through them)"})

(caches/register-derived
 {:id :Q5 :label "Equality moves" :kind :queue :keyed-by :term :reads [:T3]
  :holds-content? false
  :retired-by {:equality :K :edge-belief :K :settle-exit :Q :settle-pass :Q :recover :R
               :image-install :R}
  :computed :write :imaged? :taxonomy
  :at [[:taxonomy :equality :moved] [:taxonomy :equality :believed-again]]
  :note "the class members moved per reader and the handles believed again; `take-equality-moves!` and `take-believed-again!` drain them"})
