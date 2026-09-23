;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.columnar
  "The dense **columnar trie** index — the `:memory-columnar` backend, off by default.

  The flat-map index (`vaelii.impl.kv`) stores each trie node as three entries keyed by
  a boxed **vector of the full path prefix**; a path's every prefix is a separate object,
  so the structure is redundant boxed keys + HAMT overhead — `bench/…/densetrie.clj`
  measured that at ~487 MB of the 592 MB index (300k real facts), and it is the index's
  dominant cost.  The bench also found the win is the *layout*, not interning: a
  fastutil-map-per-node recovers only 1.28×, a columnar layout ~15–20×.

  So here the trie is a real node graph, not a map of prefixes:

    * nodes are `int` ids; node data lives in **grow-on-demand parallel arrays** indexed
      by id — `counts` (primitive `int[]`), `toks`/`tgts` (a node's child edges: a
      **sorted `int[]`** of tokens and the parallel `int[]` of child node ids while the
      node is narrow, one primitive `Int2IntOpenHashMap` once it is wide), `leaves` (an
      `IntPostings`, the same tiered `int[]`/Roaring set Phase 1 uses — this is where the
      two phases unify);
    * edges carry **interned `int` tokens** from a `vaelii.impl.tokens` dictionary, not
      boxed symbols/markers/lists; the dictionary's inverse decodes them for `children`.

  **Mutable, not a static CSR.**  A compressed-sparse-row trie is the densest a trie
  gets, but it is *static* — the index mutates on every assert/retract.  A per-node
  sorted `int[]` supports incremental add/remove (binary-search + array splice) while
  still dropping the boxed prefixes and the per-node hashmap slack; the node ids of a
  pruned subtree are recycled through a free list.  Freezing the cold majority to a true
  CSR is a later compaction pass (the mutable-head / compacted-tail pattern the record
  store already uses), justified by measuring where this lands.

  **A node's child structure is tiered on its width, and that is a measurement.**  The
  splice above costs O(children already there), and nothing bounds a node's width: the
  level-2 node holds one child per distinct first argument of a predicate, so an
  array-only node structure loads one broad relation — `(genl S T)`, any hot
  relation — in time quadratic in that relation's own extent.  It is the *node* that is
  expensive, not the trie: holding 200k facts fixed and varying only the widest node's
  fan-out, an array-only structure reads 4.2 s at 2,000 children, 9.0 s at 20,000 and
  18.2 s at 200,000.  So past `promote-at` children a node's edges become one primitive
  `Int2IntOpenHashMap` (O(1) insert, no splice) and drop back to the array pair below
  half of it.  Blanket maps are the wrong answer in the other direction — the bench found
  a fastutil map per node worth 1.28× against the columnar layout's ~15–20× — and the
  tiering is what takes both, since the overwhelming majority of nodes are narrow and
  never leave the dense pair.

  **Composition keeps the new surface small.**  Only the trie families
  (`index`/`unindex`/`lookup`/`count-at`/`children`) are native here; the secondary
  roots, the rule / exception indexes, the inverted term index, and the term roster
  beside it — all flat `key → set` maps — delegate to an embedded `KvIndexStore` over a
  Phase-1 `TieredKvBackend` (int-dense postings already).  `index-sentex` and
  `unindex-sentex!` take the ops for those families from `kv/flat-family-adds` /
  `kv/flat-family-retires` and batch them straight to the shared backend, so both stores
  write the same keys in the same order and the delegated reads stay consistent.

  Single-writer, like every index: the arrays are mutated in place; `lookup`/`children`
  /`leaves` materialize fresh Clojure collections at the boundary.  Proven set-equal to
  `KvIndexStore` by `columnar_index_oracle_test`.

  **Single-*threaded*, which is narrower than single-writer.**  The `Trie` fields are
  `^:unsynchronized-mutable`, so a write publishes through no barrier: a second thread
  reading this index may see an array reference, a capacity or the CSR-mode flag from
  before a growth or a compaction, and there is no happens-before edge that would stop
  it.  The atom- and lock-based backends give an incidental reader beside the writer a
  consistent view; this one does not, and it is the caller's job to keep its reads on
  the writer's thread or behind a synchronizer of its own.  The fields are unsynchronized
  because the walk reads them at every frontier node, which is the index's hottest loop
  — a volatile read there is paid per node per lookup, to buy a guarantee the engine's
  own single writer never needs."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.dense-roots :as dense-roots]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.trie :as trie-types
             :refer [t-child-count t-children t-clear! t-compact! t-count-at
                     t-insert! t-leaves-at t-lookup t-remove!]]))

;; ---- the portable projection ---------------------------------------------
;; The trie here is a node graph, not a map of prefix keys, so its share of the index's
;; portable form has to be *computed*: one DFS from the root, carrying the decoded prefix
;; down, emitting each node as the three entries `KvIndexStore` would have stored it as.
;; Read back, only the leaf entries are needed — counts and child edges are functions of
;; the leaves, and `t-insert!` maintains both — so a load ignores them rather than
;; trusting them, and a dumped count can never disagree with the trie it describes.

(defn- trie-entry? [k] (and (vector? k) (= :trie (nth k 0))))
(defn- leaf-entry? [k] (and (trie-entry? k) (= :handles (nth k 1))))

;; ---- the composed IndexStore --------------------------------------------

(defrecord ColumnarIndexStore [dict trie roots embedded]
  p/IndexStore
  ;; trie native; roots + term index straight to the shared int-keyed backend (same keys
  ;; as KvIndexStore, so the delegated reads below stay consistent)
  (index-sentex [_ sentex handle]
    (let [pth  (sx/path sentex)
          flat (kv/flat-family-adds roots sentex handle)] ; reads the pre-write postings
      (t-insert! trie pth handle)
      (p/kv-batch roots (:ops flat))
      ;; the same tally `KvIndexStore` keeps, because this store writes the index itself
      ;; rather than through it — an instrument that went quiet on the backend the
      ;; density work exists for would report a KB that never writes an index.  The four
      ;; family counts come back from `flat-family-adds`, so only `:levels` — the trie
      ;; depth, which is this store's own — is counted here.
      (when (prof/profiling?)
        (prof/record-index-write sentex (assoc (:counts flat) :levels (inc (count pth))))))
    handle)
  ;; A stray unindex — `t-remove!` answers -1 when the handle is not at the leaf — touches
  ;; nothing: the roots and the term index are left as they are, the same no-op
  ;; `KvIndexStore` makes off its leaf probe, and it says so for that store's reason.  The
  ;; caller deletes the record next either way, so a genuine record/index divergence would
  ;; otherwise surface as a handle with no record, several operations away from the store
  ;; that diverged.  `reindex` is the repair.
  (unindex-sentex! [_ sentex handle]
    (let [pth  (sx/path sentex)
          dead (long (t-remove! trie pth handle))]
      (if (neg? dead)
        (trove/log! {:level :warn :id ::unindex-absent
                     :data {:handle handle :path pth :context (:context sentex)}})
        (let [flat (kv/flat-family-retires roots sentex handle)] ; reads the pre-write postings
          (p/kv-batch roots (:ops flat))
          (when (prof/profiling?)
            (prof/record-index-retract sentex (assoc (:counts flat)
                                                     :levels (inc (count pth))
                                                     :dead   dead))))))
    handle)
  ;; the same family labels `KvIndexStore` records, for the same reason: the split
  ;; between a retrieval walk and the planner's selectivity probes is the reading that
  ;; says whether a KB uses its trie to fetch or to plan, and it must not depend on
  ;; which index is underneath.  `:fan` is the one tally this store does not keep — the
  ;; walk below is native and counts no node probes (docs/profile.md).
  (count-at [_ prefix]  (prof/record-read :trie-counts) (t-count-at trie prefix))
  (children [_ prefix]  (prof/record-read :trie-counts) (t-children trie prefix))
  (count-children [_ prefix] (prof/record-read :trie-counts) (t-child-count trie prefix))
  (lookup   [_ pattern] (prof/record-read :trie-lookup) (t-lookup   trie pattern))
  ;; the exact leaf — the trie's own `t-leaves-at`, which walks the path's nodes and
  ;; decodes nothing else.  Tallied as retrieval, like the walk above it.
  (leaf-at  [_ path]    (prof/record-read :trie-lookup) (t-leaves-at trie path))

  ;; the non-trie families — flat key→handle-set maps — read/write the shared backend
  (sentexes-in-context   [_ c]        (p/sentexes-in-context   embedded c))
  (count-in-context      [_ c]        (p/count-in-context      embedded c))
  (sentexes-with-functor [_ pred]     (p/sentexes-with-functor embedded pred))
  (count-with-functor    [_ pred]     (p/count-with-functor    embedded pred))
  (sentexes-with-arg     [_ pos term] (p/sentexes-with-arg     embedded pos term))
  ;; the unary roster lives with the other root families, in the embedded store
  (unary-sentexes-with-arg [_ term]   (p/unary-sentexes-with-arg embedded term))

  (count-with-arg        [_ pos term] (p/count-with-arg        embedded pos term))
  (sentexes-with-args    [_ pred pts] (p/sentexes-with-args    embedded pred pts))
  (index-rule            [_ h a c]    (p/index-rule            embedded h a c))
  (unindex-rule!         [_ h a c]    (p/unindex-rule!         embedded h a c))
  (rules-by-antecedent   [_ pred]     (p/rules-by-antecedent   embedded pred))
  (rules-by-consequent   [_ pred]     (p/rules-by-consequent   embedded pred))
  (index-exception       [_ h preds]  (p/index-exception       embedded h preds))
  (unindex-exception!    [_ h preds]  (p/unindex-exception!    embedded h preds))
  (rules-with-exception-on [_ pred]   (p/rules-with-exception-on embedded pred))
  (exception-rules       [_]          (p/exception-rules       embedded))
  (exception-rule?       [_ h]        (p/exception-rule?       embedded h))
  (sentexes-with-term    [_ term]     (p/sentexes-with-term    embedded term))
  (sentexes-with-terms   [_ terms]    (p/sentexes-with-terms   embedded terms))
  (terms                 [_]          (p/terms                 embedded))
  (term-count            [_]          (p/term-count            embedded))

  ;; Two structures, one entry stream: the native trie projected into the flat key shape,
  ;; then the roots backend's own entries.  The load consumes the stream **once** —
  ;; it arrives off a dump one frame at a time — dispatching each entry to the structure
  ;; that owns it, and buffering the roots side so the backend still installs in batches.
  ;; Neither direction goes through `index-sentex`: no record is fetched, no path is
  ;; recomputed, no term is re-derived.  That is the whole difference from `reindex`.
  (index-entries [_] (concat (trie-types/trie-entries trie) (p/kv-entries roots)))
  (index-load [_ entries]
    (let [buf (volatile! (transient []))
          flush! (fn [] (let [b (persistent! @buf)]
                          (when (seq b) (p/kv-load roots b))
                          (vreset! buf (transient []))))]
      (doseq [[k v] entries]
        (cond
          (leaf-entry? k) (doseq [h v] (t-insert! trie (nth k 2) h))
          (trie-entry? k) nil                       ; counts and edges rebuild themselves
          :else           (do (vswap! buf conj! [k v])
                              (when (>= (count @buf) 10000) (flush!)))))
      (flush!))
    nil)

  ;; one wipe of the shared dictionary, after both structures that reference it are reset
  (clear-index! [_] (t-clear! trie) (p/kv-clear! roots) (tok/clear-tokens! dict) nil))

;; ---- construction (space-number sharing, like the memory / dense backends) --
;; The trie and the roots backend share ONE token dictionary per space (a term interned by
;; the trie and by a root get the same id), so the whole {dict trie roots} triple is one
;; shared unit keyed by space number.

(defonce ^:private state-spaces (atom {}))

(defn- state-for [space]
  (or (@state-spaces space)
      (get (swap! state-spaces
                  (fn [m] (if (m space)
                            m
                            (let [dict (tok/token-dict)]
                              (assoc m space {:dict  dict
                                              :trie  (trie-types/make-trie dict)
                                              :roots (dense-roots/dense-roots dict)})))))
           space)))

(defn columnar-index-store
  "A dense columnar `IndexStore`.  `:space` selects the shared {dict, trie, roots} state."
  [{:keys [space] :or {space 0}}]
  (let [{:keys [dict trie roots]} (state-for space)]
    (->ColumnarIndexStore dict trie roots (kv/->KvIndexStore roots))))

(defn drop-state-space!
  "Forget the {dict, trie, roots} state held under `space` — the columnar twin of
  `vaelii.impl.memory/drop-index-space!`, `core/close!`'s release of the RAM index a
  disk-backed KB derived.  A no-op for a `space` nothing holds; returns true when an entry
  was dropped."
  [space]
  (let [had? (contains? @state-spaces space)]
    (swap! state-spaces dissoc space)
    had?))

(defn compact!
  "Freeze a columnar index store's trie into read-optimized CSR arrays — the mutable
  node-linked graph collapses to flat parallel `int` arrays with no per-node objects.
  A subsequent write transparently reverts it to mutable, so this is the after-a-bulk-load,
  before-the-query-phase move (the 100M workload).  A no-op on a non-columnar store."
  [store]
  (when (instance? ColumnarIndexStore store) (t-compact! (:trie store)))
  store)

;; ---- the snapshot's two participants -------------------------------------
;; `vaelii.impl.disk.index-snapshot` writes the trie in `:trie` and the root columns in
;; `:roots`, and asks each of them the same three questions through
;; `vaelii.impl.types.snapshot`'s `SnapshotSections`.  Both fields are read off the store
;; directly, so this namespace carries no second vocabulary for them.

(defn columnar? [store] (instance? ColumnarIndexStore store))
