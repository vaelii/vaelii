;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.trie
  "The columnar index's mutable int-token trie, as a held namespace
  (`vaelii.impl.types.prover` states what that means).  `Trie` mutates its own fields,
  which only its inline methods can do, so the type and the code it calls live here
  together; it calls only held namespaces.  The `IndexStore` over it is
  `vaelii.impl.columnar`."
  (:require [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.postings :as postings]
            [vaelii.impl.types.sentex :as sentex-types]
            [vaelii.impl.types.snapshot :as snapshot-types])
  (:import [it.unimi.dsi.fastutil.ints Int2IntOpenHashMap IntSet]
           [java.nio IntBuffer]
           [java.util Arrays ArrayDeque]))

(def ^:const init-cap 16)

(def promote-at
  "How many child edges a trie node holds as the sorted `int[]` pair before its edges
  become one primitive hash map — and, at half of this, drop back to the pair.

  The pair is the better structure while a node is narrow: two primitive arrays, no
  object header between them and the data, and a binary search over a run short enough to
  sit in a cache line or two.  What it cannot do is grow cheaply, since minting an edge
  splices both arrays.  64 is where the two costs cross — the splice is still one short
  `arraycopy`, and a hash map's tables (over-provisioned to a 0.75 load factor, plus the
  object) are still bulkier than the pair they would replace, which matters because
  nearly every node in a real trie is on this side of the line.

  Dropping back at *half* rather than at the same width is hysteresis: a node sitting
  exactly on the boundary would otherwise rebuild its whole edge structure on every
  add/remove pair, and one rebuild per `promote-at`/2 operations is amortized O(1)."
  64)

(defn- buf->ints
  "A mapped `int` run copied into heap — what a write costs the first time it lands on a
  mapped trie.  Through a duplicate, so the shared buffer's position is untouched and a
  concurrent reader is unaffected."
  ^ints [^IntBuffer b]
  (let [n (.limit b)
        a (int-array n)]
    (.get (doto (.duplicate b) (.rewind)) a 0 n)
    a))

;; ---- the native mutable int-token trie ----------------------------------

(defprotocol PTrie
  ;; public trie ops (the IndexStore trie families bottom out here)
  (t-insert!   [t path handle] "Insert a sentex handle at the leaf of `path` (a token seq).")
  (t-remove!   [t path handle] "Remove `handle` from `path`'s leaf, pruning nodes that empty; answers how many of the path's own nodes emptied, or **-1** when `handle` was not at that leaf (the path absent, or the handle never there) — nothing was removed and nothing counted down.")
  (t-count-at  [t prefix]      "Subtree leaf count at a path prefix (0 if absent).")
  (t-children  [t prefix]      "Decoded child edge tokens at a prefix (a vector, [] if absent).")
  (t-child-count [t prefix]    "How many child edges sit at a prefix — the width, without decoding it.")
  (t-leaves-at [t prefix]      "Leaf handles exactly at a prefix (a set, #{} if absent).")
  (t-lookup    [t pattern]     "Handles whose full path matches `pattern` (variables fan out; markers skip).")
  (t-clear!    [t]             "Reset to a single empty root (the dict is wiped by the store).")
  (t-compact!  [t]             "Freeze the mutable trie into flat CSR arrays (read-optimized, dense).")
  ;; internal node helpers (field access lives only inside the deftype)
  (^:private -ensure!       [t id])
  (^:private -alloc!        [t])
  (^:private -free-subtree! [t node])
  (^:private -get-child     [t node tok-id])
  (^:private -add-child     [t node tok-id])
  (^:private -child-of      [t node tok-val])
  (^:private -child-arrays  [t node])
  (^:private -count-of      [t node])
  (^:private -dec-count!    [t node])
  (^:private -detach!       [t node tok-id])
  (^:private -edges         [t node])
  (^:private -leaves-of     [t node])
  (^:private -leaf-postings [t node])
  (^:private -node-at       [t prefix])
  (^:private -thaw!         [t]))

;; A `Trie` is in one of two modes.  **Mutable** (the default): a node-linked graph in the
;; grow-on-demand `counts`/`toks`/`tgts`/`leaves` arrays, supporting incremental
;; add/remove.  **Frozen** (after `t-compact!`): a read-optimized **CSR** — node i's child
;; edges are `[foffsets[i], foffsets[i+1])` in the parallel `fedge-tok`/`fedge-tgt` arrays
;; (sorted by token), its leaf handles `[fleaf-off[i], fleaf-off[i+1])` in `fhandles`, its
;; count `fcounts[i]`.  No per-node objects at all — the dense-native shape the bench
;; measured at ~11 MB.  The read primitives dispatch on `frozen?`, so `lookup`/`count-at`/
;; `children`/`leaves-at` are unchanged; a write (`t-insert!`/`t-remove!`) `-thaw!`s back to
;; mutable first, matching the bulk-load-then-query workload (compact once, then read).
;;
;; A frozen trie holds its leaf columns in **one of two places**, and that is the whole
;; residency split, and the walk is the half that must never page.  `fleaf-off` /
;; `fhandles` are heap `int[]` after a `t-compact!`, and `mleaf-off` / `mhandles` —
;; `IntBuffer` views of an mmap'd snapshot section — after `snapshot-install!` maps one.
;; The **skeleton** (`fcounts` `foffsets` `fedge-tok` `fedge-tgt`) is heap either way,
;; because the lookup walk reads it at every frontier node and a page fault there would
;; resurrect the leading-variable fan pathology at disk latency.  The leaves are read once,
;; at a walk's terminus, and are the fact-scaled mass — so they are what pages.  A write
;; thaws, which copies a mapped run into heap exactly as it rebuilds a frozen one.
;;
;; In mutable mode a node's edges are in one of two shapes, by width (see `promote-at`),
;; and `toks[i]` says which: nil for a leaf, a sorted `int[]` of tokens paralleled by
;; `tgts[i]` while narrow, an `Int2IntOpenHashMap` from token to child id (with `tgts[i]`
;; nil) once wide.  Only `-get-child` / `-add-child` / `-detach!` / `-child-arrays` /
;; `-edges` read the shape; everything above them is written against those five.
(deftype Trie [dict
               ^:unsynchronized-mutable ^ints    counts   ; counts[i]  = subtree leaf count
               ^:unsynchronized-mutable ^objects toks     ; toks[i]    = sorted int[] tokens | Int2IntOpenHashMap | nil
               ^:unsynchronized-mutable ^objects tgts     ; tgts[i]    = int[] child node ids parallel to toks[i] | nil
               ^:unsynchronized-mutable ^objects leaves   ; leaves[i]  = IntPostings | nil
               ^:unsynchronized-mutable ^int     cap
               ^:unsynchronized-mutable ^int     high     ; next fresh node id (high-water mark)
               ^ArrayDeque free                           ; recycled node ids (Integer)
               ^:unsynchronized-mutable          frozen?  ; CSR mode?
               ^:unsynchronized-mutable ^ints    fcounts  ; ── CSR arrays (nil when mutable) ──
               ^:unsynchronized-mutable ^ints    foffsets ; node i edges: [foffsets[i], foffsets[i+1])
               ^:unsynchronized-mutable ^ints    fedge-tok
               ^:unsynchronized-mutable ^ints    fedge-tgt
               ^:unsynchronized-mutable ^ints    fleaf-off ; node i leaves: [fleaf-off[i], fleaf-off[i+1])
               ^:unsynchronized-mutable ^ints    fhandles
               ^:unsynchronized-mutable          mleaf-off ; ── the same two, mapped (IntBuffer) ──
               ^:unsynchronized-mutable          mhandles] ;    exactly one pair is non-nil when frozen
  PTrie
  (-ensure! [_ id]
    (when (>= (int id) cap)
      (let [nc (max (inc (int id)) (* 2 cap))
            c2 (int-array nc) k2 (object-array nc) g2 (object-array nc) l2 (object-array nc)]
        (System/arraycopy counts 0 c2 0 cap)
        (System/arraycopy toks   0 k2 0 cap)
        (System/arraycopy tgts   0 g2 0 cap)
        (System/arraycopy leaves 0 l2 0 cap)
        (set! counts c2) (set! toks k2) (set! tgts g2) (set! leaves l2)
        (set! cap (int nc)))))

  (-alloc! [this]
    (let [id (if (.isEmpty free)
               (let [h high] (set! high (unchecked-inc-int high)) h)
               (.intValue ^Integer (.pop free)))]
      (-ensure! this id)
      (aset ^ints counts id (int 0))
      (aset ^objects toks   id nil)
      (aset ^objects tgts   id nil)
      (aset ^objects leaves id nil)
      id))

  (-free-subtree! [this node]
    (let [node (int node)
          ca   (-child-arrays this node)]
      (when ca
        (let [^ints tg (nth ca 1)]
          (dotimes [i (alength tg)] (-free-subtree! this (aget tg i)))))
      (aset ^ints counts node (int 0))
      (aset ^objects toks   node nil)
      (aset ^objects tgts   node nil)
      (aset ^objects leaves node nil)
      (.push free (Integer/valueOf node))
      nil))

  (-get-child [_ node tok-id]
    (let [tok-id (int tok-id) node (int node)]
      (if (neg? tok-id)
        -1
        (if frozen?
          (let [i (Arrays/binarySearch fedge-tok (aget ^ints foffsets node)
                                       (aget ^ints foffsets (inc node)) tok-id)]
            (if (>= i 0) (aget ^ints fedge-tgt i) -1))
          (let [ch (aget ^objects toks node)]
            (cond
              (nil? ch) -1
              (instance? Int2IntOpenHashMap ch)
              (.get ^Int2IntOpenHashMap ch tok-id)               ; default return value is -1
              :else
              (let [^ints ts ch
                    i (Arrays/binarySearch ts tok-id)]
                (if (>= i 0) (aget ^ints (aget ^objects tgts node) i) -1))))))))

  ;; The one place a fresh edge is minted, and the only place a node's edge structure
  ;; changes shape: return the child for `tok-id`, minting it (and widening the node's
  ;; edges past `promote-at`) when absent.  `-alloc!` can grow the OUTER parallel arrays,
  ;; so every per-node array is re-read AFTER calling it.
  (-add-child [this node tok-id]
    (let [node   (int node)
          tok-id (int tok-id)
          ch     (aget ^objects toks node)]
      (cond
        (nil? ch)
        (let [c (int (-alloc! this))]
          (aset ^objects toks node (int-array [tok-id]))
          (aset ^objects tgts node (int-array [c]))
          c)

        (instance? Int2IntOpenHashMap ch)
        (let [^Int2IntOpenHashMap m ch
              hit (.get m tok-id)]
          (if (>= hit 0)
            hit
            (let [c (int (-alloc! this))]                        ; the map object survives a grow
              (.put m tok-id c)
              c)))

        :else
        (let [^ints ts ch
              i (Arrays/binarySearch ts tok-id)]
          (if (>= i 0)
            (aget ^ints (aget ^objects tgts node) i)
            (let [c (int (-alloc! this))
                  ^ints ts (aget ^objects toks node)             ; re-read post-alloc
                  ^ints tg (aget ^objects tgts node)
                  n (alength ts)]
              (if (>= n (long promote-at))
                (let [^Int2IntOpenHashMap m (Int2IntOpenHashMap. (inc n))]
                  (.defaultReturnValue m (int -1))
                  (dotimes [j n] (.put m (aget ts j) (aget tg j)))
                  (.put m tok-id c)
                  (aset ^objects toks node m)
                  (aset ^objects tgts node nil)
                  c)
                (let [ip (dec (- i))
                      nt (int-array (inc n))
                      ng (int-array (inc n))]
                  (System/arraycopy ts 0 nt 0 ip)
                  (aset ^ints nt ip tok-id)
                  (System/arraycopy ts ip nt (inc ip) (- n ip))
                  (System/arraycopy tg 0 ng 0 ip)
                  (aset ^ints ng ip c)
                  (System/arraycopy tg ip ng (inc ip) (- n ip))
                  (aset ^objects toks node nt)
                  (aset ^objects tgts node ng)
                  c))))))))

  (-child-of [this node tok-val] (-get-child this node (tok/token-id dict tok-val)))

  ;; A node's edges as `[tokens targets]`, two parallel `int[]`s sorted by token, or nil
  ;; for a leaf — the shape-independent view compaction and subtree-freeing want.  Narrow
  ;; nodes hand back their own live arrays (no copy, so a caller must not mutate them);
  ;; a wide node's map is materialized and sorted, which is why the read paths that do not
  ;; need an order (`-edges`) do not come through here.  Mutable-only: writes thaw first.
  (-child-arrays [_ node]
    (let [node (int node)
          ch   (aget ^objects toks node)]
      (cond
        (nil? ch) nil
        (instance? Int2IntOpenHashMap ch)
        (let [^Int2IntOpenHashMap m ch
              ^IntSet ks (.keySet m)
              ^ints kt   (.toIntArray ks)
              n          (alength kt)
              ^ints tg   (int-array n)]
          (Arrays/sort kt)
          (dotimes [j n] (aset tg j (.get m (aget kt j))))
          [kt tg])
        :else [ch (aget ^objects tgts node)])))

  (-count-of [_ node] (if frozen? (aget ^ints fcounts (int node)) (aget ^ints counts (int node))))
  (-dec-count! [_ node] (let [node (int node)]
                          (aset ^ints counts node (unchecked-dec-int (aget ^ints counts node)))))

  (-detach! [_ node tok-id]
    (let [node   (int node)
          tok-id (int tok-id)
          ch     (aget ^objects toks node)]
      (cond
        (nil? ch) nil

        (instance? Int2IntOpenHashMap ch)
        (let [^Int2IntOpenHashMap m ch]
          (when (>= (.remove m tok-id) 0)
            (let [k (.size m)]
              (cond
                (zero? k) (aset ^objects toks node nil)
                (<= k (quot (long promote-at) 2))     ; narrow again — back to the dense pair
                (let [^IntSet ks (.keySet m)
                      ^ints kt   (.toIntArray ks)
                      ^ints tg   (int-array k)]
                  (Arrays/sort kt)
                  (dotimes [j k] (aset tg j (.get m (aget kt j))))
                  (aset ^objects toks node kt)
                  (aset ^objects tgts node tg))
                :else nil))))

        :else
        (let [^ints ts ch
              i (Arrays/binarySearch ts tok-id)]
          (when (>= i 0)
            (let [nlen (dec (alength ts))]
              (if (zero? nlen)
                (do (aset ^objects toks node nil) (aset ^objects tgts node nil))
                (let [^ints tg (aget ^objects tgts node)
                      nt (int-array nlen) ng (int-array nlen)]
                  (System/arraycopy ts 0 nt 0 i)
                  (System/arraycopy ts (inc i) nt i (- nlen i))
                  (System/arraycopy tg 0 ng 0 i)
                  (System/arraycopy tg (inc i) ng i (- nlen i))
                  (aset ^objects toks node nt)
                  (aset ^objects tgts node ng)))))))))

  ;; No reader of `children` depends on the order (the flat-map index answers it out of an
  ;; unordered set, `skip-one` mapcats, the projection sets it), so a wide node's edges come
  ;; off the map as they lie rather than through the sort `-child-arrays` would pay.
  (-edges [_ node]
    (let [node (int node)]
      (if frozen?
        (let [lo (aget ^ints foffsets node) hi (aget ^ints foffsets (inc node))]
          (mapv (fn [e] [(tok/id-token dict (aget ^ints fedge-tok (int e))) (aget ^ints fedge-tgt (int e))])
                (range lo hi)))
        (let [ch (aget ^objects toks node)]
          (cond
            (nil? ch) []
            (instance? Int2IntOpenHashMap ch)
            (let [^Int2IntOpenHashMap m ch
                  ^IntSet ks (.keySet m)
                  ^ints kt   (.toIntArray ks)]
              (mapv (fn [i] (let [t (aget kt (int i))] [(tok/id-token dict t) (.get m t)]))
                    (range (alength kt))))
            :else
            (let [^ints ts ch
                  ^ints tg (aget ^objects tgts node)]
              (mapv (fn [i] [(tok/id-token dict (aget ts (int i))) (aget tg (int i))])
                    (range (alength ts)))))))))

  (-leaf-postings [_ node] (aget ^objects leaves (int node)))     ; mutable-only (writes thaw first)
  (-leaves-of [_ node]
    (let [node (int node)]
      (cond
        ;; mapped: the two reads that touch the file, and the only ones — the walk that
        ;; reached this node ran entirely on the resident skeleton
        mhandles
        (let [^IntBuffer lo mleaf-off
              ^IntBuffer hs mhandles]
          (loop [e (.get lo node), hi (.get lo (inc node)), s (transient #{})]
            (if (< e hi) (recur (inc e) hi (conj! s (long (.get hs (int e))))) (persistent! s))))

        frozen?
        (loop [e (aget ^ints fleaf-off node), hi (aget ^ints fleaf-off (inc node)), s (transient #{})]
          (if (< e hi) (recur (inc e) hi (conj! s (long (aget ^ints fhandles (int e))))) (persistent! s)))

        :else
        (let [lp (aget ^objects leaves node)] (if lp (postings/pmembers lp) #{})))))

  (-node-at [this prefix]
    (loop [node 0, ps (seq prefix)]
      (if ps
        (let [c (-child-of this node (first ps))]
          (if (neg? c) -1 (recur (long c) (next ps))))
        node)))

  (t-insert! [this path handle]
    (when frozen? (-thaw! this))                                        ; a write reverts to mutable
    (aset ^ints counts 0 (unchecked-inc-int (aget ^ints counts 0)))     ; root count
    (loop [node 0, ps (seq path)]
      (if ps
        (let [tok-id (int (tok/intern-token! dict (first ps)))
              child  (long (-add-child this (int node) tok-id))]
          (aset ^ints counts (int child) (unchecked-inc-int (aget ^ints counts (int child))))
          (recur child (next ps)))
        (let [node (int node)
              lp (or (aget ^objects leaves node)
                     (let [p (postings/int-postings)] (aset ^objects leaves node p) p))]
          (postings/padd! lp handle))))
    nil)

  ;; Answers the count of this path's own nodes that emptied, which the workload
  ;; instrument prices as `:dead` (`vaelii.impl.profile`).  Counted from `t` — the
  ;; topmost node whose count reached zero — rather than from `cut`, so the number means
  ;; the same here as the flat store's, which counts the path prefixes that emptied and
  ;; has no dead-root special case to work around.
  (t-remove! [this path handle]
    (when frozen? (-thaw! this))                                        ; a write reverts to mutable
    (let [pv (vec path)
          n  (count pv)]
      (loop [node 0, i 0, nodes (transient [0]), tids (transient [])]
        (if (< i n)
          (let [tid (tok/token-id dict (nth pv i))
                c   (long (if (neg? tid) -1 (-get-child this node tid)))]
            (if (neg? c)
              -1                                                 ; absent path ⇒ nothing to remove
              (recur c (inc i) (conj! nodes c) (conj! tids tid))))
          (let [nodes (persistent! nodes)                        ; n+1 entries: root..terminus
                tids  (persistent! tids)
                lp    (-leaf-postings this (nth nodes n))]
            ;; gated on the handle being at the leaf: the counts below come down without
            ;; looking, and a node that reaches zero is freed with its whole subtree, so a
            ;; stray remove — a handle never stored here, or already taken out — would cut
            ;; live nodes and every sentex under them.  One `pcontains?` makes it a no-op.
            (if-not (and lp (postings/pcontains? lp handle))
              -1
              (do
                (postings/prem! lp handle)
                (dotimes [k (inc n)] (-dec-count! this (nth nodes k)))
                ;; counts are non-increasing down the path, so the dead nodes are a
                ;; suffix; cut the topmost one from its (live) parent and free its
                ;; subtree.  A dead root (empty KB) is never removed — cut its single
                ;; remaining child instead.
                (let [t (loop [k 0]
                          (cond (> k n) -1
                                (<= (-count-of this (nth nodes k)) 0) k
                                :else (recur (inc k))))]
                  (if (neg? t)
                    0
                    (let [cut (if (zero? t) 1 t)]
                      (when (<= cut n)
                        (-detach! this (nth nodes (dec cut)) (nth tids (dec cut)))
                        (-free-subtree! this (nth nodes cut)))
                      (- (inc n) t)))))))))))

  (t-count-at [this prefix]
    (let [nd (-node-at this prefix)] (if (neg? nd) 0 (-count-of this nd))))

  (t-children [this prefix]
    (let [nd (-node-at this prefix)]
      (if (neg? nd) [] (mapv first (-edges this nd)))))

  ;; The width off each representation's own shape, decoding nothing: an edge-array span
  ;; in the frozen sections, the map's size or the token array's length while mutable.
  ;; `(count (t-children …))` would be the same number for O(width) work and one vector
  ;; per call, and the planner asks this once per literal per plan.
  (t-child-count [this prefix]
    (let [nd (int (-node-at this prefix))]
      (if (neg? nd)
        0
        (if frozen?
          (- (aget ^ints foffsets (inc nd)) (aget ^ints foffsets nd))
          (let [ch (aget ^objects toks nd)]
            (cond
              (nil? ch)                          0
              (instance? Int2IntOpenHashMap ch)  (.size ^Int2IntOpenHashMap ch)
              :else                              (alength ^ints ch)))))))

  (t-leaves-at [this prefix]
    (let [nd (-node-at this prefix)] (if (neg? nd) #{} (-leaves-of this nd))))

  ;; The structural lookup walk — identical in shape to `KvIndexStore/lookup`, over node
  ;; ids instead of prefix vectors: a variable fans over a node's whole child set
  ;; (`skip-one`), skipping the subtree a `[::subterm k]` marker spans; a concrete token
  ;; advances one edge; markers/handles never mix (edges are tokens, leaves are separate).
  (t-lookup [this pattern]
    (letfn [(skip-one [node]
              (mapcat (fn [[tok-val child]]
                        (if (sentex-types/subterm-mark? tok-val)
                          (skip-n child (sentex-types/subterm-arity tok-val))
                          [child]))
                      (-edges this node)))
            (skip-n [node m]
              (if (zero? m) [node] (mapcat #(skip-n % (dec m)) (skip-one node))))]
      (loop [frontier [0], qs (seq pattern)]
        (if (nil? qs)
          (into #{} (mapcat #(-leaves-of this %)) frontier)
          (let [q (first qs)
                frontier' (into []
                                (mapcat
                                 (fn [node]
                                   (if (sentex-types/variable? q)
                                     (skip-one node)
                                     (let [c (-child-of this node q)]
                                       (if (and (>= c 0) (pos? (-count-of this c))) [c] [])))))
                                frontier)]
            (recur frontier' (next qs)))))))

  (t-clear! [this]                          ; resets the trie arrays only — the dict is
    (set! counts (int-array init-cap))      ; shared with the roots backend, so the store
    (set! toks   (object-array init-cap))   ; clears it once (see clear-index!)
    (set! tgts   (object-array init-cap))
    (set! leaves (object-array init-cap))
    (set! cap    (int init-cap))
    (set! high   (int 0))
    (.clear free)
    (set! frozen? false)                    ; drop any frozen (or mapped) CSR state
    (set! fcounts nil) (set! foffsets nil) (set! fedge-tok nil)
    (set! fedge-tgt nil) (set! fleaf-off nil) (set! fhandles nil)
    (set! mleaf-off nil) (set! mhandles nil)
    (-alloc! this)                          ; re-mint node 0 = root
    nil)

  ;; Freeze the mutable graph into CSR.  Nodes are renumbered in DFS preorder (root = 0),
  ;; which also compacts away the id holes a churny load's `-free-subtree!` left.  Every
  ;; pass takes a node's edges through `-child-arrays`, so the per-node run lands sorted by
  ;; token whichever shape the mutable node was holding, which is what the frozen
  ;; `-get-child`'s binary search needs.
  (t-compact! [this]
    (when-not frozen?
      (let [order (java.util.ArrayList.)             ; oldId in preorder — new id = its index
            ^ints newid (int-array (max 1 high) -1)   ; oldId -> newId
            stack (ArrayDeque.)]
        (.push stack (Integer/valueOf 0))
        (loop []
          (when-not (.isEmpty stack)
            (let [old (.intValue ^Integer (.pop stack))]
              (when (neg? (aget newid old))
                (aset newid old (int (.size order)))
                (.add order (Integer/valueOf old))
                (when-let [ca (-child-arrays this old)]
                  (let [^ints tg (nth ca 1)
                        n (alength tg)]
                    (dotimes [j n]                    ; push in reverse so preorder is sorted
                      (.push stack (Integer/valueOf (aget tg (- n 1 j))))))))
              (recur))))
        (let [nn   (.size order)
              ^ints fcnt  (int-array nn)
              ^ints foff  (int-array (inc nn))
              ^ints floff (int-array (inc nn))]
          (dotimes [i nn]                              ; pass 1: counts + edge/leaf offsets
            (let [old (.intValue ^Integer (.get order i))
                  ca  (-child-arrays this old)
                  lp  (aget ^objects leaves old)]
              (aset fcnt i (aget ^ints counts old))
              (aset foff  (inc i) (int (+ (aget foff  i)
                                          (if ca (let [^ints kt (nth ca 0)] (alength kt)) 0))))
              (aset floff (inc i) (+ (aget floff i) (int (if lp (postings/pcard lp) 0))))))
          (let [^ints ftok (int-array (aget foff  nn))
                ^ints ftgt (int-array (aget foff  nn))
                ^ints fh   (int-array (aget floff nn))]
            (dotimes [i nn]                             ; pass 2: fill edges + handles
              (let [old  (.intValue ^Integer (.get order i))
                    base (aget foff i)]
                (when-let [ca (-child-arrays this old)]
                  (let [^ints kt (nth ca 0)
                        ^ints tg (nth ca 1)]
                    (dotimes [j (alength kt)]
                      (aset ftok (+ base j) (aget kt j))
                      (aset ftgt (+ base j) (aget ^ints newid (aget tg j))))))   ; remap target
                ;; **A leaf run is laid down ascending by handle**, which is what `pints`
                ;; hands back.  Filling it from `pmembers` instead builds a Clojure set
                ;; first and lays the run down in *hash* order — an ordering that is a
                ;; function of how the set was assembled as well as of what is in it, so
                ;; the same index could freeze to two different byte layouts.  Handle
                ;; order is the right order to fix on because this is a byte layout and
                ;; not a belief question: every reader takes a run as a whole set, none
                ;; reads its order for meaning, and the postings already hold it that way.
                (when-let [lp (aget ^objects leaves old)]
                  (let [^ints hs (postings/pints lp)]
                    (System/arraycopy hs 0 fh (aget floff i) (alength hs))))))
            (set! fcounts fcnt) (set! foffsets foff) (set! fedge-tok ftok)
            (set! fedge-tgt ftgt) (set! fleaf-off floff) (set! fhandles fh)
            (set! frozen? true)
            (set! counts (int-array 0)) (set! toks (object-array 0))    ; free the mutable graph
            (set! tgts (object-array 0)) (set! leaves (object-array 0))
            (set! cap (int 0)) (set! high (int 0)) (.clear free)))))
    nil)

  ;; Rebuild the mutable graph from CSR (a write reverts to mutable).  The CSR node ids
  ;; become the mutable ids, edges stay sorted, so the mutable invariants hold immediately.
  ;; Each node's shape is re-derived from its actual width here rather than remembered, so
  ;; a compact/thaw cycle is also where a node that shrank while frozen gets its dense pair
  ;; back — and where one that grew arrives already wide instead of splicing its way there.
  ;;
  ;; A **mapped** trie thaws by copying its leaf run into heap first: a write needs
  ;; `IntPostings` it can splice, and there is no half-mapped mode to fall into.  That copy
  ;; is the honest price of the first write after a mapped open, and it is why the snapshot
  ;; is a read-phase structure rather than a live one.
  (-thaw! [_this]
    (when frozen?
      (let [^ints loff (if mleaf-off (buf->ints mleaf-off) fleaf-off)
            ^ints hnds (if mhandles  (buf->ints mhandles)  fhandles)
            nn   (dec (alength foffsets))
            cap2 (max init-cap nn)
            ^ints c (int-array cap2) ^objects tk (object-array cap2)
            ^objects tg (object-array cap2) ^objects lv (object-array cap2)]
        (dotimes [i nn]
          (aset ^ints c i (aget ^ints fcounts i))
          (let [lo (aget ^ints foffsets i) hi (aget ^ints foffsets (inc i)) ne (- hi lo)]
            (when (pos? ne)
              (if (> ne (long promote-at))
                (let [^Int2IntOpenHashMap m (Int2IntOpenHashMap. ne)]
                  (.defaultReturnValue m (int -1))
                  (dotimes [j ne]
                    (.put m (aget ^ints fedge-tok (+ lo j)) (aget ^ints fedge-tgt (+ lo j))))
                  (aset ^objects tk i m))
                (let [^ints nt (int-array ne) ^ints ng (int-array ne)]
                  (dotimes [j ne]
                    (aset ^ints nt j (aget ^ints fedge-tok (+ lo j)))
                    (aset ^ints ng j (aget ^ints fedge-tgt (+ lo j))))
                  (aset ^objects tk i nt) (aset ^objects tg i ng)))))
          (let [llo (aget loff i) lhi (aget loff (inc i))]
            (when (< llo lhi)
              (let [p (postings/int-postings)]
                (loop [e llo] (when (< e lhi) (postings/padd! p (aget hnds (int e))) (recur (inc e))))
                (aset ^objects lv i p)))))
        (set! counts c) (set! toks tk) (set! tgts tg) (set! leaves lv)
        (set! cap (int cap2)) (set! high (int nn)) (.clear free)
        (set! frozen? false)
        (set! fcounts nil) (set! foffsets nil) (set! fedge-tok nil)
        (set! fedge-tgt nil) (set! fleaf-off nil) (set! fhandles nil)
        (set! mleaf-off nil) (set! mhandles nil)))
    nil)

  snapshot-types/SnapshotSections
  (snapshot-mapped? [_] (some? mhandles))

  ;; The frozen sections, whichever place they live in — the snapshot writer's read of
  ;; the trie, and nil while mutable so a caller must compact first rather than write a
  ;; half-frozen image.  The trie's sections are a function of the trie alone, so `opts`
  ;; carries nothing for it.
  (snapshot-read [_ _opts]
    (when frozen?
      {:nodes    (dec (alength foffsets))
       :counts   fcounts   :offsets  foffsets
       :edge-tok fedge-tok :edge-tgt fedge-tgt
       :leaf-off (or fleaf-off mleaf-off)
       :handles  (or fhandles mhandles)}))

  ;; Install sections read back from a snapshot.  The skeleton is always heap `int[]`;
  ;; the leaf pair arrives either as heap arrays or as `IntBuffer`s over an mmap'd
  ;; region, and which it is *is* the residency decision — nothing below here cares.
  ;; The section names carry a `*` because `counts`, `toks`, `tgts` and `leaves` are
  ;; fields of this type, and a destructured binding of one would shadow the field the
  ;; `set!` beside it assigns.
  (snapshot-install! [_ {:keys [counts* offsets* edge-tok* edge-tgt* leaf-off* handles*]}]
    (set! fcounts counts*) (set! foffsets offsets*)
    (set! fedge-tok edge-tok*) (set! fedge-tgt edge-tgt*)
    (if (instance? IntBuffer handles*)
      (do (set! mleaf-off leaf-off*) (set! mhandles handles*)
          (set! fleaf-off nil) (set! fhandles nil))
      (do (set! fleaf-off leaf-off*) (set! fhandles handles*)
          (set! mleaf-off nil) (set! mhandles nil)))
    (set! frozen? true)
    (set! counts (int-array 0)) (set! toks (object-array 0))    ; no mutable graph beside it
    (set! tgts (object-array 0)) (set! leaves (object-array 0))
    (set! cap (int 0)) (set! high (int 0)) (.clear free)
    nil))

(defn make-trie [dict]
  (let [t (->Trie dict (int-array init-cap) (object-array init-cap)
                  (object-array init-cap) (object-array init-cap) init-cap 0 (ArrayDeque.)
                  false nil nil nil nil nil nil nil nil)]
    (-alloc! t)                             ; node 0 = root
    t))

(defn trie-entries
  "Every node of `trie` as `[[:trie :count|:children|:handles prefix] value]`, in the flat
  index's own key shape.  Lazy and depth-first, so a corpus-sized trie streams."
  [trie]
  (letfn [(walk [node prefix]
            (lazy-seq
             (let [edges (-edges trie node)
                   cnt   (long (-count-of trie node))
                   lvs   (-leaves-of trie node)]
               (concat
                ;; a node with no sentexes under it does not exist in the flat index —
                ;; its counter is deleted when it hits zero — and the empty root of an
                ;; empty KB is the one node here that can be in that state.
                (when (pos? cnt) [[[:trie :count prefix] cnt]])
                (when (seq edges) [[[:trie :children prefix] (into #{} (map first) edges)]])
                (when (seq lvs) [[[:trie :handles prefix] lvs]])
                (mapcat (fn [[tok child]] (walk child (conj prefix tok))) edges)))))]
    (walk 0 [])))
