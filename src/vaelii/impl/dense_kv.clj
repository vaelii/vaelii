;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-kv
  "A dense in-memory `KvBackend` (`vaelii.impl.kv`) — the `:dense` index axis, under either
  record store (`:memory-dense`, `:disk-dense`).

  The index's handle-set families (trie leaves, the context / functor / argument roots, the
  rule and exception indexes) are the bulk of its RAM, and a bake-off across candidate
  encodings found a **packed sorted `int[]`** ~5.6× denser than the
  `PersistentHashSet<Long>` the memory backend stores, with `RoaringBitmap` winning only the
  few large/hot postings.  So a handle set here is an `IntPostings`: an exact sorted `int[]`
  while small, promoted to a `RoaringBitmap` once it crosses a threshold (dense for large,
  O(log) add, fast intersect).  The trie's child-*label* set (`[:trie :children …]`) holds tokens —
  including numbers — not handles, so it stays an ordinary set; counters stay `Long`s.  The
  backend dispatches on the key tag.

  `kv-intersect` narrows **in that representation** rather than in the sets it would make:
  `RoaringBitmap/and` where both sides are hot, a sorted merge where both are cold, and a
  probe of the cold side into the bitmap where the tiers differ, and a binary search of the
  short run into the long one where neither is a bitmap.  Smallest posting first, and one
  Clojure set built at the end at the size of the answer.  What that buys is not mainly
  speed on the big case (hot ∩ hot at 32k: 29.2 → 0.56 ms) but the *shape* of the common
  one: a query pins a rare argument on a hot predicate, and 4 handles against a root of n
  went from 4.73 ms at n=32,000 to 0.0015 ms at any n — flat in the extent the argument
  roots exist to avoid scanning.  `lein perf --only intersect-selectivity` is the gate on
  that, and what cost is left tracks the answer rather than the columns, which is the
  boundary contract and not the narrowing.

  Off by default (`:index :dense`); proven set-equal to `MemoryKvBackend` by
  `dense_kv_oracle_test`.  Single-writer: the int structures are mutated in place, and
  `kv-members` / `kv-intersect` materialize a fresh Clojure set at the boundary so a caller
  never holds the mutable structure.  Handles fit `int` through 2³¹ (≫ 100M)."
  (:require [clojure.set :as set]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.postings :as postings
             :refer [as-set int-postings intersect-postings padd! pcard pcontains?
                     pmembers prem!]])
  (:import [vaelii.impl.types.postings IntPostings]))

(defn- intersect
  "Intersection of the posting values as a Clojure set.  A handle family holds
  `IntPostings`, and those narrow in their own representation; any other key holds an
  ordinary set whose members are not handles at all (path tokens, term names), so a list
  containing one folds `clojure.set/intersection` smallest-first instead."
  [vals]
  (if (every? #(instance? IntPostings %) vals)
    (intersect-postings vals)
    (let [sets (sort-by count (map as-set vals))]
      (reduce set/intersection sets))))

;; ---- the backend --------------------------------------------------------

(defn- handle-key?
  "Does `k` name a HANDLE set (int postings)?  Handle sets: trie leaves `[:trie :handles …]`, and
  the roots/indexes under `:context-root` `:functor-root` `:argument-root` `:term-index` `:rule-index` `:exception-index`.  The trie
  child-token set `[:trie :children …]` (tokens, incl. numbers), the counter `[:trie :count …]`
  and the term roster `[:term-roster]` (term *names*) are not — they stay an ordinary set / a Long.

  A key this fails to recognize is stored boxed and answers every read identically, so
  nothing behavioural can catch a spelling that drifts from the one `vaelii.impl.kv`
  writes; `dense_routing_test` checks the stored representation instead."
  [k]
  (and (vector? k)
       (case (first k)
         :trie (= :handles (second k))
         (:context-root :functor-root :argument-root :term-index :rule-index :exception-index) true
         false)))

(defrecord TieredKvBackend [state]
  p/KvBackend
  (kv-get  [_ k]   (get @state k))
  (kv-put  [_ k v] (swap! state assoc k v) nil)
  (kv-delete  [_ k]   (swap! state dissoc k) nil)
  (kv-increment [_ k]   (long (get (swap! state update k (fnil inc 0)) k)))
  ;; floored at 0 — a counter is a cardinality, and the dense store answers a decrement
  ;; as the flat one does or the oracles comparing them stop meaning anything
  ;; (`p/KvBackend`, `dense_kv_oracle_test`)
  (kv-decrement [_ k]   (long (get (swap! state update k
                                          (fn [v] (max 0 (dec (long (or v 0))))))
                                   k)))

  (kv-add-to-set [_ k m]
    (if (handle-key? k)
      (padd! (or (get @state k) (let [p (int-postings)] (swap! state assoc k p) p)) m)
      (swap! state update k (fnil conj #{}) m))
    nil)
  (kv-remove-from-set [_ k m]
    (if (handle-key? k)
      (when-let [p (get @state k)]
        (prem! p m)
        (when (zero? (pcard p)) (swap! state dissoc k)))          ; empty set == absent
      (swap! state (fn [st] (let [s (disj (get st k) m)]
                              (if (empty? s) (dissoc st k) (assoc st k s))))))
    nil)
  (kv-members [_ k] (as-set (get @state k)))
  ;; the probe, straight into whichever representation the key holds — a handle set is
  ;; searched or bitmap-tested in place, so a caller asking "is this handle here?" never
  ;; pays for the Clojure set `kv-members` has to build
  (kv-member? [_ k m] (let [v (get @state k)]
                        (cond (nil? v)                  false
                              (instance? IntPostings v) (pcontains? v m)
                              :else                     (contains? v m))))
  (kv-count    [_ k] (let [v (get @state k)]
                       (cond (nil? v) 0
                             (instance? IntPostings v) (pcard v)
                             :else (count v))))
  (kv-intersect [_ ks]
    (if (empty? ks)
      #{}
      (let [st @state, vals (mapv #(get st %) ks)]
        (if (some nil? vals) #{} (intersect vals)))))       ; a missing key ⇒ empty

  (kv-batch [this ops]
    (mapv (fn [[op k a]]
            (case op
              :put  (do (p/kv-put  this k a) nil)
              :delete  (do (p/kv-delete  this k) nil)
              :increment (p/kv-increment this k)
              :decrement (p/kv-decrement this k)
              :add-to-set (do (p/kv-add-to-set this k a) nil)
              :remove-from-set (do (p/kv-remove-from-set this k a) nil)
              ;; `p/unknown-op!` rather than `case`'s bare IllegalArgumentException:
              ;; every adapter refuses an unreadable op by the one name a caller
              ;; discriminates on (`:unknown-frame`)
              (p/unknown-op! op)))
          ops))
  ;; the portable projection: an `IntPostings` is this backend's private representation
  ;; of a handle set, so it is materialized out on the way and rebuilt on the way back
  ;; in.  A `kv-put` of a plain set would look like it worked and then blow up on the
  ;; next `kv-add-to-set`, which is why the install is its own operation.
  (kv-entries [_] (map (fn [[k v]] [k (if (instance? IntPostings v) (pmembers v) v)]) @state))
  (kv-load [_ entries]
    (swap! state into
           (map (fn [[k v]]
                  [k (if (and (handle-key? k) (set? v))
                       (reduce padd! (int-postings) v)
                       v)]))
           entries)
    nil)

  (kv-clear! [_] (reset! state {}) nil))

;; ---- construction (space-number sharing, like the memory backend) ----------

(defonce ^:private index-spaces (atom {}))

(defn- space-atom [space]
  (or (@index-spaces space)
      (-> (swap! index-spaces (fn [m] (if (m space) m (assoc m space (atom {})))))
          (get space))))

(defn dense-kv-backend
  "A dense in-memory `KvBackend`.  Only `:space` matters (selects the shared state atom)."
  [{:keys [space] :or {space 0}}]
  (->TieredKvBackend (space-atom space)))

(defn dense-index-store
  "A dense in-memory `IndexStore` — `KvIndexStore` over a `TieredKvBackend`."
  [opts]
  (kv/->KvIndexStore (dense-kv-backend opts)))

(defn drop-index-space!
  "Forget the derived index state held under `space` — the dense twin of
  `vaelii.impl.memory/drop-index-space!`, `core/close!`'s release of the RAM index a
  disk-backed KB derived.  A no-op for a `space` nothing holds; returns true when an entry
  was dropped."
  [space]
  (let [had? (contains? @index-spaces space)]
    (swap! index-spaces dissoc space)
    had?))
