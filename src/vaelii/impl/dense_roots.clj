;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-roots
  "A key-interning `KvBackend` (`vaelii.impl.kv`) for the columnar index's non-trie
  families — the secondary roots, the rule / exception indexes, and the inverted term
  index.

  Those families are flat `structured-vector-key → handle-set` maps, and the columnar
  measurement (`bench/…/densetrie.clj`) found their **boxed vector keys**
  (`[:term-index term]`, `[:functor-root pred]`, …) to be ~150 MB — the majority of the
  columnar index once the trie went native.  This backend keeps the *values* as
  `IntPostings` (Phase 1's tiered
  `int[]`/Roaring set) but collapses the keys: the term is interned to an `int` through
  the **shared trie dictionary** (`vaelii.impl.tokens`) — so a predicate/individual gets
  the same id the trie edges use — and the whole key becomes one packed `long`
  (`family | pos | term-id`) into a single primitive `Long2ObjectOpenHashMap`.  No boxed
  vectors, no HAMT nodes, one map.

  It stays a full `KvBackend` so the existing composition (an embedded `KvIndexStore`
  over it) is unchanged: only the recognized index families are int-routed; any other key
  — the slot roster and the term roster (whose members are *names*, not handles), a
  scalar, a counter, the contract test's synthetic keys — falls back to a plain in-memory
  backend (in the columnar store the trie is native, so no `[:trie …]` key ever reaches
  here).

  **Every handle family routes**, the predicate-scoped argument roots included: their
  `(pred, pos)` scope is interned to a dense id of its own (`argfam-id`) and rides the
  `pos` field, which no other family uses.  So the fallback holds only vocabulary-scaled
  name sets, and the fact-scaled mass is one packed map — or, under a snapshot, one
  mapped run.  Single-writer, like every index;
  `kv-members` / `kv-intersect` materialize a fresh Clojure set at the boundary — but
  `kv-intersect` builds it at the size of the *answer*, narrowing through
  `postings/intersect-postings` in whichever representation each posting is in, a mapped run
  included.  Proven set-equal to `MemoryKvBackend` on the index families by
  `dense_roots_oracle_test` —
  which, like every behavioural check, cannot see a family that falls back when it should
  route, since the fallback answers identically; `dense_routing_test` reads the
  representation and covers that.

  **Single-*threaded*, which is narrower than single-writer.**  The mapped-section fields
  on `DenseRoots` are `^:unsynchronized-mutable`, so installing or thawing a snapshot
  publishes through no barrier and a second thread may read this backend mid-install —
  `mapped?` true against a `mkeys` it has not seen, say.  The atom- and lock-based
  backends give an incidental reader beside the writer a consistent view; this one does
  not.  Same trade as `vaelii.impl.columnar`, whose docstring states it: these fields are
  read on the hot lookup path, and a volatile read there buys a guarantee the engine's own
  single writer never needs."
  (:require [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.dense-roots :as dense-roots-types])
  (:import [it.unimi.dsi.fastutil.longs Long2ObjectOpenHashMap]
           [vaelii.impl.types.dense_roots DenseRoots]))

;; ---- the argument columns, and why this backend takes the default ------
;;
;; `ArgColumns` (`vaelii.impl.kv`) names the three shapes a settle asks the
;; argument-root family for: a scoped leaf, the predicate-agnostic union at a
;; `(pos, term)` node, and that node's cardinality.  The in-memory backend overrides it
;; with a counted `::arg` trie and answers all three as node reads; every other backend
;; takes the `Object` default, which spells the keys and folds the generic set ops.
;;
;; This backend takes the default, and the two halves of that are worth separating.
;;
;; **The scoped reads are packed reads.**  `arg-scoped-members` is one packed-long lookup
;; and `arg-scoped-intersect` one `kv-intersect` over packed keys — no consed vector, no
;; `doEquiv`, and the narrowing runs in the postings' own representation, a mapped run
;; included.  These are the reads `sentexes-with-args` makes for a named functor, which is
;; the overwhelmingly common query shape.
;;
;; **The agnostic reads cost one extra lookup.**  The default reaches them over the
;; slot roster — `[:argument-slot pos term]` → the predicates present there — and then
;; unions the scoped postings.  That roster is *one predicate* in the common case (a
;; term occupies a given position under one predicate; `kv.clj`, `sentexes-with-arg`),
;; so the union is a single set handed straight back and the cost over a maintained node
;; union is the roster read itself.  A handful of predicates is a handful of packed
;; lookups.
;;
;; Maintaining an agnostic union here instead would mean a second posting per
;; `(pos, term)` holding what the scoped postings already hold — the family's whole
;; fact-scaled mass, stored twice — to save one lookup on a read that is usually a union
;; of one.  The roster is already maintained and already vocabulary-scaled.  So the
;; default is the right reading of this representation rather than a gap in it, and the
;; trie's advantage stays where it is paid for: in RAM, on the memory backend.

(defn dense-roots
  "A key-interning `KvBackend` sharing `dict` (the columnar trie's token dictionary) so a
  term interned by the trie and by a root get the same id."
  [dict]
  (dense-roots-types/->DenseRoots dict (tok/token-dict) (Long2ObjectOpenHashMap.)
                                  (mem/->MemoryKvBackend (atom {}))
                                  nil nil nil 0))

(defn fallback-entries
  "The entries the routed families do **not** claim: the term roster and the slot roster,
  whose members are *names* rather than handles.  Both are **vocabulary-scaled**, which
  is what lets a snapshot write them as one nippy blob and load them resident without
  the blob tracking the fact count (`disk/index_snapshot.clj`, \"The residency split\")."
  [^DenseRoots b] (p/kv-entries (.-fallback b)))

(defn load-fallback! [^DenseRoots b entries] (p/kv-load (.-fallback b) entries) nil)

;; ---- the scope dictionary, as a snapshot section ------------------------
;; The packed argument keys cite scope ids, so an image that carries the keys has to
;; carry the table that decodes them.  It rides `roots.csr` — the file whose key column
;; is its only reader — rather than a log beside `tokens.log`, and the reason is the
;; failure each shape can have.  `tokens.log` is durable ground truth: appended as facts
;; arrive, cited by the mapped trie edges, and able to disagree with an image written at
;; some other time — which is what `:duplicate-tokens` exists to repair.  This table is
;; written in the same pass as the column that cites it and discarded with it, so the two
;; cannot drift apart at all.  A second log would buy nothing and inherit that repair.

(defn argfam-table
  "The scope dictionary as `{:preds int[] :positions int[]}`, indexed by scope id, with
  each predicate taken through `remap` into the durable dictionary's id space — the same
  `int[]` the packed keys' term halves are remapped by.

  A pair's predicate is interned into the term dictionary when the pair is
  (`argfam-id`), so every id here has a term id to be written as."
  [^DenseRoots b ^ints remap]
  (let [af (.-argfam b)
        n  (long (tok/token-count af))
        ps (int-array n)
        qs (int-array n)]
    (dotimes [i n]
      (let [[pred pos] (tok/id-token af i)]
        (aset ps i (int (aget remap (int (tok/token-id (.-dict b) pred)))))
        (aset qs i (int pos))))
    {:preds ps :positions qs}))

(defn load-argfam!
  "Rebuild the scope dictionary from a snapshot's table, ids implied by position — the
  same first-writer-wins order `vaelii.impl.tokens` allocates in, so an id read out of a
  packed key names the pair it named when the image was written."
  [^DenseRoots b ^ints preds ^ints positions n]
  (let [af   (.-argfam b)
        dict (.-dict b)]
    (tok/clear-tokens! af)
    (dotimes [i (long n)]
      (tok/intern-token! af [(tok/id-token dict (aget preds i)) (aget positions i)]))
    (let [loaded (long (tok/token-count af))]
      (when (not= loaded (long n))
        (throw (ex-info (str "the argument-root scope dictionary reloaded as " loaded
                             " entries where the image holds " n
                             " — the ids the packed keys cite have shifted")
                        {:type :torn-snapshot :loaded loaded :entries n})))))
  nil)

