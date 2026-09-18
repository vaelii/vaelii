;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.capabilities
  "The callers' entry point to the **optional** storage capabilities: one function per
  capability that uses it when the store has it and falls back to the plain
  `RecordStore` op when it does not.

  It is beside `vaelii.impl.protocols` rather than in it because that file is
  protocol-only — the `IndexStore` declaration there is large enough that
  re-evaluating the form (as cloverage does, form by form, to instrument a
  namespace) overflows the JVM's 64 KB per-method bytecode limit, so the whole
  namespace is loaded but not instrumented (scripts/coverage.sh).  A protocol
  carries no code to cover; these fallbacks do, and here they stay measured.
  `vaelii.impl.jtms-protocol` is split from `vaelii.impl.jtms` for the same reason.

  Each entry point is the same shape: `satisfies?` the capability, take its op, else the
  loop it replaces.  A caller therefore never branches on a capability, and a store
  without one reads exactly as it did before the capability existed.  `hinting` and
  `recovery-hint-chunk` are not entry points but the chunking a prefetch entry point is used
  through, which is why they sit here beside it."
  (:require [vaelii.impl.protocols :as p]))

(defn prefetcher
  "`(fn [ids] …)` hinting **sentexes** to `store`, or **nil** when it does not prefetch.

  Resolved once per walk rather than tested per chunk, and the nil is the point: a caller
  branches on it once and then runs its ordinary per-handle loop, so a store without the
  capability pays nothing for the existence of the capability."
  [store]
  (when (satisfies? p/Prefetching store)
    (fn [ids] (p/prefetch-sentexes! store ids))))

(defn justification-prefetcher
  "`(fn [ids] …)` hinting **justifications** to `store`, or nil — `prefetcher`'s twin."
  [store]
  (when (satisfies? p/Prefetching store)
    (fn [ids] (p/prefetch-justifications! store ids))))

(def recovery-hint-chunk
  "Handles per hint on a walk that consumes **all** of them — `reindex` over the records,
  `recover` over the justifications.

  Such a walk needs no setting to gate it and does not have one.  The chunk size on the
  *query* path is a trade (a consumer that stops early has over-fetched a chunk), which is
  why that one is off by default; a recovery walk reads every handle it is given, so a
  hint there can only save round trips and never waste one.  Large, because the only cost
  of a bigger chunk here is the store's own cache bound, which it applies itself."
  1000)

(defn hinting
  "`ids` unchanged, with each chunk of `n` handed to `hint` before that chunk is yielded.

  The element sequence is identity — same handles, same order, duplicates kept — so a walk
  wraps its enumeration in this and is otherwise the walk it was, and `hint` nil is that
  walk exactly, with no chunking at all.

  **One chunk is in flight, and that is why this is not `mapcat`.**  `mapcat` is `(apply
  concat (map f …))`, and `concat`'s variadic arity realizes three mapped cells before the
  first element exists — a fourth once `cat` steps — so a `mapcat` spelling hints *four*
  chunks ahead of what has been consumed.  That is not merely eager: a store sizes its
  batch against its own cache, so four chunks in flight against a cache smaller than four
  of them evict each other and the walk pays the batch queries **and** every point read it
  meant to avoid.  The explicit `lazy-seq` step below hints exactly the chunk about to be
  read.

  `n` is floored at 1: `partition-all` with 0 is an infinite sequence of empty chunks, and
  0 is truthy, so a caller's `(or setting 1)` does not catch it.

  **The return type depends on `hint`**: `ids` itself when nil (a set stays a set), a lazy
  seq when not.  A caller that needs set operations — `contains?` above all — must hold the
  enumeration it was given rather than the hinted view, since `contains?` on a seq throws.
  Every caller here consumes the result sequentially and none of them keeps it."
  [hint n ids]
  (if hint
    (let [n (max 1 (long n))]
      ((fn step [s]
         (lazy-seq
          (when-let [s (seq s)]
            (let [chunk (take n s)]
              (hint chunk)
              (concat chunk (step (drop n s)))))))
       ids))
    ids))

(defn count-sentexes
  "How many live sentexes `store` holds.  `p/Tallying`'s answer when it has one, else the
  cardinality of the roster — the same number either way."
  ^long [store]
  (if (satisfies? p/Tallying store)
    (long (p/sentex-tally store))
    (long (count (p/sentex-ids store)))))

(defn count-justifications
  "How many live justifications `store` holds — `count-sentexes`'s twin."
  ^long [store]
  (if (satisfies? p/Tallying store)
    (long (p/justification-tally store))
    (long (count (p/justification-ids store)))))

(defn some-sentex-id
  "A live sentex handle from `store`, or nil when it holds none.  The engine's spelling of
  *is this store empty*, and of *give me one record to prove this build can read them*."
  [store]
  (if (satisfies? p/Tallying store)
    (p/a-sentex-id store)
    (first (p/sentex-ids store))))

(defn some-justification-id
  "A live justification handle from `store`, or nil — `some-sentex-id`'s twin."
  [store]
  (if (satisfies? p/Tallying store)
    (p/a-justification-id store)
    (first (p/justification-ids store))))

(defn some-premise-id
  "A handle `store` has marked a premise, or nil — `some-sentex-id`'s twin.  Asked
  together with `some-justification-id` to tell a store that can be recovered into belief
  from one that has to be loaded again (`vaelii.browser.catalog`)."
  [store]
  (if (satisfies? p/Tallying store)
    (p/a-premise-id store)
    (first (p/premise-ids store))))

(defn mark-premises
  "Mark every handle in `id->strength` a premise at its strength — the store's bulk write
  when it has one, else `mark-premise` per handle, which is the loop this replaces."
  [store id->strength]
  (if (satisfies? p/BulkAnnotating store)
    (p/mark-premise-batch store id->strength)
    (doseq [[id strength] id->strength] (p/mark-premise store id strength)))
  nil)

(defn put-all-provenance
  "Persist every `[id prov]` pair — the store's bulk write when it has one, else
  `put-provenance` per pair.  `mark-premises`'s twin."
  [store entries]
  (if (satisfies? p/BulkAnnotating store)
    (p/put-provenance-batch store entries)
    (doseq [[id prov] entries] (p/put-provenance store id prov)))
  nil)

(defn- loop-sink
  "The sink every store has: `put` per record, and the premise mark the caller would have
  made itself.  It is the whole of what a store without `p/BulkLoading` does, kept in one
  place so a loader writes through a sink unconditionally and never branches on the
  capability."
  [store put! premises?]
  (reify
    p/RecordSink
    (write-record! [_ rec]
      (let [h (put! store rec)]
        (when (and premises? (:strength rec))
          (p/mark-premise store h (:strength rec)))
        h))
    java.io.Closeable
    (close [_] nil)))

(defn sentex-sink
  "An open bulk write for sentexes — the store's own when it bulk-loads, else `put-sentex`
  per record.  `opts` is `{:premises? bool}`, default true: whether a record carrying a
  `:strength` is rostered a premise by the write.

  Close it (`with-open`) before reading any of what was written back."
  ([store] (sentex-sink store {}))
  ([store {:keys [premises?] :or {premises? true} :as opts}]
   (if (satisfies? p/BulkLoading store)
     (p/open-sentex-sink store (assoc opts :premises? premises?))
     (loop-sink store p/put-sentex premises?))))

(defn justification-sink
  "`sentex-sink`'s twin for justifications, which carry no strength and roster no premise."
  ([store] (justification-sink store {}))
  ([store opts]
   (if (satisfies? p/BulkLoading store)
     (p/open-justification-sink store opts)
     (loop-sink store p/put-justification false))))
