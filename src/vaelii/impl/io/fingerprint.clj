;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.fingerprint
  "What makes a dumped index and a dumped set of records provably the same KB.

  The index is derived from the records, so an index dump is only valid *against the
  records it was derived from*.  Nothing downstream can notice when it is not: a stale
  trie node simply reports fewer handles and a query returns fewer results — no
  exception, no warning, just a KB that quietly knows less.  So the writer records a
  fingerprint over the records and the reader recomputes it while storing them; a
  mismatch discards the index and rebuilds.

  **A sum, not a chain.**  The digest is the sum (mod 2⁶⁴) of a per-record hash, so it is
  commutative — the reader accumulates it in whatever order the frames arrive, which is
  not the order the writer walked — and *additive* rather than xor, so two identical
  records cannot cancel each other out.

  **What is hashed is what the index is a function of**: the handle, the sentence
  (`sentex/sentence-of`, which is a rule's `implies` form), `:context`, the sign
  (`sentex/polarity`), and a rule's `:antecedent` / `:consequent`.  `sentex/path`,
  `kv/root-keys`, `kv/sentex-terms` and the rule index read exactly those, and the handle
  because a posting *is* a set of handles — the same content at a different handle makes
  every posting naming it wrong.  Deliberately **not** hashed: `:strength`, `:varmap`,
  `:direction`, `:defeasible`.  None of them changes a single index entry, so a dump
  differing in one of them still has a valid index, and hashing them would make the cache
  go unused for a reason that is not a reason.  (`:strength` also arrives after the
  storing pass — a premise mark is applied once every record is down — so hashing it
  would cost the second pass over the records this exists to avoid.)

  The hash is FNV-1a over the fields' own `hash` values: cheap, deterministic across
  runs, and strong enough for the question being asked, which is whether two sets of
  records are *the same* — not whether an adversary can forge one.  A dump is not a
  trust boundary; if it were, this would be a real digest and signed.

  **Two granularities, one rule.**  `accumulator` (over `record-hash`) folds in what a
  record *says*, and needs the record — the export rides it on the sentex walk it is
  already making, and the import rides it on the frames it is already decoding.
  `slot-accumulator` (over `slot-hash`) folds in where each record *is*:
  `(id, offset, length)` off the idx, no frame decoded and no record fetched.  The mapped index snapshot (`vaelii.impl.disk.index-snapshot`) is
  checked with that one, because an image exists to make an open cost bytes read rather
  than records read, and a content digest would put every record back on the open path.
  It is the coarser hash in one direction and the finer one in the other: it cannot see
  a record rewritten to the same bytes at the same offset (nothing can produce that),
  and it *does* see a rewrite the index does not care about — a premise mark, or a
  compaction moving every frame — so a snapshot is discarded and rebuilt after one.
  Both directions are safe, because a discard is always legal for derived state."
  (:require [vaelii.impl.sentex :as sx]))

(def ^:private ^:const fnv-offset 1469598103934665603)
(def ^:private ^:const fnv-prime  1099511628211)

(defn- mix ^long [^long acc ^long x]
  (unchecked-multiply (bit-xor acc x) fnv-prime))

(defn record-hash
  "A 64-bit hash of the sentex `sx` stored at handle `h` — its identity for the purpose
  of deciding whether an index still describes it.  See the namespace docstring for what
  is in it and what deliberately is not."
  ^long [^long h sx]
  (-> fnv-offset
      (mix h)
      (mix (hash (sx/sentence-of sx)))
      (mix (hash (:context sx)))
      (mix (hash (sx/polarity sx)))
      (mix (hash (:antecedent sx)))
      (mix (hash (:consequent sx)))))

(defn slot-hash
  "A 64-bit hash of one idx slot — the handle and where its frame lies.  A record
  rewritten in place gets a new frame at a new offset, so this moves whenever the record
  at a handle does, without the frame being read."
  ^long [^long h ^long offset ^long length]
  (-> fnv-offset (mix h) (mix offset) (mix length)))

(defn justification-hash
  "A 64-bit hash of the justification `j` stored at handle `h` — what belief reads of it:
  the informant, the antecedents in their stored order, the consequence and the
  strength.  The bindings are not hashed: belief never reads them
  (`jtms/graph-just`).  A dump's reasoning image is stamped with an accumulator of these, so
  an import that lands different justifications declines the image."
  ^long [^long h j]
  (-> fnv-offset
      (mix h)
      (mix (hash (:informant j)))
      (mix (hash (vec (:antecedents j))))
      (mix (hash (:consequence j)))
      (mix (hash (:strength j)))))

(defn accumulator
  "A mutable fingerprint accumulator: `(acc h record)` folds one record in, `(acc)` reads
  `{:count n :max-handle h :digest d}`.  Mutable because it is folded inside the storing
  loop — the one pass over the records a reader gets — and single-writer like everything
  else here.  `hash-fn` is `record-hash` unless given (`justification-hash` for the
  justifications)."
  ([] (accumulator record-hash))
  ([hash-fn]
   (let [n      (volatile! 0)
         hi     (volatile! 0)
         digest (volatile! 0)]
     (fn
       ([] {:count @n :max-handle @hi :digest @digest})
       ([h rec]
        (let [h (long h)]
          (vswap! n inc)
          (when (> h (long @hi)) (vreset! hi h))
          (vswap! digest (fn [^long d] (unchecked-add d (long (hash-fn h rec))))))
        nil)))))

(defn slot-accumulator
  "The same accumulator over slots rather than records: `(acc h offset length)` folds one
  in, `(acc)` reads the same `{:count :max-handle :digest}` shape.  Commutative and
  additive for the same reasons."
  []
  (let [n      (volatile! 0)
        hi     (volatile! 0)
        digest (volatile! 0)]
    (fn
      ([] {:count @n :max-handle @hi :digest @digest})
      ([h offset length]
       (let [h (long h)]
         (vswap! n inc)
         (when (> h (long @hi)) (vreset! hi h))
         (vswap! digest (fn [^long d] (unchecked-add d (slot-hash h offset length)))))
       nil))))

