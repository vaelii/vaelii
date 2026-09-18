;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.mount
  "Mounting a fork: freeze a base, compose a private writable overlay over it, and hand
  back the two stores a KB is built from.

  A **base** is any pair of stores mounted read-only (`vaelii.impl.overlay.frozen`); a
  **fork** is a fresh writable pair composed over it.  Nothing is copied and nothing in
  the base is written, so any number of forks in **one JVM** share one base and each
  evolves its own — the sharing needs no protocol between them, and equally offers no
  coherence between them: a base that changes under a mounted fork is outside the
  contract.

  A durable base is one JVM's, not several.  Its directory takes the exclusive
  single-writer lock when it opens (`vaelii.impl.disk.lock`), and a fork's `:disk` base
  opens through the same per-directory registry — so a second process cannot mount it
  while the first holds it.  Read-only *composition* is what the frozen decorator
  guarantees; read-only *file access* is a separate thing the disk backend does not
  offer.

  ## Which index a fork can be taken over

  The overlay is a `KvBackend` decorator, so it forks exactly the index path that is
  written over that protocol: `KvIndexStore` (`vaelii.impl.kv`) and therefore the
  `:memory`, `:dense` and `:disk-log` index axes.  The `:columnar` index is a **native**
  `IndexStore` — its trie is int-id nodes in parallel arrays, with no keys and no backend
  underneath — so a `KvBackend` decorator would fork its roots and leave its trie behind.
  That is refused here rather than half-done.  Forking a columnar index is a different
  construction: its compacted CSR mode is already an immutable base, so the natural shape
  is a mutable columnar head over a frozen CSR base, not a KV decorator.

  ## Bookkeeping

  The record half keeps tombstones and released premise marks in a small `KvBackend`
  beside the overlay (`vaelii.impl.overlay.store`).  An in-RAM overlay gets an in-RAM one
  — the whole fork is ephemeral — and a disk overlay gets a durable one under
  `<dir>/overlay-meta`, so remounting that directory over the same base serves the merged
  view it was left in.  The index half needs none: its bookkeeping lives in the overlay
  index itself, under reserved keys, and so is exactly as durable as the fork is."
  (:require [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.overlay.store :as ostore]
            [vaelii.impl.protocols :as p]))

(defn kv-backend-of
  "The `KvBackend` an `IndexStore` is written over, or nil when it is not written over one
  at all.  A `KvIndexStore` holds it as `:backend`; a native index (the columnar one) has
  no such protocol and answers nil."
  [index-store]
  (let [b (:backend index-store)]
    (when (and b (satisfies? p/KvBackend b)) b)))

(defn- base-kv
  [base-index]
  (or (kv-backend-of base-index)
      ;; Lead with what the caller can act on. The mechanism (KvBackend, decorator,
      ;; roots, trie) is four internal names before the one usable clause, and a
      ;; reader who has never opened this namespace cannot use any of them.
      (throw (ex-info (str "cannot fork a :columnar index — the forkable index backends are "
                           ":memory, :dense and :disk-log.  (A columnar index is not written over "
                           "a KV backend, so forking it would fork its roots and leave its "
                           "trie behind.)")
                      {:type :unforkable-index :index (class base-index)}))))

(defn meta-kv
  "The bookkeeping `KvBackend` for a fork whose *record* overlay is `kind` (`:memory` or
  `:disk`) under `opts` — in RAM for an ephemeral fork, durable beside the records for a
  disk one, so the two are exactly as recoverable as each other."
  [kind opts]
  (case kind
    :memory (mem/memory-kv-backend {:space [::meta (:space opts 0)]})
    :disk   (disk/overlay-meta-for (disk/disk-dir opts))
    (throw (ex-info (str "no overlay bookkeeping for record backend " (pr-str kind)
                         " — a fork's own records are :memory or :disk")
                    {:type :unknown-backend :mismatch :illegal-position
                     :axis :records :kind kind :records kind}))))

(defn forked?
  "Is either half of this `{:records :index}` store pair already a **fork's own**?

  A stack of forks is not built (docs/overlay.md): the overlay is a two-store decorator,
  and stacking it would make every read walk one more layer per level while the id
  watermark, the tombstone sets and the copy-on-write counters would each have to merge
  across all of them.  `open-kb` refuses an `:overlay` half that is itself declared
  `:overlay`, which catches the opts spelling; this catches the other road in — a live
  fork's stores handed straight to `open-kb` as `:base-stores`, which is exactly what
  `core/fork` passes."
  [{:keys [records index]}]
  (boolean (or (ostore/overlay-record-store? records)
               (okv/overlay-kv? (kv-backend-of index)))))

(defn mount-records
  "An `OverlayRecordStore`: `overlay` (writable) over `base` (frozen), with `meta` holding
  the record-level bookkeeping."
  [overlay base meta]
  (ostore/overlay-record-store overlay (frozen/frozen-records base) meta))

(defonce ^:private fork-seq (atom 0))

(defn fresh-overlay-opts
  "Storage opts for an **ephemeral** fork: an in-RAM overlay on a space nothing else
  names, so two forks taken with no opts are independent rather than accidentally the same
  one.  Naming the space explicitly is how a caller asks for the other behaviour — a
  remount of a fork it took earlier."
  []
  (let [n (swap! fork-seq inc)]
    {:backend :memory :space [::fork n]}))

(defn mount-index
  "A `KvIndexStore` over an `OverlayKv`: `overlay`'s backend (writable) over `base`'s
  (frozen).  Both arguments are `IndexStore`s, and both must be `KvIndexStore`s — see the
  namespace docstring on why the columnar index is not forkable this way."
  [overlay base]
  (kv/->KvIndexStore (okv/overlay-kv (base-kv overlay) (frozen/frozen-kv (base-kv base)))))
