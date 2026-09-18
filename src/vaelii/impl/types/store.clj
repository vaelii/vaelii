;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.store
  "The storage records with no methods (`Kind`, `TokenLog`, `Oplog`), as a held namespace
  (`vaelii.impl.types.prover` states what that means), with the notes on their fields.

  A store with methods — a record store, an index store, a key-value backend — is defined,
  with its methods inline, in the namespace that implements it (`vaelii.impl.memory`,
  `vaelii.impl.kv`, `vaelii.impl.disk.kv`, …)."
  (:import [java.io RandomAccessFile]))

;; `compacting` boxes the copy-on-write compactor's state while a compaction is in
;; flight, else nil.  `store!`/`kill!` fold the ids they touch into `:touched`, and
;; `clear-records!` sets `:aborted` — both under the kind lock, so the compactor's
;; delta reconcile sees a consistent view.  See `compact-kind!`.  `failed` holds the
;; failure of a compaction that could not install its result past the commit point,
;; else nil; while set, every read and write refuses (`usable!`).
(defrecord Kind [log idx lock live-ids log-path idx-path compacting failed cache enc dec])

(defrecord TokenLog [log path fwd rev lock])                          ; vaelii.impl.disk.tokens

;; `raf` is the log file, written and forced under `lock` because a `RandomAccessFile`
;; shares one file pointer (`vaelii.impl.disk.files`, the shared-pointer invariant).
;; `state` is `fresh-state`'s map; `reg` the durability registration; `seal-fn` the
;; function `run-op` calls when a seal is due.
(defrecord Oplog [path ^RandomAccessFile raf lock state reg seal-fn])
