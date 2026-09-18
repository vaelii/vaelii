;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.kb
  "The KB record, as a held namespace (`vaelii.impl.types.prover` states what that means).
  A reload that redefined it would leave every open KB an instance of a class the reloaded
  code no longer constructs.  Opening, closing and every operation on a KB is
  `vaelii.impl.kb`.")

;; `reasoning` is a volatile holding one `Reasoning` value
;; (`vaelii.impl.types.reasoning`): the network, the taxonomy and every atom a recover or a
;; settle fills.  It is not a store — `records` and `index` are the two stores, and a
;; `Reasoning` value lives in this process alone.  The readers in that namespace
;; dereference it.  A background rebuild's install replaces the value with one `vreset!`,
;; and no other code resets it.
;;
;; `provers` and `solver` are atoms holding configuration the caller sets: the solver is
;; swappable (the ASP backend in vaelii.impl.asp.edge).
;;
;; `feed` is the change feed's listeners and the region a settle files for them
;; (`vaelii.impl.feed`).  A field rather than a bare key for the same reason as
;; `:naming`: every settle reads it to decide whether to accumulate anything, and a KB
;; nobody is listening to should pay a field read and not a hash lookup.
;; `dir` is the record store's directory when the records are durable, else nil. It is
;; here so `core/close!` can release the exclusive FileLock the disk backend takes:
;; without it a long-running process could not hand a directory to another process, or
;; reopen it elsewhere, until the JVM exited.
;; `snapshot-dir` is that same directory again, and non-nil only on a KB whose index is
;; the mapped image — the write entry point's whole gate on the image cadence
;; (`create-sentex`).  A separate field rather than a test on `dir`, because `dir` is set
;; for every durable-records KB and the cadence is for one of them: reading `dir` there
;; put the refresh call, its root-count argument and a `realpath` on the write path of
;; `:disk-memory`, `:disk-dense`, `:disk-columnar` and `:disk-log` alike, none of which
;; has an image.  Resolved once at `open-kb`, so nothing on the write path canonicalizes
;; a path this one already did.
;; `unrecovered` is the write side of "this KB's derived state was never built over a
;; store that already held records" — `{:no-belief bool :no-index bool :announced? bool}`,
;; each key absent until something asks.  Reads over that state answer nothing and can be
;; re-asked; a write lands content the store keeps, so the write entry points ask
;; `write-hazards` below.  An atom because `recover` and `reindex` clear what they build.
;; `oplog` is the operation log (`vaelii.impl.oplog`) this KB records its public writes
;; into, or nil.  A field, because every public write reads it to decide whether to record.
(defrecord KB [records index reasoning provers solver naming constraints feed dir
               snapshot-dir index-space unrecovered oplog])
