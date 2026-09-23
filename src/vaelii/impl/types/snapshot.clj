;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.snapshot
  "The snapshot sink and source protocols, and the one an index structure participates in a
  snapshot through, as a held namespace (`vaelii.impl.types.prover` states what that means).
  The three media the engine ships, and writing and reading an index image through them, are
  `vaelii.impl.io.snapshot`.")

(defprotocol SnapshotSink
  "Where a snapshot's bytes go — a directory, a database, memory.  Two ops: stream a
  named section, and commit the manifest that vouches for the lot."
  (write-section! [sink name frames]
    "Write the lazy seq `frames` to the section named `name`, one chunk in memory at a
    time.  Returns the number of frames written.")
  (commit! [sink manifest]
    "Write `manifest` as the completion marker — **last**, after every section, so an
    image with no committed manifest is never offered."))

(defprotocol SnapshotSource
  "Where a snapshot's bytes come from.  Two ops mirroring the sink: read the manifest, and
  stream a named section back."
  (read-manifest [source]
    "The committed manifest map, or nil when the image is absent or was never committed.")
  (read-section [source name]
    "A constant-memory lazy seq of the frames in the section named `name`."))

(defprotocol SnapshotSections
  "How an index structure takes part in a mapped index image.  Two structures implement it
  — the columnar trie (`vaelii.impl.types.trie`) and the routed root columns
  (`vaelii.impl.types.dense-roots`) — and `vaelii.impl.disk.index-snapshot` asks each of
  them the same three questions.

  Each implementer holds its columns in `^:unsynchronized-mutable` fields, which only an
  inline method can assign, so the three questions are a protocol rather than functions
  over the structure.

  The section maps are the implementer's own: what a structure writes is what it reads
  back, and this namespace fixes neither the key set nor the array shapes."
  (snapshot-mapped? [x]
    "Is this structure reading its columns out of an mmap'd image rather than out of heap
    arrays?  True exactly while nothing has been written since an image was installed,
    since a write thaws.")
  (snapshot-read [x opts]
    "The sections to write, as a map of heap arrays, or nil when the structure holds none.
    `opts` carries what an implementer needs to build them — the roots take `:remap`, an
    `int[]` from the in-RAM dictionary's term ids to the durable ones; the trie reads
    nothing out of it.")
  (snapshot-install! [x sections]
    "Install sections read back from an image, replacing whatever the structure held.  A
    column arrives either as a heap array or as a buffer over the mapping, and which it is
    *is* the residency decision."))
