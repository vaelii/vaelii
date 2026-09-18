;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.snapshot
  "The snapshot sink and source protocols, as a held namespace (`vaelii.impl.types.prover`
  states what that means).  The three media the engine ships, and writing and reading an
  index image through them, are `vaelii.impl.io.snapshot`.")

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
