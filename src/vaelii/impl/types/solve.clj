;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.solve
  "The `Solver` protocol and the `Program` record a solve is handed, as a held namespace
  (`vaelii.impl.types.prover` states what that means).  The local solver behind the
  protocol, and `program`, which builds a `Program` from a KB, are `vaelii.impl.solve`.")

(defprotocol Solver
  (solve [solver program]
    "Assign truth to `program`'s contested assumptions.  Return
       {:defeat   #{handle ...}   ; assumptions to disbelieve
        :violated [nogood ...]}   ; contradictions left unsatisfiable (the result)"))

(defrecord Program
           [assumptions        ; #{handle} — contested defeasible nodes (never known-true)
            fixed              ; #{handle} — known-true background referenced by a contradiction
            contradictions     ; [{:nogood #{handle} :priority int :sentence any}]
            content            ; {handle {:sentence s :context c}} — what each assumption SAYS
            cardinalities])
