;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cli
  "Drive a KB from the shell: assert, match, query, and an interactive REPL.

  Public because it is a documented entry point — `lein cli`, or
  `lein run -m vaelii.cli`.  The implementation is `vaelii.impl.cli`, which is free to
  change."
  (:require [vaelii.impl.cli :as cli]))

(defn open-kb-from
  "The KB a set of parsed CLI options names — `--dir` for the durable `:disk` backend
  (recovered on open), `--starter` for a starter-loaded in-memory one, else empty."
  [opts]
  (cli/open-kb-from opts))

(defn dispatch
  "Run one command against `kb` and return its result (a handle, a seq of sentences or
  solutions, a proof tree, …) — the same verbs `-main` takes, for a caller that has its
  own argument handling.  `args` are data; `opts` is the parsed option map."
  [kb cmd args opts]
  (cli/dispatch kb cmd args opts))

(defn -main
  "Run one command and print its result.

    lein cli assert '(dog Muffet)' NaturalWorldContext --dir /var/lib/vaelii
    lein cli match  '(dog ?x)'   NaturalWorldContext --dir /var/lib/vaelii
    lein cli repl --starter"
  [& args]
  (apply cli/-main args))
