;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web
  "The web browser over a KB: the upper ontology, any term, any sentex and its
  justifications, all cross-linked.

  Public because it is a documented entry point — `lein browser`, or
  `lein run -m vaelii.web`.  The implementation is `vaelii.browser.web`, which is free to
  change; the dev-only affordances (`dev-repl`, `dev-stop`) stay there.

  It binds loopback and authenticates nobody; read `.github/SECURITY.md` before
  `--listen` names an address."
  (:require [vaelii.browser.web :as web]))

(defn handler
  "The ring handler for `target` — a KB, an access value, or a catalog holder —
  behind the `Host` allowlist for the network interface it will be served on (`:host`,
  default loopback).  Pure `request -> response`, so it is tested without a socket."
  ([target] (web/handler target))
  ([target opts] (web/handler target opts)))

(defn start
  "Start a Jetty server for `target` and return it (non-blocking).  Opts: `:port`
  (default 3000) and `:host` (default loopback).  `:reload?` is refused: a served browser
  never reloads, and `scripts/start-vaelii-dev.sh` runs the one that does."
  [target opts]
  (web/start target opts))

(defn -main
  "Serve a starter-loaded KB on http://localhost:3000.

    lein run -m vaelii.web
    lein run -m vaelii.web --listen 0.0.0.0    ; reachable off-machine (opt-in)"
  [& args]
  (apply web/-main args))
