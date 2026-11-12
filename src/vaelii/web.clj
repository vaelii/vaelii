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
  default loopback).  A `:host` naming an address requires `:token` (default
  `VAELII_API_TOKEN`) as `start` does, and the handler checks it on every request.
  Pure `request -> response`, so it is tested without a socket."
  ([target] (web/handler target))
  ([target opts] (web/handler target opts)))

(defn start
  "Start a Jetty server for `target` and return it (non-blocking).  Opts: `:port`
  (default 3000), `:host` (default loopback) and `:token` (default `VAELII_API_TOKEN`),
  which a `:host` naming an address requires.  `:reload?` is refused: a served browser
  never reloads, and `scripts/start-vaelii-dev.sh` runs the one that does."
  [target opts]
  (web/start target opts))

(defn -main
  "Serve a starter-loaded KB on http://localhost:3000.

    lein run -m vaelii.web
    lein run -m vaelii.web --listen 0.0.0.0    ; reachable off-machine (opt-in)"
  [& args]
  (apply web/-main args))

;; ---- extensions ---------------------------------------------------------
;;
;; A library adds pages and panels to the browser by registering an extension; the
;; browser names no extension.  A handler receives `env`, the render env the browser
;; builds per request, which is opaque but for `:kb` (the KB it reads) and `:sandbox`
;; (this session's scratch context), and renders with the helpers below.  docs/web.md,
;; "Extensions".

(defn register-extension
  "File `ext` under `ext-name`, a lower-case keyword, replacing any extension of that
  name; answers the name.  Keys, all optional: `:routes` (under `/ext/<name>/`, methods
  `:get` `:post` `:write`, each `(fn [env req] …)`), `:menu` (`[[label href] …]`, hrefs
  under the same prefix), `:term-actions` and `:term-panel` (`(fn [env term] …)`, beside
  the heading and at the foot), `:on-start` (`(fn [])`), `:stylesheet` and `:script`
  (classpath resources).  `vaelii.browser.web/register-extension` has the contract."
  [ext-name ext]
  (web/register-extension ext-name ext))

(defn unregister-extension
  "Take the extension filed under `ext-name` out of the browser, from the next request."
  [ext-name]
  (web/unregister-extension ext-name))

(defn local-kb
  "The in-process KB behind the render env `env`, or nil when the browser reads a remote
  daemon."
  [env]
  (web/local-kb env))

(defn read-form
  "Read a request parameter as EDN, or nil when it does not read — never a throw, since
  the value is whatever the request carried."
  [s]
  (web/->form s))

(defn render-form
  "A sentence or term as the browser draws it: every atomic subterm a role-coloured
  link to its term page."
  [env form]
  (web/render-form env form))

(defn term-link
  "A role-coloured link to `term`'s page."
  [env term]
  (web/term-link env term))

(defn consequences
  "The panel of what `batch` (`{:add [[sentence context] …] :remove [handle …]}`) would
  do, previewed over the render env's KB under `heading`.  It asserts and rolls back, so call
  it from a `:write` route."
  [env heading batch]
  (web/consequences env heading batch))

(defn stored-sentexes
  "What a write stored — a row per sentex, then what followed from them — from
  `vaelii.core/edit-with-consequences!`'s answer."
  [env result]
  (web/stored-sentexes env result))
