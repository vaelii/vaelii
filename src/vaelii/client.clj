;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.client
  "A thin EDN-over-HTTP client for the vaelii daemon (`vaelii.serve`).  Runs no engine:
  it POSTs `{:op :args}` and reads the result back, over JDK `java.net.http` (no
  dependency — JDK 21 ships it).

  Every call threads an **explicit connection handle** as its first argument —
  `(query conn '(dog ?x) 'Ctx)` — the network mirror of `vaelii.core`'s explicit-`kb`
  API.  A `conn` from `client` holds a reusable `HttpClient`; no socket opens until a
  call.  A daemon reply of `{:ok false}` becomes an `ex-info` carrying the daemon's
  `:error` and `:type`, so a remote naming or disjointness refusal surfaces like a
  local one.

  A daemon with `VAELII_API_TOKEN` set answers 401 (`:unauthorized`) to a call that
  presents no bearer token; the `conn` reads the same variable, so a client in the
  daemon's environment carries it with nothing said.

  Public because a client is a thing applications write against; the implementation is
  `vaelii.impl.client`, which is free to change.  Result shapes are `vaelii.core`'s: a
  sentex comes back as a plain map (the daemon projects the record), a solution as a
  binding map."
  (:refer-clojure :exclude [assert isa?])
  (:require [vaelii.impl.client :as c]))

(defn client
  "A connection handle to a daemon at `host`:`port` (opts: `:timeout-ms`, default
  30000; `:token`, the bearer token every call presents — `VAELII_API_TOKEN` when the
  key is absent, and an explicit nil to send no `Authorization` header at all).  Holds
  a reusable `HttpClient`; no network happens until a call."
  ([host port] (c/client host port))
  ([host port opts] (c/client host port opts)))

(defn call
  "POST `{:op op :args args}` and return the `:result`, or throw `ex-info` on an
  `{:ok false}` reply.  The low-level entry the wrappers below use; reach for it for
  an op with no wrapper yet — `vaelii.serve/ops` is the reachable set."
  [conn op args]
  (c/call conn op args))

(defn health
  "The daemon's liveness reply, `{:ok true}` — a GET, so it needs no op."
  [conn]
  (c/health conn))

;; ---- the vaelii.core surface, conn-first ---------------------------------

(defn assert
  "Assert `sentence` in `context` (optional `opts`) — returns the handle(s).  Bare —
  no `!` — for `vaelii.core/assert`'s reason: additive, and `retract!` takes it back."
  ([conn sentence context] (c/assert! conn sentence context))
  ([conn sentence context opts] (c/assert! conn sentence context opts)))

(defn assert-rule
  "Assert a rule from `antecedents` to `consequent` in `context` — returns the
  handle(s); a conjunctive consequent yields one handle per conjunct."
  ([conn antecedents consequent context]
   (c/assert-rule! conn antecedents consequent context))
  ([conn antecedents consequent context opts]
   (c/assert-rule! conn antecedents consequent context opts)))

(defn assert-many
  "Assert every sentence in `sentences` into `context`, as one call."
  ([conn sentences context] (c/assert-many conn sentences context))
  ([conn sentences context opts] (c/assert-many conn sentences context opts)))

(defn retract!
  "Retract the sentex `handle` names, tearing down what it solely supported."
  [conn handle]
  (c/retract! conn handle))

(defn sentexes-matching
  "The believed sentexes matching `sentence` (a pattern may carry `?vars`), as maps."
  ([conn sentence] (c/sentexes-matching conn sentence))
  ([conn sentence context] (c/sentexes-matching conn sentence context)))

(defn query
  "Solutions for `goal` as binding maps — `({?x Muffet})`."
  ([conn goal] (c/query conn goal))
  ([conn goal context] (c/query conn goal context))
  ([conn goal context opts] (c/query conn goal context opts)))

(defn ask
  "The first solution for `goal`, or nil."
  ([conn goal] (c/ask conn goal))
  ([conn goal context] (c/ask conn goal context)))

(defn ask?
  "Whether `goal` has any solution."
  ([conn goal] (c/ask? conn goal))
  ([conn goal context] (c/ask? conn goal context)))

(defn prove
  "A proof tree for `goal`, as data."
  ([conn goal] (c/prove conn goal))
  ([conn goal context] (c/prove conn goal context)))

(defn provable?
  "Whether `goal` is provable."
  ([conn goal] (c/provable? conn goal))
  ([conn goal context] (c/provable? conn goal context)))

(defn in?
  "Whether the sentex `handle` names is currently believed."
  [conn handle]
  (c/in? conn handle))

(defn why
  "Why the sentex `handle` names is believed — its supporting justifications, as data."
  [conn handle]
  (c/why conn handle))

(defn why-not
  "Why a sentence is *not* believed, by handle or by sentence and context."
  ([conn handle] (c/why-not conn handle))
  ([conn sentence context] (c/why-not conn sentence context)))

(defn isa?
  "Whether individual `x` is of type `t`, through the `genl` closure."
  ([conn x t] (c/isa? conn x t))
  ([conn x t context] (c/isa? conn x t context)))

(defn types-of
  "The types individual `x` belongs to."
  ([conn x] (c/types-of conn x))
  ([conn x context] (c/types-of conn x context)))

(defn genls
  "The types `t` is a subtype of, transitively."
  [conn t]
  (c/genls conn t))

(defn specs
  "The types that are subtypes of `t`, transitively."
  [conn t]
  (c/specs conn t))

(defn contexts
  "Every context the KB holds."
  [conn]
  (c/contexts conn))

(defn sentex
  "The sentex `handle` names, as a map."
  [conn handle]
  (c/sentex conn handle))

(defn handle-of
  "The handle for `sentence` in `context`, or nil."
  [conn sentence context]
  (c/handle-of conn sentence context))

(defn find-sentexes
  "Every sentex containing `term`."
  [conn term]
  (c/find-sentexes conn term))

(defn conflicts
  "The KB's current conflicts."
  [conn]
  (c/conflicts conn))

(defn contradictions
  "The coexisting P/¬P dilemmas."
  [conn]
  (c/contradictions conn))

(defn violations
  "The recorded definitional violations."
  [conn]
  (c/violations conn))
