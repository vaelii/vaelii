;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.koinii.types
  "Koinii's two protocols, as a held namespace: the development browser's reloader never
  re-evaluates it (docs/web.md, *Hot reload*), because a re-evaluated `defprotocol` defines
  a new interface and a running channel's medium and cursor store would stop answering it.
  It requires no vaelii namespace.  The records that implement them are defined with their
  methods inline: the media in `vaelii.koinii.channel`, the cursor store in
  `vaelii.koinii.catchup`.")

(defprotocol Medium
  "The transport a channel runs over — a daemon connection (`wire`, cross-process) or an
  in-process KB (`local`, single-process).  Everything above this protocol is written
  once and runs over either; the two implementations differ only where the engine does —
  in how a subscription is delivered."
  (-assert [medium sentence context opts]
    "Assert `sentence` in `context` with `opts` (carrying `:creator`), returning the
    handle.  The daemon stamps `:creator` from the opts — the cooperative identity
    annotation crossing the wire (`identity`), since `*creator*` is a var in the daemon's
    process, not the client's.")
  (-sentex [medium handle] "The stored sentex `handle` names, as a map (`:sentence` …).")
  (-matching [medium sentence context]
    "The believed sentexes matching `sentence` in `context` (a `?ctx` matches anywhere).")
  (-check-edit [medium batch]
    "`check-edit` over an `{:add […] :remove […]}` batch — the dry run, storing nothing.
    A vector of problems, empty when admissible.")
  (-edit [medium batch] "Apply an `{:add […] :remove […]}` batch in one settle.")
  (-subscribe [medium goal context callback opts]
    "Register `callback` for events matching `goal` in `context` (nil `goal` = every
    change).  Returns `{:token … :stop (fn []) …}`.  Where the two media genuinely
    diverge — a wire poll loop off the agent's thread, vs an in-process listener.")
  (-query [medium goal context]
    "Solutions for `goal` in `context` as binding maps — the ANCESTOR-SET-AWARE read (walks the
    genlCx ancestor set, unlike `-matching`, so a channel read sees its agents' own-context
    sentexes).  The snapshot half of catch-up (`catchup`) reads through this.")
  (-feed-open [medium goal context]
    "Open a raw change-feed subscription with a cursor — `{:token :cursor :max-events}`.
    The wire feed's cursor primitive that catch-up (`catchup`) resumes from; `-subscribe`
    wraps it for the happy path, this exposes it for the durable-cursor / lag case.  A
    local (in-process) medium THROWS: `core/watch` is callback-based with no ring or
    cursor, so there is nothing to fall off and nothing to resume.")
  (-feed-poll [medium token cursor opts]
    "Read a raw subscription forward — `{:events :cursor :lagged}`.  `:lagged` non-zero is
    the whole point of catch-up: the cursor fell off the ring.  Local THROWS, as above."))

(defprotocol CursorStore
  "Where an agent keeps 'the last feed position I processed' — `{:token :cursor}` — so a
  restart RESUMES the stream rather than re-reading everything.  Deliberately CLIENT-SIDE
  (D7): a cursor in a KB context would be self-describing but would write to the shared
  truth on every poll, turning a read loop into a write loop through the single writer.  A
  deployment backs this with a file, the agent's own store, or a row — anything durable and
  local; the atom store below is the in-memory default."
  (read-position [store] "The stored `{:token :cursor}`, or nil if none.")
  (write-position! [store position] "Persist `{:token :cursor}`; returns it."))

