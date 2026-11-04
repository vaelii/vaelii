;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.access
  "How a *read* client reaches a KB — directly in-process, or over the daemon HTTP API
  (`vaelii.host.serve`).  It re-exports the slice of the `vaelii.core` read surface the
  browser uses, so the browser is written once against these names and runs unchanged
  against a local KB or a remote daemon.

  A **target** is either a KB, read in-process, or an access value from `remote`.  A
  KB-read op dispatches on it:

    :remote  → the client (`vaelii.host.client/call`) — one HTTP round-trip
    a KB     → `vaelii.core`, via `serve/ops` (the very allowlist the daemon serves, so
               local and remote answer through the same table and cannot drift)

  The pure display fns (`term-role`, `reified-term?`, `readable-sentence`,
  `indexable-terms`, `negative?`, `mint-rule-kind`, `rests-on`, `query-contexts`,
  `assertable-strengths`, `sort-by-content`, `levels`, `calculi`), the bootstrap fns
  (`open-kb`, `clear!`), the in-process `write-hazards` and the process-wide
  `switch-value` take no target and delegate to `vaelii.core`.  They are here so a caller
  can require this one namespace and reach the whole surface it needs.

  Reads — including `check` / `check-edit`, which answer what `assert` would refuse
  and write nothing — plus the four writes the browser performs: `edit` (an
  assert/retract batch in one settle), `edit-with-consequences` (the same batch, plus
  the belief it moved), `forward-chain`, and `preview` (which stores nothing but applies
  a batch and rolls it back, so it holds the single writer).  A remote result is already
  EDN-clean (the daemon projects sentex records to maps); a local result is the raw
  record, and both answer to the same keys, so a caller handles them identically."
  (:refer-clojure :exclude [isa?])
  (:require [vaelii.core :as core]
            [vaelii.host.client :as client]
            [vaelii.host.serve :as serve]))

(defn remote
  "A remote access to the daemon at `host`:`port` — builds a client connection the
  KB-read ops send over.

  The connection reads `VAELII_API_TOKEN` like any other (`client/client`), so a
  browser attached to an authenticating daemon carries the token by being started in
  the same environment.  There is nothing here to configure and no second place to say
  it: the target is a host and a port, and the credential is the process's."
  [host port] {:mode :remote :conn (client/client host port)})

(defn local-kb
  "The in-process KB behind `target`, or nil when the target is a remote daemon.

  Every op above works either way, so a caller that only reads never needs this.  It is
  for the one thing that cannot go over the wire: handing the KB itself to a component
  written against `vaelii.core` rather than against this facade — a browser extension
  that reads a term's neighbourhood, its vocabulary and its checks through dozens of
  calls, which a round-trip at a time is not a thing to offer a reader.  A nil answer
  lets the caller say so, rather than degrade silently."
  [target]
  (case (:mode target)
    :remote nil
    nil     target))                                      ; a KB is local

(defn- dispatch
  "Run KB-read op `op` with `args` against `target` (a remote access or a KB)."
  [op target args]
  (case (:mode target)
    :remote (client/call (:conn target) op (vec args))
    nil     ((serve/ops op) target (vec args))))          ; a KB is local

(defmacro ^:private defreads
  "Define a target-first wrapper per read op that dispatches through `dispatch`.  The op
  keyword is the fn name, so `(ask target …)` sends `:ask` — the same key
  `serve/ops` and the daemon use.

  Also defs `read-ops`, the vector of keywords declared here.  A name with no `serve/ops`
  entry is a wrapper that type-checks, publishes and then throws on the nil it looks
  up — so the two lists agreeing is a fact worth being able to state, and `access_test`
  states it."
  [& names]
  `(do ~@(for [n names]
           `(defn ~n [~'target & ~'args] (dispatch ~(keyword n) ~'target ~'args)))
       (def read-ops ~(mapv keyword names))))

(defreads
  sentexes-matching ask argue sentex handle-of find-sentexes
  in? believed? belief-status believed why-not
  why genls types contexts premise? defeat-class justification
  ;; one `genl` step each way, whatever installed the edge — a stated `genl` or a cover
  ;; declaration — which is what the taxonomy graph draws and the tree opens
  direct-genls direct-specs
  ;; every subtype of a type, which a whole-KB list reads to find the members of
  ;; `unary_predicate`
  specs
  ;; the one-step neighbours no other one-step neighbour stands between, which is what the
  ;; concept graph draws: one round trip an expansion, the reduction done by the engine
  min-genls max-specs
  ;; the same reduction over `genlCx`, for a context's page
  min-context-parents max-context-children
  ;; whether a `types` node is a relation, and a predicate's arity, for the term colouring
  relation? relation-arity
  supporting-justifications dependent-justifications
  ;; the verdict a context reads on each justification of a handle — what cannot be read
  ;; off belief, and so what a remote reader would otherwise have to render wrong
  justification-verdicts
  lookup escalate count-in-context
  sentexes-in-context sentexes-with-arg sentexes-with-functor count-with-arg
  ;; the sentex page's two annotation sections: the metas naming a handle, and the
  ;; provenance map recorded beside it
  sentexes-naming provenance
  count-with-functor disjoint-metatypes metatype-members separating-covers conflicts
  ;; a type's members off the index, and whether one is believed: the whole-KB list of
  ;; types without a genl reads every member of `unary_predicate`'s subtypes this way
  stored-first-args isa?
  ;; whether two types are disjoint, which a rename into an existing term is checked for
  disjoint?
  ;; the cover declarations over a whole, which the concept graph groups a type's
  ;; subtypes by
  covers-of
  contradictions
  ;; what a reified term denotes, so a reified NAT is displayed as the expression it was
  ;; minted from rather than as its opaque constant (docs/nat.md).  The pure
  ;; `reified-term?` below decides whether it is sent, so a KB with no reified terms
  ;; never sends it
  term-expression
  violations chain-stats terms term-count sentex-count find-terms
  ;; the filed ledger alone, which `/stats` counts and lists on a page load; `violations`
  ;; also fetches every held sentex and convicted firing, so it is read in a job
  filed-violations
  ;; the per-rule funnel behind chain-stats — placed / refused / silent, for the page that
  ;; answers "which of my rules actually do anything"
  chain-report
  ;; how a goal would be answered — which provers bear on it and what each would cost,
  ;; or for a conjunction the join order and the counts that decided it
  query-plan
  ;; the run that plan predicts: the search tree as data, and the same goal under several
  ;; tacticians side by side — the reads behind the inference debugger.  Both bound their
  ;; own work, so a remote reader cannot turn one call into an unbounded search
  search-tree compare-tacticians
  ;; the *standing* disjointness question, as against the arising one `settle` files
  ;; into `violations`.  Computed on demand, so a caller asks for it rather than
  ;; receiving it, and a remote one pays a round trip for the pass
  exposed-clashes
  ;; the seven readings about the knowledge rather than about a run, which `/quality`
  ;; renders.  `:on-progress` is a fn and does not cross the wire, so a remote reading
  ;; reports no phase and cannot be cancelled
  kb-quality
  ;; qualitative constraint reasoning: the network a context's facts constrain, and one
  ;; arrangement out of it
  qualitative-network qualitative-scenario
  ;; the dry run of the write path: `check` writes nothing, so it is a read like any
  ;; other and the editor validates a line before it is saved
  check check-edit
  ;; what the process is holding beside the store — the caches, their bounds and the
  ;; hit rate.  O(1) per row by construction, so the page that renders it can poll
  caches
  ;; everything the KB holds about one term, assembled once.  The term page's three type
  ;; lines are this and not a second computation, which is what keeps the page and the API
  ;; agreeing about what a term is — and against a remote daemon it is one round trip for
  ;; an answer a dozen reads would otherwise have to fetch a piece at a time
  describe)

;; ---- the writes ---------------------------------------------------------

(defn edit!
  "Apply an edit batch to the target, local or over the daemon.  `batch` is
  `{:add [[sentence context opts?]…] :remove [handles…]}`; adds land before removes and
  the whole thing settles once (`vaelii.core/edit!`).  Both of the browser's mutations —
  saving edited sentexes, asserting new ones, retracting a selection — are this one
  call, so every write it makes is one settle."
  [target batch] (dispatch :edit target [batch]))

(defn edit-with-consequences!
  "`edit`, and what the batch turned out to mean — the belief it added and took away
  (`vaelii.core/edit-with-consequences!`, docs/preview.md).  The browser's commit paths
  use this rather than `edit` so a page can say what followed from a save; the extra
  answer is sentences and handles, EDN-clean, so it crosses the wire like any read."
  ([target batch] (dispatch :edit-with-consequences target [batch]))
  ([target batch opts] (dispatch :edit-with-consequences target [batch opts])))

(defn forward-chain
  "Run the forward-chaining fixpoint over the target's KB — `{:derived n :truncated?
  bool}`.  A write (it derives and places conclusions), and the browser's one way to
  ask what a load's rules would conclude without asserting anything new."
  [target & args] (dispatch :forward-chain target (vec args)))

(defn preview
  "What `edit`ing `batch` would make the target believe and stop believing, without
  leaving it done (`vaelii.core/preview`, docs/preview.md).

  Filed with the writes although it stores nothing: it applies the batch and rolls it
  back, so it holds the single writer for its duration and is not a thing to run beside
  one.  The answer is EDN-clean either way — sentences and handles, no records — so it
  crosses the wire like any read."
  ([target batch] (dispatch :preview target [batch]))
  ([target batch opts] (dispatch :preview target [batch opts])))

(defn clear-caches
  "Drop the target's derived caches and say what went (`vaelii.core/clear-caches`).

  Filed here rather than with the reads because it mutates, and *not* with the writes
  above because what it mutates is not knowledge: no belief moves, every entry it drops
  the next read recomputes, and it holds no writer. So it is the one control on this
  facade that is safe to use while a load runs — which is when a reader most wants it,
  since a hit rate means nothing until you can watch a miss."
  [target] (dispatch :clear-caches target []))

;; ---- pure display + bootstrap: no target, straight delegation ------------

(def term-role         core/term-role)
(def reified-term?     core/reified-term?)
(def readable-sentence core/readable-sentence)
(def indexable-terms   core/indexable-terms)
(def levels            core/levels)
(def calculi           core/calculi)
(def negative?         core/negative?)
(def mint-rule-kind    core/mint-rule-kind)
(def rests-on          core/rests-on)
(def query-contexts    core/query-contexts)
(def assertable-strengths core/assertable-strengths)
(def sort-by-content   core/sort-by-content)
(def open-kb           core/open-kb)
(def clear!            core/clear!)
;; asked only of an in-process KB: a daemon refuses an unrecovered write itself, and its
;; hazards are its own process's state
(def write-hazards     core/write-hazards)
;; a switch is this process's configuration, not a KB read, so it delegates straight
(def switch-value      core/switch-value)
;; the cache profile is process-wide, not a KB read, so it delegates straight rather than
;; dispatching to a target: the scale it moves is this process's, the way `set-log-level`
;; changes the process a daemon runs in rather than the KB it serves.  Only the two the
;; browser uses are re-exported — the read and the scale control; a per-cache override is
;; `vaelii.core/set-cache-limit` for an API or REPL caller
(def cache-profile     core/cache-profile)
(def set-cache-scale   core/set-cache-scale)
;; the log dial is process-wide too, and delegates straight for the same reason
(def log-level         core/log-level)
(def set-log-level     core/set-log-level)
