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
  binding map.

  **Every op the daemon serves has a wrapper here**, spelled as `vaelii.core` spells the
  fn — bare or `!`-marked exactly as it does — and at its arities, with `kb` replaced by
  `conn`.  The ones below are written out; the rest are generated from the daemon's op
  table by `lein regen-client`, which is also what makes the claim checkable rather than
  aspirational (`client_surface_test`).  `call` still reaches any op directly, which is
  what a caller wants for `serve/feed-ops` and for an op newer than this build."
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
  an op with no wrapper yet — `vaelii.serve/op-names` is the reachable set.  `opts` is
  `{:timeout-ms n}` for this call alone, which the long `poll` below is what needs."
  ([conn op args] (c/call conn op args))
  ([conn op args opts] (c/call conn op args opts)))

(defn health
  "The daemon's liveness reply, `{:ok true}` — a GET, so it needs no op."
  [conn]
  (c/health conn))

;; ---- the vaelii.core surface, conn-first ---------------------------------

(defn assert
  "Assert `sentence` in `context` (optional `opts`) — returns the handle(s).  Bare —
  no `!` — for `vaelii.core/assert`'s reason: additive, and `retract!` takes it back.
  With no context it is `CxUniverse`, as in process."
  ([conn sentence] (c/assert conn sentence))
  ([conn sentence context] (c/assert conn sentence context))
  ([conn sentence context opts] (c/assert conn sentence context opts)))

(defn assert-rule
  "Assert a rule from `antecedents` to `consequent` in `context` — returns the
  handle(s); a conjunctive consequent yields one handle per conjunct.  With no context
  it is `CxUniverse`, as in process."
  ([conn antecedents consequent]
   (c/assert-rule conn antecedents consequent))
  ([conn antecedents consequent context]
   (c/assert-rule conn antecedents consequent context))
  ([conn antecedents consequent context opts]
   (c/assert-rule conn antecedents consequent context opts)))

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
  "The first solution for `goal`, or nil.  `opts` is the wall clock `vaelii.core/ask`
  takes — `{:max-ms n}`, held under the daemon's ceiling, and given the ceiling's when
  absent."
  ([conn goal] (c/ask conn goal))
  ([conn goal context] (c/ask conn goal context))
  ([conn goal context opts] (c/ask conn goal context opts)))

(defn ask?
  "Whether `goal` has any solution.  Same `opts` as `ask`."
  ([conn goal] (c/ask? conn goal))
  ([conn goal context] (c/ask? conn goal context))
  ([conn goal context opts] (c/ask? conn goal context opts)))

(defn prove
  "A proof tree for `goal`, as data.  `opts` is `vaelii.core/prove`'s bound —
  `{:max-ms n :max-depth n}`, both held under the daemon's ceilings."
  ([conn goal] (c/prove conn goal))
  ([conn goal context] (c/prove conn goal context))
  ([conn goal context opts] (c/prove conn goal context opts)))

(defn provable?
  "Whether `goal` is provable.  Same `opts` as `prove`."
  ([conn goal] (c/provable? conn goal))
  ([conn goal context] (c/provable? conn goal context))
  ([conn goal context opts] (c/provable? conn goal context opts)))

(defn in?
  "Whether the sentex `handle` names is raw JTMS IN."
  [conn handle]
  (c/in? conn handle))

(defn believed?
  "Whether `handle` is JTMS IN after exceptions visible from `context`, before
  assertion-context inheritance."
  [conn handle context]
  (c/believed? conn handle context))

(defn belief-status
  "Storage, raw IN, exception forest, inheritance path, belief, and visibility for
  `handle` as viewed from `context`."
  [conn handle context]
  (c/belief-status conn handle context))

(defn blocked-justifications
  "The ids of the justifications a rule exception currently blocks — every antecedent IN
  and supporting nothing.  The one justification property belief does not report."
  [conn]
  (c/blocked-justifications conn))

(defn why
  "Why the sentex `handle` names is believed — its supporting justifications, as data.
  `opts` is `core/why`'s `{:max-depth n}`, which is how a `{:truncated? true}` branch is
  re-asked whole."
  ([conn handle] (c/why conn handle))
  ([conn handle opts] (c/why conn handle opts)))

(defn why-not
  "Why a sentence is *not* believed, by handle or by sentence and context; `opts` takes
  `{:nearest n}` to name the rule that came closest and what it is missing."
  ([conn handle] (c/why-not conn handle))
  ([conn sentence context] (c/why-not conn sentence context))
  ([conn sentence context opts] (c/why-not conn sentence context opts)))

(defn isa?
  "Whether individual `x` is of type `t`, through the `genl` closure."
  ([conn x t] (c/isa? conn x t))
  ([conn x t context] (c/isa? conn x t context)))

(defn types-of
  "The types individual `x` belongs to."
  ([conn x] (c/types-of conn x))
  ([conn x context] (c/types-of conn x context)))

(defn genls
  "The types `t` is a subtype of, transitively.  With a `context`, only the `genl` edges
  visible from it count."
  ([conn t] (c/genls conn t))
  ([conn t context] (c/genls conn t context)))

(defn specs
  "The types that are subtypes of `t`, transitively.  Scoped by `context` like `genls`."
  ([conn t] (c/specs conn t))
  ([conn t context] (c/specs conn t context)))

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

;; ---- the change feed -----------------------------------------------------

(defn watch
  "Open a change-feed subscription and return `{:token t :cursor 0 :max-events n}`.

  In process `vaelii.core/watch` takes a callback; a callback does not cross an EDN
  wire, so what a remote caller holds is a subscription the daemon keeps and this client
  reads forward with a cursor.  With no goal it is every belief change; with one it is
  the same standing query, and a goal that cannot be answered from a moved region is
  refused with the same `:not-watchable` it is refused with in process.

      (let [{:keys [token cursor]} (watch conn)]
        (loop [c cursor]
          (let [{:keys [events cursor lagged]} (poll conn token c {:wait-ms 20000})]
            (when (pos? lagged) (resync!))
            (run! render! events)
            (recur cursor))))"
  ([conn] (c/watch conn))
  ([conn goal context] (c/watch conn goal context)))

(defn poll
  "Read a subscription forward from `cursor` — `{:events [...] :cursor n :lagged k}`.
  Each event is `{:believed-added [...] :believed-removed [...]}` in `preview`'s entry
  shapes, one per settle, oldest first.

  `opts` is `{:wait-ms n}`: the daemon holds the request open that long waiting for the
  first event, and this client extends its read timeout to cover it.

  **`:lagged` is on every reply and is the one field a caller must read.**  Non-zero, the
  daemon's ring dropped that many events before this poll reached them, and the caller is
  behind rather than current — re-read what it cares about rather than trusting the
  events it did get to be the whole story."
  ([conn token cursor] (c/poll conn token cursor))
  ([conn token cursor opts] (c/poll conn token cursor opts)))

(defn unwatch
  "Drop subscription `token`; true if there was one.  Idempotent."
  [conn token]
  (c/unwatch conn token))

(defn watchers
  "What the daemon is holding open: one entry per subscription with its goal, how many
  events it has been `:delivered`, and how many are still `:pending` on its ring.  Neither
  is the reader's own position — that lives here, not there."
  [conn]
  (c/watchers conn))

;; ---- the rest of the daemon's surface ------------------------------------
;; One delegation apiece, and nothing between the markers is hand-written: the wrappers
;; above are the ones worth prose, and these are the ops that are the same shape as the
;; `vaelii.core` fn they name.  `lein regen-client` rewrites the section from
;; `vaelii.impl.serve/ops`.

;; ---- generated: one wrapper per daemon op, from serve/ops ---------------

(defn abduce
  "What would have to be true for `goal` to be provable in `context`."
  ([conn goal] (c/abduce conn goal))
  ([conn goal context] (c/abduce conn goal context))
  ([conn goal context opts] (c/abduce conn goal context opts)))

(defn abduce-discard!
  "Discard an abduction's scratch context — every hypothesis in it, and everything they
  licensed."
  [conn result]
  (c/abduce-discard! conn result))

(defn add-provenance
  "Merge `m` into `handle`'s provenance map (creating it if absent), returning the merged
  map."
  [conn handle m]
  (c/add-provenance conn handle m))

(defn all-specified-violations
  "Audit every binary `predAllSpecified` and `predSpecifiedAll` declaration visible in
  `context`, and return `{[functor pred indep] result…}` — each result carrying a
  `:status`, either `{:status :audited :violations #{…}}` or a `{:status :gap …}`
  diagnostic (`:missing-slot-typing`, or `:legacy-ternary-declaration` for a stored
  pre-migration ternary sentex the bulk import path can carry past the assert-time
  refusal)."
  [conn context]
  (c/all-specified-violations conn context))

(defn argue
  "Four-valued epistemic status of a ground assertion."
  ([conn asent context] (c/argue conn asent context))
  ([conn asent context opts] (c/argue conn asent context opts)))

(defn ask-within
  "Anytime `ask`: answer `goal` in `context`, but bounded by `budget` — a map of any of
  `{:max-ms n :max-results n :max-cost <tier>}`."
  ([conn goal budget] (c/ask-within conn goal budget))
  ([conn goal context budget] (c/ask-within conn goal context budget)))

(defn believed
  "The subset of `handles` raw structural JTMS IN, as a set — `in?` asked of many handles
  at once."
  [conn handles]
  (c/believed conn handles))

(defn caches
  "What this process is holding beside the stores — every derived structure the engine
  caches, ranked by entries."
  [conn]
  (c/caches conn))

(defn calculi
  "The shipped qualitative calculi as data — one map apiece, naming the calculus, the base
  relations it distinguishes (jointly exhaustive and pairwise disjoint, so exactly one
  holds of any two terms), the identity it puts on the diagonal, and the predicates it
  claims."
  [conn]
  (c/calculi conn))

(defn canonical-sentex
  "The canonical sentex for `sentence` in `context`, **without storing it** — the un-stored
  counterpart of `sentex`."
  [conn sentence context]
  (c/canonical-sentex conn sentence context))

(defn chain-report
  "Per forward rule, what forward chaining did with it — how many firings it **placed**,
  how many it **refused** and why, or whether it did nothing at all."
  [conn]
  (c/chain-report conn))

(defn chain-stats
  "Chaining-run instrumentation: `{:runs n :last {:derived n :truncated? bool}}`."
  [conn]
  (c/chain-stats conn))

(defn check
  "Would `(assert kb sentence context opts)` succeed, and if not, why? Returns a **vector
  of problems** — empty when the sentence is admissible — and **stores nothing**: no
  sentex, no index entry, no taxonomy edge, no chaining, no settle."
  ([conn sentence] (c/check conn sentence))
  ([conn sentence context] (c/check conn sentence context))
  ([conn sentence context opts] (c/check conn sentence context opts)))

(defn check-edit
  "`check` over a whole `edit` batch — `{:add [[sentence context opts?] …] :remove [handle
  …]}`, the shape `edit` takes — storing nothing."
  [conn batch]
  (c/check-edit conn batch))

(defn clear-caches
  "Drop every cache that offers a clear, and say what went: `{:cleared [{:cache :label
  :entries}…] :entries total}`."
  ([conn] (c/clear-caches conn))
  ([conn opts] (c/clear-caches conn opts)))

(defn compare-tacticians
  "Run `goal` in `context` under several **tacticians** — the node engine's search
  orderings — each to completion, and return one row per tactician: the search it ran, its
  wall-clock, and its answer set."
  ([conn goal] (c/compare-tacticians conn goal))
  ([conn goal context] (c/compare-tacticians conn goal context))
  ([conn goal context opts] (c/compare-tacticians conn goal context opts)))

(defn context-down
  "The contexts that inherit from `c`, reflexively — `c` plus every context that sees it."
  [conn c]
  (c/context-down conn c))

(defn context-up
  "The contexts `c` inherits from, reflexively — `c` plus everything it *sees* via
  `genlCx`."
  [conn c]
  (c/context-up conn c))

(defn contexts-of
  "The contexts in which `sentence` is asserted."
  [conn sentence]
  (c/contexts-of conn sentence))

(defn count-in-context
  "How many sentexes are **stored** in `context` — one set-size read, O(1), nothing
  fetched."
  [conn context]
  (c/count-in-context conn context))

(defn count-with-arg
  "How many fact sentexes hold `term` at argument position `pos`, as **stored** — cheap,
  one O(1) set-size read per predicate declaring an argument at that slot."
  [conn pos term]
  (c/count-with-arg conn pos term))

(defn count-with-functor
  "How many fact sentexes with functor `pred` are **stored** — one set-size read, O(1)."
  [conn pred]
  (c/count-with-functor conn pred))

(defn defeat-class
  "The current defeat-class of a believed handle (:monotonic / :default), or nil when it is
  OUT — the effective strength of the belief after settling."
  [conn handle]
  (c/defeat-class conn handle))

(defn dependent-justifications
  "Justifications that use `handle` as an antecedent — what rests on it, which is what an
  impact analysis before a `retract!` asks for."
  [conn handle]
  (c/dependent-justifications conn handle))

(defn deprecated?
  "Did a believed `rewriteOf` name `term` the dispreferred side? False for a `sameAs` or
  `equals` member: those merge without retiring either name."
  ([conn term] (c/deprecated? conn term))
  ([conn term context] (c/deprecated? conn term context)))

(defn describe
  "Everything the KB holds about one term, as one map, keyed by the term's own role
  (`term-role`) — the read behind \"what can I ask about `X`?\"."
  ([conn term] (c/describe conn term))
  ([conn term context] (c/describe conn term context))
  ([conn term context opts] (c/describe conn term context opts)))

(defn disjoint-metatypes
  "The declared disjoint metatypes — each a type whose member types are pairwise disjoint
  by `(disjoint_metatype M)`."
  [conn]
  (c/disjoint-metatypes conn))

(defn disjoint?
  "Are types `a` and `b` provably disjoint (via disjoint declarations, closed under genl)?
  With a `context`, only declarations and genl edges visible from it count — the vantage
  every definitional check now judges from."
  ([conn a b] (c/disjoint? conn a b))
  ([conn a b context] (c/disjoint? conn a b context)))

(defn edit!
  "Apply a batch of assertions and retractions in **one settle**."
  [conn batch]
  (c/edit! conn batch))

(defn edit-with-consequences!
  "`edit`, plus what the batch turned out to **mean** — the belief it added and the belief
  it took away, in `preview`'s entry shapes."
  ([conn batch] (c/edit-with-consequences! conn batch))
  ([conn batch opts] (c/edit-with-consequences! conn batch opts)))

(defn equiv-class
  "Every term known equal to `term`, itself included."
  ([conn term] (c/equiv-class conn term))
  ([conn term context] (c/equiv-class conn term context)))

(defn escalate
  "The cheapest level that answers `goal` — climb the stack from `floor` and stop at the
  first level with results."
  ([conn goal] (c/escalate conn goal))
  ([conn goal context] (c/escalate conn goal context))
  ([conn goal context floor] (c/escalate conn goal context floor)))

(defn explain-levels
  "What every level yields for `goal`: a seq of {:level :name :count}."
  ([conn goal] (c/explain-levels conn goal))
  ([conn goal context] (c/explain-levels conn goal context)))

(defn export!
  "Write `kb` out as a portable **export dump** in `dir` and return a summary:"
  ([conn dir] (c/export! conn dir))
  ([conn dir opts] (c/export! conn dir opts)))

(defn exposed-clashes
  "Every disjointness clash the KB currently makes jointly visible: a term holding two
  types some context can see as disjoint, where each membership was admissible where it
  was written."
  [conn]
  (c/exposed-clashes conn))

(defn find-terms
  "The vocabulary terms whose name matches `q`, sorted by name."
  ([conn q] (c/find-terms conn q))
  ([conn q opts] (c/find-terms conn q opts)))

(defn forward-chain
  "Run forward chaining to a fixpoint over every believed sentex, then settle belief
  (resolve contradictions)."
  ([conn] (c/forward-chain conn))
  ([conn opts] (c/forward-chain conn opts)))

(defn genl?
  "Is `sub` a (reflexive-transitive) subtype of `super`? Types, not individuals — for an
  individual's type membership use `isa?`."
  ([conn sub super] (c/genl? conn sub super))
  ([conn sub super context] (c/genl? conn sub super context)))

(defn handles
  "Every live sentex handle in the KB — premises and anything forward-derived alike, read
  straight off the record store."
  [conn]
  (c/handles conn))

(defn has-prop?
  "Does `pred` carry the metadata property `kind` — one of `:transitive`, `:symmetric`,
  `:asymmetric`, `:reflexive`, `:functional`, `:decontextualized`,
  `:forced-decontextualized`, `:abducible`, `:reifiable`, `:unreifiable`? Declared by the
  corresponding sentex, e.g. `(symmetric siblingOf)`."
  ([conn kind pred] (c/has-prop? conn kind pred))
  ([conn kind pred context] (c/has-prop? conn kind pred context)))

(defn inverse-of
  "The predicate declared inverse to `pred` by an `(inverse P Q)` sentex, or nil."
  ([conn pred] (c/inverse-of conn pred))
  ([conn pred context] (c/inverse-of conn pred context)))

(defn justification
  "The justification for an id, or nil — nil in, nil out; a non-id is refused
  (`:bad-handle`)."
  [conn jid]
  (c/justification conn jid))

(defn kb-diff
  "What two KBs disagree about, as content: `{:added :removed :moved :belief-changed}`."
  [conn b]
  (c/kb-diff conn b))

(defn kb-quality
  "Seven readings about the **knowledge** — one map, seven keys, each a distribution rather
  than a number:"
  ([conn] (c/kb-quality conn))
  ([conn opts] (c/kb-quality conn opts)))

(defn levels
  "The stack as data: {:level :name :below :adds} per level."
  [conn]
  (c/levels conn))

(defn lookup
  "Answer `goal` in `context` using exactly the machinery of `level`:"
  ([conn level goal] (c/lookup conn level goal))
  ([conn level goal context] (c/lookup conn level goal context)))

(defn metatype-members
  "The member types of disjoint metatype `m` — the set whose every pair `disjoint?` holds
  of, closed under genl."
  [conn m]
  (c/metatype-members conn m))

(defn possible-relations
  "The base relations `calculus` still allows between `a` and `b`, given everything
  believed in `context` — the set `ask` checks a goal against, exposed directly."
  [conn calculus context a b]
  (c/possible-relations conn calculus context a b))

(defn premise?
  "Is the sentex at `handle` a **premise** — asserted in its own right rather than derived?
  A premise rests on nothing, so no justification names it as a conclusion and retracting
  its supports cannot take it OUT; a derived sentex is the other case, and
  `supporting-justifications` is what shows why."
  [conn handle]
  (c/premise? conn handle))

(defn preview
  "What would this batch do to the KB — **without** leaving it done."
  ([conn batch] (c/preview conn batch))
  ([conn batch opts] (c/preview conn batch opts)))

(defn props
  "The set of predicates carrying metadata property `kind` (see `has-prop?`)."
  [conn kind]
  (c/props conn kind))

(defn prove-within
  "Anytime `prove`: run the depth-first backward chainer over `goal` (a sentence or a
  conjunction vector, as `prove`) in `context`, bounded by `budget` — a map of any of
  `{:max-ms n :max-results n :max-depth n :max-term-growth n}`."
  ([conn goal budget] (c/prove-within conn goal budget))
  ([conn goal context budget] (c/prove-within conn goal context budget)))

(defn provenance
  "The provenance map recorded for `handle` — `{:creator … :created … …}` — or nil if none."
  [conn handle]
  (c/provenance conn handle))

(defn qualitative-network
  "The constraint network `calculus` computes over everything **believed and visible** in
  `context`: every pair of terms its predicates relate, tightened by path consistency to
  the base relations still possible between them."
  [conn calculus context]
  (c/qualitative-network conn calculus context))

(defn qualitative-scenario
  "One concrete arrangement consistent with everything believed in `context` — `{[a b] →
  relation}`, one base relation per pair — or nil when the believed facts are
  unsatisfiable."
  [conn calculus context]
  (c/qualitative-scenario conn calculus context))

(defn qualitative-scenarios
  "Up to `limit` distinct arrangements, as `qualitative-scenario` renders one."
  [conn calculus context limit]
  (c/qualitative-scenarios conn calculus context limit))

(defn quality-report
  "A `kb-quality` map as Markdown — the counts first and the capped lists after."
  [conn quality]
  (c/quality-report conn quality))

(defn query-plan
  "How a goal would be answered, at whichever of the two scales the goal has."
  ([conn goal] (c/query-plan conn goal))
  ([conn goal context] (c/query-plan conn goal context)))

(defn query?
  "Is `goal` answerable under `opts`? `query`, asked for one answer."
  ([conn goal] (c/query? conn goal))
  ([conn goal context] (c/query? conn goal context))
  ([conn goal context opts] (c/query? conn goal context opts)))

(defn readable-sentence
  "A sentex's sentence with the author's variable names restored — pass a sentex map (from
  `sentex` / `sentexes-matching`)."
  [conn sx]
  (c/readable-sentence conn sx))

(defn representative
  "The term standing for `term`'s equivalence class — `term` itself when nothing has merged
  it, so this is total and never nil."
  ([conn term] (c/representative conn term))
  ([conn term context] (c/representative conn term context)))

(defn same-class?
  "Do `a` and `b` denote the same thing? Distinct symbols denote distinct individuals until
  an equality sentex says otherwise."
  ([conn a b] (c/same-class? conn a b))
  ([conn a b context] (c/same-class? conn a b context)))

(defn search-tree
  "The backward search for `goal` in `context`, as data — every node the frontier reached,
  not only the path that answered."
  ([conn goal] (c/search-tree conn goal))
  ([conn goal context] (c/search-tree conn goal context))
  ([conn goal context opts] (c/search-tree conn goal context opts)))

(defn sees?
  "Does context `k` see assertions made in context `y`? True iff `y` is in `k`'s genlCx
  up-closure (reflexively, so a context sees itself)."
  [conn k y]
  (c/sees? conn k y))

(defn sentex-count
  "How many sentexes the KB holds, in total — the count the count-aware trie keeps at its
  root, so O(1) and nothing fetched."
  [conn]
  (c/sentex-count conn))

(defn sentexes-in-context
  "Every **stored** sentex asserted in `context` (its extent, rules included) — a defeated
  or unsupported one included."
  ([conn context] (c/sentexes-in-context conn context))
  ([conn context opts] (c/sentexes-in-context conn context opts)))

(defn sentexes-with-arg
  "Every **stored** fact sentex holding `term` at 1-based argument position `pos` — a
  defeated or unsupported one included."
  ([conn pos term] (c/sentexes-with-arg conn pos term))
  ([conn pos term opts] (c/sentexes-with-arg conn pos term opts)))

(defn sentexes-with-functor
  "Every **stored** fact sentex whose functor is `pred`, any arity, either polarity — a
  defeated or unsupported one included."
  ([conn pred] (c/sentexes-with-functor conn pred))
  ([conn pred opts] (c/sentexes-with-functor conn pred opts)))

(defn settle-stats
  "Instrumentation for the `exceptWhen` fixpoint in `settle`."
  [conn]
  (c/settle-stats conn))

(defn specified-violations
  "The audit result for one binary `(predAllSpecified pred indep)` integrity requirement in
  `context`, always carrying a `:status`: `{:status :audited :violations #{x…}}` — every
  member x of `indep` for which no believed `(pred x y)` carries a **determinate** filler
  y satisfying `pred`'s derived slot contract, an empty set where the requirement holds —
  or `{:status :gap :gap :missing-slot-typing …}` where `pred` carries no visible slot
  typing at the audited position."
  ([conn pred indep context] (c/specified-violations conn pred indep context))
  ([conn pred indep context arg-pos] (c/specified-violations conn pred indep context arg-pos)))

(defn supporting-justifications
  "Justifications that conclude `handle` (its supporting justifications), in **content**
  order — the informant's own sentence, then the antecedent sentences
  (`kb/justification-content-key`)."
  [conn handle]
  (c/supporting-justifications conn handle))

(defn term-count
  "How many distinct terms the KB's vocabulary holds — one set-size read, O(1), nothing
  fetched."
  [conn]
  (c/term-count conn))

(defn term-expression
  "The functional expression a reified term denotes — `(FruitFn AppleTree)` for the
  constant minted from it — or nil for an ordinary term, and for a reified one whose
  `(termOfUnit K E)` map is not believed."
  [conn term]
  (c/term-expression conn term))

(defn terms
  "Every term the index is keyed by — the KB's vocabulary: each predicate, individual,
  type, and context name mentioned by a stored sentex, at any nesting depth."
  [conn]
  (c/terms conn))

(defn types
  "Every type currently in the genl hierarchy — the nodes of the closure, i.e. every type
  named by some believed `genl` edge."
  [conn]
  (c/types conn))

(defn vocabulary-audit
  "Every term `CxCore` declares in `kb`, classified — `{:enforced [[term why] …] :inert
  [[term why] …] :unclassified [term …] :retired [term …] :contradicted [term …]}`."
  [conn]
  (c/vocabulary-audit conn))

;; ---- end generated ------------------------------------------------------
