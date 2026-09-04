;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.wiring
  "The write path and the prover registry as the layers *beneath* them see it — the whole
  inventory of calls the require graph cannot express, in one file.

  Everything else in the engine is layered, and every edge is a static require the
  compiler checks: kb <- checks <- special <- integrate <- chain <- settle <- vaelii.core.
  Exactly two calls run the other way:

    `assert-sentence` — the full assertion path, called from `vaelii.impl.nat` (a reified
    NAT stores its `(termOfUnit K E)` map and its materialized types), from
    `vaelii.impl.skolem` (a firing mints its witness), and from
    `vaelii.impl.quasiquote` (declaring the four marks quasiquotation runs on).  Storing
    is a *whole* assert — naming, the definitional checks, the index, chaining, settle —
    so the write path runs chaining, and chaining calls back here to mint a constant
    (docs/skolem.md).

    `solve-goal` — the prover registry, called from `vaelii.impl.resolution` to discharge
    a deferred antecedent (`different` / `evaluate` / `unknown`).  Backward chaining is a
    leaf the registry dispatches to, and `unknown` runs the registry back over its own
    argument, so negation-as-failure is mutually recursive with the chainer that asked
    for it (docs/naf.md).

  Two further calls run the other way for a different reason:

    `import-dump` — `vaelii.impl.io.import` sits *above* `vaelii.core` and requires it,
    because reading a dump is asserting: it re-canonicalizes records, reindexes and
    recovers through the public write path.  `vaelii.core/import!` is the inverse of
    `export!`, which is public, and a round trip whose two halves are not both public is
    not a round trip — so the delegation points up, and this is where a call that points
    up is written down.

    `specified-violations` / `all-specified-violations` — `vaelii.impl.predall` sits
    *above* `vaelii.core` for the mirror-image reason: running the `predAllSpecified`
    audit is asking.  The audit reads a declaration and then asks the KB one goal per
    member, and a goal answered outside `vaelii.core/ask` sees neither the context's
    `genlCx` ancestor set nor the goal preparation that read runs (`read-in-context`,
    `ist-goal` and `prepare-goal-for-read` are private to `vaelii.core`).  An audit that
    reported violations a scoped read would not have is worse than no audit, so the
    reader asks through the public read path and the delegation points up to reach it.

  The first two are genuine mutual recursion: the cycle is in the **behaviour**, neither
  is a misplaced function, and no arrangement of the code removes either.  The last two
  are layering inversions rather than recursions, and are kept here for the same reason —
  a call the require graph cannot express belongs in the one file that inventories them.
  Why they are gathered here rather than left at their call sites, what `lein lint`'s
  **E8** enforces, and why each is a `delay` rather than a dynamic var —
  docs/namespaces.md, \"The layering\"."
  (:refer-clojure :exclude [assert]))

;; ---- the write-path mode flag --------------------------------------------
;; It lives here rather than with the write path because both sides of the recursion read
;; it: `vaelii.core`'s assert decides whether to settle by it, and `skolem` binds it around
;; a mint to say "not now — I am inside the fixpoint you are about to settle".  Down here
;; both can see it without either naming the other.

(def ^:dynamic *defer-settle?*
  "When true, the assert path does **not** `settle` after storing — belief is left
  un-reconciled for the caller to settle once, later.  Three callers bind it:

  - a rule firing minting a skolem NAT mid-fixpoint (`vaelii.impl.skolem`): the nested
    `(termOfUnit K E)` assert is monotonic bookkeeping and the enclosing firing settles
    once when it finishes, so settling per mint would be redundant churn — and worse,
    would relabel belief inside the running chain (docs/skolem.md);
  - a fired conclusion reducing a ground `Quasiquote` to its constant
    (`vaelii.impl.quasiquote/reduce-in-conclusion`), which is the same mint at the same
    moment and defers for the same reason;
  - `with-deferred-settle` / `assert-many`, which run a whole batch of asserts under it
    and settle once at the end, so a bulk load pays one belief reconciliation instead of
    N.  Chaining still runs per assert (only the `settle` is deferred), so the final
    settle sees the same stored state a per-assert settle would have, and order
    independence guarantees the same beliefs.

  Retraction settles eagerly regardless — reviving a defeated default is not part of an
  assert batch."
  false)

;; ---- the two cuts, and the two inversions ---------------------------------

(def ^:private core-assert
  (delay (requiring-resolve 'vaelii.core/assert)))

(def ^:private provers-solve-goal
  (delay (requiring-resolve 'vaelii.impl.provers/solve-goal)))

(def ^:private io-import-dump
  (delay (requiring-resolve 'vaelii.impl.io.import/import-dump)))

(def ^:private predall-specified-violations
  (delay (requiring-resolve 'vaelii.impl.predall/specified-violations)))

(def ^:private predall-all-specified-violations
  (delay (requiring-resolve 'vaelii.impl.predall/all-specified-violations)))

(defn assert-sentence
  "`vaelii.core/assert` — store `sentence` in `context` under `opts`, returning its handle.
  See the namespace docstring for why this is not a require."
  [kb sentence context opts]
  (@core-assert kb sentence context opts))

(defn solve-goal
  "`vaelii.impl.provers/solve-goal` — the registry's raw solution bindings for `goal` in
  `context`.  See the namespace docstring for why this is not a require."
  [kb goal context]
  (@provers-solve-goal kb goal context))

(defn import-dump
  "`vaelii.impl.io.import/import-dump` — read the export dump at `dir` into `kb`.
  See the namespace docstring for why this is not a require."
  [kb dir opts]
  (@io-import-dump kb dir opts))

(defn specified-violations
  "`vaelii.impl.predall/specified-violations` — the audit result for one binary
  `(predAllSpecified pred indep)` declaration in `context`: `{:violations #{…}}`, or
  `{:gap …}` where `pred` carries no visible slot typing at `arg-pos`.  See the
  namespace docstring for why this is not a require."
  [kb pred indep context arg-pos]
  (@predall-specified-violations kb pred indep context arg-pos))

(defn all-specified-violations
  "`vaelii.impl.predall/all-specified-violations` — every `predAllSpecified` and
  `predSpecifiedAll` declaration visible in `context`, audited.  See the namespace
  docstring for why this is not a require."
  [kb context]
  (@predall-all-specified-violations kb context))
