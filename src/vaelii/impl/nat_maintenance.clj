;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.nat-maintenance
  "The reified-NAT maintenance the write paths run once their own work is done —
  docs/nat.md, docs/context-nat.md.

  Three entry points, one per site in `vaelii.core`:

  - `reconcile-assert`, after a sentence is stored: the collision merge an equality may
    have caused, the correspondence reconciliation, and the structural `genlCx` edges the
    new fact entails.
  - `reconcile-revivals!`, after a teardown has settled: the edges the producer could not
    build while their declaration was OUT.
  - `collect-orphans!`, on the same teardown: the reified constants no live use
    references any more, removed to a fixpoint.

  Sits above both `vaelii.impl.nat` and `vaelii.impl.context-nat`, because the assert-path
  sequencing spans the two, and above `vaelii.impl.settle`, because a computed `genlCx`
  edge owes a chain and a settle of its own.

  The teardown entry point is an **argument**, not a require: the orphan sweep retracts
  through `vaelii.core/retract!`, and the engine never requires the API namespace
  (docs/namespaces.md, \"The layering\").  `vaelii.core` hands its own `retract!` in."
  (:require [vaelii.impl.context-nat :as context-nat]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.settle :as settle]))

;; ---- computed genlCx edges: the merges they license -----------------------

(defn- settle-computed-edges
  "Settle once a computed `genlCx` edge was built (`built?`), so the settle's drain reads
  what it shows (`special/drain-context-moves!`), seeding no chaining when `opts` asks
  `{:chain? false}`.  The producer runs after the write that entails the edge has
  settled, so the edge needs a settle of its own."
  [kb built? opts]
  (when built? (settle/settle-write kb (:chain? opts true)))
  nil)

;; ---- the assert path ------------------------------------------------------

(defn reconcile-assert
  "The reified-NAT maintenance a just-stored `sentence` calls for, run after
  the sentence is in and its own chaining has settled.  `opts` is the assert's, carried
  through to the chain a computed `genlCx` edge's merges run.

  Two questions in order, behind one gate:

  - `nat/reconcile-nats!` — the collision merge a rename may have caused, and the
    correspondence a value, an application or a declaration arriving last leaves to
    settle (docs/nat.md).
  - `context-nat/reconcile-genlCx` — the structural `genlCx` edges a context's mint, a
    `contextArgSubrelation` declaration or an `R`-evidence fact entails; materialized
    justified so they belief-follow (docs/context-nat.md), and settled
    (`settle-computed-edges`).

  **One gate covers all of it**, `nat/any-reified-constants?`: a KB with a reifiable
  function or a stored `natFormula` map.  A context slot mints a `cx/` constant with no
  declaration, so the map count is what admits a KB whose only constants are contexts.  A
  KB that has minted nothing and declares no reifiable function pays neither the
  `any-context-subrelations?` index read nor the correspondence count."
  [kb sentence opts]
  (when (and (nat/any-reified-constants? kb) (sequential? sentence))
    (nat/reconcile-nats! kb sentence)
    (settle-computed-edges kb (context-nat/reconcile-genlCx kb sentence) opts)))

;; ---- the teardown path ----------------------------------------------------

(defn reconcile-revivals!
  "Rebuild the structural `genlCx` edges a teardown revived the premises of, and apply
  the merges they license.

  A teardown can put a `contextArgSubrelation` declaration or a stored R-evidence fact
  back IN by retracting a monotonic defeater above it, and the producer runs on the
  assert path only — so an edge never built while the declaration was OUT would stay
  absent with nothing for the JTMS to revive.  `context-nat/reconcile-revivals` rebuilds
  it against the settled belief, and settles what it built.

  Gated internally on the KB declaring a context function."
  [kb]
  (settle-computed-edges kb (context-nat/reconcile-revivals kb) nil))

(def ^:dynamic ^:private *in-orphan-removal?*
  "Bound true while `remove-orphaned-nats!` retracts orphaned reified NAT bookkeeping, so
  the nested retractions do not re-enter the sweep."
  false)

(defn- remove-orphaned-nats!
  "Remove every reified constant no live use references any more — its `natFormula`
  map and materialized result types would otherwise dangle a raw `nat/` symbol.

  **Both kinds of constant, at one gate and by one rule** (docs/nat.md,
  docs/context-nat.md).  An object `nat/` constant is referenced by the sentences that
  name it; a `cx/` context is referenced by those *and* by whatever is stored in it, so
  the last fact leaving an empty reified context is as much an orphaning removal as the
  last sentence dropping its name — `nat/orphans-named-by` reads a removed sentex's
  context slot beside its sentence for exactly that, and asks the extent before the term
  index.  What the producer *computed* off the map — the structural `genlCx` edges of
  docs/context-nat.md — is not a reference: it is derived from the very bookkeeping in
  question, so a pair of ordered contexts would otherwise hold each other up forever.

  `sink` is the teardown's removal record (`integrate/*removed-sink*`), or nil to ask
  the whole KB.  With one, each round's candidates are the constants the sentexes
  removed since the last round named, and the cost is the region's rather than the KB's
  whole `natFormula` population's.  `retract!` is the teardown entry point to take each
  bookkeeping handle out with.

  **A removal is what makes a candidate, and belief is what settles one** — the two are
  not the same question and this arm does not treat them as one.  A use that merely stops
  being *believed* is not a use that went: a defeated premise is still in the store, still
  names its constant, and a relabel can restore it.  Collecting on that reading would
  delete the map while a stored sentence names the constant, and the restoring relabel
  would dangle the very `nat/` symbol the sweep exists to prevent — so a constant no
  removal named is not a candidate however its uses are labelled.  `nat/orphan?` still
  reads belief, because that is the right question about a candidate: whether what is
  *left* referencing it is only its own bookkeeping.

  Loops to a fixpoint either way, since removing one orphan can orphan a nested one —
  the constant standing in the removed expression.  **The region grows with the loop**:
  the retractions below append to the same sink, so what one round's removals stopped
  referencing is exactly the next round's candidate set, and a cascade is found by the
  same rule that found the first orphan.  The guard bounds a pathological chain; the
  empty round is what normally ends it."
  [kb sink retract!]
  (binding [*in-orphan-removal?* true]
    (loop [mark 0 guard 0]
      (let [removed (when sink @sink)
            orphans (if sink
                      (nat/orphans-named-by kb (subvec removed mark))
                      (nat/orphaned-constants kb))
            ;; realized before the first retraction below, not while it runs: what
            ;; counts as an orphan's bookkeeping is read off the bookkeeping itself,
            ;; so a set computed lazily is a set computed partly against a KB this
            ;; loop has already torn pieces out of
            handles (vec (distinct (mapcat #(nat/bookkeeping-handles kb %) orphans)))]
        (when (and (seq handles) (< guard 64))
          (doseq [h handles] (retract! kb h))
          (recur (count removed) (inc guard)))))))

(defn collect-orphans!
  "Sweep a reified NAT orphaned by a teardown — its natFormula map and materialized types
  would dangle a raw `nat/` symbol (docs/nat.md), and an emptied `cx/` context would be
  a place nothing can reach and nothing is in (docs/context-nat.md).  Gated on
  `nat/any-reified-constants?`, and suppressed while already removing orphans.  `retract!` is the teardown entry point the
  sweep takes each bookkeeping handle out with.

  Two arms, and which one a caller takes turns on whether it can name the region the
  teardown touched:

  * **`retract!` and `edit!` pass their removal record** — every sentex that left the
    store while they ran, collected at the removal choke point
    (`integrate/*removed-sink*`), the settle's own sweep included.  A constant no removal
    named is not a candidate, at the cost of the region instead of the cost of the KB's
    whole NAT population; `remove-orphaned-nats!` says why a merely *defeated* use is not
    a use that went, and why collecting on one would be the dangling symbol rather than
    the fix for it.
  * **`rollback-batch!` for a batch passes nothing and asks the whole KB.**  It is
    putting a KB back rather than taking something out of one, so the claim it owes — the
    KB is as it was found — is about all of it rather than about one teardown's region;
    and a preview's batch reached this sweep at no point, having run with the settle
    sweep off (`settle/*sweep?*`).  A rollback runs once per batch, and only for a
    preview or a batch that refused, so the whole-KB cost is one it can carry.  The
    rollback of a single refused `assert` passes its removal record, since its settles
    ran with the sweep on.

  **The two arms therefore ask different questions, not one question at two costs.**  The
  region arm asks what a teardown's removals orphaned; the whole-KB arm asks which
  constants are orphaned *now*, which is the stronger reading and the one a restore owes."
  ([kb retract!] (collect-orphans! kb nil retract!))
  ([kb sink retract!]
   (when (and (not *in-orphan-removal?*) (nat/any-reified-constants? kb))
     (remove-orphaned-nats! kb sink retract!))))
