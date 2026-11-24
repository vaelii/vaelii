;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.reasoning
  "The `Reasoning` record and its readers, as a held namespace (`vaelii.impl.types.prover`
  states what that means).  A KB holds one `Reasoning` value in a volatile under its
  `:reasoning` field: the belief network, the taxonomy, and every atom a recover or a
  settle fills.  `vaelii.impl.kb/empty-reasoning` builds an empty one.

  A `Reasoning` value is not a store.  A KB's two stores, `:records` and `:index`, are
  durable and are reached through `vaelii.impl.protocols`, and both survive the process
  that wrote them.  A `Reasoning` value lives in this process alone:
  `vaelii.impl.recovery/recover` rebuilds it from the records, as `vaelii.impl.reindex`
  rebuilds the index from them.  `vaelii.impl.reasoning-image` writes one to a directory so
  that an open can install it in place of a recover, and a KB that declines the image runs
  the recover instead.

  A background rebuild's install replaces the whole value with one `vreset!`
  (`vaelii.impl.recovery`), so the belief a KB holds changes in one step.  A reader
  that must read the network and the taxonomy of one belief reads them through one
  dereference: `vaelii.impl.kb/read-copy` returns a KB whose volatile holds the current
  value and is never reset, and `vaelii.core`'s public reads run against it while an
  install is pending.

  Each reader below is inlined at its call site, so `(taxonomy kb)` compiles to
  `(:taxonomy @(:reasoning kb))`: one field read, one volatile read and one field read.")

;; `solver` is not here: it is configuration the caller sets, and a rebuild shares it
;; with the KB it rebuilds (`kb/rebuild-shared`).  Everything here is empty on a new KB
;; and rebuilt by `recover`, or is a cache a missing read refills.
;;
;; `program` holds the last edge Program handed to the solver (the ASP backend in
;; vaelii.impl.asp.edge).  It is kept because belief is *self-erasing evidence*: once
;; settle defeats one side of a tie, that side stops matching, so the very nogood that
;; produced the contested set is no longer derivable from the KB.  Recomputing it after the
;; fact yields nothing.  Anything wanting to ask what the tie *was* — which beliefs were
;; forced and which were an arbitrary pick (`asp.edge/classify`) — has to read the program
;; the decision was actually made from.
;;
;; `violations` holds the definitional constraints a *derived* conclusion would have broken
;; during the last chaining run — see `place-conclusion` and `violations`.
;;
;; `recheck` is the exception re-check queue: `{rule-handle -> triggers}` for the rules
;; whose `exceptWhen` query may have flipped since the last settle, posted by the triggers
;; (a fact arriving or leaving on one of the exception's predicates, or any genl/genlCx
;; edge change) and drained by `settle`.  `triggers` is the set of sentences that moved —
;; which firings of that rule to re-evaluate — or `:all` when there is no such sentence and
;; all of them must be.  Nothing here caches whether an exception *holds* — the queue says
;; what to re-evaluate, and the re-evaluation says what is true.
;;
;; `settle-stats` is instrumentation for the exception fixpoint: `:iterations` counts the
;; passes in which the blocked set actually moved (0 = nothing blocked, 1 = one pass
;; sufficed), `:passes` the total loop passes including the confirming one, and
;; `:histogram` the distribution of `:iterations` since the last reset.
;;
;; `qcn` is where a qualitative constraint network **lives between reads**: an atom of
;; `{[calculus-name context] -> {:read … :clock n}}`, keyed by `observe/change-clock`
;; and re-derived the moment that has moved (`vaelii.impl.qcn-kb`).  Per KB rather than
;; global, because two KBs in one JVM share the clock but not their content.
;;
;; `matches` is the literal cache (`vaelii.impl.literal-cache`): an atom of
;; `{[canonical-literal context hierarchical? arg-root?] -> {:value … :clock n}}` holding
;; what `matches-visible` answered, α-renamed so two spellings of one question share an
;; entry and keyed by `observe/change-clock` so any mutation retires it.  Per KB for
;; the same reason `qcn` is.  A declared field rather than a key on the record's extension
;; map, because `matches-visible` reads it on every retrieval and an extension-map key
;; costs a hash lookup where a field costs none.  Every other field here is declared for
;; the same reason.
;;
;; `mint-queues` holds two queues the settle's mint withdrawal and release drain:
;; `:departed`, the removed records that can have subsumed a mint
;; (`special/note-departure!`), and `:unpremised`, the records a retraction left standing
;; on a derivation alone (`special/note-unpremised!`).  The mints themselves are an index
;; family (docs/indexing.md, "The mint family").
;;
;; `mint-rules` holds `{:gen n}`, and `:table`, the `{kind handle}` of the stored inert
;; rule each argument declaration kind's mints are justified under, once a read fills it
;; off the index's `[:mint-rules]` family (`kb/mint-rule-table`).  A store or removal of
;; such a rule and a rewrite of the stores drop the table and move `:gen`
;; (`kb/forget-mint-rules!`).
;;
;; `nogood-candidates` is the candidate index of the nogood families,
;; `{:converse #{handle} :arity #{handle} … :inherited …}`: the stored ground binary tuples
;; under a converse mark with a stored converse, the arity, membership and related-types
;; candidates, kept at the store and removal choke points and rebuilt by `recover`; and
;; the inherited clashes with their vantages, which each settle re-finds.  No verdict is stored
;; here: the settle places each nogood (`vaelii.impl.decide`, docs/nmtms.md, "The nogood
;; families").
;;
;; `arity-lengths` holds the arity family's length entries, a weighted LRU keyed by functor
;; carrying the `genl` generation and relation epoch it last read under `:gen` and `:epoch`
;; (`vaelii.impl.decide.arity`).  Nil until the family first reads it, and reset by
;; `recover`.
;;
;; `kb/empty-reasoning` states what the remaining fields hold, beside the expression that
;; makes each one.
(defrecord Reasoning [tms taxonomy program violations recheck refused
                      settle-stats chain-stats preserved-clashes
                      supersessions qcn qcn-joined matches closures
                      respell except-moves owed-drops
                      mint-queues mint-rules engine-rules nogood-candidates arity-lengths
                      sync-memo crossing-reads])

(defn of
  "The `Reasoning` value `kb` holds now."
  {:inline (fn [kb] `(deref (:reasoning ~kb)))}
  [kb]
  @(:reasoning kb))

(defn tms
  "`kb`'s belief network."
  {:inline (fn [kb] `(:tms (deref (:reasoning ~kb))))}
  [kb]
  (:tms @(:reasoning kb)))

(defn taxonomy
  "`kb`'s taxonomy atom."
  {:inline (fn [kb] `(:taxonomy (deref (:reasoning ~kb))))}
  [kb]
  (:taxonomy @(:reasoning kb)))

(defn program
  "`kb`'s `:program` atom."
  {:inline (fn [kb] `(:program (deref (:reasoning ~kb))))}
  [kb]
  (:program @(:reasoning kb)))

(defn violations
  "`kb`'s `:violations` atom."
  {:inline (fn [kb] `(:violations (deref (:reasoning ~kb))))}
  [kb]
  (:violations @(:reasoning kb)))

(defn recheck
  "`kb`'s `:recheck` atom."
  {:inline (fn [kb] `(:recheck (deref (:reasoning ~kb))))}
  [kb]
  (:recheck @(:reasoning kb)))

(defn refused
  "`kb`'s `:refused` atom."
  {:inline (fn [kb] `(:refused (deref (:reasoning ~kb))))}
  [kb]
  (:refused @(:reasoning kb)))

(defn settle-stats
  "`kb`'s `:settle-stats` atom."
  {:inline (fn [kb] `(:settle-stats (deref (:reasoning ~kb))))}
  [kb]
  (:settle-stats @(:reasoning kb)))

(defn chain-stats
  "`kb`'s `:chain-stats` atom."
  {:inline (fn [kb] `(:chain-stats (deref (:reasoning ~kb))))}
  [kb]
  (:chain-stats @(:reasoning kb)))

(defn nogood-candidates
  "`kb`'s `:nogood-candidates` atom."
  {:inline (fn [kb] `(:nogood-candidates (deref (:reasoning ~kb))))}
  [kb]
  (:nogood-candidates @(:reasoning kb)))

(defn arity-lengths
  "`kb`'s `:arity-lengths` atom."
  {:inline (fn [kb] `(:arity-lengths (deref (:reasoning ~kb))))}
  [kb]
  (:arity-lengths @(:reasoning kb)))

(defn preserved-clashes
  "`kb`'s `:preserved-clashes` atom."
  {:inline (fn [kb] `(:preserved-clashes (deref (:reasoning ~kb))))}
  [kb]
  (:preserved-clashes @(:reasoning kb)))

(defn mint-queues
  "`kb`'s `:mint-queues` atom."
  {:inline (fn [kb] `(:mint-queues (deref (:reasoning ~kb))))}
  [kb]
  (:mint-queues @(:reasoning kb)))

(defn mint-rules
  "`kb`'s `:mint-rules` atom."
  {:inline (fn [kb] `(:mint-rules (deref (:reasoning ~kb))))}
  [kb]
  (:mint-rules @(:reasoning kb)))

(defn engine-rules
  "`kb`'s `:engine-rules` atom: `{:gen n}`, and under `:any` the answer per engine once
  `kb/stores-engine-rule?` has read whether the store holds a rule taking it.
  `kb/forget-engine-rules!` drops `:any`."
  {:inline (fn [kb] `(:engine-rules (deref (:reasoning ~kb))))}
  [kb]
  (:engine-rules @(:reasoning kb)))

(defn supersessions
  "`kb`'s `:supersessions` atom."
  {:inline (fn [kb] `(:supersessions (deref (:reasoning ~kb))))}
  [kb]
  (:supersessions @(:reasoning kb)))

(defn respell
  "`kb`'s `:respell` atom."
  {:inline (fn [kb] `(:respell (deref (:reasoning ~kb))))}
  [kb]
  (:respell @(:reasoning kb)))

(defn except-moves
  "`kb`'s `:except-moves` atom."
  {:inline (fn [kb] `(:except-moves (deref (:reasoning ~kb))))}
  [kb]
  (:except-moves @(:reasoning kb)))

(defn owed-drops
  "`kb`'s `:owed-drops` atom."
  {:inline (fn [kb] `(:owed-drops (deref (:reasoning ~kb))))}
  [kb]
  (:owed-drops @(:reasoning kb)))

(defn sync-memo
  "`kb`'s `:sync-memo` atom."
  {:inline (fn [kb] `(:sync-memo (deref (:reasoning ~kb))))}
  [kb]
  (:sync-memo @(:reasoning kb)))

(defn crossing-reads
  "`kb`'s `:crossing-reads` atom."
  {:inline (fn [kb] `(:crossing-reads (deref (:reasoning ~kb))))}
  [kb]
  (:crossing-reads @(:reasoning kb)))

(defn qcn
  "`kb`'s `:qcn` atom."
  {:inline (fn [kb] `(:qcn (deref (:reasoning ~kb))))}
  [kb]
  (:qcn @(:reasoning kb)))

(defn qcn-joined
  "`kb`'s `:qcn-joined` atom."
  {:inline (fn [kb] `(:qcn-joined (deref (:reasoning ~kb))))}
  [kb]
  (:qcn-joined @(:reasoning kb)))

(defn matches
  "`kb`'s `:matches` atom."
  {:inline (fn [kb] `(:matches (deref (:reasoning ~kb))))}
  [kb]
  (:matches @(:reasoning kb)))

(defn closures
  "`kb`'s `:closures` atom."
  {:inline (fn [kb] `(:closures (deref (:reasoning ~kb))))}
  [kb]
  (:closures @(:reasoning kb)))
