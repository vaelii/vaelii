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
  dereference: `vaelii.impl.kb/read-view` returns a KB whose volatile holds the current
  value and is never reset, and `vaelii.core`'s public reads run against it while an
  install is pending.

  Each reader below is inlined at its call site, so `(taxonomy kb)` compiles to
  `(:taxonomy @(:reasoning kb))`: one field read, one volatile read and one field read.")

;; `solver` is not here: it is configuration the caller sets, and a rebuild shares it
;; with the KB it rebuilds (`kb/rebuild-shared`).  Everything here is empty on a new KB
;; and rebuilt by `recover`, or is a cache a missing read refills.
;;
;; `clash-readings` holds the last settle's three coupled readings in one atom —
;; `:conflicts` (the unsatisfiable contradictions surfaced by `core/conflicts`),
;; `:contradictions`, and `:reports` — so a reader beside the writer takes them as one
;; publication rather than three (`settle/record-clashes!`).  `:contradictions` holds the
;; coexisting P/¬P pairs the last settle left standing.  Those are *represented dilemmas*,
;; not conflicts: neither rule named the other's case, so there is nothing to arbitrate and
;; both sides stay believed at :default (docs/exceptions.md, "What surfaces where").
;; `:conflicts` holds only the irreducible clashes among known-true content.  `:reports`
;; memoizes the `contradicts` reports the other two hand back — `{#{h1 h2} -> report}` for
;; the pairs the last settle reported, and nothing else, so it is bounded by what is
;; standing rather than by what ever stood.  Why an entry the settle's region does not hold
;; can be carried forward, and what removing it costs: docs/nmtms.md, "The reports are
;; rebuilt only where the region moved".
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
;; `{[calculus-name context] -> {:read … :clock n}}`, stamped with `observe/change-clock`
;; and re-derived the moment that has moved (`vaelii.impl.qcn-kb`).  Per KB rather than
;; global, because two KBs in one JVM share the clock but not their content.
;;
;; `matches` is the literal cache (`vaelii.impl.literal-cache`): an atom of
;; `{[canonical-literal context hierarchical? arg-root?] -> {:value … :clock n}}` holding
;; what `matches-visible` answered, α-renamed so two spellings of one question share an
;; entry and stamped with `observe/change-clock` so any mutation retires it.  Per KB for
;; the same reason `qcn` is.  A declared field rather than a key on the record's extension
;; map, because `matches-visible` reads it on every retrieval and an extension-map key
;; costs a hash lookup where a field costs none.  Every other field here is declared for
;; the same reason.
;;
;; `negations` is the memo beside `:opposed`, and the two answer different halves of one
;; question: `:opposed` says *which bodies could contradict*, kept O(1) per mutation at the
;; store and removal choke points; `:negations` says *what each of those bodies currently
;; contradicts about*, as `{body #{nogood}}`.  `:dirty` is the bodies a store or a removal
;; touched since the last settle drained it (`note-opposed!` posts them, the same choke
;; points that maintain `:opposed`); `:vocab` is the genlCx generation the joint-visibility
;; test reads through, so a context edge retires the whole memo.  Which three things move a
;; pairing, and the measured cost of dropping either narrowing: docs/nmtms.md, "Soft,
;; prioritized contradictions".
;;
;; `rule-antecedents` and `rule-contexts` are the rule rosters `special` bumps on every
;; rule index/unindex and reads per settle for the visibility seeds.  Neither is stored,
;; and recovery replays belief and the taxonomy rather than rule indexing, so
;; `rebuild-rule-roster!` is what refills them on a recovered, reopened or forked KB.
;;
;; `excepted` is the visibility roster beside `:opposed`, and kept the same way: `{context
;; -> {except-handle -> hidden-handle}}` for the stored `(except (sentexHandle H))` facts,
;; maintained O(1) at the store and removal choke points and rebuilt by `recover`.  It
;; holds **storage**, not belief — an except's own handle is what a reader checks `in?`
;; against — for the reason `:opposed` holds storage: belief moves without a sentex
;; arriving or leaving, so a roster that tried to track it would be maintained at a choke
;; point that does not exist.  `res/excepted-handles` reads it per placement and per
;; candidate justification (docs/exceptions.md, "Visibility removal").
;;
;; `scoped-defeats` is `{vantage -> #{handle}}`: the nogood losers the settle disbelieved
;; at a vantage strictly below their own context, which a reader at or below that vantage
;; reads as withdrawn (docs/nmtms.md, "A defeat is scoped to its vantage").  It is derived
;; state, cleared and re-decided by every settle exactly as the network's defeated set is.
;; `withdrawn` is the per-reader answer built from it and from `excepted`, `{reader ->
;; #{handle}}`, emptied whenever either input or the network moves.
;;
;; `vantage-disagreements` is `[{vantage -> handle} …]`, one entry per nogood whose live
;; vantages defeated **different** members.  A reader that sees two of an entry's vantages
;; sees two verdicts and takes neither: it reads every member of that nogood as believed,
;; and the nogood is reported by `contradictions` (docs/nmtms.md, "Vantages that
;; disagree").  Empty on nearly every KB, and every read of it is gated on that.
;;
;; `kb/empty-reasoning` states what the remaining fields hold, beside the expression that
;; makes each one.
(defrecord Reasoning [tms taxonomy clash-readings program violations recheck refused
                      settle-stats chain-stats opposed preserving preserved-clashes excepted
                      meta-except-count rule-antecedents rule-contexts negations clashes
                      sib-exc-dirty supersessions qcn qcn-joined matches closures
                      scoped-defeats vantage-disagreements withdrawn])

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

(defn clash-readings
  "`kb`'s `:clash-readings` atom."
  {:inline (fn [kb] `(:clash-readings (deref (:reasoning ~kb))))}
  [kb]
  (:clash-readings @(:reasoning kb)))

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

(defn opposed
  "`kb`'s `:opposed` atom."
  {:inline (fn [kb] `(:opposed (deref (:reasoning ~kb))))}
  [kb]
  (:opposed @(:reasoning kb)))

(defn preserving
  "`kb`'s `:preserving` atom."
  {:inline (fn [kb] `(:preserving (deref (:reasoning ~kb))))}
  [kb]
  (:preserving @(:reasoning kb)))

(defn preserved-clashes
  "`kb`'s `:preserved-clashes` atom."
  {:inline (fn [kb] `(:preserved-clashes (deref (:reasoning ~kb))))}
  [kb]
  (:preserved-clashes @(:reasoning kb)))

(defn excepted
  "`kb`'s `:excepted` atom."
  {:inline (fn [kb] `(:excepted (deref (:reasoning ~kb))))}
  [kb]
  (:excepted @(:reasoning kb)))

(defn scoped-defeats
  "`kb`'s `:scoped-defeats` atom."
  {:inline (fn [kb] `(:scoped-defeats (deref (:reasoning ~kb))))}
  [kb]
  (:scoped-defeats @(:reasoning kb)))

(defn vantage-disagreements
  "`kb`'s `:vantage-disagreements` atom."
  {:inline (fn [kb] `(:vantage-disagreements (deref (:reasoning ~kb))))}
  [kb]
  (:vantage-disagreements @(:reasoning kb)))

(defn withdrawn
  "`kb`'s `:withdrawn` atom."
  {:inline (fn [kb] `(:withdrawn (deref (:reasoning ~kb))))}
  [kb]
  (:withdrawn @(:reasoning kb)))

(defn meta-except-count
  "`kb`'s `:meta-except-count` atom."
  {:inline (fn [kb] `(:meta-except-count (deref (:reasoning ~kb))))}
  [kb]
  (:meta-except-count @(:reasoning kb)))

(defn rule-antecedents
  "`kb`'s `:rule-antecedents` atom."
  {:inline (fn [kb] `(:rule-antecedents (deref (:reasoning ~kb))))}
  [kb]
  (:rule-antecedents @(:reasoning kb)))

(defn rule-contexts
  "`kb`'s `:rule-contexts` atom."
  {:inline (fn [kb] `(:rule-contexts (deref (:reasoning ~kb))))}
  [kb]
  (:rule-contexts @(:reasoning kb)))

(defn negations
  "`kb`'s `:negations` atom."
  {:inline (fn [kb] `(:negations (deref (:reasoning ~kb))))}
  [kb]
  (:negations @(:reasoning kb)))

(defn clashes
  "`kb`'s `:clashes` atom."
  {:inline (fn [kb] `(:clashes (deref (:reasoning ~kb))))}
  [kb]
  (:clashes @(:reasoning kb)))

(defn sib-exc-dirty
  "`kb`'s `:sib-exc-dirty` atom."
  {:inline (fn [kb] `(:sib-exc-dirty (deref (:reasoning ~kb))))}
  [kb]
  (:sib-exc-dirty @(:reasoning kb)))

(defn supersessions
  "`kb`'s `:supersessions` atom."
  {:inline (fn [kb] `(:supersessions (deref (:reasoning ~kb))))}
  [kb]
  (:supersessions @(:reasoning kb)))

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
