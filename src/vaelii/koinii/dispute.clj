;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii.dispute
  "Koinii dispute reads: two context-scoped reads over the engine's
  whole-KB contradiction surface, plus the small dispute-STATE surface the
  adjudication driver drives.

  The engine *represents* contradiction but answers it only whole-KB: `contradictions`
  and `conflicts` each scan the whole store and hand back entries whose sides carry
  their own `:context`.  A subscriber wants the per-channel question — 'is there an open
  dispute *here*?' — so that scoping lives in one wrapper rather than being re-derived at
  every call site.

  **'Disputed' is a precise word.**  It is NOT 'false' and NOT 'defeated-by-strength'.
  A dispute is a *coexisting* clash — S and ¬S both believed with no strength winner, so
  `argue` returns `:contradiction` and the engine deliberately leaves both standing
  (paraconsistent tolerance — Priest's LP, the four-valued `argue`).  A clean
  strength-defeat (a `:monotonic` premise beating a `:default` one) is the opposite: the
  loser is `:defeated`, `argue` returns `:false`, and that is *resolved*, not disputed.

  Two error classes, kept distinct, never merged:

  - **`:contradiction`** — a coexisting `:default` dilemma (a rebuttal, or a definitional
    clash left at equal strength).  Both sides believed; `argue` -> `:contradiction`.
  - **`:conflict`** — an irreducible clash among `:monotonic` content: two things asserted
    known-true that cannot both hold, which the engine has no grounds to prefer.  Harder
    than a rebuttal, and a caller usually wants to see it alongside.

  **Detection matches the engine, not the intuition.**  A coexisting dilemma keeps BOTH
  sides believed, so `why-not` reports `:believed? true` on either — it never reads
  `:defeated` there (that reason is reserved for the strength-defeat, i.e. the resolved
  case).  So the named-sentence read is `argue`, whose `:contradiction` verdict is exactly
  'both provable, neither strength-wins' and whose context scoping is exactly 'the asker
  sees both sides'.  `argue` is per-sentence and never computes whole-KB contradictions,
  which is the perf property the hot path needs.

  This module owns the *reads*, the state *vocabulary*, and the dispute *id*.  The clock,
  the timeout value, and the notify sink are the driver's.  So the
  recording functions here take the timestamp (and stale reason) from the caller rather
  than reading a clock: this module supplies the mechanism, the driver supplies the policy.

  Additive, like the sibling koinii modules: only the public core API (`argue`,
  `canonical-sentex`, `digests`) — nothing under `vaelii.impl`, and nothing in core
  loads it."
  (:require [vaelii.core :as v]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.types :as koinii-types]))

;; ---- the dispute id: a stable name for one clash -------------------------

(defn dispute-id
  "The stable id of a dispute `entry` (from `disputes-in`, `contradictions`, or
  `conflicts`): the content digests (`v/digests`) of its side `:handles`, sorted.  A seat
  holding the clash at other handles computes the same id, and the side order the engine
  reported does not change it.  The id is the key the driver attaches lifecycle state to.

  Two digests for a rebuttal and three for an `anti_transitive` chain: a nogood is a *set*
  and the engine reports it whole (docs/nmtms.md), so this reads `:handles` rather than
  destructuring it as a pair."
  [kb entry]
  (koinii-types/needs-kb! `dispute-id kb)
  (vec (sort (v/digests kb (:handles entry)))))

(defn dispute-key
  "`id` in the ONE spelling every reader compares — the sorted digest vector `dispute-id`
  builds.  The single home for that sort, and the reason there is one: a caller may hold
  the digests in either order (`dispute-id` sorts, but its contract accepts any digest
  seq and `disputes-in` hands the entries out), and a mark or a provenance tag written
  under one order is invisible to a read for the other — a standing ruling no guard
  can see.  A non-sequential id passes through unchanged."
  [id]
  (if (sequential? id) (vec (sort id)) id))

(defn dispute-term
  "The structural term naming a dispute by its id, for the stored lifecycle marks:
  `(DisputeFn \"sha256:…\" …)`, digests sorted (`dispute-key`) so the term is a function
  of the clash and not of argument order, and names no handle.  `id` is a `dispute-id`.

  **As many digests as the clash has**, never the first two.  A nogood is a *set* and
  `anti_transitive` forms one over three sentexes (docs/nmtms.md), so `disputes-in` hands
  back three-handle entries — and a term keyed on a pair would name two different
  three-member disputes identically whenever they shared their two lowest digests, and
  name a three-member one the same as the pair over those two.  The marks this term keys
  are the notify and stale sweeps' idempotency key, so a collision is a dispute silently
  never announced."
  [id]
  (let [k (dispute-key id)]
    (list* 'DisputeFn (if (sequential? k) k [k]))))

;; ---- disputes-in: the whole surface, scoped to what a context sees -------

(defn- observed-by?
  "Does `ctx` observe the clash `entry` — i.e. can it read BOTH clashing sides?  A
  contradiction is visible exactly where both its sentences are readable, up the
  `genlCx` ancestor set (`sees?`).  So a clash between `(ist CxAtlas P)` and `(ist CxBoreas ¬P)`
  surfaces in the channel `CxDeploy` (which sees both agent contexts) and NOT in a
  sibling that sees only one — from a one-sided vantage there is no clash to see, and
  `argue` from there returns `:true`, not `:contradiction`.  Both-sides is what keeps the
  named read (`disputed?`, `argue`-based) and this whole-surface read agreeing."
  [kb ctx entry]
  (every? (fn [side] (v/sees? kb ctx (:context side))) (:sides entry)))

(defn disputes-in
  "The disputes a context `ctx` observes: every `contradictions` and `conflicts` entry
  both of whose sides `ctx` sees, each tagged with its `:dispute-class`
  (`:contradiction` — a coexisting `:default` dilemma / `:conflict` — a `:monotonic`
  irreducible clash) and its stable `:dispute-id`.  The engine entry's own `:kind`
  (`:disjoint` / `:functional` / `:asymmetric` / `:anti-transitive`, nil for a plain
  rebuttal) rides along unchanged.

  This is the per-channel reading the whole-KB `contradictions` cannot give: 'what is
  disputed *here*'.  It hides nothing and invents nothing — the union of `disputes-in`
  over every context equals `(contradictions kb)` + `(conflicts kb)`, because the
  common-descendant context that raised each clash sees both of its sides and so reports
  it.  Conflicts are folded in by default (most callers want the harder monotonic clashes
  beside the rebuttals); a caller wanting only one class filters on `:dispute-class`."
  [kb ctx]
  (koinii-types/needs-kb! `disputes-in kb)
  (->> (concat (map #(assoc % :dispute-class :contradiction) (v/contradictions kb))
               (map #(assoc % :dispute-class :conflict)      (v/conflicts kb)))
       (filter #(observed-by? kb ctx %))
       (mapv   #(assoc % :dispute-id (dispute-id kb %)))))

;; ---- disputed?: the per-sentence hot path, and the thin any-path ---------

(defn disputed?
  "Is there an open dispute?  Two arities:

  - **`(disputed? kb ctx)`** — is *anything* disputed in `ctx`?  `disputes-in`'s two clash
    reads without grounds, the conflicts read only when `ctx` observes no contradiction.

  - **`(disputed? kb S ctx)` / `(disputed? kb S ctx opts)`** — is the named sentence `S`
    disputed in `ctx`?  THE HOT PATH: a scoped `argue` read, which never computes whole-KB
    contradictions (subscribers call it in a loop, so that is a perf property, not a
    nicety).  `S` is disputed exactly when `argue` returns `:contradiction` — S and ¬S
    both provable from `ctx` with no strength winner — which is a coexisting `:default`
    dilemma OR a `:monotonic` conflict, but NOT a clean strength-defeat (that returns
    `:false`: resolved, not disputed).  `opts` (e.g. `{:max-depth n}`) is passed to
    `argue`; without it `argue` uses `ask?` — ground facts and provers, no rule expansion —
    which is what a koinii dispute (an asserted `¬S`) needs.

  Arity tells the two apart: 2 args is `(kb ctx)`, 3+ is `(kb S ctx …)`."
  ([kb ctx]
   (koinii-types/needs-kb! `disputed? kb)
   (boolean (or (some #(observed-by? kb ctx %) (v/contradictions kb nil {:grounds? false}))
                (some #(observed-by? kb ctx %) (v/conflicts kb {:grounds? false})))))
  ([kb S ctx] (disputed? kb S ctx nil))
  ([kb S ctx opts]
   (koinii-types/needs-kb! `disputed? kb)
   (= :contradiction (:verdict (v/argue kb S ctx opts)))))

;; ---- the dispute lifecycle (koinii design D9) ----------------------------
;;
;; open -> notified -> resolved, with a stale sweep for the un-ruled.  Two of the four
;; states are DERIVED from current belief (`:open`, `:resolved`) and two are STORED as
;; ordinary assertions (`:notified`, `:stale`) — stored so `why` explains them and
;; retracting one reopens the dispute.  This module records and reads them; the driver decides
;; WHEN (the clock, the timeout, the notify sink).

(def state-context
  "The coordination context the stored lifecycle marks (`:notified`, `:stale`) live in.
  A dispute id is globally unique within the KB (a digest vector), so one well-known place
  to look suffices; the marks are bookkeeping, not channel knowledge, so they sit apart
  from the channels' own reasoning."
  'CxDisputes)

(def ^:private state-declaration
  "The one sentence of koinii's `CxDisputes` seed that `ensure-state-context!` reads to
  decide whether the seed is stored in a KB."
  '(ternary_predicate disputeStale))

(defn- ensure-state-context!
  "Load koinii's `CxDisputes` seed (`resources/kb/koinii/CxDisputes.txt`) into `kb` unless it
  is already stored there.  The seed places `CxDisputes` under `CxUniverse` and declares the two
  marks and the `DisputeFn` term they carry, so the arity check reads a declaration where
  every mark is stored.  `identity/load-registry` and `speech-acts/load-speech-acts` load
  the seed as well; the two writes call this for a KB that ran neither."
  [kb]
  (when-not (v/handle-of kb state-declaration state-context)
    (id/load-seed-context kb state-context)))

(defn- marks-of
  "The stored lifecycle mark sentexes for `id` under `pred` (arity per pred), in
  `state-context`."
  [kb pred id args]
  (v/sentexes-matching kb (list* pred (dispute-term id) args) state-context))

(defn notified?
  "Is there a stored `:notified` mark for dispute `id`?"
  [kb id]
  (koinii-types/needs-kb! `notified? kb)
  (boolean (seq (marks-of kb 'disputeNotified id ['?at]))))

(defn stale?
  "Is there a stored `:stale` mark for dispute `id`?"
  [kb id]
  (koinii-types/needs-kb! `stale? kb)
  (boolean (seq (marks-of kb 'disputeStale id ['?at '?reason]))))

(defn mark-notified
  "Record that dispute `id` has been pushed to subscribers / a human, at time `at` (the
  caller — the driver — supplies the clock).  An ordinary assertion
  `(disputeNotified (DisputeFn …) at)` in `state-context`, so `why` explains it and a
  retract (`reopen!`) un-notifies.  The mark is what stops the driver re-notifying a clash it
  has already announced.  Returns the mark's handle."
  [kb id at]
  (koinii-types/needs-kb! `mark-notified kb)
  (ensure-state-context! kb)
  (v/assert kb (list 'disputeNotified (dispute-term id) at) state-context))

(defn mark-stale
  "Record that dispute `id` aged out — open past the driver's timeout with no ruling — at time
  `at`, tagged with `reason` (a symbol, e.g. `TimedOut`).  An ordinary assertion
  `(disputeStale (DisputeFn …) at reason)` in `state-context`, so open disputes do not pile
  up unmarked and `why` can explain the sweep.  Staleness does not resolve the clash — the
  dispute is still live — it only flags it.  Returns the mark's handle."
  [kb id at reason]
  (koinii-types/needs-kb! `mark-stale kb)
  (ensure-state-context! kb)
  (v/assert kb (list 'disputeStale (dispute-term id) at reason) state-context))

(defn reopen!
  "Retract every stored `:notified` / `:stale` mark on dispute `id`, returning it to
  `:open` (if the clash is still live).  The inverse of `mark-notified` / `mark-stale`,
  and the reason those states are stored rather than derived: retract the ruling and the
  dispute reopens.  Returns the number of marks retracted."
  [kb id]
  (koinii-types/needs-kb! `reopen! kb)
  ;; the whole mark set is realized BEFORE the first retract.  `marks-of` is a live read
  ;; of the index and `concat` is lazy, so retracting while walking it would run the
  ;; second read against a store the first retracts have already moved — the stale marks
  ;; enumerated against a KB that no longer holds the notified ones.
  (let [marks (into [] (concat (marks-of kb 'disputeNotified id ['?at])
                               (marks-of kb 'disputeStale id ['?at '?reason])))]
    (doseq [sx marks] (v/retract! kb (:id sx)))
    (count marks)))

(defn- live-ids
  "The ids of every clash currently on the whole-KB surface — `contradictions` +
  `conflicts`.  A whole-KB scan; the lifecycle driver is not the hot path (that is the
  named `disputed?`), so this is where the scan is affordable."
  [kb]
  (into #{} (map #(dispute-id kb %)) (concat (v/contradictions kb) (v/conflicts kb))))

(defn- mark-state
  "The state implied by the stored marks alone (`:stale` > `:notified` > `:open`), for a
  clash already known to be live."
  [kb id]
  (cond (stale? kb id)    :stale
        (notified? kb id) :notified
        :else             :open))

(defn dispute-state
  "The lifecycle state of dispute `id`:

  - `:open`     — live, no mark recorded (`disputes-in`/`disputed?` report it, `argue`
                  returns `:contradiction`).  Derived.
  - `:notified` — live, and the driver has recorded a notify mark.  Stored.
  - `:stale`    — live, and the driver has recorded a stale sweep.  Stored.
  - `:resolved` — no longer live: a side was retracted or strength-demoted, the clash is
                  gone and `argue` has collapsed to `:true`/`:false`.  Derived.

  For an `id` obtained from `disputes-in` (the contract), `:resolved` means 'was a
  dispute, now settled'; an id that was never a clash also reads `:resolved` (absent = not
  an open dispute here).  Reading state runs a whole-KB liveness scan — `contradictions`
  plus `conflicts` — so a caller holding entries that are already live by construction
  (everything `disputes-in` hands back) reads the marks instead (`notified?` / `stale?`)
  and pays no scan at all."
  [kb id]
  (koinii-types/needs-kb! `dispute-state kb)
  (if (contains? (live-ids kb) (dispute-key id))
    (mark-state kb id)
    :resolved))

(defn pending-disputes
  "The disputes `ctx` observes that still need announcing — `disputes-in` entries in
  state `:open` (no notify/stale mark yet).  The driver's work-list: the clashes to push.  Each
  entry from `disputes-in` is live by construction, so this checks the marks, not liveness
  again."
  [kb ctx]
  (koinii-types/needs-kb! `pending-disputes kb)
  (filterv #(= :open (mark-state kb (:dispute-id %))) (disputes-in kb ctx)))
