;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii.adjudication
  "Koinii adjudication — the DEFAULT policy: leave-open-and-notify, plus the
  lifecycle that keeps disputes from piling up, plus the two escalations (a named
  arbiter's ruling, and a counted majority).  A thin CLIENT
  wrapper over the dispute reads (`vaelii.koinii.dispute`) — it touches no
  engine internals and changes belief only through ordinary asserts / retracts.

  koinii's first answer to a disagreement is NOT to pick a winner.  When two agents
  assert P and ¬P at `:default`, the KB stays **paraconsistent** — both coexist, `argue`
  reports `:contradiction` (Priest's LP) — and this layer just records the dispute open,
  pushes it to whoever is watching, and manages its life.  Automatic resolution by source
  trust is a harder, engine-side policy; do not reach for it here.

  Three policies, one default (koinii.md, *Adjudication: split by policy*), and all three
  are here:

  - **Leave-open-and-notify** *(the default)* — record open, notify, change no
    belief.  Correct for a ground truth people curate.
  - **Arbiter escalation** — a designated arbiter's ruling is an
    ordinary `:monotonic` assertion of the upheld side; its strength defeats the losing
    `:default` side, so the clash clears, `why` explains who ruled, and retracting the
    ruling reopens the dispute (cascading).
  - **Majority vote** — the ballots cast on the disputed claim are counted and the side
    with strictly more is upheld, through that same reversible ruling; a tie upholds
    nothing, so an evenly-split house stays open.

  **Trust-resolve** — automatic resolution by source trust — is out of scope for this
  layer: it is engine-side reputation work, and reaching for it here would resolve
  disagreements by weighing spoofable identities.

  The dispute module owns the reads, the state vocabulary, and the dispute id; THIS module owns the policy
  the dispute module deliberately left out — the **clock**, the **timeout**, and the **notify sinks**.  The
  clock is the engine clock (`v/*clock*`), so a lifecycle time and its assertion's
  `:created` provenance agree.

  Additive, like the sibling koinii modules: only the public core API — including
  `sort-by-content` for the two content orders it reports (`contested-premises`,
  `standing-rulings`) — plus koinii `dispute`, `identity` and `types`.  Nothing in core loads it."
  (:require [vaelii.core :as v]
            [vaelii.koinii.dispute :as d]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.types :as koinii-types]))

;; ---- the policy extension points the dispute module left to the caller --------------

(def ^:dynamic *timeout-ms*
  "How long a dispute may stay live with no ruling before `sweep-stale` flags it (and
  re-surfaces it to a human).  A judgement call — a curated ground truth wants it long
  enough that a real disagreement is not swept before anyone looks.  Default 24h."
  (* 24 60 60 1000))

(def ^:dynamic *notify-sink*
  "Where a newly-opened dispute is pushed: `(fn [dispute-entry] …)`, called once per
  dispute as it transitions `open -> notified`.  This is the extension point the channel's feed
  subscribers and a configured human sink wire into; nil ships no push (the
  lifecycle mark is still recorded, so nothing is lost — a later `notify-disputes` with a
  sink still finds it un-pushed only if the mark was cleared).  Idempotency does not live
  here — it lives in the stored mark — so a sink need not dedupe."
  nil)

(def ^:dynamic *stale-sink*
  "The operator sink for `sweep-stale`: `(fn [dispute-entry] …)`, called once per dispute
  swept to `:stale`.  An aged-out dispute is re-surfaced to a human, never silently
  dropped.  nil ships no push."
  nil)

(defn- now
  "The current time from the engine clock (`v/*clock*`), so a lifecycle timestamp and the
  `:created` provenance of the assertion recording it agree.  Bind `v/*clock*` in a test to
  fix it."
  []
  (v/*clock*))

;; ---- notify: open -> notified, pushed once -------------------------------

(defn notify-disputes
  "The default policy's core move: announce every not-yet-announced dispute `channel`
  observes and record it `notified`.  For each `:open` dispute (`pending-disputes`), record
  a `notified` mark (`open -> notified`) and push the entry to `*notify-sink*`.  Changes NO
  belief: both sides stay believed at `:default`.  **Fires once per dispute**: the stored mark
  is the idempotency key, so a redelivery or a catch-up re-run does not re-push it.  Returns
  the disputes newly notified."
  [kb channel]
  (koinii-types/needs-kb! `notify-disputes kb)
  (let [pending (d/pending-disputes kb channel)]
    (doseq [entry pending]
      (d/mark-notified kb (:dispute-id entry) (now))
      (when *notify-sink* (*notify-sink* entry)))
    pending))

;; ---- the stale sweep: bound the accumulation -----------------------------

(defn- support-handles
  "The handles a stored conclusion `handle` transitively rests on: every node of its `why`
  graph except the conclusion itself."
  [kb handle]
  (disj (set (keys (:nodes (v/why kb handle)))) handle))

(defn- opened-at
  "When the dispute over the sides at `handles` arose: the latest `:created` time among
  them and everything they rest on.  A **derived** side carries no provenance of its own, so its
  creation times are its premises': an emergent clash (two rules concluding `S` and `¬S`)
  arose when the last of those premises landed.  0 if nothing in the closure carries a
  `:created` time, so the sweep surfaces such a dispute instead of hiding it."
  [kb handles]
  (reduce max 0 (keep #(:created (v/provenance kb %))
                      (into (set handles) (mapcat #(support-handles kb %)) handles))))

(defn sweep-stale
  "Sweep every dispute `channel` observes that has stayed live past `*timeout-ms*` with no
  ruling to `:stale`, pushing each to `*stale-sink*`.  A stale dispute is STILL live (both
  sides coexist, `argue` still reports `:contradiction`); `:stale` flags that it aged out
  unaddressed.  Idempotent.  Returns the disputes swept.  **One whole-KB scan for the
  sweep**: the skip reads the stored `:stale` mark (`dispute/stale?`), since every entry
  `disputes-in` hands back is live and `dispute-state` would re-scan per entry."
  [kb channel]
  (koinii-types/needs-kb! `sweep-stale kb)
  (let [cutoff (- (now) *timeout-ms*)
        swept  (filterv (fn [e]
                          (and (not (d/stale? kb (:dispute-id e)))
                               (< (opened-at kb (:handles e)) cutoff)))
                        (d/disputes-in kb channel))]
    (doseq [e swept]
      (d/mark-stale kb (:dispute-id e) (now) 'TimedOut)
      (when *stale-sink* (*stale-sink* e)))
    swept))

(defn poll
  "One driver tick over `channel`: notify the fresh disputes, then sweep the aged ones.
  Returns `{:notified [...] :stale [...]}`.  A subscribe loop or a timer calls
  this; the two halves are also usable apart."
  [kb channel]
  (koinii-types/needs-kb! `poll kb)
  {:notified (notify-disputes kb channel)
   :stale    (sweep-stale kb channel)})

;; ---- arbiter escalation: a reversible ruling that clears the clash -------

(defn who-ruled
  "Read a ruling off its handle: `{:arbiter :dispute-ids :at}` from the provenance `rule`
  recorded, or nil if `ruling-handle` is not an adjudication assertion.  `:dispute-ids` is a
  **set**: canonical dedup gives one sentex per (sentence, context), so an arbiter who rules
  two disputes the same way records an adjudication on one handle twice, and a single-valued
  tag would leave the earlier dispute with no standing ruling and let a second monotonic
  ruling land beside the first (a `:conflict` no ruling can settle)."
  [kb ruling-handle]
  (koinii-types/needs-kb! `who-ruled kb)
  (let [p (v/provenance kb ruling-handle)]
    (when-let [dids (:adjudication p)]
      {:arbiter (:creator p) :dispute-ids (set dids) :at (:created p)})))

(defn standing-rulings
  "The rulings `arbiter` currently holds on dispute `id`: the handles in the arbiter's own
  context whose provenance `rule` tagged with `id`.  **Believed rulings only**
  (`{:believed? true}`), since `rule`'s caller retracts what this returns and a defeated
  ruling must not be withdrawn twice.  Ranked by the ruling's **sentence** with
  `v/sort-by-content`, not by handle (assertion order would make `resolve-by-majority`'s
  `:withdrawn` list a fact about how the KB was loaded) and not by a printed key (an ambient
  `*print-*` var could elide two rulings to one key; a ruling of 9 precedes one of 10).
  Canonical dedup gives one sentex per (sentence, context), so the sentence is a total
  order."
  [kb arbiter id]
  (koinii-types/needs-kb! `standing-rulings kb)
  (let [k (d/dispute-key id)]
    (into [] (comp (map :id)
                   (filter #(contains? (:dispute-ids (who-ruled kb %)) k))
                   (distinct))
          (v/sort-by-content v/sentence-of
                             (v/sentexes-in-context kb (id/context-for arbiter)
                                                    {:believed? true})))))

(defn- sides
  "The stored sentexes dispute `k` names, believed or not: each record of a sentence in
  `both`, a canonical sentence and its negation, whose digest is in `k`, and the sides of
  the live clash `k` names when that finds fewer than `k` holds (a definitional clash)."
  [kb k both]
  (let [ds    (set (if (sequential? k) k [k]))
        names (into [] (comp (filter symbol?) (remove #{'not}) (distinct)) (tree-seq sequential? seq (seq both)))
        cands (filterv #(both (v/sentence-of %)) (v/find-sentexes-all kb names))
        found (into #{} (keep-indexed #(when (ds %2) (cands %1)))
                    (v/digests kb (mapv :id cands)))]
    (if (<= (count ds) (count found))
      found
      (into found (comp (filter #(= k (d/dispute-id kb %))) (mapcat :handles)
                        (keep #(v/sentex kb %)))
            (concat (v/contradictions kb nil {:grounds? false})
                    (v/conflicts kb {:grounds? false}))))))

(defn rule
  "Arbiter escalation: `arbiter` (an agent id, e.g. `AgentArbiter`) rules dispute `id` within
  `channel` for `upheld`, a side or its negation; any other is refused `:koinii/not-a-side`.

  The ruling is an ordinary assertion: `upheld` at `:monotonic` strength in the arbiter's OWN
  context (`id/context-for`), lifted under `channel`, with creator `arbiter` and tagged
  `:adjudication id` in provenance.  Monotonic strength defeats the losing `:default` side,
  so the dispute reads `:resolved` and `argue` collapses to `:true`/`:false`.

  **One ruling per arbiter per dispute**: a ruling for the *other* side is retracted first;
  ruling the same side again is a belief no-op that returns the standing handle.
  **Reversible**: retracting the returned handle reopens the dispute through the JTMS.  The
  open/notified/stale marks are cleared once the ruling has LANDED, so a reopen re-notifies;
  a REFUSED ruling clears nothing.  Returns the ruling handle.  It resolves a `:default`
  coexisting dilemma only: a `:monotonic` `:conflict` needs a human to retract a premise.

  **An arbiter who is a party to the dispute is refused** (`:arbiter-is-party`): the
  arbiter's context already holds one of the two sentences, so ruling their own way would
  re-record their claim and ruling the other way would *retract* it, deleting the claim
  instead of settling the dispute."
  [kb arbiter id upheld channel]
  (koinii-types/needs-kb! `rule kb)
  (let [actx (id/context-for arbiter)
        k    (d/dispute-key id)
        s    (v/sentence-of (v/canonical-sentex kb upheld actx))
        both #{s (if (= 'not (first s)) (second s) (list 'not s))}
        held (sides kb k both)
        ;; the arbiter's own *claims*, which make them a party: the sentexes their context
        ;; BELIEVES, less their own rulings, which this call may supersede.  A defeated
        ;; claim is not a side they hold (docs/koinii.md, "Disputes and adjudication").
        mine (into #{} (comp (remove #(who-ruled kb (:id %))) (map v/sentence-of))
                   (v/sentexes-in-context kb actx {:believed? true}))]
    ;; a sentence `assert` refuses is left to `edit!` below, which throws assert's `:type`
    (when (and (not-any? #(both (v/sentence-of %)) held) (empty? (v/check kb upheld actx)))
      (throw (ex-info (str "koinii: neither " (pr-str s) " nor its negation is a side of dispute "
                           (pr-str k) " — no stored sentex of either has a digest in the id, and"
                           " no live clash carries the id.  A side respelled since the id was"
                           " read has a new digest; read the id again from `disputes-in`")
                      {:type :koinii/not-a-side :upheld upheld :dispute-id k})))
    (when (some #(contains? mine (v/sentence-of %)) held)
      (throw (ex-info (str "koinii: " arbiter " is a party to dispute " (pr-str k)
                           " — an arbiter's ruling lands in the arbiter's own context, so"
                           " ruling a dispute they hold a side of would re-record or retract"
                           " their own claim rather than settle the clash.  Name an arbiter who holds no"
                           " side of it")
                      {:type :arbiter-is-party :arbiter arbiter :dispute-id k})))
    (v/assert kb (list 'genlCx channel actx) 'CxUniverse {:strength :monotonic})
    (let [same    (v/handle-of kb upheld actx)
          stale   (remove #{same} (standing-rulings kb arbiter id))
          ;; the tag is a set, and this handle may already carry other disputes' ids —
          ;; ruling one must not un-rule another that dedups onto the same sentex
          carried (when same (:dispute-ids (who-ruled kb same)))
          ;; one settle: the replacement lands before the displaced ruling goes, so a
          ;; throw between them cannot leave the arbiter having retracted a ruling and
          ;; asserted nothing (`edit!` adds first, then removes)
          res     (v/edit! kb {:add    [[upheld actx {:strength :monotonic :creator arbiter
                                                      :provenance {:adjudication
                                                                   (conj (set carried) k)}}]]
                               :remove (vec stale)})]
      ;; the lifecycle episode ends only once the ruling has LANDED.  `edit!` refuses an
      ;; inadmissible replacement by throwing, and clearing the marks first would leave the
      ;; dispute reopened and un-notified with nothing ruled on it — the driver then
      ;; re-announcing a clash whose ruling never happened.
      (d/reopen! kb id)                                  ; end the lifecycle episode
      (first (:added res)))))

;; ---- a second resolution policy: majority vote ---------------------------
;;
;; Arbiter escalation upholds whatever ONE authority decrees; this upholds whatever a
;; MAJORITY of cast ballots does — and upholds NOTHING on a tie, so an
;; evenly-split house stays open rather than being decided by fiat.  A ballot is a
;; meta-sentex on the disputed claim (`channel/vote` casts it — `(votesFor voter
;; (sentexHandle claim))` / `(votesAgainst …)`, knowledge like every other move), so `why`
;; explains a decision as "the majority voted, here are the ballots."  The decision itself
;; REUSES `rule` — a reversible monotonic assertion — so retracting it reopens the dispute
;; exactly as an arbiter ruling does; the only differences are who is recorded as deciding
;; (`majority-arbiter`) and that a tie decides nobody.
;;
;; The count only becomes a ruling under the `:proof-tier` identity policy, and only over
;; ballots an in-process `identity/ingest` attested (`cast-ballot`).  Counting (`tally`)
;; stays open for transparency.

(def majority-arbiter
  "The principal recorded as ruler of a majority-vote resolution — not a real agent but
  the stand-in 'the house majority', so `who-ruled` tells a counted vote apart from a named
  arbiter's decree."
  'AgentMajority)

(def ^:private ballot-predicates {:for 'votesFor :against 'votesAgainst})

(defn cast-ballot
  "Cast `principal`'s `stance` (`:for` / `:against`) ballot on the claim at
  `claim-handle` through `identity/ingest`: `(votesFor id (sentexHandle claim))` in the
  principal's own context, attested when `principal` is a `:proof-tier` one
  `authenticate` minted.  The in-process ballot `resolve-by-majority` counts;
  `channel/vote` writes the same sentence unattested.  An unknown stance is refused
  (`:koinii/no-such-stance`).  Returns the ballot's handle."
  [kb principal stance claim-handle]
  (koinii-types/needs-kb! `cast-ballot kb)
  (let [pred (or (ballot-predicates stance)
                 (throw (ex-info (str "koinii: no such ballot stance " (pr-str stance)
                                      " — a vote is cast :for or :against")
                                 {:type :koinii/no-such-stance :stance stance
                                  :known [:for :against]})))]
    (id/ingest kb principal (list pred (:id principal) (v/sentex-handle claim-handle)))))

(defn- ballots
  "The believed ballot sentexes on the claim at `claim-handle` for `stance`, matched in any
  context (`?ctx`): a ballot names the globally-unique claim handle, and a channel read
  would miss ballots in the voters' own contexts."
  [kb claim-handle stance]
  (v/sentexes-matching kb (list (ballot-predicates stance) '?a (v/sentex-handle claim-handle))
                       '?ctx))

(defn- proven-voter?
  "Does `ballot` prove its voter: stored in the voter's own context (`identity/context-for`),
  and carrying an attestation naming the voter (`identity/attested-by`) or a `:principal`
  the daemon recorded from the voter's token-table grant (docs/operations.md, the token
  table)?"
  [kb ballot]
  (let [voter (second (:sentence ballot))]
    (and (= (:context ballot) (id/context-for voter))
         (or (= voter (id/attested-by kb (:id ballot)))
             (= voter (:principal (v/provenance kb (:id ballot))))))))

(defn tally
  "Count the ballots cast on the claim at `claim-handle`: `{:for n :against n}`, each a
  count of DISTINCT voters (`ballots`).

  A voter who cast BOTH stances (without retracting the first, against `vote`'s contract)
  has SPOILED their ballot — counted on neither side — so one self-contradicting voter can
  neither manufacture a tie nor swing a majority; their confusion abstains rather than
  double-voting."
  [kb claim-handle]
  (koinii-types/needs-kb! `tally kb)
  (let [who (fn [stance] (into #{} (map (comp second :sentence)) (ballots kb claim-handle stance)))
        yes (who :for) no (who :against)]
    {:for (count (remove no yes)) :against (count (remove yes no))}))

(defn resolve-by-majority
  "Resolve dispute `id` over the claim at `claim-handle` by MAJORITY VOTE, within `channel`.
  Count the ballots (`tally`); if one side has strictly more, uphold it as a reversible
  ruling (`rule`, arbiter `majority-arbiter`): the claim for a `:for` majority, its negation
  for `:against`.  **A tie upholds nothing**: the dispute stays open.

  **The count is the authority, every time**: a ruling that no longer matches the count is
  withdrawn before the new one lands, so a swing retracts the standing ruling and rules the
  other side, and a majority that dissolves into a tie retracts it and leaves the dispute
  open.  Returns `{:for n :against n :outcome :for/:against/:tie :ruling handle-or-nil
  :withdrawn [handle …]}`.  Idempotent: re-running on an unchanged count withdraws nothing,
  so a driver may poll it.

  **Requires the `:proof-tier` identity policy, and a proven voter on every ballot.**  A
  count by claimed voter name is spoofable, so this refuses (`:koinii/identity-unverified`)
  under any other policy, and when any ballot on the claim, spoiled ones included, proves no
  voter (`proven-voter?`), naming them in `:unattested`.  `cast-ballot` under a minted
  `:proof-tier` principal attests one, and a daemon with a token table records the
  `:principal` of a wire ballot (docs/koinii.md, *Identity and the write boundary*).  `tally`
  is unrestricted."
  [kb id claim-handle channel]
  (koinii-types/needs-kb! `resolve-by-majority kb)
  (when-not (= :proof-tier id/*policy*)
    (throw (ex-info (str "koinii: majority resolution requires the :proof-tier identity "
                         "policy; under " (pr-str id/*policy*) " the ballot count is "
                         "spoofable and must not produce a defeating ruling")
                    {:type :koinii/identity-unverified :policy id/*policy*
                     :resolution :majority :dispute id})))
  (let [unattested (into #{}
                         (comp (mapcat #(ballots kb claim-handle %))
                               (remove #(proven-voter? kb %))
                               (map :id))
                         [:for :against])]
    (when (seq unattested)
      (throw (ex-info (str "koinii: majority resolution refused — " (count unattested)
                           " ballot(s) on the claim sit outside their voter's own context or"
                           " carry no attestation and no daemon-recorded principal naming"
                           " their voter, so the count"
                           " includes names nobody proved.  Cast ballots with cast-ballot"
                           " under a :proof-tier principal, or over a daemon holding a"
                           " token table, and retract the ones in :unattested")
                      {:type :koinii/identity-unverified :policy :proof-tier
                       :resolution :majority :dispute id :unattested unattested}))))
  (let [{yes :for no :against :as counts} (tally kb claim-handle)
        claim    (v/sentence-of (v/sentex kb claim-handle))
        standing (standing-rulings kb majority-arbiter id)
        decide   (fn [outcome upheld]
                   (let [h (rule kb majority-arbiter id upheld channel)]
                     (assoc counts :outcome outcome :ruling h
                            :withdrawn (filterv #(not= h %) standing))))]
    (cond
      (> yes no) (decide :for claim)
      (> no yes) (decide :against (list 'not claim))
      :else      (do (doseq [h standing] (v/retract! kb h))
                     (assoc counts :outcome :tie :ruling nil :withdrawn standing)))))

;; ---- does an open dispute block dependent reasoning? no — but make it visible

(defn contested-premises
  "The disputed premises the conclusion `S` rests on in `ctx`: the handles in S's support
  closure that are a side of an open dispute `ctx` observes.  Empty if S rests on nothing
  contested.  A pure read that changes no belief (unlike `quarantine`): an open dispute does
  not block dependent reasoning, so a conclusion resting on a contested premise should be
  *visible as such*.

  **Scoped to the ANCESTOR SET.**  `S` is every believed sentex of `S` in a context `ctx`
  sees (`v/sees?`), the scoping `disputes-in` and `ask?` use: forward chaining places a
  conclusion in the most specific context that sees its premises, an AGENT's context
  rather than the channel's, so an exact-context lookup would answer 'nothing contested' for
  a conclusion built on a disputed claim.  **Every visible derivation**: where more than one
  context holds `S`, their support closures are UNIONED, so no tie-break depends on seq
  order or handles.  **Belief-filtered**: a defeated stored sentex holds up no answer.
  **Content-ordered** by the premise's `[sentence context]` (`v/sort-by-content`); the
  context is required since the union can hold one sentence in two agents' contexts."
  [kb S ctx]
  (koinii-types/needs-kb! `contested-premises kb)
  ;; the ancestor set filter runs before `disputes-in`, which computes whole-KB contradictions:
  ;; a conclusion `ctx` cannot see costs one index probe rather than that.
  (let [visible (filterv #(v/sees? kb ctx (:context %)) (v/sentexes-matching kb S '?ctx))]
    (if (seq visible)
      (let [contested (into #{} (mapcat :handles) (d/disputes-in kb ctx))
            support   (into #{} (mapcat #(support-handles kb (:id %))) visible)]
        (v/sort-by-content #(let [sx (v/sentex kb %)] [(v/sentence-of sx) (:context sx)])
                           (filterv contested support)))
      [])))

(defn rests-on-contested?
  "Does the conclusion `S`, as `ctx` sees it, rest on any premise that is currently disputed
  there?  The boolean over `contested-premises` — the flag a high-stakes reader checks before
  trusting a derived answer, and it reads `S` up the genlCx ancestor set for exactly that reason: an
  answer `ask?` gives at `ctx` off a premise stored below it is the case a safety flag exists
  to catch, not the case it may miss."
  [kb S ctx]
  (koinii-types/needs-kb! `rests-on-contested? kb)
  (boolean (seq (contested-premises kb S ctx))))

;; ---- quarantine: the OPTION, off by default ------------------------------

(defn quarantine
  "OPTIONAL, off by default: hide the contested sentex `target-handle` from `channel`'s reads
  and derivations, reversibly, via an index-layer `except` asserted in `channel`, for a
  high-stakes channel that must never let a conclusion rest silently on a contested premise.
  Scoped to `channel`: the claim stays believed in its OWN context.  It OVER-SUPPRESSES:
  `channel` can no longer see the dispute (`argue` there reads the lone surviving side), and
  `except` interacts with the TMS and contexts.  Prefer `contested-premises` /
  `rests-on-contested?` unless a channel must exclude contested claims from derivation.
  Returns the mask's handle; `unquarantine!` retracts it (cascading derivations back)."
  [kb channel target-handle]
  (koinii-types/needs-kb! `quarantine kb)
  (v/assert kb (list 'except (v/sentex-handle target-handle)) channel {:strength :monotonic}))

(defn unquarantine!
  "Undo a `quarantine`: retract the `except` mask at `handle`, so the claim and anything it
  fed count again in the channel.  Returns `retract!`'s counts."
  [kb handle]
  (koinii-types/needs-kb! `unquarantine! kb)
  (v/retract! kb handle))

(defn quarantined
  "The sentex handles `channel` is currently quarantining — the targets of its
  `(except (sentexHandle ?h))` masks.  'What has this channel screened out' as a plain read."
  [kb channel]
  (koinii-types/needs-kb! `quarantined kb)
  (->> (v/sentexes-matching kb (list 'except '?h) channel)
       (keep (fn [s] (let [t (second (:sentence s))]
                       (when (v/sentex-handle? t) (second t)))))
       vec))
