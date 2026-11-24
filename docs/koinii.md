# Koinii: multi-agent coordination over one knowledge base

- **Covers:** the coordination layer that lets independent agents assert, reply, dispute
  and resolve over a **shared** KB — agents as contexts, moves as sentexes, the change
  feed as the medium — and the two deployment shapes it runs in (one single-writer daemon,
  or independently-replicated seats). The design decisions the koinii modules cite by
  number (D1, D3–D9) are tabled here.
- **Not here:** the per-function API — that is in the module docstrings under
  `vaelii.koinii.*`; the change feed the channel rides →
  [feed.md](feed.md); the single-writer daemon and client → [operations.md](operations.md);
  modal belief projection → [belief.md](belief.md); paraconsistent contradiction and
  strength defeat → [nmtms.md](nmtms.md); the `except` mask →
  [exceptions.md](exceptions.md); content-address canonicalization →
  [canonicalization.md](canonicalization.md).
- **Assumes:** sentex, context, `genlCx`, provenance / `:creator`, meta-sentex,
  `target_following_predicate`, the change feed → [glossary.md](glossary.md),
  [contexts.md](contexts.md), [storage.md](storage.md), [feed.md](feed.md).

Koinii is the layer where more than one agent works over one knowledge base — a *shared,
common* store several parties read and write. Its whole claim is that a common-sense KB
**already is** the substrate a
group of agents needs to coordinate — identity, a shared medium, provenance, contradiction
handling, truth maintenance — so coordination is not a new transport bolted on the side but a
small vocabulary and a handful of conventions expressed **in the KB itself**.

It is an **application, not part of the engine**, and the tree says so: koinii lives at
`src/vaelii/koinii/`, beside `impl/` rather than inside it, and requires nothing under
`vaelii.impl` — every module is built on the public core API and the thin `vaelii.client`,
exactly as an outside consumer would be (`public_api_test/koinii-reaches-into-no-impl`
checks it). That is also why it is out of the engine's frozen lists (the API golden, the
SPI protocols, the refusal-type list). Koinii's surface is frozen in a golden of its own,
`test/golden/koinii-surface.edn`: the public vars of `vaelii.koinii.*` with their
arglists, the refusal `:type`s its modules raise, and the arity of each term CxRegistry,
CxSpeechActs and CxDisputes declare. A koinii change moves that file and none of the
engine's, and a removed var, `:type` or term, or a changed arglist or arity, is a
Breaking changelog entry (CONTRIBUTING §3.8).
When koinii needs something the API does not publish, the
answer is to publish it — `sort-by-content` is here for that reason — never to reach past
it.

It is **additive**. Nothing in `vaelii.core` loads it. Load a koinii context explicitly
(`identity/load-registry`, `speech-acts/load-speech-acts`) — the starter walks only
`upper/` and `middle/`, so a KB pays for koinii only when a deployment asks for it.

## The model: agents are contexts, moves are knowledge

Three identifications carry the whole layer. Each reuses a core mechanism rather than adding
one.

- **An agent *is* a context.** Atlas writes into `CxAtlas`; the channel `CxDeploy` sees it
  through `(genlCx CxDeploy CxAtlas)`, so a read of the channel is the union of every agent's
  assertions and a read of `CxAtlas` alone is "everything Atlas said." Because context is
  part of sentex identity, Atlas's `P` and Boreas's `P` are two **distinct** sentexes with
  two creators — first-writer-wins provenance loses no co-source. Identity therefore needs no
  new subsystem: it is the context lattice, and the one enforcement point is "write your own
  context, and nothing else" (`identity/check-write-boundary!`).

- **A move *is* a sentex.** A question, an answer, an endorsement, a dispute — each is a
  fact in the KB, queryable and retractable and auditable like any other, not an out-of-band
  message. A **response** is a *meta-sentex on its target*, naming it by handle
  `(sentexHandle T)`; because it lives on the target, retracting the target sweeps its
  replies with it. This is the property a message bus cannot give (see *Reply is an
  assertion*).

- **The KB *is* the medium.** There is no separate broker. Agents coordinate by writing and
  reading; the live half is the **change feed** ([feed.md](feed.md)) — an agent subscribes
  and is told when belief moves — and the durable half is the store, which persists every
  move so an agent that connects later reads the conversation whether or not its author is
  still online. Decoupled in time by construction: history that predates a subscription is
  recovered by *reading*, not by replay.

The consequence, stated plainly: **the conversation is in the graph, not in the
client.** Who spoke is the sentex's own context and `:creator`; what was said is its
sentence. A client holds no conversation state a fresh reader could not reconstruct from the
KB.

## The deployment shape

Every write funnels through **one single writer**. In the cross-process case that writer is
the daemon ([operations.md](operations.md)), which serializes every assertion through one
monitor. This is not an incidental detail — three properties rest on it, and they are why
koinii ships no logical clocks:

The change-feed cursor delivers a **total order**: every agent reads the same events in the
same sequence, and a reply is a later write than the claim it answers, in the one order every
agent observes. So the happy path is **causally sound by construction** — a reply never
precedes its target in any agent's view. Lamport and vector clocks exist to *rebuild* a
causal order across concurrent writers; with one writer the store order already **is** the
causal order, so a timestamp would be a field nothing reads. (If koinii ever goes
multi-writer — several daemons over sharded KBs — that is when causal metadata becomes load
bearing. Until then it is ceremony. This is decision D7.)

The transport an agent coordinates over is the `Medium` protocol, with two implementations:

- **`wire`** — a daemon connection (`vaelii.client`). The inter-agent case: agents are
  separate processes funnelling every write through the one daemon, and a subscription runs
  the feed's poll loop **off** the agent's own thread. This matters because an in-process
  feed callback runs *on* the writer's thread ([feed.md](feed.md)); one slow agent would
  stall the writer for everyone. Polling off the agent's thread removes that coupling.
  A poll that fails ends the loop and unwatches the daemon's subscription, unless the
  daemon answered `:unknown-subscription`.
- **`local`** — an in-process KB. `subscribe` is a plain `watch` listener, no cursor
  apparatus. The callback runs on the writing thread, so a slow one still slows the writer —
  fine single-process, wrong across agents.

Everything above the protocol — `assert`, the five reply verbs (`answer` / `endorse` /
`justify` / `dispute` / `vote`), `reply-many`, and the recovery reads — runs the same over
either medium. Only `subscribe` differs, because only the feed does.

The rest of koinii takes a KB, not a medium. `dispute`, `adjudication`, `belief`, `deref` and
`identity`'s ingest and registry writes call `vaelii.core` on the KB they are handed, so they
run in the process that holds it — the daemon's, in the `wire` shape. A remote agent moves
through `channel` and catches up through `catchup`; the dispute reads, the notify and stale
sweeps, a ruling, a majority count and a belief projection run beside the daemon. Each public
fn of those modules that takes a KB first refuses a `vaelii.client` connection or a medium in
its place with `:koinii/needs-kb`, naming the fn in `:fn` (`vaelii.koinii.types/needs-kb!`).

### When to stop

`local` is the right shape until the moment agents become **separate processes**. Then `wire`
is mandatory, and the reason is exactly the writer's thread above: separate processes cannot
share an in-process callback, and even if they could, one slow agent stalling the single
writer is a failure the whole deployment feels. The single-writer daemon plus the wire feed
is the structure that scales to N independent agents; the in-process medium is the structure that
keeps a single-process demo simple. Neither is a lesser version of the other — they are the
two answers to "is this one process or many," and the `Medium` protocol is the one
surface that lets everything else not care.

## Identity and the write boundary

The engine deliberately pushes per-caller identity *out*: `*creator*` is an unauthenticated
annotation and the daemon's only auth is one shared bearer token. Koinii's answer is the
context lattice, not a new auth subsystem (decision D8): the destination of an agent's writes
is a **deterministic function of its id** — `AgentAtlas` → `CxAtlas` (`identity/context-for`)
— so "write only your own context" needs no lookup, and a principal can never be routed to a
context that is not its own. The one context every governed agent may *not* write is the
admin-only registry `CxRegistry`: the governed may not write the authority that governs them.

The boundary is checked at **both ends of the edge**. An agent's writes land in its own
context; a *join* grafts that context under a coordination channel, which widens what the
**parent** sees — every ancestor set read of the parent returns the newcomer's claims from then on —
so the parent is held to the same standard the destination is. The registry, the agent's own
context, and any context already placed as an agent's own are refused
(`:koinii/not-a-channel`). A placed context **says so in the KB**: `(agentContext CxAtlas
AgentAtlas)`, written into that context by the one placement every route goes through
(`identity/place-agent-context`), and therefore true of an agent context however it was
placed. It has to be written rather than inferred, because neither the spelling nor the
lattice distinguishes the two — `CxAtlas` and `CxDeploy` are spelled alike, and a placement's
`genlCx` edges are the ordinary wiring of any nested context, so reading the role off them
would make admission depend on what else had landed and in which order. A context nothing has
claimed is admissible: the entry point refuses what a placement told it, not what it could guess.

The **creator** is fixed by the same id, and refused rather than bent: `channel/assert`
records `:creator` as the agent the handle names, and a caller passing a *different*
`:creator` is refused (`:koinii/creator-mismatch`). Neither silent outcome is acceptable —
honouring it lets an agent sign another's name, dropping it leaves a call that looks like
it took — and ownership is required downstream, since `belief/disregard` will only
withdraw a statement whose creator is the withdrawing agent. Passing the agent's own id is
redundant and allowed.

The auth **strength** is conditional on policy (decision D4):

- **Cooperative** (the default) — `*creator*` trusted by convention, the write routed to the
  agent's own context. Correct for a notify-only deployment among trusted agents. State it
  plainly: identity here is **unverified** — `authenticate` trusts the claimed id with no
  proof, so it defends fat-fingers, not attackers.
- **Proof-tier** — required the moment trust-resolve is enabled, because trust-weighting a
  spoofable identity is worse than no trust. `authenticate` verifies a credential through the
  `verify-fn` extension point (sign-at-ingest, an authenticating proxy, A2A AgentCards / DIDs) and
  **refuses** an unverified request; a nil verifier fails *closed*. `identity/ingest` under
  the principal it mints **attests** each write: provenance gets `:attestation`, an
  HMAC-SHA256 over creator, handle, stored sentence and context. `identity/attested-by` reads
  it back, and the MAC fails on any other sentex, including the same sentence re-asserted
  under a new handle. A rebase gives each fork write a new handle, and the sentence of one
  naming a base record by handle changes with it. `deref/pull!` rebases through
  `identity/rebase!`, which seals the MAC again over the new handle and sentence for each
  write whose attestation verified for its handle before the rebase, under the current key.
  A stopped rebase leaves its writes in the fork's directory with the record each was
  captured from, and the next `identity/rebase!` seals them again as it seals its own. The
  writes an `open-kb` asserts again after a rebase stopped are sealed by no one and read
  unattested ([overlay.md](overlay.md#replacing-the-base)).

**Proof-tier attestation is in-process only.** `authenticate`, `ingest` and the
attestation run in the process that holds the KB and the key, and nothing on the wire calls
them. The refusals `channel` raises (`:koinii/registry-forbidden`,
`:koinii/creator-mismatch`, `:koinii/speaker-mismatch`) are thrown in the caller's process
before anything is sent, so a client that does not go through `channel` meets none of them.

**On the wire the daemon's token table is the write boundary**
([operations.md](operations.md#the-token-table)). The deployment gives each agent a token
whose grant names the agent id as `:principal` and the agent's own context as `:writes`,
built with `identity/context-for` — `{"<token>" {:principal AgentAtlas :writes
#{CxAtlas}}}` — and gives the operator an `:admin? true` token. The daemon then refuses a
write into any other context, `CxRegistry` included (`:forbidden-context`), a `retract!` or
`edit!` of another agent's claim, and a `:creator` other than the agent's
(`:creator-mismatch`), whichever client sent it. `join` writes the placement edges into
`CxUniverse`, so the operator runs each `join` over the admin token, and the agent's process
uses the handle `join` returns — `{:medium :agent :context :channel}` — with a `wire`
medium over its own connection. With no table, the daemon's one bearer token is the whole
of its access control: a `wire` write reaches the daemon with the `:creator` and the
context the caller sent, and a `retract!` from any connection removes any agent's claim.

**A wire ballot proves its voter by the recorded `:principal`.** Under the table the daemon
records the presenting token's principal in each write's provenance. No request may name
that key, with or without a table. `deref/pull!` drops the key from every provenance map it
imports (`import!`'s `:drop-principal?`), since no daemon of the pulling seat's operator's
choosing recorded a peer's principals. A plain `import!` keeps the key. A ballot
proves its voter only when it is stored in the voter's own context (`identity/context-for`).
`resolve-by-majority` counts a ballot there whose recorded `:principal` is its voter as it
counts an attested one. A wire ballot cast through a daemon
with no table proves no voter, and the resolver refuses a count that includes one.

**The key** is `identity/*attest-key*`: a byte array or a string of at least 32 bytes, or
nil (the default) for 32 random bytes drawn once per process. A deployment sets it at start
with `alter-var-root`, or with `binding`. Provenance holds only the MAC; no koinii function
writes the key to provenance, a log, a refusal or the wire. An attestation made under one key
does not verify under another, so on the per-process key ballots cast before a restart read
unattested after it, and the resolver refuses until they are re-cast. A key shorter than
32 bytes is refused (`:koinii/bad-attest-key`), naming its class and not its value.

**The admin grant is minted by `authenticate`**, from a request carrying `:admin? true`:
the deployment's `verify-fn` must pass `(verify-fn id credential {:admin? true})`, under
either policy. A nil verifier, or one with no three-argument arm, mints no admin
(`:koinii/identity-unverified`). Every principal `authenticate` verifies carries a `:grant`,
an HMAC under the same key over its id, policy and `:admin?`. The registry functions refuse a
principal whose grant does not verify (`:koinii/registry-forbidden`, `:minted? false`), a
hand-built `{:id … :admin? true}` included, and `ingest` refuses a map claiming
`:authenticated? true` without one (`:koinii/identity-unverified`). A plain
`vaelii.core/assert` into `CxRegistry` passes no koinii check at all.

The registry itself carries three facts per agent — a membership mark
(`registered_agent`), a display
name (`displayNameOf`), and a **trust value** (`trustLevel`). Trust is a *mutable number*,
not a fixed rank (decision D3): an operator-assigned tier at bootstrap, overwritten by earned
reputation later. `trustLevel` is `functional`, so an update retracts the old value and
asserts the new rather than accumulating two. The number must support one constraint any
reputation math would have to honour — an endorsement is a trust signal only across
**distinct** principals, so homogeneous agents endorsing each other are worth one signal
between them. No such math ships: nothing computes `trustLevel` from endorsements, and no
resolution policy reads it. Here trust is only *stored*.

## Speech acts: reply is an assertion

The moves agents make are a small vocabulary in `CxSpeechActs` (decision D5). They split by
whether a move stands on its own or answers another:

- **Origination** (`asserts`, `queries`) — a plain assertion in the acting agent's own
  context. The claim, plus its provenance, **is** the act; nothing wraps it, because
  provenance already records who spoke. So `asserts` is documentary vocabulary, never minted
  — *an assertion in koinii is just an assertion*. A `queries` node **is** minted, because a
  question must be told apart from a claim.
- **Response** (`answers`, `disputes`, `endorses`, `justifies`, `votesFor`,
  `votesAgainst`) — a **meta-sentex on the target**, naming it by handle, asserted in the
  responder's own context with the responder recorded as creator. The two ballots are
  response acts like the rest, marks included: a vote is cast *on* a claim, so retracting
  the claim withdraws the votes rather than leaving a count standing over nothing.

Two independent facts force the response shape, and together they are decision D1:

- **The cascade.** Each response predicate is declared `target_following_predicate` in
  `CxSpeechActs`, so retracting a target sweeps its replies with it
  (`retract-following-metas!`). A bare assertion that merely *named* the target would outlive
  it as a dangling edge; a meta-sentex on the target does not. (The cascade needs *both* the
  meta-sentex and the mark — an unmarked meta merely orphans harmlessly.)
- **First-writer-wins.** Because provenance is first-writer-wins, an endorsement cannot be
  the endorser re-asserting the claim (that writes no new provenance) — it must be its own
  object with its own creator. So two endorsers of one claim are two distinct `endorses`
  sentexes, the case a bare re-assert would collapse to one.

Idempotence falls out of sentence identity: re-asserting the same meta-sentex in the same
context moves no belief, so an at-least-once feed is safe to act on — replay a reply and the
KB is unchanged. The error acts (`notUnderstood`, `refuse`) name the received edge in the
refusing agent's context and are deliberately *unmarked*: a parse failure is a fact about the
exchange that should outlive whatever provoked it. Adjudication is a separate concern (below);
this layer only *represents* the moves.

### Lineage: ACL performatives and social commitments

The eleven acts in `CxSpeechActs` correspond to the performatives of KQML (Finin et al.
1994) and FIPA-ACL (FIPA 2002), and to the moves of an argumentation dialogue (Walton &
Krabbe 1995). Both ACLs descend from speech-act theory (Searle 1969). Koinii reads each act
as a public commitment in the sense of Singh (2000) and Fornara & Colombetti (2002). An
act's sentex, its context and its `:creator` provenance are stored in the KB, and every
agent that reads the channel can read all three. FIPA's SL semantics define a performative
by the sender's beliefs and intentions, and no receiver can inspect that state.

| Act | KQML / FIPA-ACL | Dialogue move | What the stored act records |
|---|---|---|---|
| `asserts` | KQML `tell`; FIPA `inform` | claim | The creator commits to the claim, which is stored in the creator's context. |
| `queries` | KQML `ask-if`; FIPA `query-if`, `query-ref` | question | The creator opens a request for an answer and commits to no content. |
| `answers` | KQML `reply`; FIPA `inform-if`, `inform-ref` | reply | The answerer commits to the answer content. |
| `endorses` | FIPA `confirm` (nearest) | concession | The endorser takes on the target's claim under its own `:creator`. |
| `disputes` | KQML `deny`; FIPA `disconfirm` | challenge | The disputer commits to the negation of the target, which `channel/dispute` asserts beside the edge. |
| `justifies` | none; an `inform` that carries a reason | argument | The justifier offers a reason for the target. |
| `votesFor` | none | none in Walton & Krabbe | A ballot for the target, which the majority policy counts. Neither ACL has a ballot act. |
| `votesAgainst` | none | none in Walton & Krabbe | A ballot against the target, counted as `votesFor` is. |
| `retracts` | KQML `untell`; FIPA-ACL has none | retraction | `retract!` removes the claim, and the creator's commitment goes with it. FIPA's `cancel` withdraws an intended action, not an `inform`. |
| `notUnderstood` | KQML `error`; FIPA `not-understood` | none; a protocol move | No content commitment. |
| `refuse` | KQML `sorry`; FIPA `refuse` | none; a protocol move | No content commitment. |

Koinii stores the acts and computes no commitment state. No function reports whether a
query has an answer, whether a commitment is discharged or violated, or which commitments an
agent holds. `channel/open-queries` returns every query node, answered or not. The dispute
reads (below) report a clash from belief, not from a commitment record. An act is a sentex
in the KB, and koinii sends no KQML or FIPA-ACL message. The action dimension (request,
propose, accept, commit-to-do) is not in the vocabulary, and `CxSpeechActs`'s header maps it
to the A2A protocol.

References: J. R. Searle, *Speech Acts: An Essay in the Philosophy of Language*, Cambridge
University Press, 1969. T. Finin, R. Fritzson, D. McKay, R. McEntire, "KQML as an Agent
Communication Language", CIKM 1994. FIPA, *FIPA Communicative Act Library Specification*,
SC00037J, 2002. M. P. Singh, "A Social Semantics for Agent Communication Languages", in
*Issues in Agent Communication*, LNCS 1916, Springer, 2000. N. Fornara, M. Colombetti,
"Operational Specification of a Commitment-Based Agent Communication Language", AAMAS 2002.
D. N. Walton, E. C. W. Krabbe, *Commitment in Dialogue: Basic Concepts of Interpersonal
Reasoning*, SUNY Press, 1995.

## A session, start to finish

The block below runs in one process over the `local` medium, and the suite runs it
(`doc_examples_test`). It opens a KB with the starter ontology, loads the speech acts, and
joins Ava, Ben and an arbiter, Judge, to the channel `CxDeploy`.

```clojure run
(require '[vaelii.core :as v]
         '[vaelii.starter :as starter]
         '[vaelii.koinii.adjudication :as adj]
         '[vaelii.koinii.channel :as ch]
         '[vaelii.koinii.dispute :as d]
         '[vaelii.koinii.speech-acts :as sa])

(def kb (sa/load-speech-acts (starter/load-into (v/open-kb {:space 5}))))
(def ava (ch/join (ch/local kb) 'CxDeploy 'AgentAva))
(def ben (ch/join (ch/local kb) 'CxDeploy 'AgentBen))
(ch/join (ch/local kb) 'CxDeploy 'AgentJudge)

(def claim '(usesDatabase ProdCluster Postgres))
(def h (ch/assert ava claim))
(ch/endorse ben h)
(map ch/speaker-of (ch/endorsements-of ava h))           ;=> (AgentBen)

(def q (ch/pose-query ava "Which Postgres major version?"))
(ch/answer ben "16" q)                 ; (answers AgentBen "16" (sentexHandle q)) in CxBen
(map ch/answer-content (ch/answers-to ava q))            ;=> ("16")

;; the dispute asserts (not claim) and a disputes edge in CxBen; the channel
;; sees both sides of the clash, and Ava's own context sees one
(ch/dispute ben h)
(d/disputed? kb claim 'CxDeploy)                         ;=> true
(d/disputed? kb claim 'CxAva)                            ;=> false

;; Judge rules for Ava: a :monotonic assertion in CxJudge defeats Ben's rebuttal
(def id (:dispute-id (first (d/disputes-in kb 'CxDeploy))))
(def ruling (adj/rule kb 'AgentJudge id claim 'CxDeploy))
(d/disputed? kb claim 'CxDeploy)                         ;=> false
(let [r (adj/who-ruled kb ruling)]
  [(:arbiter r) (= #{id} (:dispute-ids r))])             ;=> [AgentJudge true]

;; retracting the ruling reopens the dispute
(v/retract! kb ruling)
(d/disputed? kb claim 'CxDeploy)                         ;=> true
```

Against a daemon, `ch/wire` over a `vaelii.client` connection takes the place of
`ch/local`, and the `ch/` calls run unchanged. The `d/` and `adj/` calls take the KB itself
and refuse a connection or a medium (`:koinii/needs-kb`), so they run in the daemon's
process ([The deployment shape](#the-deployment-shape)).

## Disputes and adjudication

**"Disputed" is a precise word.** It is not "false" and not "defeated-by-strength." A dispute
is a *coexisting* clash — `S` and `¬S` both believed with no strength winner, so `argue`
returns `:contradiction` and the engine deliberately leaves both standing (paraconsistent
tolerance — [nmtms.md](nmtms.md)). A clean strength-defeat, a `:monotonic` premise beating a
`:default` one, is the **opposite**: the loser is `:defeated`, `argue` returns `:false`, and
that is *resolved*, not disputed. Two error classes are kept distinct and never merged:

- **`:contradiction`** — a coexisting `:default` dilemma (a rebuttal, or a definitional clash
  at equal strength). Both sides believed.
- **`:conflict`** — an irreducible clash among `:monotonic` content: two things asserted
  known-true that cannot both hold, which the engine has no grounds to prefer.

The engine represents contradiction but answers it only whole-KB; koinii adds the
**per-channel** reading — "is there an open dispute *here*?" A dispute is observed by a context
exactly where it can read **both** clashing sides, up the `genlCx` ancestor set. So a clash between
Atlas's `P` and Boreas's `¬P` surfaces in the channel that sees both agent contexts and *not*
in a sibling that sees only one — from a one-sided vantage there is no clash to see. The hot
path (`disputed?` on a named sentence) is a scoped `argue`, which never computes whole-KB
contradictions, so a subscriber may call it in a loop.

The **dispute lifecycle** is decision D9: `open → notified → resolved`, with a stale sweep for
the un-ruled. Two of the four states are *derived* from current belief (`:open`, `:resolved`)
and two are *stored* as ordinary assertions (`:notified`, `:stale`) — stored so `why` explains
them and retracting one reopens the dispute.

**A dispute id names content.** `dispute-id` is the sorted vector of its sides' content
digests (`v/digests`, [storage.md](storage.md#content-digests)), so two seats holding the
clash at different handles name it with one value. The stored marks carry it as `(DisputeFn
"sha256:…" …)`, and the `:adjudication` tag below holds it, so neither holds a handle. A
dispute id is compared, never looked up: `adjudication/rule` reads a dispute's sides off
the live clash that carries the id.

### Adjudication: split by policy

koinii's first answer to a disagreement is **not** to pick a winner. When two agents
assert `P` and `¬P` at `:default`, the KB stays paraconsistent — both coexist — and the layer
records the dispute, pushes it to whoever is watching, and manages its life. Three policies:

- **Leave-open-and-notify** *(the default)* — record open, notify, change no belief. Correct
  for a ground truth people curate. Notification fires **once per dispute**; the stored mark
  is the idempotency key, so a redelivery or a catch-up re-run does not re-push it. A stale
  sweep bounds the accumulation: an aged-out dispute is flagged `:stale` (still live — the
  clash still coexists) and re-surfaced to a human, never silently dropped. A dispute's age is the
  latest `:created` among its sides and everything they rest on, since a derived side has no
  provenance of its own; reading the sides alone would give an emergent clash (two rules
  concluding `S` and `¬S`) no age and sweep it at its first tick.
- **Arbiter escalation** — a designated arbiter's ruling is an ordinary `:monotonic`
  assertion of the upheld side. Its strength defeats the losing `:default` side, so the clash
  clears, `why` explains who ruled, and — the point — **retracting the ruling reopens the
  dispute**, cascading through the JTMS. A ruling koinii could not undo would be a worse store
  than one that leaves the dispute open. One ruling per arbiter per dispute: ruling the
  other side retracts the arbiter's standing ruling first, since two monotonic rulings on
  one clash would be a `:conflict` no ruling can settle. Both moves land in **one settle**
  (`edit!` adds before it removes), so a refusal on the replacement cannot leave the
  arbiter having withdrawn a ruling and asserted nothing.

  A ruling is found again by the `:adjudication` tag on its provenance, which holds the
  **set** of disputes it settles: canonical dedup gives one sentex per sentence and
  context, so an arbiter upholding one claim against two opponents records an adjudication
  on a single handle twice, and a single-valued tag would leave the earlier dispute
  reading no standing ruling at all — then taking a second one beside the first. The
  dispute id is compared in the sorted spelling `dispute-id` builds, since a caller may
  hold its digests in either order. An arbiter who is **a party** to the dispute is refused
  (`:arbiter-is-party`): a ruling lands in the arbiter's own context, so for a party it
  would re-record their own claim or retract it, deleting the disputed sentence rather
  than settling the clash. A ruling for a sentence that is neither a side nor a side's
  negation is refused (`:koinii/not-a-side`). A side respelled since the id was read, as a
  `symmetric` declaration respells one, has a new digest, so the old id names no side.

  Both of those reads follow **belief**, not storage. A defeated sentex stays stored on
  purpose (it can revive), so an unfiltered enumeration of an agent's context sees claims
  and rulings the agent no longer holds — and each has a consequence: a defeated ruling
  read back as standing is *withdrawn as stale*, which for the majority policy's tie arm
  means retracted, so a ruling that had already lost its force is destroyed rather than
  left to revive; a defeated claim read back as a side convicts its holder of being a
  party to a dispute they have stepped out of.
- **Majority vote** — a ballot is a meta-sentex on the disputed claim (`votesFor` /
  `votesAgainst`), knowledge like every other move, so `why` explains a decision as "the
  majority voted, here are the ballots." The decision reuses the arbiter's reversible
  monotonic assertion; the rule the count adds is that **a tie upholds nothing** — an
  evenly-split house stays open rather than being decided by fiat, which is the whole reason
  to count instead of decree. A voter who cast both stances has *spoiled* their ballot,
  counted on neither side. The count is the authority every time it is taken: a house that
  swings withdraws the standing ruling and rules the other side, and one that dissolves into
  a tie withdraws it and stays open (`:withdrawn` in the result names what was retired).
  Turning the count into a ruling **requires the proof-tier policy** — a defeating verdict
  tallied by claimed voter name is spoofable under cooperative (one operator, many names),
  which is exactly the trust-weighting the identity design forbids, so `resolve-by-majority`
  refuses there (`:koinii/identity-unverified`). Counting stays open for transparency; only
  the ruling requires the proof-tier policy. Under `:proof-tier` it also refuses when any
  ballot on the claim, a spoiling one included, sits outside its voter's own context or
  carries neither an attestation nor a daemon-recorded `:principal` naming its voter, and
  names those ballots in `:unattested`. `adjudication/cast-ballot` casts the attested ballot through
  `identity/ingest`, and a daemon holding a token table records the `:principal` that
  stands in for an attestation; `channel/vote` in process, and over a daemon with no table,
  casts ballots that prove no voter. One such ballot therefore blocks the ruling until it is
  retracted.

**Trust-resolve** — automatic resolution by source trust — is deliberately out of scope for
this layer; it is engine-side reputation work, and reaching for it here would resolve
disagreements by weighing spoofable identities.

An open dispute does **not** block dependent reasoning — the KB keeps deriving and both sides
stay believed. But a conclusion resting on a contested premise should be *visible as such*:
`contested-premises` / `rests-on-contested?` are pure reads that surface the risk without
hiding anything. Both resolve the conclusion **up the `genlCx` ancestor set**, the scoping the
dispute reads and `ask?` already use: a channel's answer is usually placed in the agent
context that holds its premises rather than in the channel, so a flag keyed on the reading
context's own store would call a conclusion built on a disputed claim uncontested. Where
several contexts in the ancestor set hold the conclusion their support closures are unioned — a
reader is trusting whichever derivation answered — and only believed ones count, since a
defeated sentex holds up no answer. `contested-premises` reports its handles in **content
order**: the support
walk collects them into a set, and the handles in it are allocated in assertion order, so
ranking on either would make the list a fact about how the KB was loaded. The heavier option,
`quarantine`, reversibly masks a contested claim from a channel via `except` — off by default,
because it over-suppresses (with the claim masked the channel can no longer see the *dispute*
either).

## Belief: what an agent holds

Reading what an agent *holds* is modal belief projection ([belief.md](belief.md)):
`(believes agent P)` proves `P` in the agent's **own** context, never the asker's. So agents
may hold contradictory beliefs without the KB contradicting itself, and asking what one agent
believes never pulls in another's. `believe-own` links an agent's belief context to its
koinii write context, so it believes what it asserted and endorsed.

The constructive complement is `convene`: create a spec (arbiter) context that sees several
agents' belief contexts, so their otherwise-isolated beliefs meet in one place and any `P`/`¬P`
among them surfaces as a contradiction (`disagreements`) ready for adjudication. Agent belief
contexts share no ancestor, so contradictory beliefs coexist silently until a common
descendant is convened on demand.

A boundary here matters. An agent may **disregard** its own statement — `disregard` puts an
`except` in the agent's own context, hiding the statement reversibly without deleting it — but
this is restricted to *own* statements by construction, and the restriction is the point.
An `except` hides its target from belief at every context that sees the except, and the
target stays stored. Using it across agents (B hiding A's claim) would make a
common-descendant context unable to *argue*, because argumentation needs both a claim and
its rebuttal believed there for the TMS to weigh them. Cross-agent disagreement is therefore
`dispute` / `argue`, which leaves both sides for the TMS to weigh; `except` is only ever an
agent hiding what it *itself* said.

## Catch-up: snapshot + tail

An agent that was offline must catch up on what it missed — including the case the naive
version gets wrong. The feed's ring is bounded, so an agent gone long enough is **lagged past
recovery**: its stored cursor can no longer replay the gap. This is exactly the **CDC
snapshot+tail** pattern (Debezium, Kafka): a consumer that joined late — or fell too far
behind — re-reads current state (the *snapshot*), then resumes streaming from the newest
offset (the *tail*). Koinii's context re-read is the snapshot half. This is decision D6.

**The snapshot is authoritative, not a fallback nicety.** The change feed is add-oriented: it
reports a datum entering belief and a stored one leaving it, but a **premise retracted** is
dropped, and so is every conclusion its sweep deleted with it ([feed.md](feed.md)). So the
incremental stream cannot, by itself, be a complete replica — only a full re-read reflects
retractions. The tail is an optimization for the common case (koinii accretes — claims,
replies, votes); the snapshot is the source of truth, and every catch-up path ends
reconciled against it or a live tail. When `poll` reports `:lagged` non-zero, `sync!`
re-reads rather than trusting a stream it knows is incomplete.

The cursor an agent keeps ("the last feed position I processed") is deliberately **client-side**
(decision D7). A cursor in a KB context would be self-describing, but it would write to the
shared truth on every poll — turning a read loop into a *write* loop through the single writer.
A deployment backs the `CursorStore` with a file, a KV row, or the agent's own store; the
in-memory atom is the default, and the tests use it.

Catch-up is **wire-only**: the ring, the cursor, and lag exist on the wire feed. An in-process
medium has no ring to fall off, so a single-process agent needs none of this and the
`-feed-open` / `-feed-poll` / `-feed-close` operations throw there.

**A pass that throws closes the subscription it opened.** A bootstrap or a re-open that
fails before `sync!` stores its position leaves a subscription only the daemon holds, and the
next pass opens another; unclosed, each one counts against the daemon's subscription limit
until its idle reap. So `sync!` calls `-feed-close` on the subscription it opened last when
the pass throws, unless the stored position names it.

**A poll that fails is a failure, whatever it threw.** `sync!` reads a `:type` off a refusal
to tell a reaped subscription from anything else, but a transport is free to throw something
carrying no type at all — and treating that as "no error" drops it into the drained-to-head
arm, which persists a nil cursor and hands the caller its stale replica as though the stream were
current. Silent loss is the failure this module exists to prevent, so any exception out of the
poll is re-thrown with the original as its cause, and a poll answering no cursor is refused
rather than stored.

**Recovery is bounded, and one budget covers both ways of needing it.** Two replies send
`sync!` back for a re-read — the cursor off the ring (`:lagged`) and the subscription reaped
out from under the poll (`:unknown-subscription`) — and a pass gets eight re-reads between
them, not eight apiece: what the bound protects is the work of re-reading the whole context
per turn, which costs the same whichever reply asked for it. Spending the budget throws
`:koinii/catchup-thrashing` carrying a `:condition` that names the reply that spent it, so a
consumer that cannot keep up with the ring is told apart from one whose subscription never
survives long enough to be polled. Either way the pass ends in a refusal the caller can act
on rather than in a `sync!` that re-reads forever without returning.

**A consumer has one driving thread.** `sync!` is a read-modify-write over the stored cursor
and the replica, and the cursor is a claim about what *this* replica has applied —
two drivers each advancing it apply half the stream apiece. `sync!` takes the consumer's own
monitor (uncontended when the contract is kept), which stops an interleaving from corrupting
the replica outright; it does not make two drivers a sensible arrangement.

## The other deployment shape: independent seats

The default topology is N agents funnelling writes through one daemon — the daemon *is* the
shared KB, and dereferencing a claim is a plain read. A second topology drops the shared
daemon: independent **seats**, each a separate process holding its own copy of the KB, stay in
sync by **content-addressed commits** rather than a live socket. A seat asserts and commits;
another seat pulls the same commit and resolves the same sentence *from its own KB*. The
locator travels over a transport; the proof comes from the KB; neither seat trusts the marker.
Complements the daemon, not rivals it: the daemon for live co-writing, seats for disconnected
or independently-replicated deployments.

Five ideas, each grounded on a primitive that ships:

- **The locator is content-addressed.** A handle is a number one store minted and does not
  travel; a locator is a self-describing `"sha256:"` digest over a sentex's **canonical
  identity** — its context, polarity, and canonicalized sentence
  ([canonicalization.md](canonicalization.md)), the content digest `vaelii.core/digest`
  computes ([storage.md](storage.md#content-digests)). Two seats holding the same assertion compute
  the *same* locator, because `import!` re-canonicalizes every record through the reading
  build's own constructor. The digest input is an explicit type-tagged byte encoding, not
  `pr-str`: injective across the value space a sentence holds, and independent of ambient
  print vars, so a symbol never digests as the like-spelled string.
- **The commit is a Merkle function of belief.** `commit-id` is an RFC-6962 Merkle root over
  the seat's *sorted* per-sentex leaf digests, domain-separated (`0x00` leaf, `0x01` node) so
  a leaf cannot be forged as an internal node. Order- and handle-independent, because belief
  and storage are order-independent ([nmtms.md](nmtms.md)) — so two seats that reached the
  same beliefs by different routes compute the same commit id. **A reply is located by its
  target**: every response act names its target as `(sentexHandle n)`, and the digest
  carries the target's own digest in place of `n`, recursively, so two seats that built one
  conversation in different orders agree on each reply's locator and on the commit id. A
  record whose chain of targets comes back to itself digests that reference as the number
  of links back, and a handle naming no record digests its number, since nothing else
  distinguishes two such references. The tree
  shape buys pure auditability: `inclusion-proof` yields an audit path and `verify-inclusion`
  recomputes the root from just a `(locator, proof)` pair, with **no KB**. (`commit-id`
  fingerprints *knowledge*; `state-root` folds provenance in for a git-commit-like *snapshot*
  identity that moves when who/when moves.)

  **The leaves are what the seat believes, not what it stores.** A defeated default and a
  conclusion whose support was withdrawn stay stored on purpose ([nmtms.md](nmtms.md)) — they
  can revive — and they are no part of what the seat *holds*. Folding them in would make the
  id a function of a seat's retraction history as well as its knowledge: two seats agreeing
  on every belief but differing in what each had once stored would compute different ids and
  read as disagreeing about the knowledge, which is the one question these ids answer. So
  `commit-id`, `state-root` and `inclusion-proof` all enumerate the believed records, and a
  defeat moves the id exactly as a retraction does. `inclusion-proof` on an unbelieved
  record's locator is `nil`: there is no leaf, and a path that verified against the published
  root would be claiming otherwise.
- **The marker is untrusted.** `dereference` finds the sentence in the seat's own KB and
  rehashes what it found; a stale or tampered marker fails that check and is rejected, and a
  marker the seat cannot resolve means the commit was not received — never that the payload
  should be believed. A reply's marker carries its target's marker under `:targets`, keyed
  by the sender's handle number; `dereference` resolves each target on its own seat first
  and substitutes the handle it finds there, so a seat that built the conversation itself
  resolves the reply as a pulled seat does. A target the seat does not hold fails the reply
  with `:target` naming it; the reply's rehash covers every target, so no target's locator
  is trusted either. Attribution is trustworthy only as far as the identity model above makes
  it: a distributed KB inherits the same cooperative-vs-proof-tier question.
- **Resolution follows belief, exactly as the commit does.** `dereference` answers from the
  *believed* records, not the stored ones, so the two halves of a seat agree about what it
  holds: a defeated default resolves nowhere, which is the same set `inclusion-proof` will
  not prove. It finds the record by the marker's sentence and context and tells the two
  absences apart (`:not-received` vs `:not-believed`). A bare locator resolves nothing: a
  digest is a checksum, and no index is keyed by it ([storage.md](storage.md#content-digests)).
- **`dereference` fails closed on a malformed payload**, the way `verify-inclusion` does on a
  malformed proof. A marker that is not a map, one whose `:locator` is not the `"sha256:"` +
  64-hex format, one missing `:sentence` or `:context`, and one whose sentence the engine
  declines to be asked about all answer `:reason :malformed` with a `:problem` naming the
  part — never an engine refusal thrown out of the resolve path, which would let a peer crash
  a receiving seat by sending garbage. A distinct reason from `:not-received` because the two
  say different things about the peer: one is out of sync and the next pull fixes it, the
  other is sending garbage. Sentence grammar stays the engine's: the resolver asks
  `handle-of` and translates its typed refusal rather than keeping a copy of the grammar
  that would drift from the entry point that decides.

**A seat that writes is a fork over the commits it pulls.** `pull!` into a seat that is not
a fork needs an empty KB and is refused `:not-empty` otherwise, so such a seat is a replica.
A seat opened as a fork holds the shared knowledge as its base and its own writes in the
fork's own half, and each `pull!` installs the commit as the new base and asserts the
seat's writes again over it ([overlay.md](overlay.md#replacing-the-base)):

```clojure
(def seat (v/open-kb {:backend :overlay
                      :base    {:backend :disk-log :dir "/var/lib/seat/base"}
                      :overlay {:backend :disk-log :dir "/var/lib/seat/own"}}))
(deref/pull! seat "/srv/commits/shared")         ; the shared knowledge, as the base
(v/assert seat '(genlCx CxSeatA CxShared))
(v/assert seat '(usesDatabase EdgeNode SQLite3) 'CxSeatA)
(deref/pull! seat "/srv/commits/shared")         ; a newer commit, the observation kept
```

The seat's observations go in a context of its own that sees the shared contexts through
`genlCx`, so a rule the commit carries applies to them. The two directories are the seat's
own: the process that opens the seat holds both locks, and the base's lock until the JVM
exits (`close!` releases the fork's own directory). The next open names the same two
directories and needs no pull. A seat's retraction of a shared fact is retracted again
after the pull. A seat's `except` on a shared fact names that fact's handle in the new
commit. `pull!`'s summary reports under `:rebase` what the seat asserted again and what
it could not.

**A seat publishes its own writes as a delta.** `(v/export-text! seat dir {:delta? true})`
writes the fork's own writes as a text KB, each handle a sentence names written as the
`(ist Cx S)` reference it resolves from, with the named record's digest, and
`(v/load-text! peer dir {:merge? true})` reads them into a peer that holds the shared
knowledge at its own handles, reporting what it refuses ([overlay.md](overlay.md#a-delta)).
A reference the peer canonicalizes otherwise is refused `:canonical-mismatch`. A peer that loads a seat's observation reaches the
seat's defeat of a shared default, since belief decides between the two in either KB.

**What leaves a seat names content.** A reply, a ballot or a mark written to text names its
target as `(ist Cx S)`; a dispute id, a locator and a commit id are digests; a marker
carries its sentence and context. A handle in a daemon reply is that daemon's; a sentex the
reply names as a map carries its sentence and context, and its digest under `:digests?
true`. The attestation MAC covers a handle and is checked only in the process that holds
the key ([overlay.md](overlay.md#a-handle-stays-in-its-kb)).

## Design decisions

The koinii modules cite these by number. Each is a choice to reuse a core mechanism over
adding one, or to state a limit rather than hide it.

| | Decision | Why |
|---|---|---|
| **D1** | A reply is a meta-sentex on its target | The `target_following_predicate` cascade tears replies down with the target; first-writer-wins forces each act to be its own object with its creator recorded. |
| **D3** | Trust is a mutable number, not a fixed rank | An operator tier at bootstrap, overwritten by earned reputation; `functional`, so an update retracts-then-asserts rather than accumulating. |
| **D4** | Identity strength is conditional on policy | Cooperative (trusted by convention) for notify-only; proof-tier (a verified credential, fail-closed) required once trust-resolve is on. |
| **D5** | Moves are knowledge, not messages | A speech act is a sentex — queryable, retractable, auditable — so the conversation lives in the graph, not the client. |
| **D6** | Catch-up is CDC snapshot + tail | The feed drops retracted premises, so it cannot be a complete replica; a full re-read is authoritative, the tail an optimization. |
| **D7** | Single-writer total order; client-side cursor | Store order already *is* causal order, so logical clocks are redundant; a KB-side cursor would turn every poll into a write. |
| **D8** | An agent writes only its own context | The write destination is a deterministic function of the authenticated id, so "write your own context" needs no separate check. |
| **D9** | A four-state dispute lifecycle | `open`/`resolved` derived from belief, `notified`/`stale` stored so `why` explains them and a retract reopens the dispute. |

## Where it lives

`src/vaelii/koinii/`. Every module is additive over the public core API; nothing in core
loads any of them, and none of them requires anything under `vaelii.impl`.

- `vaelii.koinii.identity` — per-agent contexts, the write boundary, the admin registry,
  the `authenticate` extension point, and the write attestation (`*attest-key*`). KB:
  `resources/kb/koinii/CxRegistry.txt`.
- `vaelii.koinii.speech-acts` — the `CxSpeechActs` vocabulary and the origination /
  response acts. KB: `resources/kb/koinii/CxSpeechActs.txt`.
- `vaelii.koinii.channel` — the coordination library: the `Medium` protocol (`wire` /
  `local`), `join` / `assert` / `pose-query`, the reply verbs `answer` / `endorse` /
  `justify` / `dispute` / `vote` / `reply-many`, `subscribe` / `unsubscribe`, and the
  recovery reads `answers-to` / `endorsements-of` / `open-queries` / `query`.
- `vaelii.koinii.dispute` — the per-channel dispute reads and the lifecycle vocabulary.
  The stored half of that lifecycle — the `:notified` and `:stale` marks — lives in
  `CxDisputes` (`dispute/state-context`), the one well-known place a dispute id is
  looked up in. The marks are bookkeeping rather than channel knowledge, so nothing sees
  the context by default. Its seed, `resources/kb/koinii/CxDisputes.txt`, places it under
  `CxUniverse` and declares `disputeNotified`, `disputeStale` and the `DisputeFn` term they
  carry. `identity/load-registry` and `speech-acts/load-speech-acts` each load the seed,
  so a context that sees CxDisputes reads those declarations before any dispute exists. A
  mark written into a KB that ran neither loader loads the seed first.
- `vaelii.koinii.adjudication` — the leave-open / arbiter / majority policies, the notify
  and stale sweeps, and the contested-premise reads.
- `vaelii.koinii.belief` — belief projection, `convene` / `disagreements`, and
  own-statement `disregard`.
- `vaelii.koinii.catchup` — the CDC snapshot+tail consumer and the client-side
  `CursorStore`.
- `vaelii.koinii.deref` — the independent-seat topology: content-addressed locators,
  Merkle commits, and untrusted-marker dereference.
