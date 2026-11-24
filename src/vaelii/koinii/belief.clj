;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii.belief
  "Koinii belief projection and own-statement disregard — reasoning about what agents
  hold, built on modal belief projection (`vaelii.impl.modal`, `docs/belief.md`) and
  `except` masking.

  Two capabilities, and a boundary between them that matters:

  - **Projection — read what an agent holds.**  `(believes agent P)` proves `P` in the
    agent's OWN context (`CxAgent<agent>`), never the asker's, so agents may
    hold contradictory beliefs without the KB contradicting itself, and asking what one
    agent believes never pulls in another's.  `believe-own` links an agent's belief
    context to its koinii write context, so it believes what it asserted and endorsed.
    This is the whole cross-agent story: you ask what an agent holds *from that agent's
    own context* — you never merge one agent's beliefs into another (a cross-agent
    `genlCx` would, and would drag one agent's contradictions into the other).

  - **Disregard — an agent reversibly withdraws its OWN statement.**  `disregard` puts
    an `(except (sentexHandle H))` in the agent's own context, hiding `H` for reads and
    derivations, reversibly (`restore!`), without deleting it.  It is restricted to the
    agent's own statements **by construction**, and that restriction is the point: an
    `except` hides its target from belief at every context that sees it, so using it
    across agents (agent B hiding agent A's claim) would make a common-descendant context
    unable to *argue*: argumentation needs both a claim and its rebuttal believed there
    for the TMS to weigh them.  Cross-agent disagreement is therefore `dispute` / argue
    (speech-acts + adjudication), which leaves both sides for the TMS to weigh; `except`
    is only ever an agent removing from belief what it *itself* said.

  Additive, like the other koinii modules: only the public core API plus koinii
  `identity` and `types` — nothing under `vaelii.impl`, and nothing in core loads it."
  (:require [vaelii.core :as v]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.types :as koinii-types]))

;; ---- projection: read what an agent holds, from its own context ----------

(defn belief-context
  "The context koinii `(believes agent P)` projects into — the modal
  convention's `CxAgent<agent>` (`vaelii.core/context-of-agent`).  Distinct from
  the agent's koinii write context (`id/context-for`); `believe-own` links the two."
  [agent]
  (v/context-of-agent agent))

(defn believe-own
  "Link `agent`'s belief context to its OWN koinii context (`id/context-for`) —
  `(genlCx CxAgent<agent> CxAgentWriteCtx)` — so `(believes agent P)` reflects what the
  agent asserted and endorsed as speech-acts.  A same-agent edge only: it never links one
  agent's context to another's (that would merge belief sets), so it cannot tangle the
  lattice argumentation runs over.  Monotonic topology.  Returns the belief context."
  [kb agent]
  (koinii-types/needs-kb! `believe-own kb)
  (v/assert kb (list 'genlCx (belief-context agent) (id/context-for agent)) 'CxUniverse
            {:strength :monotonic :creator agent})
  (belief-context agent))

(def ^:private grant-ctx
  "The context the `believes` `modal_predicate` grant is declared in (core.txt, loaded into
  CxUniverse), so a modal goal posed from here is recognized by `BeliefProjectionProver`."
  'CxUniverse)

(defn would-believe?
  "Does `agent` hold `proposition`? — `(believes agent proposition)` proved in the
  agent's own belief context, never the asker's.  `asker` (default CxUniverse) need only
  see the `believes` grant; it does not affect where the proposition is proved."
  ([kb agent proposition] (would-believe? kb agent proposition grant-ctx))
  ([kb agent proposition asker]
   (koinii-types/needs-kb! `would-believe? kb)
   (v/ask? kb (list 'believes agent proposition) asker)))

(defn project
  "The binding maps for what `agent` believes matching `goal` (a proposition that may
  carry `?variables`), each answer proved in the agent's own context.
  `(project kb 'AgentAtlas '(usesDatabase ProdCluster ?db))` -> the DBs Atlas holds
  ProdCluster uses.  `asker` defaults to a grant-seeing context."
  ([kb agent goal] (project kb agent goal grant-ctx))
  ([kb agent goal asker]
   (koinii-types/needs-kb! `project kb)
   (v/ask kb (list 'believes agent goal) asker)))

;; ---- convene: bring isolated beliefs into one arena to argue --------------

(defn convene
  "Create/extend a spec (arbiter) context `spec-ctx` that sees the belief contexts of
  `agents` — `(genlCx spec-ctx CxAgent<a>)` for each — so their otherwise-isolated
  beliefs meet in one context and any P/¬P among them surfaces as a `contradiction`
  (read with `disagreements`).

  The constructive complement to projection: agent belief contexts share no ancestor, so
  contradictory beliefs coexist silently (`docs/belief.md`); this convenes a common
  descendant on demand, and contradiction detection — scoped to what a context sees —
  raises the clash the moment the edges land.  (This is also why `disregard` is
  own-statement-only: an `except` here would hide a side and suppress the very
  contradiction the arbiter convened.)  Monotonic, idempotent.  Returns `spec-ctx`."
  [kb spec-ctx agents]
  (koinii-types/needs-kb! `convene kb)
  (doseq [a agents]
    (v/assert kb (list 'genlCx spec-ctx (belief-context a)) 'CxUniverse
              {:strength :monotonic}))
  spec-ctx)

(defn convened-agents
  "The agents whose belief contexts `spec-ctx` sees — the agent set `convene` gathered,
  read back off the visibility lattice."
  [kb spec-ctx]
  (koinii-types/needs-kb! `convened-agents kb)
  (into #{} (keep v/agent-of-context) (v/context-up kb spec-ctx)))

(defn disagreements
  "The disagreements among the agents convened into `spec-ctx`: the KB `contradictions`
  both of whose sides are held by convened agents, each as
  `{:between #{agent …} :sides [{:agent :sentence :handle} …]}`.  A disagreement is here
  only because `spec-ctx` sees both sides — the contradiction the arbiter convened, ready
  for adjudication to weigh and resolve.  A side is matched to its agent whether
  the belief is stored in the belief context directly or seen through it from the agent's
  koinii context (`believe-own`)."
  [kb spec-ctx]
  (koinii-types/needs-kb! `disagreements kb)
  (let [agents     (convened-agents kb spec-ctx)
        ctx->agent (into {} (mapcat (fn [a] [[(belief-context a) a] [(id/context-for a) a]]))
                         agents)]
    (into []
          (keep (fn [c]
                  (when (every? #(ctx->agent (:context %)) (:sides c))
                    {:between (into #{} (map (comp ctx->agent :context)) (:sides c))
                     :sides   (mapv (fn [s] {:agent    (ctx->agent (:context s))
                                             :sentence (:sentence s)
                                             :handle   (:handle s)})
                                    (:sides c))})))
          (v/contradictions kb))))

;; ---- disregard: an agent reversibly withdraws its OWN statement -----------

(defn disregard
  "`agent` reversibly withdraws its OWN statement at `target-handle`: an
  `(except (sentexHandle target-handle))` in the agent's own context hides the statement
  for reads and derivations — from the agent's beliefs and from anyone reading the
  agent's context — while keeping it stored, so `restore!` can bring it back.  Softer
  than `retracts` (a real teardown): nothing is deleted and no cascade runs (`except` is
  deliberately not `target_following_predicate`).

  **Own statements only, enforced.**  An `except` hides its target from belief at every
  context that sees it, so hiding *another* agent's claim would take it from a
  common-descendant context, which could no longer weigh the claim against its
  rebuttal.  Cross-agent disagreement is `dispute` / argue, not this.  A `target-handle`
  whose provenance creator is not `agent` is refused (`:koinii/not-own-statement`).
  Returns the except's handle."
  [kb agent target-handle]
  (koinii-types/needs-kb! `disregard kb)
  (let [creator (:creator (v/provenance kb target-handle))]
    (when-not (= creator agent)
      (throw (ex-info (str "koinii: an agent may disregard only its own statement — "
                           agent " cannot except a statement by " (pr-str creator))
                      {:type :koinii/not-own-statement :agent agent
                       :creator creator :handle target-handle})))
    (v/assert kb (list 'except (v/sentex-handle target-handle))
              (id/context-for agent) {:strength :monotonic :creator agent})))

(defn restore!
  "Undo a `disregard`: retract the except at `handle`, so the withdrawn statement counts
  again.  Retracting the except restores the statement to belief.  Returns
  `retract!`'s counts."
  [kb handle]
  (koinii-types/needs-kb! `restore! kb)
  (v/retract! kb handle))

(defn disregards
  "Every statement `agent` is currently disregarding — the `(except (sentexHandle ?h))`
  facts in the agent's own context.  'What has this agent chosen to withdraw' as a plain
  read."
  [kb agent]
  (koinii-types/needs-kb! `disregards kb)
  (v/sentexes-matching kb (list 'except '?h) (id/context-for agent)))
