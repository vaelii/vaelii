;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii.identity
  "Koinii actor identity: per-agent contexts as the identity substrate AND the
  write boundary, an admin-only agent registry, and the one auth extension point whose strength
  is conditional on the adjudication policy.

  The engine deliberately pushes per-caller identity OUT — `*creator*` is an
  unauthenticated annotation and the daemon's only auth is one shared bearer token —
  so koinii's answer is the context lattice, not a new auth subsystem:

  - **An agent IS its context.**  Atlas writes into `CxAtlas`, lifted under the
    channel by `(genlCx CxDeploy CxAtlas)`.  A reader of `CxDeploy` sees the union of
    every agent's assertions; `CxAtlas` alone is 'everything Atlas said' — a plain
    context read.  Because context is part of sentex identity, Atlas's `P` and
    Boreas's `P` are two DISTINCT sentexes, each with its own creator, so
    first-writer-wins loses no co-source (`co-attribution-survives?`).
  - **The write boundary is 'your own context, and nothing else.'**  That is the one
    enforcement point identity needs, and it is why the registry context is the one
    context agents may NOT write — the governed may not write the authority that
    governs them.

  The auth extension point is conditional on policy (koinii design D4):

  - **Cooperative** (the default) — `*creator*` bound by convention, the write routed
    to the agent's own context, trusted because the agents are.  Correct for a
    notify-only deployment.  It defends fat-fingers, NOT attackers: `authenticate`
    trusts the claimed id with no proof, so a client may claim any identity.  State
    plainly that identity is unauthenticated here.
  - **Proof-tier** — REQUIRED the moment trust-resolve is enabled, because
    trust-weighting a spoofable identity is worse than no trust.  `authenticate`
    verifies a credential (the `verify-fn` extension point — sign-at-ingest, an authenticating
    proxy, or A2A AgentCards / DIDs) and REFUSES an unverified request; `ingest` under
    the principal it mints attests each write with the deployment key (`*attest-key*`).
    Both checks run in the process that holds the key, never on the wire.

  Every write goes through the provenance-recording `assert` path — NEVER
  `bulk-assert-facts!`, which binds `*bulk-load?*` and writes no provenance at all."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.koinii.types :as koinii-types])
  (:import [java.io PushbackReader]
           [java.security MessageDigest SecureRandom]
           [javax.crypto Mac]
           [javax.crypto.spec SecretKeySpec]))

;; ---- loading a koinii seed context ---------------------------------------
;; koinii ships its own seed KB files under resources/kb/koinii/ and loads them
;; itself, through the public `assert` — the engine's ontology loader only walks
;; upper/ and middle/, and koinii depends on nothing under `vaelii.impl`.

(defn- read-seed
  "Every sentence of koinii's seed KB file for `context`, in file order.  Throws if the
  resource is missing — a silently empty registry is worse than a failure to start."
  [context]
  (let [path (str "kb/koinii/" (name context) ".txt")]
    (if-let [res (io/resource path)]
      (with-open [r (PushbackReader. (io/reader res))]
        (let [eof (Object.)]
          (loop [acc []]
            (let [form (edn/read {:eof eof} r)]
              (if (identical? form eof) acc (recur (conj acc form)))))))
      (throw (ex-info (str "koinii seed KB file not on the classpath: " path
                           " — koinii ships one file per context under kb/koinii/, so a"
                           " context named here wants its own file on the classpath")
                      {:type :koinii/missing-seed :context context :resource path})))))

(defn load-seed-context
  "Assert every sentence of koinii's seed KB file for `context` into that context,
  **order-insensitively**: a sentence refused because content further down the file has
  not arrived yet is retried rather than fatal, so the file may be grouped term-centrically
  rather than in dependency order.  The sentences that survive a round changing nothing are
  re-asserted without a catch, so a genuinely ill-formed one still throws.  Returns kb."
  [kb context]
  (koinii-types/needs-kb! `load-seed-context kb)
  (let [attempt (fn [ss]
                  (reduce (fn [acc s]
                            (try (v/assert kb s context) acc
                                 (catch clojure.lang.ExceptionInfo _ (conj acc s))))
                          [] ss))]
    (loop [pending (attempt (read-seed context))]
      (when (seq pending)
        (let [remaining (attempt pending)]
          (if (< (count remaining) (count pending))
            (recur remaining)
            (doseq [s remaining] (v/assert kb s context)))))))
  kb)

(defn load-registry
  "Load the CxRegistry vocabulary into `kb` from resources/kb/koinii/CxRegistry.txt.
  Koinii KB files are not auto-discovered (the starter only walks upper/ and
  middle/), so this explicit loader is how the registry context comes into being.
  Requires the upper ontology already loaded (CxRegistry wires `(genlCx CxRegistry
  CxUniverse)`).  Loads the CxDisputes seed too, so the dispute marks' declarations are
  stored before the first mark.
  Returns kb."
  [kb]
  (koinii-types/needs-kb! `load-registry kb)
  (load-seed-context kb 'CxRegistry)
  (load-seed-context kb 'CxDisputes))

;; ---- per-agent contexts: the identity substrate + write boundary ---------

(defn context-for
  "The per-agent context for `agent-id`, by convention: `AgentAtlas` -> `CxAtlas`
  (a leading `Agent` is dropped, then `Cx`-prefixed).  The destination of an agent's
  writes is a DETERMINISTIC function of its authenticated id, so 'write only your own
  context' needs no separate lookup — identity fixes the destination, and a principal
  can never be routed to a context that is not its own."
  [agent-id]
  (let [n    (name agent-id)
        base (if (str/starts-with? n "Agent") (subs n (count "Agent")) n)]
    (symbol (str "Cx" base))))

(def registry-context
  "The admin-only registry context.  The one context governed agents may not write."
  'CxRegistry)

(defn agent-context-mark
  "The sentence that says `ctx` is `agent`'s own context — `(agentContext CxAtlas
  AgentAtlas)`, written into `ctx` itself by `place-agent-context`.  Pass `'?agent` for
  the pattern that reads it back.

  **Why a written fact rather than a shape read off the lattice.**  `context-for` maps
  `AgentAtlas` to `CxAtlas` by dropping a prefix, so an agent context is spelled exactly
  like a channel and no name tells them apart; and the placement EDGES do not either,
  because `(genlCx ?parent ctx)` and `(genlCx ctx ?root)` are the ordinary wiring of any
  nested context — the same two edges under a channel rolled up into a wider one.
  Inferring the role from them makes admission a function of what else has landed and of
  which vocabulary a placement rooted at, which is order dependence in an entry point.  A
  positive stored fact is neither: it is written once by whoever placed the context, it
  reads the same however the rest of the lattice grew, and every koinii placement route
  writes it.

  It lands in the agent's OWN context, which is the one context D8 already says the agent
  writes — so recording it needs no privilege the agent does not have, and no agent can
  mark a context it may not write.  Under cooperative identity that boundary is an entry point
  and not a wall (`*policy*`), exactly as it is for everything else the agent asserts."
  [ctx agent]
  (list 'agentContext ctx agent))

(defn place-agent-context
  "Place `agent-id`'s per-agent context (`context-for`) in the lattice: LIFTED under
  `parent` so the parent sees the agent's writes — `(genlCx parent CxAtlas)` — ROOTED
  under `roots` so the agent speaks that vocabulary and the rules over it fire, and
  MARKED as the agent's own (`agent-context-mark`) so a later reader can tell an agent's
  context from a channel.  All three are `:monotonic` and idempotent, so re-placing an
  agent is a no-op; the two edges are topology in `CxUniverse`, the mark is a fact about
  the context and lands in it.  Returns the agent context symbol.

  **The three writes in one place, and `write!` is what lets them be.**  A channel writes
  through its `Medium` (for a `wire` handle, the daemon), a plain caller writes straight
  to a KB — so the writer is the argument: `write!` is `(fn [sentence context opts] …)`.
  Every koinii placement — `agent-context` here, `speech-acts/speaker-context`,
  `channel/join`, `adjudication`'s arbiter — is this trio under a different parent and a
  different root, which is what makes the mark true of an agent context however it was
  placed."
  [write! parent agent-id roots]
  (let [actx (context-for agent-id)]
    (write! (list 'genlCx parent actx) 'CxUniverse {:strength :monotonic})
    (write! (list 'genlCx actx roots)  'CxUniverse {:strength :monotonic})
    (write! (agent-context-mark actx agent-id) actx
            {:strength :monotonic :creator agent-id})
    actx))

(defn agent-context
  "Create/lift `agent-id`'s per-agent context under the channel `deploy-ctx` so the
  channel sees it — `(genlCx deploy-ctx CxAtlas)` — and root it under `CxUniverse` so the
  agent speaks the shipped vocabulary.  Both edges are monotonic topology.  Returns the
  agent context symbol."
  [kb deploy-ctx agent-id]
  (koinii-types/needs-kb! `agent-context kb)
  (place-agent-context #(v/assert kb %1 %2 %3) deploy-ctx agent-id 'CxUniverse))

;; ---- the auth extension point: authenticate a principal (policy-conditional) --------

(def ^:dynamic *policy*
  "The identity policy (koinii design D4).

  - `:cooperative` (the default) — `*creator*` is trusted by convention; correct for
    a notify-only deployment.  It defends fat-fingers, not attackers: a client may
    claim any id, and there is no barrier to impersonation.
  - `:proof-tier` — REQUIRED once trust-resolve is enabled; a credential is verified
    at ingest and an unverified request is refused.  Trust-weighting a spoofable
    identity is worse than no trust."
  :cooperative)

(def ^:dynamic *verify-fn*
  "The proof-tier verifier EXTENSION POINT: `(verify-fn claimed-id credential)` returns truthy
  iff the credential proves the claim.  nil ships no crypto — the design provides the
  extension point (sign-at-ingest / an authenticating proxy / A2A AgentCards / DIDs) and the
  deployment wires it.  Under `:proof-tier` a nil verifier fails CLOSED: every
  request is refused rather than silently trusted."
  nil)

;; ---- the deployment key: principal grants and write attestations ---------

(def ^:dynamic *attest-key*
  "The deployment's HMAC-SHA256 key — a byte array or a string of at least 32 bytes — or
  nil for a key drawn at random once per process.  `authenticate` seals each principal it
  verifies with it (`:grant`), and `ingest` under a sealed `:proof-tier` principal attests
  each write with it (`:attestation` in provenance).  The key itself lives in this var or
  in the per-process draw, and no koinii fn writes it to provenance, a log, a refusal or
  the wire.  A deployment sets it at start with `alter-var-root`, or with `binding`.  A
  grant or attestation made under one key does not verify under another, so ballots
  attested before a restart on the per-process key read unattested after it."
  nil)

(def ^:private process-key
  (delay (let [b (byte-array 32)] (.nextBytes (SecureRandom.) b) b)))

(defn- key-bytes
  "The bytes of `*attest-key*`, the per-process key when it is nil, or a refusal
  (`:koinii/bad-attest-key`) naming the class it holds — never the key."
  ^bytes []
  (let [k *attest-key*
        b (cond (nil? k) @process-key
                (bytes? k) k
                (string? k) (.getBytes ^String k "UTF-8"))]
    (if (and b (>= (alength ^bytes b) 32))
      b
      (throw (ex-info (str "koinii: *attest-key* must be a byte array or a string of at"
                           " least 32 bytes, or nil for a per-process key")
                      {:type :koinii/bad-attest-key :key-class (some-> k class .getName)})))))

(defn- mac
  "The lowercase-hex HMAC-SHA256 of `parts` under the deployment key.  `parts` is printed
  with every print var at its default, so no ambient binding changes the bytes."
  [parts]
  (let [m (doto (Mac/getInstance "HmacSHA256")
            (.init (SecretKeySpec. (key-bytes) "HmacSHA256")))
        s (binding [*print-length* nil *print-level* nil *print-meta* false
                    *print-namespace-maps* false *print-readably* true]
            (pr-str parts))]
    (apply str (map #(format "%02x" %) (.doFinal m (.getBytes ^String s "UTF-8"))))))

(defn- mac=
  "Constant-time equality of two MAC strings; false when either is not a string."
  [a b]
  (and (string? a) (string? b)
       (MessageDigest/isEqual (.getBytes ^String a "UTF-8") (.getBytes ^String b "UTF-8"))))

(defn- grant [principal]
  (mac [:koinii/grant (:id principal) (:policy principal) (boolean (:admin? principal))]))

(defn- minted?
  "True when `authenticate` sealed `principal` under the current key: its `:grant` covers
  its id, policy and `:admin?`, so a hand-built map, or a minted one with any of those
  changed, is not minted."
  [principal]
  (and (map? principal) (mac= (:grant principal) (grant principal))))

(defn- admin? [principal]
  (and (:admin? principal) (minted? principal)))

(defn- verified-admin?
  "Whether `verify` passes `id` as an admin: its three-argument arm, called with
  `{:admin? true}`.  A verify-fn with no such arm mints no admin."
  [verify id credential]
  (try (boolean (verify id credential {:admin? true}))
       (catch clojure.lang.ArityException _ false)))

(defn authenticate
  "Turn a `request` into a principal, or refuse — the identity extension point.

  `request` is `{:claimed-id <id> :credential <opaque> :source <str> :admin? <bool>}`;
  `opts` may override `{:policy … :verify-fn …}` (defaulting to `*policy*` /
  `*verify-fn*`).  Returns `{:id :context :source :policy :authenticated?}`, `:context`
  being `(context-for :id)`, plus a `:grant` sealing it under `*attest-key*` when the
  identity was verified.

  - `:cooperative` — trusts the claimed id: `:authenticated? false` and no grant.
  - `:proof-tier` — requires `(verify-fn id credential)` to pass, else throws
    `:koinii/identity-unverified`.
  - `:admin? true`, under either policy — mints the registry's one writer, `:context`
    `CxRegistry` and `:policy :admin`.  Requires `(verify-fn id credential {:admin? true})`
    to pass, else throws `:koinii/identity-unverified`; a nil verify-fn, or one with no
    three-argument arm, mints no admin."
  ([request] (authenticate request nil))
  ([request opts]
   (let [policy (get opts :policy *policy*)
         verify (get opts :verify-fn *verify-fn*)
         id     (:claimed-id request)
         cred   (:credential request)
         base   {:id id :context (context-for id) :source (:source request)}
         refuse (fn [what extra]
                  (throw (ex-info (str "koinii: identity unverified " what " — "
                                       (if verify
                                         (str (pr-str id) " did not pass the verify-fn with"
                                              " the credential it sent")
                                         (str "no verify-fn is bound, so no credential"
                                              " passes: bind one as :verify-fn or"
                                              " *verify-fn*")))
                                  (merge {:type :koinii/identity-unverified :claimed-id id
                                          :verifier? (boolean verify)}
                                         extra))))]
     (cond
       (:admin? request)
       (if (and verify (verified-admin? verify id cred))
         (let [p (assoc base :context registry-context :admin? true :policy :admin
                        :authenticated? true)]
           (assoc p :grant (grant p)))
         (refuse "for the admin grant" {:admin? true}))

       (= policy :cooperative) (assoc base :policy :cooperative :authenticated? false)

       (= policy :proof-tier)
       (if (and verify (verify id cred))
         (let [p (assoc base :policy :proof-tier :authenticated? true)]
           (assoc p :grant (grant p)))
         (refuse "under proof-tier" {:policy :proof-tier}))

       :else
       (throw (ex-info (str "koinii: unknown identity policy " (pr-str policy)
                            " — want :cooperative or :proof-tier")
                       {:type :koinii/unknown-policy :policy policy}))))))

;; ---- the write boundary --------------------------------------------------

(defn- write-boundary-problem
  "The write-auth violation `principal` would commit writing `target-ctx`, or nil, with the
  `:message` `check-write-boundary!` throws.  Two rules, one boundary:
  - `CxRegistry` is admin-only — a principal that is not an admin `authenticate` minted is
    refused (`:koinii/registry-forbidden`, with `:minted? false` for a map that claims
    `:admin?` without a valid grant): the governed may not write the authority.
  - every other context: an agent writes ONLY its own `(context-for :id)` — a write
    aimed elsewhere is refused (`:koinii/foreign-context`)."
  [principal target-ctx]
  (let [id  (:id principal)
        own (if (admin? principal) registry-context (context-for id))
        why (fn [type] (str "koinii: write refused — " (name type) ": " (pr-str id)
                            " writes " own ", not " target-ctx))]
    (cond
      (= target-ctx registry-context)
      (when-not (admin? principal)
        (cond-> {:type :koinii/registry-forbidden :principal id :context target-ctx
                 :message (why :koinii/registry-forbidden)}
          (:admin? principal)
          (-> (assoc :minted? false)
              (update :message str ".  Its :admin? carries no grant `authenticate` sealed,"
                      " so it is not an admin"))))

      (admin? principal)
      {:type :koinii/admin-off-registry :principal id :context target-ctx
       :message (why :koinii/admin-off-registry)}

      (not= target-ctx own)
      {:type :koinii/foreign-context :principal id :context target-ctx :own own
       :message (why :koinii/foreign-context)})))

(defn check-write-boundary!
  "Throw if `principal` may not write `target-ctx`; else return nil.  The single
  enforcement point — the extension point a proof-tier deployment relies on, and the reason no
  call site can route a write into a context it does not own."
  [principal target-ctx]
  (when-let [prob (write-boundary-problem principal target-ctx)]
    (throw (ex-info (:message prob) (dissoc prob :message)))))

(defn check-registry-write!
  "Throw if `target-ctx` is the admin registry; else return nil.  The **one** boundary
  that holds even in cooperative mode — where an agent may otherwise write across
  contexts (the speech-act entry points take an explicit `ctx` for exactly that) — because the
  governed may never write the authority that governs them (docs/koinii.md).  Narrower
  than `check-write-boundary!`, which also enforces own-context-only, a proof-tier rule
  the cooperative entry points do not impose.  `who` is named in the refusal for the log."
  [who target-ctx]
  (when (= target-ctx registry-context)
    (throw (ex-info (str "koinii: write refused — registry-forbidden: " (pr-str who)
                         " is governed by " registry-context ", and the governed do not"
                         " write the authority that governs them.  An agent's own"
                         " context takes the write")
                    {:type :koinii/registry-forbidden :principal who :context target-ctx}))))

(defn- principal-provenance
  "The open-provenance fields a principal rides onto its writes — `:source` and the
  identity `:policy` / `:authenticated?` it wrote under.  These are app fields the
  engine never reads (belief is provenance-blind), so a trust hint or a signature ref
  travels here without touching truth maintenance."
  [principal]
  (into {} (remove (comp nil? val))
        {:source (:source principal)
         :policy (:policy principal)
         :authenticated? (:authenticated? principal)}))

;; ---- attestation: what an ingest under a verified principal proves -------

(defn- attestation-mac [creator sx]
  (mac [:koinii/attestation creator (:id sx) (v/sentence-of sx) (:context sx)]))

(defn- attest!
  "Write `{:attestation {:creator :mac}}` into the provenance of each sentex at `h`, the
  MAC covering creator, handle, stored sentence and context, so an attestation copied onto
  another sentex, or onto the same sentence after a retract and re-assert, fails."
  [kb creator h]
  (doseq [h (if (sequential? h) h [h])
          :let [sx (v/sentex kb h)]
          :when sx]
    (v/add-provenance kb h {:attestation {:creator creator
                                          :mac (attestation-mac creator sx)}})))

(defn attested-by
  "The principal id whose `ingest` attested the sentex at `handle` under the current
  `*attest-key*`, or nil when it carries no attestation that verifies.  Only this process
  holds the key, so a writer on the wire, or a caller of `v/add-provenance`, cannot make
  one that does."
  [kb handle]
  (koinii-types/needs-kb! `attested-by kb)
  (let [sx (v/sentex kb handle)
        a  (:attestation (v/provenance kb handle))]
    (when (and sx (map? a) (mac= (:mac a) (attestation-mac (:creator a) sx)))
      (:creator a))))

(defn- reseal-replayed
  "An `import!` `:on-replayed` fn over `kb`: when the attestation a rebase carried onto
  `handle` verifies for `old`, the record the rebase captured, it is written again over
  `handle`.  An attestation that does not verify for `old`, or any under a malformed
  `*attest-key*`, stays as carried, so the rebase finishes."
  [kb]
  (fn [old handle]
    (let [a (:attestation (v/provenance kb handle))]
      (when (and (map? a)
                 (try (mac= (:mac a) (attestation-mac (:creator a) old))
                      (catch clojure.lang.ExceptionInfo _ false)))
        (attest! kb (:creator a) handle)))))

(defn rebase!
  "`(v/import! kb dir (assoc opts :rebase? true))`, sealing again over its new handle each
  fork premise whose attestation verified for its captured handle under the current
  `*attest-key*`, and each write a stopped rebase left that this one finishes first.  A
  rebase `open-kb` finishes after a stop seals none.  Returns `import!`'s summary."
  [kb dir opts]
  (koinii-types/needs-kb! `rebase! kb)
  (v/import! kb dir (assoc opts :rebase? true :on-replayed (reseal-replayed kb))))

(defn- write
  "The one provenance-recording write chokepoint.  Enforces the write boundary, binds
  `*creator*` to the principal id, rides its provenance hints in the open map, and goes
  through `v/assert` — never `bulk-assert-facts!`.  Under a `:proof-tier` principal
  `authenticate` minted it attests the write (`attest!`); a principal claiming
  `:authenticated? true` that `authenticate` did not mint is refused
  (`:koinii/identity-unverified`).  Returns the sentex handle."
  [kb principal target-ctx sentence]
  (check-write-boundary! principal target-ctx)
  (when (and (:authenticated? principal) (not (minted? principal)))
    (throw (ex-info (str "koinii: identity unverified — " (pr-str (:id principal))
                         " claims :authenticated? true with no grant `authenticate`"
                         " sealed")
                    {:type :koinii/identity-unverified :claimed-id (:id principal)
                     :minted? false})))
  (let [h (binding [v/*creator* (:id principal)]
            (v/assert kb sentence target-ctx {:provenance (principal-provenance principal)}))]
    (when (and (= :proof-tier (:policy principal)) (minted? principal))
      (attest! kb (:id principal) h))
    h))

;; ---- THE ingest helper: bind identity onto writes ------------------------

(defn ingest
  "The sanctioned everyday write path.  Given a `principal` from `authenticate` and a
  `sentence`, assert it into the agent's OWN context with `*creator*` bound to the
  principal id, so no call site can forget either the attribution or the routing.  Under
  `:proof-tier` the write is attested (`attested-by` reads it back), which is what makes
  a ballot count (`adjudication/resolve-by-majority`).  Returns the handle."
  [kb principal sentence]
  (koinii-types/needs-kb! `ingest kb)
  (write kb principal (context-for (:id principal)) sentence))

(defn ingest-into
  "The explicit-target write path, for a caller that names `target-ctx` — the write
  goes through the SAME boundary check `ingest` does, so a principal authenticated as
  Boreas targeting `CxAtlas` is refused (`:koinii/foreign-context`) and any governed
  agent targeting `CxRegistry` is refused (`:koinii/registry-forbidden`).  Returns the
  handle."
  [kb principal target-ctx sentence]
  (koinii-types/needs-kb! `ingest-into kb)
  (write kb principal target-ctx sentence))

;; ---- admin-only registry writes ------------------------------------------

(defn register-agent
  "Register `agent-id` in `CxRegistry` — its membership mark, display name, and
  bootstrap trust value — as the admin `principal`, minted by `authenticate` with
  `:admin? true`.  Refused (`:koinii/registry-forbidden`) for any other principal,
  a hand-built `{:admin? true}` included, so a governed agent cannot self-register or
  self-promote.  Returns the agent id."
  [kb principal agent-id display-name trust]
  (koinii-types/needs-kb! `register-agent kb)
  (ingest-into kb principal registry-context (list 'registered_agent agent-id))
  (ingest-into kb principal registry-context (list 'displayNameOf agent-id display-name))
  (ingest-into kb principal registry-context (list 'trustLevel agent-id trust))
  agent-id)

(defn- sole-registry-match
  "The one believed sentex matching `pattern` in the registry, or nil — and a refusal
  (`:koinii/registry-not-functional`) naming every handle when more than one stands.

  **Why this rather than `first`.**  `sentexes-matching` answers with the *set* of
  matches and promises nothing about the order they come back in, so a bare `first` over
  two rows names whichever the index enumerated — which is the order the registry was
  written in.  The trust a read reports, and the row an overwrite retracts, would then
  depend on the write order rather than on what the registry holds.

  `trustLevel` and `displayNameOf` are declared `functional`
  (`resources/kb/koinii/CxRegistry.txt`), and the koinii writers retract a value before
  writing its successor.  A second value written beside the first is stored, and the
  settle decides the pair: a second value at the first's class is a dilemma and both
  stand.  This read names that state rather than silently halving it."
  [kb pattern]
  (let [ms (v/sentexes-matching kb pattern registry-context)]
    (when (next ms)
      (throw (ex-info (str "koinii: registry read refused — " (pr-str pattern)
                           " matches " (count ms) " believed rows in " registry-context
                           ", which declares its predicates functional and holds one."
                           "  Retract the extra rows named in :handles")
                      {:type :koinii/registry-not-functional
                       :pattern pattern
                       :context registry-context
                       :handles (into #{} (map :id) ms)})))
    (first ms)))

(defn set-trust!
  "OVERWRITE `agent-id`'s trust with `new-value`, as the admin `principal` (D3: trust
  is a mutable number).  `trustLevel` is functional, so the update retracts the old
  value and asserts the new rather than accumulating two.  Refused for any principal
  but an admin `authenticate` minted.  Returns the new handle.

  The row it retracts is read through `sole-registry-match`, whose docstring holds the
  reason: the overwrite must not rest on an unordered set having exactly one member."
  [kb principal agent-id new-value]
  (koinii-types/needs-kb! `set-trust! kb)
  (check-write-boundary! principal registry-context)      ; admin check on the retract too
  (when-let [sx (sole-registry-match kb (list 'trustLevel agent-id '?v))]
    (v/retract! kb (:id sx)))
  (ingest-into kb principal registry-context (list 'trustLevel agent-id new-value)))

;; ---- registry reads: queryable ground truth ------------------------------

(defn- object-of
  "The last argument of the believed `(pred subject ?o)` sentex in `CxRegistry`, or
  nil — a plain context-scoped read of one stored fact, taken through
  `sole-registry-match` so the answer is what the registry holds and not what the
  retrieval enumerated first."
  [kb pred subject]
  (some-> (sole-registry-match kb (list pred subject '?o))
          :sentence last))

(defn trust-of
  "The stored trust number for `agent-id`, or nil — a plain context-scoped read of
  `CxRegistry`, ready for adjudication to weigh."
  [kb agent-id]
  (koinii-types/needs-kb! `trust-of kb)
  (object-of kb 'trustLevel agent-id))

(defn display-name-of
  "The stored display name for `agent-id`, or nil."
  [kb agent-id]
  (koinii-types/needs-kb! `display-name-of kb)
  (object-of kb 'displayNameOf agent-id))

(defn registered-agents
  "Every registered agent id — the extent of `(registered_agent ?a)` in `CxRegistry`.
  'Which agents exist' as a plain context-scoped read."
  [kb]
  (koinii-types/needs-kb! `registered-agents kb)
  (->> (v/sentexes-matching kb (list 'registered_agent '?a) registry-context)
       (map (comp second :sentence))
       distinct))

(defn co-attribution
  "Every context that independently asserts `sentence` — the set of per-agent contexts
  backing a claim.  Because context is part of sentex identity, an agent re-asserting
  a fact another already stated is a DISTINCT sentex in a DISTINCT context, so
  first-writer-wins provenance loses no co-source: 'how many sources back P' is this
  set, recovered from the per-agent contexts with no separate source index."
  [kb sentence]
  (koinii-types/needs-kb! `co-attribution kb)
  (v/contexts-of kb sentence))
