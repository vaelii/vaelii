;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.client
  "A thin EDN-over-HTTP client for the vaelii daemon (`vaelii.host.serve`).  Runs no
  engine: it POSTs `{:op :args}` and reads the result back, over JDK `java.net.http`
  (no dependency — JDK 21 ships it).

  Every call threads an **explicit connection handle** as its first argument —
  `(query conn '(dog ?x) 'Ctx)` — the network mirror of `vaelii.core`'s explicit-`kb`
  API.  A `conn` from `client` holds a reusable `HttpClient`; no socket opens until a
  call.  A daemon reply of `{:ok false}` becomes an `ex-info` carrying the daemon's
  `:error`, `:type` and `:status`, so a remote naming/disjointness refusal surfaces like
  a local one and the coarse client-fault/server-fault split the status carries is
  readable without writing the request by hand.

  **The bearer token rides on the request the daemon requires it on**: the `conn`
  carries it (`VAELII_API_TOKEN` unless `:token` says otherwise) and every call sets one
  more header on the builder it was already using.  No dependency, no client state, and
  the `conn` is still a map you can read.

  **One wrapper per op, and they are generated** (`vaelii.regen-client`, `lein
  regen-client`).  The daemon's op table is the single source — an op is a `vaelii.core`
  fn with the KB supplied — so a wrapper here is that fn's own spelling, bare or
  `!`-marked exactly as `vaelii.core` spells it, at its own arities with `kb` replaced by
  `conn`.  It is generated at *build* time rather than macroexpanded from `serve/ops`,
  because requiring the table would pull the engine, jetty and reitit onto the classpath
  of a namespace whose whole point is not needing them.  `client_surface_test` compares
  this file against what the generator would write now, so an op added to the daemon
  fails the suite until the wrapper is written."
  (:refer-clojure :exclude [assert isa?])
  (:require [clojure.edn :as edn]
            [vaelii.host.guard :as guard]
            ;; the option-map entry point.  A leaf on `clojure.string` alone, like `guard`
            ;; beside it, so requiring it costs this namespace none of the independence
            ;; the generated wrappers exist to keep
            [vaelii.impl.opts :as opts])
  (:import [java.net URI]
           [java.net.http HttpClient HttpClient$Builder
            HttpRequest HttpRequest$Builder HttpRequest$BodyPublishers
            HttpResponse HttpResponse$BodyHandlers]
           [java.time Duration]))

(def ^:private client-opt-keys
  "Every key `client` reads."
  #{:timeout-ms :token :digests?})

(defn client
  "A connection handle to a daemon at `host`:`port` (opts: `:timeout-ms`, default
  30000).  Holds a reusable `HttpClient`; no network happens until a call.

  `:token` is the bearer token every call presents.  Omitted, it is `VAELII_API_TOKEN`
  (`guard/api-token`), the variable the daemon reads; an explicit nil sends no
  `Authorization` header, which is what an open daemon wants.  `:digests? true` asks
  every reply to carry each sentex's content `:digest` (docs/operations.md, \"Daemon\").
  Another key, or a non-map `opts`, is refused (`:unknown-option`)."
  ([host port] (client host port {}))
  ([host port {:keys [timeout-ms] :or {timeout-ms 30000} :as opts}]
   (opts/check! opts client-opt-keys "client"
                (str "A misspelt :token is not an explicit nil — the conn falls back to"
                     " VAELII_API_TOKEN, so a caller meaning to present a different"
                     " credential, or none, presents the environment's instead."))
   (let [^HttpClient$Builder b (HttpClient/newBuilder)]
     (.connectTimeout b (Duration/ofMillis timeout-ms))
     {:base-url   (str "http://" host ":" port)
      :timeout-ms timeout-ms
      :token      (if (contains? opts :token) (:token opts) (guard/api-token))
      :digests?   (true? (:digests? opts))
      :http       (.build b)})))

(defn- with-token
  "Set `conn`'s bearer token on the request builder, when it holds one.  One `.header`
  call on the builder each call already makes — the whole of what carrying a credential
  costs this client.

  **The refusal never quotes the token.**  `VAELII_API_TOKEN` is the token byte for byte
  and untrimmed (`guard/api-token`), so a value carrying a trailing newline or a control
  character — a secret read out of a file, or injected by a process manager that kept the
  line ending — reaches the JDK, which **quotes a rejected header value verbatim** in the
  `IllegalArgumentException` it raises.  That exception travels: into the log of whatever
  process holds the `conn`, and out of every call this client makes.  So the throw is
  replaced by one that names the variable and never the value.

  `:unknown-option` is the type, the same one `guard/max-body-bytes` throws for a
  `VAELII_*` variable holding a value this build cannot use — the token is a `conn`
  option (`client-opt-keys`), and this is that option outside its domain."
  ^HttpRequest$Builder [^HttpRequest$Builder rb conn]
  (when-let [token (:token conn)]
    (try
      (.header rb "authorization" (str "Bearer " token))
      (catch IllegalArgumentException _
        (throw (ex-info (str "the bearer token holds a character an HTTP header cannot "
                             "carry — VAELII_API_TOKEN is read untrimmed, so a trailing "
                             "newline or a control character in it is the usual cause")
                        {:type :unknown-option :mismatch :bad-value :option :token})))))
  rb)

(defn- read-reply
  "Parse a daemon reply body, or refuse it typed.  `status` is the HTTP status it came
  back under, and it is carried on the refusal.

  The daemon answers EDN; anything else on the wire came from something that is not the
  daemon — a proxy's HTML error page, a truncated body — and reading it raised a bare
  `RuntimeException` with no `:type`, or handed back `nil`, which then read as
  `{:ok nil}` and threw \"vaelii daemon: \" with no message and no type.  `Throwable`,
  because a deeply nested reply overflows the reader's stack.

  **The status is on the refusal because it is what names the thing that answered.**  A
  proxy's 502 and a daemon that answered 200 with a truncated body are one `:bad-reply`
  to a caller reading the body alone.  They have different causes — a hop between the
  caller and the daemon in the first, the daemon in the second — and the status is the
  only field that separates them, since this is the one reply the `:type` vocabulary
  does not reach: it came from something other than a daemon."
  [^String body status]
  (let [form (try (edn/read-string body)
                  (catch Throwable t
                    (throw (ex-info (str "the daemon's reply does not read as EDN"
                                         " (HTTP " status "): " (.getMessage t))
                                    {:type :bad-reply :status status :body body}))))]
    (if (map? form)
      form
      (throw (ex-info (str "the daemon's reply is not a map (HTTP " status "): "
                           (pr-str form))
                      {:type :bad-reply :status status :reply form})))))

(defn- send-edn
  "POST `body` (an EDN string) to `path` and return `[status reply-map]` — the HTTP
  status beside the parsed EDN, since `call` puts the status on the refusal it builds.
  `timeout-ms` overrides the `conn`'s, which is what a long `:poll` needs: the daemon
  holds the request open for its wait, and a read timeout shorter than that would fail
  every poll that had nothing to report."
  ([conn path body] (send-edn conn path body (:timeout-ms conn)))
  ([conn path body timeout-ms]
   (let [^HttpClient http (:http conn)
         ^HttpRequest$Builder rb (HttpRequest/newBuilder (URI/create (str (:base-url conn) path)))]
     (.timeout rb (Duration/ofMillis (long timeout-ms)))
     (.header rb "content-type" "application/edn")
     (with-token rb conn)
     (.POST rb (HttpRequest$BodyPublishers/ofString ^String body))
     (let [^HttpResponse resp (.send http (.build rb) (HttpResponse$BodyHandlers/ofString))]
       [(.statusCode resp) (read-reply (.body resp) (.statusCode resp))]))))

(defn call
  "POST `{:op op :args args}` and return the `:result`, or throw `ex-info` on an
  `{:ok false}` reply.  The low-level entry the convenience fns wrap; use it for an op
  with no wrapper yet.

  `opts` is `{:timeout-ms n}` for this call alone, which only the long `:poll` needs —
  everything else answers inside the `conn`'s own timeout.

  **The refusal carries `:status`**, the HTTP status the daemon answered under.  A
  caller discriminates on `:type` — that is the one vocabulary `docs/operations.md`
  promises — and the status is the coarse split under it: the caller's mistake at 4xx,
  the daemon's fault at 5xx.  Without it that split is a fact only a caller writing its
  own HTTP could read, and a `:type` outside the daemon's request-refusal types
  reaches this client looking exactly like one inside it."
  ([conn op args] (call conn op args nil))
  ([conn op args {:keys [timeout-ms]}]
   (let [body           (cond-> {:op op :args (vec args)} (:digests? conn) (assoc :digests? true))
         [status reply] (send-edn conn "/op" (guard/edn-str body) (or timeout-ms (:timeout-ms conn)))]
     (if (:ok reply)
       (:result reply)
       ;; the daemon's own `:type` when it sent one, so a caller discriminates on the one
       ;; vocabulary `docs/operations.md` promises; `:daemon-error` when it did not, since
       ;; this is the one `ex-info` in the tree that could carry no `:type` at all.
       ;; `or` rather than `merge` defaults: a reply carrying `:type nil` — the key
       ;; present, the value useless — must not defeat the fallback.
       (throw (ex-info (str "vaelii daemon: "
                            (or (:error reply)
                                (str "refused " (pr-str op) " and sent no :error — the"
                                     " reply held " (pr-str (dissoc reply :ok)))))
                       (-> (assoc reply :op op :args (vec args) :status status)
                           (update :type #(or % :daemon-error)))))))))

(defn health
  "The daemon's liveness reply, `{:ok true}` — a GET, so it needs no op, and the one
  route a daemon answers without the token (`serve/open-routes`).  The header is sent
  when the `conn` holds one all the same: a probe that authenticates where it can is no
  worse off, and this way one code path builds every request."
  [conn]
  (let [^HttpClient http (:http conn)
        ^HttpRequest$Builder rb (HttpRequest/newBuilder (URI/create (str (:base-url conn) "/health")))]
    ;; a read timeout, the same one every other request carries: a probe is the one
    ;; call that most needs to fail rather than hang, and a daemon wedged with its
    ;; single writer held answers the handshake and then nothing.
    (.timeout rb (Duration/ofMillis (long (:timeout-ms conn))))
    (with-token rb conn)
    (.GET rb)
    (let [^HttpResponse resp (.send http (.build rb) (HttpResponse$BodyHandlers/ofString))]
      (read-reply (.body resp) (.statusCode resp)))))

;; ---- the vaelii.core surface, conn-first --------------------------------
;; Each threads `conn` and forwards the same args the in-process fn takes.  A sentex
;; result comes back as a plain map (the daemon projects the record), a solution as a
;; binding map — the same shapes `vaelii.core` returns.
;;
;; Nothing between the two markers below is hand-written.

;; ---- generated: one wrapper per daemon op, from serve/ops ---------------

(defn ^:daemon-op abduce
  "What would have to be true for `goal` to be provable in `context`."
  ([conn goal] (call conn :abduce [goal]))
  ([conn goal context] (call conn :abduce [goal context]))
  ([conn goal context opts] (call conn :abduce [goal context opts])))

(defn ^:daemon-op abduce-discard!
  "Discard an abduction's scratch context — every hypothesis in it, and everything they
  licensed."
  [conn result]
  (call conn :abduce-discard [result]))

(defn ^:daemon-op add-provenance
  "Merge `m` into `handle`'s provenance map (creating it if absent), returning the merged
  map."
  [conn handle m]
  (call conn :add-provenance [handle m]))

(defn ^:daemon-op all-functional-at-instant-violations
  "Audit every `(functional_at_instant f)` declaration visible in `context`, and return `{f
  #{violation…} …}` — declarations that clash nowhere are omitted, so an empty map is a
  clean sweep."
  [conn context]
  (call conn :all-functional-at-instant-violations [context]))

(defn ^:daemon-op all-specified-violations
  "Audit every binary `predAllSpecified` and `predSpecifiedAll` declaration visible in
  `context`, each stored one in every known reader seeing its GAF and an ordinary defining
  home, and every *Exists* declaration (`exists-violations`, keyed `[functor pred a b]`),
  and return `{[functor pred indep] result…}`, each result `{:status :audited :violations
  #{…}}` or a `{:status :gap …}` diagnostic (`:missing-slot-typing`,
  `:incomplete-defining-contexts`, or `:legacy-ternary-declaration` keyed by its whole
  argument tuple)."
  [conn context]
  (call conn :all-specified-violations [context]))

(defn ^:daemon-op argue
  "Four-valued epistemic status of a ground assertion."
  ([conn asent context] (call conn :argue [asent context]))
  ([conn asent context opts] (call conn :argue [asent context opts])))

(defn ^:daemon-op ask
  "Answer `goal` in `context` with the pluggable prover engine: stored facts, taxonomy
  closures, disjointness, predicate metadata, evaluables, NAF, argument-type inference and
  any prover the application added."
  ([conn goal] (call conn :ask [goal]))
  ([conn goal context] (call conn :ask [goal context]))
  ([conn goal context opts] (call conn :ask [goal context opts])))

(defn ^:daemon-op ask-within
  "Anytime `ask`: answer `goal` in `context`, bounded by `budget`, a map of any of
  `{:max-ms n :max-results n :max-cost <tier>}`."
  ([conn goal budget] (call conn :ask-within [goal budget]))
  ([conn goal context budget] (call conn :ask-within [goal context budget])))

(defn ^:daemon-op ask?
  "Is `goal` answerable via the prover engine? `ask`'s caveats are this one's too — in
  particular it expands no rule."
  ([conn goal] (call conn :ask? [goal]))
  ([conn goal context] (call conn :ask? [goal context]))
  ([conn goal context opts] (call conn :ask? [goal context opts])))

(defn ^:daemon-op assert
  "Assert `sentence` in `context` (default 'CxUniverse) as a JTMS premise: enforce naming,
  arg and disjointness constraints, persist, index, mark IN, integrate into the taxonomy
  and rule index, then forward-chain."
  ([conn sentence] (call conn :assert [sentence]))
  ([conn sentence context] (call conn :assert [sentence context]))
  ([conn sentence context opts] (call conn :assert [sentence context opts])))

(defn ^:daemon-op assert-many
  "Assert every sentence in `sentences` (into one shared `context`, optional shared `opts`)
  with belief settled **once** at the end: the collection form of `with-deferred-settle`."
  ([conn sentences context] (call conn :assert-many [sentences context]))
  ([conn sentences context opts] (call conn :assert-many [sentences context opts])))

(defn ^:daemon-op assert-rule
  "Assert a rule (a sentex whose sentence is an implication) in `context`."
  ([conn antecedents consequent] (call conn :assert-rule [antecedents consequent]))
  ([conn antecedents consequent context] (call conn :assert-rule [antecedents consequent context]))
  ([conn antecedents consequent context opts] (call conn :assert-rule [antecedents consequent context opts])))

(defn ^:daemon-op belief-status
  "Explain `handle`'s belief and visibility from `context` as a deterministic map: storage,
  raw JTMS IN, context-visible exception force, withdrawal from `context`,
  assertion-context inheritance, and the terminal answers `:believed?` / `:visible?`."
  [conn handle context]
  (call conn :belief-status [handle context]))

(defn ^:daemon-op believed
  "The subset of `handles` `in?` answers true for, as a set — `in?` asked of many handles
  at once."
  [conn handles]
  (call conn :believed [handles]))

(defn ^:daemon-op believed?
  "Is `handle` JTMS IN and not withdrawn from `context` — hidden by the `(except ...)`
  cascade visible from it, the target of a placed `defeat` in force there, or resting only
  on such a handle (docs/nmtms.md, \"A defeat is scoped to its vantage\")?"
  [conn handle context]
  (call conn :believed? [handle context]))

(defn ^:daemon-op blocked-justifications
  "The ids of the justifications the network currently holds **blocked**: a block their
  rule carries holds (a closed extent, a withdrawn `different`), so they confer nothing
  even with every antecedent IN (docs/exceptions.md)."
  [conn]
  (call conn :blocked-justifications []))

(defn ^:daemon-op caches
  "What this process is holding beside the stores: every derived structure the engine
  caches, ranked by entries."
  [conn]
  (call conn :caches []))

(defn ^:daemon-op calculi
  "The shipped qualitative calculi as data — one map apiece, naming the calculus, the base
  relations it distinguishes (jointly exhaustive and pairwise disjoint, so exactly one
  holds of any two terms), the identity it puts on the diagonal, and the predicates it
  claims."
  [conn]
  (call conn :calculi []))

(defn ^:daemon-op canonical-sentex
  "The canonical sentex for `sentence` in `context`, **without storing it**: the un-stored
  counterpart of `sentex`, built through the store's own constructor, so it is the form
  `assert` would key on (docs/canonicalization.md)."
  [conn sentence context]
  (call conn :canonical-sentex [sentence context]))

(defn ^:daemon-op chain-report
  "Per forward rule, what forward chaining did with it: how many firings it **placed**, how
  many it **refused** and why, or whether it did nothing."
  [conn]
  (call conn :chain-report []))

(defn ^:daemon-op chain-stats
  "Chaining-run instrumentation: `{:runs n :last {:derived n :truncated? bool}}`."
  [conn]
  (call conn :chain-stats []))

(defn ^:daemon-op check
  "Would `(assert kb sentence context opts)` succeed, and if not, why? Returns a vector of
  problems, empty when the sentence is admissible, and stores nothing."
  ([conn sentence] (call conn :check [sentence]))
  ([conn sentence context] (call conn :check [sentence context]))
  ([conn sentence context opts] (call conn :check [sentence context opts])))

(defn ^:daemon-op check-edit
  "`check` over a whole `edit` batch, `{:add [[sentence context opts?] …] :remove [handle
  …]}`, storing nothing."
  [conn batch]
  (call conn :check-edit [batch]))

(defn ^:daemon-op clear-caches
  "Drop every cache that offers a clear, and say what went: `{:cleared [{:cache :label
  :entries}…] :entries total}`."
  ([conn] (call conn :clear-caches []))
  ([conn opts] (call conn :clear-caches [opts])))

(defn ^:daemon-op common-genls
  "The supertypes **every** type in `types` has, a collection of types: the intersection of
  their `genls`."
  ([conn types] (call conn :common-genls [types]))
  ([conn types context] (call conn :common-genls [types context])))

(defn ^:daemon-op common-specs
  "The subtypes **every** type in `types` has: the intersection of their `specs`."
  ([conn types] (call conn :common-specs [types]))
  ([conn types context] (call conn :common-specs [types context])))

(defn ^:daemon-op compare-tacticians
  "Run `goal` in `context` under several **tacticians** (the node engine's search
  orderings), each to completion, and return one row per tactician: the search it ran, its
  wall-clock `:ms`, its `:status`, its `:unenumerated` and its answer set."
  ([conn goal] (call conn :compare-tacticians [goal]))
  ([conn goal context] (call conn :compare-tacticians [goal context]))
  ([conn goal context opts] (call conn :compare-tacticians [goal context opts])))

(defn ^:daemon-op conflicts
  "The contradictions the last settle could not satisfy: irreducible clashes among
  known-true content, two `:monotonic` beliefs that cannot both hold."
  ([conn] (call conn :conflicts []))
  ([conn opts] (call conn :conflicts [opts])))

(defn ^:daemon-op context-down
  "The contexts that inherit from `c`, reflexively — `c` plus every context that sees it."
  [conn c]
  (call conn :context-down [c]))

(defn ^:daemon-op context-up
  "The contexts `c` inherits from, reflexively — `c` plus everything it *sees* via
  `genlCx`."
  [conn c]
  (call conn :context-up [c]))

(defn ^:daemon-op contexts
  "Every context currently in the genlCx hierarchy — the nodes of the closure."
  [conn]
  (call conn :contexts []))

(defn ^:daemon-op contexts-of
  "The contexts in which `sentence` is stored **and believed** — a read through
  `sentexes-matching`, so the context of a defeated or unsupported sentex is not listed."
  [conn sentence]
  (call conn :contexts-of [sentence]))

(defn ^:daemon-op contradictions
  "The coexisting pairs the last settle left standing: represented dilemmas, not failures."
  ([conn] (call conn :contradictions []))
  ([conn context] (call conn :contradictions [context]))
  ([conn context opts] (call conn :contradictions [context opts])))

(defn ^:daemon-op count-in-context
  "How many sentexes are **stored** in `context` — one set-size read, O(1), nothing
  fetched."
  [conn context]
  (call conn :count-in-context [context]))

(defn ^:daemon-op count-with-arg
  "How many fact sentexes hold `term` at argument position `pos`, as **stored** — cheap,
  one O(1) set-size read per predicate declaring an argument at that slot."
  [conn pos term]
  (call conn :count-with-arg [pos term]))

(defn ^:daemon-op count-with-functor
  "How many fact sentexes with functor `pred` are **stored** — one set-size read, O(1)."
  [conn pred]
  (call conn :count-with-functor [pred]))

(defn ^:daemon-op covers-of
  "The believed `covering`, `separating` and `partition` sentexes whose whole is `whole`,
  in every context, as a set of `[kind parts]`: `kind` is `:covering`, `:separating` or
  `:partition`, and `parts` is the declared part vector, deduplicated and sorted by
  printed name."
  [conn whole]
  (call conn :covers-of [whole]))

(defn ^:daemon-op defeat-class
  "The current defeat-class of a believed handle (:monotonic / :default), or nil when it is
  OUT — the effective strength of the belief after settling."
  [conn handle]
  (call conn :defeat-class [handle]))

(defn ^:daemon-op defining-contexts
  "The maximal contexts of ordinary believed assertions about term."
  [conn term]
  (call conn :defining-contexts [term]))

(defn ^:daemon-op dependent-justifications
  "Justifications that use `handle` as an antecedent, in content order as
  `supporting-justifications` is: what rests on it, as an impact analysis before a
  `retract!` asks."
  [conn handle]
  (call conn :dependent-justifications [handle]))

(defn ^:daemon-op deprecated?
  "Did a believed `rewriteOf` name `term` the dispreferred side? False for a `sameAs` or
  `equals` member: those merge without retiring either name."
  ([conn term] (call conn :deprecated? [term]))
  ([conn term context] (call conn :deprecated? [term context])))

(defn ^:daemon-op describe
  "Everything the KB holds about one term, as one map, keyed by the term's own role
  (`term-role`; stored content overrides it, `described-role`)."
  ([conn term] (call conn :describe [term]))
  ([conn term context] (call conn :describe [term context]))
  ([conn term context opts] (call conn :describe [term context opts])))

(defn ^:daemon-op digest
  "The **content digest** of a sentex: `\"sha256:\"` and the lowercase hex SHA-256 of its
  context, sign and canonical sentence (docs/storage.md, \"Content digests\")."
  ([conn handle] (call conn :digest [handle]))
  ([conn sentence context] (call conn :digest [sentence context])))

(defn ^:daemon-op digests
  "`(mapv #(digest kb %) handles)`, digesting each record a chain of references names once."
  ([conn handles] (call conn :digests [handles]))
  ([conn handles opts] (call conn :digests [handles opts])))

(defn ^:daemon-op direct-genls
  "The types `t` is a subtype of by **one** `genl` edge in the closure — its direct
  parents, where `genls` is everything they reach."
  ([conn t] (call conn :direct-genls [t]))
  ([conn t context] (call conn :direct-genls [t context])))

(defn ^:daemon-op direct-specs
  "The types that are a subtype of `t` by **one** `genl` edge in the closure — its direct
  children."
  ([conn t] (call conn :direct-specs [t]))
  ([conn t context] (call conn :direct-specs [t context])))

(defn ^:daemon-op disjoint-metatypes
  "The declared disjoint metatypes — each a type whose member types are pairwise disjoint
  by `(disjoint_metatype M)`."
  [conn]
  (call conn :disjoint-metatypes []))

(defn ^:daemon-op disjoint?
  "Are types `a` and `b` provably disjoint (via disjoint declarations, closed under genl)?
  With a `context`, only declarations and genl edges visible from it count — the vantage
  every definitional check now judges from."
  ([conn a b] (call conn :disjoint? [a b]))
  ([conn a b context] (call conn :disjoint? [a b context])))

(defn ^:daemon-op edit!
  "Apply a batch of assertions and retractions in **one settle**."
  ([conn batch] (call conn :edit [batch]))
  ([conn batch opts] (call conn :edit [batch opts])))

(defn ^:daemon-op edit-with-consequences!
  "`edit`, plus what the batch turned out to **mean**: the belief it added and took away,
  in `preview`'s entry shapes."
  ([conn batch] (call conn :edit-with-consequences [batch]))
  ([conn batch opts] (call conn :edit-with-consequences [batch opts])))

(defn ^:daemon-op equiv-class
  "Every term known equal to `term`, itself included."
  ([conn term] (call conn :equiv-class [term]))
  ([conn term context] (call conn :equiv-class [term context])))

(defn ^:daemon-op escalate
  "The cheapest level that answers `goal`: climb from `floor` and stop at the first level
  with results."
  ([conn goal] (call conn :escalate [goal]))
  ([conn goal context] (call conn :escalate [goal context]))
  ([conn goal context floor] (call conn :escalate [goal context floor]))
  ([conn goal context floor opts] (call conn :escalate [goal context floor opts])))

(defn ^:daemon-op exists-violations
  "The audit result for one *Exists* declaration in `context`, `{:status :audited
  :violations #{x…}}`: for `(predAllExists pred indep dep)` each member x of `indep` with
  no believed `(pred x y)` whose y is a member of `dep`; for `(predExistsAll pred dep
  indep)` each member x of `indep` with no believed `(pred y x)` whose y is a member of
  `dep`; for `(predExistsInstance pred indep fixed)` and `(predInstanceExists pred fixed
  dep)` the fixed term when no such tuple bears to it or from it."
  [conn declaration context]
  (call conn :exists-violations [declaration context]))

(defn ^:daemon-op explain-levels
  "What every level yields for `goal`: a seq of {:level :name :count}."
  ([conn goal] (call conn :explain-levels [goal]))
  ([conn goal context] (call conn :explain-levels [goal context])))

(defn ^:daemon-op export!
  "Write `kb` out as a portable **export dump** in `dir` and return a summary:"
  ([conn dir] (call conn :export [dir]))
  ([conn dir opts] (call conn :export [dir opts])))

(defn ^:daemon-op exposed-clashes
  "Every disjointness clash the KB currently makes jointly visible: a term holding two
  types some context can see as disjoint, where each membership was admissible where it
  was written."
  [conn]
  (call conn :exposed-clashes []))

(defn ^:daemon-op filed-violations
  "The filed ledger alone: the entries `violations` begins with, in its order, without the
  `:forced-conclusion`, `:inert-argument` and `:inert-rule` entries it reads off the
  stored firings and held sentexes."
  [conn]
  (call conn :filed-violations []))

(defn ^:daemon-op find-sentexes
  "Every stored sentex that contains `term` anywhere (any position, any nesting)."
  [conn term]
  (call conn :find-sentexes [term]))

(defn ^:daemon-op find-sentexes-all
  "Every stored sentex that contains all of `terms`."
  [conn terms]
  (call conn :find-sentexes-all [terms]))

(defn ^:daemon-op find-terms
  "The vocabulary terms whose name matches `q`, sorted by name."
  ([conn q] (call conn :find-terms [q]))
  ([conn q opts] (call conn :find-terms [q opts])))

(defn ^:daemon-op forward-chain
  "Run forward chaining to a fixpoint over every believed sentex, then settle belief."
  ([conn] (call conn :forward-chain []))
  ([conn opts] (call conn :forward-chain [opts])))

(defn ^:daemon-op functional-at-instant-violations
  "The per-instant functionality clashes of one `(functional_at_instant f)` declaration in
  `context`, as a set of maps `{:function f :subject s :instant t :values #{v…} :kind k}`,
  one per moment `t` at which more than one distinct value of the fluent function `f`
  holds for one subject `s`."
  [conn f context]
  (call conn :functional-at-instant-violations [f context]))

(defn ^:daemon-op genl?
  "Is `sub` a (reflexive-transitive) subtype of `super`? Types, not individuals — for an
  individual's type membership use `isa?`."
  ([conn sub super] (call conn :genl? [sub super]))
  ([conn sub super context] (call conn :genl? [sub super context])))

(defn ^:daemon-op genls
  "The supertypes of type `t`, reflexively — `t` itself plus everything reachable from it
  by `genl`."
  ([conn t] (call conn :genls [t]))
  ([conn t context] (call conn :genls [t context])))

(defn ^:daemon-op handle-of
  "The handle of the sentex already storing `sentence` in `context`, or **nil**."
  [conn sentence context]
  (call conn :handle-of [sentence context]))

(defn ^:daemon-op handles
  "Every live sentex handle in the KB, premises and forward-derived alike, read off the
  record store."
  [conn]
  (call conn :handles []))

(defn ^:daemon-op has-prop?
  "Does `pred` carry the metadata property `kind`? `vaelii.impl.predicates/prop-kinds`
  enumerates the kinds (docs/api.md)."
  ([conn kind pred] (call conn :has-prop? [kind pred]))
  ([conn kind pred context] (call conn :has-prop? [kind pred context])))

(defn ^:daemon-op in?
  "Is the sentex handle believed as the context it is stored in reads it: JTMS IN, and not
  hidden there by a placed `defeat` in force there or by resting only on a handle one
  hides (docs/nmtms.md, \"A read with no reader\")? Visibility `except`s are not applied."
  [conn handle]
  (call conn :in? [handle]))

(defn ^:daemon-op inverse-of
  "The predicate declared inverse to `pred` by an `(inverse P Q)` sentex, or nil."
  ([conn pred] (call conn :inverse-of [pred]))
  ([conn pred context] (call conn :inverse-of [pred context])))

(defn ^:daemon-op isa?
  "Is individual `x` (transitively) of type `t`? Considers only type memberships visible
  from `context` (default: any context)."
  ([conn x t] (call conn :isa? [x t]))
  ([conn x t context] (call conn :isa? [x t context])))

(defn ^:daemon-op justification
  "The justification for an id, or nil — nil in, nil out; a non-id is refused
  (`:bad-handle`)."
  [conn jid]
  (call conn :justification [jid]))

(defn ^:daemon-op justification-verdicts
  "The verdict `context` reads on each justification of `handle`, as `{justification-id
  reason}`: `:supports` where every handle it rests on is believed there, else
  `:antecedent-out`, unless the network blocks it (`:blocked`, its rule's `exceptWhen`
  holds) or holds it void (`:void`), `context`'s forced-monotonic reading holds it void
  (`:void`), a guard defeat in force at `context` covers it (`:guard`, docs/naf.md), or it
  is a `nogood` justification of a placement `context` exempts (`:exempt`)."
  [conn handle context]
  (call conn :justification-verdicts [handle context]))

(defn ^:daemon-op kb-diff
  "What two KBs disagree about, as content: `{:added :removed :moved :belief-changed}`."
  [conn b]
  (call conn :kb-diff [b]))

(defn ^:daemon-op kb-integrity
  "Run the bounded, read-only integrity sweep in `context`."
  ([conn candidate-terms context] (call conn :kb-integrity [candidate-terms context]))
  ([conn candidate-terms context options] (call conn :kb-integrity [candidate-terms context options])))

(defn ^:daemon-op kb-quality
  "Seven readings about the knowledge, one map with the keys `:rules`, `:extents`,
  `:chains`, `:taxonomy`, `:declarations`, `:subsumption` and `:clashes`, each a
  distribution rather than a number (shapes: docs/quality.md, \"The result map\")."
  ([conn] (call conn :kb-quality []))
  ([conn opts] (call conn :kb-quality [opts])))

(defn ^:daemon-op last-program
  "The last edge `Program` handed to the solver — the contested assumptions and the nogoods
  among them — or nil if no tie has ever been arbitrated."
  [conn]
  (call conn :last-program []))

(defn ^:daemon-op levels
  "The stack as data: {:level :name :below :adds} per level."
  [conn]
  (call conn :levels []))

(defn ^:daemon-op lookup
  "Answer `goal` in `context` using exactly the machinery of `level`:"
  ([conn level goal] (call conn :lookup [level goal]))
  ([conn level goal context] (call conn :lookup [level goal context])))

(defn ^:daemon-op max-common-specs
  "The **maximal** common subtypes of `types`: the members of `common-specs` that are no
  member of `types` and have no other such member strictly above them."
  ([conn types] (call conn :max-common-specs [types]))
  ([conn types context] (call conn :max-common-specs [types context])))

(defn ^:daemon-op max-context-children
  "The **maximal** contexts that inherit from context `c`: the contexts that reach `c` over
  one `genlCx` edge with no other such context strictly above them."
  [conn c]
  (call conn :max-context-children [c]))

(defn ^:daemon-op max-specs
  "The **maximal** subtypes of type `t`: its direct children (`direct-specs`) with no other
  direct child of `t` strictly above them."
  ([conn t] (call conn :max-specs [t]))
  ([conn t context] (call conn :max-specs [t context])))

(defn ^:daemon-op metatype-members
  "The member types of disjoint metatype `m` — the set whose every pair `disjoint?` holds
  of, closed under genl."
  [conn m]
  (call conn :metatype-members [m]))

(defn ^:daemon-op min-common-genls
  "The **minimal** common supertypes of `types`: the members of `common-genls` that are no
  member of `types` and have no other such member strictly below them."
  ([conn types] (call conn :min-common-genls [types]))
  ([conn types context] (call conn :min-common-genls [types context])))

(defn ^:daemon-op min-context-parents
  "The **minimal** contexts context `c` inherits from: the contexts `c` reaches over one
  `genlCx` edge with no other such context strictly below them."
  [conn c]
  (call conn :min-context-parents [c]))

(defn ^:daemon-op min-genls
  "The **minimal** supertypes of type `t`: its direct parents (`direct-genls`) with no
  other direct parent of `t` strictly below them."
  ([conn t] (call conn :min-genls [t]))
  ([conn t context] (call conn :min-genls [t context])))

(defn ^:daemon-op owed-releases
  "How many departures and arrivals the settles of an open, a recover, an upgrade or a bulk
  load left owed: the general argument-type mints a departed specific membership had
  withheld are not drawn until `release-withheld!` runs, so the KB may miss them."
  [conn]
  (call conn :owed-releases []))

(defn ^:daemon-op possible-relations
  "The base relations `calculus` still allows between `a` and `b`, given everything
  believed in `context` — the set `ask` checks a goal against, exposed directly."
  [conn calculus context a b]
  (call conn :possible-relations [calculus context a b]))

(defn ^:daemon-op premise?
  "Is the sentex at `handle` a **premise** — asserted in its own right rather than derived?
  A premise rests on nothing, so no justification names it as a conclusion and retracting
  its supports cannot take it OUT; a derived sentex is the other case, and
  `supporting-justifications` is what shows why."
  [conn handle]
  (call conn :premise? [handle]))

(defn ^:daemon-op preview
  "What would this batch do to the KB, **without** leaving it done."
  ([conn batch] (call conn :preview [batch]))
  ([conn batch opts] (call conn :preview [batch opts])))

(defn ^:daemon-op props
  "The set of predicates carrying metadata property `kind` (see `has-prop?`)."
  [conn kind]
  (call conn :props [kind]))

(defn ^:daemon-op provable?
  "Is `goal` provable in `context`? Takes `prove`'s goal; a conjunction is provable iff all
  its conjuncts are, under one consistent binding."
  ([conn goal] (call conn :provable? [goal]))
  ([conn goal context] (call conn :provable? [goal context]))
  ([conn goal context opts] (call conn :provable? [goal context opts])))

(defn ^:daemon-op prove
  "Backward-chain in `context` with the DFS prover; returns a vector of solution binding
  maps, type-aware and visible from `context`."
  ([conn goal] (call conn :prove [goal]))
  ([conn goal context] (call conn :prove [goal context]))
  ([conn goal context opts] (call conn :prove [goal context opts])))

(defn ^:daemon-op prove-within
  "Anytime `prove`: run the depth-first backward chainer over `goal` (a sentence or a
  conjunction vector, as `prove`) in `context`, bounded by `budget`, a map of any of
  `{:max-ms n :max-results n :max-depth n :max-term-growth n}`."
  ([conn goal budget] (call conn :prove-within [goal budget]))
  ([conn goal context budget] (call conn :prove-within [goal context budget])))

(defn ^:daemon-op provenance
  "The provenance map recorded for `handle` — `{:creator … :created … …}` — or nil if none."
  [conn handle]
  (call conn :provenance [handle]))

(defn ^:daemon-op qualitative-network
  "The constraint network `calculus` computes over everything **believed and visible** in
  `context`: every pair of terms its predicates relate, tightened by path consistency."
  [conn calculus context]
  (call conn :qualitative-network [calculus context]))

(defn ^:daemon-op qualitative-scenario
  "One concrete arrangement consistent with everything believed in `context`, `{[a b] →
  relation}` with one base relation per pair, or nil when the believed facts are
  unsatisfiable."
  [conn calculus context]
  (call conn :qualitative-scenario [calculus context]))

(defn ^:daemon-op qualitative-scenarios
  "Up to `limit` distinct arrangements, as `qualitative-scenario` renders one."
  [conn calculus context limit]
  (call conn :qualitative-scenarios [calculus context limit]))

(defn ^:daemon-op quality-report
  "A `kb-quality` map as Markdown — the counts first and the capped lists after."
  [conn quality]
  (call conn :quality-report [quality]))

(defn ^:daemon-op query
  "Answer `goal` in `context` as a seq of **binding maps** (`{?x val …}`) projected onto
  the goal's own variables."
  ([conn goal] (call conn :query [goal]))
  ([conn goal context] (call conn :query [goal context]))
  ([conn goal context opts] (call conn :query [goal context opts])))

(defn ^:daemon-op query-plan
  "How a goal would be answered."
  ([conn goal] (call conn :query-plan [goal]))
  ([conn goal context] (call conn :query-plan [goal context])))

(defn ^:daemon-op query-status
  "`query`'s answers, plus a **report** of the run, so a query truncated at the depth bound
  reads differently from one whose goal is unprovable."
  ([conn goal context] (call conn :query-status [goal context]))
  ([conn goal context opts] (call conn :query-status [goal context opts])))

(defn ^:daemon-op query?
  "Is `goal` answerable under `opts`? `query`, asked for one answer: the search stops at
  the first."
  ([conn goal] (call conn :query? [goal]))
  ([conn goal context] (call conn :query? [goal context]))
  ([conn goal context opts] (call conn :query? [goal context opts])))

(defn ^:daemon-op readable-sentence
  "A sentex's sentence with the author's variable names restored — pass a sentex map (from
  `sentex` / `sentexes-matching`)."
  [conn sx]
  (call conn :readable-sentence [sx]))

(defn ^:daemon-op relation-arity
  "The exact number of places that binds `term`, its own or one inherited through `genl`,
  or nil when no exact length binds it (a `variable_arity` relation, or none stored)."
  [conn term]
  (call conn :relation-arity [term]))

(defn ^:daemon-op relation?
  "Is `term` a relation of two or more places by what the KB stores of it, visible from
  `context` (default `?ctx`, every context): an `(arity P n)` declaration or exact-arity
  class membership of two or more, or a `variable_arity` membership, or, where none of
  these answers, a length of two or more inherited through `genl`."
  ([conn term] (call conn :relation? [term]))
  ([conn term context] (call conn :relation? [term context])))

(defn ^:daemon-op replace-facts!
  "Make `facts`, a seq of ground literals, the ground literal premises `context` stores
  that name no sentex, in one `edit!`: a fact not held so, or held weaker than requested,
  is added under `opts`' `assert` keys, and each such premise no fact names is retracted."
  ([conn context facts] (call conn :replace-facts [context facts]))
  ([conn context facts opts] (call conn :replace-facts [context facts opts])))

(defn ^:daemon-op representative
  "The term standing for `term`'s equivalence class — `term` itself when nothing has merged
  it, so this is total and never nil."
  ([conn term] (call conn :representative [term]))
  ([conn term context] (call conn :representative [term context])))

(defn ^:daemon-op retract!
  "Retract premise support for a handle, tear down solely-supported sentexes and
  justifications (keeping anything re-derivable via other witnesses), and reverse their
  taxonomy / rule-index effects."
  [conn handle]
  (call conn :retract [handle]))

(defn ^:daemon-op same-class?
  "Do `a` and `b` denote the same thing? Distinct symbols denote distinct individuals until
  an equality sentex says otherwise."
  ([conn a b] (call conn :same-class? [a b]))
  ([conn a b context] (call conn :same-class? [a b context])))

(defn ^:daemon-op search-tree
  "The backward search for `goal` in `context` as data: every node the frontier reached,
  what each cost and what was dropped."
  ([conn goal] (call conn :search-tree [goal]))
  ([conn goal context] (call conn :search-tree [goal context]))
  ([conn goal context opts] (call conn :search-tree [goal context opts])))

(defn ^:daemon-op sees?
  "Does context `k` see assertions made in context `y`? True iff `y` is in `k`'s genlCx
  up-closure (reflexively, so a context sees itself)."
  [conn k y]
  (call conn :sees? [k y]))

(defn ^:daemon-op sentence-of
  "A sentex map's canonical sentence: a literal's `:sentence`, or for a rule the `(implies
  <antecedent> <consequent>)` form built from its `:antecedent` and `:consequent` — a rule
  map carries no `:sentence` of its own."
  [conn sx]
  (call conn :sentence-of [sx]))

(defn ^:daemon-op sentex
  "The sentex for a handle as a **map**, or nil."
  [conn handle]
  (call conn :sentex [handle]))

(defn ^:daemon-op sentex-count
  "How many sentexes the KB holds, in total — the count the count-aware trie keeps at its
  root, so O(1) and nothing fetched."
  [conn]
  (call conn :sentex-count []))

(defn ^:daemon-op sentexes-in-context
  "Every **stored** sentex asserted in `context` (its extent, rules included), a defeated
  or unsupported one included."
  ([conn context] (call conn :sentexes-in-context [context]))
  ([conn context opts] (call conn :sentexes-in-context [context opts])))

(defn ^:daemon-op sentexes-matching
  "*Believed* sentexes matching `sentence` in `context` (default ?ctx)."
  ([conn sentence] (call conn :sentexes-matching [sentence]))
  ([conn sentence context] (call conn :sentexes-matching [sentence context])))

(defn ^:daemon-op sentexes-naming
  "Every **stored** sentex whose sentence nests `(sentexHandle handle)` — the meta-sentexes
  naming `handle` — a defeated or unsupported one included."
  ([conn handle] (call conn :sentexes-naming [handle]))
  ([conn handle opts] (call conn :sentexes-naming [handle opts])))

(defn ^:daemon-op sentexes-with-arg
  "Every **stored** fact sentex holding `term` at 1-based argument position `pos` — a
  defeated or unsupported one included."
  ([conn pos term] (call conn :sentexes-with-arg [pos term]))
  ([conn pos term opts] (call conn :sentexes-with-arg [pos term opts])))

(defn ^:daemon-op sentexes-with-functor
  "Every **stored** fact sentex whose functor is `pred`, any arity, either polarity — a
  defeated or unsupported one included."
  ([conn pred] (call conn :sentexes-with-functor [pred]))
  ([conn pred opts] (call conn :sentexes-with-functor [pred opts])))

(defn ^:daemon-op separating-covers
  "The believed `separating` and `partition` declarations, as a set of `[whole parts
  kind]`: every two distinct `parts` are disjoint, and `disjoint?` reads them from this
  table."
  [conn]
  (call conn :separating-covers []))

(defn ^:daemon-op settle-stats
  "Instrumentation for the `exceptWhen` fixpoint in `settle`: `{:iterations n :passes n
  :histogram {n count}}`."
  [conn]
  (call conn :settle-stats []))

(defn ^:daemon-op specified-violations
  "The audit result for one binary `(predAllSpecified pred indep)` requirement in
  `context`: `{:status :audited :violations #{x…}}`, every member x of `indep` that
  `context` audits (it sees an ordinary defining home of x, or none is stored) with no
  believed `(pred x y)` whose **determinate** filler y satisfies `pred`'s derived slot
  contract, or a `{:status :gap …}` (`:missing-slot-typing`, or
  `:incomplete-defining-contexts` naming unclassified support)."
  ([conn pred indep context] (call conn :specified-violations [pred indep context]))
  ([conn pred indep context arg-pos] (call conn :specified-violations [pred indep context arg-pos])))

(defn ^:daemon-op specs
  "The subtypes of type `t`, reflexively — `t` itself plus everything that reaches it by
  `genl`."
  ([conn t] (call conn :specs [t]))
  ([conn t context] (call conn :specs [t context])))

(defn ^:daemon-op stored-first-args
  "The terms **stored** at argument 1 of a fact with functor `pred`, as a set: the index's
  own child set under `pred`, one read — no record fetched and no belief consulted, so a
  defeated or unsupported fact's term is in it."
  [conn pred]
  (call conn :stored-first-args [pred]))

(defn ^:daemon-op subsumption-status
  "The subsumption relationship of type `a` to type `b`, one of: `:coextensional` (each is
  `genl` the other), `:genl` (`a` is a subtype of `b`), `:spec` (`a` is a supertype of
  `b`), `:disjoint` (provably no shared instance), `:orthogonal` (see
  `subsumption-statuses`), `:unknown` (none provable) or `:inconsistent` (contradictory
  relationships hold)."
  ([conn a b] (call conn :subsumption-status [a b]))
  ([conn a b context] (call conn :subsumption-status [a b context])))

(defn ^:daemon-op subsumption-statuses
  "The set of applicable subsumption relationships between types `a` and `b`: any subset of
  `#{:coextensional :genl :spec :disjoint :orthogonal}`."
  ([conn a b] (call conn :subsumption-statuses [a b]))
  ([conn a b context] (call conn :subsumption-statuses [a b context])))

(defn ^:daemon-op supporting-justifications
  "Justifications that conclude `handle`, in **content** order
  (`kb/justification-content-key`), so one knowledge base answers identically whatever
  order it arrived in."
  [conn handle]
  (call conn :supporting-justifications [handle]))

(defn ^:daemon-op term-count
  "How many distinct terms the KB's vocabulary holds — one set-size read, O(1), nothing
  fetched."
  [conn]
  (call conn :term-count []))

(defn ^:daemon-op term-expression
  "The functional expression a reified term denotes — `(FruitFn AppleTree)` for the
  constant minted from it — or nil for an ordinary term, and for a reified one whose
  `(natFormula K E)` map is not believed."
  [conn term]
  (call conn :term-expression [term]))

(defn ^:daemon-op terms
  "Every term the index is keyed by: each predicate, individual, type and context name
  mentioned by a stored sentex, at any nesting depth, as a vector sorted by name."
  [conn]
  (call conn :terms []))

(defn ^:daemon-op try-assert
  "`assert`, refusing a sentence that would open a definitional clash with believed content
  visible from `context`."
  ([conn sentence] (call conn :try-assert [sentence]))
  ([conn sentence context] (call conn :try-assert [sentence context]))
  ([conn sentence context opts] (call conn :try-assert [sentence context opts])))

(defn ^:daemon-op types
  "Every type currently in the genl hierarchy — the nodes of the closure, i.e. every type
  named by some believed `genl` edge."
  ([conn] (call conn :types []))
  ([conn context] (call conn :types [context])))

(defn ^:daemon-op types-of
  "The types asserted of individual `x` — functors of unary sentexes (T x), found via the
  term index."
  ([conn x] (call conn :types-of [x]))
  ([conn x context] (call conn :types-of [x context])))

(defn ^:daemon-op unsupported
  "The stored records the last `recover` found with no premise mark, no justification and
  no `:inert` mark, as `{:n n :handles [h …]}`, ascending, re-checked against the KB now:
  a handle since premise-marked, concluded, marked `:inert` or retracted is left out."
  [conn]
  (call conn :unsupported []))

(defn ^:daemon-op violations
  "The ledger of definitional constraints a derived conclusion would have broken during
  forward chaining, and what a bounded pass did not reach: a vector of `{:violation <kind>
  :sentence S :context C :rule handle :run n :detail {…}}`."
  [conn]
  (call conn :violations []))

(defn ^:daemon-op vocabulary-audit
  "Every term core.txt comments in `kb`, classified: `{:enforced [[term why] …] :inert
  [[term why] …] :unclassified [term …] :retired [term …] :contradicted [term …]}`."
  [conn]
  (call conn :vocabulary-audit []))

(defn ^:daemon-op why
  "Why does the KB believe `handle`? The justification graph reachable from `handle`, as
  data:"
  ([conn handle] (call conn :why [handle]))
  ([conn handle opts] (call conn :why [handle opts])))

(defn ^:daemon-op why-not
  "Why does the KB *not* believe `handle`? The complement of `why`, as data: `{:handle h
  :sentence S :context C :believed? false :reason <keyword> …}`, with one `:reason` per
  way a handle goes unbelieved (`:not-stored`, `:superseded`, `:defeated`, `:withdrawn`,
  `:inert`, `:forced-conclusion`, `:unsupported`, `:excepted`, `:closed-extent`)."
  ([conn handle] (call conn :why-not [handle]))
  ([conn sentence context] (call conn :why-not [sentence context]))
  ([conn sentence context opts] (call conn :why-not [sentence context opts])))

;; ---- end generated ------------------------------------------------------

;; ---- the two deprecated spellings ---------------------------------------

(defn ^:deprecated assert!
  "Deprecated spelling of `assert`, which is what `vaelii.core` calls it.  Identical in
  every other respect.  `!` means *irreversible* here (`docs/api.md`) and an assertion is
  neither — `retract!` takes it back — so the wrapper carrying one said the opposite of
  what the entry point does."
  ([conn sentence] (assert conn sentence))
  ([conn sentence context] (assert conn sentence context))
  ([conn sentence context opts] (assert conn sentence context opts)))

(defn ^:deprecated assert-rule!
  "Deprecated spelling of `assert-rule`, which is what `vaelii.core` calls it.  Identical
  in every other respect; see `assert!` for why the `!` went."
  ([conn antecedents consequent]
   (assert-rule conn antecedents consequent))
  ([conn antecedents consequent context]
   (assert-rule conn antecedents consequent context))
  ([conn antecedents consequent context opts]
   (assert-rule conn antecedents consequent context opts)))

;; ---- the change feed, held open with a cursor ----------------------------
;; `core/watch` takes a callback and a callback does not cross an EDN wire, so what a
;; remote caller holds is a subscription the daemon keeps and reads forward with a
;; cursor.  Three calls, the same `{:op :args}` envelope as everything above, and no
;; second wire format — docs/feed.md, "Across the wire".

(def ^:private max-wait-ms
  "The longest the daemon parks a long poll, whatever `:wait-ms` asks for.

  Mirrored here rather than required from `vaelii.host.subscribe`, which would pull the
  whole engine onto the classpath of a client whose whole point is not needing it.  A
  mirrored constant is a constant that drifts, so `client_test` asserts the two agree —
  the coupling is checked rather than assumed."
  30000)

(defn watch
  "Open a change-feed subscription — `{:token t :cursor 0 :max-events n}`.  With no
  goal it is every belief change; with one it is the standing query `core/watch` takes,
  refused identically (`:not-watchable`) when the goal is not answerable from a moved
  region."
  ([conn] (call conn :watch []))
  ([conn goal context] (call conn :watch [goal context])))

(defn poll
  "Read a subscription forward from `cursor` — `{:events [...] :cursor n :lagged k}`.

  `opts` is `{:wait-ms n}`, the long poll: the daemon holds the request open that long
  waiting for the first event.  The read timeout is extended to cover it, which is the
  whole of what a long poll costs this client — no second protocol, no held socket of
  its own, and nothing about the reply changes.

  **`:lagged` is on every reply and is the one field a caller must read**: non-zero, the
  ring dropped that many events before this poll reached them."
  ([conn token cursor] (poll conn token cursor nil))
  ([conn token cursor opts]
   (let [w (:wait-ms opts 0)]
     ;; refused here as well as at the daemon, so a bad value names the option instead of
     ;; reaching `long` as a bare cast error on the way out
     (when-not (nat-int? w)
       (throw (ex-info (str "poll :wait-ms must be a whole number of milliseconds, got "
                            (pr-str w))
                       {:type :unknown-option :mismatch :bad-value :options [:wait-ms]})))
     ;; extended by what the daemon will actually wait, not by what was asked for: the
     ;; wait is capped there, so a caller asking for ten minutes would otherwise hold its
     ;; own socket open for ten minutes against a reply that came in thirty seconds
     (call conn :poll (if opts [token cursor opts] [token cursor])
           {:timeout-ms (+ (long (:timeout-ms conn)) (long (min max-wait-ms w)))}))))

(defn unwatch
  "Drop subscription `token`; true if there was one.  Idempotent."
  [conn token] (call conn :unwatch [token]))

(defn watchers
  "What the daemon is holding open — one entry per subscription, with its goal, how many
  events it has been `:delivered`, and how many are still `:pending` on its ring.
  Neither is the *reader's* position, which lives on the client and is a thing the daemon
  has no way to know."
  [conn] (call conn :watchers []))
