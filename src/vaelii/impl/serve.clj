;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.serve
  "Headless EDN-over-HTTP daemon: one JVM owns one KB and serves it to remote clients
  (`vaelii.impl.client`).  A thin reitit-ring + jetty layer over `vaelii.core`, the
  network dual of the in-process API.

  **Wire format is EDN.**  A sentence is a symbol s-expression — `(dog Muffet)`, `?x`,
  `(genl dog animal)` — which EDN round-trips losslessly; JSON would mangle the symbols.
  The body of every call is `{:op <keyword> :args [...]}`, and the reply is
  `{:ok true :result …}` or `{:ok false :error \"…\"}`.  EDN is read with
  `clojure.edn/read-string` (never `clojure.core/read-string`), so an untrusted body
  cannot evaluate code — EDN has no reader-eval.

  **A refusal's `:type` is a plain keyword** — `:body-too-large`, `:not-edn`,
  `:cross-origin`, `:bad-host` — and so is the `:type` an engine `ex-info` carries
  through.  The protocol is what a client written against another build discriminates
  on, so it cannot be qualified by the namespace that happens to serve it: a
  `::`-qualified keyword names *this* namespace, and a client matching on it would be
  matching on where the daemon's code lives.

  **The daemon is the single writer** (docs/storage.md, the single-writer contract): it
  owns the one process allowed to mutate the store, so it serializes every op through
  one monitor.  Concurrent client writes therefore apply one at a time and cannot
  interleave; reads pay the same lock, which is conservative but keeps the contract
  simple.

  **Only the allowlisted ops are reachable** (`ops`).  Each is a `vaelii.core` fn with
  the KB supplied by the daemon — the client sends only the op and the remaining args —
  so no client can reach an arbitrary var.  Sentex records in a result are projected to
  plain maps before they hit the wire (the `sentex`-map contract), so the client reads
  them back without the `impl` record class.

  **The change feed is the one thing that is not a `vaelii.core` fn** (`feed-ops`), and
  it is a table of its own for that reason: `core/watch` takes a callback, so what a
  remote caller holds open instead is a subscription with a **cursor** — `:watch`,
  `:poll`, `:unwatch`, `:watchers`, over the per-handler registry `app` builds
  (`vaelii.impl.subscribe`, docs/feed.md).  A `:poll` that waits runs **outside** the
  monitor; everything else about them is an ordinary EDN op.

  **One shared bearer token authenticates the caller.**  With `VAELII_API_TOKEN` set
  (`guard/api-token`), every request presents `Authorization: Bearer <token>` or is
  answered 401 with a `WWW-Authenticate: Bearer` challenge; `GET /health` is the one
  route that answers without it.  One token for the process, not a session and not an
  identity — per-caller identity is a reverse proxy's job, and this is the check that
  has to exist below it.  Binding anything but loopback **requires** a token (`-main`
  refuses to start otherwise); on the loopback default it is optional, and a daemon
  without one is drivable by every process on the machine.

  `vaelii.impl.guard` covers what a token does not, and matters most on the open
  loopback daemon: `POST /op` requires `Content-Type: application/edn`, refuses a
  cross-origin `Origin`, and answers only to a `Host` naming the interface it was
  started on.  Together those stop a page the operator happens to visit from driving
  the KB over loopback — which binding to loopback alone does not."
  (:require [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [reitit.ring :as ring]
            [ring.adapter.jetty :as jetty]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.config :as config]
            [vaelii.impl.guard :as guard]
            [vaelii.impl.subscribe :as sub])
  (:import [org.eclipse.jetty.server Server ServerConnector]))

;; ---- the op table: the allowlisted vaelii.core surface -------------------
;; op keyword -> (fn [kb args-vector]).  `apply`ing keeps the varying arities
;; (assert's optional context/opts, why-not's two shapes) working unchanged: the
;; client sends exactly the args it would pass in-process, minus the KB.

(defn- op [f] (fn [kb args] (apply f kb args)))

(defn- op*
  "The same, for a `vaelii.core` fn that takes **no KB** — the static rosters and the
  pure renderers (`levels`, `calculi`, `readable-sentence`, `quality-report`).  The
  daemon still supplies a KB to every row, so this one drops it; `kbless-ops` below is
  the roster a caller generating from this table reads, since a closure cannot be asked
  which shape it has."
  [f] (fn [_kb args] (apply f args)))

(def kbless-ops
  "The ops whose `vaelii.core` fn takes no KB (`op*` above).  Held as data rather than
  left implicit in the closures, because two generators read this table and both have to
  know whether an op's first `vaelii.core` parameter is the KB the daemon supplies or an
  argument the caller sends: `vaelii.impl.client`'s wrappers (arity for arity) and
  `vaelii.impl.llm.tools`' schemas (parameter by parameter)."
  #{:levels :calculi :readable-sentence :quality-report})

(defn- wire-handles
  "`core/handles` as a sorted vector.  The whole-KB roster is a `java.util.Set` that is
  deliberately *not* an `IPersistentSet` at scale (`vaelii.impl.roster`), and such a
  value has no EDN print form — it would reach a client as `#object[…]`.  Sorted, so two
  daemons over the same store answer the same bytes."
  [kb] (vec (sort (v/handles kb))))

(defn- without-resume
  "Wrap an anytime read (`ask-within` / `prove-within`) so its partial result crosses the
  wire.  The contract's `:resume` is a **function** closing over an unrealized lazy tail
  or a DFS goal stack, and neither a function nor the heap it pins crosses an EDN wire —
  the same wall `:export`'s `:on-progress` hits.  So the key is dropped and replaced by
  **`:resumable`**, the one bit of it a remote caller can act on: the search had more to
  give, and asking for the rest means a fresh call under a larger budget rather than
  `core/resume`, which is in-process only (docs/anytime.md).

  A boolean rather than a silent omission: a caller writing the documented
  `(when (:resume r) …)` loop against a daemon would otherwise read every partial as
  complete and stop one step in."
  [f]
  (fn [& args]
    (let [r (apply f args)]
      (-> r (dissoc :resume) (assoc :resumable (some? (:resume r)))))))

;; ---- the search ceiling: a bound a request may lower and not raise ------

(def search-bounds
  "Which of the two ceilings apply to which op, and under which key the op reads it.

  A read that expands rules runs on the daemon's **single write monitor**, so its cost
  is not the caller's alone: every other request queues behind it.  The two dials a
  caller sets are the two ceilings — `:max-ms` (`config/max-query-ms`) and `:max-depth`
  (`config/max-query-depth`) — and this table says which entry point reads which, because the
  option rosters differ (`query-opt-keys` has no `:max-ms` to fill in, `search-tree`'s
  has both, an anytime budget map is `:max-ms` and takes no default of its own).

  **An entry point with no bound of its own is not on it**, which is a fact about the entry point rather
  than a category: `:sentexes-matching` has no dial to raise, so there is nothing to
  clamp. The four backward-search entry points do have one (`core/ask-opt-keys`,
  `core/prove-opt-keys`), and are held to the ceiling like the rest — `:ask` and `:ask?`
  to the clock alone, since nothing in the prover registry expands a rule."
  {:query              #{:max-depth}
   :query?             #{:max-depth}
   :argue              #{:max-depth}
   :why                #{:max-depth}
   :why-not            #{:max-depth :max-ms}
   :search-tree        #{:max-depth :max-ms}
   :compare-tacticians #{:max-depth :max-ms}
   :ask                #{:max-ms}
   :ask?               #{:max-ms}
   :prove              #{:max-depth :max-ms}
   :provable?          #{:max-depth :max-ms}
   :ask-within         #{:max-ms}
   :prove-within       #{:max-depth :max-ms}
   :kb-integrity       #{:max-ms :max-work :max-results}})

(def integrity-max-work
  "The most cooperative query units one daemon integrity request may spend."
  10000)

(def integrity-max-results
  "The most findings one daemon integrity response may carry."
  1000)

(def ^:private clock-fill
  "The ops whose ceiling has to reach a caller who sent **no option map at all**, and the
  arguments to fill in between what they sent and the map.

  A `:max-depth` op needs nothing here: absent there is a *smaller* question than the
  ceiling — no rule expansion at `query`'s entry point, the shipped guard at `prove-within`'s —
  so a call with no map is already inside the bound. Absent `:max-ms` is the opposite: it
  is **no clock**, and an unbounded backward search on the daemon's single write monitor
  is the exposure the ceiling exists for. So a short call to one of these is padded out to
  the arity that has a map, with `vaelii.core`'s own default for each argument in
  between, and `under-ceiling` then fills the clock in.

  The four search entry points fill their one intervening context argument with `?ctx`;
  `kb-integrity` has no intervening default. `:option-arity` distinguishes an omitted
  options map from an explicit nil already occupying that arity, which is normalized to
  the same empty map. An entry point added here owes the same reading of its own arglists."
  {:ask         {:fill ['?ctx] :option-arity 3}
   :ask?        {:fill ['?ctx] :option-arity 3}
   :prove       {:fill ['?ctx] :option-arity 3}
   :provable?   {:fill ['?ctx] :option-arity 3}
   :kb-integrity {:fill [] :option-arity 3}})

(defn- with-opts-map
  "`args` padded out to the arity whose last argument is the option map: nothing to do
  when the caller already sent one (or sent nothing at all, which is an arity refusal the
  op itself owes), else the tail of `fill` the call is short by, and then an empty map for
  `under-ceiling` to write the clock into."
  [args {:keys [fill option-arity]}]
  (cond
    (empty? args) args
    (map? (peek args)) args
    (and (= option-arity (count args)) (nil? (peek args)))
    (assoc args (dec option-arity) {})
    :else
    (conj (into args (subvec fill (min (count fill) (dec (count args))))) {})))

(defn- ceiling-for
  "The ceiling on `k`, or nil when the operator lifted it (`0`)."
  [k]
  (let [n (case k
            :max-ms    (config/max-query-ms)
            :max-depth (config/max-query-depth)
            :max-work integrity-max-work
            :max-results integrity-max-results)]
    (when (pos? n) n)))

(defn- under-ceiling
  "`opts` — an option or budget map an op's caller sent — held under the ceilings
  `keys` names, or a refusal.

  Two things happen, and only one of them is a refusal.  A value **over** the ceiling is
  refused by name (`:over-ceiling`): the caller asked for more than this daemon serves,
  and answering under a quietly lowered bound would hand back a partial result labelled
  as the one that was asked for.  A `:max-ms` the caller left **absent** is filled in
  with the ceiling, because absent there means *no clock at all* — an unbounded read on
  the write monitor — and the ceiling is the answer to \"how long may this run\" that
  the daemon already gives every other read.

  An absent `:max-depth` is left alone: absent is not unbounded there, it is the
  no-rule-expansion answer at `query`'s entry point and the shipped guard at `prove-within`'s,
  both of which are *smaller* questions than the ceiling rather than larger ones."
  [op ks opts]
  (reduce
   (fn [m k]
     (let [ceiling (ceiling-for k)
           v       (get m k)]
       (cond
         (nil? ceiling)                     m
         (and (number? v) (> v ceiling))
         (throw (ex-info (str "op " op " " k " " v " is over this daemon's ceiling of "
                              ceiling " — a request may name a smaller bound and not a"
                              " larger one, since every op runs on the single writer and"
                              " holds every other caller behind it")
                         {:type :over-ceiling :op op :option k :requested v
                          :ceiling ceiling}))
         (and (#{:max-ms :max-work :max-results} k) (nil? v))
         (assoc m k ceiling)
         :else                              m)))
   opts
   ks))

(defn- bounded
  "Wrap an op's `(fn [kb args])` so the trailing option/budget map its caller sent is
  held under `search-bounds`' ceilings.

  Wrapped **in the table** rather than at the HTTP route, because the table is what two
  callers dispatch through: `POST /op` and the model's generated tool set
  (`vaelii.impl.llm.tools`, which builds its schemas from this map and calls back into
  it).  A ceiling applied at one of those entry points would be a ceiling the other does not
  have.

  For a `clock-fill` op the args are padded first, so a caller who sent no option map
  still gets one to be clamped: absent means *no clock* at those entry points, and no clock is
  the exposure rather than a smaller question."
  [op f]
  (if-let [ks (search-bounds op)]
    (let [fill (clock-fill op)]
      (fn [kb args]
        (let [args (cond-> (vec args) fill (with-opts-map fill))]
          (f kb (if (map? (peek args))
                  (conj (vec (butlast args)) (under-ceiling op ks (peek args)))
                  args)))))
    f))

(def ops
  "The reachable operations, keyed by op keyword.  Reads, writes, and introspection —
  the working set a remote caller needs; extend by adding a `vaelii.core` fn here.

  Every entry is wrapped by `bounded`, which is a no-op for an op `search-bounds` does
  not name."
  (into
   {}
   (map (fn [[op f]] [op (bounded op f)]))
   {:assert       (op v/assert)
    :assert-rule  (op v/assert-rule)
    :assert-many  (op v/assert-many)
    :retract      (op v/retract!)
    :edit         (op v/edit!)
    ;; the same write, reporting what it turned out to mean — the *after* to `:preview`'s
    ;; *before*, and the one a caller wants when it has just committed rather than when it
    ;; is deciding whether to
    :edit-with-consequences (op v/edit-with-consequences!)
    ;; the dry run of the two above: what `assert` / `edit` would refuse, and why,
    ;; without storing anything.  A remote editor validates before it writes.
    :check        (op v/check)
    :check-edit   (op v/check-edit)
    ;; and the other dry run: not whether the batch would be *admitted* but what it would
    ;; *mean* — the belief it adds and takes away (docs/preview.md).  Served with the
    ;; writes rather than the reads because it applies the batch and rolls it back, so it
    ;; holds the daemon's single writer for its duration; it stores nothing, and hands the
    ;; KB back at the same handles.
    ;; a write to the **filesystem**, not to the KB.  Two things a caller has to know and
    ;; the wire cannot tell them: the directory is resolved on the **daemon's** host — the
    ;; only place it can be, since the daemon owns the KB and there is no stream to hand
    ;; back — and the export reports no progress, because `:on-progress` is a function and
    ;; functions do not cross an EDN wire.  Served with the writes so it runs under the
    ;; monitor: the walk fetches record by record, and a dump of a KB something is
    ;; asserting into is a dump of no single state.
    :export       (op v/export!)
    :preview      (op v/preview)
    :sentexes-matching (op v/sentexes-matching)
    :query        (op v/query)
    :query?       (op v/query?)
    :ask          (op v/ask)
    :ask?         (op v/ask?)
    :prove        (op v/prove)
    :provable?    (op v/provable?)
    :in?          (op v/in?)
    :believed?    (op v/believed?)
    :belief-status (op v/belief-status)
    :believed     (op v/believed)
    :why          (op v/why)
    :why-not      (op v/why-not)
    :isa?         (op v/isa?)
    :types-of     (op v/types-of)
    :disjoint?    (op v/disjoint?)
    :genls        (op v/genls)
    :specs        (op v/specs)
    :types        (op v/types)
    :contexts     (op v/contexts)
    :sentex       (op v/sentex)
    :handle-of    (op v/handle-of)
    :find-sentexes (op v/find-sentexes)
    ;; the vocabulary — enumerate / count / search the terms themselves.  Served because
    ;; the alternative for a remote client is shipping every sentex over the wire to
    ;; collect the terms out of them.
    :terms        (op v/terms)
    :term-count   (op v/term-count)
    :sentex-count (op v/sentex-count)
    :find-terms   (op v/find-terms)
    :forward-chain (op v/forward-chain)
    :chain-stats  (op v/chain-stats)
    ;; the per-rule breakdown behind chain-stats — what each forward rule placed, refused
    ;; (and why), or never did — read O(rules) off the ledger and the justification graph
    :chain-report (op v/chain-report)
    :conflicts    (op v/conflicts)
    :contradictions (op v/contradictions)
    :violations   (op v/violations)
    ;; the *standing* disjointness question, as against the arising one `settle` files
    ;; into `violations` above.  Computed on demand and not filed, so it is asked for
    ;; rather than accumulated — the read an imported KB needs, since a load rebuilds
    ;; belief rather than changing it and nothing is newly anything to report
    :exposed-clashes (op v/exposed-clashes)
    ;; the predAllSpecified integrity audit, one declaration or every visible one.  Read
    ;; only and filed nowhere, like the two above, so a remote caller asks for it rather
    ;; than reading an accumulated ledger.  Its own cost is one read per member of the
    ;; audited collection, which is the caller's to spend (docs/predall.md)
    :specified-violations     (op v/specified-violations)
    :all-specified-violations (op v/all-specified-violations)
    :kb-integrity             (op v/kb-integrity)
    ;; how a goal would be answered: the provers bearing on it with their estimates, or
    ;; for a conjunction the join order and the counts behind it
    :query-plan   (op v/query-plan)
    ;; and the run that plan predicts: the search tree as data, and the same goal under
    ;; several tacticians side by side.  Both bound their own work (a node budget + a
    ;; wall-clock), so a remote reader cannot turn one call into an unbounded search
    :search-tree       (op v/search-tree)
    :compare-tacticians (op v/compare-tacticians)
    ;; introspection reads — the surface a read client (the browser) needs to render
    ;; a KB it does not own; safe to serve, and shared with vaelii.impl.access
    :premise?     (op v/premise?)
    :defeat-class (op v/defeat-class)
    :justification    (op v/justification)
    :supporting-justifications (op v/supporting-justifications)
    :dependent-justifications  (op v/dependent-justifications)
    ;; the one thing about a justification that belief cannot be read off: blocked by its
    ;; rule's exception, so every antecedent is IN and it still supports nothing.  Served
    ;; because a remote reader has no other way to ask — the network is not a record — and
    ;; a proof tree drawn without it calls a blocked justification supporting
    :blocked-justifications    (op v/blocked-justifications)
    :lookup       (op v/lookup)
    :escalate     (op v/escalate)
    :explain-levels (op v/explain-levels)
    :count-in-context (op v/count-in-context)
    :sentexes-in-context   (op v/sentexes-in-context)
    :sentexes-with-arg     (op v/sentexes-with-arg)
    :sentexes-with-functor (op v/sentexes-with-functor)
    :count-with-arg        (op v/count-with-arg)
    :count-with-functor    (op v/count-with-functor)
    :disjoint-metatypes    (op v/disjoint-metatypes)
    :metatype-members      (op v/metatype-members)
    ;; what a reified term denotes (docs/nat.md).  A remote reader has no other way to
    ;; ask: the constant is opaque by construction, so a client that could not resolve it
    ;; would have to show a reader `nat/g17` — which is the one thing it must not do
    :term-expression       (op v/term-expression)
    ;; qualitative constraint reasoning (docs/qcn.md).  Reads: they compute a network
    ;; from the believed facts and register nothing, so they are safe on a KB the caller
    ;; does not own.  Every result is already EDN — relation keywords, term symbols, and
    ;; vectors of the two — so none of them needs the sentex-map projection below.
    :qualitative-network   (op v/qualitative-network)
    :possible-relations    (op v/possible-relations)
    :qualitative-scenario  (op v/qualitative-scenario)
    :qualitative-scenarios (op v/qualitative-scenarios)
    ;; what this process is holding beside the store, and the one control that drops it.
    ;; The clear is a write in the HTTP sense and in no other: it destroys no knowledge,
    ;; moves no belief, and is the instrument that makes a hit rate mean something
    :caches       (op v/caches)
    :clear-caches (op v/clear-caches)
    ;; what would have to be true for a goal to follow, and the control that drops it.
    ;; A **write**, and filed with the writes for that reason: a hypothesis is minted
    ;; through the whole assert pipeline into a scratch context hung below the asking
    ;; one, so it holds the daemon's single writer for its run.  Without `{:keep? true}`
    ;; the scratch is torn down on the way out and the KB is left as it was found
    ;; (docs/abduction.md)
    :abduce         (op v/abduce)
    :abduce-discard (op v/abduce-discard!)
    ;; the four-valued epistemic read: the case for a sentence, the case against, and
    ;; which of them the engine can resolve.  A read — it queries both sides and stores
    ;; nothing (docs/belief.md)
    :argue        (op v/argue)
    ;; the reading about the **knowledge** rather than about a run — unfired rules,
    ;; extent skew, chain depth, taxonomy coverage, stranded declarations — and its
    ;; Markdown rendering.  `:quality-report` takes the *map*, not the KB, so a caller
    ;; renders a reading it already holds; it is `kbless-ops` above for that reason.
    ;; `:on-progress` is a function and does not cross the wire, so a long census over a
    ;; large KB reports nothing until it answers (docs/quality.md)
    :kb-quality     (op v/kb-quality)
    :quality-report (op* v/quality-report)
    ;; the creation record, read and layered on.  `:add-provenance` is a write — it
    ;; stores — and is metadata rather than belief, so it moves nothing
    :provenance     (op v/provenance)
    :add-provenance (op v/add-provenance)
    ;; the anytime reads, **without a resumable tail** (`without-resume`).  A continuation
    ;; is a function over an in-memory lazy tail, so what crosses is the results, the
    ;; completion status and one `:resumable` bit; continuing is a fresh call under a
    ;; larger budget (docs/anytime.md)
    :ask-within   (op (without-resume v/ask-within))
    :prove-within (op (without-resume v/prove-within))
    ;; the taxonomy and context questions the browser's own reads left short: the genl
    ;; test between two *types*, the genlCx ancestor set both ways, and the visibility question
    ;; behind every scoped read (docs/taxonomy.md, docs/contexts.md)
    :genl?        (op v/genl?)
    :context-up   (op v/context-up)
    :context-down (op v/context-down)
    :sees?        (op v/sees?)
    ;; the declared predicate properties, and the inverse pairing — read off the cached
    ;; closures rather than matched, so a remote caller has no other way to ask
    :has-prop?    (op v/has-prop?)
    :props        (op v/props)
    :inverse-of   (op v/inverse-of)
    ;; the equality partition, read.  `:deprecated?` is what makes the `rewriteOf` /
    ;; `sameAs` distinction observable at all — both produce the same class
    ;; (docs/equality.md)
    :representative (op v/representative)
    :same-class?    (op v/same-class?)
    :equiv-class    (op v/equiv-class)
    :deprecated?    (op v/deprecated?)
    ;; the whole-KB enumerations an audit pass folds over: every live handle, the
    ;; contexts one sentence holds in, the canonical form a sentence *would* key on
    ;; without storing it, and the census of what the engine does with its own grammar
    :handles          (op wire-handles)
    :contexts-of      (op v/contexts-of)
    :canonical-sentex (op v/canonical-sentex)
    :vocabulary-audit (op v/vocabulary-audit)
    ;; the exceptWhen fixpoint's instrumentation (docs/exceptions.md)
    :settle-stats (op v/settle-stats)
    ;; the rest of `kbless-ops` (`:quality-report` above is the fourth): the retrieval
    ;; stack and the shipped calculi as data, and a stored rule's sentence with its
    ;; author's variable names put back — the last of which a client needs in order to
    ;; *display* a rule it fetched
    :levels            (op* v/levels)
    :calculi           (op* v/calculi)
    :readable-sentence (op* v/readable-sentence)
    ;; the three usability reads.  `:describe` is what a remote reader asks instead of a
    ;; dozen round trips — one call answers arity, declarations, properties, closures and
    ;; counts for a term, and the browser's term page is built on it.  `:why-not` is
    ;; already above and needs no entry of its own for `{:nearest n}`: the table `apply`s
    ;; the var, so a new arity crosses the wire the moment `vaelii.core` grows one
    :describe     (op v/describe)
    ;; `kb-diff`'s second side is a **path on the daemon's host**, for the reason `:export`'s
    ;; destination is: the daemon owns the KB, a KB value does not cross an EDN wire, and a
    ;; text export is a directory the daemon can read.  So the remote reading is "what has
    ;; the live KB done since this export was taken"
    :kb-diff      (op v/kb-diff)}))

;; ---- the daemon's own ops: the change feed, held open with a cursor ------
;;
;; `ops` above is an allowlist of `vaelii.core` fns with the KB supplied, and the feed
;; cannot be one of them: `core/watch` takes a **function**, and a function does not
;; cross an EDN wire — the same wall `:export`'s `:on-progress` hits.  What crosses is
;; state with a cursor, which is state *this daemon* holds rather than anything the
;; engine has, so these three take the handler's subscription registry as well as its
;; KB (`vaelii.impl.subscribe`, docs/feed.md).
;;
;; A second table rather than a second value shape in the first one, because the
;; difference is worth being able to state: `ops` is the surface a caller could also
;; reach in process, and `vaelii.impl.access` dispatches through it for exactly that
;; reason; `feed-ops` is the daemon's own, and a local caller holding a KB uses
;; `core/watch` instead.  `vaelii.impl.llm.tools` derives the model's tool set from
;; `ops` alone, so a subscription is not something a model can allocate.

(defn- feed-args!
  "The args a feed op takes, or a `:bad-args` refusal naming what it wanted.  The
  engine ops get this from `apply` and an `ArityException`; these take an args vector
  whole, so the arity check has to be written."
  [op args shapes]
  (or (some #(when (= (count args) (count %)) args) shapes)
      (throw (ex-info (str "op " (pr-str op) " takes " (str/join " or " (map pr-str shapes))
                           ", got " (count args) " argument"
                           (when (not= 1 (count args)) "s"))
                      {:type :bad-args :op op}))))

(def feed-ops
  "The change-feed operations, keyed by op keyword — `(fn [ctx args])` over a `ctx` of
  `{:kb :registry :monitor}`.

  Each says its own relationship to the daemon's write monitor, which is the one thing
  about them that is not like an engine op.  `:watch` and `:unwatch` take it: they are
  instantaneous, and taking it makes the boundary exact — every settle that finished
  before a `:watch` returned is outside the subscription's feed, and every one that
  starts after it is inside.  `:poll` **must not**, because a long poll parks: inside
  the monitor it would block every writer for the duration of its wait, turning a
  feature about liveness into a global stall.  `:watchers` does not either — it reads
  the registry and expires what has expired, and a listing that had to queue behind a
  bulk load is a listing an operator asks for while the daemon is busy."
  {:watch
   (fn [{:keys [kb registry monitor]} args]
     (let [[goal context] (feed-args! :watch args [[] '[goal context]])]
       (locking monitor (sub/watch registry kb goal context))))

   :poll
   (fn [{:keys [kb registry]} args]
     (let [[token cursor opts] (feed-args! :poll args ['[token cursor]
                                                       '[token cursor opts]])]
       (sub/poll registry kb token cursor opts)))

   :unwatch
   (fn [{:keys [kb registry monitor]} args]
     (let [[token] (feed-args! :unwatch args ['[token]])]
       (locking monitor (sub/unwatch registry kb token))))

   :watchers
   (fn [{:keys [kb registry]} args]
     (feed-args! :watchers args [[]])
     (sub/subscriptions registry kb))})

(def op-names
  "Every op keyword this daemon answers, sorted — the `vaelii.core` allowlist and the
  daemon's own together.  What an `:unknown-op` refusal hands back, so a caller
  discovering the surface sees one roster rather than the larger half of two."
  (vec (sort (concat (keys ops) (keys feed-ops)))))

(defn- wire-safe
  "Make a result EDN-clean for a client that lacks the `impl` record classes: project
  every sentex/record to a plain map (the `sentex`-map contract).  `clojure.walk/walk`
  `doall`s each seq, so a lazy answer stream is realized before the response closes;
  a **list stays a list** (a sentence `(dog Muffet)` must not become `[dog Muffet]`, or it
  would `pr-str` differently on the far side)."
  [x]
  (walk/postwalk (fn [y] (if (record? y) (into {} y) y)) x))

(def ^:private client-error-types
  "The engine's request-refusal vocabulary — every `:type` the entry points throw at input a
  caller shaped wrong, answered **400** like the daemon's own seven.  A snake_case
  predicate or a misspelt option is the client's mistake: answered 500, it would
  count as a backend fault at every reverse proxy and 5xx alarm between the caller
  and the daemon, and feed the log one warning per typo.  A `:type` outside this set keeps
  the 500 default, so a genuine internal fault — a broken solver binary, a store
  error — still reads as one; a *new* refusal type belongs in this set the day it is
  born, and `wire_contract_test` pins the pairing."
  #{:naming :not-well-formed :not-ground :not-range-restricted :not-indexable
    :disjunction-too-wide
    :shape :not-encodable
    :arg-type :inter-arg-type :arg-genl :quoted-arg-type :arg-position :arg-constraint-kind
    :arg-variable :arity
    ;; the six relation-property refusals, which `check` reports and `assert` throws as
    ;; one family — a caller that asserts content a declared property forbids has made
    ;; one kind of mistake, so the six answer alike rather than splitting on which
    ;; property caught it
    :disjoint :functional :asymmetric :anti-transitive :irreflexive :anti-symmetric
    :unknown-option :bad-handle
    :unknown-handle :bad-level :exception-not-closed :not-stratified :naf-not-closed
    :quantifier-not-local
    :not-watchable :not-checkable :not-assertible
    :bad-table-entry
    ;; a map handed to `:quality-report` that is not one of `:kb-quality`'s answers —
    ;; the caller reporting on the wrong reading, refused rather than rendered as a page
    ;; of zeros
    :not-a-report
    ;; a query context (`CxEverything` / `CxInference` / `CxNothing`) handed to a read
    ;; that does not resolve one — `:why-not`, `:lookup`, `:query-plan`, `:search-tree`
    ;; and the rest.  The caller named a reading this entry point does not offer, which is the
    ;; same class of mistake as naming an option it does not read
    :unsupported-context
    ;; a `:find-terms` regex whose backtracking blew the per-term step budget — the
    ;; caller sent a pathological pattern, which is their mistake to fix, not a fault
    :pattern-too-costly
    ;; a `:max-depth` or `:max-ms` past what this daemon serves (`search-bounds`).  The
    ;; caller named a bound rather than the daemon being at capacity, so it is a 400 and
    ;; not a 503 — and the refusal carries the ceiling, which is what the next request
    ;; has to name
    :over-ceiling
    ;; and its other side: a bound the request named, or the ceiling standing in for one
    ;; it did not, that the search did not finish inside.  A 400 for `:over-ceiling`'s
    ;; reason — the caller decides what to do next, by widening the bound or by asking
    ;; through `:ask-within` / `:prove-within`, which hand back the prefix with a
    ;; `:status` — where a 503 would say the daemon is at capacity, which it is not
    :budget-exhausted
    ;; `:export` is in `ops`, so its destination refusals are caller mistakes too —
    ;; a directory that exists and is not empty is not a backend fault — and so are the
    ;; two that name a dump this build does not write
    :no-destination :not-a-directory :not-empty :export-busy :unsupported-format
    :unsupported-variant :unsupported-compression
    ;; the feed's four (docs/feed.md).  The two ceilings are the odd ones and are here
    ;; on purpose: the daemon is at capacity rather than the request being malformed,
    ;; but the caller is who can fix it — by dropping a subscription, or by polling on a
    ;; timer instead of asking to wait — and inventing a status for either would break
    ;; the promise that a client discriminates on `:type` with the code as the coarse
    ;; client/server split
    :unknown-subscription :bad-cursor :too-many-subscriptions :too-many-waiters})

(defn- handle-op
  "Run one `{:op :args}` request under the write lock and answer with EDN.

  The two guards run before the body is read.  `POST /op` is the write route of the
  single writer, and on an open loopback daemon nothing above has identified the
  caller, so a page the operator merely *visits* must not be able to drive it:
  `guard/edn-body?` forces a CORS preflight this daemon cannot answer, and
  `guard/same-origin?` refuses a browser that stamped someone else's origin.  See
  `vaelii.impl.guard`.

  Two tables are looked up, in order: the `vaelii.core` allowlist (`ops`, run under the
  monitor), then the daemon's own change-feed ops (`feed-ops`, which take the handler's
  subscription registry and decide about the monitor themselves — a long poll parks, and
  a parked poll holding it would block every writer)."
  [kb registry monitor req]
  (let [edn-reply (fn [status m]
                    {:status status
                     :headers {"content-type" "application/edn"}
                     :body (pr-str m)})]
    (try
      (cond
        (not (guard/edn-body? req))
        (edn-reply 415 {:ok false :type :not-edn
                        :error "POST /op requires Content-Type: application/edn"})

        (not (guard/same-origin? req))
        (edn-reply 403 {:ok false :type :cross-origin
                        :error "cross-origin request refused"})

        :else
        ;; The body read is its own step so an unreadable one answers **400 `:not-edn`**
        ;; rather than falling into the catch below as a 500 with the reader's message —
        ;; a malformed request is the client's fault, and `docs/operations.md` promises a
        ;; client discriminates on `:type` rather than on the status code.
        (let [body (guard/read-capped-body req)
              form (try (edn/read-string body)
                        (catch Throwable t
                          (throw (ex-info (str "request body does not read as EDN: "
                                               (.getMessage t))
                                          {:type :not-edn}))))
              {:keys [op args]} (when (map? form) form)
              ;; `:args` is spliced with `(vec args)` below, so a non-sequential one —
              ;; `{:op :assert :args 5}` — would throw a bare IllegalArgumentException
              ;; into the Throwable arm and answer 500 with no usable `:type`.  It is
              ;; the caller's mistake, so it is a 400 `:bad-args` like the arity
              ;; mismatch beside it.
              _ (when-not (or (nil? args) (sequential? args))
                  (throw (ex-info (str "op :args must be a sequence, got " (pr-str args))
                                  {:type :bad-args :op op})))
              f (ops op)
              g (when-not f (feed-ops op))]
          (cond
            ;; `wire-safe` inside the monitor, not after it: the walk is what *realizes*
            ;; a lazy answer stream, so releasing the lock around the call alone would
            ;; let a `:query` read its matches while a concurrent `:assert` is settling
            ;; — one reply straddling two states of the KB.  The daemon promises reads
            ;; pay the same lock, and the read is not over until its seq is.
            ;; an arity mismatch is the caller naming the wrong number of args, so it is
            ;; a 400 like the unknown op beside it rather than a server fault
            f
            (let [result (try (locking monitor (wire-safe (f kb (vec args))))
                              (catch clojure.lang.ArityException t
                                (throw (ex-info (str "wrong number of arguments for op "
                                                     (pr-str op) ": " (.getMessage t))
                                                {:type :bad-args :op op}))))]
              (edn-reply 200 {:ok true :result result}))

            ;; the feed's own, **outside** the monitor here — each takes it for itself
            ;; where it needs it, and `:poll` must not, since a parked long poll holding
            ;; the daemon's one lock would stall every writer for the length of its wait.
            ;; Nothing a feed op answers is a lazy stream over the store, so realizing it
            ;; out here straddles no state: the events were built at settle time and are
            ;; already values.
            g
            (edn-reply 200 {:ok true
                            :result (wire-safe (g {:kb kb :registry registry :monitor monitor}
                                                  (vec args)))})

            :else
            (edn-reply 400 {:ok false :error (str "unknown op: " (pr-str op))
                            :type :unknown-op
                            :ops op-names}))))
      (catch clojure.lang.ExceptionInfo e
        (let [ty (:type (ex-data e))]
          (cond
            (= :body-too-large ty)
            (edn-reply 413 {:ok false :error (.getMessage e) :type :body-too-large})
            (or (#{:not-edn :bad-args} ty) (client-error-types ty))
            (edn-reply 400 {:ok false :error (.getMessage e) :type ty})
            :else
            (do (trove/log! {:level :warn :id ::op-error :error e})
                (edn-reply 500 {:ok false :error (.getMessage e)
                                :type (or ty :internal-error)})))))
      ;; `Throwable`, not `Exception`: an oversized or deeply-nested body raises
      ;; `OutOfMemoryError`/`StackOverflowError`, which an `Exception` catch lets
      ;; escape the handler and kill the connection rather than answering on it.
      ;; `:internal-error` when the throwable carries no `:type` of its own — a bare
      ;; Java exception would otherwise answer `:type nil`, the key present and
      ;; useless, breaching the one-vocabulary promise (`docs/operations.md`).
      (catch Throwable t
        (trove/log! {:level :warn :id ::op-error :error t})
        (edn-reply 500 {:ok false :error (.getMessage t)
                        :type (:type (ex-data t) :internal-error)})))))

;; ---- authentication: one shared bearer token -----------------------------

(def ^:private open-routes
  "The routes that answer before the token is checked, and `GET /health` is the whole
  set.  A daemon only its token-holder can probe is one no container orchestrator, load
  balancer or shell script can watch, and `{:ok true}` tells a caller nothing it did not
  already know by connecting.  Stated here because an unauthenticated route inside an
  authenticated daemon is indistinguishable from an oversight to delete: this one is a decision."
  #{"/health"})

(defn- wrap-bearer-auth
  "`guard/wrap-bearer` with the daemon's own 401: EDN carrying a non-nil `:type` like
  every other refusal the daemon can answer, plus the `WWW-Authenticate` challenge a 401
  is defined to carry.  The comparison and the header read are the browser's too, and
  live in `vaelii.impl.guard` for that reason."
  [handler token]
  (guard/wrap-bearer
   handler token open-routes
   (fn [_] {:status 401
            :headers {"content-type" "application/edn"
                      "www-authenticate" "Bearer"}
            :body (pr-str {:ok false :type :unauthorized
                           :error "this daemon requires Authorization: Bearer <token>"})})))

(def http-threads
  "How many worker threads the daemon's HTTP server runs.

  Stated rather than defaulted, because it is one half of a pair: a parked long poll
  holds one of these for the length of its wait, so `subscribe/max-parked` has to stay
  well under it or the feature that exists for liveness becomes the thing that stalls
  the daemon.  Left implicit the two numbers were 50 and 64, the wrong way round, and
  nothing said so — 55 parked polls took `/health` from 62 ms to 26 s.  `serve_test`
  pins the relationship."
  50)

(def ^:private loopback
  "The network interface the daemon binds unless told otherwise.  `POST /op` is the **write**
  route of the single writer, so it answers only the machine it runs on; exposing it is
  an explicit choice (`--listen`), not the default.  The same rule the browser holds to
  (`vaelii.impl.web`), and the more important of the two — the browser edits a KB, and
  this one *is* the KB's only writer.

  Loopback bounds *which machine* may reach the daemon and nothing more: a browser on
  that machine is a local client too, which is what `vaelii.impl.guard` is for, and
  every other process on it is a client with a socket, which is what the bearer token
  is for.  A loopback daemon may run open; one that binds an address may not
  (`auth-posture`)."
  "127.0.0.1")

(defn app
  "The ring handler for a KB — pure `request -> response`, so it is tested without a
  socket.  One monitor per handler serializes the ops (the single-writer contract).

  `:host` names the interface this handler will be served on, which fixes the `Host`
  values it answers to (`guard/allowed-hosts`).  On the loopback default that refuses
  a rebound DNS name, the one attack `same-origin?` cannot see.

  `:token` is the shared bearer token every request must present.  Omitted, it is
  `VAELII_API_TOKEN` (`guard/api-token`), so a daemon and a client on one host agree
  without either being configured; an explicit nil serves **open**, which is what a
  test of the other refusals needs — a handler that 401s first exercises none of them."
  ([kb] (app kb {}))
  ([kb {:keys [host] :or {host loopback} :as opts}]
   (let [monitor (Object.)
         ;; per handler, beside the monitor and for the same reason: a feed token names
         ;; a subscription *on this daemon*, so it is state the handler owns rather than
         ;; state the KB does — two handlers over one KB are two daemons, and a token
         ;; from one means nothing to the other
         registry (sub/registry)
         token   (if (contains? opts :token) (:token opts) (guard/api-token))
         allowed (guard/allowed-hosts host)]
     (wrap-bearer-auth
      (guard/wrap-host-allowed
       (ring/ring-handler
        (ring/router
         [["/health" {:get (fn [_] {:status 200
                                    :headers {"content-type" "application/edn"}
                                    :body (pr-str {:ok true})})}]
          ["/op" {:post (fn [req] (handle-op kb registry monitor req))}]])
        (ring/create-default-handler
         {:not-found (fn [_] {:status 404 :headers {"content-type" "application/edn"}
                              ;; typed like every other {:ok false} — the migration
                              ;; line "every reply carries a non-nil :type" holds on
                              ;; this route too, not only on POST /op
                              :body (pr-str {:ok false :error "not found"
                                             :type :not-found})})}))
       allowed
       (fn [_] {:status 400
                :headers {"content-type" "application/edn"}
                :body (pr-str {:ok false :type :bad-host
                               :error "unrecognized Host header"})}))
      token))))

(defn start
  "Start the daemon over `kb` and return the running jetty `Server` (`:join? false`, so
  the caller controls its lifetime — a test stops it in a `finally`).  `:port 0` binds
  an ephemeral port; read the actual one with `port`.

  `:host` defaults to loopback; pass an address (`\"0.0.0.0\"`) to bind publicly, and
  read the note on `loopback` before doing so.  `:token` is `app`'s, forwarded only
  when the key is there, so an omitted one still reads `VAELII_API_TOKEN` and an
  explicit nil still serves open."
  ^Server [kb {:keys [port host] :or {port 4200 host loopback} :as opts}]
  (jetty/run-jetty (app kb (assoc (select-keys opts [:token]) :host host))
                   {:port port :host host :join? false :max-threads http-threads}))

(defn port
  "The actual TCP port a started `Server` is listening on — the ephemeral one when it
  was started with `:port 0`, read off its first connector."
  ^long [^Server server]
  (.getLocalPort ^ServerConnector (first (.getConnectors server))))

(defn- listen-host
  "The bind address `--listen` names, or `loopback` when the flag is absent — and a
  refusal (`:unknown-option`) when the flag is present with no address after it.
  Reading that as loopback fails safe and is still a lie: the flag is the explicit
  opt-in to a public bind, and an operator whose flag was silently ignored walks away
  believing the daemon is reachable when only this machine can see it.

  **The next flag is not an address either.**  `--listen --whatever` otherwise binds an
  network interface literally named `--whatever`, which is a Jetty failure naming a token rather
  than the refusal this entry point owes — the same reading `impl.cli`'s `--dir --starter`
  refuses, and the more consequential of the two, since this flag publishes the KB's only
  writer."
  [args]
  (let [tail (drop-while #(not= "--listen" %) args)]
    (if (seq tail)
      (let [v (second tail)]
        (if (and v (not (str/starts-with? v "--")))
          v
          (throw (ex-info (str "--listen needs an address and "
                               (if v (str "the next word is the flag " v)
                                   "the line ends after it")
                               " — write --listen <address> (e.g. --listen 0.0.0.0)")
                          {:type :unknown-option :mismatch :missing-value :flag "--listen"}))))
      loopback)))

(defn- positional-args
  "The non-flag arguments, in order, wherever they sit relative to the flags —
  `4200 --listen 0.0.0.0 /var/lib` names the same daemon as
  `4200 /var/lib --listen 0.0.0.0`.  A flag this table does not know, or a third
  positional, is refused (`:unknown-option`): a positional silently dropped is a
  disk daemon running in memory, every client write evaporating at exit with one
  `:dir :memory` log line as the only witness."
  [args]
  (loop [[a & more] (seq args), pos []]
    (cond
      (nil? a)                        (if (> (count pos) 2)
                                        (throw (ex-info (str "unexpected argument: "
                                                             (nth pos 2)
                                                             " — the daemon takes a port"
                                                             " and a store directory and"
                                                             " nothing else: <port>"
                                                             " [<dir>] [--listen <address>]")
                                                        {:type :unknown-option :mismatch :unknown-key :arg (nth pos 2)}))
                                        pos)
      (= "--listen" a)                (recur (rest more) pos)   ; value read by listen-host
      (.startsWith ^String a "--")    (throw (ex-info (str "unknown flag: " a " — the"
                                                           " daemon reads --listen"
                                                           " <address>, and takes a port"
                                                           " and a store directory as"
                                                           " positionals")
                                                      {:type :unknown-option :mismatch :unknown-key :flag a}))
      :else                           (recur more (conj pos a)))))

(def ^:private public-bind?
  "`guard/public-bind?` — the same question the browser asks, so the bind that requires
  a token is the same bind on both servers."
  guard/public-bind?)

(defn- auth-posture
  "Which posture a daemon binding `host` with `token` runs in — and the refusal when
  neither is available.

    :required  a token is set, and every request presents it
    :open      loopback with no token: every process on this machine drives the writes

  **A bind that names an address with no token is refused** (`guard/require-token!`,
  `:unauthorized`), which is the one place the daemon fails closed, and the browser is
  held to the same rule by the same fn.  It is the flag that publishes `POST /op` — the
  KB's only writer — and the same flag drops the `Host` allowlist, so the exposed
  configuration would otherwise be the one with the fewest checks.  The loopback
  default is not held to it because `lein serve` on a laptop is a real workflow that a
  required credential would only teach an operator to export a constant.  The `Host`
  allowlist is not held to it either — see `host-posture` for why that one warns
  instead of refusing."
  [host token]
  (guard/require-token! "daemon" host token)
  (if (str/blank? token) :open :required))

(defn- host-posture
  "Which `Host`-allowlist policy a daemon binding `host` runs under — the question
  `auth-posture` answers for the token, beside it:

    :allowlisted  the daemon checks Host — loopback's own names, or VAELII_ALLOWED_HOSTS's
    :open         every Host is answered — a public bind naming no VAELII_ALLOWED_HOSTS

  **Never throws.**  Unlike a missing token, an open allowlist is not fail-closed: a
  daemon fronted by a reverse proxy legitimately receives whatever `Host` the proxy
  sets, and an operator cannot always enumerate that set in advance, so a refusal here
  would trip a normal deployment rather than a broken one.  `announce-auth!` is what
  turns `:open` into the operator-visible warning."
  [host]
  (if (guard/allowlist-open? (guard/allowed-hosts host)) :open :allowlisted))

(defn- announce-auth!
  "Say which postures the daemon started in, every start — the token question
  (`posture`) and the `Host`-allowlist question (`hosts`) beside it.  Each absence is a
  warning rather than a silence: it is the line an operator greps for after an
  incident, and an absent log line is indistinguishable from a daemon that never
  started."
  [host posture hosts]
  (if (= :required posture)
    (trove/log! {:level :info :id ::authenticated
                 :msg "every request must carry Authorization: Bearer <VAELII_API_TOKEN>"})
    (trove/log! {:level :warn :id ::no-token
                 :msg (str "no VAELII_API_TOKEN: POST /op is the KB's only writer and "
                           "every process on this machine can drive it — set one, and "
                           "note that --listen with an address requires one")}))
  (when (public-bind? host)
    (trove/log! {:level :warn :id ::public-bind
                 :msg (str "daemon bound to " host " — the wire is plaintext; "
                           "terminate TLS in a reverse proxy")
                 :data {:host host}}))
  (when (= :open hosts)
    (trove/log! {:level :warn :id ::open-hosts
                 :msg (str "no VAELII_ALLOWED_HOSTS: every Host header is answered on "
                           host " — fine behind a reverse proxy that sets its own Host, "
                           "a DNS-rebinding vector otherwise.  Name the hosts this "
                           "daemon should answer, or confirm that is what fronts it")
                 :data {:host host}})))

(defn -main
  "Run the daemon in the foreground.  Args: `[port [dir]] [--listen ADDR]`, in any
  order — `dir` selects the durable `:disk-log` backend (recovered on open, so it
  persists across restarts); with no `dir` the KB is in-memory and lives only as
  long as the process.

    lein run -m vaelii.impl.serve 4200 /var/lib/vaelii
    lein run -m vaelii.impl.serve 4200 /var/lib/vaelii --listen 0.0.0.0   ; opt-in

  It binds **loopback** unless `--listen` says otherwise, for the reason on `loopback`
  above: `POST /op` writes, and it is the KB's only writer.  What it binds and what it
  requires are one decision (`auth-posture`), so they are stated together:

  - `--listen` names a **non-loopback** address ⇒ `VAELII_API_TOKEN` is **required**.
    Without one it is a line on stderr and exit **2**, a code of its own so a
    supervisor tells a missing credential from the configuration typos below.
  - **Loopback** — the default, and `--listen 127.0.0.1` said out loud — ⇒ the token
    is used when set, and its absence is a startup warning naming the flag that would
    require one.

  Naming an address also drops the `Host` allowlist (`guard/allowed-hosts`), since the
  name you reach it by is then yours to know; set `VAELII_ALLOWED_HOSTS` to keep the
  check.  Left unset, the daemon starts anyway — a reverse proxy setting its own `Host`
  needs exactly this — and `host-posture` turns the gap into a startup warning rather
  than a silence.  A `--listen` with no address, an unknown flag, or a stray argument
  is one line and exit 1, like the port typo below."
  [& args]
  (let [[port-s dir] (try (positional-args args)
                          (catch clojure.lang.ExceptionInfo e
                            (binding [*out* *err*] (println (ex-message e)))
                            (System/exit 1)))
        host  (try (listen-host args)
                   (catch clojure.lang.ExceptionInfo e
                     (binding [*out* *err*] (println (ex-message e)))
                     (System/exit 1)))
        ;; a non-numeric port is the operator's typo: one line and exit 1, not a
        ;; NumberFormatException stack trace — the same courtesy `impl.cli` extends
        port  (if port-s
                (try (Integer/parseInt port-s)
                     (catch NumberFormatException _
                       (binding [*out* *err*]
                         (println (str "not a port number: " port-s)))
                       (System/exit 1)))
                4200)
        token (guard/api-token)
        ;; before the KB is opened, which takes the directory's single-writer lock: a
        ;; daemon that is going to refuse to serve must not first take a lock off the
        ;; process that could have
        posture (try (auth-posture host token)
                     (catch clojure.lang.ExceptionInfo e
                       (binding [*out* *err*] (println (ex-message e)))
                       (System/exit 2)))
        hosts (host-posture host)
        kb    (if dir
                (v/open-kb {:backend :disk-log :dir dir :recover? :auto})
                (v/open-kb {}))]
    (trove/log! {:level :info :id ::start
                 :msg "vaelii daemon listening"
                 :data {:port port :host host :dir (or dir :memory)
                        :auth posture :hosts hosts}})
    (announce-auth! host posture hosts)
    ;; `:max-threads` here as in `start`: `http-threads` is one half of the pair
    ;; `subscribe/max-parked` is pinned against, and a daemon run from the command line
    ;; has to hold the same relationship as one a test starts
    (jetty/run-jetty (app kb {:host host :token token})
                     {:port port :host host :join? true :max-threads http-threads})))
